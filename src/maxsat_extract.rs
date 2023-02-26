use std::process::Command;

use crate::{Analysis, EGraph, HashMap, HashSet, Id, Language, RecExpr};

/// Get all cycles in the given E-Graph
pub fn get_cycles<L, N>(
    egraph: &EGraph<L, N>,
    root: &Id,
    path: &mut Vec<(Id, L)>,
    vis: &mut HashSet<Id>,
    cycles: &mut Vec<Vec<(Id, L)>>,
) where
    L: Language,
    N: Analysis<L>,
{
    assert!(
        !vis.contains(root),
        "cannot be visited again, should be handled in cycle detection"
    );
    vis.insert(*root);
    for node in egraph[*root].nodes.iter() {
        for ch in node.children() {
            if vis.contains(ch) {
                // cycle detected
                if let Some((idx, _)) = path.iter().enumerate().find(|(_, (id, _))| id == ch) {
                    let mut subpath = path[idx..].to_vec();
                    subpath.push((*root, node.clone()));
                    cycles.push(subpath);
                } else if ch == root {
                    // self loop
                    cycles.push(vec![(*root, node.clone())])
                }
            } else {
                let mut to_here = path.clone();
                to_here.push((*root, node.clone()));
                get_cycles(egraph, ch, &mut to_here, vis, cycles);
            }
        }
    }
}

struct ProblemWriter {
    pub path: String,
    problem: String,
}

impl ProblemWriter {
    pub fn new(path: String) -> Self {
        Self {
            path,
            problem: String::new(),
        }
    }

    pub fn comment(&mut self, comment: &str) {
        self.problem.push_str(&format!("c {}\n", comment));
    }

    pub fn parameters(&mut self, num_vars: usize, num_clauses: usize, top: f64) {
        self.problem
            .push_str(&format!("p wcnf {} {} {}\n", num_vars, num_clauses, top));
    }

    pub fn hard_clause(&mut self, clause: &str, top: f64) {
        self.problem.push_str(&format!("{} {} 0\n", top, clause));
    }

    pub fn soft_clause(&mut self, clause: &str, weight: f64) {
        self.problem.push_str(&format!("{} {} 0\n", weight, clause));
    }

    pub fn dump(&mut self) {
        std::fs::write(self.path.clone(), self.problem.clone()).unwrap();
    }
}

pub struct MaxsatExtractor<'a, L: Language, N: Analysis<L>> {
    pub egraph: &'a EGraph<L, N>,
    writer: ProblemWriter,
}

pub struct WeightedPartialMaxsatProblem<'a, L: Language, N: Analysis<L>> {
    // pub class_vars: HashMap<Id, i32>,
    pub node_vars: HashMap<L, usize>,
    pub root: Id,
    pub egraph: &'a EGraph<L, N>,
    pub problem_path: String,
}

impl<'a, L, N> WeightedPartialMaxsatProblem<'a, L, N>
where
    L: Language,
    N: Analysis<L>,
{
    /// Given a weighted partial maxsat problem, solve the problem
    /// and parse the output
    pub fn solve(&self, problem: &WeightedPartialMaxsatProblem<'a, L, N>) {
        // assume maxhs installed
        let result = Command::new("maxhs")
            .arg(problem.problem_path.clone())
            .output();
        if let Ok(output) = result {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let lines = stdout.lines();
            let (mut comments, mut opt_line, mut sol_line) = (vec![], vec![], vec![]);
            for l in lines {
                let mut line = l.split(" ");
                if let Some(indicator) = line.next() {
                    match indicator {
                        "c" => comments.push(line.collect::<Vec<_>>().join(" ")),
                        "o" => opt_line.push(line.collect::<Vec<_>>().join(" ")),
                        "s" => sol_line.push(line.collect::<Vec<_>>().join(" ")),
                        _ => (),
                    }
                }
            }
            // parse opt
            if opt_line.len() > 0 {
                let opt = opt_line.iter().next().unwrap();
                println!("Optimal: {}", opt)
            }
            assert!(sol_line.len() > 0, "Solution cannot be empty");
            let sol = sol_line.iter().next().unwrap();
            if sol.contains("UNSATISFIABLE") {
                println!("Problem UNSAT")
            } else {
                let sat_map = sol
                    .chars()
                    .enumerate()
                    .filter(|(_, res)| *res == '1')
                    .map(|(car, _)| car)
                    .collect::<HashSet<_>>();
                let mut worklist = Vec::new();
                let mut expr = RecExpr::default();
                let mut id_map = HashMap::default();
                worklist.push(self.root);
                while let Some(&id) = worklist.last() {
                    if id_map.contains_key(&id) {
                        worklist.pop();
                        continue;
                    }
                    for n in &self.egraph[id].nodes {
                        if sat_map.contains(&self.node_vars[&n]) {
                            if n.all(|ch| id_map.contains_key(&ch)) {
                                let new_id = expr.add(
                                    n.clone().map_children(|ch| id_map[&self.egraph.find(ch)]),
                                );
                                id_map.insert(id.clone(), new_id);
                                worklist.pop();
                            } else {
                                worklist.extend_from_slice(n.children());
                            }
                            break;
                        }
                    }
                    panic!("No active node for eclass: {}", id.clone());
                }
            }
        } else {
            panic!(
                "Unable to solve {}, err: {}",
                problem.problem_path,
                result.err().unwrap()
            );
        }
    }
}

pub trait MaxsatCostFunction<L: Language, N: Analysis<L>> {
    /// Returns the cost of the given e-node.
    ///
    /// This function may look at other parts of the e-graph to compute the cost
    /// of the given e-node.
    fn node_cost(&mut self, egraph: &EGraph<L, N>, eclass: Id, enode: &L) -> f64;
}

impl<'a, L, N> MaxsatExtractor<'a, L, N>
where
    L: Language,
    N: Analysis<L>,
{
    /// create a new maxsat extractor
    pub fn new(egraph: &'a EGraph<L, N>, path: String) -> Self {
        Self {
            egraph,
            writer: ProblemWriter::new(path.clone()),
        }
    }

    /// create a maxsat problem
    pub fn create_problem<CF>(
        &mut self,
        root: Id,
        name: &str,
        no_cycle: bool,
        mut cost_fn: CF,
    ) -> WeightedPartialMaxsatProblem<'a, L, N>
    where
        CF: MaxsatCostFunction<L, N>,
    {
        // Hard Constraints
        // === root constraint (pick at least one in root)
        // \forall n \in R, \bigvee v_n
        // === children constraint
        // \forall n, \forall C\in children(n), v_n -> \bigvee_cN v_cN \forall cN \in C
        self.writer.comment(&format!("Problem: {}", name));
        // create variables
        let mut num_vars = 0;
        let mut top = 0 as f64;
        let mut node_vars = HashMap::default();
        let mut node_weight_map = HashMap::default();
        for c in self.egraph.classes() {
            for n in c.nodes.iter() {
                node_vars.insert(n.clone(), num_vars + 1);
                num_vars += 1;

                node_weight_map.insert(n.clone(), cost_fn.node_cost(self.egraph, c.id, n));
                top += cost_fn.node_cost(self.egraph, c.id, n);
            }
        }

        let top = top + 1 as f64;

        // Hard clauses
        let mut hard_clauses = Vec::new();
        // root constraint
        let root_clause = self.egraph[root]
            .nodes
            .iter()
            .map(|n| node_vars[n])
            .map(|v| v.to_string())
            .collect::<Vec<_>>()
            .join(" ");
        hard_clauses.push(root_clause);

        // children constraint
        for c in self.egraph.classes() {
            for n in c.nodes.iter() {
                // v_n -> \bigvee_cN v_cN forall C
                for ch in n.children() {
                    let mut clause = String::new();
                    clause.push_str(&format!("-{}", node_vars[n]));
                    for ch_node in self.egraph[*ch].nodes.iter() {
                        clause.push_str(&format!(" {}", node_vars[ch_node]));
                    }
                    hard_clauses.push(clause);
                }
            }
        }

        // cycle constraint
        if no_cycle {
            let mut cycles = Vec::new();
            let mut vis = HashSet::default();
            let mut path = Vec::new();
            get_cycles(self.egraph, &root, &mut path, &mut vis, &mut cycles);
            for cycle in cycles {
                // println!("cycle: {:?}", cycle);
                let clause = cycle
                    .iter()
                    .map(|(_, n)| node_vars[n])
                    .map(|v| format!("-{}", v))
                    .collect::<Vec<_>>()
                    .join(" ");
                hard_clauses.push(clause);
            }
        }

        // soft clauses (i.e. not all nodes need to be picked)
        let mut soft_clauses = HashMap::default();
        for c in self.egraph.classes() {
            for n in c.nodes.iter() {
                soft_clauses.insert(n.clone(), format!("-{}", node_vars[n]));
            }
        }

        let nbclause = hard_clauses.len() + soft_clauses.len();
        let nbvars = num_vars;

        self.writer.comment(&format!("Parameters"));
        self.writer.parameters(nbvars, nbclause, top);

        self.writer.comment("Hard clauses:");
        for clause in hard_clauses {
            self.writer.hard_clause(&clause, top);
        }

        self.writer.comment("Soft clauses:");
        for (n, clause) in soft_clauses {
            self.writer.soft_clause(&clause, node_weight_map[&n]);
        }

        self.writer.dump();

        WeightedPartialMaxsatProblem {
            node_vars,
            root,
            egraph: self.egraph,
            problem_path: self.writer.path.clone(),
        }
    }
}
