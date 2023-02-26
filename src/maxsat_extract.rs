use crate::{Analysis, EGraph, HashMap, HashSet, Id, Language};

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
    pub egraph: &'a EGraph<L, N>,
    pub problem_path: String,
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
            egraph: self.egraph,
            problem_path: self.writer.path.clone(),
        }
    }
}
