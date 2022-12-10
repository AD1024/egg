use std::sync::Arc;

use coin_cbc::{Col, Model, Sense};
use rplex::*;

use crate::*;
use rand::{thread_rng, Rng};

/// A cost function to be used by an [`LpExtractor`].
#[cfg_attr(docsrs, doc(cfg(feature = "lp")))]
pub trait LpCostFunction<L: Language, N: Analysis<L>> {
    /// Returns the cost of the given e-node.
    ///
    /// This function may look at other parts of the e-graph to compute the cost
    /// of the given e-node.
    fn node_cost(&mut self, egraph: &EGraph<L, N>, eclass: Id, enode: &L) -> f64;
}

#[cfg_attr(docsrs, doc(cfg(feature = "lp")))]
impl<L: Language, N: Analysis<L>> LpCostFunction<L, N> for AstSize {
    fn node_cost(&mut self, _egraph: &EGraph<L, N>, _eclass: Id, _enode: &L) -> f64 {
        1.0
    }
}

/// A structure to perform extraction using integer linear programming.
/// This uses the [`cbc`](https://projects.coin-or.org/Cbc) solver.
/// You must have it installed on your machine to use this feature.
/// You can install it using:
///
/// | OS               | Command                                  |
/// |------------------|------------------------------------------|
/// | Fedora / Red Hat | `sudo dnf install coin-or-Cbc-devel`     |
/// | Ubuntu / Debian  | `sudo apt-get install coinor-libcbc-dev` |
/// | macOS            | `brew install cbc`                       |
///
/// # Example
/// ```
/// use egg::*;
/// let mut egraph = EGraph::<SymbolLang, ()>::default();
///
/// let f = egraph.add_expr(&"(f x x x)".parse().unwrap());
/// let g = egraph.add_expr(&"(g (g x))".parse().unwrap());
/// egraph.union(f, g);
/// egraph.rebuild();
///
/// let best = Extractor::new(&egraph, AstSize).find_best(f).1;
/// let lp_best = LpExtractor::new(&egraph, AstSize).solve(f);
///
/// // In regular extraction, cost is measures on the tree.
/// assert_eq!(best.to_string(), "(g (g x))");
///
/// // Using ILP only counts common sub-expressions once,
/// // so it can lead to a smaller DAG expression.
/// assert_eq!(lp_best.to_string(), "(f x x x)");
/// assert_eq!(lp_best.as_ref().len(), 2);
/// ```
#[cfg_attr(docsrs, doc(cfg(feature = "lp")))]
pub struct LpExtractor<'a, L: Language, N: Analysis<L>> {
    egraph: &'a EGraph<L, N>,
    model: Model,
    vars: HashMap<Id, ClassVars>,
    cycle: HashSet<(Id, usize)>,
    fractional_extract: bool,
}

pub struct FractionalExtractor<'a, L: Language, N: Analysis<L>> {
    egraph: &'a EGraph<L, N>,
    model: Problem<'a>,
    vars: HashMap<Id, FractionalClassVar>,
    fallback: bool,
}

struct FractionalClassVar {
    topo: usize,
    nodes: Vec<usize>,
}

/// Extractor trait
pub trait LpExtractorTrait<L: Language, N: Analysis<L>> {
    /// Solve extraction for a single root
    fn solve(&mut self, root: Id) -> RecExpr<L>;

    /// Solve extraction for a set of roots
    fn solve_multiple(&mut self, roots: &[Id]) -> (RecExpr<L>, Vec<Id>);

    /// Timeouts
    fn set_timeout(&mut self, timeout: u64) -> &mut Self;
}

struct ClassVars {
    active: Col,
    order: Col,
    nodes: Vec<Col>,
}

impl<'a, L, N> LpExtractor<'a, L, N>
where
    L: Language,
    N: Analysis<L>,
{
    /// Create an [`LpExtractor`] using costs from the given [`LpCostFunction`].
    /// See those docs for details.
    pub fn new<CF>(egraph: &'a EGraph<L, N>, mut cost_function: CF, fractional: bool) -> Self
    where
        CF: LpCostFunction<L, N>,
    {
        let max_order = egraph.total_number_of_nodes() as f64 * 10.0;
        println!("Fractional: {}", fractional);

        let mut model = Model::default();

        let vars: HashMap<Id, ClassVars> = egraph
            .classes()
            .map(|class| {
                let cvars = ClassVars {
                    active: if fractional {
                        model.add_col()
                    } else {
                        model.add_binary()
                    },
                    order: model.add_col(),
                    nodes: class
                        .nodes
                        .iter()
                        .map(|_| {
                            if fractional {
                                model.add_col()
                            } else {
                                model.add_binary()
                            }
                        })
                        .collect(),
                };
                model.set_col_upper(cvars.order, max_order);
                (class.id, cvars)
            })
            .collect();

        let mut cycles: HashSet<(Id, usize)> = Default::default();
        find_cycles(egraph, |id, i| {
            cycles.insert((id, i));
        });

        for (&id, class) in &vars {
            // class active maximum to 1.0
            // let row = model.add_row();
            // model.set_row_upper(row, 1.0);
            // model.set_weight(row, class.active, 1.0);

            // class active == some node active
            // sum(for node_active in class) == class_active
            let row = model.add_row();
            model.set_row_lower(row, 0.0);
            model.set_weight(row, class.active, -1.0);
            for &node_active in &class.nodes {
                model.set_weight(row, node_active, 1.0);
            }

            if (0..egraph[id].len()).all(|i| cycles.contains(&(id, i))) {
                // class active == 0 && node_active == 0 if
                // all children are in a cycle
                model.set_row_upper(row, 0.0);
                class.nodes.iter().for_each(|&node_active| {
                    model.set_col_upper(node_active, 0.0);
                });
                continue;
            }

            for (i, (node, &node_active)) in egraph[id].iter().zip(&class.nodes).enumerate() {
                if cycles.contains(&(id, i)) {
                    model.set_col_upper(node_active, 0.0);
                    model.set_col_lower(node_active, 0.0);
                    continue;
                }

                for child in node.children() {
                    let child_active = vars[child].active;
                    // node active implies child active, encoded as:
                    //   node_active <= child_active
                    //   node_active - child_active <= 0
                    let row = model.add_row();
                    model.set_row_upper(row, 0.0);
                    model.set_weight(row, node_active, 1.0);
                    model.set_weight(row, child_active, -1.0);
                }
            }
        }

        model.set_obj_sense(Sense::Minimize);
        for class in egraph.classes() {
            for (node, &node_active) in class.iter().zip(&vars[&class.id].nodes) {
                model.set_obj_coeff(node_active, cost_function.node_cost(egraph, class.id, node));
            }
            // for (_, class) in &vars {
            //     model.set_obj_coeff(class.active, -1.0);
            // }
        }

        dbg!(max_order);

        Self {
            egraph,
            model,
            vars,
            fractional_extract: fractional,
            cycle: cycles,
        }
    }

    /// Set the cbc timeout in seconds.
    pub fn timeout(&mut self, seconds: f64) -> &mut Self {
        self.model.set_parameter("seconds", &seconds.to_string());
        self
    }

    /// Extract a single rooted term.
    ///
    /// This is just a shortcut for [`LpExtractor::solve_multiple`].
    pub fn solve(&mut self, root: Id) -> RecExpr<L> {
        self.solve_multiple(&[root]).0
    }

    /// Extract (potentially multiple) roots
    pub fn solve_multiple(&mut self, roots: &[Id]) -> (RecExpr<L>, Vec<Id>) {
        let egraph = self.egraph;

        if !self.fractional_extract {
            for class in self.vars.values() {
                self.model.set_binary(class.active);
            }
        }

        for root in roots {
            let root = &egraph.find(*root);
            self.model.set_col_lower(self.vars[root].active, 1.0);
        }

        let solution = self.model.solve();
        // log::info!(
        //     "CBC status {:?}, {:?}",
        //     solution.raw().status(),
        //     solution.raw().secondary_status()
        // );

        let mut todo: Vec<Id> = roots.iter().map(|id| self.egraph.find(*id)).collect();
        let mut expr = RecExpr::default();
        // converts e-class ids to e-node ids
        let mut ids: HashMap<Id, Id> = HashMap::default();

        while let Some(&id) = todo.last() {
            if ids.contains_key(&id) {
                todo.pop();
                continue;
            }
            let id = egraph.find(id);
            let v = &self.vars[&id];
            assert!(
                solution.col(v.active) > 0.0,
                "class {} not active: {}",
                id,
                solution.col(v.active)
            );
            println!("decide for eclass {}", id);
            let node_idx = {
                if self.fractional_extract {
                    let mut rng = rand::thread_rng();
                    let mut choice = 0;
                    let total = v.nodes.iter().map(|&x| solution.col(x)).sum::<f64>();
                    for (i, &node_active) in v.nodes.iter().enumerate() {
                        println!(
                            "{} {} (total: {})",
                            i,
                            solution.col(node_active) / total,
                            total
                        );
                        if solution.col(node_active) > 0.0 && solution.col(v.nodes[choice]) == 0.0 {
                            choice = i;
                        }
                        if solution.col(node_active) / total > rng.gen_range(0.1..1.0) {
                            choice = i;
                            break;
                        }
                    }
                    choice
                } else {
                    // v.nodes.iter().for_each(|&n| println!("{}", solution.col(n)));
                    v.nodes.iter().position(|&n| solution.col(n) > 0.0).unwrap()
                }
            };
            println!(
                "node_idx {} with sol: {}",
                node_idx,
                solution.col(v.nodes[node_idx])
            );
            let node = &self.egraph[id].nodes[node_idx];
            if node.all(|child| ids.contains_key(&child)) {
                let new_id = expr.add(node.clone().map_children(|i| ids[&self.egraph.find(i)]));
                ids.insert(id, new_id);
                todo.pop();
            } else {
                todo.extend_from_slice(node.children())
            }
        }

        let root_idxs = roots.iter().map(|root| ids[root]).collect();

        assert!(expr.is_dag(), "LpExtract found a cyclic term!: {:?}", expr);
        (expr, root_idxs)
    }
}

impl<'a, L: Language, N: Analysis<L>> LpExtractorTrait<L, N> for LpExtractor<'a, L, N> {
    fn solve(&mut self, root: Id) -> RecExpr<L> {
        self.solve_multiple(&[root]).0
    }

    fn solve_multiple(&mut self, roots: &[Id]) -> (RecExpr<L>, Vec<Id>) {
        self.solve_multiple(roots)
    }

    fn set_timeout(&mut self, timeout: u64) -> &mut Self {
        self.timeout(timeout as f64);
        self
    }
}

impl<'a, L: Language, N: Analysis<L>> FractionalExtractor<'a, L, N> {
    /// Create a fractional extraction problem
    pub fn new<CF>(
        egraph: &'a EGraph<L, N>,
        env: &'a rplex::Env,
        mut cost_function: CF,
        order_var: bool,
        fallback: bool,
    ) -> Self
    where
        CF: LpCostFunction<L, N>,
    {
        let max_order = (egraph.total_size() * 5) as f64;
        let eps = 1.0 / (max_order * 2.0);
        let mut problem = rplex::Problem::new(env, "fractional_ext").unwrap();
        let vars = egraph
            .classes()
            .map(|cls| {
                let topo_name = format!("topo_{}", cls.id);
                let variable_type = if fallback {
                    rplex::VariableType::Binary
                } else {
                    rplex::VariableType::Continuous
                };
                let topo_var = problem
                    .add_variable(var!(0.0 <= topo_name <= max_order -> 0.0 as Continuous))
                    .unwrap();
                let nodes = cls
                    .nodes
                    .iter()
                    .enumerate()
                    .map(|(i, node)| {
                        let node_active = format!("node_active_{}_{}", cls.id, i);
                        let node_cost = cost_function.node_cost(egraph, cls.id, node);
                        let node_active_var = problem
                            .add_variable(
                                var!(0.0 <= node_active <= 1.0 -> node_cost as variable_type),
                            )
                            .unwrap();
                        node_active_var
                    })
                    .collect::<Vec<_>>();
                (
                    cls.id,
                    FractionalClassVar {
                        topo: topo_var,
                        nodes,
                    },
                )
            })
            .collect::<HashMap<_, _>>();

        let mut cycles: HashSet<(Id, usize)> = HashSet::default();
        find_cycles(egraph, |id, i| {
            cycles.insert((id, i));
        });

        // Constraint:
        // if a node is active, then at least one of the nodes in each child class is active
        for cls in egraph.classes() {
            if (0..cls.nodes.len()).all(|i| cycles.contains(&(cls.id, i))) {
                panic!(
                    "All nodes in class {} are in a cycle: {:?}",
                    cls.id, cls.nodes
                );
            }
            // let normalization_cons = rplex::Constraint::new(ConstraintType::GreaterThanEq, 1.0, format!("normalization_{}", cls.id));
            for (i, node) in cls.nodes.iter().enumerate() {
                if !fallback {
                    if cycles.contains(&(cls.id, i)) {
                        let cons_name = format!("elim_cycle_{}_{}", cls.id, i);
                        let node_var_idx = vars[&cls.id].nodes[i];
                        problem
                            .add_constraint(con!(cons_name: 0.0 = 1.0 node_var_idx))
                            .unwrap();
                        continue;
                    }
                }
                let node_var_idx = vars[&cls.id].nodes[i];
                for child in node.children() {
                    let cons_name = format!("child_active_{}_{}_{}", cls.id, i, child);
                    // let child = egraph.find(*child);
                    let child_var = &vars[child];
                    let mut constraint =
                        rplex::Constraint::new(ConstraintType::GreaterThanEq, 0.0, cons_name);
                    constraint.add_wvar(WeightedVariable::new_idx(node_var_idx, -1.0));
                    for child_node in &child_var.nodes {
                        constraint.add_wvar(WeightedVariable::new_idx(*child_node, 1.0));
                    }
                    problem.add_constraint(constraint).unwrap();
                    if order_var {
                        // topo_var(cls) - topo_var(child) - eps + 2 * (1 - node_var) >= 0
                        // ==> topo_var(cls) - topo_var(child) - eps + 2 - 2 * node_var >= 0
                        // ==> topo_var(cls) - topo_var(child) - 2 * node_var >= eps - 2
                        let cls_topo_idx = vars[&cls.id].topo;
                        let child_topo_idx = vars[&child].topo;
                        let cons_name = format!("topo_{}_{}_{}", cls.id, i, child);
                        let lhs = eps - 2.0;
                        let constraint = con!(cons_name: lhs <= 1.0 cls_topo_idx + (-1.0) child_topo_idx + (-2.0) node_var_idx);
                        problem.add_constraint(constraint).unwrap();
                    }
                }
            }
        }
        problem.set_objective_type(ObjectiveType::Minimize).unwrap();
        Self {
            egraph,
            model: problem,
            vars,
            fallback,
        }
    }

    /// Borrowed and modified from Tensat
    /// Extract an expression using the LP solution
    pub fn construct_expr(
        &self,
        solution: &Solution,
        eclass: Id,
        rec_expr: &mut RecExpr<L>,
        memo: &mut HashMap<Id, Id>,
    ) -> Id {
        let id = self.egraph.find(eclass);
        match memo.get(&id) {
            Some(id) => *id,
            None => {
                // figure out which node to pick
                let cls = &self.egraph[id];
                let mut picked = -1;
                for (i, node_idx) in self.vars[&id].nodes.iter().enumerate() {
                    let val = match solution.variables[*node_idx] {
                        VariableValue::Continuous(val) => val,
                        VariableValue::Binary(val) => {
                            if val {
                                1.0
                            } else {
                                0.0
                            }
                        }
                        _ => panic!("Unexpected variable value type"),
                    };
                    if val > 0.0 {
                        if picked < 0 {
                            picked = i as i32;
                        } else {
                            let threshold: f64 = thread_rng().gen_range(0.0..=1.0);
                            if threshold <= val {
                                picked = i as i32;
                            }
                        }
                    }
                }
                assert!(picked >= 0, "No node picked for class: {}", id);
                let node = &cls.nodes[picked as usize]
                    .clone()
                    .map_children(|child| self.construct_expr(solution, child, rec_expr, memo));
                let new_id = rec_expr.add(node.clone());
                assert!(memo.insert(id, new_id).is_none());
                new_id
            }
        }
    }
}

impl<'a, L: Language, N: Analysis<L>> LpExtractorTrait<L, N> for FractionalExtractor<'a, L, N> {
    fn set_timeout(&mut self, _: u64) -> &mut Self {
        self
    }

    fn solve(&mut self, root: Id) -> RecExpr<L> {
        let root = self.egraph.find(root);
        let root_var = &self.vars[&root];
        let mut constraint = rplex::Constraint::new(
            ConstraintType::GreaterThanEq,
            1.0,
            format!("root_constraint_{}", root),
        );
        for node in &root_var.nodes {
            constraint.add_wvar(WeightedVariable::new_idx(*node, 1.0));
        }
        self.model.add_constraint(constraint).unwrap();
        let solution = self.model.solve_as(if self.fallback {
            ProblemType::MixedInteger
        } else {
            ProblemType::Linear
        });
        if let Ok(sol) = solution {
            let mut rec_expr = RecExpr::default();
            let mut memo = HashMap::default();
            let _ = self.construct_expr(&sol, root, &mut rec_expr, &mut memo);
            rec_expr
        } else {
            panic!("Failed to solve the problem: {}", solution.err().unwrap());
        }
    }

    fn solve_multiple(&mut self, _: &[Id]) -> (RecExpr<L>, Vec<Id>) {
        // not capable of extracting multiple for now
        unimplemented!()
    }
}

fn find_cycles<L, N>(egraph: &EGraph<L, N>, root: (id, usize), mut f: impl FnMut(Id, usize)) -> HashMap<Id, i32> //returns bfs_index
where
    L: Language,
    N: Analysis<L>,
{
    enum Color {
        White,
        Black,
    }

    let mut color: HashMap<Id, Color> = egraph.classes().map(|c| (c.id, Color::White)).collect(); //contains reverse edges
    *color.get_mut(&id).unwrap() = Color::Black;
    
    let mut stack: Vec<Id> = [root];

    let mut count: i32 = 0;
    let mut bfs_index: HashMap<Id, i32> = egraph.classes().map(|c| (c.id, -1)).collect();

    while let Some(id) = stack.pop() {
        // if enter {
            // *color.get_mut(&id).unwrap() = Color::Gray;
            stack.push((false, id));
            count += 1;
            *bfs_index.get_mut(&id).unwrap() = count;

            for (i, node) in egraph[id].iter().enumerate() {
                for child in node.children() {
                    match &color[child] {
                        Color::White => {
                            stack.push((true, *child))
                            *color.get_mut(&child).unwrap() = Color::Black;
                        },
                        Color::Black => f(id, i),
                    }
                }
            }
        // } else {
        //     *color.get_mut(&id).unwrap() = Color::Black;
        // }
    }

    bfs_index
}

#[cfg(test)]
mod tests {
    use crate::{SymbolLang as S, *};

    #[test]
    fn simple_lp_extract_two() {
        let mut egraph = EGraph::<S, ()>::default();
        let a = egraph.add(S::leaf("a"));
        let plus = egraph.add(S::new("+", vec![a, a]));
        let f = egraph.add(S::new("f", vec![plus]));
        let g = egraph.add(S::new("g", vec![plus]));

        let mut ext = LpExtractor::new(&egraph, AstSize, false);
        ext.timeout(10.0); // way too much time
        let (exp, ids) = ext.solve_multiple(&[f, g]);
        println!("{:?}", exp);
        println!("{}", exp);
        assert_eq!(exp.as_ref().len(), 4);
        assert_eq!(ids.len(), 2);
    }
}
