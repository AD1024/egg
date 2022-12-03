use coin_cbc::{Col, Model, Sense};

use crate::*;
use rand::Rng;

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
                    active: if fractional { model.add_col() } else { model.add_binary() },
                    order: model.add_col(),
                    nodes: class.nodes.iter().map(|_| if fractional { model.add_col() } else { model.add_binary() }).collect(),
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
                    println!("Id: {} node: {} is in a cycle (total: {})", id, i, egraph[id].len());
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
            cycle: cycles
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
            assert!(solution.col(v.active) > 0.0, "class {} not active: {}", id, solution.col(v.active));
            println!("decide for eclass {}", id);
            let node_idx = {
                if self.fractional_extract {
                    let mut rng = rand::thread_rng();
                    let mut choice = 0;
                    let total = v.nodes.iter().map(|&x| solution.col(x)).sum::<f64>();
                    for (i, &node_active) in v.nodes.iter().enumerate() {
                        println!("{} {} (total: {})", i, solution.col(node_active) / total, total);
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
            println!("node_idx {} with sol: {}", node_idx, solution.col(v.nodes[node_idx]));
            let node = &self.egraph[id].nodes[node_idx];
            if node.all(|child| ids.contains_key(&child)) {
                let new_id = expr.add(node.clone().map_children(|i| ids[&self.egraph.find(i)]));
                ids.insert(id, new_id);
                todo.pop();
            } else {
                println!("Node of {} in cycle: {}", id, self.cycle.contains(&(id, node_idx)));
                for child in node.children() {
                    println!("child {} active: {}", child, solution.col(self.vars[&child].active));
                    if solution.col(self.vars[&child].active) == 0.0 {
                        println!("child {} == 0: {:?} | {:?}", child,
                            self.vars[&child].nodes.iter().map(|&n| solution.col(n)).collect::<Vec<_>>(), (0..egraph[*child].len()).map(|x| self.cycle.contains(&(*child, x))).collect::<Vec<_>>());
                    }
                }
                todo.extend_from_slice(node.children())
            }
        }

        let root_idxs = roots.iter().map(|root| ids[root]).collect();

        assert!(expr.is_dag(), "LpExtract found a cyclic term!: {:?}", expr);
        (expr, root_idxs)
    }
}

fn find_cycles<L, N>(egraph: &EGraph<L, N>, mut f: impl FnMut(Id, usize))
where
    L: Language,
    N: Analysis<L>,
{
    enum Color {
        White,
        Gray,
        Black,
    }
    type Enter = bool;

    let mut color: HashMap<Id, Color> = egraph.classes().map(|c| (c.id, Color::White)).collect();
    let mut stack: Vec<(Enter, Id)> = egraph.classes().map(|c| (true, c.id)).collect();

    while let Some((enter, id)) = stack.pop() {
        if enter {
            *color.get_mut(&id).unwrap() = Color::Gray;
            stack.push((false, id));
            for (i, node) in egraph[id].iter().enumerate() {
                for child in node.children() {
                    match &color[child] {
                        Color::White => stack.push((true, *child)),
                        Color::Gray => f(id, i),
                        Color::Black => (),
                    }
                }
            }
        } else {
            *color.get_mut(&id).unwrap() = Color::Black;
        }
    }
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
