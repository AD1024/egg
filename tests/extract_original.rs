use egg::*;
use std::cmp::Ordering;

type BuildHasher = fxhash::FxBuildHasher;
type HashSet<K> = hashbrown::HashSet<K, BuildHasher>;
type EG = egg::EGraph<TestLang, TestLangAnalysis>;
type Expr = RecExpr<TestLang>;
type MatchPat = Pattern<TestLang>;

define_language! {
    pub enum TestLang {
        "bias_add" = BiasAdd([Id; 2]),
        "dense"    = Dense([Id; 2]),
        "add"      = Add([Id; 2]),
        "reshape"  = Reshape([Id; 2]),
        "shape"    = Shape(Box<[Id]>),
        Usize(usize),
        Symbol(String),
    }
}

struct TestLangAnalysis;

impl Analysis<TestLang> for TestLangAnalysis {
    type Data = HashSet<TestLang>;
    fn make(egraph: &EGraph<TestLang, Self>, enode: &TestLang) -> Self::Data {
        let mut original_exprs : HashSet<TestLang> = Default::default();
        if egraph.tagging() {
            original_exprs.insert(enode.clone());
        }
        original_exprs
    }
    fn merge(&self, a: &mut Self::Data, b: Self::Data) -> Option<Ordering> {
        a.extend(b.iter().cloned());
        None
    }
}

fn validation_fn(x: &TestLang, data: &HashSet<TestLang>) -> bool {
    data.contains(x)
}

fn validate_data(x: &HashSet<TestLang>) -> bool {
    x.len() > 0
}
 
fn rewrites() -> Vec<egg::Rewrite<TestLang, TestLangAnalysis>> {
    fn is_shape(s : Var) -> impl Fn(&mut EG, Id, &Subst) -> bool {
        move |egraph, _, subst| {
            egraph[subst[s]].nodes.iter().map(|enode| match enode {
                TestLang::Shape(_) => true,
                _ => false
            }).all(|x| x)
        }
    }
    vec! [
        rewrite!("bubble-reshape"; "(add 
                                    (reshape 
                                        (dense ?x ?w) 
                                        ?s) ?b)"
                                =>
                               "(reshape (bias_add (dense ?x ?w) ?b) ?s)" if is_shape("?s".parse().unwrap()))
    ]
}

#[test]
fn linear_rewrite() {
    let expr : Expr = "(add (reshape (dense x w) (shape 1 4 4)) b)".parse().unwrap();
    let pattern : MatchPat = "(bias_add (dense ?x ?w) ?b)".parse().unwrap();
    let mut egraph = EG::new(TestLangAnalysis {});
    egraph.toggle_tag_original(true);
    egraph.add_expr(&expr);
    egraph.toggle_tag_original(false);
    let rws = rewrites();
    let runner = Runner::<_, _, ()>::new(TestLangAnalysis {}).with_egraph(egraph).run(&rws);
    println!("Matches:");
    let matches =  pattern.search(&runner.egraph);
    runner.egraph.dot(&validation_fn).to_svg("/mnt/e/Junior/egg/viz.svg").unwrap();
    for eclass in matches.iter().map(|x| x.eclass) {
        println!("Searching for eclass {}", eclass);
        println!("{:?}", runner.egraph.find_nearest_expr(&eclass, None, &Box::new(validate_data)));
    }
}