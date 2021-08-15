use egg::*;
use std::cmp::Ordering;

type BuildHasher = fxhash::FxBuildHasher;
type HashSet<K> = hashbrown::HashSet<K, BuildHasher>;
type EG = egg::EGraph<TestLang, TestLangAnalysis>;
type Expr = RecExpr<TestLang>;
type MatchPat = Pattern<TestLang>;

define_language! {
    pub enum TestLang {
        "relu"     = ReLu([Id; 1]),
        "bias_add" = BiasAdd([Id; 2]),
        "dense"    = Dense([Id; 2]),
        "add"      = Add([Id; 2]),
        "reshape"  = Reshape([Id; 2]),
        "shape"    = Shape(Box<[Id]>),
        "flex-linear" = FlexLinear([Id; 3]),
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

fn patterns() -> Vec<egg::Rewrite<TestLang, TestLangAnalysis>> {
    vec! [
        rewrite!("linear-layer"; "(bias_add (dense ?x ?w) ?b)" => "(flex-linear ?x ?w ?b)")
    ]
}

fn linear_layer() -> RecExpr<TestLang> {
    "(add (reshape (dense x w) (shape 1 4 4)) b)".parse().unwrap()
}

fn stacked_linear() -> RecExpr<TestLang> {
    "(add 
        (reshape
            (dense 
                (relu (add (reshape (dense x w) (shape 1 4 4)) b))
                w2)
            (shape 1 32 32)) b2)".parse().unwrap()
}

#[test]
fn linear_rewrite() {
    let expr : Expr = stacked_linear();
    // let pattern : MatchPat = "(bias_add (dense ?x ?w) ?b)".parse().unwrap();
    let mut egraph = EG::new(TestLangAnalysis {});
    egraph.toggle_tag_original(true);
    let id = egraph.add_expr(&expr);
    egraph.toggle_tag_original(false);
    egraph.rebuild();
    egraph.dot(&validation_fn).to_svg("/mnt/e/Junior/egg/model.svg").unwrap();
    let mut rws = rewrites();
    rws.extend(patterns());
    let runner = Runner::<_, _, ()>::new(TestLangAnalysis {}).with_egraph(egraph).run(&rws);
    println!("Matches:");
    runner.egraph.dot(&validation_fn).to_svg("/mnt/e/Junior/egg/viz.svg").unwrap();
    println!("{}", runner.egraph.record().to_record_instructions(id));
    // let matches =  pattern.search(&runner.egraph);
    // for eclass in matches.iter().map(|x| x.eclass) {
    //     println!("Searching for eclass {}", eclass);
    //     println!("{:?}", runner.egraph.find_nearest_expr(&eclass, None, &Box::new(validate_data)));
    // }
}