use std::fmt::{self, Debug};
use std::hash::Hash;
use std::rc::Rc;

use smallvec::SmallVec;
use symbolic_expressions::Sexp;

use crate::unionfind::UnionFind;

/// The type of an eclass id in the [`EGraph`](struct.EGraph.html)
pub type Id = u32;

/// An operator from the user-defined [`Language`] with some children.
///
/// An [`ENode`] is operator from the user-provided [`Language`] with
/// zero or more children.
/// Note that [`ENode`] is generic over both the [`Language`] and the
/// type of the children.
/// In the typical setting (inside and [`EClass`]), the children of an
/// [`ENode`] are elcass [`Id`]s, so the second generic parameter
/// defaults to [`Id`].
/// In other cases ([cost functions][cf] or [metadata]), the generic
/// parameter may be something else.
///
/// [`EGraph`]: struct.EGraph.html
/// [`EClass`]: struct.EClass.html
/// [`ENode`]: struct.ENode.html
///
/// [`Id`]: type.Id.html
/// [`Language`]: trait.Language.html
/// [cf]: trait.CostFunction.html
/// [metadata]: trait.Metadata.html
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct ENode<O, Child = Id> {
    /// The operator from the user-defined [`Language`](trait.Language.html)
    pub op: O,
    /// The children of the [`ENode`](struct.ENode.html).
    /// In most cases, the child type is [`Id`](type.Id.html).
    pub children: SmallVec<[Child; 2]>,
}

type Inner<L> = ENode<L, RecExpr<L>>;

/// A recursive expression from a user-defined [`Language`].
///
/// This is type is essentially an [`ENode`] whose children are
/// [`RecExpr`]s. This is resource counted with [`Rc`], so it's cheap
/// to clone.
///
/// If the `serde-1` feature is enabled, this implements
/// [`serde::Serialize`][ser] by pretty-printing with
/// [`self.pretty(80)`][pretty].
///
/// [`ENode`]: struct.ENode.html
/// [`RecExpr`]: struct.RecExpr.html
/// [`Language`]: trait.Language.html
/// [ser]: https://docs.rs/serde/latest/serde/trait.Serialize.html
/// [pretty]: struct.RecExpr.html#method.pretty
/// [`Rc`]: https://doc.rust-lang.org/std/rc/struct.Rc.html
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct RecExpr<L> {
    rc: Rc<Inner<L>>,
}

#[cfg(feature = "serde-1")]
impl<L: Language + fmt::Display> serde::Serialize for RecExpr<L> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        // 3 is the number of fields in the struct.
        let s = self.pretty(80);
        serializer.serialize_str(&s)
    }
}

impl<L> From<Inner<L>> for RecExpr<L> {
    fn from(inner: Inner<L>) -> Self {
        let rc = Rc::new(inner);
        RecExpr { rc }
    }
}

impl<L> std::borrow::Borrow<Inner<L>> for RecExpr<L> {
    fn borrow(&self) -> &Inner<L> {
        &self.rc
    }
}

impl<L> AsRef<Inner<L>> for RecExpr<L> {
    fn as_ref(&self) -> &Inner<L> {
        &self.rc
    }
}

impl<L: Language + fmt::Display> RecExpr<L> {
    fn to_sexp(&self) -> Sexp {
        let e = self.as_ref();
        let mut vec: Vec<_> = e.children.iter().map(Self::to_sexp).collect();
        let op = Sexp::String(e.op.to_string());
        if vec.is_empty() {
            op
        } else {
            vec.insert(0, op);
            Sexp::List(vec)
        }
    }

    /// Pretty print with a maximum line length.
    ///
    /// This gives you a nice, indented, pretty-printed s-expression.
    ///
    /// # Example
    /// ```
    /// # use egg::*;
    /// define_language! {
    ///     enum FooLanguage {
    ///         Num(i32),
    ///         Add = "+",
    ///         Mul = "*",
    ///         Symbol(String),
    ///     }
    /// }
    ///
    /// let e: RecExpr<FooLanguage> = "(* (+ 2 2) (+ x y))".parse().unwrap();
    /// assert_eq!(e.pretty(10), "
    /// (*
    ///   (+ 2 2)
    ///   (+ x y))
    /// ".trim());
    /// ```
    pub fn pretty(&self, width: usize) -> String {
        use std::fmt::{Result, Write};
        let sexp = self.to_sexp();

        fn pp(buf: &mut String, sexp: &Sexp, width: usize, level: usize) -> Result {
            if let Sexp::List(list) = sexp {
                let indent = sexp.to_string().len() > width;
                write!(buf, "(")?;

                for (i, val) in list.iter().enumerate() {
                    if indent && i > 0 {
                        writeln!(buf)?;
                        for _ in 0..level {
                            write!(buf, "  ")?;
                        }
                    }
                    pp(buf, val, width, level + 1)?;
                    if !indent && i < list.len() - 1 {
                        write!(buf, " ")?;
                    }
                }

                write!(buf, ")")?;
                Ok(())
            } else {
                // I don't care about quotes
                write!(buf, "{}", sexp.to_string().trim_matches('"'))
            }
        }

        let mut buf = String::new();
        pp(&mut buf, &sexp, width, 1).unwrap();
        buf
    }
}

impl<L: Language, Child> ENode<L, Child> {
    /// Create a new [`ENode`] with no children.
    /// Equivalent to calling [`ENode::new`](#method.new) with no
    /// children.
    ///
    /// [`ENode`]: struct.ENode.html
    #[inline(always)]
    pub fn leaf(op: L) -> Self {
        ENode::new(op, vec![])
    }

    /// Create a new [`ENode`].
    ///
    /// [`ENode`]: struct.ENode.html
    #[inline(always)]
    pub fn new<I>(op: L, children: I) -> Self
    where
        I: IntoIterator<Item = Child>,
    {
        let children = children.into_iter().collect();
        ENode { op, children }
    }

    /// Try to create an [`ENode`] with a falliable child iterator.
    ///
    /// # Example
    /// ```
    /// # use egg::*;
    /// define_language! {
    ///     enum Math {
    ///         Num(i32),
    ///         Add = "+",
    ///         Mul = "*",
    ///     }
    /// }
    ///
    /// // This is obviously silly, but maybe you have some more
    /// // complex function
    /// fn non_neg(i: i32) -> Result<u32, String> {
    ///     if i >= 0 {
    ///         Ok(i as u32)
    ///     } else {
    ///         Err(format!("{} is less than 0", i))
    ///     }
    /// }
    /// let r1: Result<ENode<Math, u32>, String> = ENode::try_new(
    ///     Math::Add,
    ///     vec![non_neg(1), non_neg(8)]
    /// );
    /// let r2: Result<ENode<Math, u32>, String> = ENode::try_new(
    ///     Math::Add,
    ///     vec![non_neg(-1), non_neg(8)]
    /// );
    /// assert_eq!(r1, Ok(enode!(Math::Add, 1, 8)));
    /// assert_eq!(r2, Err("-1 is less than 0".into()));
    /// ```
    ///
    /// [`ENode`]: struct.ENode.html
    #[inline(always)]
    pub fn try_new<Error, I>(op: L, children: I) -> Result<Self, Error>
    where
        I: IntoIterator<Item = Result<Child, Error>>,
    {
        let c: Result<_, Error> = children.into_iter().collect();
        c.map(|children| ENode { op, children })
    }

    /// Create a new [`ENode`] by mapping a function over the children.
    ///
    /// `enode.map_children(f)` is equivalent to:
    /// ```
    /// # use egg::*;
    /// # let enode = ENode::<String, i32>::leaf("h".into());
    /// # let f = |x| x;
    /// # assert_eq!(enode,
    /// ENode::new(
    ///     enode.op.clone(),
    ///     enode.children.iter().cloned().map(f),
    /// )
    /// # );
    /// ```
    ///
    /// [`ENode`]: struct.ENode.html
    #[inline(always)]
    pub fn map_children<Child2, F>(&self, mut f: F) -> ENode<L, Child2>
    where
        Child: Clone,
        F: FnMut(Child) -> Child2,
    {
        let some_f = |child| Result::<Child2, std::convert::Infallible>::Ok(f(child));
        self.map_children_result(some_f).unwrap()
    }

    /// Create a new [`ENode`] by mapping a falliable function over
    /// the children.
    ///
    /// `enode.map_children_result(f)` is equivalent to:
    /// ```
    /// # use egg::*;
    /// # let enode = ENode::<String, i32>::leaf("h".into());
    /// # let f = |x| -> Result<i32, ()> { Ok(x) };
    /// # assert_eq!(enode,
    /// ENode::try_new(
    ///     enode.op.clone(),
    ///     enode.children.iter().cloned().map(f),
    /// )
    /// # .unwrap());
    /// ```
    ///
    /// [`ENode`]: struct.ENode.html
    #[inline(always)]
    pub fn map_children_result<Child2, F, Error>(&self, f: F) -> Result<ENode<L, Child2>, Error>
    where
        Child: Clone,
        F: FnMut(Child) -> Result<Child2, Error>,
    {
        ENode::try_new(self.op.clone(), self.children.iter().cloned().map(f))
    }
}

impl<L: Language> ENode<L> {
    pub(crate) fn update_ids<V>(&self, unionfind: &UnionFind<Id, V>) -> Self {
        self.map_children(|id| unionfind.find(id))
    }
}

/// Trait defines a Language whose terms will be in the [`EGraph`].
///
/// Typically, you'll want your language to implement [`FromStr`] and
/// [`Display`] so parsing and printing works.
/// Check out the [`define_language!`] macro for an easy way to create
/// a [`Language`].
///
/// [`String`] implements [`Language`] for quick use cases.
///
/// [`define_language!`]: macro.define_language.html
/// [`Language`]: trait.Language.html
/// [`EGraph`]: struct.EGraph.html
/// [`String`]: https://doc.rust-lang.org/std/string/struct.String.html
/// [`FromStr`]: https://doc.rust-lang.org/std/str/trait.FromStr.html
/// [`Display`]: https://doc.rust-lang.org/std/fmt/trait.Display.html
pub trait Language: Debug + Ord + Hash + Clone + 'static {}

impl Language for String {}
