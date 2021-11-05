use crate::{Analysis, EGraph, Id, Language};
use std::fmt::Display;

pub struct RecordConstructor<'a, L: Language, N: Analysis<L>> {
    pub(crate) egraph: &'a EGraph<L, N>,
}

impl<'a, L: Language + Display, N: Analysis<L>> RecordConstructor<'a, L, N> {
    pub fn to_record_instructions(&self, root: Id) -> String {
        let mut result = String::from("");
        self.set_size(&mut result, self.egraph.classes().len());
        self.set_root(&mut result, root);
        for eclass in self.egraph.classes() {
            self.begin_eclass(&mut result, Id::from(eclass.id));
            for node in eclass.iter() {
                self.add_enode(&mut result, node);
            }
            self.end_eclass(&mut result);
        }
        format!("{}\nFIN", result)
    }

    fn set_symbol(&self, s: &mut String, symbol: String) {
        s.push_str(&format!("BEGIN_SYMBOL {} END_SYMBOL\n", symbol)[..]);
    }

    fn add_enode(&self, s: &mut String, node: &L) {
        s.push_str("BEGIN_ENODE\n");
        self.set_symbol(s, node.to_string());
        if node.children().len() > 0 {
            s.push_str("BEGIN_CHILDREN ");
            node.for_each(|ch| s.push_str(&format!("{} ", ch)[..]));
            s.push_str("\nEND_CHILDREN\n");
        }
        s.push_str("END_ENODE\n");
    }

    fn begin_eclass(&self, s: &mut String, id: Id) {
        s.push_str(&format!("{} {}\n", "ECLASS", id)[..]);
    }

    fn end_eclass(&self, s: &mut String) {
        s.push_str(&format!("{}\n", "END_ECLASS")[..]);
    }

    fn set_root(&self, s: &mut String, root: Id) {
        s.push_str(&format!("ROOT {}\n", root));
    }

    fn set_size(&self, s: &mut String, size: usize) {
        s.push_str(&format!("SIZE {}\n", size)[..]);
    }
}
