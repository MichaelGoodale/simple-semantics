use serde::ser::SerializeSeq;
use serde::{Serialize, ser};

use crate::lambda::LambdaExpr;
use crate::{lambda::RootedLambdaPool, language::Expr};

impl Serialize for RootedLambdaPool<Expr> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        /*
        let n = self.len();
        let mut s = serializer.serialize_seq(Some(n))?;
        for (x, d) in self.pool.bfs_from(self.root) {
            let x = self.get(x);
            s.serialize_element(x)
        }*/
        todo!();
    }
}
