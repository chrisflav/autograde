import Lean
import Batteries

open Lean Elab Command

structure DeclInfo where
  name : Name
  type : Expr
  axiomsUsed : Array Name
  tacticsUsed : Array Name
deriving BEq, Hashable, Repr

instance : ToString DeclInfo where
  toString := toString ∘ repr
