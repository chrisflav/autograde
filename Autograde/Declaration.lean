import Lean
import Batteries

open Lean Elab Command

deriving instance Repr for ConstantVal
deriving instance Hashable for ConstantVal

structure DeclInfo where
  name : Name
  type : Expr
  axiomsUsed : Array (Name × List ConstantVal)
  tacticsUsed : Array Name
deriving BEq, Hashable, Repr

instance : ToString DeclInfo where
  toString := toString ∘ repr
