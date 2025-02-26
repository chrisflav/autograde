import Lean

def Lean.ConstantInfo.getConstantVal? (info : ConstantInfo) : Option ConstantVal :=
  match info with
  | .thmInfo val => val.toConstantVal
  | .defnInfo val => val.toConstantVal
  | _ => none

def Lean.Name.isRelevant (name : Name) : Bool :=
  !((Lean.privateToUserName? name).getD name).isInternal
