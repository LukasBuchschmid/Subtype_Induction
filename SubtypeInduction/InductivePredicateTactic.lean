import Lean

open Lean Elab Command Meta

syntax "#Induct_Pred_Recursor " ident : command

def findSubtypeApp (e : Expr) : Expr :=
  match e with
  | Expr.lam _ _ body _ => findSubtypeApp body
  | _ => e

elab_rules : command
  | `(#Induct_Pred_Recursor $targetType) => do

    let name := targetType.getId

    logInfo m!"Targeting subtype: {name}"

    liftTermElabM do

      let info <- getConstInfo name
      match info with
        | ConstantInfo.defnInfo defInfo =>
          let actualBody := defInfo.value
          logInfo m!"{actualBody}"
          let subType := findSubtypeApp actualBody
          logInfo m!"{subType}"
          let testSubType := subType.isAppOf ``Subtype
          logInfo m!"{testSubType}"
          let SubTypeArgs := subType.getAppArgs
          logInfo m!"{SubTypeArgs}"
          -- currently unsafe, need to throw an error if we don't have a Subtype app
          let Property := SubTypeArgs[1]!
          logInfo m!"{Property}"
          let ActProperty := findSubtypeApp Property
          let PropertyFun := ActProperty.getAppFn
          let FunName := PropertyFun.constName
          logInfo m!"{FunName}"
          let FunInfo <- getConstInfo FunName
          match FunInfo with
          | ConstantInfo.inductInfo indInfo =>
            logInfo m!"Success! It is inductive!"
            logInfo m!"{indInfo.ctors}"
            for ctorName in indInfo.ctors do

            let ctorInfo ← getConstInfo ctorName
            let rawCtorType := ctorInfo.type

            logInfo m!"Constructor {ctorName} has raw type:\n{rawCtorType}"
          | _ =>
            logError m!"The predicate is not inductive."
          let recName := Name.str FunName "rec"
          logInfo m!"The recursor name is: {recName}"
          let recInfo ← getConstInfo recName
          logInfo m!"Successfully found the recursor! Its type signature is: {recInfo.type}"
        | _ =>
          logError m!"Expected {name} to be a definition but it was something elese."
