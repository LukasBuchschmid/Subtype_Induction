import Lean

open Lean Elab Command Meta


syntax "#What_A_View " ident "with" ident* "and" ident* : command


elab_rules : command
  | `(#What_A_View $targetType with $[$ctors]* and $[$thms]*) => do

    let typeExpr ← liftTermElabM do

      let e ← Term.elabType targetType
      return e


    logInfo m!"Successfully verified target is a type: {typeExpr}"

    let env ← getEnv



    for ctor in ctors do
      let ctorName := ctor.getId


      match env.find? ctorName with
      | some info =>
        let ctorType := info.type

        let ctorExpr := Expr.const ctorName (info.levelParams.map Level.param)

        logInfo m!"Verified function '{ctorName}' with type: {ctorType}"

      | none =>
        throwError m!"'{ctorName}' is not a valid existing name in the environment!"


    for thm in thms do
      let thmName := thm.getId
      logInfo m!"Found theorem : {thmName}"
