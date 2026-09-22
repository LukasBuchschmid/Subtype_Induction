import Lean
open Lean Elab Command Meta Term

syntax "#Build_Dummy " term : command

elab_rules : command
  | `(#Build_Dummy $targetType) => do
      liftTermElabM do

        -- HOLE 1: Turn Syntax into an Expr
        -- You need to elaborate the raw syntax `$targetType` into a properly typed `Expr`.
        -- Hint: Look at the very beginning of your `#What_A_View` script to see how you did this.
        let e ← Term.elabType targetType

        Term.synthesizeSyntheticMVarsNoPostponing
        let typeExpr ← instantiateMVars e

        -- HOLE 2: The Return Value
        -- We want to return the string "dummy". We need an `Expr` representing a string literal.
        -- Hint: Lean has a built-in pure function for this named `mkStrLit`.
        let dummyVal : Expr := mkStrLit "dummy"

        -- HOLE 3 & 4: Building the Lambda
        -- We want to build: fun (x : typeExpr) => dummyVal
        -- `withLocalDeclD` creates a local variable named `x` of type `typeExpr`.
        let myFunction ← withLocalDeclD `x typeExpr fun xVar => do

          -- `xVar` is now an `Expr` representing your bound variable `x`.
          -- (If this wasn't a dummy function, this is where you would build PSum.casesOn using xVar)

          -- HOLE 3: Turn the body into a Lambda
          -- You need to bind `xVar` to `dummyVal` to create the final function.
          -- Hint: The function you need starts with `mkLambda` and takes an Array of variables.
          let lam ← mkLambdaFVars #[xVar] dummyVal

          -- HOLE 4: Return it
          -- We are in a monad (`do` block), so how do you return the `lam` you just built?
          pure lam

        -- Let's print it out!
        logInfo m!"Successfully built: {myFunction}"
