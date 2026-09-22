import Lean
open Lean Elab Command Meta Term

-- A recursive function to build a dynamic chain of `withLocalDeclD`
-- `types`: The list of types we want as arguments
-- `idx`: A counter to generate unique names (arg_0, arg_1, etc.)
-- `fvars`: The array accumulating the created Free Variables
-- `bodyBuilder`: The function to execute once all variables are created
partial def buildLambdas (types : List Expr) (idx : Nat) (fvars : Array Expr)
  (bodyBuilder : Array Expr → MetaM Expr) : MetaM Expr := do

  -- HOLE 1: Implement the entire recursive CPS logic here.
  --
  -- Hints:
  -- 1. Pattern match on `types`.
  -- 2. Base case: If the list is empty, you are at the center of the maze.
  --    What do you do with `bodyBuilder`?
  -- 3. Recursive case: If you have a `currentType` and `remainingTypes`:
  --    - Create a name: `let argName := Name.mkSimple s!"arg_{idx}"`
  --    - Use `withLocalDeclD` to open a context for `currentType`.
  --    - INSIDE that context, add the new variable to your array and recursively
  --      call `buildLambdas` to keep going deeper.

  match types with
    | [] => bodyBuilder fvars
    | hd :: tl =>
        let argName := Name.mkSimple s!"arg_{idx}"
        withLocalDeclD argName hd fun newVar => do
          buildLambdas tl (idx + 1) (fvars.push newVar) bodyBuilder



-- The Command Parser
syntax "#Build_Multi_Arg " term* : command

-- We define the syntax and the elaboration rule in one clean step
elab "#Build_Multi_Arg " args:term,* : command => do
  liftTermElabM do
    let mut typeExprs : List Expr := []

    -- Because we used `elab`, `args` is automatically an array of syntax nodes!
    -- We don't need the $ anymore.
    for arg in args.getElems do
      let e ← Term.elabType arg
      typeExprs := typeExprs ++ [← instantiateMVars e]

        -- HOLE 2: Define the `bodyBuilder` closure.
        -- This function takes the fully populated `Array Expr` of variables
        -- that `buildLambdas` will eventually hand to it.
        -- It must return a `MetaM Expr`.
        -- Your job: Create a dummy string Expr, and wrap it in a lambda using `allVars`.
      let myBodyBuilder : Array Expr → MetaM Expr := fun allVars => do
        let dummyVal : Expr := mkStrLit "dummy"
        let lam ← mkLambdaFVars allVars dummyVal
        pure lam

      -- HOLE 3: Start the chain reaction.
      -- Call `buildLambdas` with the correct initial inputs to generate the final Expr.
      let finalFunction ← buildLambdas typeExprs 0 #[] myBodyBuilder

      logInfo m!"Successfully built: {finalFunction}"
