
inductive T2
 | a : T2
 | b : T2
 | c (t : T2) : T2

def valid : T2 → Prop
  | .a => True
  | .b => True
  | .c t => match t with
    | .a => True
    | .b => False
    | _ => valid t

def T2Sub : Type := { t : T2 // valid t }

/--
error: Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  T
has type `Type` which does not have the necessary form.
---
error: (kernel) arg #2 of 'T.c' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in
inductive T : Type
 | a : T
 | b : T
 | c (t : T) : t ≠ T.a → T
