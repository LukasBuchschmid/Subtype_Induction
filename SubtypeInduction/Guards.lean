import SubtypeInduction.What_A_View


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

@[reducible]
def T2Sub : Type := { t : T2 // valid t }

@[view_ctor]
def T2Sub.a : T2Sub := ⟨T2.a, by dsimp [valid]⟩

@[view_ctor]
def T2Sub.b : T2Sub := ⟨T2.b, by dsimp [valid]⟩

@[view_ctor]
def T2Sub.c (a : T2Sub) (h : a.val ≠ T2.b) : T2Sub := ⟨T2.c a.val, by dsimp [valid]; split <;> first | trivial | contradiction | exact a.property⟩

theorem validProp (t : T2) : (valid t.c.c) → (valid t.c) := by
  intro h
  unfold valid at h
  exact h

theorem ImpliesNotb (t : T2) : (valid t.c) → t ≠ T2.b := by
  intro h h_t
  unfold valid at h
  rw [h_t] at h
  exact h

@[view_cases]
def T2cases (x : T2Sub) : PSum (x = T2Sub.a) (PSum (x = T2Sub.b) (Σ' a : T2Sub, Σ' h : (a.val ≠ T2.b), x = T2Sub.c a h)) :=
  match x with
    | ⟨T2.a, h⟩  => PSum.inl (Subtype.ext rfl)
    | ⟨T2.b, h⟩ => PSum.inr <| PSum.inl (Subtype.ext rfl)
    | ⟨T2.c y, h⟩ => by
      have h_y : valid y := by
        match y with
          | .a => exact h
          | .b => contradiction
          | .c t => exact validProp t h
      have h_yn : y ≠ T2.b := ImpliesNotb y h
      have cElem : T2Sub := T2Sub.c ⟨y, h_y⟩ h_yn
      have eq : ⟨y.c,h⟩ = T2Sub.c ⟨y, h_y⟩ h_yn := by
        apply Subtype.ext
        dsimp [T2Sub.c]
      exact PSum.inr <| PSum.inr ⟨⟨y,h_y⟩, h_yn, eq⟩

@[view_pos]
theorem cDecr (t : T2Sub) (h : t.val ≠ T2.b) : sizeOf t < sizeOf (t.c h) := by
  rcases t with ⟨val, prop⟩
  dsimp [T2Sub.c, sizeOf, Subtype._sizeOf_1, T2._sizeOf_1]
  omega


#What_A_View T2Sub

#check T2Sub.recView



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
