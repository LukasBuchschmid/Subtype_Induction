import SubtypeInduction.What_A_View

inductive CType
  | int  : CType
  | void : CType
  | arr (elem : CType) : CType

def Valid : CType → Prop
  | .int   => True
  | .void  => True
  | .arr t => match t with
    | .int  => True
    | .void => False
    | _     => Valid t

@[reducible]
def ValidCType : Type := { t : CType // Valid t }

@[view_ctor]
def ValidCType.a : ValidCType := ⟨CType.int, by dsimp [Valid]⟩

@[view_ctor]
def ValidCType.b : ValidCType := ⟨CType.void, by dsimp [Valid]⟩

@[view_ctor]
def ValidCType.c (a : ValidCType) (h : a.val ≠ CType.void) : ValidCType := ⟨CType.arr a.val, by dsimp [Valid]; split <;> first | trivial | contradiction | exact a.property⟩

theorem ValidProp (t : CType) : (Valid t.arr.arr) → (Valid t.arr) := by
  intro h
  unfold Valid at h
  exact h

theorem ImpliesNotb (t : CType) : (Valid t.arr) → t ≠ CType.void := by
  intro h h_t
  unfold Valid at h
  rw [h_t] at h
  exact h

@[view_cases]
def CType.cases (x : ValidCType) : PSum (x = ValidCType.a) (PSum (x = ValidCType.b) (Σ' a : ValidCType, Σ' h : (a.val ≠ CType.void), x = ValidCType.c a h)) :=
  match x with
    | ⟨CType.int, h⟩  => PSum.inl (Subtype.ext rfl)
    | ⟨CType.void, h⟩ => PSum.inr <| PSum.inl (Subtype.ext rfl)
    | ⟨CType.arr y, h⟩ => by
      have h_y : Valid y := by
        match y with
          | .int => exact h
          | .void => contradiction
          | .arr t => exact ValidProp t h
      have h_yn : y ≠ CType.void := ImpliesNotb y h
      have cElem : ValidCType := ValidCType.c ⟨y, h_y⟩ h_yn
      have eq : ⟨y.arr,h⟩ = ValidCType.c ⟨y, h_y⟩ h_yn := by
        apply Subtype.ext
        dsimp [ValidCType.c]
      exact PSum.inr <| PSum.inr ⟨⟨y,h_y⟩, h_yn, eq⟩

@[view_pos]
theorem cDecr (t : ValidCType) (h : t.val ≠ CType.void) : sizeOf t < sizeOf (t.c h) := by
  rcases t with ⟨val, prop⟩
  dsimp [ValidCType.c, sizeOf, Subtype._sizeOf_1, CType._sizeOf_1]
  omega


#What_A_View ValidCType

#check ValidCType.recView


/--
error: Invalid field notation: Field projection operates on types of the form `C ...` where C is a constant. The expression
  CType'
has type `Sort ?u.2` which does not have the necessary form.
---
error: (kernel) arg #2 of 'CType'.arr' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in
inductive CType'
  | int  : CType'                      -- a
  | void : CType'                     -- b
  | arr (elem : CType') : elem ≠ CType'.void → CType'        -- c
