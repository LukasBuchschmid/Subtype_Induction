
inductive BTree (α : Type) where
  | empty : BTree α
  | node (a : α) (l r : BTree α) : BTree α


abbrev NatTree := BTree Nat

def ForallTreeNat (P : Nat → Prop) : NatTree → Prop
  | .empty => True
  | .node x l r => P x ∧ ForallTreeNat P l ∧ ForallTreeNat P r

-- This should not work, since the predicate is truly global and we can therefore not give any working constructors
--
def IsBST_standard : NatTree → Prop
  | .empty => True
  | .node x l r =>
      ForallTreeNat (fun y => y < x) l ∧
      ForallTreeNat (fun y => x < y) r ∧
      IsBST_standard l ∧
      IsBST_standard r

def BST_Standard := { t : NatTree // IsBST_standard t }

def BST_Standard.empty : BST_Standard := ⟨BTree.empty, by trivial⟩

def BST_Standard.step (n : Nat) (l : BST_Standard) (r: BST_Standard) (pl : ForallTreeNat (fun y => y < n) l.val)
    (pr : ForallTreeNat (fun y => n < y) r.val) : BST_Standard := by
        let tree := BTree.node n l.val r.val
        let proof : IsBST_standard (BTree.node n l.val r.val) := by
            unfold IsBST_standard
            exact ⟨pl, pr, l.property, r.property⟩
        exact ⟨tree, proof⟩

def BST_Standard.rec2 {motive : BST_Standard → Sort u} (empty : motive BST_Standard.empty)
    (step : (n : Nat) → (l : BST_Standard) → (r: BST_Standard) → (pl : ForallTreeNat (fun y => y < n) l.val) →
    (pr : ForallTreeNat (fun y => n < y) r.val) → motive (BST_Standard.step n l r pl pr)) (t : BST_Standard) : motive t :=



inductive IsBoundedBST : Option Nat → Option Nat → NatTree → Prop where
  | empty {min max : Option Nat} :
      IsBoundedBST min max .empty

  | node (x : Nat) (l r : NatTree) {min max : Option Nat}
      (h_min : ∀ m, min = some m → m < x)
      (h_max : ∀ M, max = some M → x < M)
      (hl : IsBoundedBST min (some x) l)
      (hr : IsBoundedBST (some x) max r) :
      IsBoundedBST min max (.node x l r)

def IsBST_bounded (t : NatTree) : Prop :=
  IsBoundedBST none none t

def BST_Bounded := { t : NatTree // IsBST_bounded t }


inductive IsFull {α : Type} : BTree α → Prop where
| empty : IsFull BTree.empty
| node (a : α) (l r : BTree α)
    (hl : IsFull l) (hr : IsFull r)
    (hiff : l = BTree.empty ↔ r = BTree.empty) :
    IsFull (BTree.node a l r)
