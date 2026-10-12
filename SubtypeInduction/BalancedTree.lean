import SubtypeInduction.What_A_View

inductive Tree
  | leaf
  | node (l r : Tree)
  deriving Repr

def Tree.height : Tree → Nat
  | .leaf => 0
  | .node l r => max l.height r.height + 1

def Tree.size : Tree → Nat
  | .leaf => 1
  | .node l r => l.size + r.size + 1

def IsBalanced : Tree → Prop
  | .leaf => True
  | .node l r =>
      IsBalanced l ∧
      IsBalanced r ∧
      Int.natAbs (l.height - r.height) ≤ 1

def BalancedTree := { t : Tree // IsBalanced t }

def BalancedTree.leaf : BalancedTree := ⟨.leaf, trivial⟩

def BalancedTree.node (l r : BalancedTree)
    (h : Int.natAbs (l.val.height - r.val.height) ≤ 1) : BalancedTree :=
  ⟨.node l.val r.val, ⟨l.property, r.property, h⟩⟩

theorem node_left_smaller (l r : BalancedTree) (h : Int.natAbs (l.val.height - r.val.height) ≤ 1) :
    l.val.size < (BalancedTree.node l r h).val.size := by
  dsimp [BalancedTree.node, Tree.size]
  omega

theorem node_right_smaller (l r : BalancedTree) (h : Int.natAbs (l.val.height - r.val.height) ≤ 1) :
    r.val.size < (BalancedTree.node l r h).val.size := by
  dsimp [BalancedTree.node, Tree.size]
  omega

def balanced_cases (x : BalancedTree) :
    PSum (x = BalancedTree.leaf)
         (Σ' l : BalancedTree, Σ' r : BalancedTree, Σ' h : Int.natAbs (l.val.height - r.val.height) ≤ 1, x = BalancedTree.node l r h) :=
  match x with
  | ⟨.leaf, h⟩ => PSum.inl (Subtype.ext rfl)
  | ⟨.node l r, h⟩ =>
    let lb : BalancedTree := ⟨l, h.1⟩
    let rb : BalancedTree := ⟨r, h.2.1⟩
    let hb : Int.natAbs (lb.val.height - rb.val.height) ≤ 1 := h.2.2
    PSum.inr ⟨lb, rb, hb, Subtype.ext rfl⟩

#What_A_View BalancedTree with
  BalancedTree.leaf BalancedTree.node
plus
  node_left_smaller node_right_smaller
cases
  balanced_cases
through
  (measure (fun t => t.val.size))

#check BalancedTree.recView



-- ============================================================================
-- Exercises
-- ============================================================================

/-- Exercise 1: Write a function that mirrors a balanced tree (swaps left and right children).
Hint: You can use `induction t using BalancedTree.recView` to build this!
You will need to prove that `Int.natAbs (r.height - l.height) ≤ 1`, which you can do with `omega`. -/
noncomputable def BalancedTree.mirror (t : BalancedTree) : BalancedTree := by
  induction t using BalancedTree.recView with
  | case_1 => exact BalancedTree.leaf
  | case_2 l r h ih_l ih_r => exact BalancedTree.node r l (by omega)

theorem mirror_leaf : (BalancedTree.leaf).mirror = BalancedTree.leaf := by
  unfold BalancedTree.mirror BalancedTree.recView
  rw [WellFounded.fix_eq]
  dsimp [balanced_cases, BalancedTree.leaf]

theorem mirror_node (l r : BalancedTree) (h : Int.natAbs (l.val.height - r.val.height) ≤ 1) :
    (BalancedTree.node l r h).mirror = BalancedTree.node r l (by omega) := by
  unfold BalancedTree.mirror BalancedTree.recView
  rw [WellFounded.fix_eq]
  dsimp [balanced_cases, BalancedTree.node]

/-- Exercise 2: Prove that mirroring a balanced tree doesn't change its height. -/
theorem mirror_height (t : BalancedTree) : (t.mirror).val.height = t.val.height := by
  induction t using BalancedTree.recView with
  | case_1 =>
    rw [mirror_leaf]
  | case_2 l r h ih_l ih_r =>
    rw [mirror_node]
    dsimp [BalancedTree.node, Tree.height]
    omega

/-- Exercise 3: Prove that the height of a balanced tree is always ≤ its size.
Hint: `omega` knows how to handle `max`! -/
theorem height_le_size (t : BalancedTree) : t.val.height ≤ t.val.size := by
  induction t using BalancedTree.recView with
  | case_1 =>
    change (BalancedTree.leaf).val.height ≤ (BalancedTree.leaf).val.size
    dsimp [BalancedTree.leaf, Tree.height, Tree.size]
    omega
  | case_2 l r h ih_l ih_r =>
    change (BalancedTree.node l r h).val.height ≤ (BalancedTree.node l r h).val.size
    dsimp [BalancedTree.node, Tree.height, Tree.size]
    omega
