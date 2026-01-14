/-
  Treaps

-/

import Projects.Treap.time
import Projects.Treap.perm

import Mathlib
import Mathlib.Tactic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.BigOperators

namespace TreapLogic
open Tree

/-
  Base Treap definitions and properties

  We use explicit type variables for functions. structures and abbrevs are defined implicitely
  LinearOrder is required for both Key and Prio types to enable comparisons
-/
variable {Key : Type} [LinearOrder Key]
variable {Prio : Type} [LinearOrder Prio]

-- A single Treap Node Type
structure KeyPrioPair (Key : Type) (Prio : Type) [LinearOrder Key] [LinearOrder Prio] where
  key : Key
  prio : Prio

-- Abbreviation for a TreapNode, which is a Tree of KeyPrioPairs
abbrev TreapNode (Key : Type) (Prio : Type) [LinearOrder Key] [LinearOrder Prio] := Tree (KeyPrioPair Key Prio)

-- Getter for root node key-priority pair
def TreapNode.root : TreapNode Key Prio → Option (KeyPrioPair Key Prio)
  | Tree.nil => none
  | Tree.node (kp : KeyPrioPair Key Prio) _ _ => some kp

-- Getter for root node key
def TreapNode.key : TreapNode Key Prio → Option Key
  | Tree.nil => none
  | Tree.node (kp : KeyPrioPair Key Prio) _ _ => some kp.key

-- Getter for root node priority
def TreapNode.prio : TreapNode Key Prio → Option Prio
  | Tree.nil => none
  | Tree.node (kp : KeyPrioPair Key Prio) _ _ => some kp.prio

-- Getter for all nodes
def TreapNode.all_nodes : TreapNode Key Prio → Set (KeyPrioPair Key Prio)
  | Tree.nil => ∅
  | Tree.node (kp : KeyPrioPair Key Prio) l r => (all_nodes l) ∪ {kp} ∪ (all_nodes r)

-- Getter for all keys in the treap
def TreapNode.all_keys : TreapNode Key Prio → Set Key
  | Tree.nil => ∅
  | Tree.node (kp : KeyPrioPair Key Prio) l r => (all_keys l) ∪ {kp.key} ∪ (all_keys r)

-- Getter for all priorities in the treap
def TreapNode.all_prios : TreapNode Key Prio → Set Prio
  | Tree.nil => ∅
  | Tree.node (kp : KeyPrioPair Key Prio) l r => (all_prios l) ∪ {kp.prio} ∪ (all_prios r)

-- Useful methods, self explanatory
def TreapNode.all_keys_left : TreapNode Key Prio → Set Key
  | Tree.nil => ∅
  | Tree.node _ l _ => all_keys l

def TreapNode.all_keys_right : TreapNode Key Prio → Set Key
  | Tree.nil => ∅
  | Tree.node _ _ r => all_keys r

def TreapNode.all_prios_left : TreapNode Key Prio → Set Prio
  | Tree.nil => ∅
  | Tree.node _ l _ => all_prios l

def TreapNode.all_prios_right : TreapNode Key Prio → Set Prio
  | Tree.nil => ∅
  | Tree.node _ _ r => all_prios r

-- Example usage of all_keys
example :
  let t := Tree.node (KeyPrioPair.mk (5 : ℕ) (10 : ℕ))
                     (Tree.node (KeyPrioPair.mk (3 : ℕ) (20 : ℕ)) Tree.nil Tree.nil)
                     (Tree.node (KeyPrioPair.mk (7 : ℕ) (15 : ℕ)) Tree.nil Tree.nil)
  TreapNode.all_keys t = {3, 5, 7} := by
  simp [TreapNode.all_keys]
  ext; simp; tauto

/-
  Treap properties

-/

-- BST property
inductive IsBST : (TreapNode Key Prio) → Prop
  | nil : IsBST Tree.nil
  | node (tn : KeyPrioPair Key Prio) (l r : TreapNode Key Prio) :
    -- Require all keys in left subtree < current node key
    (∀ k, k ∈ l.all_keys → k < tn.key) →
    -- Require all keys in right subtree ≥ current node key
    (∀ k, k ∈ r.all_keys → tn.key ≤ k) →
    -- Recursively require left and right subtrees to also satisfy BST property
    IsBST l →
    IsBST r →
    -- Conclude that the current node satisfies the BST property
    IsBST (Tree.node tn l r)

-- Heap property
inductive IsHeap : (TreapNode Key Prio) → Prop
  | nil : IsHeap Tree.nil
  | node (tn : KeyPrioPair Key Prio) (l r : TreapNode Key Prio) :
    -- Require priority of current node to be >= priorities of all left and right subtrees (stricter but easier to prove)
    (∀ p, p ∈ l.all_prios → p ≤ tn.prio) →
    (∀ p, p ∈ r.all_prios → p ≤ tn.prio) →
    -- Recursively require left and right subtrees to also satisfy heap property
    IsHeap l →
    IsHeap r →
    -- Conclude that the current node satisfies the heap property
    IsHeap (Tree.node tn l r)

-- Treap property: both BST and Heap properties
def IsTreap (tn : TreapNode Key Prio) : Prop :=
  IsHeap tn ∧ IsBST tn

-- Treap structure contains treap properties + the data
structure Treap (Key : Type) (Prio : Type) [LinearOrder Key] [LinearOrder Prio] where
  root : TreapNode Key Prio
  is_treap : IsTreap root

/-
  Base methods

  We define all methods on TreapNodes, then migrate them to Treaps, proving their correctness there
-/

-- If the treap node is empty
def TreapNode.isEmpty (tn : TreapNode Key Prio) : Bool :=
  match tn with
  | Tree.nil => true
  | _ => false

-- Builder for singleton treap nodes
def TreapNode.singleton (kp : KeyPrioPair Key Prio) : TreapNode Key Prio :=
  Tree.node kp Tree.nil Tree.nil

-- Get the leftmost key in the treap
def TreapNode.leftmost (tn : TreapNode Key Prio) : Option (KeyPrioPair Key Prio) :=
  match tn with
  | Tree.nil => none
  | Tree.node kp l _ =>
    match l with
    | Tree.nil => some kp
    | Tree.node _ _ _ => TreapNode.leftmost l

-- Split the treap in two disjoint treaps, at key value k
-- Cartesian product to return pair of values
def TreapNode.split (tn : TreapNode Key Prio) (k : Key) : TreapNode Key Prio × TreapNode Key Prio :=
  match tn with
  | Tree.nil => (Tree.nil, Tree.nil)
  | Tree.node kp l r =>
    if kp.key < k then
      -- Root goes left, split right
      let (split_l, new_r) := TreapNode.split r k
      -- Return a (l, split_l) treap and a (new_r) treap
      let new_l := Tree.node kp l split_l
      (new_l, new_r)
    else
      -- Root goes right, split left
      let (new_l, split_r) := TreapNode.split l k
      -- Return (new_l) treap and (split_r, r) treap
      let new_r := Tree.node kp split_r r
      (new_l, new_r)

-- Alternative split, to split with l ≤ k < r
-- This is used for inserts/deletes
def TreapNode.splitUpper (tn : TreapNode Key Prio) (k : Key) : TreapNode Key Prio × TreapNode Key Prio :=
  match tn with
  | Tree.nil => (Tree.nil, Tree.nil)
  | Tree.node kp l r =>
    if kp.key ≤ k then
      -- Root goes left, split right
      let (split_l, new_r) := TreapNode.splitUpper r k
      -- Return a (l, split_l) treap and a (new_r) treap
      let new_l := Tree.node kp l split_l
      (new_l, new_r)
    else
      -- Root goes right, split left
      let (new_l, split_r) := TreapNode.splitUpper l k
      -- Return (new_l) treap and (split_r, r) treap
      let new_r := Tree.node kp split_r r
      (new_l, new_r)

-- Merge two sorted, disjoint treaps
def TreapNode.merge (l r : TreapNode Key Prio) : TreapNode Key Prio :=
  match l, r with
  | Tree.nil, Tree.nil => Tree.nil
  | Tree.nil, Tree.node _ _ _ => r
  | Tree.node _ _ _, Tree.nil => l
  | Tree.node kp_1 l_1 r_1, Tree.node kp_2 l_2 r_2 =>
    -- We have to choose the root, use priorities
    if kp_1.prio ≥ kp_2.prio then
      -- Left goes as root
      let new_l := l_1
      let new_r := TreapNode.merge r_1 (Tree.node kp_2 l_2 r_2)
      Tree.node kp_1 new_l new_r
    else
      -- Right as root
      let new_l := TreapNode.merge (Tree.node kp_1 l_1 r_1) l_2
      let new_r := r_2
      Tree.node kp_2 new_l new_r

/-
  Operations correctness - Ensure every operation which creates a new treap satisfies the treap properties

-/

/-
  Helpers
-/

-- All elems on the left are < all elems on the right
lemma left_lt_right (tn : TreapNode Key Prio) (bst_prop : IsBST tn) :
  ∀ lk ∈ tn.all_keys_left, ∀ rk ∈ tn.all_keys_right, lk < rk := by
  match tn with
  | Tree.nil => simp [TreapNode.all_keys_left]
  | Tree.node kp l r =>
    simp [TreapNode.all_keys_left, TreapNode.all_keys_right]
    -- Expand bst_prop
    cases bst_prop; rename_i bst_l left_l_key bst_r right_ge_key
    grind

-- Merging two treaps results in all keys being the union of both
theorem all_keys_union_merge (l r : TreapNode Key Prio) :
  l.all_keys ∪ r.all_keys = (TreapNode.merge l r).all_keys := by
  fun_induction TreapNode.merge
  · rw [Set.union_self]
  · simp [TreapNode.all_keys]
  · simp [TreapNode.all_keys]
  · expose_names
    simp only [TreapNode.all_keys]
    rw [←ih1]
    subst new_l -- delete alias
    nth_rw 1 [TreapNode.all_keys]
    nth_rw 2 [←Set.union_assoc]
  · expose_names
    simp only [TreapNode.all_keys]
    rw [←ih1]
    subst new_r -- delete alias
    nth_rw 1 [TreapNode.all_keys]
    repeat rw [←Set.union_assoc]

-- Merging treaps merges the priorities too
theorem all_prios_union_merge (l r : TreapNode Key Prio) :
  l.all_prios ∪ r.all_prios = (TreapNode.merge l r).all_prios := by
  match l, r with
  | Tree.nil, Tree.nil
  | Tree.nil, Tree.node _ _ _
  | Tree.node _ _ _, Tree.nil => simp_all [TreapNode.merge, TreapNode.all_prios]
  | Tree.node kp_1 l_1 r_1, Tree.node kp_2 l_2 r_2 =>
    unfold TreapNode.merge
    split_ifs <;> expose_names <;> simp_all
    · simp_all [TreapNode.all_prios]
      rw [← all_prios_union_merge r_1 (node kp_2 l_2 r_2)]
      nth_rw 7 [TreapNode.all_prios.eq_def]
      simp only [Set.union_singleton]
      rw [←
        Set.union_assoc (insert kp_1.prio (TreapNode.all_prios l_1)) (TreapNode.all_prios r_1)
          (insert kp_2.prio (TreapNode.all_prios l_2) ∪ TreapNode.all_prios r_2)]
    · -- You can prove it by just rewriting expressions
      nth_rw 3 [TreapNode.all_prios]
      rw [← all_prios_union_merge (node kp_1 l_1 r_1) l_2]
      rw [Set.union_assoc (TreapNode.all_prios (node kp_1 l_1 r_1)) (TreapNode.all_prios l_2)
          {kp_2.prio}]
      rw [Set.union_assoc (TreapNode.all_prios (node kp_1 l_1 r_1))
          (TreapNode.all_prios l_2 ∪ {kp_2.prio}) (TreapNode.all_prios r_2)]
      rw [← TreapNode.all_prios]

-- All keys found on the left after a split were originally on the root
theorem all_keys_subset_split_l (node : TreapNode Key Prio) (l : TreapNode Key Prio) (k : Key) :
  (TreapNode.split node k).1 = l → l.all_keys ⊆ node.all_keys := by
  match node with
  | Tree.nil =>
    -- Trivial case
    intro h
    subst h
    simp_all [TreapNode.split, TreapNode.all_keys]
  | Tree.node kp l r =>
    -- Complex case
    rw [TreapNode.split]
    split_ifs <;> expose_names
    · simp_all [TreapNode.all_keys]
      -- Bring r to the left
      rw [Set.insert_union]
      rw [Set.union_comm]
      rw [← Set.insert_union]

      intro h kk hkk
      subst h
      simp_all [TreapNode.all_keys]

      have split_in_r : TreapNode.all_keys (TreapNode.split r k).1 ⊆ TreapNode.all_keys r := by
        apply all_keys_subset_split_l r (TreapNode.split r k).1 k
        trivial

      cases hkk
      · aesop
      · aesop

    · simp_all [TreapNode.all_keys]
      intro h

      have all_in_l : TreapNode.all_keys l_1 ⊆ TreapNode.all_keys l := by
        apply all_keys_subset_split_l l l_1
        trivial

      grind

-- All keys found on the right after a split were originally on the root
theorem all_keys_subset_split_r (node : TreapNode Key Prio) (r : TreapNode Key Prio) (k : Key) : (TreapNode.split node k).2 = r → r.all_keys ⊆ node.all_keys := by
  match node with
  | Tree.nil =>
    -- Trivial case
    intro h
    subst h
    simp_all [TreapNode.split, TreapNode.all_keys]
  | Tree.node kp l r =>
    -- Complex case
    rw [TreapNode.split]
    split_ifs <;> expose_names
    · simp_all [TreapNode.all_keys]
      intro hr

      have all_in_r : TreapNode.all_keys r_1 ⊆ TreapNode.all_keys r := by
        apply all_keys_subset_split_r r r_1
        trivial

      grind

    · intro hh kk hkk
      subst hh
      simp_all [TreapNode.all_keys]

      have split_in_l : TreapNode.all_keys (TreapNode.split l k).2 ⊆ TreapNode.all_keys l := by
        apply all_keys_subset_split_r l (TreapNode.split l k).2 k
        trivial

      cases hkk
      · aesop
      · aesop

-- All priorities on the left of a split are a subset of the root priorities
theorem all_prios_subset_split_l (node l : TreapNode Key Prio) (k : Key) :
  (TreapNode.split node k).1 = l → l.all_prios ⊆ node.all_prios := by
  intro hl; subst hl
  match node with
  | Tree.nil => simp_all [TreapNode.split]
  | Tree.node kp l r =>
    simp_all [TreapNode.all_prios]
    unfold TreapNode.split
    split_ifs <;> expose_names <;> simp_all
    · rw [TreapNode.all_prios]
      simp_all only [Set.union_singleton, Set.union_subset_iff, Set.subset_union_left, true_and]
      suffices (TreapNode.split r k).1.all_prios ⊆ TreapNode.all_prios r by grind
      exact all_prios_subset_split_l r (TreapNode.split r k).1 k (by simp)
    · suffices (TreapNode.split l k).1.all_prios ⊆ TreapNode.all_prios l by grind
      exact all_prios_subset_split_l l (TreapNode.split l k).1 k (by simp)

-- All priorities on the right of a split are a subset of the root priorities
theorem all_prios_subset_split_r (node r : TreapNode Key Prio) (k : Key) :
  (TreapNode.split node k).2 = r → r.all_prios ⊆ node.all_prios := by
  intro hr; subst hr
  match node with
  | Tree.nil => simp_all [TreapNode.split]
  | Tree.node kp l r =>
    simp_all [TreapNode.all_prios]
    unfold TreapNode.split
    split_ifs <;> expose_names <;> simp_all
    · suffices (TreapNode.split r k).2.all_prios ⊆ TreapNode.all_prios r by grind
      exact all_prios_subset_split_r r (TreapNode.split r k).2 k (by simp)
    · rw [TreapNode.all_prios]
      simp_all only [Set.union_singleton, Set.union_subset_iff]
      suffices (TreapNode.split l k).2.all_prios ⊆ TreapNode.all_prios l by grind
      exact all_prios_subset_split_r l (TreapNode.split l k).2 k (by simp)

-- All keys on the left of a split k are < k
lemma split_left_lt_k (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) :
  ∀ lk, lk ∈ (TreapNode.split tn k).1.all_keys → lk < k := by
  match tn with
  | Tree.nil =>
    -- Trivial case
    rw [TreapNode.split]
    simp [TreapNode.all_keys]
  | Tree.node kp l r =>
    -- Complex case
    rw [TreapNode.split]
    -- Break down the IsBST proof
    cases tn_proof; expose_names
    split_ifs
    · simp

      have l_less : ∀ lk, lk ∈ (TreapNode.all_keys l) → lk < k := by
        rename_i h_less
        grw [←h_less]
        -- By definition l < kp.key
        exact h_1

      have r_less : ∀ lk, lk ∈ (TreapNode.split r k).1.all_keys → lk < k := by

        -- Recursively, the splitted part will be less than k
        apply split_left_lt_k
        exact h_2

      unfold TreapNode.all_keys
      grind
    · -- Apply recursion again
      apply split_left_lt_k
      exact h

-- All keys on the right of a split k are ≥ k
lemma split_right_ge_k (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) :
  ∀ rk, rk ∈ (TreapNode.split tn k).2.all_keys → k ≤ rk := by
  match tn with
  | Tree.nil =>
    -- Trivial case again
    rw [TreapNode.split]
    simp [TreapNode.all_keys]
  | Tree.node kp l r =>
    -- Complex one
    rw [TreapNode.split]
    -- Break down the IsBST proof
    cases tn_proof; rename_i l_proof l_less r_proof r_ge
    split_ifs <;> simp_all
    · exact split_right_ge_k r r_proof k
    · unfold TreapNode.all_keys
      intro rk rk_h
      -- Cover all cases (in left, as root, in right)
      cases rk_h
      · rename_i rk_h
        cases rk_h
        · rename_i le_h rk_h; revert rk_h rk
          exact split_right_ge_k l l_proof k
        · rename_i rk_h
          rw [Set.mem_singleton_iff] at rk_h
          rw [rk_h]
          assumption
      · rename_i le_h rk_h; revert rk_h rk -- reinsert into hypotheses
        grw [le_h]
        exact r_ge

/-
  splitUpper proofs are almost the same as the split ones
  They are mostly copy pasted and adjusted

-/
-- All keys found on the left after a splitUpper were originally on the root
theorem all_keys_subset_splitUpper_l (node : TreapNode Key Prio) (l : TreapNode Key Prio) (k : Key) :
  (TreapNode.splitUpper node k).1 = l → l.all_keys ⊆ node.all_keys := by
  match node with
  | Tree.nil =>
    -- Trivial case
    intro h
    subst h
    simp_all [TreapNode.splitUpper, TreapNode.all_keys]
  | Tree.node kp l r =>
    -- Complex case
    rw [TreapNode.splitUpper]
    split_ifs <;> expose_names
    · simp_all [TreapNode.all_keys]
      -- Bring r to the left
      rw [Set.insert_union]
      rw [Set.union_comm]
      rw [← Set.insert_union]

      intro h kk hkk
      subst h
      simp_all [TreapNode.all_keys]

      have splitUpper_in_r : TreapNode.all_keys (TreapNode.splitUpper r k).1 ⊆ TreapNode.all_keys r := by
        apply all_keys_subset_splitUpper_l r (TreapNode.splitUpper r k).1 k
        trivial

      cases hkk
      · aesop
      · aesop

    · simp_all [TreapNode.all_keys]
      intro h

      have all_in_l : TreapNode.all_keys l_1 ⊆ TreapNode.all_keys l := by
        apply all_keys_subset_splitUpper_l l l_1
        trivial

      grind

-- All keys found on the right after a splitUpper were originally on the root
theorem all_keys_subset_splitUpper_r (node : TreapNode Key Prio) (r : TreapNode Key Prio) (k : Key) : (TreapNode.splitUpper node k).2 = r → r.all_keys ⊆ node.all_keys := by
  match node with
  | Tree.nil =>
    -- Trivial case
    intro h
    subst h
    simp_all [TreapNode.splitUpper, TreapNode.all_keys]
  | Tree.node kp l r =>
    -- Complex case
    rw [TreapNode.splitUpper]
    split_ifs <;> expose_names
    · simp_all [TreapNode.all_keys]
      intro hr

      have all_in_r : TreapNode.all_keys r_1 ⊆ TreapNode.all_keys r := by
        apply all_keys_subset_splitUpper_r r r_1
        trivial

      grind

    · intro hh kk hkk
      subst hh
      simp_all [TreapNode.all_keys]

      have splitUpper_in_l : TreapNode.all_keys (TreapNode.splitUpper l k).2 ⊆ TreapNode.all_keys l := by
        apply all_keys_subset_splitUpper_r l (TreapNode.splitUpper l k).2 k
        trivial

      cases hkk
      · aesop
      · aesop

-- TODO: copy these for splitUpper
-- All keys are union in a split
theorem all_keys_union_split (node : TreapNode Key Prio) (k : Key) :
  (node.split k).1.all_keys ∪ (node.split k).2.all_keys = node.all_keys := by
  rw [TreapNode.all_keys.eq_def node]
  match node with
  | Tree.nil =>
    simp [TreapNode.split, TreapNode.all_keys]
  | Tree.node kp l r =>
    unfold TreapNode.split; split_ifs <;> expose_names
    · simp_rw [TreapNode.all_keys] -- gives a better result in this case (simp puts insert ...) tactic found the first time in https://github.com/nielsvoss/lean-pitfalls?tab=readme-ov-file#rewriting-under-binders
      have : (TreapNode.split r k).1.all_keys ∪ (TreapNode.split r k).2.all_keys = TreapNode.all_keys r := by
        exact all_keys_union_split r k
      rw [← this]
      grind
    · simp_rw [TreapNode.all_keys]
      have : (TreapNode.split l k).1.all_keys ∪ (TreapNode.split l k).2.all_keys = TreapNode.all_keys l := by
        exact all_keys_union_split l k
      rw [← this]
      grind

-- Keys are not duplicated in splits (requires IsBST)
theorem all_keys_inter_split (node : TreapNode Key Prio) (bst : IsBST node) (k : Key) :
  (node.split k).1.all_keys ∩ (node.split k).2.all_keys = ∅ := by
  match node with
  | Tree.nil =>
    simp [TreapNode.split, TreapNode.all_keys]
  | Tree.node kp l r =>
    have split_l_lt_r :
      ∀ kl ∈ (TreapNode.split (Tree.node kp l r) k).1.all_keys,
      ∀ kr ∈ (TreapNode.split (Tree.node kp l r) k).2.all_keys, kl < kr := by
      intro kl hkl kr hkr
      apply Std.lt_of_lt_of_le -- convert < to (< k, k ≤)
      · exact split_left_lt_k (Tree.node kp l r) bst k kl hkl
      · exact split_right_ge_k (Tree.node kp l r) bst k kr hkr
    grind

-- All priorities on the left of a splitUpper are a subset of the root priorities
theorem all_prios_subset_splitUpper_l (node l : TreapNode Key Prio) (k : Key) :
  (TreapNode.splitUpper node k).1 = l → l.all_prios ⊆ node.all_prios := by
  intro hl; subst hl
  match node with
  | Tree.nil => simp_all [TreapNode.splitUpper]
  | Tree.node kp l r =>
    simp_all [TreapNode.all_prios]
    unfold TreapNode.splitUpper
    split_ifs <;> expose_names <;> simp_all
    · rw [TreapNode.all_prios]
      simp_all only [Set.union_singleton, Set.union_subset_iff, Set.subset_union_left, true_and]
      suffices (TreapNode.splitUpper r k).1.all_prios ⊆ TreapNode.all_prios r by grind
      exact all_prios_subset_splitUpper_l r (TreapNode.splitUpper r k).1 k (by simp)
    · suffices (TreapNode.splitUpper l k).1.all_prios ⊆ TreapNode.all_prios l by grind
      exact all_prios_subset_splitUpper_l l (TreapNode.splitUpper l k).1 k (by simp)

-- All priorities on the right of a splitUpper are a subset of the root priorities
theorem all_prios_subset_splitUpper_r (node r : TreapNode Key Prio) (k : Key) :
  (TreapNode.splitUpper node k).2 = r → r.all_prios ⊆ node.all_prios := by
  intro hr; subst hr
  match node with
  | Tree.nil => simp_all [TreapNode.splitUpper]
  | Tree.node kp l r =>
    simp_all [TreapNode.all_prios]
    unfold TreapNode.splitUpper
    split_ifs <;> expose_names <;> simp_all
    · suffices (TreapNode.splitUpper r k).2.all_prios ⊆ TreapNode.all_prios r by grind
      exact all_prios_subset_splitUpper_r r (TreapNode.splitUpper r k).2 k (by simp)
    · rw [TreapNode.all_prios]
      simp_all only [Set.union_singleton, Set.union_subset_iff]
      suffices (TreapNode.splitUpper l k).2.all_prios ⊆ TreapNode.all_prios l by grind
      exact all_prios_subset_splitUpper_r l (TreapNode.splitUpper l k).2 k (by simp)

-- All keys on the left of a splitUpper k are < k
lemma splitUpper_left_le_k (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) :
  ∀ lk, lk ∈ (TreapNode.splitUpper tn k).1.all_keys → lk ≤ k := by
  match tn with
  | Tree.nil =>
    -- Trivial case
    rw [TreapNode.splitUpper]
    simp [TreapNode.all_keys]
  | Tree.node kp l r =>
    -- Complex case
    rw [TreapNode.splitUpper]
    -- Break down the IsBST proof
    cases tn_proof; expose_names
    split_ifs
    · simp

      have l_less : ∀ lk, lk ∈ (TreapNode.all_keys l) → lk < k := by
        rename_i h_less
        grw [←h_less]
        -- By definition l < kp.key
        exact h_1

      have r_less : ∀ lk, lk ∈ (TreapNode.splitUpper r k).1.all_keys → lk ≤ k := by

        -- Recursively, the splitUpperted part will be less than k
        apply splitUpper_left_le_k
        exact h_2

      unfold TreapNode.all_keys
      grind
    · -- Apply recursion again
      apply splitUpper_left_le_k
      exact h

-- All keys on the right of a splitUpper k are > k
lemma splitUpper_right_gt_k (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) :
  ∀ rk, rk ∈ (TreapNode.splitUpper tn k).2.all_keys → k < rk := by
  match tn with
  | Tree.nil =>
    -- Trivial case again
    rw [TreapNode.splitUpper]
    simp [TreapNode.all_keys]
  | Tree.node kp l r =>
    -- Complex one
    rw [TreapNode.splitUpper]
    -- Break down the IsBST proof
    cases tn_proof; rename_i l_proof l_less r_proof r_ge
    split_ifs <;> simp_all
    · exact splitUpper_right_gt_k r r_proof k
    · unfold TreapNode.all_keys
      intro rk rk_h
      -- Cover all cases (in left, as root, in right)
      cases rk_h
      · rename_i rk_h
        cases rk_h
        · rename_i le_h rk_h; revert rk_h rk
          exact splitUpper_right_gt_k l l_proof k
        · rename_i rk_h
          rw [Set.mem_singleton_iff] at rk_h
          rw [rk_h]
          assumption
      · rename_i le_h rk_h; revert rk_h rk -- reinsert into hypotheses
        by_cases hc : k = kp.key
        · simp_all
        · grind


/-
  Split correctness
-/

-- Splitting creates a BST on the left
theorem split_IsBST_left (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) :
  IsBST (TreapNode.split tn k).1 := by
  fun_induction TreapNode.split
  · exact IsBST.nil
  · expose_names; cases tn_proof; expose_names
    simp_all

    apply IsBST.node
    · simp_all
    · grw [all_keys_subset_split_l a_1 split_l k]
      exact h_5
      · simp_all
    · simp_all
    · simp_all
  · cases tn_proof
    simp_all

-- Splitting creates a BST on the right
theorem split_IsBST_right (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) :
  IsBST (TreapNode.split tn k).2 := by
  fun_induction TreapNode.split
  · exact IsBST.nil
  · cases tn_proof
    simp_all
  · expose_names; cases tn_proof; expose_names
    simp_all

    apply IsBST.node
    · grw [all_keys_subset_split_r a new_r k]
      exact h_3
      · simp_all
    · simp_all
    · simp_all
    · simp_all

-- Splitting creates a Heap on the left
theorem split_IsHeap_left (tn : TreapNode Key Prio) (tn_proof : IsHeap tn) (k : Key) :
  IsHeap (TreapNode.split tn k).1 := by
  fun_induction TreapNode.split
  · exact IsHeap.nil
  · expose_names; cases tn_proof; expose_names
    simp_all

    apply IsHeap.node
    · simp_all
    · grw [all_prios_subset_split_l a_1 split_l k]
      exact h_5
      · simp_all
    · simp_all
    · simp_all
  · cases tn_proof
    simp_all

-- Splitting creates a Heap on the right
theorem split_IsHeap_right (tn : TreapNode Key Prio) (tn_proof : IsHeap tn) (k : Key) :
  IsHeap (TreapNode.split tn k).2 := by
  fun_induction TreapNode.split
  · exact IsHeap.nil
  · cases tn_proof
    simp_all
  · expose_names; cases tn_proof; expose_names
    simp_all

    apply IsHeap.node
    · grw [all_prios_subset_split_r a new_r k]
      · simp_all
      · simp_all
    · simp_all
    · exact ih1
    · simp_all

/-
  SplitUpper correctness

  Again, the code is copy-pasted from the split variant
-/

-- Splitting creates a BST on the left
theorem splitUpper_IsBST_left (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) :
  IsBST (TreapNode.splitUpper tn k).1 := by
  fun_induction TreapNode.splitUpper
  · exact IsBST.nil
  · expose_names; cases tn_proof; expose_names
    simp_all

    apply IsBST.node
    · simp_all
    · grw [all_keys_subset_splitUpper_l a_1 split_l k]
      exact h_5
      · simp_all
    · simp_all
    · simp_all
  · cases tn_proof
    simp_all

-- Splitting creates a BST on the right
theorem splitUpper_IsBST_right (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) :
  IsBST (TreapNode.splitUpper tn k).2 := by
  fun_induction TreapNode.splitUpper
  · exact IsBST.nil
  · cases tn_proof
    simp_all
  · expose_names; cases tn_proof; expose_names
    simp_all

    apply IsBST.node
    · grw [all_keys_subset_splitUpper_r a new_r k]
      exact h_3
      · simp_all
    · simp_all
    · simp_all
    · simp_all

-- Splitting creates a Heap on the left
theorem splitUpper_IsHeap_left (tn : TreapNode Key Prio) (tn_proof : IsHeap tn) (k : Key) :
  IsHeap (TreapNode.splitUpper tn k).1 := by
  fun_induction TreapNode.splitUpper
  · exact IsHeap.nil
  · expose_names; cases tn_proof; expose_names
    simp_all

    apply IsHeap.node
    · simp_all
    · grw [all_prios_subset_splitUpper_l a_1 split_l k]
      exact h_5
      · simp_all
    · simp_all
    · simp_all
  · cases tn_proof
    simp_all

-- Splitting creates a Heap on the right
theorem splitUpper_IsHeap_right (tn : TreapNode Key Prio) (tn_proof : IsHeap tn) (k : Key) :
  IsHeap (TreapNode.splitUpper tn k).2 := by
  fun_induction TreapNode.splitUpper
  · exact IsHeap.nil
  · cases tn_proof
    simp_all
  · expose_names; cases tn_proof; expose_names
    simp_all

    apply IsHeap.node
    · grw [all_prios_subset_splitUpper_r a new_r k]
      · simp_all
      · simp_all
    · simp_all
    · exact ih1
    · simp_all


-- All keys are union in a splitUpper
theorem all_keys_union_splitUpper (node : TreapNode Key Prio) (k : Key) :
  (node.splitUpper k).1.all_keys ∪ (node.splitUpper k).2.all_keys = node.all_keys := by
  rw [TreapNode.all_keys.eq_def node]
  match node with
  | Tree.nil =>
    simp [TreapNode.splitUpper, TreapNode.all_keys]
  | Tree.node kp l r =>
    unfold TreapNode.splitUpper; split_ifs <;> expose_names
    · simp_rw [TreapNode.all_keys] -- gives a better result in this case (simp puts insert ...) tactic found the first time in https://github.com/nielsvoss/lean-pitfalls?tab=readme-ov-file#rewriting-under-binders
      have : (TreapNode.splitUpper r k).1.all_keys ∪ (TreapNode.splitUpper r k).2.all_keys = TreapNode.all_keys r := by
        exact all_keys_union_splitUpper r k
      rw [← this]
      grind
    · simp_rw [TreapNode.all_keys]
      have : (TreapNode.splitUpper l k).1.all_keys ∪ (TreapNode.splitUpper l k).2.all_keys = TreapNode.all_keys l := by
        exact all_keys_union_splitUpper l k
      rw [← this]
      grind

-- Keys are not duplicated in splitUppers (requires IsBST)
theorem all_keys_inter_splitUpper (node : TreapNode Key Prio) (bst : IsBST node) (k : Key) :
  (node.splitUpper k).1.all_keys ∩ (node.splitUpper k).2.all_keys = ∅ := by
  match node with
  | Tree.nil =>
    simp [TreapNode.splitUpper, TreapNode.all_keys]
  | Tree.node kp l r =>
    have splitUpper_l_lt_r :
      ∀ kl ∈ (TreapNode.splitUpper (Tree.node kp l r) k).1.all_keys,
      ∀ kr ∈ (TreapNode.splitUpper (Tree.node kp l r) k).2.all_keys, kl < kr := by
      intro kl hkl kr hkr
      apply Std.lt_of_le_of_lt -- convert < to (< k, k ≤)
      · exact splitUpper_left_le_k (Tree.node kp l r) bst k kl hkl
      · exact splitUpper_right_gt_k (Tree.node kp l r) bst k kr hkr
    grind

/-
  Merge correctness

-/

-- Merging creates another BST
theorem merge_IsBST (l r : TreapNode Key Prio)
  (l_proof : IsBST l) (r_proof : IsBST r) (sorted_l_r : ∀ kl ∈ l.all_keys, ∀ kr ∈ r.all_keys, kl < kr) : IsBST (TreapNode.merge l r) := by
  match l, r with
  -- Easier to prove with these three trivial cases
  | Tree.nil, Tree.nil
  | Tree.nil, Tree.node _ _ _
  | Tree.node _ _ _, Tree.nil =>
    simp [TreapNode.merge];
    trivial -- all other cases here

  -- Complex case
  | Tree.node kp_1 l_1 r_1, Tree.node kp_2 l_2 r_2 =>
    simp_all [TreapNode.merge]
    expose_names; cases l_proof; cases r_proof; expose_names

    split_ifs <;> rename_i h_if
    · apply IsBST.node
      · assumption
      · suffices
        (∀ k ∈ TreapNode.all_keys r_1, kp_1.key ≤ k) ∧
        (∀ k ∈ TreapNode.all_keys (Tree.node kp_2 l_2 r_2), kp_1.key ≤ k) by
          rw [← all_keys_union_merge]
          grind
        constructor
        · assumption
        · -- We have a stricter
          suffices
          ∀ k ∈ TreapNode.all_keys (Tree.node kp_2 l_2 r_2), kp_1.key < k by
            grind
          -- now we use sorted_l_r
          apply sorted_l_r kp_1.key
          simp [TreapNode.all_keys]
      · assumption
      · apply merge_IsBST
        · assumption
        · apply IsBST.node <;> all_goals assumption
        · simp_all [TreapNode.all_keys]
    · apply IsBST.node
      · suffices
        (∀ k ∈ TreapNode.all_keys (Tree.node kp_1 l_1 r_1), k < kp_2.key) ∧
        (∀ k ∈ TreapNode.all_keys l_2, k < kp_2.key) by
          rw [← all_keys_union_merge]
          grind
        constructor
        · -- swap l and r, they are already unpacked as kp_x, l_x, ...
          have sorted_r_l :
            ∀ kr ∈ TreapNode.all_keys (Tree.node kp_2 l_2 r_2),
            ∀ kl ∈ TreapNode.all_keys (Tree.node kp_1 l_1 r_1),
            kl < kr := by
            intro kr a kl a_1
            simp_all only [not_le]
          -- do the same by applying sorted_r_l
          apply sorted_r_l kp_2.key
          simp_all [TreapNode.all_keys]
        · assumption
      · assumption
      · apply merge_IsBST
        · apply IsBST.node <;> all_goals assumption
        · assumption
        · simp_all [TreapNode.all_keys]
      · assumption

-- Merging creates another Heap
theorem merge_IsHeap (l r : TreapNode Key Prio)
  (l_proof : IsHeap l) (r_proof : IsHeap r) : IsHeap (TreapNode.merge l r) := by
  match l, r with
  | Tree.nil, Tree.nil => simp [TreapNode.merge, IsHeap.nil]
  | Tree.nil, Tree.node _ _ _ => simp_all [TreapNode.merge]
  | Tree.node _ _ _, Tree.nil => simp_all [TreapNode.merge]
  | Tree.node kp_1 l_1 r_1, Tree.node kp_2 l_2 r_2 =>
    simp_all [TreapNode.merge]

    split_ifs <;> rename_i h_if
    · cases l_proof; rename_i l_1_proof l_1_ge r_1_proof r_1_ge
      apply IsHeap.node
      · exact l_1_ge
      · rw [← all_prios_union_merge]
        intro p hp
        cases hp
        · tauto
        · cases r_proof; rename_i l_2_proof l_2_ge r_2_proof r_2_ge
          trans kp_2.prio
          · grind [TreapNode.all_prios]
          · exact h_if
      · exact l_1_proof
      · apply merge_IsHeap r_1 (Tree.node kp_2 l_2 r_2) r_1_proof r_proof
    · cases r_proof; rename_i l_2_proof l_2_ge r_2_proof r_2_ge
      apply IsHeap.node
      · rw [← all_prios_union_merge]
        intro p hp
        cases hp
        · cases l_proof; rename_i l_1_proof l_1_ge r_1_proof r_1_ge
          trans kp_1.prio
          · grind [TreapNode.all_prios]
          · grind
        · tauto
      · exact r_2_ge
      · apply merge_IsHeap (Tree.node kp_1 l_1 r_1) l_2 l_proof l_2_proof
      · exact r_2_proof

/-
  Singleton correctness
-/

-- Singleton is a BST
theorem singleton_isBST (kp : KeyPrioPair Key Prio) :
  IsBST (TreapNode.singleton kp) := by
  apply IsBST.node <;> simp_all [TreapNode.all_keys, IsBST.nil]

-- Singleton is a Heap
theorem singleton_isHeap (kp : KeyPrioPair Key Prio) :
  IsHeap (TreapNode.singleton kp) := by
  apply IsHeap.node <;> simp_all [TreapNode.all_prios, IsHeap.nil]

/-
  Treap operations (joint correctness and operation)

  Again, we only prove that operations which build Treaps make valid Treaps

-/

def Treap.empty : Treap Key Prio :=
  { root := Tree.nil,
    is_treap := by
      simp [IsTreap, IsBST.nil, IsHeap.nil] }

def Treap.singleton (kp : KeyPrioPair Key Prio) : Treap Key Prio :=
  let root := TreapNode.singleton kp
  have singleton_bst_proof : IsBST root := singleton_isBST kp
  have singleton_heap_proof : IsHeap root := singleton_isHeap kp

  have treap_proof : IsTreap root := by
    simp_all [IsTreap]

  { root := root, is_treap := treap_proof }

-- Leftmost doesn't need correctness proofs here, doesn't produce treaps
def Treap.leftmost (t : Treap Key Prio) : Option (KeyPrioPair Key Prio) :=
  -- Delegate the call
  TreapNode.leftmost t.root

-- Prove the resulting treaps satisfy the treap properties
def Treap.split (t : Treap Key Prio) (k : Key) : Treap Key Prio × Treap Key Prio :=
  let split_res := t.root.split k

  -- Construct treap proofs for l and r
  let l_bst_proof := split_IsBST_left t.root t.is_treap.2 k
  let r_bst_proof := split_IsBST_right t.root t.is_treap.2 k
  let l_heap_proof := split_IsHeap_left t.root t.is_treap.1 k
  let r_heap_proof := split_IsHeap_right t.root t.is_treap.1 k

  have l_treap_proof : IsTreap split_res.1 := by
    subst split_res
    simp_all [IsTreap]

  have r_treap_proof : IsTreap split_res.2 := by
    subst split_res
    simp_all [IsTreap]

  let l_treap := { root := (t.root.split k).1, is_treap := l_treap_proof }
  let r_treap := { root := (t.root.split k).2, is_treap := r_treap_proof }
  (l_treap, r_treap)

-- Repeat the same for splitUpper
def Treap.splitUpper (t : Treap Key Prio) (k : Key) : Treap Key Prio × Treap Key Prio :=
  let split_res := t.root.splitUpper k

  -- Construct treap proofs for l and r
  let l_bst_proof := splitUpper_IsBST_left t.root t.is_treap.2 k
  let r_bst_proof := splitUpper_IsBST_right t.root t.is_treap.2 k
  let l_heap_proof := splitUpper_IsHeap_left t.root t.is_treap.1 k
  let r_heap_proof := splitUpper_IsHeap_right t.root t.is_treap.1 k

  have l_treap_proof : IsTreap split_res.1 := by
    subst split_res
    simp_all [IsTreap]

  have r_treap_proof : IsTreap split_res.2 := by
    subst split_res
    simp_all [IsTreap]

  let l_treap := { root := (t.root.splitUpper k).1, is_treap := l_treap_proof }
  let r_treap := { root := (t.root.splitUpper k).2, is_treap := r_treap_proof }
  (l_treap, r_treap)

-- Prove the merged treap satisfies the treap properties
def Treap.merge (l r : Treap Key Prio) (sorted_l_r : ∀ kl ∈ l.root.all_keys, ∀ kr ∈ r.root.all_keys, kl < kr) : Treap Key Prio :=
  let root_merged := TreapNode.merge l.root r.root
  let bst_proof := merge_IsBST l.root r.root l.is_treap.2 r.is_treap.2 sorted_l_r
  let heap_proof := merge_IsHeap l.root r.root l.is_treap.1 r.is_treap.1

  have treap_proof : IsTreap root_merged := by
    subst root_merged
    simp_all [IsTreap]

  { root := root_merged, is_treap := treap_proof }

/-
  Composite operations

  We now define more operations on Treaps, and prove their correctness.
  These operations will be:
  - find
  - insert
  - delete

  We'll not prove complexity of these operations, since they are direct compositions of
  previously defined operations whose complexity has already been analyzed.

  We will however prove their behavioral correctness.
-/

-- Returns none if the key is not found, some (key,prio) if it is found
def Treap.find (t : Treap Key Prio) (k : Key) : Option (KeyPrioPair Key Prio) :=
  let split := t.split k
  match split.2.root.leftmost with
  | none => none
  | some kp =>
    if kp.key = k then
      some kp
    else
      none

-- We discard other existing occurrences of the same key
def Treap.insert (t : Treap Key Prio) (kp : KeyPrioPair Key Prio) : Treap Key Prio :=
  let split_l_key := t.split kp.key
  -- Save split proofs
  have l_less_k := split_left_lt_k t.root t.is_treap.2 kp.key
  have r_ge_k := split_right_ge_k t.root t.is_treap.2 kp.key

  let split_key_r := t.splitUpper kp.key
  -- Save splitUpper proofs
  have l_le_k := splitUpper_left_le_k t.root t.is_treap.2 kp.key
  have r_greater_k := splitUpper_right_gt_k t.root t.is_treap.2 kp.key

  let new_node := Treap.singleton kp

  -- We need new_node < r
  have kp_less_r : (∀ kl ∈ new_node.root.all_keys, ∀ kr ∈ TreapNode.all_keys split_key_r.2.root, kl < kr) := by
    subst new_node
    subst split_key_r
    subst split_l_key
    simp_all [Treap.singleton, TreapNode.singleton, TreapNode.all_keys]
    exact r_greater_k

  let merged_right := Treap.merge new_node split_key_r.2 kp_less_r -- First merge right (ensures l < r)

  -- We need l < new_node ∪ r
  have l_less_kp_r : (∀ kl ∈ TreapNode.all_keys split_l_key.1.root, ∀ kr ∈ merged_right.root.all_keys, kl < kr) := by
    subst merged_right
    subst new_node
    subst split_key_r
    subst split_l_key
    simp_all [Treap.merge, Treap.split, Treap.singleton, TreapNode.singleton, TreapNode.all_keys]
    simp [Treap.singleton, TreapNode.singleton, TreapNode.all_keys] at kp_less_r
    suffices ∀ kl ∈ (t.root.split kp.key).1.all_keys, kl < kp.key by
      rw [← all_keys_union_merge]
      simp_all only [Set.mem_union]
      intro kl kl_h kr kr_h
      cases kr_h <;> rename_i kr_h
      · simp [TreapNode.all_keys] at kr_h
        rw [kr_h]
        revert kr kl_h kl
        simp
        exact this
      · grind
    simp_all

  Treap.merge split_l_key.1 merged_right l_less_kp_r

-- Deletes the key only if it exists, otherwise doesn't do anything
def Treap.delete (t : Treap Key Prio) (kp : KeyPrioPair Key Prio) : Treap Key Prio :=
  let split_l_key := t.split kp.key
  -- Save split proofs
  have l_less_k := split_left_lt_k t.root t.is_treap.2 kp.key
  have r_ge_k := split_right_ge_k t.root t.is_treap.2 kp.key

  let split_key_r := t.splitUpper kp.key
  -- Save splitUpper proofs
  have l_le_k := splitUpper_left_le_k t.root t.is_treap.2 kp.key
  have r_greater_k := splitUpper_right_gt_k t.root t.is_treap.2 kp.key

  -- We need new_node < r
  have l_less_r : (∀ kl ∈ TreapNode.all_keys split_l_key.1.root, ∀ kr ∈ TreapNode.all_keys split_key_r.2.root, kl < kr) := by
    intro kl hkl kr hkr
    trans kp.key
    · revert kl hkl
      assumption
    · revert kr hkr
      assumption

  Treap.merge split_l_key.1 split_key_r.2 l_less_r

/-
  Operation correctness - Behavioral correctness

  If we use find, prove that we get this value iff the value is present on the Treap
  Same reasoning for insert, delete, ...
-/

def opt_get_key (okp : Option (KeyPrioPair Key Prio)) :=
  match okp with
  | none => none
  | some kp => some kp.key

theorem leftmost_in_all_keys (tn : TreapNode Key Prio) :
  ∀ k : Key, opt_get_key tn.leftmost = some k → k ∈ tn.all_keys := by
  match tn with
  | Tree.nil => simp_all [opt_get_key, TreapNode.leftmost]
  | Tree.node kp l r =>
    simp_all [TreapNode.leftmost]
    split
    · simp_all [opt_get_key, TreapNode.all_keys]
    · rw [TreapNode.all_keys]
      rename_i kp' l' r'
      suffices ∀ (k : Key),
        opt_get_key (TreapNode.leftmost (node kp' l' r')) = some k →
        k ∈ TreapNode.all_keys (node kp' l' r') by grind
      apply leftmost_in_all_keys

-- The leftmost key is the smallest key in the treap
theorem leftmost_is_smallest (tn : TreapNode Key Prio) (tn_bst : IsBST tn) :
  ∀ k ∈ tn.all_keys, opt_get_key tn.leftmost ≤ some k := by
  fun_induction TreapNode.leftmost
  · simp [TreapNode.all_keys]
  · simp [TreapNode.all_keys, opt_get_key]
    cases tn_bst; rename_i l_proof l_keys_less r_proof r_keys_ge
    grind
  · rename_i kp tn_2 kp_1 l_1 r_1 ih
    intro k hk

    -- If none, if some
    unfold opt_get_key; unfold opt_get_key at ih; split
    · trivial

    -- Each case (left, root, right)
    simp_all only [Option.some_le_some]
    cases hk <;> rename_i hk; try cases hk <;> rename_i hk
    · cases tn_bst; rename_i l_proof l_keys_less r_proof r_keys_ge
      simp_all
    · cases tn_bst; rename_i l_proof l_keys_less r_proof r_keys_ge
      rename_i okp kp' heq
      simp_all
      refine Std.le_of_lt ?_
      refine l_keys_less kp'.key ?_
      apply leftmost_in_all_keys
      simp_all [opt_get_key]
    · rename_i okp kp' heq

      have := left_lt_right (node kp (node kp_1 l_1 r_1) tn_2) tn_bst kp'.key ?_
      refine Std.le_of_lt ?_
      apply this
      · grind
      · simp [TreapNode.all_keys_left]
        apply leftmost_in_all_keys
        simp_all [opt_get_key]

lemma leftmost_eq_none_iff (tn : TreapNode Key Prio) :
  TreapNode.leftmost tn = none ↔ tn = Tree.nil := by
  match tn with
  | Tree.nil => simp [TreapNode.leftmost]
  | Tree.node kp l r =>
    match l with
    | Tree.nil => simp [TreapNode.leftmost]
    | Tree.node kp' l' r' =>
      have := leftmost_eq_none_iff (node kp' l' r')
      simp_all [TreapNode.leftmost]

-- The smallest key in the treap is the leftmost key (proof is similar to the previous one)
theorem smallest_is_leftmost (tn : TreapNode Key Prio) (tn_bst : IsBST tn) (k : Key) (hk : k ∈ tn.all_keys) (smallest : ∀ x, x ∈ tn.all_keys → k ≤ x) :
  opt_get_key tn.leftmost = some k := by
  cases hlm : TreapNode.leftmost tn
  · simp_all [opt_get_key, leftmost_eq_none_iff, TreapNode.all_keys]
  · rename_i kp
    -- kp.key is in all_keys
    have hkp_mem : kp.key ∈ tn.all_keys := by
      apply leftmost_in_all_keys
      simp [opt_get_key, hlm]

    -- get kp.key ≤ k with leftmost_is_smallest
    have h_lm_le_k : kp.key ≤ k := by
      have h := leftmost_is_smallest tn tn_bst k hk
      simp_all [opt_get_key]

    -- smallest gives k ≤ kp.key
    have h_k_le_lm : k ≤ kp.key := smallest kp.key hkp_mem

    have hkpeq : kp.key = k := le_antisymm h_lm_le_k h_k_le_lm
    simp [opt_get_key, hkpeq]

-- TODO: maybe show that doing ops on t.root is the same as doing them on t (nah, just needs a simp [Treap.xxx])
-- We don't prove priorities stay the same with insert/delete: it is not needed for the correctness of the data structure

-- split and splitUpper are exactly the same if the key element is not in the treap
lemma split_eq_splitUpper_if_no_k (tn : TreapNode Key Prio) (k : Key) :
  k ∉ tn.all_keys → (tn.split k).2.all_keys = (tn.splitUpper k).2.all_keys := by
  intro hk
  match tn with
  | Tree.nil =>
    simp [TreapNode.split, TreapNode.splitUpper]
  | Tree.node kp l r =>
    simp [TreapNode.split, TreapNode.splitUpper]
    -- Go through each case
    split_ifs <;> expose_names
    · simp
      refine split_eq_splitUpper_if_no_k r k ?_
      rw [TreapNode.all_keys] at hk
      simp_all only [Set.union_singleton, Set.mem_union, Set.mem_insert_iff, not_or,
        not_false_eq_true]

    · -- Contradictory case
      rw [not_le] at h_1
      grind

    · -- kp.key = k
      rw [not_lt] at h
      have : k = kp.key := by exact Std.le_antisymm h h_1
      subst this
      simp_all [TreapNode.all_keys]

    · simp_rw [TreapNode.all_keys]
      suffices
        (TreapNode.split l k).2.all_keys =
        (TreapNode.splitUpper l k).2.all_keys by simp_all only [not_lt, not_le, Set.union_singleton]
      refine split_eq_splitUpper_if_no_k l k ?_
      rw [TreapNode.all_keys] at hk
      simp_all only [Set.union_singleton, Set.mem_union, Set.mem_insert_iff, not_or,
        not_false_eq_true]

lemma all_keys_eq_split_splitUpper_r (tn : TreapNode Key Prio) (k : Key) (bst : IsBST tn) :
  k ∈ tn.all_keys → TreapNode.all_keys (tn.split k).2 = TreapNode.all_keys (tn.splitUpper k).2 ∪ {k} := by
  intro hk
  match tn with
  | Tree.nil => simp_all [TreapNode.all_keys]
  | Tree.node kp l r =>
    simp only [TreapNode.split, TreapNode.splitUpper]
    split_ifs <;> expose_names
    · simp only
      cases bst; rename_i bst_l left_l_key bst_r right_ge_key
      refine all_keys_eq_split_splitUpper_r r k bst_r ?_
      -- Show it can only be in the right subtree with bst inequalities

      -- Left, center, right
      cases hk <;> rename_i hk; try cases hk <;> rename_i hk
      · grind
      · simp_all
      · simp_all

    · -- Contradictory case
      rw [not_le] at h_1
      grind

    · -- kp.key = k
      rw [not_lt] at h
      have : k = kp.key := by exact Std.le_antisymm h h_1
      subst this

      cases bst; rename_i bst_l left_l_key bst_r right_ge_key
      simp_all only [TreapNode.all_keys]
      suffices (TreapNode.split l kp.key).2.all_keys ∪ (TreapNode.all_keys r) ∪ {kp.key} =
        (TreapNode.splitUpper r kp.key).2.all_keys ∪ {kp.key} by grind

      -- Build all inequalities on left and right side
      have l_ge_k := split_right_ge_k l bst_l kp.key
      have r_le_k := splitUpper_left_le_k r bst_r kp.key
      have l_lt_k : ∀ k ∈ (TreapNode.split l kp.key).2.all_keys, k < kp.key := by
        grw [all_keys_subset_split_r l (TreapNode.split l kp.key).2 kp.key (by simp)]
        exact left_l_key
      have r_gt_k : ∀ k ∈ (TreapNode.splitUpper r kp.key).1.all_keys, kp.key ≤ k := by
        grw [all_keys_subset_splitUpper_l r (TreapNode.splitUpper r kp.key).1 kp.key (by simp)]
        exact right_ge_key

      -- Trivially empty with inequalities
      have split_l_r : (TreapNode.split l kp.key).2.all_keys = ∅ := by grind
      have split_r_l :
        (TreapNode.splitUpper r kp.key).1.all_keys = ∅ ∨
        (TreapNode.splitUpper r kp.key).1.all_keys = {kp.key} := by grind

      -- Close the goal
      rw [← all_keys_union_splitUpper r kp.key]
      cases split_r_l
      · simp_all
      · simp_all

    · simp only [TreapNode.all_keys]
      suffices (TreapNode.split l k).2.all_keys = (TreapNode.splitUpper l k).2.all_keys ∪ {k} by grind
      cases bst; rename_i bst_l left_l_key bst_r right_ge_key
      refine all_keys_eq_split_splitUpper_r l k bst_l ?_
      -- Show it can only be in the left subtree with bst inequalities

      -- Left, center, right
      cases hk <;> rename_i hk; try cases hk <;> rename_i hk
      · simp_all
      · simp_all
      · grind

-- Stricter condition, implies the other keys don't change
theorem insert_inserts_element (t : Treap Key Prio) (ins_kp : KeyPrioPair Key Prio) :
  (Treap.insert t ins_kp).root.all_keys = (t.root.all_keys \ {ins_kp.key}) ∪ {ins_kp.key} := by
  -- Split inequalities
  have l_lt_k := split_left_lt_k t.root t.is_treap.2 ins_kp.key
  have r_ge_k := split_right_ge_k t.root t.is_treap.2 ins_kp.key

  -- SplitUpper inequalities
  have l_le_k := splitUpper_left_le_k t.root t.is_treap.2 ins_kp.key
  have r_gt_k := splitUpper_right_gt_k t.root t.is_treap.2 ins_kp.key

  -- Unfold all Treap definitions, get only the TreapNode ones
  simp_all [Treap.insert, Treap.split, Treap.merge, Treap.splitUpper]

  repeat rw [← all_keys_union_merge]
  simp only [Treap.singleton, TreapNode.singleton, TreapNode.all_keys, Set.union_singleton,
    insert_empty_eq, Set.union_empty, Set.singleton_union, Set.union_insert]


  by_cases hc : ins_kp.key ∉ t.root.all_keys
  · suffices ((t.root.split ins_kp.key).1.all_keys ∪ (t.root.splitUpper ins_kp.key).2.all_keys) = t.root.all_keys by grind
    rw [← split_eq_splitUpper_if_no_k t.root ins_kp.key hc]
    exact all_keys_union_split t.root ins_kp.key
  · suffices
      (t.root.split ins_kp.key).1.all_keys ∪
      ((t.root.splitUpper ins_kp.key).2.all_keys ∪ {ins_kp.key}) = t.root.all_keys by grind
    simp at hc
    -- Remove ins_kp from both sets
    rw [← all_keys_eq_split_splitUpper_r t.root ins_kp.key t.is_treap.2 ?_]
    rw [all_keys_union_split t.root ins_kp.key]

    grind


theorem delete_deletes_element (t : Treap Key Prio) (del_kp : KeyPrioPair Key Prio) :
  (Treap.delete t del_kp).root.all_keys = t.root.all_keys \ {del_kp.key} := by
    -- Split inequalities
  have l_lt_k := split_left_lt_k t.root t.is_treap.2 del_kp.key
  have r_ge_k := split_right_ge_k t.root t.is_treap.2 del_kp.key

  -- SplitUpper inequalities
  have l_le_k := splitUpper_left_le_k t.root t.is_treap.2 del_kp.key
  have r_gt_k := splitUpper_right_gt_k t.root t.is_treap.2 del_kp.key

  -- Unfold all Treap definitions, get only the TreapNode ones
  simp_all [Treap.delete, Treap.split, Treap.merge, Treap.splitUpper]

  rw [← all_keys_union_merge]

  -- Again, prove by cases
  by_cases hc : del_kp.key ∉ t.root.all_keys
  · rw [← split_eq_splitUpper_if_no_k t.root del_kp.key hc]
    rw [Set.diff_singleton_eq_self hc]
    exact all_keys_union_split t.root del_kp.key
  · rw [not_not] at hc
    rw [← all_keys_union_split t.root del_kp.key]
    rw [all_keys_eq_split_splitUpper_r t.root del_kp.key t.is_treap.2 hc]
    grind


-- Find returns the key iff the key is present in the treap
theorem find_finds_element (t : Treap Key Prio) (k : Key) :
  opt_get_key (Treap.find t k) = some k ↔ k ∈ t.root.all_keys := by
  unfold Treap.find
  simp only

  -- Split inequalities
  have l_less_k := split_left_lt_k t.root t.is_treap.2 k
  have r_ge_k := split_right_ge_k t.root t.is_treap.2 k

  split <;> expose_names
  · -- None case
    rw [leftmost_eq_none_iff] at heq
    simp_all [TreapNode.all_keys, opt_get_key, Treap.split]
    rw [← all_keys_union_split t.root k]
    suffices k ∉ (t.root.split k).1.all_keys ∧ k ∉ (t.root.split k).2.all_keys by grind
    constructor
    · -- Not in split left
      grind
    · -- Not in split right
      simp_all [TreapNode.all_keys]

  · -- Some case
    split <;> expose_names
    · -- Element found
      simp_all [opt_get_key]
      rw [← h]
      have := all_keys_subset_split_r t.root (t.split k).2.root k (by simp [Treap.split])
      grw [← this]
      refine leftmost_in_all_keys (t.split k).2.root kp.key ?_
      rw [heq]
      rfl
    · -- Element not found
      simp_all [opt_get_key]
      rw [← all_keys_union_split t.root k]
      suffices k ∉ (t.root.split k).1.all_keys ∧ k ∉ (t.root.split k).2.all_keys by grind
      constructor
      · -- Not in split left
        grind
      · -- Not in split right
        simp_all [Treap.split]
        by_contra hc
        have eq : kp.key = k := by
          -- k is the leftmost
          have k_leftmost := smallest_is_leftmost (t.root.split k).2 (t.split k).2.is_treap.2 k hc r_ge_k
          -- kp is the leftmost too
          have kp_leftmost : opt_get_key (t.root.split k).2.leftmost = some kp.key := by
            rw [heq]
            rfl
          -- then they must be equal
          simp_all only [Option.some.injEq]

        contradiction

/-
  Operations time complexity

-/

-- lenT with do notations
def leftmostT (tn : TreapNode Key Prio) : TimeM (Option (KeyPrioPair Key Prio)) := do
  match tn with
  | Tree.nil => return none
  | Tree.node kp l _ =>
    match l with
    | Tree.nil => ✓ (some kp)
    | Tree.node _ _ _ =>
      let lm ← leftmostT l
      ✓ lm

-- Prove the leftmostT has the same behavior as leftmost
theorem leftmostT_correctness (tn : TreapNode Key Prio) : (leftmostT tn).ret = TreapNode.leftmost tn := by
  match tn with
  | Tree.nil =>
    rfl
  | Tree.node kp l r =>
    match l with
    | Tree.nil =>
      rfl
    | Tree.node kp' l' r' =>
      unfold leftmostT
      unfold TreapNode.leftmost
      simp_all [bind, TimeM.tick, TimeM.ret_bind]
      exact leftmostT_correctness (node kp' l' r')

-- Prove the leftmostT is bounded by 1 + tn.height
theorem leftmostT_time (tn : TreapNode Key Prio) : (leftmostT tn).time ≤ 1 + tn.height := by
  match tn with
  | Tree.nil =>
    simp [leftmostT]
  | Tree.node kp l _ =>
    match l with
    | Tree.nil =>
      simp [leftmostT]
    | Tree.node kp' l' r' =>
      unfold leftmostT
      simp_all [bind, TimeM.tick, TimeM.time_of_bind]
      ring_nf
      have root_proof : (leftmostT (node kp' l' r')).time ≤ 1 + (node kp' l' r').height := by
        exact leftmostT_time (node kp' l' r')

      grw [root_proof]
      simp_all [Tree.height]
      omega

def splitT (tn : TreapNode Key Prio) (k : Key) : TimeM (TreapNode Key Prio × TreapNode Key Prio) := do
  match tn with
  | Tree.nil => return (Tree.nil, Tree.nil)
  | Tree.node kp l r =>
    if kp.key < k then
      -- Root goes left, split right
      let (split_l, new_r) ← splitT r k
      -- Return a (l, split_l) treap and a (new_r) treap
      let new_l := Tree.node kp l split_l
      ✓ (new_l, new_r)
    else
      -- Root goes right, split left
      let (new_l, split_r) ← splitT l k
      -- Return (new_l) treap and (split_r, r) treap
      let new_r := Tree.node kp split_r r
      ✓ (new_l, new_r)

-- Prove the splitT has the same behavior as leftmost
theorem splitT_correctness (tn : TreapNode Key Prio) (k : Key) : (splitT tn k).ret = TreapNode.split tn k := by
  match tn with
  | Tree.nil =>
    rfl
  | Tree.node kp l r =>
    simp only [TreapNode.split, splitT, bind, TimeM.tick]
    split_ifs <;> simp [TimeM.ret_bind]
    · constructor <;> rw [splitT_correctness]
    · constructor <;> rw [splitT_correctness]

-- Prove the splitT is bounded by 1 + tn.height
theorem splitT_time (tn : TreapNode Key Prio) (k : Key) : (splitT tn k).time ≤ 1 + tn.height := by
  match tn with
  | Tree.nil =>
    simp [splitT]
  | Tree.node kp l r =>
    simp only [splitT, bind, TimeM.tick]
    split_ifs <;> simp [TimeM.time_of_bind]
    · grw [splitT_time]
      omega
    · grw [splitT_time]
      omega

def splitUpperT (tn : TreapNode Key Prio) (k : Key) : TimeM (TreapNode Key Prio × TreapNode Key Prio) := do
  match tn with
  | Tree.nil => return (Tree.nil, Tree.nil)
  | Tree.node kp l r =>
    if kp.key ≤ k then
      -- Root goes left, splitUpper right
      let (splitUpper_l, new_r) ← splitUpperT r k
      -- Return a (l, splitUpper_l) treap and a (new_r) treap
      let new_l := Tree.node kp l splitUpper_l
      ✓ (new_l, new_r)
    else
      -- Root goes right, splitUpper left
      let (new_l, splitUpper_r) ← splitUpperT l k
      -- Return (new_l) treap and (splitUpper_r, r) treap
      let new_r := Tree.node kp splitUpper_r r
      ✓ (new_l, new_r)

-- Prove the splitUpperT has the same behavior as leftmost
theorem splitUpperT_correctness (tn : TreapNode Key Prio) (k : Key) : (splitUpperT tn k).ret = TreapNode.splitUpper tn k := by
  match tn with
  | Tree.nil =>
    rfl
  | Tree.node kp l r =>
    simp only [TreapNode.splitUpper, splitUpperT, bind, TimeM.tick]
    split_ifs <;> simp [TimeM.ret_bind]
    · constructor <;> rw [splitUpperT_correctness]
    · constructor <;> rw [splitUpperT_correctness]

-- Prove the splitUpperT is bounded by 1 + tn.height
theorem splitUpperT_time (tn : TreapNode Key Prio) (k : Key) : (splitUpperT tn k).time ≤ 1 + tn.height := by
  match tn with
  | Tree.nil =>
    simp [splitUpperT]
  | Tree.node kp l r =>
    simp only [splitUpperT, bind, TimeM.tick]
    split_ifs <;> simp [TimeM.time_of_bind]
    · grw [splitUpperT_time]
      omega
    · grw [splitUpperT_time]
      omega

def mergeT (l r : TreapNode Key Prio) : TimeM (TreapNode Key Prio) := do
  match l, r with
  | Tree.nil, Tree.nil => return Tree.nil
  | Tree.nil, Tree.node _ _ _ => ✓ r
  | Tree.node _ _ _, Tree.nil => ✓ l
  | Tree.node kp_1 l_1 r_1, Tree.node kp_2 l_2 r_2 =>
    -- We have to choose the root, use priorities
    if kp_1.prio ≥ kp_2.prio then
      -- Left goes as root
      let new_l := l_1
      let new_r ← mergeT r_1 (Tree.node kp_2 l_2 r_2)
      ✓ (Tree.node kp_1 new_l new_r)
    else
      -- Right as root
      let new_l ← mergeT (Tree.node kp_1 l_1 r_1) l_2
      let new_r := r_2
      ✓ (Tree.node kp_2 new_l new_r)

-- Prove the mergeT has the same behavior as leftmost
theorem mergeT_correctness (l r : TreapNode Key Prio) : (mergeT l r).ret = TreapNode.merge l r := by
  match l, r with
  | Tree.nil, Tree.nil
  | Tree.nil, Tree.node _ _ _
  | Tree.node _ _ _, Tree.nil => simp [mergeT, TreapNode.merge]
  | Tree.node kp_1 l_1 r_1, Tree.node kp_2 l_2 r_2 =>
    simp_all [mergeT, TreapNode.merge, bind, TimeM.tick]
    split_ifs <;> simp [TimeM.ret_bind]
    · exact mergeT_correctness r_1 (node kp_2 l_2 r_2)
    · exact mergeT_correctness (node kp_1 l_1 r_1) l_2

-- Prove the mergeT is bounded by sum of heights
theorem mergeT_time (l r : TreapNode Key Prio) (k : Key) : (mergeT l r).time ≤ l.height + r.height := by
  match l, r with
  | Tree.nil, Tree.nil
  | Tree.nil, Tree.node _ _ _
  | Tree.node _ _ _, Tree.nil => simp [mergeT]
  | Tree.node kp_1 l_1 r_1, Tree.node kp_2 l_2 r_2 =>
    simp_all [mergeT, bind, TimeM.tick]
    split_ifs <;> simp [TimeM.time_of_bind]
    · grw [mergeT_time r_1 (node kp_2 l_2 r_2) k]
      simp only [height]
      ring_nf
      omega
    · grw [mergeT_time (node kp_1 l_1 r_1) l_2 k]
      simp only [height]
      ring_nf
      omega

-- TODO: TreapNode.insert + TreapNode.delete time complexity
-- TODO: show that you have greatest as last element + smallest as first
-- TODO: maybe prove that merge of split is the same
-- or split of merge
-- TODO: sorted_l_r ENFORCES UNIQUENESS!
-- TODO: prove that it works only if the key is present?




















































































/-
  RandomTreap

  Augment the Treap to use uniformly random priorities, prove that height is bounded by O(log(N))
-/

-- Reuse variable for size of treap
variable {n : ℕ}
local notation "Ω" => Equiv.Perm (Fin n)

structure RandomTreap (Key : Type) (Prio : Type) [LinearOrder Key] [LinearOrder Prio] where
  treap: Treap Key Prio
  size: ℕ := n -- default value
  prio_func: Ω

-- The set is finite, enforce it to allow counting
def TreapNode.keys_finset : TreapNode Key Prio → Finset Key
  | Tree.nil => ∅
  | Tree.node kp l r => (keys_finset l) ∪ {kp.key} ∪ (keys_finset r)

-- The cardinality of keys_finset is the size of the treap
-- It will be implicitly passed to functions that need it

-- all_keys is already a set, prove they are equal
lemma keys_finset_eq_all_keys (t : TreapNode Key Prio) :
  (t.keys_finset : Set Key) = t.all_keys := by
  induction t with
  | nil => simp [TreapNode.keys_finset, TreapNode.all_keys]
  | node kp l r ihl ihr =>
    simp [TreapNode.keys_finset, TreapNode.all_keys, ihl, ihr]
    rw [← Set.insert_union]

/-
  Step 1: Define rank based on keys_finset

-/

-- Prove rank is less than size, if the element is present
-- Note that now everything is based on the key set!
lemma rank_less_size (t : TreapNode Key Prio) (k : Key) (h : k ∈ t.keys_finset) :
  (t.keys_finset.filter (fun key => key < k)).card < t.keys_finset.card := by
  -- (t.keys_finset.filter (fun key => key < k)).card < n := by
  apply Finset.card_lt_card
  grind

-- Define rank of a key in the treap (number of keys < k)
-- We don't need it to be efficient, since we only use it for proofs
def TreapNode.rank (t : TreapNode Key Prio) (k : Key)
  (h : k ∈ t.keys_finset) (n_size : t.keys_finset.card = n) : Fin n :=
  let num := (t.keys_finset.filter (fun key => key < k)).card
  let proof_card := rank_less_size t k h

  have proof_n : num < n := by
    rw [← n_size]
    exact proof_card

  { val := num,
    isLt := proof_n }

/-
  Step 2: Define ancestorship based on priorities

-/

-- We don't even need a valid treap!
-- def is_ancestor (anc k : Fin n) :
--   Bool :=
--   let ranks := Finset.Icc anc k
--   ∀ p ∈ ranks, σ p ≤ σ anc

-- /-
--   Step 3: Define depth based on ancestorship

-- -/

-- def depth (k : Fin n) : ℕ :=
--   -- ∑ j : Fin n, -- same def
--   ∑ j ∈ Finset.univ,
--     if is_ancestor σ j k then 1 else 0

/-
  Step 4: Assign priorities as a function of ranks by mapping σ to a random permutation

-/



































-- TODO: also uniqueness?

/-
  Merge and Split are inverse
  whattodo -- do i need this? also, treap that has only different priorities, do I need it??
-/
-- theorem merge_inv_split_left (k : Key) (kp : KeyPrioPair Key Prio) (l' r' : Tree (KeyPrioPair Key Prio)) (h : kp.key < k) :
--   node kp l' r' = TreapNode.merge (node kp l' (TreapNode.split r' k).1) (TreapNode.split r' k).2 := by
--   fun_induction TreapNode.merge
--   · grind
--   · grind


lemma kp_eq (a b : KeyPrioPair Key Prio) : a = b ↔ (a.key = b.key) ∧ (a.prio = b.prio) := by
  constructor
  · intro h
    subst h
    simp_all only [and_self]
  · intro h
    cases a
    simp_all


-- TODO: root and prio and key?? idk multiple defs..
-- TODO extra
inductive DistinctPrios : TreapNode Key Prio → Prop
  | nil : DistinctPrios Tree.nil
  | node (tn : KeyPrioPair Key Prio) (l r : TreapNode Key Prio) :
    -- Recursively unique
    DistinctPrios l →
    DistinctPrios r →
    -- Root priority is not in children
    tn.prio ∉ l.all_prios →
    tn.prio ∉ r.all_prios →
    -- Left and Right priority sets don't overlap
    Disjoint l.all_prios r.all_prios →
    DistinctPrios (Tree.node tn l r)


lemma roots_eq_prio (a b : TreapNode Key Prio)
  (a_dip : DistinctPrios a) (b_dip : DistinctPrios b) (ab_nodes : a.all_nodes = b.all_nodes) :
  a.root = b.root ↔ (a.prio = b.prio) := by
  sorry
  -- constructor
  -- · intro h
  --   subst h
  --   simp_all only
  -- · intro h
  --   match a, b with
  --   | Tree.nil, Tree.nil => sorry
  --   | Tree.nil, Tree.node kp l r => sorry
  --   | Tree.node kp l r, Tree.nil => sorry
  --   | Tree.node kp_1 l_1 r_1, kp_2 l_2 r_2 =>
  --     sorry

-- TODO show strict inequality when DistinctPrios
lemma prio_max (tn : TreapNode Key Prio) (tn_heap : IsHeap tn) (tn_dip : DistinctPrios tn) :
  ∀ p ∈ tn.all_prios_left ∪ tn.all_prios_right, p < tn.prio := by
  match tn with
  | Tree.nil => simp_all [TreapNode.all_prios_left, TreapNode.all_prios_right]
  | Tree.node kp l r =>
    cases tn_heap; rename_i l_heap l_ge r_heap r_ge
    by_cases hc : kp.prio ∈ TreapNode.all_prios_left (node kp l r) ∪ TreapNode.all_prios_right (node kp l r)
    · simp_all [TreapNode.all_prios_left, TreapNode.all_prios_right, TreapNode.prio]
      suffices ∀ p ∈ TreapNode.all_prios l ∪ TreapNode.all_prios r, p ≠ kp.prio by grind
      cases tn_dip; rename_i l_dip l_nin r_dip r_nin disj
      simp_all
    · simp_all [TreapNode.all_prios_left, TreapNode.all_prios_right, TreapNode.prio]
      grind

lemma all_nodes_set_eq_all_prios (t : TreapNode Key Prio) :
  Set.image (fun n : KeyPrioPair Key Prio => n.prio) t.all_nodes = t.all_prios := by
  sorry

lemma same_nodes_same_root (a b : TreapNode Key Prio)
  (a_bst : IsBST a) (b_bst : IsBST b)
  (a_heap : IsHeap a) (b_heap : IsHeap b)
  (a_dip : DistinctPrios a) (b_dip : DistinctPrios b) :
  a.all_nodes = b.all_nodes → a.root = b.root := by
  intro hs
  match a, b with
  | Tree.nil, Tree.nil => simp_all only
  | Tree.nil, Tree.node kp l r
  | Tree.node kp l r, Tree.nil =>
    exfalso
    have h : kp ∈ (TreapNode.all_nodes l ∪ {kp} ∪ TreapNode.all_nodes r) := by
      simp
    unfold TreapNode.all_nodes at hs
    -- satisfy both cases
    try rw [← hs] at h; assumption
    try rw [hs] at h; assumption
  | Tree.node kp_1 l_1 r_1, Tree.node kp_2 l_2 r_2 =>
    -- simp_all [TreapNode.root]
    -- root node is unique, extract it
    have a_max := prio_max (node kp_1 l_1 r_1) a_heap a_dip
    have b_max := prio_max (node kp_2 l_2 r_2) b_heap b_dip
    simp_all
    rw [roots_eq_prio (node kp_1 l_1 r_1) (node kp_2 l_2 r_2) a_dip b_dip hs]

    have h_prio_sets_eq : TreapNode.all_prios (node kp_1 l_1 r_1) = TreapNode.all_prios (node kp_2 l_2 r_2) := by
      -- "Image of nodes(A) = Prios(A)"
      rw [← all_nodes_set_eq_all_prios (node kp_1 l_1 r_1)]
      -- "Image of nodes(B) = Prios(B)"
      rw [← all_nodes_set_eq_all_prios (node kp_2 l_2 r_2)]
      -- Since nodes(A) = nodes(B) (hs), the images must be equal
      rw [hs]

    -- Now we can use the equality of prio sets to show prio equality
    simp_all [TreapNode.prio, TreapNode.all_prios]
    sorry

-- TODO: harden prio to have only different elements

-- Same nodes has same morphology
theorem same_nodes_same_treap (a b : TreapNode Key Prio)
  (a_bst : IsBST a) (b_bst : IsBST b)
  (a_heap : IsHeap a) (b_heap : IsHeap b) :
  a.all_nodes = b.all_nodes ↔ a = b := by
  -- TODO: rewrite with match
  constructor
  · intro hs
    cases a
    · -- a is nil
      simp_all [TreapNode.all_nodes]
      cases b
      · -- b is nil
        rfl
      · -- b is node
        rename_i kp l r
        exfalso
        have h : kp ∈ (TreapNode.all_nodes l ∪ {kp} ∪ TreapNode.all_nodes r) := by
          simp
        unfold TreapNode.all_nodes at hs
        rw [← hs] at h
        assumption
    · -- a is node
      cases b
      · -- b is nil
        rename_i kp l r
        exfalso
        have h : kp ∈ (TreapNode.all_nodes l ∪ {kp} ∪ TreapNode.all_nodes r) := by
          simp
        unfold TreapNode.all_nodes at hs
        rw [hs] at h
        assumption
      · -- b is node
        rename_i kp_1 l_1 r_1 kp_2 l_2 r_2
        simp only [node.injEq]
        cases a_bst; rename_i l_1_bst _ r_1_bst _
        cases b_bst; rename_i l_2_bst _ r_2_bst _
        cases a_heap; rename_i l_1_heap _ r_1_heap _
        cases b_heap; rename_i l_2_heap _ r_2_heap _
        constructor <;> all_goals (try constructor)
        · simp_all [TreapNode.all_nodes]
          sorry
        · rw [← same_nodes_same_treap l_1 l_2 l_1_bst l_2_bst l_1_heap l_2_heap]
          simp_all [TreapNode.all_nodes]
          sorry
        · sorry

  · simp_all

lemma merge_chooses_left_root (l r : TreapNode Key Prio) (h_prio : l.prio ≥ r.prio) :
  (TreapNode.merge l r).root = l.root := by
  match l, r with
  | Tree.nil, Tree.nil
  | Tree.nil, Tree.node _ _ _
  | Tree.node _ _ _, Tree.nil => simp_all [TreapNode.merge, TreapNode.prio]
  | Tree.node kp_1 l_1 r_1, Tree.node kp_2 l_2 r_2 =>
    unfold TreapNode.merge; split_ifs <;> rename_i h_if
    · simp_all only [ge_iff_le]
      rfl
    · simp_all [TreapNode.prio]

lemma merge_chooses_right_root (l r : TreapNode Key Prio) (h_prio : l.prio < r.prio) :
  (TreapNode.merge l r).root = r.root := by
  match l, r with
  | Tree.nil, Tree.nil
  | Tree.nil, Tree.node _ _ _
  | Tree.node _ _ _, Tree.nil => simp_all [TreapNode.merge, TreapNode.prio]
  | Tree.node kp_1 l_1 r_1, Tree.node kp_2 l_2 r_2 =>
    unfold TreapNode.merge; split_ifs <;> rename_i h_if
    · simp_all [TreapNode.prio]
      grind
    · simp_all [TreapNode.prio]
      rfl

-- lemma merge_chooses_left_root (tn l r : TreapNode Key Prio) (h_prio : l.prio ≥ r.prio) :
--   (TreapNode.merge l r) = tn → tn.prio = l.prio := by
--   match l, r with
--   | Tree.nil, Tree.nil
--   | Tree.nil, Tree.node _ _ _
--   | Tree.node _ _ _, Tree.nil => intro tn; subst tn; simp_all [TreapNode.merge, TreapNode.prio]
--   | Tree.node kp_1 l_1 r_1, Tree.node kp_2 l_2 r_2 =>
--     intro tn; subst tn
--     unfold TreapNode.merge; split_ifs <;> rename_i h_if
--     · simp_all only [ge_iff_le]
--       rfl
--     · simp_all [TreapNode.prio]

-- lemma merge_chooses_right_root (tn l r : TreapNode Key Prio) (h_prio : l.prio < r.prio) :
--   (TreapNode.merge l r) = tn → tn.prio = r.prio := by
--   match l, r with
--   | Tree.nil, Tree.nil
--   | Tree.nil, Tree.node _ _ _
--   | Tree.node _ _ _, Tree.nil => intro tn; subst tn; simp_all [TreapNode.merge, TreapNode.prio]
--   | Tree.node kp_1 l_1 r_1, Tree.node kp_2 l_2 r_2 =>
--     intro tn; subst tn
--     unfold TreapNode.merge; split_ifs <;> rename_i h_if
--     · simp_all [TreapNode.prio]
--       grind
--     · simp_all [TreapNode.prio]


theorem merge_inv_split (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) :
  let (l, r) := tn.split k;
  tn = TreapNode.merge l r := by
  match tn with
  | Tree.nil =>
    simp_all [TreapNode.split, TreapNode.merge]
  | Tree.node kp l r =>
    have l_less := split_left_lt_k (node kp l r) tn_proof k
    have r_ge := split_right_ge_k (node kp l r) tn_proof k
    simp_all
    -- cases tn_proof; rename_i l_proof l_keys_less r_proof r_keys_ge
    unfold TreapNode.merge
    split <;> simp_all -- handle all cases
    · simp_all [TreapNode.split]
      aesop
    · rename_i kp' l' r' eq_l eq_r
      simp_all [TreapNode.split]
      sorry
    · rename_i kp' l' r' eq_l eq_r
      sorry
    · rename_i kp_1 l_1 r_1 kp_2 l_2 r_2 eq_l eq_r
      -- simp_all [TreapNode.split]
      split_ifs <;> rename_i h_if
      · rw [← ge_iff_le] at h_if
        have kp_eq := merge_chooses_left_root (node kp_1 l_1 r_1) (node kp_2 l_2 r_2) h_if
        simp [TreapNode.root] at kp_eq
        have kp_eq : kp = kp_1 := by
          -- rw [← eq_l]
          -- rw [← eq_r]


          sorry
        have l_eq : l = l_1 := by
          sorry
        have r_eq : r = (TreapNode.merge r_1 (node kp_2 l_2 r_2)) := by
          sorry
        subst kp_eq l_eq r_eq
        simp_all only
      · have kp_eq : kp = kp_2 := by
          sorry
        have l_eq : l = (TreapNode.merge (node kp_1 l_1 r_1) l_2) := by
          sorry
        have r_eq : r = r_2 := by
          sorry
        subst kp_eq l_eq r_eq
        simp_all only




/-
  Empirical test

-/

def main : IO Unit := do
  let mut t : Treap ℕ ℕ := Treap.empty
  let n_elems := 1000000

  for i in [1 : n_elems] do
    let rand_prio ← IO.rand 0 1000000000
    t := t.insert { key := i, prio := rand_prio }

  IO.println s!"Done inserting {n_elems} elements."

  let h := t.root.height

  IO.println s!"Final Height after insertion: {h}"

  -- Compare with expected height
  let expected := 3 * Float.log2 n_elems.toFloat
  IO.println s!"Expected Height (approx): {expected}"

  -- Remove half elements
  for i in [n_elems / 4 : n_elems / 4 + n_elems / 2] do
    let kp := t.find i
    match kp with
    | none => continue
    | some kp => do
      t := t.delete kp

  let h := t.root.height

  IO.println s!"Final Height after removing half elements: {h}"

  -- Compare with expected height
  let expected := 3 * Float.log2 (n_elems / 2).toFloat
  IO.println s!"Expected Height (approx): {expected}"


-- #eval main


end TreapLogic
