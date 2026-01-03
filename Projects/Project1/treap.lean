/-
  Treaps

-/

import Mathlib
import Mathlib.Tactic
-- set_option diagnostics true

namespace TreapLogic
open Tree

/-
  Base Treap definitions and properties

  We use explicit type variables for functions. structures and abbrevs are defined implicitely
  LinearOrder is required for both Key and Prio types to enable comparisons

  This is as basic as it gets: the Treap will be augmented twice, first to a DisjTreap (enforcing different priorities),
  then to a RandTreap (using randomized priorities)

  Treap → DisjTreap → RandTreap
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
  | Tree.node (kp : KeyPrioPair Key Prio) _ _ => kp

-- Getter for root node key
def TreapNode.key : TreapNode Key Prio → Option Key
  | Tree.nil => none
  | Tree.node (kp : KeyPrioPair Key Prio) _ _ => kp.key

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

-- Comodity functions
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
    (∀ p, p ∈ l.all_prios → tn.prio ≥ p) →
    (∀ p, p ∈ r.all_prios → tn.prio ≥ p) →
    -- Recursively require left and right subtrees to also satisfy heap property
    IsHeap l →
    IsHeap r →
    -- Conclude that the current node satisfies the heap property
    IsHeap (Tree.node tn l r)

-- Treap property: both BST and Heap properties
def IsTreap (tn : TreapNode Key Prio) : Prop :=
  IsHeap tn ∧ IsBST tn

structure Treap (Key : Type) (Prio : Type) [LinearOrder Key] [LinearOrder Prio] where
  root : TreapNode Key Prio
  is_treap : IsTreap root

/-
  Base methods

  We define all methods on TreapNodes, then migrate them to Treaps, proving their correctness there
-/

-- TODO
-- def TreapNode.fromList

-- If the treap node is empty
def TreapNode.isEmpty (tn : TreapNode Key Prio) : Bool :=
  match tn with
  | Tree.nil => true
  | _ => false

-- Builder for singleton treap nodes
def TreapNode.singleton (kp : KeyPrioPair Key Prio) : TreapNode Key Prio :=
  Tree.node kp Tree.nil Tree.nil

-- Get the leftmost key in the treap
def TreapNode.leftmost (tn : TreapNode Key Prio) : Option Key :=
  match tn with
  | Tree.nil => none
  | Tree.node kp l _ =>
    match l with
    | Tree.nil => some kp.key
    | Tree.node _ _ _ => TreapNode.leftmost l

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

-- Helper to split the element with l ≤ k < r
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

-- Merge two sorted treaps
def TreapNode.merge (l r : TreapNode Key Prio) : TreapNode Key Prio :=
  match l, r with
  | Tree.nil, Tree.nil => Tree.nil
  | Tree.nil, Tree.node _ _ _ => r
  | Tree.node _ _ _, Tree.nil => l
  | Tree.node kp_1 l_1 r_1, Tree.node kp_2 l_2 r_2 =>
    -- We have to choose the root, use priorities
    -- TODO: how do optionals work in this case?
    if kp_1.prio ≥ kp_2.prio then
      -- Left goes as root
      let new_l := l_1
      let new_r := TreapNode.merge r_1 (Tree.node kp_2 l_2 r_2)
      -- let new_r := TreapNode.merge r_1 r -- r (termination breaks)
      Tree.node kp_1 new_l new_r
    else
      -- Right as root
      let new_l := TreapNode.merge (Tree.node kp_1 l_1 r_1) l_2
      -- let new_l := TreapNode.merge l l_2 -- l (termination breaks)
      let new_r := r_2
      Tree.node kp_2 new_l new_r

/-
  Operations correctness

  Ensure everything stays a Treap while doing splitting and merging
  Ensure a leftmost operation returns the smallest element (TODO)
-/

/-
  Helpers
-/

-- All elems on the left are < all elems on the right
lemma left_less_right (tn : TreapNode Key Prio) (bst_prop : IsBST tn) :
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
  -- match TreapNode.merge l r with -- lol you can do this
  match l, r with
  | Tree.nil, Tree.nil
  | Tree.nil, Tree.node _ _ _
  | Tree.node _ _ _, Tree.nil => simp_all [TreapNode.merge, TreapNode.all_prios]
  | Tree.node kp_1 l_1 r_1, Tree.node kp_2 l_2 r_2 =>
    -- simp_all [TreapNode.all_prios]
    unfold TreapNode.merge
    split_ifs <;> expose_names <;> simp_all
    · simp_all [TreapNode.all_prios]
      rw [← all_prios_union_merge r_1 (node kp_2 l_2 r_2)]
      nth_rw 7 [TreapNode.all_prios.eq_def]
      simp_all
      rw [←
        Set.union_assoc (insert kp_1.prio (TreapNode.all_prios l_1)) (TreapNode.all_prios r_1)
          (insert kp_2.prio (TreapNode.all_prios l_2) ∪ TreapNode.all_prios r_2)]
    · -- You can prove it only by rewriting expressions
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
lemma split_left_less_k (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) :
  let (split_l, _) := TreapNode.split tn k
  ∀ lk, lk ∈ split_l.all_keys → lk < k := by
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
        apply split_left_less_k
        exact h_2

      unfold TreapNode.all_keys
      grind
    · -- Apply recursion again
      apply split_left_less_k
      exact h

-- All keys on the right of a split k are ≥ k
lemma split_right_ge_k (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) :
  let (_, split_r) := TreapNode.split tn k
  ∀ rk, rk ∈ split_r.all_keys → k ≤ rk := by
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

-- SplitUpper are copy-pasted and shamelessly adjusted
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
  let (splitUpper_l, _) := TreapNode.splitUpper tn k
  ∀ lk, lk ∈ splitUpper_l.all_keys → lk ≤ k := by
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

-- All keys on the right of a splitUpper k are ≥ k
lemma splitUpper_right_greater_k (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) :
  let (_, splitUpper_r) := TreapNode.splitUpper tn k
  ∀ rk, rk ∈ splitUpper_r.all_keys → k < rk := by
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
    · exact splitUpper_right_greater_k r r_proof k
    · unfold TreapNode.all_keys
      intro rk rk_h
      -- Cover all cases (in left, as root, in right)
      cases rk_h
      · rename_i rk_h
        cases rk_h
        · rename_i le_h rk_h; revert rk_h rk
          exact splitUpper_right_greater_k l l_proof k
        · rename_i rk_h
          rw [Set.mem_singleton_iff] at rk_h
          rw [rk_h]
          assumption
      · rename_i le_h rk_h; revert rk_h rk -- reinsert into hypotheses
        by_cases hc : k = kp.key
        · simp_all
        · grind

-- TODO: maybe prove that merge of split is the same
-- or split of merge

/-
  Split correctness
-/

-- Splitting creates a BST on the left
theorem split_IsBST_left (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) : IsBST (TreapNode.split tn k).1 := by
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
theorem split_IsBST_right (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) : IsBST (TreapNode.split tn k).2 := by
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
theorem split_IsHeap_left (tn : TreapNode Key Prio) (tn_proof : IsHeap tn) (k : Key) : IsHeap (TreapNode.split tn k).1 := by
  fun_induction TreapNode.split
  · exact IsHeap.nil
  · expose_names; cases tn_proof; expose_names
    simp_all

    apply IsHeap.node
    · simp_all
    · simp_all
      grw [all_prios_subset_split_l a_1 split_l k]
      exact h_5
      · simp_all
    · simp_all
    · simp_all
  · cases tn_proof
    simp_all

-- Splitting creates a Heap on the right
theorem split_IsHeap_right (tn : TreapNode Key Prio) (tn_proof : IsHeap tn) (k : Key) : IsHeap (TreapNode.split tn k).2 := by
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
-/

-- Splitting creates a BST on the left
theorem splitUpper_IsBST_left (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) : IsBST (TreapNode.splitUpper tn k).1 := by
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
theorem splitUpper_IsBST_right (tn : TreapNode Key Prio) (tn_proof : IsBST tn) (k : Key) : IsBST (TreapNode.splitUpper tn k).2 := by
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
theorem splitUpper_IsHeap_left (tn : TreapNode Key Prio) (tn_proof : IsHeap tn) (k : Key) : IsHeap (TreapNode.splitUpper tn k).1 := by
  fun_induction TreapNode.splitUpper
  · exact IsHeap.nil
  · expose_names; cases tn_proof; expose_names
    simp_all

    apply IsHeap.node
    · simp_all
    · simp_all
      grw [all_prios_subset_splitUpper_l a_1 split_l k]
      exact h_5
      · simp_all
    · simp_all
    · simp_all
  · cases tn_proof
    simp_all

-- Splitting creates a Heap on the right
theorem splitUpper_IsHeap_right (tn : TreapNode Key Prio) (tn_proof : IsHeap tn) (k : Key) : IsHeap (TreapNode.splitUpper tn k).2 := by
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

/-
  Merge correctness
-/

-- TODO: sorted_l_r ENFORCES UNIQUENESS!
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
        · simp_all only [ge_iff_le]
        · cases r_proof; rename_i l_2_proof l_2_ge r_2_proof r_2_ge
          simp_all only [ge_iff_le]
          trans kp_2.prio
          · grind [TreapNode.all_prios]
          · exact h_if
      · exact l_1_proof
      · apply merge_IsHeap r_1 (Tree.node kp_2 l_2 r_2) r_1_proof r_proof
        -- suffices ∀ kl ∈ TreapNode.all_prios (node kp_1 l_1 r_1), ∀ kr ∈ TreapNode.all_prios (node kp_2 l_2 r_2), kl < kr by
        --   grind [TreapNode.all_prios]
        -- exact sorted_l_r
    · cases r_proof; rename_i l_2_proof l_2_ge r_2_proof r_2_ge
      apply IsHeap.node
      · rw [← all_prios_union_merge]
        intro p hp
        cases hp
        · cases l_proof; rename_i l_1_proof l_1_ge r_1_proof r_1_ge
          simp_all only [ge_iff_le]
          trans kp_1.prio
          · grind [TreapNode.all_prios]
          · grind
        · simp_all only [ge_iff_le]
      · exact r_2_ge
      · apply merge_IsHeap (Tree.node kp_1 l_1 r_1) l_2 l_proof l_2_proof
        -- suffices ∀ kl ∈ TreapNode.all_prios (node kp_1 l_1 r_1), ∀ kr ∈ TreapNode.all_prios (node kp_2 l_2 r_2), kl < kr by
        --   grind [TreapNode.all_prios]
        -- exact sorted_l_r
      · exact r_2_proof

/-
  Singleton correctness
-/

-- Singleton is a BST
theorem singleton_isBST (kp : KeyPrioPair Key Prio) : IsBST (TreapNode.singleton kp) := by
  apply IsBST.node <;> simp_all [TreapNode.all_keys, IsBST.nil]

-- Singleton is a Heap
theorem singleton_isHeap (kp : KeyPrioPair Key Prio) : IsHeap (TreapNode.singleton kp) := by
  apply IsHeap.node <;> simp_all [TreapNode.all_prios, IsHeap.nil]

/-
  Composite operations

  We now define more operations on Treaps, and prove their correctness.
  These operations will be:
  - insert
  - delete
  - find
  - build (TODO)
-/

-- Find operation, split the treap and check leftmost of right treap
-- TODO: return the KeyPrioPair instead of Bool?
def TreapNode.find (tn : TreapNode Key Prio) (k : Key) : Bool :=
  let (_, r) := TreapNode.split tn k
  if TreapNode.leftmost r = some k then
    true
  else
    false

-- Insert operation, split the treap and perform two merges
def TreapNode.insert (tn : TreapNode Key Prio) (kp : KeyPrioPair Key Prio) : TreapNode Key Prio :=
  let (l, r) := TreapNode.split tn kp.key
  let new_node := Tree.node kp Tree.nil Tree.nil
  let merged_right := TreapNode.merge new_node r -- First merge right (ensures l < r)
  TreapNode.merge l merged_right

-- Delete operation, split the treap twice and merge the leftovers
-- TODO: as for now, deletes all the occurrences of a key
def TreapNode.delete (tn : TreapNode Key Prio) (k : Key) : TreapNode Key Prio :=
  let (l, _) := TreapNode.split tn k -- keep < k
  let (_, r) := TreapNode.splitUpper tn k -- keep > k
  TreapNode.merge l r

/-
  Treap operations (joint correctness and operation)

-/

def Treap.singleton (kp : KeyPrioPair Key Prio) : Treap Key Prio :=
  let root := TreapNode.singleton kp
  have singleton_bst_proof : IsBST root := singleton_isBST kp
  have singleton_heap_proof : IsHeap root := singleton_isHeap kp

  have treap_proof : IsTreap root := by
    simp_all [IsTreap]

  { root := root, is_treap := treap_proof }

-- Leftmost doesn't need correctness proofs (TODO: maybe only that it's the smallest element...), doesn't produce treaps
def Treap.leftmost (t : Treap Key Prio) : Option Key :=
  -- Transfer the call
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

-- TODO: fill it
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

-- TODO: prove that it works only if the key is present?
def Treap.find (t : Treap Key Prio) (k : Key) : Bool :=
  TreapNode.find t.root k

-- We discard other existing occurrences of the same key
def Treap.insert (t : Treap Key Prio) (kp : KeyPrioPair Key Prio) : Treap Key Prio :=
  let split_l_key := t.split kp.key
  -- Save split proofs
  have l_less_k := split_left_less_k t.root t.is_treap.2 kp.key
  have r_ge_k := split_right_ge_k t.root t.is_treap.2 kp.key

  let split_key_r := t.splitUpper kp.key
  -- Save splitUpper proofs
  have l_le_k := splitUpper_left_le_k t.root t.is_treap.2 kp.key
  have r_gt_k := splitUpper_right_greater_k t.root t.is_treap.2 kp.key

  let new_node := Treap.singleton kp

  -- We need new_node < r
  have kp_less_r : (∀ kl ∈ new_node.root.all_keys, ∀ kr ∈ TreapNode.all_keys split_key_r.2.root, kl < kr) := by
    subst new_node
    subst split_key_r
    subst split_l_key
    simp_all [Treap.singleton, TreapNode.singleton, TreapNode.all_keys]
    exact r_gt_k

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


/-
  Operations time complexity

-/


-- TODO...

/-
  Randomness (oh shet)

-/

/-
  Merge and Split are inverse
  whattodo
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
    have l_less := split_left_less_k (node kp l r) tn_proof k
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

    -- simp_all [TreapNode.split]
    -- -- grind [TreapNode.split, TreapNode.merge]
    -- split_ifs <;> simp_all <;> rename_i h
    -- · sorry
    -- · sorry







    -- · apply merge_inv_split_left; assumption
    -- · -- split the merge into cases
    --   -- match (node kp l' (TreapNode.split r' k).1), (TreapNode.split r' k).2 with
    --   -- | Tree.nil, Tree.nil =>
    --   --   simp_all [TreapNode.merge]

    --   -- | _, Tree.nil => sorry
    --   -- | Tree.node kp_1 l_1 r_1, Tree.node kp_2 l_2 r_2 => sorry
    --   -- unfold TreapNode.merge; simp_all
    --   -- split
    --   -- · simp_all only [reduceCtorEq]
    --   -- · simp_all only [reduceCtorEq]
    --   -- · rename_i l r
    --   --   sorry
    --   -- · sorry

























-- /-
--   Aliases for Tree functions in treaps
--   TODO: decide if you want these
-- -/
-- def Tree.all_keys : TreapNode Key Prio → Set Key := TreapNode.all_keys


/-
  We could do this directly on Treap structure, but it's better to prove everything with least hypothesis as possible,
  and only then build the treap proofs easily by merging operations + correctness
-/

/-
  Treap proofs

-/


end TreapLogic
