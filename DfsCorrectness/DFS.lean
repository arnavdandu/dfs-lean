import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation
import Mathlib.Tactic
import DfsCorrectness.FoldlUnion
import DfsCorrectness.CycleRemoval

/-!
# Depth-first search on finite types

This file provides a generic DFS algorithm that computes the set of vertices
reachable from a source via a neighbor function, and proves it correct against
`Relation.ReflTransGen`.

## Main definitions

* `dfsReach` — DFS from a vertex with a visited set
* `DfsWitness` — inductive reachability witness compatible with DFS

## Main theorems

* `dfsReach_correct` — `v ∈ dfsReach neighbors s ∅ ↔ ReflTransGen (neighborRel neighbors) s v`
-/

universe u

section DFS

variable {V : Type u} [Fintype V] [DecidableEq V]

-- ============================================================================
-- Termination measure
-- ============================================================================

/-- Adding a fresh element strictly decreases complement cardinality. -/
lemma compl_card_lt_of_insert
    {vis : Finset V} {s : V} (h : s ∉ vis) :
    ((vis ∪ {s})ᶜ).card < (visᶜ).card := by
  observe h_sub : visᶜ ∩ {s}ᶜ ⊆ visᶜ
  have h_neq : visᶜ ∩ {s}ᶜ ≠ visᶜ := by simp [h]
  observe h_proper_sub : visᶜ ∩ {s}ᶜ ⊂ visᶜ
  observe h_goal : (visᶜ ∩ {s}ᶜ).card < (visᶜ).card
  simp only [Finset.compl_union]
  exact h_goal

-- ============================================================================
-- DFS algorithm
-- ============================================================================

/-- Depth-first search computing the set of reachable vertices.

Each neighbor's DFS starts from `vis' = vis ∪ {curr}`, and results are
unioned into the fold accumulator. -/
noncomputable def dfsReach {V : Type u} [Fintype V] [DecidableEq V]
    (neighbors : V → Finset V) (curr : V) (vis : Finset V) : Finset V :=
  if _h : curr ∈ vis then vis
  else
    let vis' := vis ∪ {curr}
    (neighbors curr).toList.foldl
      (fun acc next => acc ∪ dfsReach neighbors next vis') vis'
termination_by (visᶜ).card
decreasing_by exact compl_card_lt_of_insert _h

-- ============================================================================
-- Basic unfolding lemmas
-- ============================================================================

/- If `curr` is already visited, i.e. `curr ∈ vis`, then the result is just `vis`. -/
theorem dfsReach_visited (neighbors : V → Finset V)
    {curr : V} {vis : Finset V} (h : curr ∈ vis) :
    dfsReach neighbors curr vis = vis := by
  unfold dfsReach; split <;> [rfl; contradiction]

/- If `curr` is fresh, i.e. `curr ∉ vis`, then we need to explore its neighbors. -/
theorem dfsReach_fresh (neighbors : V → Finset V)
    {curr : V} {vis : Finset V} (h : curr ∉ vis) :
    dfsReach neighbors curr vis =
      (neighbors curr).toList.foldl
        (fun acc next => acc ∪ dfsReach neighbors next (vis ∪ {curr}))
        (vis ∪ {curr}) := by
  conv_lhs => unfold dfsReach
  simp [h]

-- ============================================================================
-- Monotonicity
-- ============================================================================

/-- The initial visited set is always a subset of the result. -/
theorem vis_subset_dfsReach (neighbors : V → Finset V) (curr : V) (vis : Finset V) :
    vis ⊆ dfsReach neighbors curr vis := by
  by_cases h : curr ∈ vis
  · rw [dfsReach_visited neighbors h]
  · rw [dfsReach_fresh neighbors h]
    exact Finset.subset_union_left.trans
      (foldl_union_subset_init (fun next => dfsReach neighbors next (vis ∪ {curr}))
        (neighbors curr).toList (vis ∪ {curr}))

/-- `curr` is in the result when `curr ∉ vis`. -/
theorem curr_mem_dfsReach (neighbors : V → Finset V)
    {curr : V} {vis : Finset V} (h : curr ∉ vis) :
    curr ∈ dfsReach neighbors curr vis := by
  rw [dfsReach_fresh neighbors h]
  have hmem : curr ∈ vis ∪ {curr} := Finset.mem_union_right _ (Finset.mem_singleton_self _)
  exact foldl_union_subset_init (fun next => dfsReach neighbors next (vis ∪ {curr}))
    (neighbors curr).toList (vis ∪ {curr}) hmem

-- ============================================================================
-- The neighbor relation
-- ============================================================================

/-- The relation induced by a neighbor function. -/
def neighborRel (neighbors : V → Finset V) (a b : V) : Prop := b ∈ neighbors a

-- ============================================================================
-- DFS-compatible reachability witness
-- ============================================================================

/-- Inductive witness that `s` is reachable from `q` via neighbors,
compatible with the DFS visited-set protocol.

A `DfsWitness neighbors vis q s` is a "stateful path" from `q` to `s`.
It mirrors the execution of `dfsReach` by ensuring:

. Every vertex on the path is "fresh" (not in `vis`) when first encountered.
. The visited set is updated (marking the current vertex) before exploring further. -/
inductive DfsWitness (neighbors : V → Finset V) :
    Finset V → V → V → Prop where
  /-- Base case: we have reached the target `q`.
  Since `q ∉ vis`, this is a "new discovery" that the DFS algorithm will
  successfully add to its result set. -/
  | here {vis : Finset V} {q : V}
      (hq : q ∉ vis) :
      DfsWitness neighbors vis q q
  /-- Recursive step: we move from `q` to a neighbor `next`.
  To be DFS-compatible, `q` must be fresh, and the remainder of the path
  must be valid starting from `next` with `q` added to the visited set. -/
  | step {vis : Finset V} {q next s : V}
      (hq : q ∉ vis)
      (hadj : next ∈ neighbors q)
      (hrest : DfsWitness neighbors (vis ∪ {q}) next s) :
      DfsWitness neighbors vis q s

-- ============================================================================
-- Soundness
-- ============================================================================

/-- Soundness: every vertex in the result is either in `vis` or reachable. -/
theorem dfsReach_sound (neighbors : V → Finset V) (curr : V) (vis : Finset V) :
    ∀ v ∈ dfsReach neighbors curr vis,
      v ∈ vis ∨ Relation.ReflTransGen (neighborRel neighbors) curr v := by
  induction h_measure : (visᶜ).card using Nat.strongRecOn generalizing curr vis with
  | _ n ih =>
    intro v hv
    by_cases hcurr : curr ∈ vis
    · rw [dfsReach_visited neighbors hcurr] at hv
      left; exact hv
    · rw [dfsReach_fresh neighbors hcurr] at hv
      rw [mem_foldl_union] at hv
      rcases hv with hv | ⟨next, hnext_mem, hv_next⟩
      · rw [Finset.mem_union, Finset.mem_singleton] at hv
        rcases hv with hv | rfl
        · left; exact hv
        · right; exact Relation.ReflTransGen.refl
      · have h_card : ((vis ∪ {curr})ᶜ).card < (visᶜ).card :=
          compl_card_lt_of_insert hcurr
        have := ih ((vis ∪ {curr})ᶜ).card (by omega) next (vis ∪ {curr}) rfl v hv_next
        rcases this with hv_vis' | hreach
        · rw [Finset.mem_union, Finset.mem_singleton] at hv_vis'
          rcases hv_vis' with hv | rfl
          · left; exact hv
          · right; exact Relation.ReflTransGen.refl
        · right
          have hnext_neighbor : next ∈ (neighbors curr).toList := hnext_mem
          rw [Finset.mem_toList] at hnext_neighbor
          exact Relation.ReflTransGen.head
            (show neighborRel neighbors curr next from hnext_neighbor) hreach

-- ============================================================================
-- Completeness
-- ============================================================================

/-- From a `DfsWitness`, the target is in the DFS result. -/
theorem dfsReach_complete_from_witness (neighbors : V → Finset V)
    {vis : Finset V} {q s : V}
    (hw : DfsWitness neighbors vis q s) :
    s ∈ dfsReach neighbors q vis := by
  induction hw with
  | here hq => exact curr_mem_dfsReach neighbors hq
  | step hq hadj _ ih =>
    rw [dfsReach_fresh neighbors hq]
    exact mem_foldl_union_of_mem (Finset.mem_toList.mpr hadj) ih

omit [Fintype V] in
/-- A nodup chain through the neighbor relation, disjoint from `vis`,
yields a `DfsWitness` from `vis` to the last element. -/
private theorem chain_to_DfsWitness (neighbors : V → Finset V) :
    ∀ (chain : List V) (vis : Finset V)
      (_ : List.IsChain (neighborRel neighbors) chain)
      (_ : chain.Nodup) (_ : ∀ x ∈ chain, x ∉ vis)
      {s t : V} (_ : chain.head? = some s) (_ : chain.getLast? = some t),
      DfsWitness neighbors vis s t := by
  intro chain
  induction chain with
  | nil => intro _ _ _ _ _ _ ht; simp at ht
  | cons a tail ih =>
    intro vis hchain hnodup hdisj s t hs ht
    simp only [List.head?_cons, Option.some.injEq] at hs; subst hs
    have ha_not_vis : a ∉ vis := hdisj a (by simp)
    cases tail with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at ht; subst ht
      exact DfsWitness.here ha_not_vis
    | cons b rest =>
      have hchain' : List.IsChain (neighborRel neighbors) (a :: b :: rest) := hchain
      have hchain_tail : List.IsChain (neighborRel neighbors) (b :: rest) :=
        List.IsChain.tail hchain'
      have hnodup_tail : (b :: rest).Nodup :=
        (List.nodup_cons.mp hnodup).2
      have hab : neighborRel neighbors a b :=
        List.IsChain.rel_head hchain'
      have hdisj_tail : ∀ x ∈ b :: rest, x ∉ vis ∪ {a} := by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_singleton]
        push_neg
        exact ⟨hdisj x (List.mem_cons_of_mem a hx), fun heq => by
          subst heq; exact (List.nodup_cons.mp hnodup).1 hx⟩
      have ht' : (b :: rest).getLast? = some t := by
        simp only [List.getLast?_cons_cons] at ht; exact ht
      exact DfsWitness.step ha_not_vis hab
        (ih (vis ∪ {a}) hchain_tail hnodup_tail hdisj_tail rfl ht')

/-- Completeness: every reachable vertex is in the DFS result from `∅`. -/
theorem dfsReach_complete (neighbors : V → Finset V) (s : V) :
    ∀ v, Relation.ReflTransGen (neighborRel neighbors) s v →
      v ∈ dfsReach neighbors s ∅ := by
  intro v hreach
  obtain ⟨chain, hhead, hlast, hnodup, hchain⟩ := reflTransGen_nodup_chain hreach
  have hdisj : ∀ x ∈ chain, x ∉ (∅ : Finset V) := by simp
  have hw := chain_to_DfsWitness neighbors chain ∅ hchain hnodup hdisj hhead hlast
  exact dfsReach_complete_from_witness neighbors hw

-- ============================================================================
-- Main correctness theorem
-- ============================================================================

/-- The DFS correctly computes `ReflTransGen`-reachability. -/
theorem dfsReach_correct (neighbors : V → Finset V) (s : V) :
    ∀ v, v ∈ dfsReach neighbors s ∅ ↔
      Relation.ReflTransGen (neighborRel neighbors) s v := by
  intro v
  constructor
  · intro h
    have := dfsReach_sound neighbors s ∅ v h
    simp_all
  · exact dfsReach_complete neighbors s v

-- ============================================================================
-- Decidability instances
-- ============================================================================

/-- `ReflTransGen` of a neighbor relation is decidable on finite types. -/
noncomputable instance instDecidableReflTransGenNeighborRel (neighbors : V → Finset V) :
    DecidableRel (Relation.ReflTransGen (neighborRel neighbors)) :=
  fun u v =>
    if h : v ∈ dfsReach neighbors u ∅
    then isTrue ((dfsReach_correct neighbors u v).mp h)
    else isFalse (fun hr => h ((dfsReach_correct neighbors u v).mpr hr))

end DFS
