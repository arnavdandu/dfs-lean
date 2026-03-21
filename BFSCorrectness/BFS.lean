import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation
import Mathlib.Tactic
import DfsCorrectness.FoldlUnion
import DfsCorrectness.CycleRemoval
import DfsCorrectness.DFS

/-!
# BFS correctness

This file defines a layer-based Breadth-First Search (BFS) algorithm and proves its correctness
against `Relation.ReflTransGen`.

## Main definitions

* `bfsReach` — BFS from a frontier of vertices with a visited set.

## Main theorems

* `bfsReach_correct` — `v ∈ bfsReach neighbors {s} ∅ ↔ ReflTransGen (neighborRel neighbors) s v`
-/

universe u

open Finset

namespace BFSCorrectness

section BFS

variable {V : Type u} [Fintype V] [DecidableEq V]

-- neighborRel is already imported from DfsCorrectness.DFS

-- ============================================================================
-- Termination and cardinality lemmas
-- ============================================================================

/-- Adding nodes from the frontier that aren't in vis, unvisited count strictly decreases. -/
lemma compl_card_lt_of_frontier {V : Type u} [Fintype V] [DecidableEq V]
    (vis frontier : Finset V) (h : ¬(frontier ⊆ vis)) :
    ((vis ∪ frontier)ᶜ).card < (visᶜ).card := by
  apply Finset.card_lt_card
  apply Finset.compl_ssubset_compl.mpr
  apply Finset.ssubset_iff.mpr
  obtain ⟨x, hxf, hxv⟩ := not_subset.mp h
  use x, hxv
  rw [Finset.insert_subset_iff]
  exact ⟨Finset.mem_union_right _ hxf, Finset.subset_union_left⟩

-- ============================================================================
-- BFS algorithm
-- ============================================================================

/-- Breadth-first search computing the set of reachable vertices. -/
noncomputable def bfsReach {V : Type u} [Fintype V] [DecidableEq V]
    (neighbors : V → Finset V) (frontier : Finset V) (vis : Finset V) : Finset V :=
  if _h : frontier ⊆ vis then vis
  else
    bfsReach neighbors (frontier.biUnion neighbors) (vis ∪ frontier)
termination_by (visᶜ).card
decreasing_by
  exact compl_card_lt_of_frontier vis frontier _h
  
-- ============================================================================
-- Properties
-- ============================================================================

/-- One-step unfolding of the `bfsReach` definition. -/
theorem bfsReach_unfold {V : Type u} [Fintype V] [DecidableEq V]
    (neighbors : V → Finset V) (frontier : Finset V) (vis : Finset V) :
    bfsReach neighbors frontier vis =
      if _h : frontier ⊆ vis then vis
      else bfsReach neighbors (frontier.biUnion neighbors) (vis ∪ frontier) := by
  exact bfsReach.eq_def neighbors frontier vis

/-- The initial visited set is always a subset of the BFS result. -/
theorem vis_subset_bfsReach (neighbors : V → Finset V) (frontier : Finset V) (vis : Finset V) :
    vis ⊆ bfsReach neighbors frontier vis := by
  induction n_m : (visᶜ).card using Nat.strongRecOn generalizing frontier vis with
  | _ n ih =>
    rw [bfsReach_unfold]
    split_ifs with h
    · exact subset_refl _
    · have h_card_val : ((vis ∪ frontier)ᶜ).card < (visᶜ).card := compl_card_lt_of_frontier _ _ h
      have h_card : ((vis ∪ frontier)ᶜ).card < n := n_m ▸ h_card_val
      have ih' := ih ((vis ∪ frontier)ᶜ).card h_card
        (frontier.biUnion neighbors) (vis ∪ frontier) rfl
      exact subset_trans (subset_union_left) ih'

/-- Soundness: every vertex in the result is reachable from the frontier or initial vis. -/
theorem bfsReach_sound (neighbors : V → Finset V) (frontier vis : Finset V) :
    ∀ v ∈ bfsReach neighbors frontier vis,
      v ∈ vis ∨ ∃ s ∈ frontier,
        Relation.ReflTransGen (DfsCorrectness.neighborRel neighbors) s v := by
  induction n_m : (visᶜ).card using Nat.strongRecOn generalizing frontier vis with
  | _ n ih =>
    rw [bfsReach_unfold]
    split_ifs with h
    · intro v hv; left; exact hv
    · intro v hv
      have h_card_val : ((vis ∪ frontier)ᶜ).card < (visᶜ).card := compl_card_lt_of_frontier _ _ h
      have h_card : ((vis ∪ frontier)ᶜ).card < n := n_m ▸ h_card_val
      have ih' := ih ((vis ∪ frontier)ᶜ).card h_card
        (frontier.biUnion neighbors) (vis ∪ frontier) rfl
      rcases ih' v hv with h_vis_union | ⟨s', hs', hreach⟩
      · rw [Finset.mem_union] at h_vis_union
        rcases h_vis_union with hv_vis | hv_frontier
        · left; exact hv_vis
        · right; use v
      · right
        rw [Finset.mem_biUnion] at hs'
        rcases hs' with ⟨s, hs, hs'⟩
        use s, hs
        apply Relation.ReflTransGen.head hs' hreach

omit [Fintype V] in
lemma bfsReach_fixed_point
    (neighbors : V → Finset V) (frontier vis : Finset V) (h : frontier ⊆ vis)
    (h_inv : ∀ x ∈ vis, neighbors x ⊆ vis ∪ frontier) :
    ∀ x, ∀ s ∈ vis, Relation.ReflTransGen (DfsCorrectness.neighborRel neighbors) s x → x ∈ vis := by
  intro x s hs hreach
  induction hreach with
  | refl => exact hs
  | tail _ hnext ih =>
    have h_neighbors := h_inv _ ih
    rw [union_eq_left.mpr h] at h_neighbors
    exact h_neighbors hnext

/-- Every reachable vertex is eventually found by BFS. -/
theorem bfsReach_complete_aux (neighbors : V → Finset V) (frontier vis : Finset V) (v : V) :
    (∀ x ∈ vis, neighbors x ⊆ vis ∪ frontier) →
    (v ∈ vis ∨ ∃ s ∈ frontier, Relation.ReflTransGen (DfsCorrectness.neighborRel neighbors) s v) →
    v ∈ bfsReach neighbors frontier vis := by
  induction n_m : (visᶜ).card using Nat.strongRecOn generalizing frontier vis with
  | _ n ih =>
    rw [bfsReach_unfold]
    split_ifs with h
    · intro h_inv h_v
      rcases h_v with hv_vis | ⟨s, hs, hreach⟩
      · exact hv_vis
      · exact bfsReach_fixed_point neighbors frontier vis h h_inv v s (h hs) hreach
    · intro h_inv h_v
      set vis' := vis ∪ frontier
      set frontier' := frontier.biUnion neighbors
      have h_card_val : (vis'ᶜ).card < (visᶜ).card := compl_card_lt_of_frontier _ _ h
      have h_card : (vis'ᶜ).card < n := n_m ▸ h_card_val
      apply ih (vis'ᶜ).card h_card frontier' vis' rfl
      · -- Invariant
        intro x hx
        rw [mem_union] at hx
        rcases hx with hx_vis | hx_frontier
        · have h_nb := h_inv x hx_vis
          exact subset_trans h_nb subset_union_left
        · exact subset_trans (subset_biUnion_of_mem neighbors hx_frontier) subset_union_right
      · -- Target
        rcases h_v with hv_vis | ⟨s, hs, hreach⟩
        · left; exact subset_union_left hv_vis
        · rcases hreach.cases_head with rfl | ⟨s', hss', hs'v⟩
          · left; exact mem_union_right _ hs
          · right; use s'
            constructor
            · rw [mem_biUnion]; use s, hs; exact hss'
            · exact hs'v

/-- Completeness: every reachable vertex is eventually found by BFS from `∅`. -/
theorem bfsReach_complete (neighbors : V → Finset V) (s : V) :
    ∀ v, Relation.ReflTransGen (DfsCorrectness.neighborRel neighbors) s v →
      v ∈ bfsReach neighbors {s} ∅ := by
  intro v hreach
  apply bfsReach_complete_aux neighbors {s} ∅ v
  · intro x hx;
    simp_all only [notMem_empty]
  · right; use s; simp only [mem_singleton, true_and]; exact hreach

-- ============================================================================
-- Main correctness theorem
-- ============================================================================

/-- The BFS correctly computes `ReflTransGen`-reachability. -/
theorem bfsReach_correct (neighbors : V → Finset V) (s : V) :
    ∀ v, v ∈ bfsReach neighbors {s} ∅ ↔
      Relation.ReflTransGen (DfsCorrectness.neighborRel neighbors) s v := by
  intro v
  constructor
  · intro h
    rcases bfsReach_sound neighbors {s} ∅ v h with h_vis | ⟨s', hs', hreach⟩
    · simp only [notMem_empty] at h_vis
    · simp only [mem_singleton] at hs'; subst hs'; exact hreach
  · exact bfsReach_complete neighbors s v

end BFS

end BFSCorrectness
