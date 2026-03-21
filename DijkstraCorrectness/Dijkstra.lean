import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Data.Nat.Basic
import DfsCorrectness.DFS

universe u

open Finset

namespace DijkstraCorrectness

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A weighted graph is represented by a neighbor function and a weight function. -/
structure WeightedGraph (V : Type u) where
  neighbors : V → Finset V
  weight : V → V → ℕ

variable (G : WeightedGraph V)

/-- Infinity for distances. -/
abbrev dist_inf : WithTop ℕ := ⊤

/-- Dijkstra state: settled vertices and current distances. -/
structure DijkstraState (V : Type u) where
  settled : Finset V
  dists : V → WithTop ℕ

/-- Initial state for Dijkstra from a source vertex. -/
def initialState (s : V) : DijkstraState V :=
  { settled := ∅,
    dists := fun v => if v = s then 0 else dist_inf }

/-- Find the unsettled vertex with the minimum distance. -/
noncomputable def minUnsettled (state : DijkstraState V) : Option V :=
  match ((univ \ state.settled).filter (fun v => state.dists v ≠ dist_inf)).toList with
  | [] => none
  | (v :: vs) =>
    some (vs.foldl (fun acc x => if state.dists x < state.dists acc then x else acc) v)

/-- Update distances for neighbors of a settled vertex. -/
def updateDists (state : DijkstraState V) (u : V) : V → WithTop ℕ :=
  fun v =>
    if v ∈ G.neighbors u then
      min (state.dists v) (state.dists u + (G.weight u v : WithTop ℕ))
    else
      state.dists v

/-- One step of Dijkstra's algorithm. -/
noncomputable def dijkstraStep (state : DijkstraState V) (u : V) : DijkstraState V :=
  { settled := insert u state.settled,
    dists := updateDists G state u }

/-- Result of the foldl for minBy is in the list. -/
lemma mem_foldl_minBy {α β : Type*} [LinearOrder β] (f : α → β) (l : List α) (v : α) :
    l.foldl (fun acc x => if f x < f acc then x else acc) v ∈ v :: l := by
  induction l generalizing v with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    split_ifs with h_lt
    · have h := ih x
      simp only [List.mem_cons] at h ⊢
      rcases h with h_res | h_res
      · right; left; exact h_res
      · right; right; exact h_res
    · have h := ih v
      simp only [List.mem_cons] at h ⊢
      rcases h with h_res | h_res
      · left; exact h_res
      · right; right; exact h_res

/-- Termination lemma for dijkstra. -/
lemma minUnsettled_not_mem_settled {state : DijkstraState V} {u : V}
    (h : minUnsettled state = some u) : u ∉ state.settled := by
  unfold minUnsettled at h
  match h_list : ((univ \ state.settled).filter (fun v => state.dists v ≠ dist_inf)).toList with
  | [] =>
    rw [h_list] at h
    contradiction
  | v :: vs =>
    rw [h_list] at h
    simp only [Option.some.injEq] at h
    have h_mem : u ∈ v :: vs := by
      rw [← h]
      apply mem_foldl_minBy (fun x => state.dists x)
    have : u ∈ ((univ \ state.settled).filter (fun v => state.dists v ≠ dist_inf)) := by
      rw [← Finset.mem_toList, h_list]
      exact h_mem
    have : u ∈ univ \ state.settled := mem_of_mem_filter u this
    simp only [mem_sdiff, mem_univ, true_and] at this
    exact this

/-- The full Dijkstra's algorithm. -/
noncomputable def dijkstra (state : DijkstraState V) : DijkstraState V :=
  match _h : minUnsettled state with
  | none => state
  | some u =>
    dijkstra (dijkstraStep G state u)
termination_by ((univ : Finset V).card - state.settled.card)
decreasing_by
  simp only [dijkstraStep]
  have h_u := minUnsettled_not_mem_settled _h
  apply Nat.sub_lt_sub_left
  · apply Finset.card_lt_card
    rw [ssubset_univ_iff]
    intro h_eq
    exact h_u (h_eq.symm ▸ mem_univ u)
  · apply Finset.card_lt_card
    exact ssubset_insert h_u


end DijkstraCorrectness
