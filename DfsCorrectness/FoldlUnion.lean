import Mathlib.Data.Finset.Basic

/-!
# Membership lemmas for `List.foldl` over `Finset` unions

Generic combinators for reasoning about `L.foldl (fun acc x => acc ∪ f x) init`.
Used by `dfsReach` proofs but independent of DFS.
-/

/-- The initial set is always a subset of a left fold of unions. -/
lemma foldl_union_subset_init {α β : Type*} [DecidableEq α]
    (f : β → Finset α) (l : List β) (init : Finset α) :
    init ⊆ l.foldl (fun acc next => acc ∪ f next) init := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact Finset.subset_union_left.trans (ih _)

/-- Characterize membership in a left fold of unions. -/
lemma mem_foldl_union {α β : Type*} [DecidableEq α]
    (f : β → Finset α) (init : Finset α) (L : List β) (v : α) :
    v ∈ L.foldl (fun acc x => acc ∪ f x) init ↔
      v ∈ init ∨ ∃ x ∈ L, v ∈ f x := by
  induction L generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [Finset.mem_union, List.mem_cons]
    constructor
    · rintro (h | ⟨x, hx, hv⟩)
      · rcases h with h | h
        · left; exact h
        · right; exact ⟨hd, Or.inl rfl, h⟩
      · right; exact ⟨x, Or.inr hx, hv⟩
    · rintro (h | ⟨x, hx, hv⟩)
      · left; left; exact h
      · rcases hx with rfl | hx
        · left; right; exact hv
        · right; exact ⟨x, hx, hv⟩

/-- Shortcut: if `v ∈ f x` for some `x ∈ L`, then `v` is in the fold result. -/
lemma mem_foldl_union_of_mem {α β : Type*} [DecidableEq α]
    {L : List β} {x : β} {v : α}
    {f : β → Finset α} {init : Finset α}
    (hx : x ∈ L) (hv : v ∈ f x) :
    v ∈ L.foldl (fun acc next => acc ∪ f next) init := by
  rw [mem_foldl_union]
  right
  exact ⟨x, hx, hv⟩
