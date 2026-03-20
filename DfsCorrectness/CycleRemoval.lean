import Mathlib.Logic.Relation
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-!
# Cycle removal in chains

Lemmas for removing duplicate occurrences from chains, culminating in
`reflTransGen_nodup_chain`: any `ReflTransGen` path in a finite type has a
duplicate-free chain representative.

These are pure list/relation lemmas with no DFS dependency.
-/

universe u

variable {V : Type u}

/-- Removing a repeated element from the middle of a list preserves `head?`. -/
private lemma head?_remove_cycle'
    {pre mid post : List V} {x : V} :
    (pre ++ x :: mid ++ x :: post).head? = (pre ++ x :: post).head? := by
  cases pre <;> simp [List.append_assoc]

/-- Removing a repeated element from the middle of a list preserves `getLast?`. -/
private lemma getLast?_remove_cycle'
    {pre mid post : List V} {x : V} :
    (pre ++ x :: mid ++ x :: post).getLast? = (pre ++ x :: post).getLast? := by
  cases post with
  | nil =>
      calc
        (pre ++ x :: mid ++ [x]).getLast?
            = (x :: mid ++ [x]).getLast? := by
                simpa [List.append_assoc] using List.getLast?_append_cons pre x (mid ++ [x])
        _ = [x].getLast? := by
              simpa [List.append_assoc] using
                (List.getLast?_append_of_ne_nil (x :: mid) (by simp : [x] ≠ []))
        _ = (pre ++ [x]).getLast? := by
              exact (List.getLast?_append_cons pre x []).symm
  | cons y ys =>
      have h1 :
          (pre ++ x :: mid ++ x :: y :: ys).getLast? = (y :: ys).getLast? := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (pre ++ x :: mid ++ [x]) (by simp : y :: ys ≠ []))
      have h2 :
          (pre ++ x :: y :: ys).getLast? = (y :: ys).getLast? := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (pre ++ [x]) (by simp : y :: ys ≠ []))
      exact h1.trans h2.symm

/-- Removing a repeated element from the middle of a chain preserves the chain
property. -/
private lemma isChain_remove_cycle {R : V → V → Prop}
    {pre mid post : List V} {x : V}
    (hchain : List.IsChain R (pre ++ x :: mid ++ x :: post)) :
    List.IsChain R (pre ++ x :: post) := by
  have hleft : List.IsChain R (pre ++ [x]) := by
    have : List.IsChain R ((pre ++ [x]) ++ (mid ++ x :: post)) := by
      simpa [List.singleton_append, List.append_assoc] using hchain
    exact this.left_of_append
  have hright : List.IsChain R ([x] ++ post) := by
    have : List.IsChain R ((pre ++ x :: mid) ++ (x :: post)) := by
      simpa [List.append_assoc] using hchain
    exact this.right_of_append
  have : List.IsChain R (pre ++ [x] ++ post) :=
    hleft.append_overlap hright (by simp)
  simpa [List.singleton_append, List.append_assoc] using this

/-- Decompose a duplicate occurrence into prefix, middle, and suffix. -/
private lemma duplicate_decompose'
    {x : V} {l : List V}
    (h : List.Duplicate x l) :
    ∃ pre mid post, l = pre ++ x :: mid ++ x :: post := by
  induction h with
  | cons_mem hmem =>
      have ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp hmem
      exact ⟨[], pre, post, by simp [hsplit]⟩
  | @cons_duplicate y l _ ih =>
      rcases ih with ⟨pre, mid, post, hsplit⟩
      exact ⟨y :: pre, mid, post, by simp [hsplit]⟩

/-- Any `ReflTransGen` path has a cycle-free chain representative. -/
theorem reflTransGen_nodup_chain
    {R : V → V → Prop}
    {s t : V} (h : Relation.ReflTransGen R s t) :
    ∃ chain : List V,
      chain.head? = some s ∧
      chain.getLast? = some t ∧
      chain.Nodup ∧
      List.IsChain R chain := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ m : List V,
      m.head? = some s ∧
      List.IsChain R m ∧
      m.getLast? = some t ∧
      m.length = n
  have hex : ∃ n, P n := by
    rcases List.exists_isChain_cons_of_relationReflTransGen h with ⟨l, hchain, hlast⟩
    refine ⟨(s :: l).length, s :: l, by simp, hchain, ?_, rfl⟩
    simpa [List.getLast?_eq_getLast_of_ne_nil] using congrArg some hlast
  let n := Nat.find hex
  have hn : P n := Nat.find_spec hex
  rcases hn with ⟨m, hhead, hchain, hlast, hlen⟩
  have hmin :
      ∀ {m' : List V},
        m'.head? = some s →
        List.IsChain R m' →
        m'.getLast? = some t →
        n ≤ m'.length := by
    intro m' hhead' hchain' hlast'
    exact Nat.find_min' hex ⟨m', hhead', hchain', hlast', rfl⟩
  have hnodup : List.Nodup m := by
    by_contra hno
    obtain ⟨x, hdup⟩ := (List.exists_duplicate_iff_not_nodup).2 hno
    rcases duplicate_decompose' hdup with ⟨pre, mid, post, hsplit⟩
    let short : List V := pre ++ x :: post
    have hchain_short : List.IsChain R short := by
      dsimp [short]
      apply isChain_remove_cycle
      simpa [hsplit] using hchain
    have hhead_short : short.head? = some s := by
      dsimp [short]
      have : (pre ++ x :: mid ++ x :: post).head? = some s := by
        simpa [hsplit] using hhead
      simpa [head?_remove_cycle'] using this
    have hlast_short : short.getLast? = some t := by
      dsimp [short]
      have : (pre ++ x :: mid ++ x :: post).getLast? = some t := by
        simpa [hsplit] using hlast
      rw [getLast?_remove_cycle'] at this
      exact this
    have hlen_split : m.length = short.length + (mid.length + 1) := by
      dsimp [short]
      rw [hsplit]
      simp [List.length_append, Nat.add_left_comm, Nat.add_comm]
    have hlt : short.length < m.length := by
      have : short.length < short.length + (mid.length + 1) :=
        Nat.lt_add_of_pos_right (Nat.succ_pos _)
      rw [hlen_split]; exact this
    have hn_eq : n = m.length := by simpa using hlen.symm
    have hlt' : short.length < n := by simpa [hn_eq] using hlt
    exact (not_lt_of_ge (hmin hhead_short hchain_short hlast_short)) hlt'
  exact ⟨m, hhead, hlast, hnodup, hchain⟩
