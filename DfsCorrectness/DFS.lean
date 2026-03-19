import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

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

theorem dfsReach_visited (neighbors : V → Finset V)
    {curr : V} {vis : Finset V} (h : curr ∈ vis) :
    dfsReach neighbors curr vis = vis := by
  unfold dfsReach; split <;> [rfl; contradiction]

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

private lemma foldl_union_subset_init {V : Type u} [DecidableEq V]
    (f : V → Finset V) (l : List V) (init : Finset V) :
    init ⊆ l.foldl (fun acc next => acc ∪ f next) init := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact Finset.subset_union_left.trans (ih _)

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
compatible with the DFS visited-set protocol. -/
inductive DfsWitness (neighbors : V → Finset V) :
    Finset V → V → V → Prop where
  | here {vis : Finset V} {q : V}
      (hq : q ∉ vis) :
      DfsWitness neighbors vis q q
  | step {vis : Finset V} {q next s : V}
      (hq : q ∉ vis)
      (hadj : next ∈ neighbors q)
      (hrest : DfsWitness neighbors (vis ∪ {q}) next s) :
      DfsWitness neighbors vis q s

-- ============================================================================
-- Helper: membership in foldl union
-- ============================================================================

/-- Characterize membership in a left fold of unions. -/
private lemma mem_foldl_union {α β : Type*} [DecidableEq α]
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
-- Chain and cycle machinery
-- ============================================================================

omit [Fintype V] [DecidableEq V] in
/-- Removing a repeated cycle from the middle of a list does not change its
head. -/
private lemma head?_remove_cycle'
    {pre mid post : List V} {x : V} :
    (pre ++ x :: mid ++ x :: post).head? = (pre ++ x :: post).head? := by
  cases pre <;> simp [List.append_assoc]

omit [Fintype V] [DecidableEq V] in
/-- Removing a repeated cycle from the middle of a list does not change its
last element. -/
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

omit [Fintype V] [DecidableEq V] in
/-- Removing a repeated state from the middle of a chain preserves the
chain property. -/
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

omit [Fintype V] [DecidableEq V] in
/-- Decompose a duplicate occurrence of `x` into two explicit copies. -/
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

omit [Fintype V] in
/-- Any `ReflTransGen` path in a finite type has a cycle-free chain. -/
theorem reflTransGen_nodup_chain {R : V → V → Prop}
    {s t : V} (h : Relation.ReflTransGen R s t) :
    ∃ chain : List V,
      chain.head? = some s ∧
      chain.getLast? = some t ∧
      chain.Nodup ∧
      List.IsChain R chain := by
  classical
  -- Pick the shortest chain from s to t. Any duplicate yields a strictly
  -- shorter chain (via cycle removal), contradicting minimality.
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

-- ============================================================================
-- Completeness
-- ============================================================================

omit [Fintype V] in
private theorem mem_foldl_union_of_mem {L : List V} {x v : V}
    {f : V → Finset V} {init : Finset V}
    (hx : x ∈ L) (hv : v ∈ f x) :
    v ∈ L.foldl (fun acc next => acc ∪ f next) init := by
  rw [mem_foldl_union]
  right
  exact ⟨x, hx, hv⟩

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
/-- A nodup chain `a :: rest` through the neighbor relation, disjoint from `vis`,
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
    simp at hs; subst hs
    have ha_not_vis : a ∉ vis := hdisj a (by simp)
    cases tail with
    | nil =>
      simp at ht; subst ht
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
    simp at this
    exact this
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
