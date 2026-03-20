# DFS Correctness for Finite Types

A Lean 4 formalization proving that depth-first search correctly computes reachability in finite directed graphs. Built on Mathlib.

## What we prove

Given any finite type `V` and a neighbor function `neighbors : V → Finset V`, we define a DFS algorithm `dfsReach` and prove:

```
theorem dfsReach_correct (neighbors : V → Finset V) (s : V) :
    ∀ v, v ∈ dfsReach neighbors s ∅ ↔
      Relation.ReflTransGen (neighborRel neighbors) s v
```

That is, the set computed by DFS starting from `s` is exactly the set of vertices reachable from `s` via the reflexive-transitive closure of the neighbor relation.

As a corollary, we derive a `DecidableRel` instance for `ReflTransGen (neighborRel neighbors)` on any `Fintype`.

## How the proof works

### The algorithm

`dfsReach neighbors curr vis` maintains a visited set `vis`. If `curr ∈ vis`, it returns `vis` unchanged. Otherwise it marks `curr` as visited and folds over `(neighbors curr).toList`, recursively calling DFS on each neighbor and unioning the results.

Termination is by `(visᶜ).card` — the number of unvisited vertices, which strictly decreases with each fresh visit (`compl_card_lt_of_insert`).

### Soundness

`dfsReach_sound` shows every vertex in the output is either already in `vis` or `ReflTransGen`-reachable from `curr`. The proof is by strong induction on `(visᶜ).card`, case-splitting on whether `curr` was already visited. The key combinator is `mem_foldl_union`, which characterizes membership in a left fold of unions.

### Completeness

Completeness is the harder direction and proceeds in three steps:

1. **Cycle removal** (`reflTransGen_nodup_chain`): Any `ReflTransGen` path has a duplicate-free representative. Proved by taking a shortest chain (via `Nat.find`) and showing any duplicate would yield a strictly shorter one, contradicting minimality.

2. **Chain to witness** (`chain_to_DfsWitness`): A nodup chain disjoint from the visited set converts into a `DfsWitness` — an inductive type that mirrors the recursive structure of DFS, tracking that each intermediate vertex is fresh when visited.

3. **Witness to membership** (`dfsReach_complete_from_witness`): A `DfsWitness` directly implies membership in the DFS result, by induction on the witness.

### Proof architecture

```
ReflTransGen R s v
        │
        ▼
reflTransGen_nodup_chain ──► nodup chain from s to v
        │
        ▼
chain_to_DfsWitness ────────► DfsWitness neighbors ∅ s v
        │
        ▼
dfsReach_complete_from_witness ► v ∈ dfsReach neighbors s ∅
```

The `DfsWitness` inductive type is the central proof device. It bridges the relational world (`ReflTransGen`) and the algorithmic world (`dfsReach`) by encoding reachability in a form that respects the visited-set protocol of DFS.

## Building

Requires Lean 4 (v4.29.0-rc6) and Mathlib. To build:

```
lake build
```
