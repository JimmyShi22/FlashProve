-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/WalkTable.lean: the walk of a forest says yes if its checks are read off one
consistent table of tree vertices.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

The joint walk of the opened leaves of a tree (Hash/Octopus.lean: `octC`) hashes two neighbours
that are siblings together, and a node without its sibling with a digest read off the paths. The
library shows that honest trees pass (Hash/OctopusFacts.lean: `Octopus.complete`): there every
level is computed from all leaves. A verifier of a file does not hold all leaves. It holds a record
of the vertices that it has met: some computed, some given. This file shows the same for such a
record: a table V from (level, number) to digests.

Main names:
  `Meets hN V k js`: at the nodes js of level k the table is consistent: the parent's entry is the
    hash of its two children's entries.
  `tpath V d k i`: the d siblings on the way up from node i of level k, read off the table;
    `tpath_eq`: at step m the entry of level k + m at the sibling of i / 2^m; `sibOf_eq_xor`: the
    sibling's number is the number with its lowest bit turned.
  `lone_table`, `stepF_table`, `upP_table`, `octF_table`: the walk from the table's entries at js,
    with the pruned form of these paths, ends in the table's entries d levels higher.
  `FromTable g V T`: the checks of the forest T are read off the table V: the leaves' digests under
    g, the paths, the roots; and V is consistent under g's node hash at the nodes that the walk
    meets.
  `walk_of_table`: then `walkP g T T.reads = true` (OnBytes/TypedOracleCompiler/Joined/WalkAt.lean).

Limits: one direction. Nothing on soundness. The table is a letter: that a reader's record of
vertices is such a table is not shown here. Each leaf's own climb to the root is not enough for
`FromTable`: where two siblings are both opened, the walk hashes the computed digests, so the paths'
entries must be the table's.

Terms: lean/GLOSSARY.md.

-/
import Mathlib.Data.Nat.Bitwise
import Hash.OctopusFacts
import OnBytes.TypedOracleCompiler.Joined.WalkAt

noncomputable section

namespace TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Octopus
open _root_.Iop (Dig)

/-! ## The walk from a table -/

section Table
variable {D : Type} [Inhabited D] (hN : D → D → D) (V : ℕ → ℕ → D)

/-- At the nodes js of level k the table is consistent: the entry of a node's parent is the hash of
the entries of the parent's two children. -/
def Meets (k : ℕ) (js : List ℕ) : Prop :=
  ∀ i ∈ js, V (k + 1) (i / 2) = hN (V k (2 * (i / 2))) (V k (2 * (i / 2) + 1))

/-- the d siblings on the way up from node i of level k, read off the table -/
def tpath : ℕ → ℕ → ℕ → List D
  | 0, _, _ => []
  | d + 1, k, i => V k (sibOf i) :: tpath d (k + 1) (i / 2)

omit [Inhabited D] in
/-- the path in closed form: at step m the table's entry of level k + m at the sibling of i / 2^m -/
theorem tpath_eq : ∀ (d k i : ℕ),
    tpath V d k i = (List.range d).map fun m => V (k + m) (sibOf (i / 2 ^ m))
  | 0, _, _ => rfl
  | d + 1, k, i => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    show V k (sibOf i) :: tpath V d (k + 1) (i / 2) = _
    rw [tpath_eq d (k + 1) (i / 2)]
    congr 1
    · simp
    · refine List.map_congr_left fun m _ => ?_
      show V (k + 1 + m) (sibOf (i / 2 / 2 ^ m)) = V (k + (m + 1)) (sibOf (i / 2 ^ (m + 1)))
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ', show k + 1 + m = k + (m + 1) by omega]

/-- the sibling's number is the number with its lowest bit turned -/
theorem sibOf_eq_xor (i : ℕ) : sibOf i = i ^^^ 1 := by
  unfold sibOf
  split
  · rename_i h
    exact (Nat.xor_one_of_even (Nat.even_iff.2 h)).symm
  · rename_i h
    exact (Nat.xor_one_of_odd (Nat.odd_iff.2 (by omega))).symm

variable {hN V}

omit [Inhabited D] in
theorem lone_table {k i : ℕ}
    (h : V (k + 1) (i / 2) = hN (V k (2 * (i / 2))) (V k (2 * (i / 2) + 1))) :
    loneF hN i (V k i) (V k (sibOf i)) = V (k + 1) (i / 2) := by
  rw [h]
  unfold loneF sibOf
  by_cases h0 : i % 2 = 0
  · have e : 2 * (i / 2) = i := by omega
    rw [if_pos h0, if_pos h0, e]
  · have e : 2 * (i / 2) + 1 = i := by omega
    have e' : 2 * (i / 2) = i - 1 := by omega
    rw [if_neg h0, if_neg h0, e, e']

theorem stepF_table (d k : ℕ) :
    ∀ (js : List ℕ) (e : List D), Meets hN V k js →
      stepF hN js (js.map (V k)) (reads1 (js.map fun j => (j, tpath V (d + 1) k j)) ++ e) =
        (up js).map (V (k + 1))
  | [], _, _ => rfl
  | [i], e, h => by
      show [loneF hN i (V k i) (V k (sibOf i))] = _
      rw [lone_table (h i List.mem_cons_self)]; rfl
  | i :: j :: l, e, h => by
      by_cases hs : sib i j
      · have ih := stepF_table d k l e fun x hx =>
          h x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
        have e1 : stepF hN (i :: j :: l) ((i :: j :: l).map (V k))
              (reads1 ((i :: j :: l).map fun j => (j, tpath V (d + 1) k j)) ++ e) =
            hN (V k i) (V k j) ::
              stepF hN l (l.map (V k)) (reads1 (l.map fun j => (j, tpath V (d + 1) k j)) ++ e) := by
          simp only [stepF, stepC, List.map_cons, reads1, if_pos hs]
          rfl
        rw [e1, ih]
        simp only [up, if_pos hs, List.map_cons]
        congr 1
        have hi := h i List.mem_cons_self
        obtain ⟨h1, rfl⟩ := hs
        have e2 : 2 * (i / 2) = i := by omega
        rw [hi, e2]
      · have ih := stepF_table d k (j :: l) e fun x hx => h x (List.mem_cons_of_mem _ hx)
        have e1 : stepF hN (i :: j :: l) ((i :: j :: l).map (V k))
              (reads1 ((i :: j :: l).map fun j => (j, tpath V (d + 1) k j)) ++ e) =
            loneF hN i (V k i) (V k (sibOf i)) ::
              stepF hN (j :: l) ((j :: l).map (V k))
                (reads1 ((j :: l).map fun j => (j, tpath V (d + 1) k j)) ++ e) := by
          simp only [stepF, stepC, List.map_cons, reads1, if_neg hs]
          rfl
        rw [e1, ih, lone_table (h i List.mem_cons_self)]
        simp only [up, if_neg hs, List.map_cons]

omit [Inhabited D] in
theorem upP_table (d k : ℕ) :
    ∀ js : List ℕ, upP (js.map fun j => (j, tpath V (d + 1) k j)) =
      (up js).map fun j => (j, tpath V d (k + 1) j)
  | [] => rfl
  | [_] => rfl
  | i :: j :: l => by
      by_cases hs : sib i j
      · simp only [List.map_cons, upP, up, if_pos hs, upP_table d k l]
        rfl
      · have ih := upP_table d k (j :: l)
        simp only [List.map_cons] at ih
        simp only [List.map_cons, upP, up, if_neg hs, ih]
        rfl

/-- **The walk from a consistent table.** From the table's entries at the nodes js of level k, with
the pruned form of the paths read off the table, the walk ends d levels higher in the table's
entries, if the table is consistent at the nodes that the walk meets on its way. -/
theorem octF_table : ∀ (d k : ℕ) (js : List ℕ), (∀ m < d, Meets hN V (k + m) (upN m js)) →
    octF hN d js (js.map (V k)) (reads d (js.map fun j => (j, tpath V d k j))) =
      (upN d js).map (V (k + d))
  | 0, _, _, _ => rfl
  | d + 1, k, js, h => by
    have e : octF hN (d + 1) js (js.map (V k))
          (reads (d + 1) (js.map fun j => (j, tpath V (d + 1) k j))) =
        octF hN d (up js)
          (stepF hN js (js.map (V k)) (reads (d + 1) (js.map fun j => (j, tpath V (d + 1) k j))))
          ((reads (d + 1) (js.map fun j => (j, tpath V (d + 1) k j))).drop (need1 js)) := rfl
    have hl : (reads1 (js.map fun j => (j, tpath V (d + 1) k j))).length = need1 js := by
      rw [length_reads1, List.map_map]
      congr 1
      exact List.map_id' js
    have h0 : Meets hN V k js := h 0 (Nat.succ_pos d)
    rw [e, reads, stepF_table d k js _ h0, ← hl, List.drop_left, upP_table,
      octF_table d (k + 1) (up js) fun m hm => by
        have := h (m + 1) (Nat.succ_lt_succ hm)
        rwa [show k + (m + 1) = k + 1 + m by omega] at this]
    show (upN d (up js)).map (V (k + 1 + d)) = (upN d (up js)).map (V (k + (d + 1)))
    rw [show k + 1 + d = k + (d + 1) by omega]

end Table

/-! ## The walk of a forest -/

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The checks of the forest T are read off the table V, under the oracle functions g. -/
structure FromTable (g : Fam (typedOracleFamily lam K L)) (V : ℕ → ℕ → Dig lam) (T : Forest lam L) : Prop where
  /-- The digest of each opened leaf under g is the table's entry at level 0. A typed query to the
  leaf oracle holds a body and a salt and nothing else. So for a g that is made from a hash on
  strings, all that the hash of a leaf takes beside the column (a label, the tree's number, the
  position, a starting value) must be read back from the typed body and salt. -/
  leaf : ∀ e ∈ T.cs, g OracleName.leaf e.2.inp = V 0 (e.1 * 2 ^ T.depth + e.2.j)
  /-- the path of each check is the siblings on the way up, read off the table -/
  path : ∀ e ∈ T.cs, e.2.path = tpath V T.depth 0 (e.1 * 2 ^ T.depth + e.2.j)
  /-- the table is consistent under g's node hash at the nodes that the walk meets -/
  meets : ∀ m < T.depth, Meets (nodeAt g) V m (upN m T.idx)
  /-- at the top the table holds the roots -/
  root : ∀ m ∈ upN T.depth T.idx, V T.depth m = T.treeRoot m

/-- **The walk of a forest whose checks are read off a consistent table says yes under g.** -/
theorem walk_of_table {g : Fam (typedOracleFamily lam K L)} {V : ℕ → ℕ → Dig lam} {T : Forest lam L}
    (h : FromTable g V T) : walkP g T T.reads = true := by
  have e1 : leavesP g T.cs = T.idx.map (V 0) := by
    unfold leavesP Forest.idx
    rw [List.map_map]
    exact List.map_congr_left fun e he => h.leaf e he
  have e2 : T.reads = reads T.depth (T.idx.map fun j => (j, tpath V T.depth 0 j)) := by
    unfold Forest.reads Forest.idx
    rw [List.map_map]
    congr 1
    exact List.map_congr_left fun e he => by rw [h.path e he]; rfl
  unfold walkP
  rw [e1, e2, octF_table T.depth 0 T.idx fun m hm => by
    rw [Nat.zero_add]; exact h.meets m hm]
  rw [Nat.zero_add, List.all_eq_true]
  intro m hm
  obtain ⟨hm1, hm2⟩ : m.1 ∈ upN T.depth T.idx ∧ m.2 = V T.depth m.1 := by
    have := List.of_mem_zip hm
    rw [List.zip_map_right] at hm
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hm
    have hx' : x.1 = x.2 := by
      clear hm this
      revert hx
      generalize upN T.depth T.idx = l
      induction l with
      | nil => intro hx; cases hx
      | cons a l ih =>
        intro hx
        rcases List.mem_cons.1 hx with rfl | hx
        · rfl
        · exact ih hx
    exact ⟨this.1, by show V T.depth x.2 = V T.depth x.1; rw [hx']⟩
  exact decide_eq_true (hm2.trans (h.root m.1 hm1))

end TypedOracleCompiler.Joined
