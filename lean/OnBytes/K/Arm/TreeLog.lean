-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/TreeLog.lean: a log of the queries made while a Merkle tree is built contains, for
every leaf index, the hash queries of all nodes on the path from that index to the root.
Purpose. `word_at_path` (OnBytes/K/Arm/TreeWord.lean) assumes that a query log contains these node
queries. This file proves it for every log of a run of the library's tree-building program
`levelsM` (Compile/MerkleM.lean), where each node is hashed by the one query `vertexQ cfg`.
States. `levels_log`: for each index j below 2 ^ d the path `pathOf lv j` has d entries, and the log
contains the node queries along it, from input value number j up to the root `rootOf lv`
(`ClimbsStr`). `pairUp_log`: one level over 2 n values yields n values, and the log contains each
pair's node query with the value above the pair as its answer. `runsIn_ownLog`: a program that draws
no random coins runs, in the log of its own queries under any oracle functions g, to its own result
under g. `noCoin_pairUp`, `noCoin_levelsM`: the tree-building program draws no random coins.
Under. Two premises in `levels_log`: the input list has exactly 2 ^ d values; and the program runs
to the result lv with every query and answer taken from the log. `pairUp_log` has the same two for
one level: the list has exactly 2 n values, and the level's run is taken from the log.
Does not show:
 1. anything about the leaves: the 2 ^ d input values are arbitrary;
 2. that `vertexQ cfg` is the query that the file format's own routine makes;
 3. that any committing program that is really run builds its tree in this way;
 4. anything about the event `EM`: that it does not occur remains an assumption of `word_at_path`;
 5. that the log contains nothing else;
 6. that the run or its result lv is unique: a log with two answers to one query may contain
    several runs, each with its own result;
 7. anything about opening-form binding, what a root fixes or whatever else names a committer;
 8. anything about a particular hash function;
 9. anything about soundness;
10. any code that runs: used in proofs only; the Lean verifier program does not import this file.
Notes in full, with every limit at length, are at the end of this file. They are the whole text.
Wherever this summary and the notes differ on a limit or a premise, the stronger limit holds, and
one that only one of the two names holds too; the notes hold for everything else.
Terms: lean/GLOSSARY.md.


-/
import OnBytes.K.Arm.TreeWord
import Compile.MerkleList

set_option autoImplicit false

namespace OnBytes.K.Arm
open Rom _root_.Compile _root_.Run
open _root_.Iop (Dig)

/-- The query at the format's string of the vertex over a and b. -/
def vertexQ (cfg : ByteArray) (a b : Dig 256) : OComp (rom 256) (Dig 256) :=
  OComp.ask () (bytesToBits (_root_.Fmt.oStr 0 166 0 0 cfg (digToBytes a ++ digToBytes b)))

/-- One level: where the pairing of 2 n values runs in a log, it yields n values, and the log holds,
for each pair, an entry at the format's string of the vertex over the pair, with the value above as
its answer. -/
theorem pairUp_log {σ : Trace (rom 256)} (cfg : ByteArray) :
    ∀ (n : ℕ) (l l' : List (Dig 256)), l.length = 2 * n →
      RunsIn σ (pairUp (vertexQ cfg) l) l' →
      l'.length = n ∧ ∀ i < n, (⟨(), bytesToBits (_root_.Fmt.oStr 0 166 0 0 cfg
        (digToBytes (l.getD (2 * i) default) ++ digToBytes (l.getD (2 * i + 1) default))),
        l'.getD i default⟩ : QA (rom 256)) ∈ σ
  | 0, [], l', _, h => by
      obtain rfl : [] = l' := runsIn_pure_iff.1 h
      exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | 0, _ :: _, _, hl, _ => by simp at hl
  | n + 1, [], _, hl, _ => by simp at hl
  | n + 1, [_], _, hl, _ => by
      simp only [List.length_singleton] at hl
      omega
  | n + 1, a :: b :: t, l', hl, h => by
      have h' : RunsIn σ ((vertexQ cfg a b).bind fun c =>
          (pairUp (vertexQ cfg) t).bind fun r => OComp.pure (c :: r)) l' := h
      obtain ⟨c, hc, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
      obtain ⟨r, hr, h3⟩ := (runsIn_bind_iff _ _ _).1 h2
      obtain rfl : c :: r = l' := runsIn_pure_iff.1 h3
      have ht : t.length = 2 * n := by
        simp only [List.length_cons] at hl
        omega
      obtain ⟨e1, e2⟩ := pairUp_log cfg n t r ht hr
      refine ⟨by rw [List.length_cons, e1], fun i hi => ?_⟩
      cases i with
      | zero => exact runsIn_ask_iff.1 hc
      | succ i =>
        have := e2 i (Nat.lt_of_succ_lt_succ hi)
        have x1 : 2 * (i + 1) = 2 * i + 1 + 1 := by omega
        rw [x1]
        simpa only [List.getD_cons_succ] using this

/-- The levels begin with the values that they are built over. -/
theorem levels_head {σ : Trace (rom 256)} (cfg : ByteArray) :
    ∀ (d : ℕ) (l : List (Dig 256)) (lv : List (List (Dig 256))),
      RunsIn σ (levelsM (vertexQ cfg) d l) lv → ∃ ls, lv = l :: ls
  | 0, l, lv, h => ⟨[], (runsIn_pure_iff.1 h).symm⟩
  | d + 1, l, lv, h => by
      have h' : RunsIn σ ((pairUp (vertexQ cfg) l).bind fun u =>
          (levelsM (vertexQ cfg) d u).bind fun r => OComp.pure (l :: r)) lv := h
      obtain ⟨u, -, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
      obtain ⟨r, -, h3⟩ := (runsIn_bind_iff _ _ _).1 h2
      exact ⟨r, (runsIn_pure_iff.1 h3).symm⟩

/-- **The induction on the depth.** Where the levels over 2 ^ d values run in a log, then for every
place j below 2 ^ d the path that is read off the levels has d entries, and the log holds the
format's strings of the vertices up that path, from the value at j to the root of the levels. -/
theorem levels_log {σ : Trace (rom 256)} (cfg : ByteArray) :
    ∀ (d : ℕ) (l : List (Dig 256)) (lv : List (List (Dig 256))), l.length = 2 ^ d →
      RunsIn σ (levelsM (vertexQ cfg) d l) lv → ∀ j < 2 ^ d,
      (pathOf lv j).length = d ∧
        ClimbsStr σ cfg (pathOf lv j) j (l.getD j default) (rootOf lv)
  | 0, l, lv, hl, h, j, hj => by
      obtain rfl : [l] = lv := runsIn_pure_iff.1 h
      obtain rfl : j = 0 := by simpa using hj
      refine ⟨rfl, ?_⟩
      match l, hl with
      | [c], _ => rfl
  | d + 1, l, lv, hl, h, j, hj => by
      have h' : RunsIn σ ((pairUp (vertexQ cfg) l).bind fun u =>
          (levelsM (vertexQ cfg) d u).bind fun r => OComp.pure (l :: r)) lv := h
      obtain ⟨u, hu, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
      obtain ⟨r, hr, h3⟩ := (runsIn_bind_iff _ _ _).1 h2
      obtain rfl : l :: r = lv := runsIn_pure_iff.1 h3
      obtain ⟨ls, rfl⟩ := levels_head cfg d u r hr
      obtain ⟨e1, e2⟩ := pairUp_log cfg (2 ^ d) l u (by rw [hl, pow_succ, Nat.mul_comm]) hu
      have hj2 : j / 2 < 2 ^ d := by
        rw [pow_succ] at hj
        omega
      obtain ⟨i1, i2⟩ := levels_log cfg d u (u :: ls) e1 hr (j / 2) hj2
      rw [pathOf_cons₂, rootOf_cons₂]
      refine ⟨by rw [List.length_cons, i1], u.getD (j / 2) default, ?_, i2⟩
      have hm := e2 (j / 2) hj2
      by_cases hb : j % 2 = 0
      · have y1 : 2 * (j / 2) = j := by omega
        rw [y1] at hm
        rw [if_pos hb, if_pos hb]
        exact hm
      · have y1 : 2 * (j / 2) = j - 1 := by omega
        have y2 : j - 1 + 1 = j := by omega
        rw [y1, y2] at hm
        rw [if_neg hb, if_neg hb]
        exact hm

/-- The pairing draws no coin. -/
theorem noCoin_pairUp (cfg : ByteArray) : ∀ l : List (Dig 256), (pairUp (vertexQ cfg) l).NoCoin
  | [] => trivial
  | [_] => trivial
  | a :: b :: t => by
      show ((vertexQ cfg a b).bind fun c =>
        (pairUp (vertexQ cfg) t).bind fun r => OComp.pure (c :: r)).NoCoin
      exact OComp.NoCoin.bind (fun _ => trivial) fun _ =>
        OComp.NoCoin.bind (noCoin_pairUp cfg t) fun _ => trivial

/-- Nor does the building of the levels. -/
theorem noCoin_levelsM (cfg : ByteArray) :
    ∀ (d : ℕ) (l : List (Dig 256)), (levelsM (vertexQ cfg) d l).NoCoin
  | 0, _ => trivial
  | d + 1, l => by
      show ((pairUp (vertexQ cfg) l).bind fun u =>
        (levelsM (vertexQ cfg) d u).bind fun r => OComp.pure (l :: r)).NoCoin
      exact OComp.NoCoin.bind (noCoin_pairUp cfg l) fun u =>
        OComp.NoCoin.bind (noCoin_levelsM cfg d u) fun _ => trivial

/-- **An algorithm without coins runs, in its own log under g, to its value under g.** -/
theorem runsIn_ownLog {S : OSpec} {α : Type} (g : Fam S) {c : OComp S α} (hc : c.NoCoin) :
    RunsIn (c.withTrace.det g).2 c (c.det g) := by
  induction c with
  | pure a => exact RunsIn.pure a
  | query o q k ih =>
    have e : ((OComp.query o q k).withTrace.det g).2 =
        ⟨o, q, g o q⟩ :: ((k (g o q)).withTrace.det g).2 := by
      show (((k (g o q)).withTrace.bind fun out =>
        OComp.pure (out.1, (⟨o, q, g o q⟩ : QA S) :: out.2)).det g).2 = _
      rw [OComp.det_bind]
      rfl
    rw [e]
    exact RunsIn.query o q k (g o q) _ List.mem_cons_self
      ((ih (g o q) (hc (g o q))).mono (List.subset_cons_self _ _))
  | sample n k _ => exact hc.elim

end OnBytes.K.Arm

#print axioms OnBytes.K.Arm.pairUp_log
#print axioms OnBytes.K.Arm.levels_head
#print axioms OnBytes.K.Arm.levels_log
#print axioms OnBytes.K.Arm.noCoin_pairUp
#print axioms OnBytes.K.Arm.noCoin_levelsM
#print axioms OnBytes.K.Arm.runsIn_ownLog

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/K/Arm/TreeLog.lean: where the levels of a hash tree over 2 ^ d values are built by queries
at the format's strings of vertices, every log in which that building runs holds, for every place,
the strings of the vertices up the place's path, from the value at the place to the root
(`ClimbsStr`, OnBytes/K/Arm/TreeWord.lean). Definitions, statements and proofs.

Why. `word_at_path` (TreeWord.lean) asks of a log of strings that it hold the vertices' strings up a
path. Here that premise is shown of a log in which the library's own program for the levels of a
tree (`levelsM`, Compile/MerkleM.lean) runs, with the query `vertexQ cfg` as its node function; the
path and the root are those that `pathOf` and `rootOf` read off the levels.

What it does not say. Anything of the leaves: the 2 ^ d values are a letter; that they are answers
to the format's strings of leaves is another file's matter. That `vertexQ cfg` is the format's own
routine at an asking hash. That any committer that runs builds its tree so. Anything of the event
`EM`, which stays a premise of `word_at_path`. That the log holds nothing else. The laws speak of
every log σ in which the program runs; `runsIn_ownLog` says that an algorithm without coins runs in
its own log under g, and the levels' program is one (`noCoin_levelsM`); a log with two answers to
one query may hold several runs, each with its own levels. Nothing on opening-form binding, no two
openings, correctness of extraction or whatever else names a committer or a prover. Nothing on any
one hash function. Nothing on soundness. For proofs only; the program does not import this file.
Main names.
 `vertexQ cfg a b`  one query, at the format's string of the vertex over a and b (number 166).
 `pairUp_log`      one level: where `pairUp (vertexQ cfg)` runs on 2 n values in σ it yields n
                   values, and σ holds for each pair an entry at the pair's vertex string with the
                   value above as its answer.
 `levels_head`     the levels begin with the values that they are built over.
 `levels_log`      the induction on the depth: from `l.length = 2 ^ d` and a run of
                   `levelsM (vertexQ cfg) d l` to lv in σ, for every j below 2 ^ d: `pathOf lv j`
                   has d entries, and
                   `ClimbsStr σ cfg (pathOf lv j) j (l.getD j default) (rootOf lv)`.
 `noCoin_pairUp`, `noCoin_levelsM`  these programs draw no coin: so `runsIn_ownLog` gives a log in
                   which they run.
 `runsIn_ownLog`   general in the oracles: an algorithm c without coins runs in
                   `(c.withTrace.det g).2`, its own log under g, to `c.det g`.

Terms: lean/GLOSSARY.md.
-/
