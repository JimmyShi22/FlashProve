-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Extraction.lean: for the honest committer of the compiled scheme the extracted index
is the committed one, except with probability 2 t² / 2^λ. theorem extractsHonestB.

The property is the optional requirement of ZKCP/Optional.lean (i* = i for the honest committer);
that file states it for the syntax of ZKCP/Defs.lean (`HasExtractionError`, one oracle, no batches);
the statement here, `Spec.extractsHonestB`, is the same inequality for the committer C of the
compiled scheme (Compile/Batch/Star.lean) over its typed oracles, and is not an instance of that
definition. Hypotheses: `L.Wired` (decoding an encoding gives the index back) and `W.OK` (a
well-formed wire record; in particular L.wordLength ≤ 2^depth).

The extractor, given the honest verification key and the committer's own trace, returns i, except
with probability 2 t² / 2^λ, where t = 2 · 2^depth bounds the number of queries for the one tree
under the root in the verification key. The rest of the committer's work does not enter: the
committer builds that tree first, and the extractor takes, for every digest, the first query of the
trace with that answer (`Merkle.OraclePair.preimage_mono`). The bound is loose by a constant: it
counts both hash events of `hashEvents` (Compile/Batch/Hash.lean) and uses one.

The calculus of runs within a trace (`OutsIn`, `TriI`) and the counting of queries (`SQ`) are those
of Compile/Extraction.lean, which are general. `OutsIn f tr c`: the values that the algorithm can
return under the oracle functions f on paths all of whose queries, with their answers, are entries
of the trace tr (how `Tri`, `TriI`, `SQ` read: Notation, below). Helper lemmas are in the namespace
`Compile.Batch.Extr`.

Notation: the hash events: `EM`, `EF` (Compile/Batch/Events.lean): the answer of a new Merkle query
occurs earlier in the trace; the chaining value of a new query collides with an earlier value (the
docstrings have the clauses); `Tri f c vs Q` (Compile/EraseKit.lean): under the oracle functions f,
whatever the coins, the erased program c, started with the store vs, returns a value a and a store
vs' with Q a vs'; `TriI f tr c vs Q` (Compile/Extraction.lean): the same postcondition for the runs
all of whose queries are entries of tr; `SQ c m P` (Compile/Extraction.lean): on every path,
whatever the answers, the program makes at most m queries, and its result has the property P; `W`: a
`QueryLayout lam L` (Iop/BatchWire.lean), the wire record; `WP`: a `WireBP L` (Iop/BatchWireP.lean): the
prover's data for the three protocols, and the enumeration of the encoding randomness; `p`: a
`Params` (Compile/Star.lean).
-/
import Compile.Batch.CompleteAcc
import Compile.Batch.RealQTree
import Compile.Batch.SpecBinding
import Compile.Batch.Hash
import Compile.Extraction
import Compile.GlueBinding

noncomputable section

namespace Compile.Batch.Extr
open Iop Rom Prob Merkle Compile.Extr Compile.Batch.Cmpl
open scoped ENNReal

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (f : Fam (spec lam K L)) (tr : Trace (spec lam K L))

/-! ## Part 1. The trace holds the queries of a tree -/

theorem triI_reveal {S : OSpec} {sp : Split S} {α : Type} {f : Fam S} {tr : Trace S} {ts : List Tok}
    {k : List Bits → Step S sp α} {vs : List Bits} {Q : α → List Bits → Prop}
    (h : TriI f tr (k (ts.map fun u => vs.getD u [])) vs Q) :
    TriI f tr (Step.reveal ts k) vs Q := h

/-- the leaf query with the input x is an entry of the trace -/
def LeafIn' (x : LeafIn L) : Prop := (⟨OracleName.leaf, x, f OracleName.leaf x⟩ : QA (spec lam K L)) ∈ tr

theorem triI_leafE (sMT : ℕ) (b : Body L) (blind : Bool) (vs : List Bits) :
    TriI f tr (leafE (lam := lam) (K := K) sMT b blind) vs fun o vs' =>
      LeafIn' f tr ⟨b, saltVal vs' o.2⟩ := by
  unfold leafE
  cases blind with
  | true =>
    simp only [if_true]
    unfold leafT
    refine triI_fresh fun r => triI_marked fun hm => triI_reveal (triI_pure_iff.2 ?_)
    have h1 : saltVal
          ((vs ++ [List.ofFn fun i : Fin sMT => r.val.testBit i]) ++
            [List.ofFn ((split lam K L).split OracleName.leaf
                  (f OracleName.leaf
                    (⟨b, (vs ++ [List.ofFn fun i : Fin sMT => r.val.testBit i]).getD
                        vs.length []⟩ : LeafIn L))).2])
          (some (vs.length, (vs ++ [List.ofFn fun i : Fin sMT => r.val.testBit i]).length)) =
        (vs ++ [List.ofFn fun i : Fin sMT => r.val.testBit i]).getD vs.length [] :=
      getD_of_prefix (List.prefix_append _ _) (by simp)
    unfold LeafIn'
    rw [h1]
    exact hm
  | false =>
    simp only [Bool.false_eq_true, if_false]
    exact triI_plain fun hm => triI_pure_iff.2 hm

theorem triI_leavesE (sMT : ℕ) :
    ∀ (l : List (Body L × Bool)) (vs : List Bits),
      TriI f tr (leavesE (lam := lam) (K := K) sMT l) vs fun o vs' =>
        ∀ x ∈ l.zip o.2, LeafIn' f tr ⟨x.1.1, saltVal vs' x.2⟩
  | [], _ => triI_pure_iff.2 fun _ h => by cases h
  | (b, bl) :: t, vs => by
      refine TriI.bind ((triI_leafE f tr sMT b bl vs).and (TriI.of_tri (tri_leafE f sMT b bl vs)))
        fun x vs1 hx => ?_
      refine TriI.bind ((triI_leavesE sMT t vs1).and (TriI.of_tri (tri_prefix _ vs1)))
        fun r vs2 hr => triI_pure_iff.2 ?_
      intro y hy
      rcases List.mem_cons.1 (show y ∈ ((b, bl), x.2) :: t.zip r.2 from hy) with rfl | h
      · show LeafIn' f tr ⟨b, saltVal vs2 x.2⟩
        rw [saltVal_of_prefix hr.2 hx.2.2.1]
        exact hx.1
      · exact hr.1 y h

theorem triI_pairUp :
    ∀ (l : List (Dig lam)) (vs : List Bits),
      TriI f tr (pairUp (nodeE (K := K) (L := L)) l) vs fun _ _ =>
        PairsIn (pairM lam K L) (nodeFB f) tr l
  | [], _ => triI_pure_iff.2 fun i h => by simp at h
  | [_], _ => triI_pure_iff.2 fun i h => by simp at h
  | a :: b :: t, vs => by
      refine TriI.bind
        (Q := fun _ _ =>
            (⟨OracleName.node, (List.ofFn a, List.ofFn b),
                f OracleName.node (List.ofFn a, List.ofFn b)⟩ : QA (spec lam K L)) ∈ tr)
        (triI_plain fun hm => triI_pure_iff.2 hm) fun c vs1 hc => ?_
      refine TriI.bind (triI_pairUp t vs1) fun r vs2 hr => triI_pure_iff.2 ?_
      intro i hi
      cases i with
      | zero => exact node_recorded_iff.2 hc
      | succ i =>
        have e1 : 2 * (i + 1) = 2 * i + 1 + 1 := by omega
        have e2 : 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 := by omega
        rw [e2, e1, List.getD_cons_succ, List.getD_cons_succ,
          List.getD_cons_succ, List.getD_cons_succ]
        exact hr i (by simp only [List.length_cons] at hi; omega)

theorem tri_pairUp (l : List (Dig lam)) (vs : List Bits) :
    Tri f (pairUp (nodeE (K := K) (L := L)) l) vs fun o vs' =>
      o = pairUpF (nodeFB f) l ∧ vs' = vs :=
  (evaluates_step f).pairUp (qN := nodeE (K := K) (L := L)) (hN := nodeFB f)
    (fun _ _ _ => tri_plain_iff.2 (tri_pure_iff.2 ⟨rfl, rfl⟩)) l vs

theorem triI_levelsM :
    ∀ (d : ℕ) (l : List (Dig lam)) (vs : List Bits),
      TriI f tr (levelsM (nodeE (K := K) (L := L)) d l) vs fun _ _ =>
        LevelsIn (pairM lam K L) (nodeFB f) tr d l
  | 0, _, _ => triI_pure_iff.2 trivial
  | d + 1, l, vs => by
      refine TriI.bind ((triI_pairUp f tr l vs).and (TriI.of_tri (tri_pairUp f l vs)))
        fun u vs1 hu => ?_
      obtain ⟨h1, rfl, rfl⟩ := hu
      exact TriI.bind (triI_levelsM d _ _) fun r vs2 hr => triI_pure_iff.2 ⟨h1, hr⟩

/-- The trace holds all queries of the tree: the leaf queries and the node queries. -/
def TreeIn (vs : List Bits) (t : TreeH lam) (d : ℕ) (leaf : ℕ → Body L × Bool) : Prop :=
  (∀ j < 2 ^ d, LeafIn' f tr ⟨(leaf j).1, saltVal vs (t.salts.getD j none)⟩) ∧
  LevelsIn (pairM lam K L) (nodeFB f) tr d
    ((List.range (2 ^ d)).map fun j => leafFB f ⟨(leaf j).1, saltVal vs (t.salts.getD j none)⟩)

theorem triI_commitE (sMT d : ℕ) (leaf : ℕ → Body L × Bool) (vs : List Bits) :
    TriI f tr (commitE (lam := lam) (K := K) sMT d leaf) vs fun t vs' =>
      TreeIn f tr vs' t d leaf := by
  refine TriI.bind ((triI_leavesE f tr sMT _ vs).and (TriI.of_tri (tri_leavesE f sMT _ vs)))
    fun x vs1 hx => ?_
  refine TriI.bind ((triI_levelsM f tr d x.1 vs1).and (TriI.of_tri (tri_levelsE f d x.1 vs1)))
    fun lv vs2 hlv => triI_pure_iff.2 ?_
  obtain ⟨hin, -, rfl⟩ := hlv
  obtain ⟨h0, h1, -, h3, -⟩ := hx
  have hl : x.2.length = 2 ^ d := by simpa using h1
  refine ⟨fun j hj => ?_, ?_⟩
  · have hjl : j < x.2.length := by rw [hl]; exact hj
    refine h0 (leaf j, x.2.getD j none) ?_
    rw [List.mem_iff_getElem]
    refine ⟨j, by simp [hl, hj], ?_⟩
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]
  · show LevelsIn _ _ _ _
      ((List.range (2 ^ d)).map fun j => leafFB f ⟨(leaf j).1, saltVal vs2 (x.2.getD j none)⟩)
    rw [← zipWith_range (fun (y : Body L × Bool) tk => leafFB f ⟨y.1, saltVal vs2 tk⟩)
          _ leaf x.2 none hl, ← h3]
    exact hin

/-! ## Part 2. Without a hash event the extractor finds every leaf of a tree that is correct
(`TreeOK`) and whose queries the trace holds (`TreeIn`) -/

variable {f tr}

theorem extLeaf_of_tree (hu : ¬ EM tr) {sMT : ℕ} {vs : List Bits} {t : TreeH lam} {d : ℕ}
    {leaf : ℕ → Body L × Bool} (hok : TreeOK f sMT vs t d leaf) (hin : TreeIn f tr vs t d leaf)
    {j : ℕ} (hj : j < 2 ^ d) :
    extLeaf tr d t.root j = some ⟨(leaf j).1, saltVal vs (t.salts.getD j none)⟩ := by
  have hcl := climbsIn_pathOf (pairM lam K L) (nodeFB f) d _ j hin.2 (by simp) hj
  rw [← hok.2.2.2] at hcl
  have hget : (((List.range (2 ^ d)).map fun j =>
          leafFB f ⟨(leaf j).1, saltVal vs (t.salts.getD j none)⟩).getD
        j default) =
      leafFB f ⟨(leaf j).1, saltVal vs (t.salts.getD j none)⟩ := by
    simp [List.getD_eq_getElem?_getD, hj]
  rw [hget] at hcl
  exact (pairM lam K L).preimage_of_opensIn hu
    (opensIn_of_climbsIn (pairM lam K L) (leaf_recorded_iff.2 (hin.1 j hj)) d _ _
      (by rw [hok.2.2.2]; exact length_pathOf_levelsF _ _ _ _) hcl)

section Scheme
variable {W : QueryLayout lam L} (WP : WireBP L) (p : Params) {fW : Fam (spec lam W.K L)} {trW : Tc W}

theorem triI_nodeP' (i : I) (vs : List Bits) : TriI fW trW (nodeP' W WP p i) vs fun nd vs' =>
    NodeOK p fW vs' i nd ∧ TreeIn fW trW vs' nd.tree W.depth (Cmpl.encLeaf i nd.r) := by
  refine (TriI.of_tri (tri_nodeP' WP p fW i vs)).and ?_
  refine TriI.bind (triI_true _ _) fun r vs0 _ => ?_
  exact TriI.bind (triI_commitE fW trW p.sMT W.depth (Cmpl.encLeaf i r) vs0)
    fun t vs1 ht => triI_pure_iff.2 ht

theorem extEnc_eq (hW : W.OK) {cm : Dig lam} {y : Fin L.wordLength → L.Symbol}
    (h : ∀ q : Fin L.wordLength, ∃ s, extLeaf trW W.depth cm q.val = some ⟨some (.inl (y q)), s⟩) :
    extEnc W trW cm = y := by
  funext q
  obtain ⟨s, hs⟩ := h q
  exact hW.B.ext.build_rd _ q (y q) (by simp only [hs])

end Scheme

/-! ## Part 3. The number of queries for one node -/

local notation "T1" => fun _ => True

theorem sq_leafE (sMT : ℕ) (b : Body L) (bl : Bool) :
    SQ (leafE (lam := lam) (K := K) sMT b bl) 1 T1 := by
  unfold leafE
  cases bl with
  | true => exact fun _ => ⟨0, rfl, fun _ _ _ => trivial⟩
  | false => exact ⟨0, rfl, fun _ => trivial⟩

theorem sq_leavesE (sMT : ℕ) : ∀ l : List (Body L × Bool),
    SQ (leavesE (lam := lam) (K := K) sMT l) l.length fun o => o.1.length = l.length
  | [] => rfl
  | (b, bl) :: t => by
      refine SQ.bind' (sq_leafE sMT b bl) (m' := t.length) (fun x _ => ?_) (by simp; omega)
      refine SQ.bind' (sq_leavesE sMT t) (m' := 0) (fun r hr => ?_) (Nat.le_refl _)
      show (x.1 :: r.1).length = ((b, bl) :: t).length
      rw [List.length_cons, List.length_cons, hr]

theorem sq_pairUp : ∀ (n : ℕ) (l : List (Dig lam)), l.length = 2 * n →
    SQ (pairUp (nodeE (K := K) (L := L)) l) n fun u => u.length = n
  | 0, [], _ => rfl
  | 0, _ :: _, h => by simp at h
  | _ + 1, [], h => by simp at h
  | n + 1, [_], h => by simp at h; omega
  | n + 1, a :: b :: t, h => by
      refine ⟨n, rfl, fun c => ?_⟩
      show SQ
        ((pairUp (nodeE (K := K) (L := L)) t).bind fun r => Step.pure ((show Dig lam from c) :: r))
        n _
      refine SQ.bind' (sq_pairUp n t (by simp only [List.length_cons] at h; omega)) (m' := 0)
        (fun r hr => ?_) (Nat.le_refl _)
      show ((show Dig lam from c) :: r).length = n + 1
      rw [List.length_cons, hr]

theorem sq_levelsM :
    ∀ (d : ℕ) (l : List (Dig lam)),
      l.length = 2 ^ d → SQ (levelsM (nodeE (K := K) (L := L)) d l) (2 ^ d - 1) T1
  | 0, _, _ => trivial
  | d + 1, l, h => by
      have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
      refine SQ.bind' (sq_pairUp (2 ^ d) l (by rw [h, pow_succ, Nat.mul_comm])) (m' := 2 ^ d - 1)
        (fun u hu => ?_) (by rw [pow_succ]; omega)
      exact SQ.bind' (sq_levelsM d u hu) (m' := 0) (fun _ _ => trivial) (Nat.le_refl _)

theorem sq_commitE (sMT d : ℕ) (leaf : ℕ → Body L × Bool) :
    SQ (commitE (lam := lam) (K := K) sMT d leaf) (2 * 2 ^ d - 1) T1 := by
  have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
  refine SQ.bind' (sq_leavesE sMT _) (m' := 2 ^ d - 1) (fun x hx => ?_) (by simp; omega)
  exact SQ.bind' (sq_levelsM d x.1 (by rw [hx]; simp)) (m' := 0)
    (fun _ _ => trivial) (Nat.le_refl _)

theorem sq_nodeP' (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I) :
    SQ (nodeP' W WP p i) (2 * 2 ^ W.depth) T1 := by
  intro rr
  show SQ ((commitE p.sMT W.depth (Cmpl.encLeaf i (WP.ri.e rr))).bind fun t =>
      Step.pure (⟨WP.ri.e rr, t⟩ : Node lam L))
    _ _
  exact SQ.bind' (sq_commitE p.sMT W.depth _) (m' := 0) (fun _ _ => trivial) (by omega)

end Compile.Batch.Extr

/-! ## Part 4. The theorem -/

namespace Compile.Batch
open Iop Rom Prob MeasureTheory Compile.Extr Compile.Batch.Cmpl Compile.Batch.Extr
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- the extraction error: a bound for a hash event among the at most 2 · 2^depth queries for the
tree under the root in the verification key -/
def deltaB (W : QueryLayout lam L) : ℝ≥0∞ := 2 * ((2 * 2 ^ W.depth : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam

/-- The counterpart, for this scheme, of the optional requirement of ZKCP/Optional.lean, under
`L.Wired` and `W.OK`: for the honest committer the extracted index is i, except with probability at
most `deltaB W`. -/
def Spec.extractsHonestB : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params), L.Wired →
    W.OK →
    ∀ i : I, pr (C W WP p i).withTrace.law {o | (extractorB W).Ei o.1.1 o.2 ≠ some i} ≤ deltaB W

namespace Extr

/-- what the committer does after it has built the tree under the root -/
def restC (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I) (root : Node lam L) :
    St lam W.K L (IVK lam L × IskH lam L) :=
  (proveT W WP p root.tree i root.r).bind fun πT => (leavesC W WP p i root (p.M + 1)).bind fun ls =>
    Step.pure (⟨root.tree.root, πT⟩, ⟨i, root, ls⟩)

theorem tri_top {S : OSpec} {sp : Split S} {α : Type} (f : Fam S)
    (c : Step S sp α) (vs : List Bits) : Tri f c vs fun _ _ => True :=
  fun _ _ => trivial

theorem tri_restC (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (f : Fam (spec lam W.K L)) (i : I)
    (root : Node lam L) (vs : List Bits) :
    Tri f (restC W WP p i root) vs fun o _ => o.1.cm = root.tree.root :=
  Tri.bind (tri_top f _ vs) fun _ vs1 _ =>
    Tri.bind (tri_top f _ vs1) fun _ _ _ => tri_pure_iff.2 rfl

theorem C_eq (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I) :
    C W WP p i = (erase (nodeP' W WP p i) []).bind fun x =>
      (eraseR (restC W WP p i x.1) x.2).bind fun o => OComp.pure (o.1.1, (o.1.2, o.2)) := by
  have h : Cp W WP p i = (nodeP' W WP p i).bind (restC W WP p i) := rfl
  have e : C W WP p i = (eraseR (Cp W WP p i) []).bind fun o => .pure (o.1.1, (o.1.2, o.2)) :=
    realQ_bind _ _
  rw [e, h, eraseR_bind, eraseR_nodeP', OComp.bind_assoc]

end Extr

/-- Under `L.Wired` and `W.OK`: for the honest committer the extracted index is the committed one,
except with probability at most `deltaB W`: `Spec.extractsHonestB` holds. -/
theorem extractsHonestB : Spec.extractsHonestB := by
  intro I X lam L W WP p hwd hW i
  have hA : (erase (nodeP' W WP p i) []).QueryBound (2 * 2 ^ W.depth) :=
    (sq_nodeP' W WP p i).erase []
  refine le_trans ?_ (hashEvents (erase (nodeP' W WP p i) []) _ hA)
  rw [← Pr_eq_law, ← Pr_eq_law]
  refine lintegral_mono fun f => ?_
  unfold PrCoins
  rw [Extr.C_eq, withTrace_bind, OComp.runEager_bind]
  have key := pr_bind_le_add ((erase (nodeP' W WP p i) []).withTrace.runEager f)
    (fun a =>
      (((eraseR (Extr.restC W WP p i a.1.1) a.1.2).bind fun o =>
          OComp.pure (o.1.1, (o.1.2, o.2))).withTrace.bind
        fun b => OComp.pure (b.1, a.2 ++ b.2)).runEager f)
    {o : (IVK lam L × ISK lam L) × Tc W | (extractorB W).Ei o.1.1 o.2 ≠ some i}
    {o | EM o.2 ∨ EF o.2} (ε := 0) fun a ha hn => ?_
  · rw [add_zero] at key
    exact key
  · refine le_of_eq (pr_eq_zero_of_forall_not_mem _ fun o ho hbad => hbad ?_)
    obtain ⟨b, hb, hob⟩ := mem_outs_bind.1 (show o ∈ Outs f _ from ho)
    obtain rfl := mem_outs_pure.1 hob
    have hEM : ¬ EM a.2 := fun h => hn (Or.inl h)
    obtain ⟨hok, hin⟩ := triI_nodeP' WP p i [] a.1 (outsIn_of_withTrace (show a ∈ Outs f _ from ha))
    obtain ⟨z, hz, hbz⟩ := mem_outs_bind.1 (outs_of_outsIn (outsIn_of_withTrace hb))
    have hcm : b.1.1.cm = a.1.1.tree.root := by
      rw [mem_outs_pure.1 hbz]
      exact Extr.tri_restC W WP p (realF f) i a.1.1 a.1.2 z (outs_realQ hz)
    show L.decodeIndex (extEnc W (a.2 ++ b.2) b.1.1.cm) = some i
    rw [hcm, extEnc_eq (y := L.encodeIndex i a.1.1.r) hW fun q => ?_, hwd.dec_enc]
    have h1 := extLeaf_of_tree hEM hok hin (j := q.val) (lt_of_lt_of_le q.isLt hW.fits)
    rw [Cmpl.encLeaf_val] at h1
    exact ⟨_, (pairM lam W.K L).preimage_mono (List.prefix_append _ _) h1⟩

end Compile.Batch
