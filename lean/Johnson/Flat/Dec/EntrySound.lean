-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Dec/EntrySound.lean: behind the frame whose entry file's rounds' data, stored openings
and decision are letters (Johnson/Flat/Dec/): the entry file's named hypothesis on soundness
(`CompilerSoundnessConditionStatements.entrySound`, Johnson/Top/InnerCompiledVerifier.lean) UNDER ONE NAMED PREMISE on the decision; how a
decision on two keys, and one on an instance, enter the frame's letter; and the four tests on the
numbers of the entry's rounds' data as one test with code. The full size and the small size.

Why. In Johnson/Flat/Dec/TwoSizesAt.lean `entrySound` is a fourth field of `RemainingSoundnessConditionsAtFullSize`: a bare named
hypothesis. The library's road to it is general in the decision already: `linkSib_sound`
(OnBytes/Flat/LinkSib.lean) takes `SoundAt T v eM lg s dec κ C ds a xs`: one list of counts, below κ, with
which at every instance the written link at that instance's decision is sound for the entry's
language. So that is the form in which whoever writes the entry's decision owes the row.

Main names (Small for Full at the small size).
  `decOfXFull decE`: a decision on an instance (`SoundAt`'s type) as the frame's letter dec: at the instance
    made of the two records (`recX`): `linkSib`'s own make.
  `decOfKeysFull d`: a decision on two keys as a decision on an instance: at the two keys written of it
    (`keysOfX`): `decFullX`'s own make (`decFullX_eq`, by unfolding). `decOfKeysFull_recX`: at two records
    these are the keys written of the records, the second with item := 1.
  `entrySoundOfFullD`: `SoundAt … decE T.εs (ckP .two) ds frS.P.T.a xs` ⟹ `CompilerSoundnessConditionStatements.entrySound` at the
    frame at dec := `decOfXFull decE`, at every other letter.
  `entryFitB K ds`, `EntryFit K ds`, `entryFitB_iff`: the four tests, as a test and as what its yes says.

THE TWO SILLY MEMBERS. A decision that says no to all: `SoundAt` holds of it (all counts 0) and the row
holds for nothing. A decision that says yes to all: `SoundAt` at a κ below the rounds' share of work asks
that EVERY pair of words lies in the entry's language: false [an argument; no theorem].
Every "there is", walked. `CompilerSoundnessConditionStatements.entrySound` begins "there is a list of errors": it is the list that
`SoundAt` holds, which stands under "there is" ON THE PREMISE's SIDE: whoever shows it names it.

Limits. NOTHING IS SHOWN OF ANY DECISION: `SoundAt` is a premise. κ := T.εs: nothing says that it is small. NO
VALUE OF THIS FRAME HAS RUN ON A REAL PROOF. That ds, xs and the decision are one declared line of a
plan is seen at the value that is laid in. The tests' yes at any data is not evaluated here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.Dec.TwoSizesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace OnBytes.Flat
open OnBytes.Slice TypedOracleCompiler.Slice OnBytes.Tie
open OnBytes.Params (recordRead smallRecordRead)
open _root_.Run (bsRound)
open _root_.Run.PQ (View)

/-- A decision on an instance, as a decision on two records. -/
def decOfXFull (decE : XE AnsT 29 1 → View → Bool) : RecFull × RecFull → View → Bool :=
  fun rr => decE (recX rr)

/-- A decision on two keys, as a decision on an instance. -/
def decOfKeysFull (d : TableKey × TableKey → View → Bool) : XE AnsT 29 1 → View → Bool :=
  fun x => d (keysOfX frS.P.v 29 1 (anT frS.P.v 1) x)

/-- The written link's decision is of that make. -/
theorem decFullX_eq : decFullX = decOfKeysFull fun kk =>
    (linkVerify recordRead.link kk.1 kk.2).decides (Entry.start recordRead) := rfl

/-- At two records: the keys written of the records, the second with item := 1. -/
theorem decOfKeysFull_recX (d : TableKey × TableKey → View → Bool) (rr : RecFull × RecFull) :
    decOfXFull (decOfKeysFull d) rr =
      d (keyOf (fun β : NZ => β.val) rr.1, { keyOf (fun β : NZ => β.val) rr.2 with item := 1 }) := by
  unfold decOfXFull decOfKeysFull
  rw [keys_recX]

/-- The like at the small size. -/
def decOfXSmall (decE : XE AnsT 19 1 → View → Bool) : RecSmall × RecSmall → View → Bool :=
  fun rr => decE (recX rr)

def decOfKeysSmall (d : TableKey × TableKey → View → Bool) : XE AnsT 19 1 → View → Bool :=
  fun x => d (keysOfX srS.P.v 19 1 (anT srS.P.v 1) x)

theorem decOfKeysSmall_recX (d : TableKey × TableKey → View → Bool) (rr : RecSmall × RecSmall) :
    decOfXSmall (decOfKeysSmall d) rr =
      d (keyOf (fun β : NZ => β.val) rr.1, { keyOf (fun β : NZ => β.val) rr.2 with item := 1 }) := by
  unfold decOfXSmall decOfKeysSmall
  rw [keys_recX]

/-- The four tests on the numbers of the entry file's rounds' data, as one test: no round needs more
than K blocks or has more than 64 bits of work; the number of a tree that a round opens is below
2 ^ 16; no tree is deeper than 63. -/
def entryFitB (K : ℕ) (ds : List TypedOracleCompiler.Run.PQ.RD) : Bool :=
  ds.all fun d => decide ((bsRound .two d.entry d.kind).b ≤ K) && decide (d.entry.work ≤ 64) &&
    (d.opens.all fun n => decide (n < 2 ^ 16)) && d.trees.all fun s => decide (s.a ≤ 63)

/-- What its yes says, in the forms in which the frame's laws ask it. -/
structure EntryFit (K : ℕ) (ds : List TypedOracleCompiler.Run.PQ.RD) : Prop where
  bL : ∀ d ∈ ds, (bsRound .two d.entry d.kind).b ≤ K
  wLk : ∀ d ∈ ds, d.entry.work ≤ 64
  own : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16
  dL : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64

theorem entryFit_of_test {K : ℕ} {ds : List TypedOracleCompiler.Run.PQ.RD} (h : entryFitB K ds = true) :
    EntryFit K ds := by
  unfold entryFitB at h
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨fun d hd => (h d hd).1.1.1, fun d hd => (h d hd).1.1.2, fun d hd => (h d hd).1.2,
    fun d hd s hs => ?_⟩
  have h63 : s.a ≤ 63 := (h d hd).2 s hs
  calc 2 ^ s.a + 2 ^ s.a = 2 ^ (s.a + 1) := by rw [pow_succ]; omega
    _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)

end OnBytes.Flat

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open TypedOracleCompiler.Slice (XE AnsT)
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {decE : XE AnsT 29 1 → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs (decOfXFull decE) rK rP depthReq early
    salt).Provers}

/-- **The entry file's named hypothesis on soundness at the frame, under one named premise on the
decision.** -/
theorem entrySoundOfFullD
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs (decOfXFull decE) rK rP depthReq early salt K P)
    (hS : SoundAt frS.P.T frS.P.v frS.eM 29 1 decE T.εs (ckP .two) ds frS.P.T.a xs) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T) := by
  obtain ⟨ε, hs, hb⟩ := linkSib_sound frS.P.T frS.P.v frS.eM 29 1 decE _ A (relationsAndEncodingOfClaims A E) _ _ _ hS
  refine ⟨ε, ?_, hs⟩
  show Err.Below (Err.timesShared (2 ^ T.W.depthReqL)
    (_root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (_root_.Run.ckP .two) ds)) ε) _
  rw [_root_.Run.Twin.allLo_eq, timesShared_allLocal]
  exact hb

end

section
variable {X : Type} {A : (srS.toDecR srZ 524285).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecSmall → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecSmall → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {decE : XE AnsT 19 1 → PQ.View → Bool} {rK rP : RecSmall} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtSmallSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs (decOfXSmall decE) rK rP depthReq early
    salt).Provers}

/-- The like at the small size. -/
theorem entrySoundOfSmallD
    (T : InnerCompilerInputAndAnalysisFieldsAtSmallSize A E DK DP runK runP ds xs (decOfXSmall decE) rK rP depthReq early salt K
      P)
    (hS : SoundAt srS.P.T srS.P.v srS.eM 19 1 decE T.εs (ckP .two) ds srS.P.T.a xs) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtSmallSize T) := by
  obtain ⟨ε, hs, hb⟩ := linkSib_sound srS.P.T srS.P.v srS.eM 19 1 decE _ A (relationsAndEncodingOfClaims A E) _ _ _ hS
  refine ⟨ε, ?_, hs⟩
  show Err.Below (Err.timesShared (2 ^ T.W.depthReqL)
    (_root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (_root_.Run.ckP .two) ds)) ε) _
  rw [_root_.Run.Twin.allLo_eq, timesShared_allLocal]
  exact hb

end

end VerifiableInference.OnPublicFiles

#print axioms OnBytes.Flat.decFullX_eq
#print axioms OnBytes.Flat.decOfKeysFull_recX
#print axioms OnBytes.Flat.entryFit_of_test
#print axioms VerifiableInference.OnPublicFiles.entrySoundOfFullD
#print axioms VerifiableInference.OnPublicFiles.entrySoundOfSmallD
