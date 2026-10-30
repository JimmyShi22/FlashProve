-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Told/FamilyBy.lean: THE TOLD RECORD OF A FAMILY WITH THE PARAMETER BYTES AS A LETTER,
so that its text names no hash function. Definition, statements and proofs.

Why. `toldFamD U` (Johnson/Flat/Told/FamilyD.lean) has `pub8 recordGround` for its public reading.
`pub8` makes the strings that it asks by `par7`, which calls the planner, which names the format's
second hash function. So every term over the told record reaches a concrete hash function by name,
though the public reading's laws read nothing of how the parameter bytes are made.

Main names (namespace `VerifiableInference.OnPublicFiles`).
  `toldFamBy U par`: `toldFamD U` field for field, but for the public reading: `pubN Prod.mk (s0Of
    U.pol U.lay U.KL) (ssOf par)`: the string of the three public files, then, at the bytes c of the
    answer, the strings of the calls that hash the members of `par c`. par : ByteArray → List
    ByteArray IS A LETTER.
  `toldFamD_eq_by`: `toldFamD U` is this one at `par7 recordGround U.pol U.KL U.lay`: by
    definition.
  `famBy_noCoin`, `famBy_asks`, `famBy_once`: the three premises on the public reading, at every
    par. `famBy_reading`: where par gives at most n members, it asks at most n + 1 strings.
  `at_toldFamBy`: the record's input at d is the frame's input at `lettersFamD U d`: by definition.
    `core_toldFamBy`: the fifteen hypotheses of `CompilerSoundnessConditions` at every d: `core_toldFamD`:
    what stands beside the input at d does not read the public reading.

Limits. Those of FamilyD.lean. A walk over the environment (the print of a check that is not in
this library; no theorem) finds no concrete hash name from `toldFamBy`; from `toldFamD` it finds
three. This file names `pub8` and `par7` in one statement and one attribute line alone. Which par a
description's own reading takes, and that the two agree, is the user's to show.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.Told.FamilyD

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open OnBytes.Maker.Page _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.K.Arm OnBytes.K.Arm.Pub OnBytes.Tie
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  {T₀ : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P}
  (U : FamLettersD T₀) (par : ByteArray → List ByteArray)

/-- **The told record of the family, the parameter bytes a letter**: `toldFamD U`
(Johnson/Flat/Told/FamilyD.lean) field for field, but for the public reading: the string of the
three public files, then, at the bytes c of the answer, the strings of the calls that hash the
members of `par c`. -/
def toldFamBy : LayoutsByPublicReading (innerCompilerInputAtFullSize T₀) where
  D := D8
  Pub := pubN Prod.mk (s0Of U.pol U.lay U.KL) (ssOf par)
  Pt := OnBytes.Slice.IsCall169
  part := cfg8
  Sd := fun d => outOfDomainSampleQueryLayoutOfCode
    ((threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P)
    (List Bool) _ _ (v := frS.P.v) (lg := 29) (s := 1) T₀.t (U.cfgOf d) T₀.shape T₀.pl0 T₀.pl1
    T₀.num (recSeedK recT recLg recS T₀.W.K T₀.hK) id seedEqFull
  cA := fun _ => codeA (v := frS.P.v) (s := 1)
  m := U.mOf
  encT := U.encT
  ISK := Unit
  commit := fun _ => .pure ((U.d₀, ⟨U.d₀, rK⟩), ())
  prove := fun _ b =>
    .pure ⟨b.map fun _ => ⟨0, none, (U.d₀, rK, none), none⟩, List.length_map ..⟩
  π₀ := ((U.d₀, ⟨U.d₀, rK⟩), ⟨0, none, (U.d₀, rK, none), none⟩)

/-- **`toldFamD U` is this record at the parameter bytes `par7 recordGround U.pol U.KL U.lay`.** -/
theorem toldFamD_eq_by :
    toldFamD U = toldFamBy U (par7 recordGround U.pol U.KL U.lay) := rfl

theorem famBy_noCoin : (toldFamBy U par).Pub.NoCoin := pubN_noCoin _ _ _

theorem famBy_asks : (toldFamBy U par).Pub.AsksIn fun _ s => (toldFamBy U par).Pt s :=
  pubN_asksIn_of _ _ _ OnBytes.Slice.IsCall169 ⟨0, 0, 2, Fmt.zero32, _, Or.inl rfl, rfl, rfl⟩
    fun c s hs => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hs
      exact ⟨0, 0, 1, Fmt.zero32, _, Or.inl rfl, rfl, rfl⟩

theorem famBy_once : NoRepeat (toldFamBy U par).Pub := pubN_noRepeat _ _ _

/-- Where `par` gives at most n members, the public reading asks at most n + 1 strings. -/
theorem famBy_reading (n : ℕ) (hn : ∀ c, (par c).length ≤ n) :
    (toldFamBy U par).Pub.QueryBound (n + 1) :=
  pubN_queries _ _ _ n fun c => by
    unfold ssOf
    rw [List.length_map]
    exact hn _

/-- The record's input at d is the frame's input at the family's member, as `toldFamD U`'s. -/
theorem at_toldFamBy (d : D8) : (toldFamBy U par).at d = innerCompilerInputAtFullSize (lettersFamD U d) := rfl

/- Lean compares the name pub8 and does not unfold it. -/
attribute [local irreducible] pub8

/-- **The fifteen at every d**: `core_toldFamD`: what stands beside the input at d does
not read the public reading. -/
theorem core_toldFamBy (code : ZKCP.CodeIsOneToOne U.encT) (hk : kThree .two DK [] DP ≤ K)
    (bL : ∀ d ∈ ds, (bsRound .two d.entry d.kind).b ≤ K) (wLk : ∀ d ∈ ds, d.entry.work ≤ 64)
    (own : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (dL : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true) (kS : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize T₀))
    (eS : CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T₀))
    (pS : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize T₀)) (d : (toldFamBy U par).D) :
    CompilerSoundnessConditions ((toldFamBy U par).beside (soundnessAnalysisDataAtFullSize T₀).Wn (soundnessAnalysisDataAtFullSize T₀).Rno
                          (soundnessAnalysisDataAtFullSize T₀).x₀ (soundnessAnalysisDataAtFullSize T₀).εs d) :=
  core_toldFamD U code hk bL wLk own dL wK dK wP dP kS eS pS d

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.core_toldFamBy
#print axioms VerifiableInference.OnPublicFiles.toldFamD_eq_by
#print axioms VerifiableInference.OnPublicFiles.famBy_noCoin
#print axioms VerifiableInference.OnPublicFiles.famBy_asks
#print axioms VerifiableInference.OnPublicFiles.famBy_once
#print axioms VerifiableInference.OnPublicFiles.famBy_reading
#print axioms VerifiableInference.OnPublicFiles.at_toldFamBy
