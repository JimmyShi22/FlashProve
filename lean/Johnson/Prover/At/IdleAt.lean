-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/At/IdleAt.lean: THREE IDLE HONEST RECORDS OVER THE THREE PROTOCOLS OF THE COMPILER's
INPUT AT WRITTEN DATA, AND: THEY MEET HonFit (Johnson/Prover/All/OfHonest.lean) WITH NO FALL
(Falls.none) AT THE NUMBERS 0, 1, 1, 1. For all data; then at the told record of a family, at the
letters S of the public files, and at the told record of the goals' description with its number of
coins laid anew.

IT SAYS NOTHING ON COMPLETENESS. The withheld set of each record is everything: so the three clauses
on acceptance ask nothing, and the three measures are bounded by 1.

The withheld set is everything. So every statement of honest-verifier zero knowledge at these
honest sides is empty too: whatever is withheld on every run is simulated by saying nothing. (That
sentence is laid here so that nobody spends these
honest sides on a statement on hiding; this file says no other word there.)

What is shown: the clauses of HonFit do not contradict each other at these protocols: above all the
clause on the copy's number, which is no empty one: the session's strategy writes the number that
its record is handed into the front's plain part, and a nonce is written into no plain part of the
front round.

Main names.
  idleRecs   the records: strategies idleW (Johnson/Prover/Print/IdleStrat.lean) at the two whole
    files, the fixed messages at the link; coins: two digests at each whole file (CoinRuns,
    Johnson/Goal/Conditions/HomeTieMet.lean).
  front_of_puts   a transcript that is another but for nonces has its front's plain part.
  recsReBound, fallsReBound, honFit_reBound   laying the number of coins anew turns nothing.
  honFit_idle_fullD, honFit_idle_famD, honFit_idle_layoutsByPublicReading   THE STATEMENT, for all data; at a family;
    at S.

Limits. No verifier is said to accept anything. The records are no honest provers of anything.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.At.ToldAt
import Johnson.Goal.Conditions.ReBound
import Johnson.Prover.All.OfHonest
import Johnson.Prover.Print.IdleStrat
import Johnson.Goal.Conditions.HomeTieMet

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Prover (ThreeProvers Falls HonFit Puts AccLaw)
open Johnson.Prover.Print (idleW)
open FlashProve (CoinRuns)
open scoped ENNReal

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)

/-- **The three idle records.** The withheld set is everything. -/
def idleRecs : ThreeProvers (innerCompilerInputAtFullSize T).protocol where
  T :=
    { Coin := CoinRuns Unit
      neCoin := ⟨((), (fun _ => false, fun _ => false))⟩
      ext := fun w => (innerCompilerInputAtFullSize T).protocol.encodeIndex w.1 w.2.1
      strat := fun _ _ c => idleW (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
        ByteArray.empty (front₀ rK) ⟨(join₀ rK).answers, digToBytes c.2.1⟩ (digToBytes c.2.2)
      Bad := Set.univ
      Hid := fun _ _ => Set.univ }
  Lk :=
    { Coin := Unit
      neCoin := ⟨()⟩
      ext := fun w => ((innerCompilerInputAtFullSize T).protocol.encodeIndex w.1 w.2.1.1, (innerCompilerInputAtFullSize T).protocol.encodeIndex w.1 w.2.2.1)
      strat := fun _ _ _ => Strat.dflt _ ()
      Bad := Set.univ
      Hid := fun _ _ => Set.univ }
  B :=
    { Coin := CoinRuns Unit
      neCoin := ⟨((), (fun _ => false, fun _ => false))⟩
      ext := fun w => (innerCompilerInputAtFullSize T).protocol.encodeIndex w.1 w.2.1
      strat := fun w _ c => idleW (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
        ByteArray.empty ⟨(front₀ rP).answers, w.2.2.2⟩ ⟨(join₀ rP).answers, digToBytes c.2.1⟩
        (digToBytes c.2.2)
      Bad := Set.univ
      Hid := fun _ _ => Set.univ }

/-- A transcript of the proof file that is another but for nonces has its front's plain part. -/
theorem front_of_puts (τ₀ τ : Tr (innerCompilerInputAtFullSize T).protocol.onlineBatch.loc.shape)
    (h : Puts (innerCompilerInputAtFullSize T).protocol.onlineBatch.loc.shape (innerCompilerInputAtFullSize T).protocol.onlineBatch.ann
      (wBC (innerCompilerInputAtFullSize T).queryLayout).sh τ₀ τ) : τ.1.2 = τ₀.1.2 := by
  rcases h.2.2.1 with e | ⟨g, n, -, e, -⟩ | ⟨g, n, -, e, -⟩
  · exact e
  · cases e
  · cases e

/-- **The idle records meet HonFit**, for all data. -/
theorem honFit_idle_fullD (hn : T.num = PV.Front.numCopy) (Yes : (innerCompilerInputAtFullSize T).Index → X → Prop) :
    HonFit (idleRecs T) (Falls.none _) (innerCompilerInputAtFullSize T).queryLayout (innerCompilerInputAtFullSize T).seedQueries Yes
      (fun _ _ => ∅) 0 1 1 1 where
  extT := fun _ _ _ => rfl
  extL := fun _ _ _ _ _ => rfl
  extB := fun _ _ _ _ => rfl
  whT := fun _ _ _ _ _ => Or.inl (Or.inl (Set.mem_univ _))
  whL := fun _ _ _ _ _ => Or.inl (Or.inl (Set.mem_univ _))
  whB := fun _ _ _ _ _ => Or.inl (Or.inl (Set.mem_univ _))
  accT := fun _ _ _ _ _ _ _ _ _ _ h => absurd (Or.inl (Or.inl (Set.mem_univ _))) h
  accL := fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => absurd (Or.inl (Or.inl (Set.mem_univ _))) h
  accB := fun _ _ _ _ _ _ _ _ _ _ _ h => absurd (Or.inl (Or.inl (Set.mem_univ _))) h
  prZ := fun _ _ _ _ => by simp [pr]
  prT := fun _ _ _ _ _ _ => pr_le_one _ _
  prL := fun _ _ _ _ _ _ _ _ => pr_le_one _ _
  prB := fun _ _ _ _ _ _ _ => pr_le_one _ _
  num := fun _ _ _ _ n _ τ _ hp => by
    have hf := front_of_puts T _ τ hp
    show T.num n τ.plains = true
    rw [hn]
    exact decide_eq_true (show τ.1.2.copy = n from congrArg FrontMsg.copy hf)

/-! ## At the told record of a family -/

section Fam
open OnBytes.K.Arm.Pub (D8)
variable {T₀ : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P}
  (U : FamLettersD T₀) (d : D8)

set_option maxRecDepth 20000 in
theorem honFit_idle_famD (hn : T₀.num = PV.Front.numCopy)
    (Yes : (innerCompilerInputAtFullSize T₀).Index → X → Prop) :
    HonFit (idleRecs T₀) (Falls.none _) (innerCompilerInputAtFullSize T₀).queryLayout ((toldFamD U).Sd d) Yes
      (fun _ _ => ∅) 0 1 1 1 :=
  honFit_idle_fullD (lettersFamD U d) hn Yes

end Fam

/-! ## Laying the number of coins anew turns nothing -/

section ReBound
variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (b : ℕ) (d : T.D)

/-- Three records over an input's protocols, as records over the input with another number of
coins. -/
def recsReBound (Hs : ThreeProvers R.protocol) : ThreeProvers (R.reBound b).protocol := Hs

/-- Falls at three records, as falls at the records over the input with another number of coins. -/
def fallsReBound {Hs : ThreeProvers R.protocol} (F : Falls Hs) : Falls (recsReBound b Hs) := F

theorem honFit_reBound (Hs : ThreeProvers R.protocol) (F : Falls Hs) (Yes : R.Index → R.Instance → Prop)
    (Z : R.Index → R.protocol.EncodingRandomness → Set R.protocol.OutOfDomainSeed) (ζ pT pL pO : ℝ≥0∞)
    (h : HonFit Hs F R.queryLayout (T.Sd d) Yes Z ζ pT pL pO) :
    HonFit (recsReBound b Hs) (fallsReBound b F) (R.reBound b).queryLayout ((T.reBound b).Sd d) Yes Z ζ pT pL
      pO := h

end ReBound

end VerifiableInference.OnPublicFiles

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run
open _root_.Iop (Dig)
open OnBytes.K.Arm.Pub (D8)
open LPFD.Full (XF)
open OnBytes.Prover (HonFit Falls)

/- Lean compares these names and does not unfold them (as in Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean). -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256)) (d : D8)

/-- the family's letters at S -/
local notation "𝔉" => LPFD.Full.famD S.A S.E S.G S.DK S.DP S.runK S.runP S.dec S.P S.hStar S.it
  Zk.pol Zk.KL Zk.lay S.sR S.hDK S.hDP S.hK S.N S.d₀ (c₀, m₀)

set_option maxRecDepth 20000 in
theorem honFit_idle_layoutsByPublicReading (Yes : (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).Index → XF → Prop) :
    HonFit (idleRecs (S.inputFieldsAtReadings c₀ m₀)) (Falls.none _) (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout
      ((S.layoutsByPublicReading c₀ m₀).Sd d) Yes (fun _ _ => ∅) 0 1 1 1 :=
  honFit_idle_famD 𝔉 d (num_tOf S c₀ m₀) Yes

end FlashProve
