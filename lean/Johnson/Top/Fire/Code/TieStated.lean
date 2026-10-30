-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/TieStated.lean. STATEMENTS ALONE: FOUR PROPOSITIONS, NONE PROVED HERE. The
full size.
The tie from what runs to the verifier of which the soundness theorem at the frame's make speaks
(`innerCompiledVerifierSoundAtFullSize`, `innerCompiledVerifierSoundAtFullSize_for`,
Johnson/Flat/Dec/TwoSizesAt.lean: they speak of `innerSystem (innerCompilerInputAtFullSize T)`).
  `TieT0`: the verifier's side of that input is the value of `InputV` that the sheet writes out
  (`DvOf`), at the letters of T.
  `TieT1`: the same at `DvE`, the value at which the fast form's equations stand.
  `TieT2D`: the chain for `fastD` (the family read off the hash through the coding): no premise
  beside sT's.
  `TieT2F`: THE CHAIN FOR WHAT RUNS: `fastF` at a family Ff and the hash made of O, UNDER THE
  PREMISE `ReadsAs T.m.v O Ff`.
T is taken AT depthReq := sB.logLeaves (types hang on it: it cannot be a
hypothesis); sT's depth is a hypothesis.
LIMITS, WHICH GO WITH THESE STATEMENTS WHEREVER THEY ARE TOLD.
 1. ∀ T: no T is laid IN THIS FILE (one is laid: `tAt`, TieAtValues.lean; filled:
 TieFilled.lean, NamedReal.lean). T holds three honest provers, a
    coding m that is one to one and onto, commit, prove, an extractor.
 2. m IS THE LETTER T.m READ AT THE VERIFIER's SIDE. What runs has a coding with code, which is NOT
 such a T.m's verifier's side as
    a record (they part at the spare oracle): one link more is owed and is not here.
 3. enc is T.enc read at the verifier's side: free.
 4. The entry file's three letters ds, xs, dec are free.
 5. THESE STATEMENTS PAY NONE OF THE SOUNDNESS THEOREM's HYPOTHESES, AND OVER THE TWIN FRAME THAT
 THEOREM ASKS MORE THAN THE ONE OF Johnson/Flat/TwoSizesAt.lean: `entrySound` is a NAMED HYPOTHESIS
 there
    (that frame proves it, at its own decision alone); four tests on the entry's rounds' numbers are
    new; the test on K is at another list; its hA is gone.
 6. The proof is the one that Lean lays of what a parser hands over (`proofE`); the parser stands
 outside.
 7. The seed is `recSeedK` at a proof that its blocks fit K + 1 (T.hSeed).
 8. THE THEOREM BINDS T OUTSIDE THE PROBABILITY: a letter that is made with the hash, or read off
 the key, the proof or the request, leaves it.
-/
import Johnson.Flat.Dec.TwoLettersAt
import Johnson.Top.InnerCompiledVerifierBack
import Johnson.Top.Fire.Code.FastFamProbe

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open TypedOracleCompiler.Run.PQ (SOf)

variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A) (DK DP : WholeD)
  (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecFull × RecFull → PQ.View → Bool) (rK rP : RecFull)
  (sB : Params.LinBindingShape) (early : X → X) (salt K : ℕ)
  (P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP sB.logLeaves early salt).Provers)

/-- The entry file's decision in the frame of Johnson/Flat/WiresAtSizes.lean (`entryFullM`). -/
abbrev decW : RecFull × RecFull → PQ.View → Bool := fun rr => decFullX (recX rr)

variable {A E DK DP runK runP ds xs dec rK rP sB early salt K P}

/-- The sheet's value `DvOf` at the letters of T. -/
abbrev DvT (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP sB.logLeaves early salt K P) : InputV :=
  DvOf DK DP runK runP rK rP sB.logLeaves T.depthReqT early (linkFullD ds xs dec) K salt
    (_root_.Run.Twin.allLo (SOf (ckP .two) ds))
    (wSib (restOfFullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP sB.logLeaves early salt P) K (chalP .two K))
    (TypedOracleCompiler.StringsList.embT salt (ckP .two) ds)
    (TypedOracleCompiler.StringsList.prjT salt (ckP .two) ds)
    T.t T.cfg T.shape T.pl0 T.pl1 T.num (recSeedK recT recLg recS (K + 1) T.hSeed) T.r₀ T.p T.m.v
    (fun k => T.enc ⟨k.cm, k.rcd⟩) T.build

/-- The value `DvE` at the letters of T and a shape sT of the key file's binding tree. -/
abbrev DvET (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP sB.logLeaves early salt K P) (sT : Params.LinBindingShape) : InputV :=
  DvE DK DP runK runP rK rP sT sB early ds xs dec K salt
    T.t T.cfg T.shape T.pl0 T.pl1 T.num (recSeedK recT recLg recS (K + 1) T.hSeed) T.r₀ T.p T.m.v
    (fun k => T.enc ⟨k.cm, k.rcd⟩) T.build

variable (A E DK DP runK runP ds xs dec rK rP sB early salt K P)

/-- (T0) -/
def TieT0 : Prop :=
  ∀ T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP sB.logLeaves early salt K P, (innerCompilerInputAtFullSize T).toInputV = DvT T

/-- (T1) -/
def TieT1 : Prop :=
  ∀ (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP sB.logLeaves early salt K P) (sT : Params.LinBindingShape), sT.logLeaves = T.depthReqT →
    (innerCompilerInputAtFullSize T).toInputV = DvET T sT

/-- (T2), for the family that is read off the hash through the coding. -/
def TieT2D : Prop :=
  ∀ (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP sB.logLeaves early salt K P) (sT : Params.LinBindingShape), sT.logLeaves = T.depthReqT →
    ∀ (hash : Hash) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
      (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn),
      fastD DK DP runK runP rK rP sT sB early ds xs dec K salt
          T.t T.cfg T.shape T.pl0 T.pl1 T.num (recSeedK recT recLg recS (K + 1) T.hSeed) T.r₀ T.p T.m.v
          (fun k => T.enc ⟨k.cm, k.rcd⟩) T.build hash commitment prompt output aux cm rcd copy fT e fB =
        ((innerSystem (innerCompilerInputAtFullSize T)).verify commitment prompt output
          ((innerCompilerInputAtFullSize T).back
            (proofE DK DP runK runP rK rP sT sB early ds xs dec aux cm rcd copy fT e fB))).evaluate hash

/-- (T2), FOR WHAT RUNS: the fast form at a family Ff, under the premise that Ff is what the coding
reads out of the hash made of O. -/
def TieT2F : Prop :=
  ∀ (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP sB.logLeaves early salt K P) (sT : Params.LinBindingShape), sT.logLeaves = T.depthReqT →
    ∀ (O : ByteArray → ByteArray) (Ff : Fam (typedOracleFamily 256 (K + 1) (carrierV (DvET T sT).L (List Bool) (DvET T sT).aT (DvET T sT).aL))),
      ReadsAs T.m.v O Ff →
    ∀ (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
      (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn),
      fastF DK DP runK runP rK rP sT sB early ds xs dec K salt
          T.t T.cfg T.shape T.pl0 T.pl1 T.num (recSeedK recT recLg recS (K + 1) T.hSeed) T.r₀ T.p Ff
          (fun k => T.enc ⟨k.cm, k.rcd⟩) T.build (hashOf O) commitment prompt output aux cm rcd copy fT e fB =
        ((innerSystem (innerCompilerInputAtFullSize T)).verify commitment prompt output
          ((innerCompilerInputAtFullSize T).back
            (proofE DK DP runK runP rK rP sT sB early ds xs dec aux cm rcd copy fT e fB))).evaluate (hashOf O)

end VerifiableInference.OnPublicFiles.SlotsBehindCutD

#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.TieT0
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.TieT1
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.TieT2D
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.TieT2F
