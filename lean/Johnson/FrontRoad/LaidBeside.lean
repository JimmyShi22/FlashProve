-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/LaidBeside.lean: proofs of the two statements of
Johnson/FrontRoad/LaidBesideSpec.lean, that the proofs of the scheme laidId are produced, and the
statement of index privacy at the stored full-size public files' own settings, with two placeholder
provers, which send fixed messages.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has.
laidProduced proves Spec.laidProduced, and idLaidOwn proves Spec.idLaidOwn. What the two statements
say, how the first is stated, and their limits, is in the head of
Johnson/FrontRoad/LaidBesideSpec.lean.

  produced_typed   in general form, over the typed oracles, for all parameters: if the honest side
      never aborts and LawFit and WiresFit hold, the scheme with argW's committer and prover and the
      test allThere (h.M + 1) in the verifier's place has completeness error at most
      (h.M + 2) · alphaAll. It is full_law (E2E/StringsAllLinks.lean) read as a completeness error.
  laidId_C_of_open, laidId_P_of_open   laidId's committer is laidOpen's followed by the map that
      keeps the commitment ID alone; laidId's prover is laidOpen's followed by the map to a form.
  phiB, phiB_backB, backB_injective   at settings that the reader returns, the map from weights to
      the committed matrix has a left inverse, so it is one-to-one (sec_the,
      Johnson/Goal/Conditions/BindsAtThe.lean).
  modelOutput_unique   at given weights and a given prompt, two outputs of one length that are both
      the model's are equal.

How it fits. See Johnson/FrontRoad/LaidBesideSpec.lean. Not among the release's goal statements.

Limits. Those of Johnson/FrontRoad/LaidBesideSpec.lean.
-/
import Johnson.FrontRoad.LaidBesideSpec

set_option autoImplicit false
set_option maxRecDepth 100000

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt AtPublicFiles.Shown
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## Over the typed oracles, for all parameters -/

section Typed
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)

/-- **All proof strings are present**, read as a completeness error: full_law
(E2E/StringsAllLinks.lean) for the scheme with the test in the verifier's place. -/
theorem produced_typed (hL : LawFit W S h.capT h.capL h.capB) (hW : WiresFit W cA)
    (hs : NeverStops h.st) {PP : Type} (R : ZKCP.Gen.RelPair I X Unit PP) :
    ZKCP.Gen.HasCompletenessError R
      (⟨commitW W S cA h, proveW W cA r₀ h, fun k _ π => .pure (allThere (h.M + 1) k π)⟩ :
        ZKCP.Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit (FullKey lam L aT aL)
          (Isk lam L Bd aT aL) (RequestProof lam L)) 1
      (((h.M + 2 : ℕ) : ℝ≥0∞) * alphaAll W h.capT h.capL h.capB 0 0 0 0 0) := by
  intro i b hb
  show PrFrom (Table.empty _) _ {c | c = false} ≤ _
  match b, hb with
  | [], _ =>
    refine le_of_eq_of_le ?_ (zero_le _)
    refine le_antisymm (PrFrom_bind_le _ _ _ _ fun out _ => ?_) (zero_le _)
    exact le_of_eq (PrFrom_pure _ true _ (by intro h; cases h))
  | [(x, u)], _ =>
    have e : ((commitW W S cA h i).bind fun key =>
        ((coinsP W h).bind fun d => (proveAt W cA r₀ h key.2 x d).bind fun π =>
          (.pure ⟨[π], rfl⟩ : OComp _ (ZKCP.Gen.Slots (RequestProof lam L) [(x, u)]))).bind fun πs =>
            ZKCP.Gen.verifyAll
              (⟨commitW W S cA h, proveW W cA r₀ h, fun k _ π => .pure (allThere (h.M + 1) k π)⟩ :
                ZKCP.Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit (FullKey lam L aT aL)
                  (Isk lam L Bd aT aL) (RequestProof lam L)) key.1
              (([(x, u)].map Prod.fst).zip πs.val)) =
        ((commitW W S cA h i).bind fun key => (coinsP W h).bind fun d =>
          (proveAt W cA r₀ h key.2 x d).bind fun π => .pure (key.1, π)).bind fun y =>
            .pure (allThere (h.M + 1) y.1 y.2 && true) := by
      simp only [OComp.bind_assoc]
      rfl
    show Rom.Pr ((commitW W S cA h i).bind fun key =>
        ((coinsP W h).bind fun d => (proveAt W cA r₀ h key.2 x d).bind fun π =>
          (.pure ⟨[π], rfl⟩ : OComp _ (ZKCP.Gen.Slots (RequestProof lam L) [(x, u)]))).bind fun πs =>
            ZKCP.Gen.verifyAll _ key.1 (([(x, u)].map Prod.fst).zip πs.val))
      (fun _ => {c | c = false}) ≤ _
    rw [e, Pr_bind_pure]
    refine le_trans (PrFrom_mono (Table.empty _) _ (F := {y | ¬ FullTo (h.M + 1) y})
      fun y hy hF => ?_) (full_law W S cA r₀ h hL hW hs i x)
    have h1 : (allThere (h.M + 1) y.1 y.2 && true) = false := hy
    rw [Bool.and_true] at h1
    exact @of_decide_eq_false (FullTo (h.M + 1) (y.1, y.2)) (Classical.dec _) h1 hF
  | _ :: _ :: _, hb => exact absurd hb.1 (by simp)

end Typed

end OnBytes.FrontRoad

namespace OnBytes.FrontRoad
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.Premises AtPublicFiles.ZetaAt AtPublicFiles.LinkLaid
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifierAndGoals (PublicFiles InScope storedPublicFiles)
open FlashProve (homeR homeT backB flashProveDescription allZeroDigest lawFit_home wiresFit_home)

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] FlashProve.theCoding FlashProve.theKeyData FlashProve.theProofData
  FlashProve.protocolDataWellFormed FlashProve.theDeadPlan FlashProve.theKeyGate FlashProve.theProofGate
  FlashProve.theLinkGate FlashProve.theProvers FlashProve.theNamed LPFD.Full.GF LPFD.Full.mOneAt
  PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem
  FlashProve.riDigits FlashProve.fieldRows VerifierAndGoals.storedPublicFiles

variable (b : PublicFiles → ℕ) (Z : PublicFiles) (b₀ : (homeR b Z).LeafBody) (M ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)
  (E : BitsE b Z b₀ M ℓ ℓr capT capL capB) (s : IntegerTransformer.Settings) (x₀ : (homeR b Z).Instance)

/-- At every value d of the public reading, over the typed oracles. -/
theorem produced_at (scope : InScope Z = true) (h1 : ∀ i, 2 ^ 40 ≤ capT i + 1)
    (h2 : ∀ i, 2 ^ 40 ≤ capL i + 1) (h3 : ∀ i, 2 ^ 40 ≤ capB i + 1) {PP : Type}
    (R : ZKCP.Gen.RelPair (homeR b Z).Index (homeR b Z).Instance Unit PP) (d : (homeT b Z).D) :
    ZKCP.Gen.HasCompletenessError R
      (testAt (homeT b Z) (fun _ => (laidAt b Z b₀ M ℓ ℓr capT capL capB E).side)
        (allThere (M + 1)) d) 1 (((M + 2 : ℕ) : ℝ≥0∞) * (71 * (2⁻¹ : ℝ≥0∞) ^ 256)) :=
  fun i l hl =>
    (produced_typed (homeR b Z).queryLayout ((homeT b Z).Sd d) ((homeT b Z).cA d) (homeR b Z).fixedSample
      (laidAt b Z b₀ M ℓ ℓr capT capL capB E).side (lawFit_home b Z d capT capL capB)
      (wiresFit_home b Z d) (neverStops_laid b Z b₀ M ℓ ℓr capT capL capB E) R i l hl).trans
      (mul_le_mul' le_rfl
        (alpha_of_tries (homeR b Z) (tries_home b Z scope) capT capL capB h1 h2 h3))

variable (Form : Type) (parse : VerifierAndGoals.Parser (flashProveDescription.reBound b) Z Form)
  (encF : VerifierAndGoals.TypedProof ((flashProveDescription.reBound b).F Z) ((flashProveDescription.reBound b).P Z) → Form)

/-- laidId's committer is laidOpen's, followed by the map that keeps the commitment ID alone. -/
theorem laidId_C_of_open (w : ModelWeights s) :
    (laidId b Z b₀ M ℓ ℓr capT capL capB E s x₀ Form parse encF).C w =
      ((laidOpen b Z b₀ M ℓ ℓr capT capL capB E s x₀).C w).mapO fun o => (o.1.1, o.2) := by
  unfold laidId laidOpen frontId
  exact frontK_C_of_open (homeT b Z) _ (allThere (M + 1)) (backB b Z s) x₀ (fun id _ => id) _ _ w

/-- laidId's prover is laidOpen's, followed by the map to a form. -/
theorem laidId_P_of_open (isk) (x' : List Token × List Token) :
    (laidId b Z b₀ M ℓ ℓr capT capL capB E s x₀ Form parse encF).P isk x' () =
      ((laidOpen b Z b₀ M ℓ ℓr capT capL capB E s x₀).P isk x' ()).mapO fun π =>
        encF ([], (lowKey isk.1, lowPrf isk.1 π)) := by
  unfold laidId laidOpen frontId
  exact frontK_P_of_open (homeT b Z) _ (allThere (M + 1)) (backB b Z s) x₀ (fun id _ => id)
    (fun k π => encF ([], (lowKey k, lowPrf k π))) _ isk x'

/-- The library's map from a committed matrix back to weights, read at the input homeR b Z. -/
def phiB (s : IntegerTransformer.Settings) (i : (homeR b Z).Index) : Option (ModelWeights s) :=
  FlashProve.phiThe Z s i

/-- At settings that the reader returns it undoes the map from weights to the matrix. -/
theorem phiB_backB (pp : Inst.Model.ScalesAndPolicy) (hr : VerifierAndGoals.readFiles Z = .ok pp)
    (w : ModelWeights (VerifierAndGoals.settingsOfRead pp)) :
    phiB b Z (VerifierAndGoals.settingsOfRead pp) (backB b Z (VerifierAndGoals.settingsOfRead pp) w) = some w :=
  FlashProve.sec_the Z pp hr w

/-- At settings that the reader returns, different weights give different committed matrices. -/
theorem backB_injective (pp : Inst.Model.ScalesAndPolicy) (hr : VerifierAndGoals.readFiles Z = .ok pp) :
    Function.Injective (backB b Z (VerifierAndGoals.settingsOfRead pp)) := fun w w' e =>
  Option.some.inj ((phiB_backB b Z pp hr w).symm.trans
    ((congrArg (phiB b Z (VerifierAndGoals.settingsOfRead pp)) e).trans (phiB_backB b Z pp hr w')))

end OnBytes.FrontRoad

namespace OnBytes.FrontRoad
open VerifiableInference
open VerifierAndGoals (PublicFiles storedPublicFiles)
open FlashProve (homeR backB)

/-- **The proofs of laidId are produced.** Proves Spec.laidProduced. -/
theorem laidProduced : Spec.laidProduced :=
  fun b Z b₀ M ℓ ℓr capT capL capB E s x₀ scope h1 h2 h3 =>
    test_front (FlashProve.homeT b Z) _ (allThere (M + 1)) (backB b Z s) x₀
      (ZKCP.languageRelation fun _ _ => True) (relTaken s) _ (familyLaws_home b Z).noCoin
      (familyLaws_home b Z).asks (familyLaws_home b Z).once (familyLaws_home b Z).spare
      (produced_at b Z b₀ M ℓ ℓr capT capL capB E scope h1 h2 h3 _) fun _ _ _ => trivial

/-- At given weights and a given prompt, two outputs of one length that are both the model's are
equal. -/
theorem modelOutput_unique (s : IntegerTransformer.Settings) (w : ModelWeights s)
    (prompt output output' : List Token) (h : VerifierAndGoals.ModelOutput s w prompt output)
    (h' : VerifierAndGoals.ModelOutput s w prompt output') (hl : output.length = output'.length) :
    output = output' := by
  have key : ∀ n, n ≤ output.length → output.take n = output'.take n := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have hn1 : n < output.length := hn
      have hn2 : n < output'.length := hl ▸ hn1
      have e := ih (Nat.le_of_lt hn1)
      have a := h n hn1
      have c := h' n hn2
      rw [e] at a
      have hEq : output[n] = output'[n] := Option.some.inj (a.symm.trans c)
      rw [List.take_succ_eq_append_getElem hn1, List.take_succ_eq_append_getElem hn2, e, hEq]
  have all := key output.length le_rfl
  rw [List.take_length, hl, List.take_length] at all
  exact all

/-- **At the stored full-size public files' own settings**, with two placeholder provers, which send
fixed messages. Proves Spec.idLaidOwn. -/
theorem idLaidOwn : Spec.idLaidOwn := by
  obtain ⟨-, pp, hr, -⟩ := VerifierAndGoals.filesRead.full
  obtain ⟨w, w', p, o, o', -, h1, -, h2, hl, hne⟩ :=
    VerifierAndGoals.fixedFacts.claim storedPublicFiles pp (Or.inl rfl) hr
  exact ⟨pp, hr,
    fun b b₀ ℓr i₀ x₀ Form parse encF =>
      (idLaidFull b b₀ ℓr i₀ (VerifierAndGoals.settingsOfRead pp) x₀ Form parse encF).1,
    fun b => backB_injective b storedPublicFiles pp hr,
    w, w', fun e => hne (modelOutput_unique _ w p o o' h1 (e ▸ h2) hl)⟩

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.produced_typed
#print axioms OnBytes.FrontRoad.produced_at
#print axioms OnBytes.FrontRoad.laidId_C_of_open
#print axioms OnBytes.FrontRoad.laidId_P_of_open
#print axioms OnBytes.FrontRoad.laidProduced
#print axioms OnBytes.FrontRoad.modelOutput_unique
#print axioms OnBytes.FrontRoad.phiB_backB
#print axioms OnBytes.FrontRoad.backB_injective
#print axioms OnBytes.FrontRoad.idLaidOwn
