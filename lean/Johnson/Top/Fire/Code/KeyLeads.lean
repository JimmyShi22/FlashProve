-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyLeads.lean, general in the instance's type (`KeyLeadsOn instK S …` · `keySound_on_leads instK S …`): at the full size: ON THE PLAIN ROAD: THE KEY FILE's FRAME's DOOR FOR THE RULE's OWN COIN: the debt said in `EachLeads` · `Glues` · «tie» AT ANY PLACES, at the cap, over a set of descriptions; the form in rows (`KeyDebtCap`: `EachKeeps` at tables of promises and claims) IS A COROLLARY.

Why. On this road this folder's files hold the key file's frame, and the files that hold the description's texts are to pay `EachLeads` at their seats INTO that frame. The frame's owed statement (`KeyOwedAtD`, KeyAtFkD.lean) stands in one coin alone: rows of promises and claims with `Keeps`. The rule beneath (`keySound_plain_of_F`, KeyPlain.lean) reads `EachLeads` at ANY
places Pl and ANY M · L₁ · L₂: so the door is cut there.
Main names.
  `KeyLeadsCap F instK A E rK DK file`: THERE ARE a type of witnesses, the chains' heads, the pieces' letters, places Pl, M · L₁ · L₂ and a statement WITH: data · three heads · `EachLeads` thrice · `Glues` (along the records: at `F.pull instK`) · «tie» (at the key's record rK of the frame; the whole last test is handed to the payer there, BUT M SEES THE FIRST CHAIN's END ALONE: what the last test says of the other two chains' ends meets nothing in M) · the pieces' errors are the cap, thrice.
  `keySound_of_leadsCap`: it, with the seal's test, gives `CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize Tl)` at every record Tl over that rK with `runK = gatedFileDecision b (F.pull instK).run`, b = true, one leaf, 2^-128 ≤ `Tl.εs`: the three equations of shapes by `shapesOfData` (Johnson/Flat/PlainOfData.lean), the three bounds by `below_atCap₁ | ₂ | ₃` (Johnson/Desc/Sound/BoundsAtCap.lean).
  `keyLeadsCap_of_debtCap`: THE ROWS' FORM PAYS IT, at every rK.
  `KeyLeadsOn S A E rK` · `keyLeadsOn_mono` · `keyLeadsOn_of_cap` · `keySound_on_leads`: over a set of descriptions, the payer holding «F is of S» and `F.planOk = true`.
  (At the key file's own maker, in the goals' scope: `KeyLeadsOwedAtD`, KeyAtFkD.lean.)
Limits. A JOINING AND DEFINITIONS: NOTHING IS PAID; no member is known. rK is a letter of the owed statement: «tie» speaks of the frame's silent rounds at that record; a payer that reads neither pays at every rK. The limits of KeyPlain.lean's | KeyDebtCap.lean's heads.

-/
import Johnson.Top.Fire.Code.KeyDebtCap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace LPFD
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

/-- **The key file's debt in the rule's own coin, at the cap.** -/
def KeyLeadsCap {XiK : Type} (F : FileDescription XiK) (instK : RecFull → XiK)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (rK : RecFull) (DK : WholeD) (file : String) : Prop :=
  ∃ (W : Type)
    (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
    (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₃ F.lastChainFirstTreeNumber)
      ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (dW wEnd : W)
    (Pl : PPlaces (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂) ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
    (M : RecFull × (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str → (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop)
    (L₁ : (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop)
    (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop)
    (_ : (F.XiPub × F.S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str),
    F.data file = .ok (DK.at frS.P.T.a) ∧
    F.first.blocksInOrder = c₁ :: k₁ ∧ F.shared.blocksInOrder = c₂ :: k₂ ∧ F.second.blocksInOrder = c₃ :: k₃ ∧
    EachLeads Pl.on₁ Pl.Q₁ 0 ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) ∧
    EachLeads Pl.on₂ Pl.Q₂ 0 ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂) ∧
    EachLeads Pl.on₃ Pl.Q₃ 0 ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃) ∧
    Glues (atDesc (F.pull instK) (piecesAt (ckP .two) (F.pull instK) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)) Pl M L₁ L₂ ∧
    (∀ rec (y : (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str) (τ : Tr (chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty).sh) (s₁ : F.S₁) (s₂ : F.S₂) (s₃ : F.S₃)
      (z : (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str),
      F.okStart (instK rec) = true →
      silK rec ((chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty).msgF τ).2 ((chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty).msgJ τ).2 ((chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty).msg3 τ).2 = true →
      F.fin (instK rec) s₁ s₂ s₃ = true →
      (Pl.on₁ 0 ((atDesc F (piecesAt (ckP .two) F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).in₁ (instK rec), (y, fun _ => [])) → M (rec, y) ((F.pub (instK rec), s₁), z)) →
      (lettersAt A (relationsAndEncodingOfClaims A E)).conf.coll y rec.1 ∨ (lettersAt A (relationsAndEncodingOfClaims A E)).conf.D y rec ≠ none) ∧
    AtCap rest₁ ∧ AtCap rest₂ ∧ AtCap rest₃

set_option maxHeartbeats 4000000 in
/-- **It gives the key file's hypothesis.** -/
theorem keySound_of_leadsCap {XiK : Type} (F : FileDescription XiK) (instK : RecFull → XiK)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD) (file : String) (sealed : F.sealLast = true)
    {DP : WholeD} {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {runP : Xr × RecFull → PQ.View → PQ.View → PQ.View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ} {early : Xr → Xr} {salt K : ℕ}
    {b : Bool} (hb : b = true) (er : runK = gatedFileDecision b (F.pull instK).run)
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (h : KeyLeadsCap F instK A E rK DK file)
    (hd : Tl.depthReqT = 0) (hε : (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ Tl.εs) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize Tl) := by
  obtain ⟨W, c₁, k₁, c₂, k₂, c₃, k₃, rest₁, rest₂, rest₃, dW, wEnd, Pl, M, L₁, L₂, dS, data, q₁, q₂, q₃, e₁, e₂, e₃, G, tie, a₁, a₂, a₃⟩ := h
  obtain ⟨h₁, h₂, h₃⟩ := shapesOfData (ckP .two) F file (DK.at frS.P.T.a) data sealed c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ rest₁ rest₂ rest₃ dW wEnd
  exact keySound_plain_of_F F instK A E DK file c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd Pl h₁ h₂ h₃ M L₁ L₂ Tl.εs dS hb er Tl
    ⟨data, sealed, q₁, q₂, q₃, e₁, e₂, e₃, G, tie,
      below_atCap₁ F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd Tl.εs hε a₁ h₁,
      below_atCap₂ F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd Tl.εs hε a₂ h₂,
      by rw [hd]; simp,
      below_atCap₃ F (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd Tl.εs hε a₃ h₃⟩

/-- **The rows' form pays it**, at every record of the key. -/
theorem keyLeadsCap_of_debtCap {XiK : Type} (F : FileDescription XiK) (instK : RecFull → XiK)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (rK : RecFull) (DK : WholeD) (file : String)
    (h : KeyDebtCap F instK A E DK file) : KeyLeadsCap F instK A E rK DK file := by
  obtain ⟨W, c₁, k₁, c₂, k₂, c₃, k₃, rest₁, rest₂, rest₃, dW, wEnd, dS, on₁, L₁, on₂, L₂, on₃, L₃, data, q₁, q₂, q₃, rows, a₁, a₂, a₃⟩ := h
  exact ⟨W, c₁, k₁, c₂, k₂, c₃, k₃, rest₁, rest₂, rest₃, dW, wEnd, plRows F DK on₁ L₁ on₂ L₂ on₃ L₃, mRows F instK DK L₁, l₁Rows F DK L₂, l₂Rows F DK L₃, dS,
    data, q₁, q₂, q₃, EachKeeps.leads _ 0 rows.keeps₁, EachKeeps.leads _ 0 rows.keeps₂, EachKeeps.leads _ 0 rows.keeps₃,
    glues_of_rows rows,
    fun rec y _ s₁ _ _ z hok _ _ h => tie_of_rows rows rec y ((F.pub (instK rec), s₁), z) hok h,
    a₁, a₂, a₃⟩

/-- **The debt in the rule's own coin, over a set of descriptions.** -/
def KeyLeadsOn {XiK : Type} (instK : RecFull → XiK) (S : FileDescription XiK → Prop)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (rK : RecFull) : Prop :=
  ∀ (F : FileDescription XiK) (DK : WholeD),
    S F → F.data "key file" = .ok (DK.at frS.P.T.a) → F.planOk = true →
    KeyLeadsCap F instK A E rK DK "key file"

theorem keyLeadsOn_mono {XiK : Type} {instK : RecFull → XiK} {S S' : FileDescription XiK → Prop} (hS : ∀ F, S F → S' F)
    {Xr : Type} {A : (frS.toDecR frZ 402653181).Claims Xr} {E : Coding A} {rK : RecFull} (h : KeyLeadsOn instK S' A E rK) : KeyLeadsOn instK S A E rK :=
  fun F DK s => h F DK (hS F s)

/-- The rows' form over the set pays it, at every record of the key. -/
theorem keyLeadsOn_of_cap {XiK : Type} (instK : RecFull → XiK) (S : FileDescription XiK → Prop)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (rK : RecFull) (h : KeyCapOn instK S A E) : KeyLeadsOn instK S A E rK :=
  fun F DK hs hD hp => keyLeadsCap_of_debtCap F instK A E rK DK "key file" (h F DK hs hD hp)

set_option maxHeartbeats 4000000 in
/-- From it: the key file's hypothesis at every description of the set. -/
theorem keySound_on_leads {XiK : Type} (instK : RecFull → XiK) (S : FileDescription XiK → Prop)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A)
    (F : FileDescription XiK) (DK : WholeD)
    (hs : S F) (hD : F.data "key file" = .ok (DK.at frS.P.T.a))
    {DP : WholeD} {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {runP : Xr × RecFull → PQ.View → PQ.View → PQ.View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
    {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ} {early : Xr → Xr} {salt K : ℕ}
    {b : Bool} (er : runK = gatedFileDecision b (F.pull instK).run)
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
    (Tl : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (h : KeyLeadsOn instK S A E rK)
    (hd : Tl.depthReqT = 0) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize Tl) := by
  cases b with
  | false =>
    subst er
    exact keySoundOfFullD_of_never (fun _ _ _ _ => rfl) Tl
  | true =>
    exact keySoundOfFullD_of_planOk (F.pull instK) true er Tl fun hp =>
      keySound_of_leadsCap F instK A E DK "key file" (Sound.sealLast_of_planOk F hp) rfl er Tl (h F DK hs hD hp) hd Tl.hε

end LPFD

#print axioms LPFD.KeyLeadsCap
#print axioms LPFD.keySound_of_leadsCap
#print axioms LPFD.keyLeadsCap_of_debtCap
#print axioms LPFD.KeyLeadsOn
#print axioms LPFD.keyLeadsOn_mono
#print axioms LPFD.keyLeadsOn_of_cap
#print axioms LPFD.keySound_on_leads
