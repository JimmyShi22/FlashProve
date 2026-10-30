-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Conditions/KeySoundOfOpen.lean: at the closed term VerifierAndGoals.theDescription, with the key
file's seat laid: the row KeySound from the laws of three rows, by name (2.9, 2.10, 3.2), and from
nothing else. KeyOpenHolds.lean proves these three (keyOpen_holds).
keySound_at_written (KeyAtTheSeatWritten.lean) with its one premise
spelled as a structure: one field a row.

Main names.
  OpenLawAt r: row r's law (LPFD.lawAt, Johnson/Top/Fire/Code/TheRest.lean) at the seat's written
    terms (the tenth road's: LPFD.encN X P, LPFD.radN among them), for every Z in scope at which
    protocolDataWellFormed says yes, UNDER ALL THAT THE SEAT HANDS ITS PAYER: RestAtSeatW's eleven facts and
    RestOffW's letters and six facts, to the sign.
  KeyOpen: THE STRUCTURE: three fields: r2_9, r2_10, r3_2: OpenLawAt at these rows.
  openLaw_29 | openLaw_210 | openLaw_32: what the three fields say, written out: KeepsAt of the
    woven promise On₂' (at 9, at 10) or On₃' (at 2), of the claims' relation and of the maker's
    row of that chain: by rfl.
  keySound_of_open: KeyOpen → KeySound.
  keyOpen_of_rest: the way back: keySound_at_written's premise gives KeyOpen: so the structure asks
    no more than that premise did.
  seat_inhabitant: the one inhabitant that RestOffW binds beside the laws (an instance, a first
    chain's state and oracles) IS THERE: written out: so it is no field.
Object: KeySound. User: the top's hypothesis on the key file. Letters: none.

Limits. A joining of statements: by itself this file closes nothing. keySound_of_open takes the
three fields of KeyOpen as a hypothesis, and this file proves none of them. KeyOpenHolds.lean proves
them (keyOpen_holds); the limits in its head hold here too. The eighteen rows that are no field are
laid in by theorems of other files of this library (KeyAtWritten.lean's head). A law is guarded by
its border's whole promise and speaks only where its piece says yes: the examples of such statements
that are known, evaluated and not proved, are described in KeyOpenHolds.lean's head. Nothing on
soundness.

-/
import Johnson.Goal.Conditions.KeyAtTheSeatWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi FirstState)
open Johnson.RunOne.KeyRows23 (Fk oneAt atSix inFront₂ Cl₂ Cl₃)

/-- **Row r's law at the seat's written terms, under all that the seat hands its payer.** -/
def OpenLawAt (r : LPFD.Row) : Prop :=
  ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
  ∀ (X₀ : OnBytes.Model.Verify.Public) (m : Johnson.G.OfPlan.Made) (X : Source) (N : H2U.PlaceNums)
    (P : LaterPlaces),
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ →
    madeAt X₀ Z.lay fixedDigest = .ok m → sourceOf m = .ok X → rangesNumbers m = .ok N →
    laterPlaces m = .ok P →
    (descriptionFromSource X N P).data "key file" = .ok ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) →
    (descriptionFromSource X N P).planOk = true → (descriptionFromSource X N P).wantedOk = true → (descriptionFromSource X N P).owedOk = true →
    (∀ t ∈ Key.lawsAsk X₀ Z.lay m (descriptionFromSource X N P) (theKeyData (asDescriptionFiles Z)), t.2 = true) →
    (dataAtFiles flashProveData Z).G = bigReq m.p →
    ∀ (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
      (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl) (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl))
      (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
      (x₀ x₁ : Lookup) (bw : Block FirstState Key.Claim),
    (Fk X N P).first.blocksInOrder = c₁ :: k₁ → (Fk X N P).shared.blocksInOrder = c₂ :: k₂ →
    (Fk X N P).second.blocksInOrder = c₃ :: k₃ →
    lookupsOf (oneAt X) = [x₀, x₁] →
    sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1))
        (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw →
    (inFront₂ X P).length = 10 →
    LPFD.lawAt X N P (dataAtFiles flashProveData Z).DK c₁ k₁ c₂ k₂ c₃ k₃ LPFD.capRest LPFD.capRest LPFD.capRest
      () ()
      (LPFD.baseAt X LPFD.decN LPFD.recBack) atSix (LPFD.readAt LPFD.tabN) (LPFD.encN X P) LPFD.radN
      LPFD.collN LPFD.off₂N LPFD.off₃N r

/-- **The three laws that keySound_of_open takes as a hypothesis, by name.** keyOpen_holds
(KeyOpenHolds.lean) proves them. -/
structure KeyOpen : Prop where
  /-- the shared chain's proximity test on G_u -/
  r2_9 : OpenLawAt .r2_9
  /-- the shared chain's proximity test on G_omega -/
  r2_10 : OpenLawAt .r2_10
  /-- the last chain's proximity test on the own group -/
  r3_2 : OpenLawAt .r3_2

/-- **The first field, written out.** -/
theorem openLaw_29 : OpenLawAt .r2_9 ↔
    ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
  ∀ (X₀ : OnBytes.Model.Verify.Public) (m : Johnson.G.OfPlan.Made) (X : Source) (N : H2U.PlaceNums)
    (P : LaterPlaces),
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ →
    madeAt X₀ Z.lay fixedDigest = .ok m → sourceOf m = .ok X → rangesNumbers m = .ok N →
    laterPlaces m = .ok P →
    (descriptionFromSource X N P).data "key file" = .ok ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) →
    (descriptionFromSource X N P).planOk = true → (descriptionFromSource X N P).wantedOk = true → (descriptionFromSource X N P).owedOk = true →
    (∀ t ∈ Key.lawsAsk X₀ Z.lay m (descriptionFromSource X N P) (theKeyData (asDescriptionFiles Z)), t.2 = true) →
    (dataAtFiles flashProveData Z).G = bigReq m.p →
    ∀ (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
      (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl) (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl))
      (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
      (x₀ x₁ : Lookup) (bw : Block FirstState Key.Claim),
    (Fk X N P).first.blocksInOrder = c₁ :: k₁ → (Fk X N P).shared.blocksInOrder = c₂ :: k₂ →
    (Fk X N P).second.blocksInOrder = c₃ :: k₃ →
    lookupsOf (oneAt X) = [x₀, x₁] →
    sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1))
        (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw →
    (inFront₂ X P).length = 10 →
    LPFD.KeepsAt
      (LPFD.On₂' X N P ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (LPFD.baseAt X LPFD.decN LPFD.recBack)
        atSix
        (LPFD.readAt LPFD.tabN) (LPFD.encN X P) LPFD.radN LPFD.collN LPFD.off₂N)
      (Cl₂ X N P ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (LPFD.baseAt X LPFD.decN LPFD.recBack) atSix
        (LPFD.readAt LPFD.tabN) (LPFD.encN X P) LPFD.radN)
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a)
          c₁ k₁ c₂ k₂ c₃ k₃ LPFD.capRest LPFD.capRest LPFD.capRest () ())).p₂ ::
        (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a)
          c₁ k₁ c₂ k₂ c₃ k₃ LPFD.capRest LPFD.capRest LPFD.capRest () ())).l₂) 9 := Iff.rfl

/-- **The second field, written out.** -/
theorem openLaw_210 : OpenLawAt .r2_10 ↔
    ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
  ∀ (X₀ : OnBytes.Model.Verify.Public) (m : Johnson.G.OfPlan.Made) (X : Source) (N : H2U.PlaceNums)
    (P : LaterPlaces),
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ →
    madeAt X₀ Z.lay fixedDigest = .ok m → sourceOf m = .ok X → rangesNumbers m = .ok N →
    laterPlaces m = .ok P →
    (descriptionFromSource X N P).data "key file" = .ok ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) →
    (descriptionFromSource X N P).planOk = true → (descriptionFromSource X N P).wantedOk = true → (descriptionFromSource X N P).owedOk = true →
    (∀ t ∈ Key.lawsAsk X₀ Z.lay m (descriptionFromSource X N P) (theKeyData (asDescriptionFiles Z)), t.2 = true) →
    (dataAtFiles flashProveData Z).G = bigReq m.p →
    ∀ (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
      (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl) (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl))
      (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
      (x₀ x₁ : Lookup) (bw : Block FirstState Key.Claim),
    (Fk X N P).first.blocksInOrder = c₁ :: k₁ → (Fk X N P).shared.blocksInOrder = c₂ :: k₂ →
    (Fk X N P).second.blocksInOrder = c₃ :: k₃ →
    lookupsOf (oneAt X) = [x₀, x₁] →
    sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1))
        (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw →
    (inFront₂ X P).length = 10 →
    LPFD.KeepsAt
      (LPFD.On₂' X N P ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (LPFD.baseAt X LPFD.decN LPFD.recBack)
        atSix
        (LPFD.readAt LPFD.tabN) (LPFD.encN X P) LPFD.radN LPFD.collN LPFD.off₂N)
      (Cl₂ X N P ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (LPFD.baseAt X LPFD.decN LPFD.recBack) atSix
        (LPFD.readAt LPFD.tabN) (LPFD.encN X P) LPFD.radN)
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a)
          c₁ k₁ c₂ k₂ c₃ k₃ LPFD.capRest LPFD.capRest LPFD.capRest () ())).p₂ ::
        (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a)
          c₁ k₁ c₂ k₂ c₃ k₃ LPFD.capRest LPFD.capRest LPFD.capRest () ())).l₂) 10 := Iff.rfl

/-- **The third field, written out.** -/
theorem openLaw_32 : OpenLawAt .r3_2 ↔
    ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
  ∀ (X₀ : OnBytes.Model.Verify.Public) (m : Johnson.G.OfPlan.Made) (X : Source) (N : H2U.PlaceNums)
    (P : LaterPlaces),
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ →
    madeAt X₀ Z.lay fixedDigest = .ok m → sourceOf m = .ok X → rangesNumbers m = .ok N →
    laterPlaces m = .ok P →
    (descriptionFromSource X N P).data "key file" = .ok ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) →
    (descriptionFromSource X N P).planOk = true → (descriptionFromSource X N P).wantedOk = true → (descriptionFromSource X N P).owedOk = true →
    (∀ t ∈ Key.lawsAsk X₀ Z.lay m (descriptionFromSource X N P) (theKeyData (asDescriptionFiles Z)), t.2 = true) →
    (dataAtFiles flashProveData Z).G = bigReq m.p →
    ∀ (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
      (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl) (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl))
      (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
      (x₀ x₁ : Lookup) (bw : Block FirstState Key.Claim),
    (Fk X N P).first.blocksInOrder = c₁ :: k₁ → (Fk X N P).shared.blocksInOrder = c₂ :: k₂ →
    (Fk X N P).second.blocksInOrder = c₃ :: k₃ →
    lookupsOf (oneAt X) = [x₀, x₁] →
    sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1))
        (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw →
    (inFront₂ X P).length = 10 →
    LPFD.KeepsAt
      (LPFD.On₃' X N P ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (LPFD.baseAt X LPFD.decN LPFD.recBack)
        atSix
        (LPFD.readAt LPFD.tabN) LPFD.collN LPFD.off₂N LPFD.off₃N)
      (Cl₃ X N P ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (LPFD.baseAt X LPFD.decN LPFD.recBack) atSix
        (LPFD.readAt LPFD.tabN))
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a)
          c₁ k₁ c₂ k₂ c₃ k₃ LPFD.capRest LPFD.capRest LPFD.capRest () ())).p₃ ::
        (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a)
          c₁ k₁ c₂ k₂ c₃ k₃ LPFD.capRest LPFD.capRest LPFD.capRest () ())).l₃) 2 := Iff.rfl

/-- **The inhabitant that RestOffW binds beside the laws is there.** -/
def seat_inhabitant (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD) :
    ((Fk X N P).XiPub × (Fk X N P).S₁) × (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str :=
  (((⟨default⟩ : Xi), (Fk X N P).start₁ (⟨default⟩ : Xi)),
    (honestTab frS (fun _ => []) (fun _ => []), fun _ => []))

/-- **The row KeySound from the three laws of KeyOpen, by name, and from nothing else.** -/
theorem keySound_of_open (h : KeyOpen) : KeySound :=
  keySound_at_written fun Z hs hl X₀ m X N P e₁ e₂ e₃ e₄ e₅ hD hp hw ho ha hG c₁ k₁ c₂ k₂ c₃ k₃ x₀
      x₁ bw q₁ q₂ q₃ hk hsw hin =>
    ⟨seat_inhabitant X N P (dataAtFiles flashProveData Z).DK, fun r hr => by
      cases r
      case r2_9 =>
        exact h.r2_9 Z hs hl X₀ m X N P e₁ e₂ e₃ e₄ e₅ hD hp hw ho ha hG c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw
          q₁ q₂ q₃ hk hsw hin
      case r2_10 =>
        exact h.r2_10 Z hs hl X₀ m X N P e₁ e₂ e₃ e₄ e₅ hD hp hw ho ha hG c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw
          q₁ q₂ q₃ hk hsw hin
      case r3_2 =>
        exact h.r3_2 Z hs hl X₀ m X N P e₁ e₂ e₃ e₄ e₅ hD hp hw ho ha hG c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw
          q₁ q₂ q₃ hk hsw hin
      all_goals exact absurd (by decide) hr⟩

/-- **THE WAY BACK: THE STRUCTURE ASKS NO MORE THAN keySound_at_written's PREMISE DID.** -/
theorem keyOpen_of_rest
    (rest : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → RestAtSeatW Z) : KeyOpen :=
  have key : ∀ r, r ∉ LPFD.paidW → OpenLawAt r :=
    fun r hr Z hs hl X₀ m X N P e₁ e₂ e₃ e₄ e₅ hD hp hw ho ha hG c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw q₁ q₂ q₃
        hk hsw hin =>
      match rest Z hs hl X₀ m X N P e₁ e₂ e₃ e₄ e₅ hD hp hw ho ha hG c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw q₁ q₂
        q₃ hk hsw hin with
      | ⟨_, H⟩ => H r hr
  ⟨key _ (by decide), key _ (by decide), key _ (by decide)⟩

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.openLaw_29
#print axioms VerifierAndGoals.AtTheName.openLaw_210
#print axioms VerifierAndGoals.AtTheName.openLaw_32
#print axioms VerifierAndGoals.AtTheName.keySound_of_open
#print axioms VerifierAndGoals.AtTheName.keyOpen_of_rest
