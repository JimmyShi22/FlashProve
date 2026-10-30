-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Conditions/KeySoundOfOpenAt.lean: at the closed term VerifierAndGoals.theDescription, WITH THE
KEY FILE's SEAT LAID: keySound_of_open (KeySoundOfOpen.lean) AT ONE Z: the row KeySound's body at
these public files from the three laws of KeyOpenAt at these files. For a top that is stated at one
Z.



Main names.
  KeySoundBodyAt Z: the row KeySound's body at Z: CompilerSoundnessConditionStatements.keySound of the names at the built system
    of Z.
  keySound_iff_bodyAt: KeySound ↔ ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
    KeySoundBodyAt Z: by rfl.
  OpenLawAtZ Z r: OpenLawAt r's body at Z: row r's law at the seat's written terms, under all that
    the seat hands its payer at Z.
  KeyOpenAt Z: THE STRUCTURE AT Z: three fields: r2_9, r2_10, r3_2: OpenLawAtZ Z at these rows.
  keyOpen_iff_at: KeyOpen ↔ ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → KeyOpenAt Z.
  keySoundAt_of_handed: the two lowest layers at one Z: the text of keySound_the_of_seat's proof
    (KeyAtTheRule.lean) and of keySound_of_handed's (KeyAtTheSeat.lean), line for line: both are
    pointwise in Z.
  restAt_of_open | keySoundAt_of_rest: the fields give RestAtSeatW Z; RestAtSeatW Z gives
    KeySoundBodyAt Z, by the layers' own lemmas at one Z.
  keySoundAt_of_open | keySound_at: InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → KeyOpenAt Z →
    KeySoundBodyAt Z; the second with the conclusion written out: the name and the form that the
    top at one Z asks.
  keySound_at_live: the same with «protocolDataWellFormed (asDescriptionFiles Z) = true →» kept in front of the fields and of
    the conclusion.
Object: KeySound's body at one Z. User: a top at one Z. Letters: Z.

Limits. A joining of statements: by itself this file closes nothing. Its theorems take the three
fields of KeyOpenAt Z as a hypothesis, and this file proves none of them at any Z. KeyOpenHolds.lean
proves them at every Z in scope where protocolDataWellFormed says yes (keyOpenAt_holds). That protocolDataWellFormed says yes at
the release's full-size public files is evaluated, not proved. The limits in KeyOpenHolds.lean's
head hold here too. No new mathematics: twins of layers that were pointwise already. Nothing on
soundness.
The statement on codes. The 18 laws that this file's proofs call (LPFD.paidW_in_scope, through
LPFD.off_of_restW) rest on this library's proof of the statement on codes (a bound on the mutual
correlated agreement of Reed-Solomon codes below the Johnson radius; lean/LIMITS.md, L15), at these
places at least: the count of bad fold points at the round "LIN point" (row 2.1), through
Cb.Bridge.foldErr_ix (Johnson/Bridge/FoldErrIx.lean), and the first chain's proximity test (row
1.15), through Cb.Gl.bchks46At (Cb/Bridge/GlCodesProved.lean). That proof rests on files under
ThirdParty/ adapted from ArkLib and Mathlib
(L15). None of this appears as a hypothesis in this file's statements.

-/
import Johnson.Goal.Conditions.KeySoundOfOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi FirstState)
open Johnson.RunOne.KeyRows23 (Fk oneAt atSix inFront₂ Cl₂ Cl₃)

/-- **The row KeySound's body at one Z.** -/
def KeySoundBodyAt (Z : PublicFiles) : Prop :=
  CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0))

/-- **It is the row's body: by definition.** -/
theorem keySound_iff_bodyAt :
    KeySound ↔ ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → KeySoundBodyAt Z := Iff.rfl

/-- **Row r's law at the seat's written terms, at one Z.** -/
def OpenLawAtZ (Z : PublicFiles) (r : LPFD.Row) : Prop :=
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

/-- **It is OpenLawAt's body: by definition.** -/
theorem openLaw_iff_at (r : LPFD.Row) :
    OpenLawAt r ↔ ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → OpenLawAtZ Z r := Iff.rfl

/-- **The three laws that keySound_at takes as a hypothesis at one Z, by name.** keyOpenAt_holds
(KeyOpenHolds.lean) proves them at every Z in scope where protocolDataWellFormed says yes. -/
structure KeyOpenAt (Z : PublicFiles) : Prop where
  /-- the shared chain's proximity test on G_u -/
  r2_9 : OpenLawAtZ Z .r2_9
  /-- the shared chain's proximity test on G_omega -/
  r2_10 : OpenLawAtZ Z .r2_10
  /-- the last chain's proximity test on the own group -/
  r3_2 : OpenLawAtZ Z .r3_2

theorem keyOpen_iff_at :
    KeyOpen ↔ ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → KeyOpenAt Z :=
  ⟨fun h Z hs hl => ⟨h.r2_9 Z hs hl, h.r2_10 Z hs hl, h.r3_2 Z hs hl⟩,
    fun h => ⟨fun Z hs hl => (h Z hs hl).r2_9, fun Z hs hl => (h Z hs hl).r2_10,
      fun Z hs hl => (h Z hs hl).r3_2⟩⟩

/-- **The two lowest layers at one Z**: keySound_the_of_seat's and keySound_of_handed's proofs, line
for line. -/
theorem keySoundAt_of_handed (Z : PublicFiles) (hs : InScope Z = true) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (the21 : The21HandedAtSeat Z) : KeySoundBodyAt Z := by
  obtain ⟨X₀, m, X', N', P', hX₀, hm, hF, hp, hw, ho, ha, hD, h9⟩ := kseat_name Z hl
  have hG := (g_built_live Z hl).trans (thePlan_of_made hX₀ hm)
  have er := runK_the_at Z _ h9
  have hd := depthReqT_the Z hl theC0 theM0
  have hε := ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0).hε
  obtain ⟨m', X, N, P, hm', hX, hN, hP, e⟩ := descAt_made X₀ Z.lay fixedDigest _ hF
  obtain rfl : m' = m := Except.ok.inj (hm'.symm.trans hm)
  rw [e] at hp hw ho ha hD er
  rw [← dk_the Z hl] at hD
  have base := LPFD.keyDebtCap_of_letters (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E X N P
    (dataAtFiles flashProveData Z).DK hD
    (LPFD.letters_of_handed _ _ _ hs (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO hX₀) hm hX hp
      (the21 X₀ m' X N P hX₀ hm hX hN hP hD hp hw ho ha hG))
  exact LPFD.keySound_of_debt (descriptionFromSource X N P) keyInstanceOfOutOfDomainSample (dataAtFiles flashProveData Z).A (dataAtFiles flashProveData Z).E
    (dataAtFiles flashProveData Z).DK _ "key file"
    (LPFD.keyDebt_of_cap _ keyInstanceOfOutOfDomainSample _ _ _ _ hε "key file"
      (VerifiableInference.Desc.Sound.sealLast_of_planOk _ hp) base)
    hl er ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0) hd rfl

/-- **RestAtSeatW Z gives KeySound's body at Z**: the layers' own lemmas, at one Z. -/
theorem keySoundAt_of_rest (Z : PublicFiles) (hs : InScope Z = true) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (rest : RestAtSeatW Z) : KeySoundBodyAt Z :=
  keySoundAt_of_handed Z hs hl <| handedAtSeat_of_base Z <| atSeat_of_name Z <|
    atName_of_pin Z hs fun X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG =>
      ⟨pin_at_seat Z hs hl, last_of_tab_at_seat Z hs
        (fun X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG =>
          LPFD.tab_of_off (LPFD.off_of_restW _ hs
            (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO hX₀) hm hX hp hN hw hD
            (pin_at_seat Z hs hl) (rest X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG)))
        X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG⟩

/-- **The three fields at Z give RestAtSeatW Z.** -/
theorem restAt_of_open (Z : PublicFiles) (h : KeyOpenAt Z) : RestAtSeatW Z :=
  fun X₀ m X N P e₁ e₂ e₃ e₄ e₅ hD hp hw ho ha hG c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw q₁ q₂ q₃ hk hsw hin =>
    ⟨seat_inhabitant X N P (dataAtFiles flashProveData Z).DK, fun r hr => by
      cases r
      case r2_9 =>
        exact h.r2_9 X₀ m X N P e₁ e₂ e₃ e₄ e₅ hD hp hw ho ha hG c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw
          q₁ q₂ q₃ hk hsw hin
      case r2_10 =>
        exact h.r2_10 X₀ m X N P e₁ e₂ e₃ e₄ e₅ hD hp hw ho ha hG c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw
          q₁ q₂ q₃ hk hsw hin
      case r3_2 =>
        exact h.r3_2 X₀ m X N P e₁ e₂ e₃ e₄ e₅ hD hp hw ho ha hG c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw
          q₁ q₂ q₃ hk hsw hin
      all_goals exact absurd (by decide) hr⟩

/-- **KeySound's body at Z from the three laws of KeyOpenAt Z, by name, and from nothing else.** -/
theorem keySoundAt_of_open (Z : PublicFiles) (hs : InScope Z = true) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (h : KeyOpenAt Z) : KeySoundBodyAt Z :=
  keySoundAt_of_rest Z hs hl (restAt_of_open Z h)

/-- **THE SAME UNDER THE NAME AND IN THE FORM THAT THE TOP AT ONE Z ASKS**: the conclusion is the
row KeySound's own body at Z, written out. -/
theorem keySound_at (Z : PublicFiles) (hs : InScope Z = true) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (h : KeyOpenAt Z) : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0)) :=
  keySoundAt_of_open Z hs hl h

/-- **THE SAME WITH «protocolDataWellFormed says yes» KEPT IN FRONT OF BOTH SIDES**: the form of the hypothesis on
the key file in the top at one Z (its own KeySoundAt Z,
Johnson/Goal/Skeleton/TopAtZ.lean, which this file does not import: the term is written out). -/
theorem keySound_at_live (Z : PublicFiles) (hs : InScope Z = true)
    (h : protocolDataWellFormed (asDescriptionFiles Z) = true → KeyOpenAt Z) :
    protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0)) :=
  fun hl => keySound_at Z hs hl (h hl)

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.keySound_iff_bodyAt
#print axioms VerifierAndGoals.AtTheName.openLaw_iff_at
#print axioms VerifierAndGoals.AtTheName.keyOpen_iff_at
#print axioms VerifierAndGoals.AtTheName.keySoundAt_of_handed
#print axioms VerifierAndGoals.AtTheName.keySoundAt_of_rest
#print axioms VerifierAndGoals.AtTheName.restAt_of_open
#print axioms VerifierAndGoals.AtTheName.keySoundAt_of_open
#print axioms VerifierAndGoals.AtTheName.keySound_at
#print axioms VerifierAndGoals.AtTheName.keySound_at_live
