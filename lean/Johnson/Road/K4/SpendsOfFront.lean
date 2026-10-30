-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SpendsOfFront.lean: WHAT K4's SHARE OF THE BRIDGE SPENDS AT ITS TWENTY-FOUR BORDERS
(K4Spends; the premise Sp of k04_law_R, Johnson/Road/K4/K04LawR.lean) FOLLOWS FROM WHAT HOLDS AT THE
TWELVE BORDERS IN FRONT OF K4's SUB-PROTOCOL: fifteen facts, one test on the index masks' ledger and
one on the approximate range proof's parameters, each at the states reached there.

  `wide_rest`: the fifteen facts (WideFacts, Johnson/Desc/Sound/MgWideFacts.lean) ride past an
    accept of K4's: each reads only what Rest keeps (Johnson/Desc/First/K4/ReadsAtS.lean).
  `spends_of_front`: at one group g: K4Spends at 28 g + 4 and at 28 g + 4 + 1.
  `sp_of_front`: at all twelve: Sp, to the letter.
No new argument: kept_rchAt, hK_at_k4 (Johnson/Road/K4/K8OpenAtK4.lean); hR_at_k4
(Johnson/Road/K4/RoomAtK4.lean).
Limits. PREMISES of spends_of_front beside the goals' scope and an opening (hS, hR, O), NONE PAID
HERE, each at every state without a mark that is reached at 28 g + 4:
  W0: the fifteen facts · R0: roomIsB at the segment's own number · L7: lay7B at the segment's
  parameters.
THAT THERE IS AN OPENING IS SHOWN BY NO THEOREM. NO MEMBER IS SHOWN. What K4Spends serves speaks at
a wider meaning and counts only when the bridge from it to the composed meaning
is paid: this is a part of that bridge's price. K04_law, the law of K4's
sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.K04LawR
import Johnson.Road.K4.RoomAtK4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Rest)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S LayOwn weightsB weightsB_same)
open VerifiableInference.Desc.First.K8.Ready (lay7B)
open VerifiableInference.Desc.Sound (MgData WideData WideFacts)
open Johnson.Desc.First.Walk.Tied (RchAt roomIsB)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  {Dm : MgData Xi P Tok rows cols nR X} {E : WideData P}

/-- **The fifteen facts ride past an accept of K4's.** -/
theorem wide_rest {z : P} {s s' : S} (R : Rest s s') {a₀ : LayOwn} (ha : s.here = .lay a₀)
    (W : WideFacts Dm E (z, s)) : WideFacts Dm E (z, s') := by
  obtain ⟨a', ha', _⟩ := R.here a₀ ha
  have hrows : s'.rows = s.rows := by
    simp only [S.rows, ha, ha', R.out]
  have hlive : s'.live = s.live := by
    unfold S.live
    rw [R.link, R.check]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : VerifiableInference.Desc.K12.Door.atFirstBook E.d12.ft s = true := W.bookInOrder
    show VerifiableInference.Desc.K12.Door.atFirstBook E.d12.ft s' = true
    unfold VerifiableInference.Desc.K12.Door.atFirstBook at h ⊢
    rw [R.book, R.roots]
    exact h
  · have h : VerifiableInference.Desc.K12.Door.atFirstSeats E.d12.L s = true := W.seatsCarried
    show VerifiableInference.Desc.K12.Door.atFirstSeats E.d12.L s' = true
    unfold VerifiableInference.Desc.K12.Door.atFirstSeats at h ⊢
    rw [R.book]
    exact h
  · have h : VerifiableInference.Desc.K12.Door.atFirstFits s = true := W.bookFits
    show VerifiableInference.Desc.K12.Door.atFirstFits s' = true
    unfold VerifiableInference.Desc.K12.Door.atFirstFits at h ⊢
    rw [R.book]
    exact h
  · have h : VerifiableInference.Desc.K12.Door.atFirstShapes E.d12.M s = true := W.msgShapes
    show VerifiableInference.Desc.K12.Door.atFirstShapes E.d12.M s' = true
    unfold VerifiableInference.Desc.K12.Door.atFirstShapes at h ⊢
    rw [R.st]
    exact h
  · have h : weightsB s = true := W.weightsOk
    show weightsB s' = true
    rw [weightsB_same hrows]
    exact h
  · have h : VerifiableInference.Desc.K13.pileMasksC s = true := W.pileMasks
    show VerifiableInference.Desc.K13.pileMasksC s' = true
    unfold VerifiableInference.Desc.K13.pileMasksC at h ⊢
    rw [hrows, R.out]
    exact h
  · have h : VerifiableInference.Desc.K13.pileWithinC s = true := W.pileWithin
    show VerifiableInference.Desc.K13.pileWithinC s' = true
    unfold VerifiableInference.Desc.K13.pileWithinC VerifiableInference.Desc.K13.ledgersFitC
      VerifiableInference.Desc.K13.rowsWithinC at h ⊢
    rw [hrows, R.st]
    exact h
  · show VerifiableInference.Desc.K13.oneRowC s' = true
    simp only [VerifiableInference.Desc.K13.oneRowC, ha']
  · have h : OnBytes.Means.tidy4B s.st = true := W.tidy
    show OnBytes.Means.tidy4B s'.st = true
    rw [R.st]
    exact h
  · have h : s.st.codes = Dm.cs := W.codes
    show s'.st.codes = Dm.cs
    rw [R.st]
    exact h
  · have h : s.check.frame.shape = Dm.shape := W.shape
    show s'.check.frame.shape = Dm.shape
    rw [R.check]
    exact h
  · have h : s.check.rows.layout = Dm.layout := W.layout
    show s'.check.rows.layout = Dm.layout
    rw [R.check]
    exact h
  · have h : s.live.frame.shape = Dm.shape := W.liveShape
    show s'.live.frame.shape = Dm.shape
    rw [hlive]
    exact h
  · have h : s.live.rows.layout = Dm.layout := W.liveLayout
    show s'.live.rows.layout = Dm.layout
    rw [hlive]
    exact h
  · have h : s.req = E.reqW z := W.reqIs
    show s'.req = E.reqW z
    rw [R.req]
    exact h

end

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **What K4's share of the bridge spends at a group's two borders, out of the border in front**,
under hS hR O hg W0 R0 L7. -/
theorem spends_of_front {Xi Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
    (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X) (E : WideData ProofFile.InstPub)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {Str : Type}
    (W0 : ∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
      RchAt (descAt Z A B c) (28 * g + 4) a → a.1.2.failed = none → WideFacts Dm E a.1)
    (R0 : ∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
      RchAt (descAt Z A B c) (28 * g + 4) a → a.1.2.failed = none →
        roomIsB E.dP.free0 E.dP.fvs (2 * g) a.1.2 = true)
    (L7 : ∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
      RchAt (descAt Z A B c) (28 * g + 4) a → a.1.2.failed = none →
        ((E.dP.tl (2 * g)).any fun tlP => lay7B tlP a.1.2) = true) :
    ∀ j, j = 28 * g + 4 ∨ j = 28 * g + 4 + 1 →
      ∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
        RchAt (descAt Z A B c) j a → a.1.2.failed = none → K4Spends Dm E j a.1 := by
  intro j hj a h hu
  obtain ⟨k1, k2⟩ := hK_at_k4 Dm E hS hR O hg L7
  obtain ⟨r1, r2⟩ := hR_at_k4 Dm E hS hR O hg R0
  rcases hj with rfl | rfl
  · have K := k1 a h hu
    exact ⟨W0 a h hu, r1 a h hu, fun m hm => (K m).1 hm, fun m hm => (K m).2.1 hm,
      fun m hm => (K m).2.2 hm⟩
  · have h5 : RchAt (descAt Z A B c) (28 * g + 5) a := h
    obtain ⟨s, p, hr, Kp⟩ := kept_rchAt hS hR O hg h5
    obtain ⟨a₀, _, _, _, ha₀, _, _, _, _, _, _, _, hRest, _⟩ := Kp
    have hu' : s.failed = none := by
      rw [← hRest.failed]
      exact hu
    have K := k2 a h5 hu
    exact ⟨wide_rest hRest ha₀ (W0 _ hr hu'), r2 a h5 hu, fun m hm => (K m).1 hm,
      fun m hm => (K m).2.1 hm, fun m hm => (K m).2.2 hm⟩

/-- **The premise Sp of k04_law_R, to the letter, out of the twelve borders in front.** -/
theorem sp_of_front {Xi Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
    (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X) (E : WideData ProofFile.InstPub)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {Str : Type}
    (W0 : ∀ g, g < 12 → ∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
      RchAt (descAt Z A B c) (28 * g + 4) a → a.1.2.failed = none → WideFacts Dm E a.1)
    (R0 : ∀ g, g < 12 → ∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
      RchAt (descAt Z A B c) (28 * g + 4) a → a.1.2.failed = none →
        roomIsB E.dP.free0 E.dP.fvs (2 * g) a.1.2 = true)
    (L7 : ∀ g, g < 12 → ∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
      RchAt (descAt Z A B c) (28 * g + 4) a → a.1.2.failed = none →
        ((E.dP.tl (2 * g)).any fun tlP => lay7B tlP a.1.2) = true) :
    ∀ g, g < 12 → ∀ j, j = 28 * g + 4 ∨ j = 28 * g + 4 + 1 →
      ∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
        RchAt (descAt Z A B c) j a → a.1.2.failed = none → K4Spends Dm E j a.1 :=
  fun g hg => spends_of_front Dm E hS hR O hg (W0 g hg) (R0 g hg) (L7 g hg)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.wide_rest
#print axioms OnBytes.Road.K4.spends_of_front
#print axioms OnBytes.Road.K4.sp_of_front
