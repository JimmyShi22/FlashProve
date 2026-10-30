-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/RidersK12.lean: THE PROXIMITY TEST's THREE ITEMS THAT RIDE PAST KIND K13's
BLOCK AND W's COMMITMENT ("K12.bookInOrder", "K12.seatsCarried", "K12.msgShapes"), AT OUR LAYER
OVER K12's LAYER: each is a rider (`Rider3`, `Rider4`:
Johnson/Desc/K13/Law/FillFromSentences.lean). Statements with their proofs.
Why. The two blocks' ties ask, of every public item that is open in front, that it holds behind. The
three are open from the chain's start and are never dropped. Their sentences are K12's files' own
tests (`fillK12`, Johnson/Desc/K12/Door/FillK12.lean); that these are the tests of which the rules
speak is shown in Johnson/Desc/K12/Door/DoorIs.lean, by the make.
Main names: `shapesItem`: the item "K12.msgShapes". `over_book`, `over_seats`, `over_shapes`: what
  `fillK13Plus D (fillK13 D (fillK12 d Mg₁))` says at the three. `shapes_same_M3`, `shapes_M4`:
  K13's block leaves the list of the messages' shapes; W's commitment
    appends its place's.
  `rider3_shapes`, `rider4_shapes`: at any filling with that sentence.
  `riders3_over`: **all three are riders at K13's block**, at our layer over K12's.
  `riders4_over`: **all three, and K13's own item, are riders at W's commitment**: under FOUR
    EQUATIONS ON THE PLAN: d.ft is the place's first tree; from the plan's counts at the block's
    place on, the plan's lists of seats, of trees' shapes and of messages' shapes go on with what
    the place lays.
What is not claimed. These equations. That `pubP` says nothing at the three in what lies beneath (a
premise). A rider's premise for any other kind's item. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.FillFromSentences
import Johnson.Desc.K1.Law.MsgShapesRideK1
import Johnson.Desc.K12.Door.FillK12
import Johnson.Desc.K12.Door.DoorIs
import Johnson.Desc.K13.KeepsCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (bookStepB Frame)
open VerifiableInference.Desc.Ground (shapesIn coreStill_shapes)
open VerifiableInference.Desc.K12.Door (K12Data fillK12 msgShapesB toTree)

/-- The door's item "K12.msgShapes". -/
def shapesItem : Pub := First.moreItem K12.Door.nShapes

section
variable {Pp W Cl : Type} {nR : ℕ}

/-! ## 1 What our layer over theirs says at the three -/

theorem over_book (D : DataK13 Pp W nR) (d : K12Data) (Mg₁ : Meaning Pp W) (x : Pp × S) :
    (fillK13Plus D (fillK13 D (fillK12 d Mg₁))).pub bookItem x = bookStepB d.ft x.2.book x.2.roots
    := rfl

theorem over_seats (D : DataK13 Pp W nR) (d : K12Data) (Mg₁ : Meaning Pp W) (x : Pp × S) :
    (fillK13Plus D (fillK13 D (fillK12 d Mg₁))).pub seatsItem x = K12.Coin.seatsPrefixB (toTree
    d.L) x.2.book :=
  rfl

theorem over_shapes (D : DataK13 Pp W nR) (d : K12Data) (Mg₁ : Meaning Pp W) (x : Pp × S) :
    (fillK13Plus D (fillK13 D (fillK12 d Mg₁))).pub shapesItem x = msgShapesB d.M x.2.st := rfl

/-! ## 2 The messages' shapes over our two steps -/

/-- K13's block leaves the list of the messages' shapes. -/
theorem shapes_same_M3 {P : Where} {x x' : Pp × S} (h : StepM3 Cl P x x') :
    shapesIn x'.2.st = shapesIn x.2.st := by
  obtain ⟨rs, gs, hd⟩ := h.2
  exact K13.RelCore.atM3_keeps coreStill_shapes P _ _ _ _ hd

/-- W's commitment appends its place's messages' shapes. -/
theorem shapes_M4 {P : Where} {P' : K1.Par} {x x' : Pp × S} (h : StepM4 Cl P P' x x') :
    shapesIn x'.2.st = shapesIn x.2.st ++ K1.shapesOf P' := by
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  obtain ⟨s₁, g₁, rs₂, g₂, h1, h2⟩ := atM4_mid hd
  have e2 : shapesIn x'.2.st = shapesIn s₁.st :=
    K13.RelCore.rowsB_keeps coreStill_shapes atS _ K13.RelCore.atS_lensCore P _ _ _ _ h2
  rw [e2]
  exact K1.sendAtS_shapesIn P' x.2 s₁ r₁ r₂ g₁ h1

theorem rider3_shapes {P : Where} {Mg : Meaning Pp W} {M : List OracleShape}
    (hM : ∀ x, Mg.pub shapesItem x = msgShapesB M x.2.st) (hP : ∀ x, Mg.pubP shapesItem x) :
    Rider3 Cl P Mg shapesItem := fun x x' h =>
  ⟨fun h0 => by
    rw [hM] at h0 ⊢
    exact K1.msgShapes_stay h0 (shapes_same_M3 h), fun _ => hP x'⟩

theorem rider4_shapes {P : Where} {P' : K1.Par} {N : Numbers} {Mg : Meaning Pp W} {Q : List Pub}
    {p : Option Place} {M : List OracleShape} (hm : shapesItem ∈ Q)
    (hM : ∀ x, Mg.pub shapesItem x = msgShapesB M x.2.st) (hP : ∀ x, Mg.pubP shapesItem x)
    (hx : (M.drop (N.msgsAt p)).take (K1.shapesOf P').length = K1.shapesOf P') :
    Rider4 Cl P P' N Mg Q p shapesItem := fun x x' h hQ hbk => by
  have h0 := hQ _ hm
  rw [hM] at h0
  unfold First.bookAt at hbk
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk
  refine ⟨?_, fun _ => hP x'⟩
  rw [hM]
  exact K1.msgShapes_ride h0 (shapes_M4 h) (by rw [hbk.2]; exact hx)

/-! ## 3 At our layer over theirs -/

/-- **All three are riders at K13's block.** -/
theorem riders3_over (D : DataK13 Pp W nR) (d : K12Data) (Mg₁ : Meaning Pp W)
    (hP : ∀ q, q = bookItem ∨ q = seatsItem ∨ q = shapesItem → ∀ x, Mg₁.pubP q x) :
    ∀ q, q = bookItem ∨ q = seatsItem ∨ q = shapesItem →
      Rider3 Cl D.P (fillK13Plus D (fillK13 D (fillK12 d Mg₁))) q := by
  rintro q (rfl | rfl | rfl)
  · exact rider3_book (over_book D d Mg₁) (hP _ (Or.inl rfl))
  · exact rider3_seats (over_seats D d Mg₁) (hP _ (Or.inr (Or.inl rfl)))
  · exact rider3_shapes (over_shapes D d Mg₁) (hP _ (Or.inr (Or.inr rfl)))

/-- **All three, and K13's own item, are riders at W's commitment.** -/
theorem riders4_over {F : Frame} (y₀ : F.E.Str) (D : DataK13 Pp W nR) (d : K12Data)
    (Mg₁ : Meaning Pp W) (P' : K1.Par) (Q : List Pub) (p : Option Place)
    (hP : ∀ q, q = bookItem ∨ q = seatsItem ∨ q = shapesItem → ∀ x, Mg₁.pubP q x)
    (hP3 : ∀ q, q = .frontOk ∨ q = .evalLaid ∨ q = wSitsItem → ∀ x, Mg₁.pubP q x)
    (hft : d.ft = P'.gp.firstTree)
    (hp : ((toTree d.L).places.drop (D.N.msgsAt p)).take P'.sent.size =
      K12.Coin.placesOf (D.N.treesAt p) P'.sent.size (K1.layOf P'))
    (hs : ((toTree d.L).shapes.drop (D.N.treesAt p)).take (K1.layOf P').shapes.size =
      (K1.layOf P').shapes.toList)
    (hx : (d.M.drop (D.N.msgsAt p)).take (K1.shapesOf P').length = K1.shapesOf P') :
    ∀ q ∈ Q, (q = bookItem ∨ q = seatsItem ∨ q = shapesItem ∨ q = .frontOk) →
      Rider4 Cl D.P P' D.N (fillK13Plus D (fillK13 D (fillK12 d Mg₁))) Q p q := by
  rintro q hq (rfl | rfl | rfl | rfl)
  · exact rider4_book hq (fun x => by rw [over_book, hft]) (hP _ (Or.inl rfl))
  · exact rider4_seats hq (over_seats D d Mg₁) (hP _ (Or.inr (Or.inl rfl))) hp hs
  · exact rider4_shapes hq (over_shapes D d Mg₁) (hP _ (Or.inr (Or.inr rfl))) hx
  · exact rider4_frontOk y₀ (sentences_at_layer D (fillK12 d Mg₁) hP3) hq

end

end VerifiableInference.Desc.K13.Law
