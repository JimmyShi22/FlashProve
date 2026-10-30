-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/FillGFromSentences.lean: WHAT THE FIRST SEGMENT's OPENING ASKS OF THE TABLE's
LETTERS (`FillG`, Johnson/Desc/K13/Law/AtTableFirst.lean), CLAUSE BY CLAUSE: WHICH IS PAID BY WHICH
SENTENCE OF THE ONE FILLING: the like of Johnson/Desc/K13/Law/FillFromSentences.lean for that block.
Definitions and statements with their proofs.
Main names:
  `RiderG … Q p i`: over a step of the joined block that begins inside the promise the item's Bool
    holds behind, and its `pubP` goes on.
  Payers: `riderG_book`, `riderG_seats`, `riderG_shapes` (the proximity test's three: THE BLOCK
    SENDS: they are EARNED, each under an equation on the plan), `riderG_reply` (any item that
    reads of the chain's state whether a reply is held, and no more).
  `OthersG`: WHAT STAYS: the items that come at the block (a list mk) (they speak of the fresh
    ledger that "link 0: opened" lays); `decodes`; what rides goes back; what other layers say of
    "in order". `openingZero_tidy`: "tidy in front, tidy behind" over a step of the joined block.
  `fillG_of`: **`FillG` at any list Q**, from the sentences, `OthersG`, one premise a rider, and
    two tests on the plan: the joined block's own `planOk`; the plan's number of the index masks'
    message is the last of the place's messages.
  `groups_of_sentence`: `first_tied`'s premise hgroups, at "nothing is sent yet" as our layer lays
    it.
What is not claimed. `OthersG` at any filling. A rider's premise for an item that is not named here.
Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.AtTableFirst
import Johnson.Desc.K13.Law.RidersK12
import Johnson.Desc.K13.Law.InOrderRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice
open Desc.Plain
open OnBytes.Means (Tidy)
open Johnson.Desc.First.Walk (LayPar)
open Johnson.Desc.First.Walk.Tied (openedZeroGives)
open VerifiableInference.Desc.First (S Item Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (bookStepB bookStep_iff)
open VerifiableInference.Desc.Ground (shapesIn By TidyStay groundQuiet_tidy admitOn_tidy)
open VerifiableInference.Desc.Keeps (Steps steps_of_fits andThen_fits)
open VerifiableInference.Desc.K12.Door (msgShapesB)

section
variable {Pp W Cl : Type}

/-- **A rider at the first segment's opening.** -/
def RiderG (Cl : Type) (q : Params.First) (gp : GPar) (nm : String) (X : LayPar) (fvs : List Bool)
    (kCol : ℕ) (N : Numbers) (Mg : Meaning Pp W) (Q : List Pub) (p : Option Place) (i : Pub) :
    Prop :=
  ∀ x x', StepG Cl q gp nm X fvs kCol x x' → (∀ q' ∈ Q, Mg.pub q' x = true) →
    First.bookAt N p x.2 = true → Mg.pub i x' = true ∧ (Mg.pubP i x → Mg.pubP i x')

variable {q : Params.First} {gp : GPar} {nm : String} {X : LayPar} {fvs : List Bool} {kCol : ℕ}
  {N : Numbers} {Mg : Meaning Pp W} {Q : List Pub} {p : Option Place}

/-- "K12.bookInOrder": where it counts from the place's first tree. -/
theorem riderG_book (hm : bookItem ∈ Q)
    (hB : ∀ x, Mg.pub bookItem x = bookStepB (K1.firstPar q gp).gp.firstTree x.2.book x.2.roots)
    (hP : ∀ x, Mg.pubP bookItem x) : RiderG Cl q gp nm X fvs kCol N Mg Q p bookItem :=
  fun x x' h hQ _ => by
    obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
    have h0 := hQ _ hm
    rw [hB] at h0
    refine ⟨?_, fun _ => hP x'⟩
    rw [hB]
    exact (bookStep_iff _ _ _).2
      (bookStep_seated (openingZero_seated hd) ((bookStep_iff _ _ _).1 h0))

/-- "K12.seatsCarried": where the plan's lists go on with what the place lays. -/
theorem riderG_seats {L : K12.Coin.Laid} (hm : seatsItem ∈ Q)
    (hSe : ∀ x, Mg.pub seatsItem x = K12.Coin.seatsPrefixB L x.2.book)
    (hP : ∀ x, Mg.pubP seatsItem x)
    (hp : (L.places.drop (N.msgsAt p)).take (K1.firstPar q gp).sent.size =
      K12.Coin.placesOf (N.treesAt p) (K1.firstPar q gp).sent.size (K1.layOf (K1.firstPar q gp)))
    (hs : (L.shapes.drop (N.treesAt p)).take (K1.layOf (K1.firstPar q gp)).shapes.size =
      (K1.layOf (K1.firstPar q gp)).shapes.toList) :
    RiderG Cl q gp nm X fvs kCol N Mg Q p seatsItem := fun x x' h hQ hbk => by
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  have h0 := hQ _ hm
  rw [hSe] at h0
  unfold First.bookAt at hbk
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk
  obtain ⟨⟨b1, b2⟩, b3⟩ := hbk
  refine ⟨?_, fun _ => hP x'⟩
  rw [hSe]
  exact (K12.Coin.seatsPrefix_iff _ _).2 ((openingZero_seated hd).seatsRide
    ((K12.Coin.seatsPrefix_iff _ _).1 h0) (by rw [b2, b3, b1]; exact hp) (by rw [b1]; exact hs))

/-- The joined block appends its place's messages' shapes. -/
theorem shapes_G {x x' : Pp × S} (h : StepG Cl q gp nm X fvs kCol x x') :
    shapesIn x'.2.st = shapesIn x.2.st ++ K1.shapesOf (K1.firstPar q gp) := by
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  obtain ⟨s₁, g₁, h1, h2⟩ := K1.openingZero_mid hd
  have e : x'.2.st = s₁.st := (openedZeroGives X fvs kCol s₁ x'.2 h2).2.2.1.2.2.1
  rw [e]
  exact K1.firstAtS_shapesIn q gp x.2 s₁ r₁ r₂ g₁ h1

/-- "K12.msgShapes": where the plan's list of shapes goes on with the place's. -/
theorem riderG_shapes {M : List OracleShape} (hm : shapesItem ∈ Q)
    (hM : ∀ x, Mg.pub shapesItem x = msgShapesB M x.2.st) (hP : ∀ x, Mg.pubP shapesItem x)
    (hx : (M.drop (N.msgsAt p)).take (K1.shapesOf (K1.firstPar q gp)).length =
      K1.shapesOf (K1.firstPar q gp)) :
    RiderG Cl q gp nm X fvs kCol N Mg Q p shapesItem := fun x x' h hQ hbk => by
  have h0 := hQ _ hm
  rw [hM] at h0
  unfold First.bookAt at hbk
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk
  refine ⟨?_, fun _ => hP x'⟩
  rw [hM]
  exact K1.msgShapes_ride h0 (shapes_G h) (by rw [hbk.2]; exact hx)

/-- An item that reads of the chain's state whether a reply is held, and no more. -/
theorem riderG_reply {i : Pub} (hm : i ∈ Q) (g : Bool → Bool)
    (hI : ∀ x, Mg.pub i x = g x.2.out.reply.isNone) (hP : ∀ x, Mg.pubP i x) :
    RiderG Cl q gp nm X fvs kCol N Mg Q p i := fun x x' h hQ _ => by
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  have h0 := hQ _ hm
  have e := (K1.openingZero_rec hd).2.2.2.2.2.1
  refine ⟨?_, fun _ => hP x'⟩
  rw [hI] at h0 ⊢
  rw [e]
  exact h0

/-- "Tidy in front, tidy behind" over a step of the joined block. -/
theorem openingZero_tidy (q : Params.First) (gp : GPar) (nm : String) (X : LayPar)
    (fvs : List Bool) (kCol : ℕ) :
    Steps (By TidyStay fun s : S => s.st)
      (K1.openingZero q gp nm X fvs kCol : Block S Cl) :=
  steps_of_fits (andThen_fits _ (fun _ _ _ x y z => y (x z)) _ _ _ rfl
    (K1.firstAtS_fits groundQuiet_tidy admitOn_tidy q gp)
    (fun s _ _ s' h => by
      have e : s'.st = s.st := (openedZeroGives X fvs kCol s s' h).2.2.1.2.2.1
      show Tidy s.st → Tidy s'.st
      rw [e]
      exact id))

/-- **What stays at the first segment's opening.** -/
structure OthersG (Cl : Type) (q : Params.First) (gp : GPar) (nm : String) (X : LayPar)
    (fvs : List Bool) (kCol : ℕ) (N : Numbers) (Mg : Meaning Pp W) (rest : Pp × S → Bool)
    (Q : List Pub) (p : Option Place) (mk : List Pub) : Prop where
  made : ∀ x x' i, StepG Cl q gp nm X fvs kCol x x' → (∀ q' ∈ Q, Mg.pub q' x = true) →
    First.bookAt N p x.2 = true → Mg.inOrder x = true → i ∈ mk →
    Mg.pub i x' = true ∧ Mg.pubP i x'
  rest : ∀ x x', StepG Cl q gp nm X fvs kCol x x' → rest x = true → rest x' = true
  decodes : ∀ x x' y y', StepG Cl q gp nm X fvs kCol x x' → y'.cell = y.cell → Mg.decodes x y →
    Mg.decodes x' y'
  back : ∀ x x' y y' w i, StepG Cl q gp nm X fvs kCol x x' → (∀ q' ∈ Q, Mg.pub q' x = true) →
    First.bookAt N p x.2 = true → y'.cell = y.cell → riderG i = true →
    Item.holds N Mg i x' y' w → Item.holds N Mg i x y w

/-- **`FillG` from the sentences**, at any list of riders. -/
theorem fillG_of {P : Where} {cs : Codes} {sh : Params.ReqShape} {ly : Params.ReqLayout}
    {rest : Pp × S → Bool} {nR : ℕ} {rw : Pp × S → W → Wit GE nR P.lin.kCol} {mk : List Pub}
    (hS : Sentences P cs sh ly N rest Mg rw) (hNS : ∀ x, Mg.pub .noneSent x = noneSentC N x.2)
    (hm : Pub.noneSent ∈ Q) (hO : OthersG Cl q gp nm X fvs kCol N Mg rest Q p mk)
    (hplan : (K1.openingZero q gp nm X fvs kCol : Block S Cl).planOk = true)
    (hidx : N.indexNo = (K1.firstPar q gp).sent.size - 1)
    (hR : ∀ i ∈ Q, i ≠ .noneSent → RiderG Cl q gp nm X fvs kCol N Mg Q p i) :
    FillG Cl q gp nm X fvs kCol N Mg Q p mk where
  made := fun x x' i h hQ hbk hin hi => by
    rcases hi with hi | rfl | rfl
    · exact (hO.made x x' i h hQ hbk hin hi).1
    · obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
      have h0 := hQ _ hm
      rw [hNS, noneSentC_eq, Bool.and_eq_true, Bool.and_eq_true] at h0
      rw [hS.indexIs, hidx]
      exact (K1.openingZero_makes hd h0.1.1).1
    · obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
      have h0 := hQ _ hm
      rw [hNS, noneSentC_eq, Bool.and_eq_true, Bool.and_eq_true] at h0
      rw [hS.indexThere]
      exact (K1.openingZero_makes hd h0.1.1).2
  madeP := fun x x' i h hQ hbk hin hi => (hO.made x x' i h hQ hbk hin hi).2
  pubRide := fun x x' i h hQ hbk hi hne => (hR i hi hne x x' h hQ hbk).1
  pubPRide := fun x x' i h hQ hbk hi hne h0 => (hR i hi hne x x' h hQ hbk).2 h0
  inOrder := fun x x' h h0 => by
    obtain ⟨ft, rs, cols, n, hst⟩ := h.2
    obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
    rw [hS.inOrder, Bool.and_eq_true] at h0 ⊢
    exact ⟨hO.rest x x' h h0.1,
      inOrderK13_rides' (openingZero_tidy q gp nm X fvs kCol hplan ft _ rs cols _ n hst)
        (openingZero_plan q gp nm X fvs kCol _ _ _ _ hd) h0.2⟩
  decodes := hO.decodes
  back := hO.back

/-- `first_tied`'s premise on the number of groups, at "nothing is sent yet" as our layer lays it.
-/
theorem groups_of_sentence (hNS : ∀ x, Mg.pub .noneSent x = noneSentC N x.2) (x : Pp × S)
    (h : Mg.pub .noneSent x = true) : N.groupAt 0 = x.2.st.groups.size := by
  rw [hNS, noneSentC_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  exact (eq_of_beq h.1.2).symm

end

end VerifiableInference.Desc.K13.Law
