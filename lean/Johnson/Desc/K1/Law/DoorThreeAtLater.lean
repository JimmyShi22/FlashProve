-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/DoorThreeAtLater.lean: the
proximity test's three names that grow with a sending, "K12.bookInOrder", "K12.seatsCarried" and
"K12.msgShapes", are kept over an accept of a later sending's sub-protocol, at every meaning
`plus13 D dk M` (K13/Law/BridgeK13.lean). Arms of hrest_plus13.
WHOSE. Section 1 (`SeatedBy.bookStep`, `LaterSeated` and its four members) is taken over,
out of the file PubAtLaterDoor.lean, to the sign. That
file reads `D.d12`, a field that `PubData` does not have, and is not in this library. Section 2
restates its three arms at `dk : K12Data` and at the layer's own tests.
  `laterSeated_blkL`   the sub-protocol at (l, d) is a member, at `parL Z G l d`
  `book_later`     "K12.bookInOrder". PREMISE hft: the number from which it counts is the place's
                   first tree
  `seats_later`    "K12.seatsCarried". PREMISES hbk (the promise's own clause on the book in front,
                   `First.bookAt`), hp, hs: from the list of rounds' counts at the place on, the
                   lists of seats and of trees' shapes go on with what the place lays
  `shapes_later`   "K12.msgShapes". PREMISES hbk, hx: the like for the messages' shapes
What is not claimed. The four equations, at any list of rounds. That the items are open at any
border. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.LaterOne
import Johnson.Desc.K1.Law.PubAtLaterIndex
import Johnson.Desc.K1.Law.SeatsRideK1
import Johnson.Desc.K1.Law.MsgShapesRideK1
import Johnson.Desc.K1.Law.RowsAtCommit
import Johnson.Desc.K12.Door.DoorIs
import Johnson.Desc.K13.Law.BridgeK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (BookStep bookStepB bookStep_iff)
open VerifiableInference.Desc.Ground (shapesIn)
open VerifiableInference.Desc.K12.Door (toTree msgShapesB K12Data)
open VerifiableInference.Desc.K13.Law (plus13 DataK13)
open OnBytes.Model.Stages (LinkH)

variable {Cl Pp : Type}

/-! ## 1 The sub-protocols -/

/-- "The book in order" through a sending of kind K1. -/
theorem SeatedBy.bookStep {P : Par} {bk bk' : TreeBook} {n r n' r' : Nat}
    (h : SeatedBy P bk n r bk' n' r') (h0 : BookStep P.gp.firstTree bk r) :
    BookStep P.gp.firstTree bk' r' := by
  obtain ⟨e, ho⟩ := h0
  refine ⟨by rw [h.roots, h.seated.size, e], fun z T hT => ?_⟩
  by_cases hz : z < bk.trees.size
  · rw [h.seated.trees z hz] at hT
    exact ho z T hT
  · have hz' : z < bk'.trees.size := by
      by_contra hn
      rw [Array.getElem?_eq_none (by omega)] at hT
      cases hT
    rw [h.seated.size] at hz'
    obtain ⟨t, ht, _, hnum, _⟩ := h.seated.made (z - bk.trees.size) (by omega)
    rw [show bk.trees.size + (z - bk.trees.size) = z by omega, hT] at ht
    obtain rfl := Option.some.inj ht
    rw [hnum, e]
    omega

/-- **A block of a later moment's sending of the place P**: what a yes of it on two rounds does to
what the four items read. -/
def LaterSeated (P : Par) (B : Block S Cl) : Prop :=
  ∀ s s' rs gs, rs.length = 2 → B.decide s rs gs = .ok s' →
    SeatedBy P s.book s.st.oracles.size s.roots s'.book s'.st.oracles.size s'.roots ∧
      shapesIn s'.st = shapesIn s.st ++ shapesOf P ∧ s'.rows = s.rows

/-- The sending alone. -/
theorem laterSeated_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    LaterSeated P (commitAtS P link moment arrays : Block S Cl) := by
  intro s s' rs gs h2 h
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  exact ⟨commitAtS_seated P link moment arrays s s' r₁ r₂ gs h,
    commitAtS_shapesIn P link moment arrays s s' r₁ r₂ gs h,
    commitAtS_rows P link moment arrays s s' _ gs h⟩

/-- **The first member**: a segment's later moment at the plan's numbers (a link's digits). -/
theorem laterSeated_laterAt (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) :
    LaterSeated (parLater q gp link piece moment)
      (laterAt q gp link piece moment arrays : Block S Cl) :=
  laterSeated_commitAtS _ _ _ _

/-- The sending with a quiet block joined behind it. -/
theorem laterSeated_joined (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (nm : String)
    (q : Block S Cl) (hq : QuietP q) :
    LaterSeated P (Block.andThen nm (commitAtS P link moment arrays) q) := by
  intro s s' rs gs h2 h
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ := joined_yes P link moment arrays nm q s s' r₁ r₂ gs h
  obtain ⟨e1, e2, _, _, _, _, _, e8, e9⟩ := hq _ _ _ _ h3
  rw [e1, e2, e8, e9]
  exact laterSeated_commitAtS P link moment arrays s s₁ _ gs₁ rfl h1

/-- **The second member**: the reads' place's joined block. -/
theorem laterSeated_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) (X : LinkH) (pr : Nat)
    (reads : Option (List Nat)) :
    LaterSeated (parLater G.first (gpOf Z) l pr 1) (IM.k1Reads Z G l X pr reads) :=
  laterSeated_joined _ _ _ _ _ _ (quietP_orLoud _ _ _ G l X _)

theorem laterSeated_blkL (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) : LaterSeated (parL Z G l d) (blkL Z G l d X arrs) := by
  cases d with
  | true => exact laterSeated_laterAt _ _ _ _ _ _
  | false => exact laterSeated_k1Reads _ _ _ _ _ _

/-! ## 2 The three names over a sub-protocol's own accept -/

section
variable {W : Type} {nR : ℕ} (D : DataK13 Pp W nR) (dk : K12Data) (M : Meaning Pp W) {P : Par}
  {B : Block S Cl} (hB : LaterSeated P B) (x x' : Pp × S) (rs : List Fmt.RoundView)
  (gs : List (List (Nat × List UInt64))) (h2 : rs.length = 2)
  (h : B.decide x.2 rs gs = .ok x'.2)
include hB h2 h

/-- **"K12.bookInOrder"** over the sub-protocol's own accept. -/
theorem book_later (hft : dk.ft = P.gp.firstTree)
    (h0 : (plus13 D dk M).pub (.more none "K12.bookInOrder") x = true) :
    (plus13 D dk M).pub (.more none "K12.bookInOrder") x' = true := by
  have h0' : bookStepB dk.ft x.2.book x.2.roots = true := h0
  show bookStepB dk.ft x'.2.book x'.2.roots = true
  rw [hft] at h0' ⊢
  exact (bookStep_iff _ _ _).2 ((hB _ _ _ _ h2 h).1.bookStep ((bookStep_iff _ _ _).1 h0'))

/-- **"K12.seatsCarried"** over the sub-protocol's own accept. -/
theorem seats_later (N : Numbers) (p : Option Place) (hbk : First.bookAt N p x.2 = true)
    (hp : ((toTree dk.L).places.drop (N.msgsAt p)).take P.sent.size =
      K12.Coin.placesOf (N.treesAt p) P.sent.size (layOf P))
    (hs : ((toTree dk.L).shapes.drop (N.treesAt p)).take (layOf P).shapes.size =
      (layOf P).shapes.toList)
    (h0 : (plus13 D dk M).pub (.more none "K12.seatsCarried") x = true) :
    (plus13 D dk M).pub (.more none "K12.seatsCarried") x' = true := by
  have h0' : K12.Coin.seatsPrefixB (toTree dk.L) x.2.book = true := h0
  show K12.Coin.seatsPrefixB (toTree dk.L) x'.2.book = true
  unfold First.bookAt at hbk
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk
  obtain ⟨⟨b1, b2⟩, b3⟩ := hbk
  refine (K12.Coin.seatsPrefix_iff _ _).2 ((hB _ _ _ _ h2 h).1.seatsRide
    ((K12.Coin.seatsPrefix_iff _ _).1 h0') ?_ ?_)
  · rw [b2, b3, b1]
    exact hp
  · rw [b1]
    exact hs

/-- **"K12.msgShapes"** over the sub-protocol's own accept. -/
theorem shapes_later (N : Numbers) (p : Option Place) (hbk : First.bookAt N p x.2 = true)
    (hx : (dk.M.drop (N.msgsAt p)).take (shapesOf P).length = shapesOf P)
    (h0 : (plus13 D dk M).pub (.more none "K12.msgShapes") x = true) :
    (plus13 D dk M).pub (.more none "K12.msgShapes") x' = true := by
  have h0' : msgShapesB dk.M x.2.st = true := h0
  show msgShapesB dk.M x'.2.st = true
  unfold First.bookAt at hbk
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk
  exact msgShapes_ride h0' (hB _ _ _ _ h2 h).2.1 (by rw [hbk.2]; exact hx)

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.laterSeated_blkL
#print axioms VerifiableInference.Desc.K1.book_later
#print axioms VerifiableInference.Desc.K1.seats_later
#print axioms VerifiableInference.Desc.K1.shapes_later
