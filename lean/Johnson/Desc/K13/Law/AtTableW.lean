-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/AtTableW.lean: W's COMMITMENT WITH KIND K13's BLOCK BEHIND IT, AT ITS ROW OF
THE TABLE OF JOINTS: A LAW OF THE TABLE's SHAPE. Definitions and statements with their proofs.

Why. The table's row at this place (Johnson/Desc/First/Borders.lean, `backRow`, kind K1) opens W's
pin and keeps the one claim on the weights and the stored table's pin: THE CLAIM RIDES PAST W's
SENDING. Kind K13's own law there (`atM4_goodInA`, Johnson/Desc/K13/Law/PinA.lean) EXCHANGES the
claim: behind the block it asks "all that the statement claims holds of the words" and "W's message
holds g^T M", which no item that is open there gives. So that law cannot be tied to this row
(by reading). Here the block has a law of the row's own shape:
the sending kind's law for what hangs on the challenge (`K1.send_tied`,
Johnson/Desc/K1/Law/AtTable.lean); the claim goes back (`FillM4.pileOne`) because the block leaves
the rows on the table (`pileOne_back`, by `rowsB_rows` and `K1.sendAtS_rows`). The exchange stays
with whoever opens the rows on W.

OBJECT. `atM4 P (K1.sendAtS P')` (Johnson/Desc/K13/AtS.lean), at the sending's two written rounds
(`K1.sendPiece`); as a chain holds it: any block c with `c.UnderR (atM4 P (K1.sendAtS P'))`.
USER. `EachTied` | `chainOfPromises` (Johnson/Desc/Sound/ChainOfPromises.lean): `w_tied` and
`w_tied_seat` end in `TiedAt N Mg links ps get k (K1.sendPiece …)`, to the letter.
LETTERS. The table's own; the two kinds' numbers P, P'; rad, fOf, fIn, e (the sending's law's).
FIELD. `first_chain_knows_means` (Johnson/Goal/Skeleton/ProofFile.lean), through `chainOfPromises`;
the step from that theorem's end into the field is other files' to show, and is not typed here.

Main names:
  What the block does to the record (`atM4_rec`, `atM4_laid`, `isSend_atM4`, `StepM4`):
    Johnson/Desc/K13/Law/AtRecord.lean.
  THROUGH THE TABLE's DOOR (`wSitsItem`, `wSitsMore`: Johnson/Desc/K13/Law/SitsDoor.lean): a public
    item "W sits as the plan says" (`wSitsB`, Johnson/Desc/K13/Law/SitsAt.lean; with W's seat in the
    book: `wSeatB`, SeatMade.lean), made by this block (`atM4_sits`, SitsMade.lean; `atM4_seat`,
    from `bookAt` in front and one equation on the plan's numbers), never dropped on this chain;
    `wSits_fit`: the table's own test on a filling says yes at both lists; `wSits_asked_early`: a
    try.
  `RowM4`, `FillM4`: what is asked of the table; what is asked of its letters.
  `pileOne_back`: `FillM4.pileOne` at "all rows on the table are true", the reader a family.
  `rowM4B`, `rowM4_of_test`, `rowM4_small`, `rowM4_full`: `RowM4` as a test with code, and
    **members**, at the filling `wSitsMore`: block number 76 of 78; 356 of 358. `rowM3_small_w`,
    `rowM3_full_w`: K13's own row's members at that same filling.
  `w_tied`: **the five ties**, of any sending whose yes is a step of the joined block.
  `w_tied_seat`: **at any such c**, where the chain's record is the carried record itself.

What is not claimed. NO MEMBER OF `FillM4`, hseal OR hshown IS SHOWN. THE MEMBERS BELOW ARE MEMBERS
OF THE TABLE's HALF ALONE: the equations on the plan's numbers stay premises, and no `Numbers` made
of a plan stands here. TWO NUMBERINGS OF TREES ARE TIED BY NOTHING: `planSeatB` lays W's tenant's
tree in the BOOK's numbering (`N.treesAt`); hshown, hseal and hbase read it in the FILE's (the
piece's base): "base = N.treesAt ps[k]?" is a test on the plan and the list of pieces, asked
nowhere. `wSeatB` reads the book's places alone: nothing of what the book's tree holds at that
part. `planSitsB` and `planSeatB` have run at no plan. hseal: the sending's seal, which names a
message by its number in the statement, gives "held" and "no collision" at the tenant N.w: it is
handed, where the door's item is open behind, that W sits as the plan says and that the book has
N.w at the sealed number. hshown: behind the sending every leaf of W's tree is shown. That W's
message holds g^T M is said nowhere here. Nothing on soundness, on an honest prover or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.AtTableRow
import Johnson.Desc.K13.Law.SeatMade
import Johnson.Desc.K13.Law.SitsDoor
import Johnson.Desc.K1.Law.AtTable
import Johnson.Desc.Sound.SeatGuardChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice Iop Run
open OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More)
open Johnson.Pack (portOmZ)
open VerifiableInference.Desc.Sound (Frame Piece strsOf onQ meansQ relQ insQ outsQ TiedAt relAt
  openAfter insL outsL openL openIsList)

/-! ## 1 What is asked of the table, and of its letters -/

/-- **W's tenant is the seat that the block makes**: a test with code on the plan's numbers: p: the
block's place. -/
def planSeatB (N : Numbers) (p : Option Place) (P' : K1.Par) : Bool :=
  N.w == (N.treesAt p + (K1.layOf P').tree.getD 0 0, (K1.layOf P').part.getD 0 0)

/-- **What is asked of the table at (M, links, ps, k).** M: a filling of the table's door. nT, nM:
the trees and the messages that the block sends. -/
structure RowM4 (N : Numbers) (M : More) (links : List ModelPart) (ps : List Place) (k nT nM : ℕ) :
    Prop where
  /-- the row closes nothing; it reads the one claim and the stored table's pin -/
  ins : ∀ i, insQ links ps k i → i = .pileOne ∨ i = .pinW ∨ i = .unmarked
  outs : outsQ links ps k .pileOne ∧ outsQ links ps k .pinW
  /-- the index masks' pin alone rides past the block -/
  rider : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ First.start links) k i →
    ¬ insQ links ps k i → i = .pinI
  next : ∀ p', ps[k + 1]? = some p' → First.standAt links p' = .mem
  pinIn : Item.pinI ∈ openAt links ps k
  /-- behind, the pins with a sample are the index masks' and W's -/
  two : ∀ t ∈ First.sampledIn N (openAt links ps (k + 1)), t = N.index ∨ t = N.w
  noRows : First.rowSegs (openAt links ps (k + 1)) = []
  /-- K13's public item is open in front -/
  frontIn : Pub.frontOk ∈ (First.pubSets M links ps)[k]?.getD []
  /-- what is open behind: K13's item still; the two that come at the block; whatever else was open
  in front -/
  pubs : ∀ q ∈ (First.pubSets M links ps)[k + 1]?.getD [],
    q = .frontOk ∨ q = .evalLaid ∨ q = wSitsItem ∨ q ∈ (First.pubSets M links ps)[k]?.getD []
  tied : ∀ q ∈ First.pubOfItems (openAt links ps (k + 1)), q = .indexIs ∨ q = .indexThere
  /-- the plan's numbers of trees and messages grow by what the block sends -/
  trees : N.treesAt ps[k + 1]? = N.treesAt ps[k]? + nT
  msgs : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]? + nM

/-- **What is asked of the table's letters at W's commitment.** Q: the public items that are open in
front. p: the block's own place. -/
structure FillM4 {Pp W : Type} (Cl : Type) (P : Where) (P' : K1.Par) (N : Numbers)
    (Mg : Meaning Pp W) (Q : List Pub) (p : Option Place) : Prop where
  /-- the three public items are the kind's own tests, and say nothing beside their Bools (by the
  table's own terms `pubP` is True at them: payable, and idle) -/
  frontOk : ∀ x, Mg.pub .frontOk x = true ↔ frontOkB P x.2 = true
  frontOkP : ∀ x, frontOkB P x.2 = true → Mg.pubP .frontOk x
  evalLaid : ∀ x, evalLaidB P x.2 = true → Mg.pub .evalLaid x = true
  evalLaidP : ∀ x, evalLaidB P x.2 = true → Mg.pubP .evalLaid x
  wSits : ∀ x, Mg.pub wSitsItem x = true ↔ (wSitsB P'.codes P x.2 = true ∧ wSeatB N.w x.2 = true)
  wSitsP : ∀ x, wSitsB P'.codes P x.2 = true → wSeatB N.w x.2 = true → Mg.pubP wSitsItem x
  /-- over a step the two public items that are tied to the index masks' pin ride -/
  indexIs : ∀ x x', StepM4 Cl P P' x x' → Mg.pub .indexIs x = true → Mg.pub .indexIs x' = true
  indexThere : ∀ x x', StepM4 Cl P P' x x' → Mg.pub .indexThere x = true →
    Mg.pub .indexThere x' = true
  /-- INSIDE THE PROMISE IN FRONT (every public item that is open there; the book stands where the
  plan says OF THIS BLOCK's PLACE) every public item that is open in front holds behind. THE BLOCK
  SENDS: an item on the book is EARNED here, not kept: over a bare step this clause would be false
  at "the book's places are a prefix of the plan's list" -/
  pubRide : ∀ x x' q, StepM4 Cl P P' x x' → (∀ q' ∈ Q, Mg.pub q' x = true) →
    First.bookAt N p x.2 = true → q ∈ Q → Mg.pub q x' = true
  pubPRide : ∀ x x' q, StepM4 Cl P P' x x' → (∀ q' ∈ Q, Mg.pub q' x = true) →
    First.bookAt N p x.2 = true → q ∈ Q → Mg.pubP q x → Mg.pubP q x'
  /-- INSIDE THE PROMISE IN FRONT (every public item that is open there; the two that are tied to
  the index masks' pin; where the book stands) the one claim goes back over a step (`pileOne_back`
  pays it where the claim is "all rows on the table are true" at a reader that rides there) -/
  pileOne : ∀ x x' y y' w, StepM4 Cl P P' x x' → (∀ q ∈ Q, Mg.pub q x = true) →
    Mg.pub .indexIs x = true → Mg.pub .indexThere x = true → First.bookAt N p x.2 = true →
    Mg.pileOne x' y' w → Mg.pileOne x y w
  inOrder : ∀ x x', StepM4 Cl P P' x x' → Mg.inOrder x = true → Mg.inOrder x' = true
  held : ∀ x x', StepM4 Cl P P' x x' → Mg.held N.index.1 N.index.2 x = true →
    Mg.held N.index.1 N.index.2 x' = true
  shown : ∀ y y', OldKept N.index.1 y y' → Mg.shown N.index.1 N.index.2 y →
    Mg.shown N.index.1 N.index.2 y'
  /-- INSIDE THE PROMISE IN FRONT (the record holds the index masks' sample; the book stands where
  the plan says of this block's place): THE BLOCK SENDS: over a bare step a short book would let
  W's tree land at the index masks' seat -/
  noColl : ∀ x x' y y', StepM4 Cl P P' x x' → Mg.held N.index.1 N.index.2 x = true →
    First.bookAt N p x.2 = true → OldKept N.index.1 y y' →
    Mg.noColl N.index.1 N.index.2 x y → Mg.noColl N.index.1 N.index.2 x' y'
  decodes : ∀ x x' y y', StepM4 Cl P P' x x' → y'.cell = y.cell → Mg.decodes x y →
    Mg.decodes x' y'
  pinWBack : ∀ x x' y y' w, StepM4 Cl P P' x x' → y'.cell = y.cell → Mg.pinW x' y' w →
    Mg.pinW x y w
  /-- inside the same -/
  pinIBack : ∀ x x' y y' w, StepM4 Cl P P' x x' → Mg.held N.index.1 N.index.2 x = true →
    First.bookAt N p x.2 = true → OldKept N.index.1 y y' →
    Mg.pin N.index.1 N.index.2 x' y' w → Mg.pin N.index.1 N.index.2 x y w

/-- **`FillM4.pileOne` is paid** where the one claim is "all rows on the table are true" at a reader
(a family in the record) under which what the rows behind a step say behind, they say in front: the
block leaves the rows on the table. -/
theorem pileOne_back {Pp W Cl : Type} {P : Where} {P' : K1.Par} {nR k : ℕ} (N : Numbers)
    (Mg : Meaning Pp W) (Q : List Pub) (rw : Pp × S → W → Wit GE nR k)
    (hfill : ∀ x y w, Mg.pileOne x y w ↔ RowsTrue (rw x) x.2 w)
    (p : Option Place)
    (hread : ∀ x x' w, StepM4 Cl P P' x x' → (∀ q ∈ Q, Mg.pub q x = true) →
      Mg.pub .indexIs x = true → Mg.pub .indexThere x = true → First.bookAt N p x.2 = true →
      RowsTrue (rw x') x'.2 w → RowsTrue (rw x) x'.2 w)
    (x x' : Pp × S) (y y' : Strs) (w : W) (h : StepM4 Cl P P' x x')
    (hq : ∀ q ∈ Q, Mg.pub q x = true) (hi : Mg.pub .indexIs x = true)
    (ht : Mg.pub .indexThere x = true)
    (hb : First.bookAt N p x.2 = true) (hw : Mg.pileOne x' y' w) : Mg.pileOne x y w := by
  obtain ⟨r₁, r₂, gs, hdec⟩ := h.decide
  have h1 := hread x x' w h hq hi ht hb ((hfill x' y' w).1 hw)
  refine (hfill x y w).2 fun r hr => h1 r ?_
  rw [(atM4_rec hdec).2.2.2.2]
  exact hr

/-! ## 2 The ties -/

section
variable {A Pp Cl W : Type} {F : Frame}

/-- **THE FIVE TIES AT W's COMMITMENT**, of any sending whose yes is a step of the joined block:
LESS WHAT IS NEW AT THIS BLOCK IN THE PROMISE BEHIND: "held", "no collision" (hseal) and "shown"
(hshown) at W's tenant are premises. -/
theorem w_tied (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (get : A → Pp × S) (k : ℕ) (P : Where) (P' : K1.Par) (rad : Nat → Nat)
    (hC : K1.condPort P' rad = true) (b : Block A Cl)
    (hS : K1.IsSend P' (fun a => (get a).2.st) b) (base : Nat) (d₁ d₂ : RDT)
    (he₁ : d₁.entry = K1.seedEntry P') (hk₁ : d₁.kind = .seeds) (e : Nat)
    (he : K1.errPort P' rad ≤ e)
    (fOf : F.E.Str → ∀ j, (portOmZ P'.codes (K1.shapeAt P' j) (rad j.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ j, (portOmZ P'.codes (K1.shapeAt P' j) (rad j.val)).Str)
    (hf : ∀ y τ, fOf ((K1.sendPiece (W := W) (F := F) b base d₁ d₂ P'.coordinates e).ior.imp y τ) =
      fIn y τ.1)
    (hT : RowM4 N Mg.more links ps k (K1.layOf P').shapes.size P'.sent.size)
    (hF : FillM4 Cl P P' N Mg ((First.pubSets Mg.more links ps)[k]?.getD []) ps[k]?)
    (hPl : wSitsItem ∈ (First.pubSets Mg.more links ps)[k + 1]?.getD [] →
      planSitsB P P' = true ∧ planSeatB N ps[k]? P' = true)
    (hbase : N.index.1 < base)
    (hyes : ∀ a τ x,
      (K1.sendPiece (W := W) (F := F) b base d₁ d₂ P'.coordinates e).ior.red.out a τ = some x →
      StepM4 Cl P P' (get a.1) (get x.1))
    (hseal : ∀ a τ x, onQ N Mg links ps get k a → (get a.1).2.failed = none →
      (K1.sendPiece (W := W) (F := F) b base d₁ d₂ P'.coordinates e).ior.red.out a τ = some x →
      (∀ j, K1.sampledAt P' j →
        K1.Sealed P'.codes (K1.shapeAt P' j) (rad j.val) (fOf x.2 j) (get x.1).2.st
          ((get x.1).2.st.oracles.size - (K1.shapesOf P').length + j.val)) →
      (wSitsItem ∈ (First.pubSets Mg.more links ps)[k + 1]?.getD [] →
        wSitsB P'.codes P (get x.1).2 = true ∧
          (get x.1).2.book.place[(get x.1).2.st.oracles.size - (K1.shapesOf P').length]? =
            some N.w) →
      Mg.held N.w.1 N.w.2 (get x.1) = true ∧ Mg.noColl N.w.1 N.w.2 (get x.1) (strsOf F x.2))
    (hshown : ∀ a τ x, onQ N Mg links ps get k a → (get a.1).2.failed = none →
      (K1.sendPiece (W := W) (F := F) b base d₁ d₂ P'.coordinates e).ior.red.out a τ = some x →
      Mg.shown N.w.1 N.w.2 (strsOf F x.2)) :
    TiedAt N Mg links ps get k (K1.sendPiece (W := W) (F := F) b base d₁ d₂ P'.coordinates e) := by
  -- what the block makes, where the door's item is open behind
  have key : ∀ a τ x, onQ N Mg links ps get k a → (get a.1).2.failed = none →
      (K1.sendPiece (W := W) (F := F) b base d₁ d₂ P'.coordinates e).ior.red.out a τ = some x →
      wSitsItem ∈ (First.pubSets Mg.more links ps)[k + 1]?.getD [] →
      wSitsB P'.codes P (get x.1).2 = true ∧ wSeatB N.w (get x.1).2 = true ∧
        (get x.1).2.book.place[(get x.1).2.st.oracles.size - (K1.shapesOf P').length]? =
          some N.w := by
    intro a τ x ha hm hx hq
    obtain ⟨_, _, hbk, hQ⟩ := promise_index N Mg links ps get k hT.pinIn a ha hm
    obtain ⟨r₁, r₂, gs, hdec⟩ := (hyes a τ x hx).decide
    have hon := (frontOkB_iff P _ a.2).1 ((hF.frontOk _).1 (hQ _ hT.frontIn).1)
    unfold First.bookAt at hbk
    simp only [Bool.and_eq_true, beq_iff_eq] at hbk
    obtain ⟨⟨b1, b2⟩, _⟩ := hbk
    have hp1 := (planSitsB_iff P P').1 (hPl hq).1
    have hp2 : N.w = _ := eq_of_beq (hPl hq).2
    have hb := atM4_booked hdec
    have hs := atM4_seat hdec b2 hp1.pos
    have hn := hb.newer b2 hp1.pos
    rw [b1, ← hp2] at hs hn
    refine ⟨atM4_sits hdec a.2 hon hp1, hs, ?_⟩
    have hl : (K1.shapesOf P').length = P'.sent.size := by simp [K1.shapesOf]
    rw [hb.msgs, hl, Nat.add_sub_cancel]
    exact hn
  refine K1.send_tied N Mg links ps get k P' rad hC b hS base d₁ d₂ he₁ hk₁ e he fOf fIn hf
    (fun x => Mg.held N.w.1 N.w.2 (get x.1) = true ∧
      Mg.noColl N.w.1 N.w.2 (get x.1) (strsOf F x.2))
    (fun a τ x ha hm hx hS' => hseal a τ x ha hm hx hS' fun hq =>
      ⟨(key a τ x ha hm hx hq).1, (key a τ x ha hm hx hq).2.2⟩) ?_ ?_ ?_ ?_ ?_
  · -- the promise behind
    intro a τ x ha hm hx hn
    obtain ⟨hd, hin, hh, hs, hc⟩ :=
      promise_front N Mg links ps get k (idx_of_pin N hT.pinIn) a ha hm
    obtain ⟨hii, hit, hbk, hQ⟩ := promise_index N Mg links ps get k hT.pinIn a ha hm
    have hfr : Mg.pub .frontOk (get a.1) = true := (hQ _ hT.frontIn).1
    have hst := hyes a τ x hx
    have hold := oldKept_out _ hx hbase
    obtain ⟨r₁, r₂, gs, hdec⟩ := hst.decide
    obtain ⟨⟨o, ho⟩, hw, _, _, _⟩ := atM4_rec hdec
    have hon := (frontOkB_iff P _ a.2).1 ((hF.frontOk _).1 hfr)
    obtain ⟨hE, hFr⟩ := atM4_laid hdec a.2 x.2 hon
    have hFrB := (frontOkB_iff P _ x.2).2 hFr
    have hEB := (evalLaidB_iff P (get x.1).2).2 hE
    have hbk' := hbk
    unfold First.bookAt at hbk'
    simp only [Bool.and_eq_true, beq_iff_eq] at hbk'
    obtain ⟨⟨b1, b2⟩, b3⟩ := hbk'
    have hmk : wSitsItem ∈ (First.pubSets Mg.more links ps)[k + 1]?.getD [] →
        wSitsB P'.codes P (get x.1).2 = true ∧ wSeatB N.w (get x.1).2 = true := fun hq =>
      ⟨(key a τ x ha hm hx hq).1, (key a τ x ha hm hx hq).2.1⟩
    refine ⟨hF.decodes _ _ _ _ hst hold.1 hd, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
    · simp only [Bool.and_eq_true]
      refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, hF.inOrder _ _ hst hin⟩, ?_⟩, ?_⟩
      · cases hp : ps[k + 1]? with
        | none => simp [First.shapeAt, First.standOf, S.noneWaits, ho, hw]
        | some p' =>
          simp [First.shapeAt, First.standOf, S.noneWaits, S.link?, ho, hw, hT.next p' hp]
      · show First.rowsHeld N (openAt links ps (k + 1)) (get x.1).2 = true
        unfold First.rowsHeld
        rw [hT.noRows]
        rfl
      · show First.membersHeld N (openAt links ps (k + 1)) (get x.1).2 = true
        unfold First.membersHeld
        rw [hT.noRows]
        rfl
      · refine List.all_eq_true.2 fun q hq => ?_
        rcases List.mem_append.1 hq with hq | hq
        · rcases hT.pubs q hq with rfl | rfl | rfl | hq'
          · exact (hF.frontOk _).2 hFrB
          · exact hF.evalLaid _ hEB
          · exact (hF.wSits _).2 (hmk hq)
          · exact hF.pubRide _ _ q hst (fun q' h' => (hQ q' h').1) hbk hq'
        · rcases hT.tied q hq with rfl | rfl
          · exact hF.indexIs _ _ hst hii
          · exact hF.indexThere _ _ hst hit
      · have hb := atM4_booked hdec
        unfold First.bookAt
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact ⟨⟨by rw [hb.trees, b1, hT.trees], hb.full b2⟩, by rw [hb.msgs, b3, hT.msgs]⟩
    · refine List.all_eq_true.2 fun t ht => ?_
      rcases hT.two t ht with rfl | rfl
      · exact hF.held _ _ hst hh
      · exact hn.1
    · intro t ht
      rcases hT.two t ht with rfl | rfl
      · exact ⟨hF.shown _ _ hold hs, hF.noColl _ _ _ _ hst hh hbk hold hc⟩
      · exact ⟨hshown a τ x ha hm hx, hn.2⟩
    · intro q hq
      rcases hT.pubs q hq with rfl | rfl | rfl | hq'
      · exact hF.frontOkP _ hFrB
      · exact hF.evalLaidP _ hEB
      · exact hF.wSitsP _ (hmk hq).1 (hmk hq).2
      · exact hF.pubPRide _ _ q hst (fun q' h' => (hQ q' h').1) hbk hq' (hQ q hq').2
  · -- what the row opens goes back to what it closes
    intro a τ x w ha hm hx hO i hi
    have hst := hyes a τ x hx
    obtain ⟨hii, hit, hbk, hQ⟩ := promise_index N Mg links ps get k hT.pinIn a ha hm
    rcases hT.ins i hi with rfl | rfl | rfl
    · exact hF.pileOne _ _ _ _ w hst (fun q hq => (hQ q hq).1) hii hit hbk
        (hO .pileOne hT.outs.1)
    · exact hF.pinWBack _ _ _ _ w hst (oldKept_out _ hx hbase).1 (hO .pinW hT.outs.2)
    · exact hm
  · -- the rider
    intro a τ x w i ha hm hx _ hall hi hin
    obtain rfl := hT.rider i hi hin
    obtain ⟨_, _, hh, _, _⟩ :=
      promise_front N Mg links ps get k (idx_of_pin N hT.pinIn) a ha hm
    obtain ⟨_, _, hbk, _⟩ := promise_index N Mg links ps get k hT.pinIn a ha hm
    exact hF.pinIBack _ _ _ _ w (hyes a τ x hx) hh hbk (oldKept_out _ hx hbase)
      (hall .pinI (Or.inl ⟨hi, hin⟩))
  · -- a mark stays
    intro a τ x hx hm
    obtain ⟨r₁, r₂, gs, hdec⟩ := (hyes a τ x hx).decide
    rw [(atM4_rec hdec).2.2.1]
    exact hm
  · -- "decodes" rides
    intro a τ x hx hd
    exact hF.decodes _ _ _ _ (hyes a τ x hx) (oldKept_out _ hx hbase).1 hd

/-- **THE FIVE TIES AT A BLOCK AS A CHAIN HOLDS IT**, where the chain's record is the carried record
itself and the public part is one value z. -/
theorem w_tied_seat (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place) (z : Pp)
    (k : ℕ) (P : Where) (P' : K1.Par) (rad : Nat → Nat) (hC : K1.condPort P' rad = true)
    (c : Block S Cl) (hc : c.UnderR (atM4 P (K1.sendAtS P'))) (base : Nat) (d₁ d₂ : RDT)
    (he₁ : d₁.entry = K1.seedEntry P') (hk₁ : d₁.kind = .seeds) (e : Nat)
    (he : K1.errPort P' rad ≤ e)
    (fOf : F.E.Str → ∀ j, (portOmZ P'.codes (K1.shapeAt P' j) (rad j.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ j, (portOmZ P'.codes (K1.shapeAt P' j) (rad j.val)).Str)
    (hf : ∀ y τ, fOf ((K1.sendPiece (W := W) (F := F) c base d₁ d₂ P'.coordinates e).ior.imp y τ) =
      fIn y τ.1)
    (hT : RowM4 N Mg.more links ps k (K1.layOf P').shapes.size P'.sent.size)
    (hF : FillM4 Cl P P' N Mg ((First.pubSets Mg.more links ps)[k]?.getD []) ps[k]?)
    (hPl : wSitsItem ∈ (First.pubSets Mg.more links ps)[k + 1]?.getD [] →
      planSitsB P P' = true ∧ planSeatB N ps[k]? P' = true)
    (hbase : N.index.1 < base)
    (hseal : ∀ a τ x, onQ N Mg links ps (fun s : S => (z, s)) k a → a.1.failed = none →
      (K1.sendPiece (W := W) (F := F) c base d₁ d₂ P'.coordinates e).ior.red.out a τ = some x →
      (∀ j, K1.sampledAt P' j →
        K1.Sealed P'.codes (K1.shapeAt P' j) (rad j.val) (fOf x.2 j) x.1.st
          (x.1.st.oracles.size - (K1.shapesOf P').length + j.val)) →
      (wSitsItem ∈ (First.pubSets Mg.more links ps)[k + 1]?.getD [] →
        wSitsB P'.codes P x.1 = true ∧
          x.1.book.place[x.1.st.oracles.size - (K1.shapesOf P').length]? = some N.w) →
      Mg.held N.w.1 N.w.2 (z, x.1) = true ∧ Mg.noColl N.w.1 N.w.2 (z, x.1) (strsOf F x.2))
    (hshown : ∀ a τ x, onQ N Mg links ps (fun s : S => (z, s)) k a → a.1.failed = none →
      (K1.sendPiece (W := W) (F := F) c base d₁ d₂ P'.coordinates e).ior.red.out a τ = some x →
      Mg.shown N.w.1 N.w.2 (strsOf F x.2)) :
    TiedAt N Mg links ps (fun s : S => (z, s)) k
      (K1.sendPiece (W := W) (F := F) c base d₁ d₂ P'.coordinates e) :=
  w_tied N Mg links ps _ k P P' rad hC c (K1.isSend_under P' _ hc.2 (isSend_atM4 P P')) base d₁ d₂
    he₁ hk₁ e he fOf fIn hf hT hF hPl hbase
    (fun a τ x hx => by
      obtain ⟨rs, cols, n, hst⟩ := piece_step _ hx
      exact ⟨rfl, _, rs, cols, n, step_under hc hst⟩)
    hseal hshown

end

/-! ## 3 `RowM4` as a test with code, and members -/

/-- No pin with a sample but the index masks' and W's. -/
def twoPins : Item → Bool
  | .pin _ _ => false
  | .pinKept _ => false
  | _ => true

/-- **`RowM4` as a test with code.** -/
def rowM4B (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  ((insL links ps k).all fun i => i == .pileOne || i == .pinW || i == .unmarked) &&
    ((outsL links ps k).contains .pileOne && (outsL links ps k).contains .pinW) &&
    ((openL (insL links ps) (outsL links ps) (First.start links) k).all fun i =>
      (insL links ps k).contains i || i == .pinI) &&
    (ps[k + 1]?.all fun p' => First.standAt links p' == .mem) &&
    (openAt links ps k).contains .pinI &&
    (openAt links ps (k + 1)).all twoPins &&
    (First.rowSegs (openAt links ps (k + 1))).isEmpty &&
    ((First.pubSets M links ps)[k]?.getD []).contains .frontOk &&
    (((First.pubSets M links ps)[k + 1]?.getD []).all fun q =>
      q == .frontOk || q == .evalLaid || q == wSitsItem ||
        ((First.pubSets M links ps)[k]?.getD []).contains q) &&
    ((First.pubOfItems (openAt links ps (k + 1))).all fun q => q == .indexIs || q == .indexThere)

/-- **A yes of the test gives what is asked of the table**, at every N whose numbers of trees and
messages grow at the block by nT and nM. -/
theorem rowM4_of_test (M : More) (links : List ModelPart) (ps : List Place) (k nT nM : ℕ)
    (h : rowM4B M links ps k = true) (N : Numbers)
    (hT : N.treesAt ps[k + 1]? = N.treesAt ps[k]? + nT)
    (hM : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]? + nM) : RowM4 N M links ps k nT nM := by
  unfold rowM4B at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2a, h2b⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_, List.contains_iff_mem.1 h5, ?_, ?_, ?_, ?_, ?_, hT, hM⟩
  · intro i hi
    have := List.all_eq_true.1 h1 i hi
    simpa [Bool.or_eq_true, or_assoc] using this
  · exact List.contains_iff_mem.1 h2a
  · exact List.contains_iff_mem.1 h2b
  · intro i hi hin
    have hm := (openIsList Item (insL links ps) (outsL links ps) (First.start links) k i).1 hi
    have := List.all_eq_true.1 h3 i hm
    rcases Bool.or_eq_true _ _ ▸ this with h | h
    · exact absurd (List.contains_iff_mem.1 h) hin
    · exact eq_of_beq h
  · intro p' hp'
    rw [hp'] at h4
    exact eq_of_beq h4
  · intro t ht
    obtain ⟨i, hi, hti⟩ := List.mem_flatMap.1 ht
    have hb := List.all_eq_true.1 h6 i hi
    cases i with
    | pinI => exact Or.inl (List.mem_singleton.1 hti)
    | pinV => exact Or.inr (List.mem_singleton.1 hti)
    | pin m u => exact absurd (show false = true from hb) Bool.false_ne_true
    | pinKept m => exact absurd (show false = true from hb) Bool.false_ne_true
    | _ => exact absurd (show t ∈ ([] : List (ℕ × ℕ)) from hti) List.not_mem_nil
  · exact List.isEmpty_iff.1 h7
  · exact List.contains_iff_mem.1 h8
  · intro q hq
    have := List.all_eq_true.1 h9 q hq
    simp only [Bool.or_eq_true] at this
    rcases this with ((e | e) | e) | e
    · exact Or.inl (eq_of_beq e)
    · exact Or.inr (Or.inl (eq_of_beq e))
    · exact Or.inr (Or.inr (Or.inl (eq_of_beq e)))
    · exact Or.inr (Or.inr (Or.inr (List.contains_iff_mem.1 e)))
  · intro q hq
    rcases Bool.or_eq_true _ _ ▸ List.all_eq_true.1 h10 q hq with e | e
    · exact Or.inl (eq_of_beq e)
    · exact Or.inr (eq_of_beq e)

set_option maxRecDepth 1000000 in
/-- **A member of the test** (the numbers' half is a premise), at the door's filling: the small
list; the block has the number 76 of 78. -/
theorem rowM4_small (N : Numbers) (nT nM : ℕ)
    (hT : N.treesAt (First.flatPlaces true linksSmall true)[76 + 1]? =
      N.treesAt (First.flatPlaces true linksSmall true)[76]? + nT)
    (hM : N.msgsAt (First.flatPlaces true linksSmall true)[76 + 1]? =
      N.msgsAt (First.flatPlaces true linksSmall true)[76]? + nM) :
    RowM4 N wSitsMore linksSmall (First.flatPlaces true linksSmall true) 76 nT nM :=
  rowM4_of_test _ _ _ _ _ _ (by decide +kernel) N hT hM

set_option maxRecDepth 1000000 in
/-- **A member of the test** (the numbers' half is a premise): the full list; the number 356 of 358.
-/
theorem rowM4_full (N : Numbers) (nT nM : ℕ)
    (hT : N.treesAt (First.flatPlaces true linksFull true)[356 + 1]? =
      N.treesAt (First.flatPlaces true linksFull true)[356]? + nT)
    (hM : N.msgsAt (First.flatPlaces true linksFull true)[356 + 1]? =
      N.msgsAt (First.flatPlaces true linksFull true)[356]? + nM) :
    RowM4 N wSitsMore linksFull (First.flatPlaces true linksFull true) 356 nT nM :=
  rowM4_of_test _ _ _ _ _ _ (by decide +kernel) N hT hM

set_option maxRecDepth 1000000 in
/-- A try: at K13's own block the test says no. -/
theorem rowM4B_other :
    rowM4B wSitsMore linksSmall (First.flatPlaces true linksSmall true) 75 = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- K13's own row's member at the same filling: the small list. -/
theorem rowM3_small_w (N : Numbers)
    (hT : N.treesAt (First.flatPlaces true linksSmall true)[75 + 1]? =
      N.treesAt (First.flatPlaces true linksSmall true)[75]?)
    (hM : N.msgsAt (First.flatPlaces true linksSmall true)[75 + 1]? =
      N.msgsAt (First.flatPlaces true linksSmall true)[75]?) :
    RowM3 N wSitsMore linksSmall (First.flatPlaces true linksSmall true) 75 :=
  rowM3_of_test _ _ _ _ (by decide +kernel) N hT hM

set_option maxRecDepth 1000000 in
/-- The full list. -/
theorem rowM3_full_w (N : Numbers)
    (hT : N.treesAt (First.flatPlaces true linksFull true)[355 + 1]? =
      N.treesAt (First.flatPlaces true linksFull true)[355]?)
    (hM : N.msgsAt (First.flatPlaces true linksFull true)[355 + 1]? =
      N.msgsAt (First.flatPlaces true linksFull true)[355]?) :
    RowM3 N wSitsMore linksFull (First.flatPlaces true linksFull true) 355 :=
  rowM3_of_test _ _ _ _ (by decide +kernel) N hT hM

set_option maxRecDepth 1000000 in
/-- **Which public items ride**, at that filling: in front of K13's block none is open; in front of
W's commitment K13's own item alone: so `pubRide` and `pubPRide` are idle AT THAT FILLING. At a
filling with other kinds' items more rides: see Johnson/Desc/K13/Law/IndexSeatAtTable.lean. -/
theorem open_in_front :
    (First.pubSets wSitsMore linksSmall (First.flatPlaces true linksSmall true))[75]?.getD [] = [] ∧
      (First.pubSets wSitsMore linksFull (First.flatPlaces true linksFull true))[355]?.getD [] =
        [] ∧
      (First.pubSets wSitsMore linksSmall (First.flatPlaces true linksSmall true))[76]?.getD [] =
        [.frontOk] ∧
      (First.pubSets wSitsMore linksFull (First.flatPlaces true linksFull true))[356]?.getD [] =
        [.frontOk] := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The table's own test on a filling of its door says yes**, at both lists; and the item is open
at the chain's last border. -/
theorem wSits_fit :
    First.pubFit wSitsMore linksSmall (First.flatPlaces true linksSmall true) = true ∧
      First.pubFit wSitsMore linksFull (First.flatPlaces true linksFull true) = true ∧
      ((First.pubSets wSitsMore linksSmall (First.flatPlaces true linksSmall true))[78]?.getD
        []).contains wSitsItem = true ∧
      ((First.pubSets wSitsMore linksFull (First.flatPlaces true linksFull true))[358]?.getD
        []).contains wSitsItem = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A try: a filling that has the item asked at K13's block, in front of its maker, rings. -/
theorem wSits_asked_early :
    First.pubFit (wSitsMore.merge
      { rows := fun _ p => if p.kind == .K13 then { asks := [(none, "K13.wSits")] } else {} })
      linksSmall (First.flatPlaces true linksSmall true) = false := by
  decide +kernel

end VerifiableInference.Desc.K13.Law
