-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/AtReachFits.lean: A CHECK BY LEAN: the structure FoldFacts
(Johnson/Desc/First/FoldFacts.lean) is imported and a value of it
is built: TWENTY-FOUR OF ITS 26 FIELDS STAND AS TERMS: eighteen theorems of Johnson/IMR/ and six of
three other folders. Its main theorem is typed by program.
WHY. The payers do not import the structure: that each statement's end is its field's type would be
held by reading or by programs that compare texts. Here Lean accepts a field's term only at the
field's own type (up to unfolding definitions: frameIs_paid writes momentW | shiftW where the field
writes momentAt | shiftAt IM.linksW).
WHAT IS SAID. foldFacts_of_rest: in the goals' scope (hS, hR), at an opening O, under hF, hRch, hB,
hLd and hD, and from two premises roomFull | roomEarlyFull: a value of FoldFacts Rch at_ d reqW
IM.linksW IM.placesW at d := { ft := 0, sent := sentAt Z, groupAt := fun m => m, ownAt | keptAt :=
FillSent.ownAt | keptAt Z.first.shape (N.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder))
IM.linksW IM.placesW built, L := Ld, M := K12.Door.msgsOfChain Z.made.proof.1, and free letters at
free0 · fvs } and reqW := fun p => Verify.words32 p.request; N and built are free letters too.
THE TWENTY-FOUR. Johnson/IMR/'s: the twelve of AtReach.lean · groupIs_field (GroupField.lean) ·
frameIs_paid (Johnson/IMR/FramePaid.lean) · IM.seatsCarried_field · IM.msgShapes_field
(Johnson/IMR/SeatsField.lean) ·
rowsSent_field (RowsSent.lean; hBook by bookHas_fold) · IM.replyNat_field
(ReplyNatField.lean, over replyNat_of_tokSmall, Johnson/Desc/Kinds/Law/ReplyNat.lean). OTHER FILES':
pileMasks · pileWithin · oneRow: LPFK9.‹field›_field_at
(Johnson/LPFK9R/ThreeK13Fields.lean): AS THEY LIE · weightsOk · reqIs:
weights_at_open | req_at_open (Johnson/LTPileR/AtGate.lean), each under a one-line fun · tidy:
tidy_at_open (Johnson/Desc/AtSeats/Fit/TidyAtOpen.lean), under a one-line fun.
A FIND ON FORM. weightsOk_field | reqIs_field (Johnson/LTPileR/WeightsReached.lean | ReqSeat.lean)
and tidy_field (Johnson/Desc/AtSeats/Fit/TidyPaid.lean), which bear the fields' names, end in «there
are Z A B c …» from onlineDescription's return: they are no terms at an opening's own letters, and are not
tried as such here; the same folders' forms at an opening are what fits.
room AND roomEarly: A LESSER CHECK. room_field_paid | roomEarly_field_paid
(Johnson/P1L20R/RoomKeepAll.lean) are NOT in this file's closure. The two premises roomFull |
roomEarlyFull are these theorems' ends with two terms replaced by the free letters free0 · fvs
(theirs: K1.free0Of Bs.G₀.first (gpOf Z) · Walk.Seat.fvsOf Z.p.built.links), at their own spelling
of the list of places, flatPlacesOf Sound.linksFull true; Lean checks that such an end gives the
field at IM.placesW (placesW_linksFull, over linksW_full, Johnson/LPFK9R/SubsFull.lean). THAT THE
PREMISES' TEXTS ARE THE THEOREMS' ENDS is a comparison of texts by program, not Lean's word.
WHAT A SPENDER MUST BRING. (a) hD :
ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F (tidy_at_open asks it beside O; IM.Open has no
field that gives it back; whoever has made O by seat_open holds it). (b) reqW is no free letter.
(c) The wrapped form of hRch IS SPENT: by ThreeK13Fields.lean's three and by tidy_at_open.
(d) The seven fields weightsOk · pileMasks · pileWithin · oneRow · tidy · reqIs · replyNat are no
premises. (e) room | roomEarly are asked in RoomKeepAll.lean's spelling of the places.
flat_planOk (Johnson/Desc/AtSeats/FoldFactsPaid.lean) lies in the closure.


BESIDE IT. foldMore_of_slots: a value of the second structure FoldMore
(Johnson/Desc/First/FoldMore.lean) with bookHas := bookHas_field
as a term and slots as a premise in the field's own type. sendsAre_of_madeRow: hB follows from hF
and PlanWritten.madeRow Z = true (Johnson/IMR/FivePinned.lean): madeRow is the stronger premise, so
the main theorem keeps hB. raw_of_below · fold_of_rch · fold_of_below · bookHas_fold: bridges.
What is not claimed. hS, hR, O, hF, hRch, hB, hLd, hD, roomFull and roomEarlyFull are shown nowhere
here; that they can be met together is shown nowhere here: NO MEMBER. At Rch := never every field is
free. That this d is the d of the constant P5J.At.foldD (Johnson/P5J/FoldAt.lean) is not shown.
weightsOk, pileMasks, pileWithin, oneRow, tidy, rowsSent and replyNat read no letter of d: no
negative test bends one for them. No soundness.

-/
import Johnson.IMR.AtReach
import Johnson.IMR.GroupField
import Johnson.IMR.FramePaid
import Johnson.IMR.SeatsField
import Johnson.IMR.RowsSent
import Johnson.IMR.ToldPaid
import Johnson.IMR.FivePinned
import Johnson.IMR.ReplyNatField
import Johnson.LTPileR.AtGate
import Johnson.LPFK9R.ThreeK13Fields
import Johnson.LPFK9R.SubsFull
import Johnson.Desc.AtSeats.Fit.TidyAtOpen
import Johnson.Desc.First.FoldFacts
import Johnson.Desc.First.FoldMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)

variable {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat} {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}

/-- What is reached by the wrapped sub-protocols' steps is reached by their own (reach_raw,
Johnson/Top/H0/Walk/Reach.lean). -/
theorem raw_of_below {X : Type} {Rch : ℕ → X → Prop} {at_ : X → ProofFile.InstPub × S}
    (hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (at_ a)) :
    ∀ k a, Rch k a → Reach 0 c.blocksInOrder (ProofFile.startS Z) k (at_ a) :=
  fun k a h => reach_raw (hRch k a h)

/-- What is reached in AtReach.lean's sense is the end of a fold over the first k
sub-protocols. -/
theorem fold_of_rch {X : Type} {Rch : ℕ → X → Prop} {at_ : X → ProofFile.InstPub × S}
    (hRch : ∀ k a, Rch k a → Reach 0 c.blocksInOrder (ProofFile.startS Z) k (at_ a)) :
    ∀ k a, Rch k a → ∃ rs cols r q,
      foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z (at_ a).1) rs cols = .ok ((at_ a).2, r, q) :=
  fun k a h => let ⟨_, rs, cols, f⟩ := (hRch k a h).fold; ⟨rs, cols, [], [], f⟩

/-- The two together. -/
theorem fold_of_below {X : Type} {Rch : ℕ → X → Prop} {at_ : X → ProofFile.InstPub × S}
    (hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (at_ a)) :
    ∀ k a, Rch k a → ∃ rs cols r q,
      foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z (at_ a).1) rs cols = .ok ((at_ a).2, r, q) :=
  fold_of_rch (raw_of_below hRch)

/-- **As many places in the list of commitment trees as oracle messages, behind the first k
sub-protocols, at every k**: in scope, under the tests on the plan; no fence is asked. By
counts_at_cut_paid (Johnson/IMR/ToldPaid.lean); beyond 358 by IM.fold_whole. -/
theorem bookHas_fold (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {k : ℕ} {z : ProofFile.InstPub} {s : S}
    {rs r : List Fmt.RoundView} {cols q : List VerifiableInference.Desc.OpenedColumn}
    (hf : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z z) rs cols = .ok (s, r, q)) :
    s.book.place.size = s.st.oracles.size := by
  rw [IM.fold_whole hS O k] at hf
  exact (Meaning.Carry.counts_at_cut_paid hS hR O z rs cols _ (Nat.min_le_right _ _)
    (fun b hb => hp b (List.mem_of_mem_take hb)) _ hf).2.1

/-- **The field «bookHas» of the second structure FoldMore** (Johnson/Desc/First/FoldMore.lean), in
its letters: general in Rch and at_. The fence is not spent. NOT A FIELD OF FoldFacts:
foldMore_of_slots, below, lays this end as a term of FoldMore. -/
theorem bookHas_field (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {X : Type} (Rch : ℕ → X → Prop)
    (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → ∃ rs cols r q,
      foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z (at_ a).1) rs cols = .ok ((at_ a).2, r, q)) :
    ∀ k a, Rch k a → (at_ a).2.failed = none →
      (at_ a).2.book.place.size = (at_ a).2.st.oracles.size :=
  fun k a h _ => let ⟨_, _, _, _, f⟩ := hRch k a h; bookHas_fold hS hR O hp f

/-- The written list of places is the list in the spelling in which the two payers of room and
roomEarly (Johnson/P1L20R/RoomKeepAll.lean) end (by linksW_full, Johnson/LPFK9R/SubsFull.lean). -/
theorem placesW_linksFull : IM.placesW = flatPlacesOf Sound.linksFull true := by
  unfold IM.placesW
  rw [LPFK9.linksW_full]

/-- **A value of FoldFacts from the fields that fit:
room and roomEarly from two premises in their payers' own
letters.** -/
theorem foldFacts_of_rest (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    {X : Type} (Rch : ℕ → X → Prop) (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (at_ a))
    (N : Numbers) (built : Array Stages.LinkH)
    (hB : K12.Door.sendsAreB Z.made.proof.1 358 (K12.Door.snAt Z Bs.G₀ IM.placesW) = true)
    {Ld : K12.Door.Laid} (hLd : K12.Door.laidAtCodes Z.first.codes Z.made.proof.1 = some Ld)
    (hD : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (free0 : Nat) (fvs : List Bool)
    (roomFull : ∀ k a p m, Rch k a → (at_ a).2.failed = none →
      (flatPlacesOf Sound.linksFull true)[k]? = some p → p.link = some m → 2 ≤ p.piece →
      Johnson.Desc.First.Walk.Tied.roomIsB free0 fvs m (at_ a).2 = true)
    (roomEarlyFull : ∀ k a p m, Rch k a → (at_ a).2.failed = none →
      (flatPlacesOf Sound.linksFull true)[k]? = some p → p.link = some m → p.piece < 2 → 0 < m →
      Johnson.Desc.First.Walk.Tied.roomIsB free0 fvs m (at_ a).2 = true) :
    FoldFacts Rch at_
    { ft := 0, sent := sentAt Z, groupAt := fun m => m,
      ownAt := FillSent.ownAt Z.first.shape (N.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder))
        IM.linksW IM.placesW built,
      keptAt := FillSent.keptAt Z.first.shape (N.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder))
        IM.linksW IM.placesW built,
      L := Ld, M := K12.Door.msgsOfChain Z.made.proof.1, free0 := free0, fvs := fvs }
    (fun p : ProofFile.InstPub => Verify.words32 p.request) IM.linksW IM.placesW where
  bookInOrder := bookInOrder_field O (flat_planOk O.desc hF) Rch at_ (raw_of_below hRch)
  seatsCarried := IM.seatsCarried_field hS hR O Rch at_ (fold_of_below hRch) hF hB hLd
  bookFits := bookFits_field O (flat_planOk O.desc hF) Rch at_ (raw_of_below hRch)
  msgShapes := IM.msgShapes_field hS hR O Rch at_ (fold_of_below hRch) hF hB
  weightsOk := fun k a h _ =>
    weights_at_open O (flat_planOk O.desc hF) 0 k (at_ a) (raw_of_below hRch k a h)
  pileMasks := LPFK9.pileMasks_field_at Rch at_ hS hR O hRch
  pileWithin := LPFK9.pileWithin_field_at Rch at_ O hF hRch
  oneRow := LPFK9.oneRow_field_at Rch at_ O hF hRch
  tidy := fun k a h hm => tidy_at_open hD hF O k (at_ a) (hRch k a h) hm
  codes := codes_field hS hR O (flat_planOk O.desc hF) Rch at_ (raw_of_below hRch)
  shape := shape_field hS hR O (flat_planOk O.desc hF) Rch at_ (raw_of_below hRch)
  layout := layout_field hS hR O (flat_planOk O.desc hF) Rch at_ (raw_of_below hRch)
  liveShape := liveShape_field hS hR O (flat_planOk O.desc hF) Rch at_ (raw_of_below hRch)
  liveLayout := liveLayout_field hS hR O (flat_planOk O.desc hF) Rch at_ (raw_of_below hRch)
  groups := groups_field hS hR O (flat_planOk O.desc hF) Rch at_ (raw_of_below hRch)
  liveGroups := liveGroups_field hS hR O (flat_planOk O.desc hF) Rch at_ (raw_of_below hRch)
  frameShape := frameShape_field hS hR O (flat_planOk O.desc hF) Rch at_ (raw_of_below hRch)
  frameGroups := frameGroups_field hS hR O (flat_planOk O.desc hF) Rch at_ (raw_of_below hRch)
  ownIs := ownIs_field hS hR O Rch at_ (raw_of_below hRch)
  groupIs := groupIs_field hS hR O Rch at_ (fold_of_below hRch)
  frameIs := frameIs_paid hS hR O (IM.blocksOk_of_planOk O hF) N built Rch at_ (fold_of_below hRch)
  rowsSent := rowsSent_field O (flat_planOk O.desc hF) Rch at_ (fold_of_below hRch) fun k a h =>
    let ⟨_, _, _, _, f⟩ := fold_of_below hRch k a h; bookHas_fold hS hR O (flat_planOk O.desc hF) f
  reqIs := fun k a h hm =>
    req_at_open O (flat_planOk O.desc hF) 0 k (at_ a) (raw_of_below hRch k a h) hm
  replyNat := IM.replyNat_field hS hR O Rch at_ (raw_of_below hRch)
  room := fun k a p m h hm hp => roomFull k a p m h hm (placesW_linksFull ▸ hp)
  roomEarly := fun k a p m h hm hp => roomEarlyFull k a p m h hm (placesW_linksFull ▸ hp)

/-- **The same with the test sendsAreB paid**: under madeRow Z = true in hB's place
(sends_pinned_paid, Johnson/IMR/FivePinned.lean; its premise on the proximity test's plan falls by
IM.hp_of_planOk). madeRow is a STRONGER premise than hB. -/
theorem sendsAre_of_madeRow (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    (hy : VerifiableInference.PlanWritten.madeRow Z = true) :
    K12.Door.sendsAreB Z.made.proof.1 358 (K12.Door.snAt Z Bs.G₀ IM.placesW) = true :=
  IM.sends_pinned_paid O hy (IM.hp_of_planOk hS hR O (IM.blocksOk_of_planOk O hF))

/-- **A value of the second structure FoldMore** (Johnson/Desc/First/FoldMore.lean): its field
bookHas stands as a term (bookHas_field); its field slots is a premise in the field's own type. -/
theorem foldMore_of_slots (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    {X : Type} (Rch : ℕ → X → Prop) (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (at_ a))
    (nsAt : Nat → Nat)
    (slots' : ∀ k a p m G, Rch k a → (at_ a).2.failed = none → IM.placesW[k]? = some p →
      p.link = some m → (at_ a).2.fork? = some G → G.ns = nsAt m ∧ G.LS.size = G.ns) :
    FoldMore Rch at_ nsAt IM.placesW where
  bookHas := bookHas_field hS hR O (flat_planOk O.desc hF) Rch at_ (fold_of_below hRch)
  slots := slots'

end Meaning.K2

#print axioms Meaning.K2.raw_of_below
#print axioms Meaning.K2.fold_of_rch
#print axioms Meaning.K2.fold_of_below
#print axioms Meaning.K2.bookHas_fold
#print axioms Meaning.K2.bookHas_field
#print axioms Meaning.K2.placesW_linksFull
#print axioms Meaning.K2.foldFacts_of_rest
#print axioms Meaning.K2.sendsAre_of_madeRow
#print axioms Meaning.K2.foldMore_of_slots
