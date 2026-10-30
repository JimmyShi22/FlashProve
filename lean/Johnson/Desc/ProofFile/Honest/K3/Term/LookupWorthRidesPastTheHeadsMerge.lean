-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT ANY FILLING: the first chain's letters L (its Script, prover's sides, rider and keeps), the
clause Said, the public data X, the link and the border are variables; in section 5 the letters are
`lettersHead`'s (Honest/Thread/FirstHead.lean), with its Script, rider and keeps still variables.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupWorthRidesPastTheHeadsMerge.lean: the honest side of the
kind "lookup" (K3): the two open items worth "planes" and worth "keys" of a link's lookup on the
digits pass over a member that leaves the link's tail as it was and only adds to the ledger
(`RidesPastAtS`, Honest/Thread/SharesS.lean), IF in front of that member what the lookup has heard
stands for some rounds at the ledger in hand (`K3Stands`, Johnson/Top/H/K3RowOut.lean). Theorems,
each conditional; no definition.

Why. The head's merge (K11) stands between the head's lookup on the digits, which opens the two
items, and the members that shut them. Its writers ask for the two items' passing.

Why the further premise. Each item says: "at all rounds for which the heard record, with the ledger
in hand, holds the end values (`Fo.HeardIs`, OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean), the claims
are 0". `Fo.HeardIs` stands on the left of the implication, and it passes from a ledger to a LATER
one (`heardIsLater`, Johnson/Top/H/K3LeftLater.lean): so the library's own direction for the items
is from the later ledger to the earlier (`k3OutBack`, there). Here the other direction is wanted.
Four fields of `Fo.HeardIs` name the ledger, each through a sentence on all later ledgers
(`Fo.FormIs`, `Fo.RowIs`, OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean). Where such a sentence holds at
the earlier ledger of SOME target and sparse form, and at the later ledger of others, the two
readings agree at the later ledger at every mask row, and at the mask row 0 the targets agree: so
the sentence holds at the earlier ledger of the others too.

What is shown.
  `sparseFormAtZeroEntriesIsZero`   a sparse form at the entries that are all 0 is 0
  `formReadingGoesBackWhereItStands`, `rowReadingGoesBackWhereItStands`   the step above, for
      `Fo.FormIs` and `Fo.RowIs`
  `heardRecordGoesBackWhereItStands`   the same for `Fo.HeardIs`
  `planesSentenceGoesForwardWhereTheRecordStands`, `keysSentenceGoesForwardWhereTheRecordStands`
      `K3OutPlanes`, `K3OutKeys` (Johnson/Top/H/K3RowOut.lean) pass to a later ledger
  `digitsWorthGoesForward`   the digits' arm of the field worth (`worthDig`,
      Johnson/Desc/First/Look/K3FillWorth.lean) passes from a state to another
  `lookupWorthRidesPastAMemberThatExtendsTheLedger`   `RidesPastAtS` at the two items
  `lookupWorthRidesPastAMemberFromTheRider`   the same, with the further premise taken from a clause
      of the thread's rider (`StandsHere`, Honest/K3/Law/Thread/LaysStands.lean)
  `heardShapeIsThePlansWhereThePromiseBehindTheLookupIsOpen`   where the public item lookOut of the
      lookup is open at the border, the heard record's shape is the shape of the item's sentence
  `lookupWorthRidesPastAMemberFromTheRiderAndThePromise`   the last but one, with
      heardShapeIsThePlans paid by the last
  `promiseBehindTheHeadsDigitsIsOpenAtTheMerge`   at the full size's lists the public item
      lookOut 24 8 is open at border 346; `promiseBehindTheHeadsDigitsIsNotOpenInFrontOfTheLookup`:
      a control: at border 345 it is not
  `lookupWorthRidesPastTheHeadsMerge`   at `lettersHead`'s thread: `RidesPastAtS` at border 346 at
      worth 24 8 "planes" and worth 24 8 "keys"

Hypotheses that remain, in the last two.
  tableSaysTheLookupsWorth: the table of joints says at the lookups' pieces what the lookups' layer
    says (`K3At`, Johnson/Desc/First/Look/K3At.lean), at every input.
  publicDataHoldTheDigitsPlace, pieceIsTheDigitsPiece: the public data hold the link's place on the
    digits; the item's piece is that lookup's.
  keepsLeavesTheTailAndExtendsTheLedger: what the member's clause of keeps gives. For the files on
    that member to show.
  heardRecordStandsInFront: from the thread's relation in front of the member, the state holds a
    ledger and a heard record, and these stand for some rounds, at the item's own shape, number 5
    and first slot. In the last theorem: riderHoldsThatTheHeardRecordStands and
    heardShapeIsThePlans in its place.
  promiseSaysTheLookupsTests, promiseBehindTheLookupIsOpen: (in section 4's last two) `K3At` at the
    meaning of which the promise's public fields are read; the public item lookOut of the link's
    lookup on the digits is open at the border (a test on the lists of links and places).
  In section 5: the library's hypothesis `P5J.AtMgA`; publicDataHoldTheDigitsPlace at link 24;
    keepsLeavesTheTailAndExtendsTheLedger and riderHoldsThatTheHeardRecordStands at border 346. The
    others are paid there.

Limits. Nothing here shows that a thread's rider has such a clause, nor that a member's keeps gives
what is asked. No instance of these hypotheses is exhibited in this file. On the digits alone.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Top.H.K3LeftLater
import Johnson.Desc.First.Look.K3At
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.Desc.First.Att.Door.ShapeSame
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.ProofFile.Honest.Thread.FormLaw
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LaysStands
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeAtLetters
import Johnson.Desc.Sound.MgAt.K3At
import Johnson.Desc.Sound.MgBase
import Johnson.P5J.K03RidesDigAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (Aff Fork Reading HTailF2)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (Item Pub pubSets)
open VerifiableInference.Desc.First.Look (Sent digAt placeAt k3OnOutAt)
open VerifiableInference.Desc.K3 (k3OnOut heardAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (K3At K3Letters K3Stands K3OutPlanes K3OutKeys K3WorthPlanes
        K3WorthKeys worthDig worthK3_digits)
open ProofFile.Honest.FirstThread (Letters thr_pub)
open ProofFile.Honest.K3.Law.AtThr (StandsHere)

local notation "FS" => VerifiableInference.Desc.First.S
local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place
local notation "pieceOf" => VerifiableInference.Desc.K3.pieceAt

/-! ## 1 The heard record, from a later ledger to an earlier one at which it stands -/

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- A sparse form at the entries that are all 0 is 0. -/
theorem sparseFormAtZeroEntriesIsZero (sparseForm : List (_root_.Fo.Pl × K)) :
    _root_.Fo.evalL (_root_.Fo.muOf (fun _ => (0 : K))) sparseForm = 0 := by
  have everyEntryIsZero : ∀ place : _root_.Fo.Pl, _root_.Fo.muOf (fun _ => (0 : K)) place = 0 :=
    fun place => by cases place <;> rfl
  unfold _root_.Fo.evalL
  refine List.sum_eq_zero fun summand isSummand => ?_
  obtain ⟨term, -, rfl⟩ := List.mem_map.1 isSummand
  simp only [everyEntryIsZero, mul_zero]

/-- **A form's reading at a later ledger holds at an earlier one at which the form has some
reading.** -/
theorem formReadingGoesBackWhereItStands {earlier later : Fork} {form : Aff}
    {someTarget target : K} {someSparseForm sparseForm : List (_root_.Fo.Pl × K)}
    (ledgerIsLater : _root_.Fo.Later earlier later)
    (standsAtTheEarlier : _root_.Fo.FormIs ρ earlier form someTarget someSparseForm)
    (holdsAtTheLater : _root_.Fo.FormIs ρ later form target sparseForm) :
    _root_.Fo.FormIs ρ earlier form target sparseForm := by
  have readingsAgree : ∀ mask : ℕ → K,
      someTarget - _root_.Fo.evalL (_root_.Fo.muOf mask) someSparseForm =
        target - _root_.Fo.evalL (_root_.Fo.muOf mask) sparseForm := fun mask =>
    ((standsAtTheEarlier later ledgerIsLater).2 mask (fun _ _ _ => 0)).symm.trans
      ((holdsAtTheLater later (_root_.Fo.Later.refl later)).2 mask (fun _ _ _ => 0))
  have targetsAgree : someTarget = target := by
    have atZero := readingsAgree (fun _ => 0)
    rw [sparseFormAtZeroEntriesIsZero, sparseFormAtZeroEntriesIsZero, sub_zero, sub_zero] at atZero
    exact atZero
  intro G isLater
  exact ⟨fun x isPublic => ((standsAtTheEarlier G isLater).1 x isPublic).trans targetsAgree,
    fun mask entry => ((standsAtTheEarlier G isLater).2 mask entry).trans (readingsAgree mask)⟩

/-- **The same for a claim row.** -/
theorem rowReadingGoesBackWhereItStands {earlier later : Fork} {row : Aff}
    {someRow flatRow : TwV.SRow _root_.Fo.Pl K}
    (ledgerIsLater : _root_.Fo.Later earlier later)
    (standsAtTheEarlier : _root_.Fo.RowIs ρ earlier row someRow)
    (holdsAtTheLater : _root_.Fo.RowIs ρ later row flatRow) :
    _root_.Fo.RowIs ρ earlier row flatRow :=
  fun G isLater mask entry => (standsAtTheEarlier G isLater mask entry).trans
    ((standsAtTheEarlier later ledgerIsLater mask (fun _ _ _ => 0)).symm.trans
      (holdsAtTheLater later (_root_.Fo.Later.refl later) mask (fun _ _ _ => 0)))

/-- **The heard record holds at the earlier ledger whatever end values it holds at the later one, if
it holds some end values at the earlier one.** -/
theorem heardRecordGoesBackWhereItStands {heard : OnBytes.Model.Forest.Heard}
    {earlier later : Fork} {someEnds ends : _root_.Fo.Ends K}
    (ledgerIsLater : _root_.Fo.Later earlier later)
    (standsAtTheEarlier : _root_.Fo.HeardIs ρ heard earlier someEnds)
    (holdsAtTheLater : _root_.Fo.HeardIs ρ heard later ends) :
    _root_.Fo.HeardIs ρ heard earlier ends :=
  { holdsAtTheLater with
    rows := fun i isRow => rowReadingGoesBackWhereItStands ρ ledgerIsLater
      (standsAtTheEarlier.rows i isRow) (holdsAtTheLater.rows i isRow)
    lvStart := formReadingGoesBackWhereItStands ρ ledgerIsLater standsAtTheEarlier.lvStart
      holdsAtTheLater.lvStart
    sBitAt := formReadingGoesBackWhereItStands ρ ledgerIsLater standsAtTheEarlier.sBitAt
      holdsAtTheLater.sBitAt
    cEnd := formReadingGoesBackWhereItStands ρ ledgerIsLater standsAtTheEarlier.cEnd
      holdsAtTheLater.cEnd }

/-! ## 2 Two sentences of the row out, from a ledger at which the record stands to a later one -/

variable (shape : FoNums.Sh) (lm first : ℕ) (ν : _root_.Fo.Pl → K) (keyVectors : ℕ → ℕ → K)

/-- **Planes-at-points passes to a later ledger.** -/
theorem planesSentenceGoesForwardWhereTheRecordStands {heard : OnBytes.Model.Forest.Heard}
    {earlier later : Fork} (ledgerIsLater : _root_.Fo.Later earlier later)
    (standsAtTheEarlier : K3Stands shape lm first ρ heard earlier)
    (holdsAtTheEarlier : K3OutPlanes shape lm first ν ρ heard earlier) :
    K3OutPlanes shape lm first ν ρ heard later :=
  fun rounds holdsAtTheLater => standsAtTheEarlier.elim fun _ someEndsHold =>
    holdsAtTheEarlier rounds
      (heardRecordGoesBackWhereItStands ρ ledgerIsLater someEndsHold holdsAtTheLater)

/-- **Keys-at-points passes to a later ledger.** -/
theorem keysSentenceGoesForwardWhereTheRecordStands {heard : OnBytes.Model.Forest.Heard}
    {earlier later : Fork} (ledgerIsLater : _root_.Fo.Later earlier later)
    (standsAtTheEarlier : K3Stands shape lm first ρ heard earlier)
    (holdsAtTheEarlier : K3OutKeys shape lm first ν keyVectors ρ heard earlier) :
    K3OutKeys shape lm first ν keyVectors ρ heard later :=
  fun rounds holdsAtTheLater => standsAtTheEarlier.elim fun _ someEndsHold =>
    holdsAtTheEarlier rounds
      (heardRecordGoesBackWhereItStands ρ ledgerIsLater someEndsHold holdsAtTheLater)

end

/-! ## 3 The digits' arm of the field worth, from a state to another -/

section
variable {Cells Tok : Type} (D : Sent) (Lk : K3Letters Cells Tok)

/-- **The digits' arm at "planes" or "keys" passes from a state to another** at which the link's
tail is the same and the ledger a later one, if at the first state the heard record stands for some
rounds. -/
theorem digitsWorthGoesForward (x : PlaceL) (tl : HTailF2) {what : String}
    (whatIsPlanesOrKeys : what = "planes" ∨ what = "keys") {front behind : FS}
    (witness : Wit Cells Tok MsgT) (otherwiseInFront otherwiseBehind : Prop)
    (tailStays : behind.tl? = front.tl?)
    (ledgerExtends : ∀ F, front.fork? = some F →
      ∃ F', behind.fork? = some F' ∧ _root_.Fo.Later F F')
    (heardRecordStands : ∃ F g, front.fork? = some F ∧ front.tl?.bind (·.heard) = some g ∧
      K3Stands tl.f9 5 x.F.next Reading.gl g F)
    (holdsInFront : worthDig D Lk x tl what front witness otherwiseInFront) :
    worthDig D Lk x tl what behind witness otherwiseBehind := by
  obtain ⟨F, g, ledgerInFront, heardInFront, stands⟩ := heardRecordStands
  obtain ⟨F', ledgerBehind, isLater⟩ := ledgerExtends F ledgerInFront
  rcases whatIsPlanesOrKeys with rfl | rfl
  · unfold worthDig at holdsInFront ⊢
    rw [if_pos rfl] at holdsInFront ⊢
    intro g₂ F₂ ledgerRead heardRead
    obtain rfl : F' = F₂ := Option.some.inj (ledgerBehind.symm.trans ledgerRead)
    have heardSame : front.tl?.bind (·.heard) = some g₂ := by
      rw [← tailStays]
      exact heardRead
    obtain rfl : g = g₂ := Option.some.inj (heardInFront.symm.trans heardSame)
    exact planesSentenceGoesForwardWhereTheRecordStands Reading.gl _ _ _ _ isLater stands
      (holdsInFront g F ledgerInFront heardInFront)
  · unfold worthDig at holdsInFront ⊢
    rw [if_neg (by decide), if_pos rfl] at holdsInFront ⊢
    intro g₂ F₂ ledgerRead heardRead
    obtain rfl : F' = F₂ := Option.some.inj (ledgerBehind.symm.trans ledgerRead)
    have heardSame : front.tl?.bind (·.heard) = some g₂ := by
      rw [← tailStays]
      exact heardRead
    obtain rfl : g = g₂ := Option.some.inj (heardInFront.symm.trans heardSame)
    exact keysSentenceGoesForwardWhereTheRecordStands Reading.gl _ _ _ _ _ isLater stands
      (holdsInFront g F ledgerInFront heardInFront)

end

/-! ## 4 On a thread of the first chain -/

section
variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo P Cells Tok : Type}
  (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo P Cells Tok MsgT)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) Xo → Prop)
  {X : OnBytes.Model.Verify.Public} {D : Sent} {Lk : K3Letters Cells Tok}

/-- **CONDITIONAL ON what this file's head lists: worth "planes" and worth "keys" of a link's lookup
on the digits pass over a member that leaves the tail as it was and only adds to the ledger.** No
instance of these hypotheses is exhibited in this file. -/
theorem lookupWorthRidesPastAMemberThatExtendsTheLedger
    (tableSaysTheLookupsWorth : ∀ w, K3At X D Lk (L.Mg w)) {link piece : Nat} {x : PlaceL}
    {tl : HTailF2} (publicDataHoldTheDigitsPlace : digAt X link = some (x, tl))
    (pieceIsTheDigitsPiece : pieceOf X link true = piece) {border : Nat}
    (keepsLeavesTheTailAndExtendsTheLedger : ∀ s s', L.thread.keeps border s s' →
      s'.tl? = s.tl? ∧ ∀ F, s.fork? = some F → ∃ F', s'.fork? = some F' ∧ _root_.Fo.Later F F')
    (heardRecordStandsInFront : ∀ k s m E, ThrS L.thread Said border k s m E →
      ∃ F g, s.fork? = some F ∧ s.tl?.bind (·.heard) = some g ∧
        K3Stands tl.f9 5 x.F.next Reading.gl g F)
    {what : String} (whatIsPlanesOrKeys : what = "planes" ∨ what = "keys") :
    RidesPastAtS L.thread Said border (Item.worth link piece what) := by
  intro k s m E s' ps v relationInFront kept holdsInFront
  subst pieceIsTheDigitsPiece
  obtain ⟨f, tableIs⟩ := (tableSaysTheLookupsWorth m.st.input).worth
  have holdsInFront' : (L.Mg m.st.input).worth link (pieceOf X link true) what
      (L.thread.seat k m s) (L.thread.strs E) v := holdsInFront
  show (L.Mg m.st.input).worth link (pieceOf X link true) what (L.thread.seat k m s')
    (L.thread.strs (E.add ps)) v
  rw [tableIs, worthK3_digits X D Lk f link publicDataHoldTheDigitsPlace] at holdsInFront' ⊢
  exact digitsWorthGoesForward D Lk x tl whatIsPlanesOrKeys v _ _
    (keepsLeavesTheTailAndExtendsTheLedger s s' kept).1
    (keepsLeavesTheTailAndExtendsTheLedger s s' kept).2
    (heardRecordStandsInFront k s m E relationInFront) holdsInFront'

/-- **The same, with "the heard record stands" taken from the thread's rider.** CONDITIONAL ON what
this file's head lists. No instance of these hypotheses is exhibited in this file. -/
theorem lookupWorthRidesPastAMemberFromTheRider
    (tableSaysTheLookupsWorth : ∀ w, K3At X D Lk (L.Mg w)) {link piece : Nat} {x : PlaceL}
    {tl : HTailF2} (publicDataHoldTheDigitsPlace : digAt X link = some (x, tl))
    (pieceIsTheDigitsPiece : pieceOf X link true = piece) {border : Nat}
    (keepsLeavesTheTailAndExtendsTheLedger : ∀ s s', L.thread.keeps border s s' →
      s'.tl? = s.tl? ∧ ∀ F, s.fork? = some F → ∃ F', s'.fork? = some F' ∧ _root_.Fo.Later F F')
    (riderHoldsThatTheHeardRecordStands : ∀ w s, L.thread.rides border w s →
      StandsHere true 5 x.F.next s)
    (heardShapeIsThePlans : ∀ k s m E, ThrS L.thread Said border k s m E →
      ∀ g, s.tl?.bind (·.heard) = some g → g.shape = tl.f9)
    {what : String} (whatIsPlanesOrKeys : what = "planes" ∨ what = "keys") :
    RidesPastAtS L.thread Said border (Item.worth link piece what) := by
  refine lookupWorthRidesPastAMemberThatExtendsTheLedger L Said tableSaysTheLookupsWorth
    publicDataHoldTheDigitsPlace pieceIsTheDigitsPiece keepsLeavesTheTailAndExtendsTheLedger
    (fun k s m E relationInFront => ?_) whatIsPlanesOrKeys
  have relation := relationInFront.1
  unfold Thr at relation
  obtain ⟨-, -, -, -, -, rider, -⟩ := relation
  obtain ⟨F, g, ledgerRead, heardRead, stands⟩ :=
    riderHoldsThatTheHeardRecordStands m.st.input s rider
  have ledgerRead' : s.fork? = some F := ledgerRead
  have heardRead' : s.tl?.bind (·.heard) = some g := heardRead
  rw [heardShapeIsThePlans k s m E relationInFront g heardRead'] at stands
  exact ⟨F, g, ledgerRead', heardRead', stands⟩

/-- **Where the public item lookOut of the link's lookup on the digits is open at the border, the
heard record's shape is the shape at which the item's sentence stands.** CONDITIONAL ON `K3At` at
the promise's meaning. -/
theorem heardShapeIsThePlansWhereThePromiseBehindTheLookupIsOpen
    (promiseSaysTheLookupsTests : K3At X D Lk L.MgP) {link piece : Nat} {x : PlaceL}
    {tl : HTailF2} (publicDataHoldTheDigitsPlace : digAt X link = some (x, tl))
    (pieceIsTheDigitsPiece : pieceOf X link true = piece) {border : Nat}
    (promiseBehindTheLookupIsOpen :
      Pub.lookOut link piece ∈ ((pubSets L.mgP.more L.links L.ps)[border]?).getD [])
    {k : Coins Bk} {s : FS} {m : Mid (Local W₀ Rc Xi Tr) Xo} {E : Env}
    (relationInFront : Thr L.thread border k s m E) {g : OnBytes.Model.Forest.Heard}
    (heardRead : s.tl?.bind (·.heard) = some g) : g.shape = tl.f9 := by
  subst pieceIsTheDigitsPiece
  have test : L.MgP.pub (.lookOut link (pieceOf X link true)) (L.pubOf m.st.input.x, s) = true :=
    thr_pub L relationInFront promiseBehindTheLookupIsOpen
  rw [promiseSaysTheLookupsTests.lookOut] at test
  unfold digAt at publicDataHoldTheDigitsPlace
  obtain ⟨x', placeRead, rest⟩ := Option.bind_eq_some_iff.1 publicDataHoldTheDigitsPlace
  obtain ⟨tl', -, rest⟩ := Option.bind_eq_some_iff.1 rest
  obtain ⟨shape, shapeRead, rest⟩ := Option.map_eq_some_iff.1 rest
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj rest
  unfold k3OnOutAt placeAt at test
  rw [placeRead] at test
  have testAtThePlace : k3OnOut (VerifiableInference.Desc.First.Look.P.ofPlace
      (OnBytes.Params.settingOf X.P.frame) true x') s = true := test
  have heardAtTheSeat : heardAt (VerifiableInference.Desc.First.Look.P.ofPlace
      (OnBytes.Params.settingOf X.P.frame) true x').digits s = some g := heardRead
  unfold k3OnOut at testAtThePlace
  rw [shapeRead, heardAtTheSeat] at testAtThePlace
  cases ledgerRead : s.fork? with
  | none =>
    rw [ledgerRead] at testAtThePlace
    cases testAtThePlace
  | some G =>
    rw [ledgerRead] at testAtThePlace
    simp only [Bool.and_eq_true] at testAtThePlace
    exact H2K5.Door.sameShapeAll_eq testAtThePlace.1.1.1.1.1.1.1.1.1.1.1.1

/-- **worth "planes" and worth "keys" of a link's lookup on the digits pass over a member that
leaves the tail as it was and only adds to the ledger**, from the rider's clause and the promise's
public item. CONDITIONAL ON what this file's head lists. No instance of these hypotheses is
exhibited in this file. -/
theorem lookupWorthRidesPastAMemberFromTheRiderAndThePromise
    (tableSaysTheLookupsWorth : ∀ w, K3At X D Lk (L.Mg w))
    (promiseSaysTheLookupsTests : K3At X D Lk L.MgP) {link piece : Nat} {x : PlaceL}
    {tl : HTailF2} (publicDataHoldTheDigitsPlace : digAt X link = some (x, tl))
    (pieceIsTheDigitsPiece : pieceOf X link true = piece) {border : Nat}
    (promiseBehindTheLookupIsOpen :
      Pub.lookOut link piece ∈ ((pubSets L.mgP.more L.links L.ps)[border]?).getD [])
    (keepsLeavesTheTailAndExtendsTheLedger : ∀ s s', L.thread.keeps border s s' →
      s'.tl? = s.tl? ∧ ∀ F, s.fork? = some F → ∃ F', s'.fork? = some F' ∧ _root_.Fo.Later F F')
    (riderHoldsThatTheHeardRecordStands : ∀ w s, L.thread.rides border w s →
      StandsHere true 5 x.F.next s)
    {what : String} (whatIsPlanesOrKeys : what = "planes" ∨ what = "keys") :
    RidesPastAtS L.thread Said border (Item.worth link piece what) :=
  lookupWorthRidesPastAMemberFromTheRider L Said tableSaysTheLookupsWorth
    publicDataHoldTheDigitsPlace pieceIsTheDigitsPiece keepsLeavesTheTailAndExtendsTheLedger
    riderHoldsThatTheHeardRecordStands
    (fun _ _ _ _ relationInFront _ heardRead =>
      heardShapeIsThePlansWhereThePromiseBehindTheLookupIsOpen L promiseSaysTheLookupsTests
        publicDataHoldTheDigitsPlace pieceIsTheDigitsPiece promiseBehindTheLookupIsOpen
        relationInFront.1 heardRead)
    whatIsPlanesOrKeys

end

/-! ## 5 At the head's letters, past the head's merge -/

section
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (flatPlacesOf)
open VerifiableInference.Desc.Sound (mgAll mgBase mgMore mgAll_more_closed linksFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)

set_option maxRecDepth 1000000 in
/-- **At the full size's lists the public item lookOut 24 8 is open at border 346.** -/
theorem promiseBehindTheHeadsDigitsIsOpenAtTheMerge :
    Pub.lookOut 24 8 ∈
      ((pubSets mgMore linksFull (flatPlacesOf linksFull true))[346]?).getD [] := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can say no: in front of the head's lookup on the digits, at border 345, the item is not
open. -/
theorem promiseBehindTheHeadsDigitsIsNotOpenInFrontOfTheLookup :
    (((pubSets mgMore linksFull (flatPlacesOf linksFull true))[345]?).getD []).contains
      (Pub.lookOut 24 8) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : PlaceL}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

local notation "LH" => lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w

/-- **CONDITIONAL ON `P5J.AtMgA` and on three hypotheses more: worth 24 8 "planes" and worth 24 8
"keys" pass over the member number 346.** The three: the public data hold the place of the head's
lookup on the digits; the member's clause of keeps leaves the tail as it was and only adds to the
ledger; the rider at 346 holds that the heard record stands for some rounds. No instance of these
hypotheses is exhibited in this file. -/
theorem lookupWorthRidesPastTheHeadsMerge {digitsPlace : PlaceL} {tl : HTailF2}
    (publicDataHoldTheDigitsPlace : digAt Zp.p.X 24 = some (digitsPlace, tl))
    (keepsLeavesTheTailAndExtendsTheLedger : ∀ s s', (LH).thread.keeps 346 s s' →
      s'.tl? = s.tl? ∧ ∀ F, s.fork? = some F → ∃ F', s'.fork? = some F' ∧ _root_.Fo.Later F F')
    (riderHoldsThatTheHeardRecordStands : ∀ v s, (LH).thread.rides 346 v s →
      StandsHere true 5 digitsPlace.F.next s)
    {what : String} (whatIsPlanesOrKeys : what = "planes" ∨ what = "keys") :
    RidesPastAtS (LH).thread Said 346 (Item.worth 24 8 what) := by
  have promiseIsOpen : Pub.lookOut 24 8 ∈
      ((pubSets (LH).mgP.more (LH).links (LH).ps)[346]?).getD [] := by
    show Pub.lookOut 24 8 ∈
      ((pubSets (mgAll h.𝔇 mgBase).more linksFull (flatPlacesOf linksFull true))[346]?).getD []
    rw [mgAll_more_closed h.𝔇 mgBase rfl]
    exact promiseBehindTheHeadsDigitsIsOpenAtTheMerge
  exact lookupWorthRidesPastAMemberFromTheRiderAndThePromise (LH) Said
    (X := Zp.p.X) (D := h.𝔇.sent) (Lk := h.𝔇.l3)
    (fun v => ProofFile.Honest.K3.Law.Exchange.k3At_lettersAt h _ Q _ _ test carryX item n₁ n₂ _ _ _ v)
    (VerifiableInference.OnPublicFiles.k3At_mgAll h.𝔇 mgBase) publicDataHoldTheDigitsPlace
    (P5J.k03_pieceAt_dig h.toAtMg 24).symm promiseIsOpen keepsLeavesTheTailAndExtendsTheLedger
    riderHoldsThatTheHeardRecordStands whatIsPlanesOrKeys

end

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.sparseFormAtZeroEntriesIsZero
#print axioms ProofFile.Honest.K3.Term.formReadingGoesBackWhereItStands
#print axioms ProofFile.Honest.K3.Term.rowReadingGoesBackWhereItStands
#print axioms ProofFile.Honest.K3.Term.heardRecordGoesBackWhereItStands
#print axioms ProofFile.Honest.K3.Term.planesSentenceGoesForwardWhereTheRecordStands
#print axioms ProofFile.Honest.K3.Term.keysSentenceGoesForwardWhereTheRecordStands
#print axioms ProofFile.Honest.K3.Term.digitsWorthGoesForward
#print axioms ProofFile.Honest.K3.Term.lookupWorthRidesPastAMemberThatExtendsTheLedger
#print axioms ProofFile.Honest.K3.Term.lookupWorthRidesPastAMemberFromTheRider
#print axioms ProofFile.Honest.K3.Term.heardShapeIsThePlansWhereThePromiseBehindTheLookupIsOpen
#print axioms ProofFile.Honest.K3.Term.lookupWorthRidesPastAMemberFromTheRiderAndThePromise
#print axioms ProofFile.Honest.K3.Term.promiseBehindTheHeadsDigitsIsOpenAtTheMerge
#print axioms ProofFile.Honest.K3.Term.promiseBehindTheHeadsDigitsIsNotOpenInFrontOfTheLookup
#print axioms ProofFile.Honest.K3.Term.lookupWorthRidesPastTheHeadsMerge
