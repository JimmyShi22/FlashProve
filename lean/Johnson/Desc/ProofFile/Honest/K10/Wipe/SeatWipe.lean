-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/SeatWipe.lean: the closing of a segment (K10): every member of the first chain in
front of a closing keeps the wiping (`Keeps wipeS 0`, Honest/K10/WipeFold.lean); and so the filler at made-up columns
(Honest/K10/StAtZero.lean) hands the verifier's own statement, wiped. Lemmas; no definition.

  `seatKeeps2_wipe`, `seatRest2_wipe`   the two structures of Wipe/Lots2.lean at `wipeS`: a field a maker, each paid by
                   the lemma of that kind's own file in this folder
  `keeps_front_wipe`   under `IM.Open`: at each place at which a block of the chain's first block and links stands:
                   every member in front of it keeps: `keeps_front` (Wipe/Open2.lean)
  `tied_in_front`   in scope: the chain's block at a closing's number stands among the first block and the links: by the
                   sealed count of the links' blocks (`IM.links_flat_352`, Johnson/IMR/BackSeat.lean)
  `takeWhile_take`, **`front_is_take`**   in scope "the members in front of the closing's place" are the chain's first
                   14 l + 12 members (14 l + 14 at the last link): the places of the flat list are apart
                   (`IM.places_scope`, Johnson/IMR/PlacesScope.lean; `IM.places_nodup`, Johnson/IMR/BorderW.lean)
  **`keeps_at_closing`**   in scope, at each of the 25 links: every member of the chain in front of that link's closing
                   keeps
  **`stAtZero_at_closing`**   so, where `frontState` returns t at the rounds seen and at some columns, `stAtZero` at the
                   chain's own list returns t's statement wiped and t's live group's number
  **`stAtZero_of_fold`**   the same where the description's fold over the chain's first 14 l + 12 members (14 l + 14 at
                   the last link) returns at the rounds seen and at some columns
  **`closeAsk_at_closing`**   and `closeAsk` at that filler is `closeAsk` at t's own statement and t's live group's
                   number
  **`stAtZero_of_chain`**   where the chain's own decision (`chainAt`) says yes at a view, and the rounds seen begin as
                   the view's as far as the members in front of the closing take rounds: `frontState` returns a state t
                   at the view's rounds and opened columns, and `stAtZero` at the rounds seen returns t's statement
                   wiped and t's live group's number: by `front_of_chain` (Honest/K10/ZeroTie.lean) and `front_same`
                   (Honest/K10/RoundsStretch.lean)

Limits. In the goals' scope, under `IM.Open` at the library's older hash, and at the closing that `Tied`
(Honest/K10/SimLot.lean) names at a link. That `frontState` returns is a premise of `stAtZero_at_closing` and
`closeAsk_at_closing`; at `stAtZero_of_fold` the premise is that the fold over these members returns, which is the same
by `front_is_take`; at `stAtZero_of_chain` it follows from hc, which is shown of no view. start and J are letters, and
J's own place is not tied to Q. That c is the description's own first chain is `open_first` (Honest/K10/LotPlaces.lean),
not carried here. Whether the premises can be had together at any files is no theorem. That the rounds which a part has
seen begin as the rounds that the verifier folds, as far as the members in front take rounds, is the frame's matter and
is not said here: it is `stAtZero_of_chain`'s premise hr. Nothing on whether `closeAsk` returns. The law on what the
closing hands on (Honest/K10/AskLaw.lean) wants a filler whose value is the state's own statement: the job on the right
side of `closeAsk_at_closing` is such a one, and the equation brings the law over to `stAtZero`, whose value is that
statement wiped. No property of the protocol is claimed: nothing is said on its soundness, completeness, binding or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.Open2
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepEach
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepK8K11
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepK3
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepK4
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepK5
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepK6K7
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepFrames
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepReads
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepK1
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepK9
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepFront
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepK2
import Johnson.Desc.ProofFile.Honest.K10.ZeroTie
import Johnson.Desc.ProofFile.Honest.K10.RoundsStretch
import Johnson.Desc.ProofFile.Honest.K10.SimLot
import Johnson.IMR.BackSeat
import Johnson.IMR.PlacesScope
import Johnson.IMR.BorderW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Block Chain Place OpenedColumn FileDescription chainAt foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par)

/-- **Every maker whose blocks the description lays inside a link keeps the wiping.** -/
theorem seatKeeps2_wipe : SeatKeeps2 wipeS where
  failed := failed_wipe
  reply := reply_wipe
  frames := fun h => frames2 h
  k1First := fun q gp => k1First2 q gp
  k1Later := fun q gp link piece moment arrays => k1Later2 q gp link piece moment arrays
  reads := fun h => reads2 h
  k3 := k3_keeps
  k4 := k4_keeps
  k5 := fun W l g before _ h => k5_keeps W l g before h
  k6 := fun h => k6_keeps h
  k7 := k7_keeps
  k8 := k8_keeps
  k11 := k11_keeps
  closeOf := closeOf2
  batch := fun p _ hc => batch2 p hc
  each := each_keeps
  tests := tests_keeps
  k2 := fun p => k2_whole2 p
  front := front2
  openQ := openQ2

/-- The three texts behind the last link keep it too. -/
theorem seatRest2_wipe : SeatRest2 wipeS where
  finFront := finFront2
  finBehind := finBehind2
  sealAsks := endAsks_wipe

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Every member in front of a place of the first block or the links keeps the wiping.** -/
theorem keeps_front_wipe (O : IM.Open o pol lay KL F Z Bs base c A B) {a : Place}
    (ha : ∃ b ∈ Meaning.K2.frontOf c, b.place = a) :
    ∀ b ∈ c.blocksInOrder.takeWhile (·.place != a), Keeps wipeS 0 b :=
  keeps_front seatKeeps2_wipe seatRest2_wipe O ha

end

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- In scope the chain's block at a closing's number stands among the first block and the links. -/
theorem tied_in_front (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {p : VerifiableInference.Desc.K9.Where} {Q : Par} {b : Block S ProofFile.Cl} (T : Tied c Z l p Q b) :
    ∃ b' ∈ Meaning.K2.frontOf c, b'.place = closePlace Q := by
  obtain ⟨hfr, h352⟩ := IM.links_flat_352 hS hR O
  obtain ⟨-, -, hb, -, -, hp, -⟩ := T
  have hlen : (Meaning.K2.frontOf c).length = 353 := by
    unfold Meaning.K2.frontOf
    rw [List.length_cons, h352]
  have hi : 14 * l + (if l = 24 then 9 else 7) + 5 < (Meaning.K2.frontOf c).length := by
    rw [hlen]
    split <;> omega
  rw [Meaning.K2.flat_eq hfr, List.getElem?_append_left hi] at hb
  exact ⟨b, List.mem_of_getElem? hb, hp⟩

/-- In a list whose members' places are apart, the members in front of the first one at a place are those in front of
any member that stands there. -/
theorem takeWhile_take {α : Type} (f : α → Place) (a : Place) :
    ∀ (l : List α) (i : Nat) (b : α), (l.map f).Nodup → l[i]? = some b → f b = a →
      l.takeWhile (fun x => f x != a) = l.take i
  | [], _, _, _, h, _ => by simp at h
  | x :: l, 0, b, _, h, hb => by
    have e : x = b := by simpa using h
    subst e
    have hx : (f x != a) = false := by rw [hb]; exact bne_self_eq_false _
    rw [List.takeWhile_cons, hx]
    rfl
  | x :: l, i + 1, b, hn, h, hb => by
    have h' : l[i]? = some b := by simpa using h
    have hn' : f x ∉ l.map f ∧ (l.map f).Nodup := List.nodup_cons.1 hn
    have hne : f x ≠ a := fun e => hn'.1 (List.mem_map.2 ⟨b, List.mem_of_getElem? h', by rw [hb, e]⟩)
    have hx : (f x != a) = true := bne_iff_ne.2 hne
    rw [List.takeWhile_cons, hx, List.take_succ_cons, takeWhile_take f a l i b hn'.2 h' hb]
    rfl

/-- **In scope the members in front of a link's closing are the chain's first 14 l + 12 members** (14 l + 14 at the last
link): the places of the chain's flat list are apart. -/
theorem front_is_take (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat}
    {p : VerifiableInference.Desc.K9.Where} {Q : Par} {b : Block S ProofFile.Cl} (T : Tied c Z l p Q b) :
    c.blocksInOrder.takeWhile (·.place != closePlace Q) = c.blocksInOrder.take (14 * l + (if l = 24 then 9 else 7) + 5) := by
  obtain ⟨-, -, hb, -, -, hp, -⟩ := T
  refine takeWhile_take (·.place) (closePlace Q) c.blocksInOrder _ b ?_ hb hp
  rw [IM.places_scope hS hR O]
  exact IM.places_nodup

/-- **Every member of the chain in front of a link's closing keeps the wiping.** -/
theorem keeps_at_closing (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {p : VerifiableInference.Desc.K9.Where} {Q : Par} {b : Block S ProofFile.Cl} (T : Tied c Z l p Q b) :
    ∀ b' ∈ c.blocksInOrder.takeWhile (·.place != closePlace Q), Keeps wipeS 0 b' :=
  keeps_front_wipe O (tied_in_front hS hR O hl T)

/-- **The filler's value at a link's closing.** -/
theorem stAtZero_at_closing {Xi : Type} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {p : VerifiableInference.Desc.K9.Where} {Q : Par} {b : Block S ProofFile.Cl} (T : Tied c Z l p Q b)
    (start : Xi → S) (x : Xi) (seen : Seen) (front : List Fmt.Drawn) {cols : List OpenedColumn} {t : S}
    (h : frontState 0 c.blocksInOrder (start x) (closePlace Q) seen.rounds cols = .ok t) :
    stAtZero c.blocksInOrder start x Q seen front = .ok (wipeSt t.st, t.live.frame.group) :=
  stAtZero_is c.blocksInOrder start x Q seen front (keeps_at_closing hS hR O hl T) h

/-- **The same from the fold over the chain's first members**: the form in which a thread's invariant holds the
verifier's state at a border (`Thread.Made`, Honest/Thread/Thr.lean); nothing here ties a thread's letters to c.blocksInOrder, 0,
start x and seen.rounds. -/
theorem stAtZero_of_fold {Xi : Type} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {p : VerifiableInference.Desc.K9.Where} {Q : Par} {b : Block S ProofFile.Cl} (T : Tied c Z l p Q b)
    (start : Xi → S) (x : Xi) (seen : Seen) (front : List Fmt.Drawn) {cols : List OpenedColumn}
    {r : S × List Fmt.RoundView × List OpenedColumn}
    (h : foldBlocks 0 (c.blocksInOrder.take (14 * l + (if l = 24 then 9 else 7) + 5)) (start x) seen.rounds cols = .ok r) :
    stAtZero c.blocksInOrder start x Q seen front = .ok (wipeSt r.1.st, r.1.live.frame.group) := by
  refine stAtZero_at_closing hS hR O hl T start x seen front (cols := cols) ?_
  have ha : c.blocksInOrder.any (·.place == closePlace Q) = true := by
    obtain ⟨-, -, hb, -, -, hp, -⟩ := T
    refine List.any_eq_true.2 ⟨b, List.mem_of_getElem? hb, ?_⟩
    rw [hp]
    exact beq_self_eq_true _
  unfold frontState
  rw [ha, front_is_take hS hR O T, h]
  rfl

/-- **What the closing hands to the fold, at a link's closing.** -/
theorem closeAsk_at_closing {W Xi : Type} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {p : VerifiableInference.Desc.K9.Where} {Q : Par} {b : Block S ProofFile.Cl} (T : Tied c Z l p Q b)
    (J : CloseJob W) (start : Xi → S) (xi : W → Xi) (w : W) (seen : Seen) (front : List Fmt.Drawn) (x : Fmt.Drawn)
    (u : Fin (2 * J.pub.par.k + 1) → OnBytes.E) (ca : CsAll (closeCarries J.pub)) {cols : List OpenedColumn} {t : S}
    (h : frontState 0 c.blocksInOrder (start (xi w)) (closePlace Q) seen.rounds cols = .ok t) :
    closeAsk { J with stAt := fun w' s f => stAtZero c.blocksInOrder start (xi w') Q s f } w seen front x u ca =
      closeAsk { J with stAt := fun _ _ _ => .ok (t.st, t.live.frame.group) } w seen front x u ca :=
  closeAsk_zero J c.blocksInOrder start xi Q w seen front x u ca (keeps_at_closing hS hR O hl T) h

/-- **From the chain's own decision**: the filler's value at the rounds seen is the statement, wiped, of the state that
the description's fold reaches in front of the closing at the view's rounds and opened columns. -/
theorem stAtZero_of_chain {Xi : Type} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {p : VerifiableInference.Desc.K9.Where} {Q : Par} {b : Block S ProofFile.Cl} (T : Tied c Z l p Q b)
    (start : Xi → S) (x : Xi) (seen : Seen) (front : List Fmt.Drawn) {name : String} {e : S} {v : Fmt.View}
    (hc : chainAt name 0 c.blocksInOrder (start x) v = .ok e)
    (hr : seen.rounds.take (roundsDue (c.blocksInOrder.takeWhile (·.place != closePlace Q))) =
      v.rounds.take (roundsDue (c.blocksInOrder.takeWhile (·.place != closePlace Q)))) :
    ∃ t, frontState 0 c.blocksInOrder (start x) (closePlace Q) v.rounds v.opened = .ok t ∧
      stAtZero c.blocksInOrder start x Q seen front = .ok (wipeSt t.st, t.live.frame.group) := by
  have ha : c.blocksInOrder.any (·.place == closePlace Q) = true := by
    obtain ⟨-, -, hb, -, -, hp, -⟩ := T
    refine List.any_eq_true.2 ⟨b, List.mem_of_getElem? hb, ?_⟩
    rw [hp]
    exact beq_self_eq_true _
  obtain ⟨t, ht⟩ := front_of_chain hc (closePlace Q) ha
  exact ⟨t, ht, stAtZero_at_closing hS hR O hl T start x seen front (front_same 0 c.blocksInOrder (closePlace Q) hr ht)⟩

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.seatKeeps2_wipe
#print axioms ProofFile.Honest.K10.seatRest2_wipe
#print axioms ProofFile.Honest.K10.keeps_front_wipe
#print axioms ProofFile.Honest.K10.tied_in_front
#print axioms ProofFile.Honest.K10.takeWhile_take
#print axioms ProofFile.Honest.K10.front_is_take
#print axioms ProofFile.Honest.K10.keeps_at_closing
#print axioms ProofFile.Honest.K10.stAtZero_at_closing
#print axioms ProofFile.Honest.K10.stAtZero_of_fold
#print axioms ProofFile.Honest.K10.closeAsk_at_closing
#print axioms ProofFile.Honest.K10.stAtZero_of_chain
