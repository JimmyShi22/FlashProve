-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/XchAtBookSwitch.lean: the closing of a segment (K10): at the written book, at segments 1 to 24, the three fields on
the book of the records `FreshBySwitch` and `TieBySwitch` (Johnson/Desc/ProofFile/Honest/K10/Pay/XchFreshField.lean,
XchTieBySwitch.lean), at the closing and the written place of the code switch into its segment.

  `fresh_place_all`, `tie_place_all`, `front_place_all`   the three closed tests, by Lean's kernel, over the 24 written places
  `fresh_place_bent`, `tie_place_bent`, `front_place_bent`   THE TESTS CAN FAIL: at a start one further on, and one entry
                    further on, they reject at every place
  **`fresh_switch_book`**   the entry by which the closing's part spends is the switch's part's, where its last message's mask
                    coins start
  **`tie_switch_book`**     the entries by which the closing's part carries the switch's messages are the switch's, at the
                    switch's own cut
  **`tie_switch_front`**    on the segments in front the closing's part and the switch's part carry by entries of one owner, start
                    and count

Limits. At the book that the maker returns at the written description: that it is the head's book is in XchAtBookHead.lean.
Owners, starts and counts alone. The full size alone.
-/
import AtFullSide.K10.XchAtBookKit
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.ProofFile.Honest.K2.Law.Counts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open ProofFile.Honest ProofFile.Honest.K10 AtFullSide.K14
open ProofFile.Honest.K2 (SwitchPlace dueBefore messageDue fromE switchSent switchFresh)
open ProofFile.Honest.K2.Law (segsW placesW)
open VerifiableInference.Desc.First.Close (Par)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- The piece of the closing of segment l. -/
def pieceAt (l : Nat) : Nat := if l = 24 then 13 else 11

/-- The address of the part at the closing of segment l. -/
def addrAt (l : Nat) : Addr := ⟨⟨1, some l, pieceAt l, .K10⟩, 0⟩

/-- The carrying entries at an address, as three fields, at the written rows. -/
def viewAt (a : Addr) : List (Addr × Due × Due) := (pickV bfW rsW a).map tv

/-- How many messages the segments in front of segment l have sent. -/
def frontAt (l : Nat) : Nat := ((segsW.take (l + 1)).dropLast.map (·.messages)).sum

/-- Where the mask coins of the switch's last message start. -/
def freshAt (p : SwitchPlace) : Nat :=
  (dueBefore p.sizes.codes (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars)
      ((switchSent p.sizes p.others).size - 1)).e +
    fromE p.sizes.codes ((switchSent p.sizes p.others).getD ((switchSent p.sizes p.others).size - 1) default).shape

/-- The switch's own cut for its message number n. -/
def cutAt (p : SwitchPlace) (d n : Nat) : Addr × Due × Due :=
  (⟨p.place, 0⟩, (dueBefore p.sizes.codes (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars) n).plus ⟨0, d⟩,
    messageDue p.sizes.codes ((switchSent p.sizes p.others).getD n default).shape
      (K2.foldAt (switchFresh p.sizes p.others p.foldVars) n))

/-- The test on the spending entry. -/
def freshB (d : Nat) (p : SwitchPlace) : Bool :=
  (rawShortW.filter fun e => e.once && e.spender == addrAt p.link).map (fun e => (e.owner, e.start.e)) ==
    [((⟨p.place, 0⟩ : Addr), freshAt p + d)]

/-- The test on the carrying entries of the switch's messages. -/
def tieB (d : Nat) (p : SwitchPlace) : Bool :=
  (List.range ((switchSent p.sizes p.others).size - 1)).all fun n =>
    (viewAt (addrAt p.link))[frontAt p.link + n]? == some (cutAt p d n)

/-- The test on the segments in front. -/
def frontB (p : SwitchPlace) : Bool :=
  decide (frontAt p.link ≤ (viewAt (addrAt p.link)).length) &&
    decide (frontAt p.link ≤ (viewAt ⟨p.place, 0⟩).length) &&
    (viewAt (addrAt p.link)).take (frontAt p.link) == (viewAt ⟨p.place, 0⟩).take (frontAt p.link)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **At each written place in a segment the spending entry is the switch's.** The list's 25th place stands behind the last
segment: its number is 25. -/
theorem fresh_place_all : (placesW.all fun p => decide (25 ≤ p.link) || freshB 0 p) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test can fail. -/
theorem fresh_place_bent : placesW.any (freshB 1) = false := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **At each written place the carrying entries of the switch's messages are at the switch's own cut.** -/
theorem tie_place_all : (placesW.all fun p => decide (25 ≤ p.link) || tieB 0 p) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test can fail. -/
theorem tie_place_bent : placesW.any (tieB 1) = false := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **At each written place the closing and the switch carry the segments in front alike.** -/
theorem front_place_all : (placesW.all fun p => decide (25 ≤ p.link) || frontB p) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The comparison can fail: one entry further on the two lists part, at every place. -/
theorem front_place_bent : (placesW.any fun p => (viewAt (addrAt p.link)).take (frontAt p.link + 1) ==
    (viewAt ⟨p.place, 0⟩).take (frontAt p.link + 1)) = false := by decide +kernel

/-- A test of the form above at a place of one of the 25 segments. -/
theorem at_seg {p : SwitchPlace} {t : Bool} (h : (decide (25 ≤ p.link) || t) = true) (hl : p.link < 25) : t = true := by
  rcases Bool.or_eq_true _ _ ▸ h with h1 | h1
  · exact absurd (of_decide_eq_true h1) (by omega)
  · exact h1

/-- The piece of a closing is the written one. -/
theorem piece_written : (lpW.all fun x => x.2 == pieceAt x.1) = true := by decide

/-- The closing's address, by its link. -/
theorem addr_of_par {Q : Par} (hQ : Q ∈ parsW) : closeAddr Q = addrAt Q.link := by
  have hm : (Q.link, Q.piece) ∈ lpW := by
    rw [← pars_written]
    exact List.mem_map.2 ⟨Q, hQ, rfl⟩
  have e : Q.piece = pieceAt Q.link := beq_iff_eq.1 (List.all_eq_true.1 piece_written _ hm)
  show (⟨⟨1, some Q.link, Q.piece, .K10⟩, 0⟩ : Addr) = _
  rw [e]
  rfl

section
variable {B : ProverCoinCounts}

/-- An entry by which a closing's part spends lies among the short pieces. -/
theorem once_short (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
    (mergesByName WP.first.blocksInOrder) = .ok B) {Q : Par} (hQ : Q ∈ parsW) {e : Ahead} (he : e ∈ B.ahead)
    (h1 : (e.spender == closeAddr Q) = true) (h2 : e.once = true) :
    e ∈ rawShortW.filter fun e => e.once && e.spender == closeAddr Q := by
  have hw : ∀ e ∈ rawWantsW.map (·.entry), (e.once && e.spender == closeAddr Q) = false := by
    intro e he
    have k : (e.spender.place.kind != .K10) = true := List.all_eq_true.1 wants_noClose e he
    cases hq : e.spender == closeAddr Q with
    | false => simp
    | true =>
      rw [beq_iff_eq.1 hq] at k
      simp [closeAddr, closePlace] at k
  have hs : ∀ e ∈ rawSegW, (e.once && e.spender == closeAddr Q) = false := by
    intro e he
    have k := List.all_eq_true.1 seg_noClose e he
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at k
    simp [k.1]
  rw [← rawFilter_whole _ hw hs, ← close_ahead hB]
  exact List.mem_filter.2 ⟨he, by rw [h1, h2]; rfl⟩

/-- **The field book of `FreshBySwitch`.** -/
theorem fresh_switch_book (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
    (mergesByName WP.first.blocksInOrder) = .ok B) {Q : Par} (hQ : Q ∈ parsW) {p : SwitchPlace} (hp : p ∈ placesW)
    (hl : p.link = Q.link) :
    ∀ e ∈ B.ahead, (e.spender == closeAddr Q) = true → e.once = true →
      e.owner = ⟨p.place, 0⟩ ∧ e.start.e = freshAt p := by
  intro e he h1 h2
  have hm := once_short hB hQ he h1 h2
  have h25 : p.link < 25 := hl ▸ (closeOk_open hQ).1
  have ht : (rawShortW.filter fun e => e.once && e.spender == addrAt p.link).map (fun e => (e.owner, e.start.e)) =
      [((⟨p.place, 0⟩ : Addr), freshAt p + 0)] := beq_iff_eq.1 (at_seg (List.all_eq_true.1 fresh_place_all p hp) h25)
  rw [hl, ← addr_of_par hQ] at ht
  have hv := List.mem_map_of_mem (f := fun e : Ahead => (e.owner, e.start.e)) hm
  rw [ht] at hv
  have hv' := List.mem_singleton.1 hv
  exact ⟨congrArg Prod.fst hv', congrArg Prod.snd hv'⟩

/-- The view of the carrying entries at a closing. -/
theorem view_close (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
    (mergesByName WP.first.blocksInOrder) = .ok B) {Q : Par} (hQ : Q ∈ parsW) :
    (K12.Light.carriedOf B (closeAddr Q)).map viewE = viewAt (addrAt Q.link) := by
  rw [carried_view hB (a := closeAddr Q) (closeOk_open hQ).2.1, addr_of_par hQ]
  rfl

/-- The view of the carrying entries at a switch's part. -/
theorem view_switch (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
    (mergesByName WP.first.blocksInOrder) = .ok B) {p : SwitchPlace} (hp : p ∈ placesW) :
    (K12.Light.carriedOf B ⟨p.place, 0⟩).map viewE = viewAt ⟨p.place, 0⟩ :=
  carried_view hB (a := ⟨p.place, 0⟩) (List.contains_iff_mem.1 (List.all_eq_true.1 switchThere_written p hp))

/-- **The field book of `TieBySwitch`.** -/
theorem tie_switch_book (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
    (mergesByName WP.first.blocksInOrder) = .ok B) {Q : Par} (hQ : Q ∈ parsW) {p : SwitchPlace} (hp : p ∈ placesW)
    (hl : p.link = Q.link) :
    ∀ n, n + 1 < (switchSent p.sizes p.others).size → ∃ e,
      (K12.Light.carriedOf B (closeAddr Q))[0 + frontAt Q.link + (0 + n)]? = some e ∧
      e.owner = ⟨p.place, 0⟩ ∧
      e.start = dueBefore p.sizes.codes (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars) n ∧
      e.count = messageDue p.sizes.codes ((switchSent p.sizes p.others).getD n default).shape
        (K2.foldAt (switchFresh p.sizes p.others p.foldVars) n) := by
  intro n hn
  have h25 : p.link < 25 := hl ▸ (closeOk_open hQ).1
  have t : (List.range ((switchSent p.sizes p.others).size - 1)).all (fun n =>
      (viewAt (addrAt p.link))[frontAt p.link + n]? == some (cutAt p 0 n)) = true :=
    at_seg (List.all_eq_true.1 tie_place_all p hp) h25
  have tn : (viewAt (addrAt p.link))[frontAt p.link + n]? = some (cutAt p 0 n) :=
    beq_iff_eq.1 (List.all_eq_true.1 t n (List.mem_range.2 (by omega)))
  rw [hl, ← view_close hB hQ] at tn
  obtain ⟨e, he, ev⟩ := at_view tn
  refine ⟨e, by rw [Nat.zero_add, Nat.zero_add]; exact he, congrArg (·.1) ev, ?_, congrArg (·.2.2) ev⟩
  have es : e.start = (dueBefore p.sizes.codes (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) n).plus ⟨0, 0⟩ := congrArg (·.2.1) ev
  rw [es]
  rcases dueBefore p.sizes.codes (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars) n with ⟨a, b⟩
  rfl

/-- **The field bookFront of `TieBySwitch`.** -/
theorem tie_switch_front (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
    (mergesByName WP.first.blocksInOrder) = .ok B) {Q : Par} (hQ : Q ∈ parsW) {p : SwitchPlace} (hp : p ∈ placesW)
    (hl : p.link = Q.link) :
    ∀ n, n < 0 + frontAt Q.link → ∃ e e', (K12.Light.carriedOf B (closeAddr Q))[n]? = some e ∧
      (K12.Light.carriedOf B ⟨p.place, 0⟩)[n]? = some e' ∧
      e.owner = e'.owner ∧ e.start = e'.start ∧ e.count = e'.count := by
  intro n hn
  rw [Nat.zero_add] at hn
  have h25 : p.link < 25 := hl ▸ (closeOk_open hQ).1
  have t := at_seg (List.all_eq_true.1 front_place_all p hp) h25
  unfold frontB at t
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at t
  obtain ⟨⟨t1, t2⟩, t3⟩ := t
  rw [hl] at t1 t2 t3
  have h1 : n < (viewAt (addrAt Q.link)).length := by omega
  have h2 : n < (viewAt ⟨p.place, 0⟩).length := by omega
  have e1 : (viewAt (addrAt Q.link))[n]? = (viewAt ⟨p.place, 0⟩)[n]? := by
    have c := congrArg (fun l => l[n]?) t3
    simp only [List.getElem?_take, if_pos hn] at c
    exact c
  obtain ⟨v, hv⟩ : ∃ v, (viewAt ⟨p.place, 0⟩)[n]? = some v := ⟨_, List.getElem?_eq_getElem h2⟩
  have a1 : ((K12.Light.carriedOf B (closeAddr Q)).map viewE)[n]? = some v := by
    rw [view_close hB hQ, e1, hv]
  have a2 : ((K12.Light.carriedOf B ⟨p.place, 0⟩).map viewE)[n]? = some v := by
    rw [view_switch hB hp, hv]
  obtain ⟨e, he, ev⟩ := at_view a1
  obtain ⟨e', he', ev'⟩ := at_view a2
  have ee := ev.trans ev'.symm
  exact ⟨e, e', he, he', congrArg (·.1) ee, congrArg (·.2.1) ee, congrArg (·.2.2) ee⟩

end

end AtFullSide.K10

#print axioms AtFullSide.K10.fresh_place_all
#print axioms AtFullSide.K10.fresh_place_bent
#print axioms AtFullSide.K10.tie_place_all
#print axioms AtFullSide.K10.tie_place_bent
#print axioms AtFullSide.K10.front_place_all
#print axioms AtFullSide.K10.front_place_bent
#print axioms AtFullSide.K10.piece_written
#print axioms AtFullSide.K10.addr_of_par
#print axioms AtFullSide.K10.once_short
#print axioms AtFullSide.K10.fresh_switch_book
#print axioms AtFullSide.K10.at_seg
#print axioms AtFullSide.K10.view_close
#print axioms AtFullSide.K10.view_switch
#print axioms AtFullSide.K10.tie_switch_book
#print axioms AtFullSide.K10.tie_switch_front
