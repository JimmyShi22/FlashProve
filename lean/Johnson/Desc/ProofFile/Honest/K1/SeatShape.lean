-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/SeatShape.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR
THE HONEST SIDE: THE SHAPE THAT THE REQUEST's LIST HAS AT A SEAT IS THE SENDER's OWN: where
momentSeat (Honest/K1/FirstData.lean), at the place's part 0 and from 0, seats message number k of a
sending at (segment l, message m of the segment's list), that message's shape is shapeAt P k at the
plan P of the place that sends the segment's moment; and the plan's codes are the request's.
Statements and proofs on public data; no definition.

  zipIdx_filter_at   tool: the k-th of a numbered list's filter is the k-th of the list's filter,
                and stands in the list at its number
  msgNo_at      msgNo s l t k = some m: the segment's list has a message M at m, and M is the k-th
                of the list's messages of moment t
  atMoment_filter   the programs' ReqFrame.atMoment at a frame of the shape s and the link l is that
                filter
  getD_notices  tool: the k-th of a list of messages, announced, in front of whatever follows, keeps
                its shape
  shapeAt_later   the k-th message of moment t of segment l has the shape
                shapeAt (K1.parLater ...) k
  shapeAt_first   the like at the first segment's opening (K1.firstPar), for its own messages: the
                first of its three named parts
  later_seat_shape, first_seat_shape   SO AT A SEAT: momentSeat at the place's part 0, from 0 |
                firstSeat: the list's message at the seat has the sender's shape
  firstPar_codes, parLater_codes   the two plans' codes are the request's (by rfl)

Why. The plan's test on a layout (Own.reqMessageLaid) and the library's laws on where an array's
element lies speak at the shape IN THE LIST; rowsR goes by shapeAt P k. These say that the two are
one.

Limits. Of momentSeat's seats at the place's part 0, from 0, at K1.firstPar and K1.parLater, alone:
a sending whose own messages begin at a later number (momentSeat's "from") is not treated; how the
fillings of the reads and the digits seat their messages is theirs to tie to it. The opening's two
other parts (the fold's mask; the messages at the start) have no seat. W's place: not treated.
Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.PlaceFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)

theorem zipIdx_filter_at {α : Type} (p : α → Bool) (L : List α) (k : Nat) (a : α) (m : Nat)
    (h : (L.zipIdx.filter (p ∘ Prod.fst))[k]? = some (a, m)) :
    L[m]? = some a ∧ (L.filter p)[k]? = some a := by
  constructor
  · have hm : (a, m) ∈ L.zipIdx.filter (p ∘ Prod.fst) := List.mem_of_getElem? h
    exact List.mem_zipIdx_iff_getElem?.1 (List.mem_filter.1 hm).1
  · have e : (L.zipIdx.filter (p ∘ Prod.fst)).map Prod.fst = L.filter p := by
      rw [← List.filter_map, List.zipIdx_map_fst]
    have e2 := congrArg (·[k]?) e
    simp only [List.getElem?_map, h, Option.map_some] at e2
    exact e2.symm

theorem msgNo_at (s : ReqShape) (l t k m : Nat) (h : msgNo s l t k = some m) :
    ∃ M, (s.link.getD l default).messages[m]? = some M ∧
      ((s.link.getD l default).messages.filter fun x => x.moment == t)[k]? = some M := by
  unfold msgNo at h
  cases e : ((s.link.getD l default).messages.zipIdx.filter fun x => x.1.moment == t)[k]? with
  | none =>
    rw [e] at h
    cases h
  | some x =>
    rw [e] at h
    obtain ⟨a, m'⟩ := x
    have hm : m' = m := Option.some.inj h
    subst hm
    exact ⟨a, zipIdx_filter_at (fun y : ReqMessage => y.moment == t) _ k a m' e⟩

theorem atMoment_filter (s : ReqShape) (g : Array ReqGroup) (l t : Nat) :
    ({ shape := s, groups := g, link := l } : ReqFrame).atMoment t =
      (s.link.getD l default).messages.filter fun x => x.moment == t := by
  unfold ReqFrame.atMoment
  rw [List.getD_eq_getElem?_getD]
  cases s.link[l]? <;> rfl

theorem getD_notices (L : List ReqMessage) (rest : List OracleNotice) (k : Nat) (M : ReqMessage)
    (h : L[k]? = some M) :
    (((ReqFrame.notices L).toList ++ rest).toArray.getD k default).shape = M.shape := by
  obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.1 h
  unfold ReqFrame.notices
  simp [Array.getD_eq_getD_getElem?, List.getElem?_append_left, hk, he]

theorem shapeAt_later (q : Params.First) (gp : _root_.Desc.Plain.GPar) (l piece t k : Nat)
    (M : ReqMessage)
    (h : ((q.shape.link.getD l default).messages.filter fun x => x.moment == t)[k]? = some M) :
    shapeAt (K1.parLater q gp l piece t) k = M.shape := by
  change (((ReqFrame.notices (ReqFrame.atMoment
    { shape := q.shape, groups := reqGroups q.shape, link := l } t)).toList ++ []).toArray.getD k
      default).shape = _
  rw [atMoment_filter]
  exact getD_notices _ [] k M h

theorem shapeAt_first (q : Params.First) (gp : _root_.Desc.Plain.GPar) (k : Nat) (M : ReqMessage)
    (h : ((q.shape.link.getD 0 default).messages.filter fun x => x.moment == 0)[k]? = some M) :
    shapeAt (K1.firstPar q gp) k = M.shape := by
  change (((ReqFrame.notices (ReqFrame.atMoment
    { shape := q.shape, groups := reqGroups q.shape, link := 0 } 0)).toList ++ _).toArray.getD k
      default).shape = _
  rw [atMoment_filter]
  exact getD_notices _ _ k M h

theorem firstPar_codes (q : Params.First) (gp : _root_.Desc.Plain.GPar) :
    (K1.firstPar q gp).codes = q.codes := rfl

theorem parLater_codes (q : Params.First) (gp : _root_.Desc.Plain.GPar) (l piece t : Nat) :
    (K1.parLater q gp l piece t).codes = q.codes := rfl

/-- **At a seat of a segment's later moment the list's message has the sender's shape.** -/
theorem later_seat_shape (q : Params.First) (gp : _root_.Desc.Plain.GPar) (l piece t k l' m : Nat)
    (h : momentSeat q.shape ⟨(K1.parLater q gp l piece t).place, 0⟩ l t 0
      ⟨⟨(K1.parLater q gp l piece t).place, 0⟩, k⟩ = some (l', m)) :
    l' = l ∧ ∃ M, (q.shape.link.getD l default).messages[m]? = some M ∧
      M.shape = shapeAt (K1.parLater q gp l piece t) k := by
  unfold momentSeat at h
  split at h
  · obtain ⟨m₀, e, hp⟩ := Option.map_eq_some_iff.1 h
    have h1 : l = l' := congrArg Prod.fst hp
    have h2 : m₀ = m := congrArg Prod.snd hp
    subst h1 h2
    obtain ⟨M, hM, hk⟩ := msgNo_at q.shape l t _ m₀ e
    exact ⟨rfl, M, hM, (shapeAt_later q gp l piece t k M hk).symm⟩
  · cases h

/-- **At a seat of the first segment's opening.** -/
theorem first_seat_shape (q : Params.First) (gp : _root_.Desc.Plain.GPar) (k l m : Nat)
    (h : firstSeat q.shape 0 ⟨firstAddr, k⟩ = some (l, m)) :
    l = 0 ∧ ∃ M, (q.shape.link.getD 0 default).messages[m]? = some M ∧
      M.shape = shapeAt (K1.firstPar q gp) k := by
  unfold firstSeat momentSeat at h
  split at h
  · obtain ⟨m₀, e, hp⟩ := Option.map_eq_some_iff.1 h
    have h1 : 0 = l := congrArg Prod.fst hp
    have h2 : m₀ = m := congrArg Prod.snd hp
    subst h1 h2
    obtain ⟨M, hM, hk⟩ := msgNo_at q.shape 0 0 _ m₀ e
    exact ⟨rfl, M, hM, (shapeAt_first q gp k M hk).symm⟩
  · cases h

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.zipIdx_filter_at
#print axioms ProofFile.Honest.K1.msgNo_at
#print axioms ProofFile.Honest.K1.atMoment_filter
#print axioms ProofFile.Honest.K1.getD_notices
#print axioms ProofFile.Honest.K1.shapeAt_later
#print axioms ProofFile.Honest.K1.shapeAt_first
#print axioms ProofFile.Honest.K1.firstPar_codes
#print axioms ProofFile.Honest.K1.parLater_codes
#print axioms ProofFile.Honest.K1.later_seat_shape
#print axioms ProofFile.Honest.K1.first_seat_shape
