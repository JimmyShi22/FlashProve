-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Over the seats Stored/HeadSeatAt.lean and Stored/ReplySeatAt.lean,
which go with Block.lean and State.lean.
given_front: the seat's lookup reads S.lookHeard?.
Johnson/Desc/Kinds/Law/RunsFixedFront.lean: FROM K6's BORDER TO THE SNAPSHOT: Law/RunsFixed.lean's Alike asks «t the same», and the quiet step behind the sending of the reads turns t in between: HERE: a weaker relation, AlikeFront, which would span it (that the blocks between keep it: not shown: below).
  AlikeFront s s'   Law/RunsFixed.lean's Alike WITHOUT ITS TWO CLAUSES ON THE READS (t the same; the trees' widths the same): both in the head's link · x, squaresP, opened, lookHeard, out.reply, req the same · PscRun.Later of the two ledgers.
  alikeFront_of     Alike gives it.      AlikeFront.trans    it is carried along a chain of records.
  given_front | heard_front   TWO OF THE THREE STEPS OF lettersAt RETURN THE SAME ALONG AlikeFront: given p L s' = given p L s · what the seat reads back as heard at s is read back at s'.
  letters_front     SO: where K6's block has said yes (given returns; heard reads back H: Law/HeardBack.lean: seatBack_at) and s' goes on from the record behind it by AlikeFront, AND THE READS' PLACES ARE LAID AT s' (L.reads s' = some x): lettersAt returns at s', with THE LETTERS OF K6's BORDER and these places.
EVERY LETTER UNDER "THERE IS": none in the tops (letters_front's return is written out).
WHAT IT IS NOT. That the blocks between K6's border and the snapshot keep AlikeFront: not here (frames' laws: not checked here: the record turns across H:5 in st · book · roots · HeadOwn.L · F · t · tl · slotA: none is among AlikeFront's fields but F, of which Later is asked: NOT SHOWN). That the reads' places are laid: a premise.
Not PlainOk | RunOk. Nothing on soundness.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RunsFixed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc.First (S)

/-- Alike, without its two clauses on the reads. -/
def AlikeFront (s s' : S) : Prop :=
  ∃ o o', s.here = .head o ∧ s'.here = .head o' ∧ o'.x = o.x ∧ o'.squaresP = o.squaresP ∧
    o'.opened = o.opened ∧ o'.lookHeard = o.lookHeard ∧
    s'.out.reply = s.out.reply ∧ s'.req = s.req ∧ Later o.F o'.F

theorem alikeFront_of {s s' : S} (a : Alike s s') : AlikeFront s s' := by
  obtain ⟨o, o', h1, h2, h3, h4, _, h6, h7, h8, h9, h10, _⟩ := a
  exact ⟨o, o', h1, h2, h3, h4, h6, h7, h8, h9, h10⟩

theorem AlikeFront.trans {s s' s'' : S} (a : AlikeFront s s') (b : AlikeFront s' s'') :
    AlikeFront s s'' := by
  obtain ⟨o, o', h1, h2, h3, h4, h6, h7, h8, h9, h10⟩ := a
  obtain ⟨p', p'', k1, k2, k3, k4, k6, k7, k8, k9, k10⟩ := b
  rw [h2] at k1
  obtain rfl : o' = p' := by
    injection k1
  exact ⟨o, p'', h1, k2, k3.trans h3, k4.trans h4, k6.trans h6, k7.trans h7, k8.trans h8,
    k9.trans h9, h10.trans k10⟩

section At

variable (h : OnBytes.Model.Head.Shape) (iU3 : Nat)

theorem given_front (p : Par) {s s' : S} (a : AlikeFront s s') :
    given p (seatAt h iU3) s' = given p (seatAt h iU3) s := by
  obtain ⟨o, o', ho, ho', ex, _, eo, el, er, eq, _⟩ := a
  have e1 : (seatAt h iU3).lookup s' = (seatAt h iU3).lookup s := by
    have _ := ex
    show s'.lookHeard?.map _ = s.lookHeard?.map _
    unfold S.lookHeard?
    rw [ho, ho']
    simp only [eo, el]
  have e2 : Reply.token (seatAt h iU3).toSeat s' = Reply.token (seatAt h iU3).toSeat s := by
    show (s'.out.reply).map _ = (s.out.reply).map _
    rw [er]
  have e3 : (seatAt h iU3).request s' = (seatAt h iU3).request s := by
    show requestOf s' = requestOf s
    unfold requestOf S.tokv S.rowR S.rowE S.reqT
    rw [eq]
  unfold given
  rw [e1, e2, e3]

theorem heard_front {s s' : S} (a : AlikeFront s s') (H : HeardAll)
    (e : (seatAt h iU3).heard s = some H) : (seatAt h iU3).heard s' = some H := by
  obtain ⟨o, o', ho, ho', ex, es, _, _, _, _, hL⟩ := a
  have e' : (match s.here with
    | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
      allOf o.F x (some (keptOf q x.wpl.sL))
    | _ => none) = some H := e
  show (match s'.here with
    | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
      allOf o.F x (some (keptOf q x.wpl.sL))
    | _ => none) = some H
  rw [ho] at e'
  rw [ho']
  simp only [ex, es] at e' ⊢
  obtain ⟨q, hq, e1⟩ := Option.bind_eq_some_iff.mp e'
  obtain ⟨x, hx, e2⟩ := Option.bind_eq_some_iff.mp e1
  rw [hq, hx]
  exact allOf_later hL x _ H e2

/-- **FROM K6's BORDER TO A RECORD AT WHICH THE READS' PLACES ARE LAID: THE LETTERS ARE READ THERE, AND THEY ARE THE BORDER's.** -/
theorem letters_front (p : Par) {s s' : S} (a : AlikeFront s s') (g : Given) (H : HeardAll)
    (x : FinalNorm.Reads × Reads) (hg : given p (seatAt h iU3) s = .ok g)
    (hH : (seatAt h iU3).heard s = some H) (hx : (seatAt h iU3).reads s' = some x) :
    lettersAt p (seatAt h iU3) s' = .ok (g, ⟨H.1, H.2.1, H.2.2⟩, ⟨x.1, x.2⟩) := by
  unfold lettersAt
  rw [given_front h iU3 p a, hg, heard_front h iU3 a H hH, hx]
  rfl

end At

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.given_front
#print axioms VerifiableInference.Desc.Kinds.Head.Law.heard_front
#print axioms VerifiableInference.Desc.Kinds.Head.Law.letters_front
