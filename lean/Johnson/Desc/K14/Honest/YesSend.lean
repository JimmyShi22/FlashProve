--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/YesSend.lean: the decide functions of the two sendings of the linear claim's
shared rounds return .ok, and what such a sending leaves of each new sampled message.

A sending is another kind's sub-protocol (Johnson/Desc/K1/Own.lean: decideSend), laid at the shared
rounds' state by sendAt (Johnson/Desc/K14/Blocks.lean). What decideSend asks and writes is a law
with both directions (Johnson/Desc/K1/Law/Writes3.lean: decideSend_iff). This file reads it
forwards. A decide function is no decision without the format's test on the rounds in front of it
(Johnson/Desc/Block.lean: Block.step): see Johnson/Desc/K14/Honest/ChainSteps.lean.

Main names:
  send_left           where decideSend returns .ok: each new sampled message stands with its
                      notice's shape, sampled, its pad's places those that the shape gives, its
                      ledger (the statement's field of that name) the fresh one
  send_returns        **decideSend returns .ok**, with what it returns written out, where: the
                      state's codes are the plan's; no sampled seed has the factor 0 as machine
                      words; the notices fit the codes and their trees can be laid; statement and
                      book are in step; the counts of seeds, answers and pads fit (fitB)
  sendAt_returns      so the decide function of the sub-protocol at the shared rounds' state returns
                      .ok, where what the kind notes behind the sending can be noted
  ids_zero, ids_one   the first two of the new messages' numbers
  behindU_is, behindOmega_is   the kind's two notes, written out, where two messages were sent

What is not claimed. That a view's rounds meet the two premises on rounds (the factors; fitB): that
is Johnson/Desc/K14/Honest/YesRounds.lean. Nothing on what a message holds or on the answers'
values. Nothing on soundness, on completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.YesFacts
import Johnson.Desc.Key.Laid.Laid2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc (named)
open VerifiableInference.Desc.K1 (decideSend decideSend_iff behind seedsOf answersIn shapesOf fitB
  wr outs put recvD cutSeeds_length)
open VerifiableInference.Desc.Key.LaidW (outs_get inFrontOf)

/-- **What a sending whose decideSend returns .ok leaves of a new sampled message.** -/
theorem send_left {L : Type} (P : VerifiableInference.Desc.K1.Par) (owed : Option Nat)
    (d d' : DState L) (r₁ r₂ : Fmt.RoundView) (ids : Array Nat)
    (h : decideSend P owed d [r₁, r₂] = .ok (ids, d')) (i : Nat) (n : OracleNotice)
    (hn : P.sent[i]? = some n) (h0 : n.shape.answers ≠ 0) :
    ∃ x : OnBytes.Oracle, d'.st.oracles[d.st.oracles.size + i]? = some x ∧ x.shape = n.shape ∧
      x.sampled = true ∧
      x.pad = ((Send.pad P.codes n.shape).getD []).map (fun p => (p.part, p.index)) ∧
      x.ledger = Slice.freshLedger P.codes n.shape := by
  obtain ⟨⟨_, hc, _, hok, hf⟩, _, hd'⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 h
  have hsome : (layTrees P.codes P.sent).isSome = true := by
    have := hok
    simp only [VerifiableInference.Desc.Ground.ok, VerifiableInference.Desc.Ground.recvL,
      VerifiableInference.Desc.Ground.sentL, List.cons_append, List.nil_append, List.all_cons,
      Bool.and_eq_true] at this
    rw [← hc]
    exact (VerifiableInference.Desc.Own.treesCan_eq _ _) ▸ this.2.1
  obtain ⟨lay, hlay⟩ := Option.isSome_iff_exists.1 hsome
  have hlen : (seedsOf P r₁).length = P.seeds := cutSeeds_length _ _ _
  have hb : d' = put (recvD P.gp.firstTree d P.sent lay)
      (d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
        (answersIn r₂)) := by
    rw [hd']
    simp [VerifiableInference.Desc.K1.behind, hlay]
  have hO : d'.st.oracles.toList = d.st.oracles.toList ++
      outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P) (answersIn r₂) := by
    rw [hb]
    simp [put]
  have hs : (shapesOf P)[i]? = some n.shape := by
    simp [shapesOf, hn]
  obtain ⟨ys', a, _⟩ := outs_get P.codes (seedsOf P r₁) (shapesOf P) d.st.oracles.size
    (answersIn r₂) i n.shape (by rw [hlen]; exact hf) hs
  refine ⟨wr P.codes (seedsOf P r₁) (d.st.oracles.size + i) n.shape ys', ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Array.getElem?_toList, hO,
      List.getElem?_append_right (by rw [Array.length_toList]; omega), Array.length_toList,
      Nat.add_sub_cancel_left]
    exact a
  all_goals simp [wr, h0]

/-- **decideSend returns .ok**; what it returns is written out. -/
theorem send_returns (Q : VerifiableInference.Desc.K1.Par) (d : St) (r₁ r₂ : Fmt.RoundView)
    (hc : d.st.codes = Q.codes) (hnz : ∀ s ∈ seedsOf Q r₁, isZeroE s.2 = false)
    (hsent : VerifiableInference.Desc.Ground.ok
      (VerifiableInference.Desc.Ground.sentL Q.codes Q.sent) = true)
    (hstep : d.st.oracles.size = d.book.place.size)
    (hfit : fitB Q.codes Q.seeds (shapesOf Q) (answersIn r₂) = true) :
    decideSend Q none (inFrontOf d) [r₁, r₂] =
      .ok ((Array.range Q.sent.size).map (· + d.st.oracles.size),
        behind Q (inFrontOf d) (seedsOf Q r₁) (answersIn r₂)) := by
  refine (decideSend_iff Q none (inFrontOf d) _ r₁ r₂ _).2 ⟨⟨rfl, hc, hnz, ?_, hfit⟩, rfl, rfl⟩
  have h1 : (VerifiableInference.Desc.Ground.sentL d.st.codes Q.sent).all (·.2) = true := by
    rw [hc]
    exact hsent
  show (VerifiableInference.Desc.Ground.sentL d.st.codes Q.sent ++
    [("recv: statement and book are in step", d.st.oracles.size == d.book.place.size)]).all
      (·.2) = true
  rw [List.all_append, h1, hstep]
  simp

/-- **The decide function of a sending at the shared rounds' state returns .ok.** note: what the
kind notes behind it. -/
theorem sendAt_returns (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (note : St → Array Nat → Option St)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (ids : Array Nat)
    (x : DState (Array Nat)) (hx : decideSend Q none (inFrontOf d) rs = .ok (ids, x))
    (hb : note { d with st := x.st, book := x.book, roots := x.roots, opened := x.opened } ids =
      some d') :
    (sendAt P n Q inFront groups note).decide d rs gs = .ok d' := by
  show (((decideSend Q none (inFrontOf d) rs).map fun y =>
      ({ owed := none, held := { y.2 with loc := y.1 } } :
        VerifiableInference.Desc.K1.Owing (DState (Array Nat)))).bind fun t =>
    named "the messages just sent are not those that this place records"
      (note { d with st := t.held.st, book := t.held.book, roots := t.held.roots,
                     opened := t.held.opened } t.held.loc)) = .ok d'
  rw [hx]
  exact (VerifiableInference.Desc.K1.named_ok _ _ _).2 hb

/-- The first of the new messages' numbers. -/
theorem ids_zero (n n0 : Nat) (h : 0 < n) : ((Array.range n).map (· + n0))[0]? = some n0 := by
  simp [h]

/-- The second of the new messages' numbers. -/
theorem ids_one (n n0 : Nat) (h : 1 < n) : ((Array.range n).map (· + n0))[1]? = some (n0 + 1) := by
  simp [h, Nat.add_comm]

/-- What the kind notes behind o_u's sending, where masks are sent ahead. -/
theorem behindU_is (p : Par) (d : St) (ids : Array Nat) (i0 i1 : Nat)
    (hM : p.S.masksAhead = true) (h0 : ids[0]? = some i0) (h1 : ids[1]? = some i1) :
    behindU p d ids = some { d with loc := { d.loc with
      oU := ⟨i0, vectorLay d.st.codes p.S.fold.u p.S.fold.rowsHigh⟩, firstMask := some i1 } } := by
  simp [behindU, hM, h0, h1]

/-- What the kind notes behind o_omega's sending, where the shape has two codes. -/
theorem behindOmega_is (p : Par) (d : St) (ids : Array Nat) (i0 i1 : Nat)
    (hS : p.S.sharedSplitNeeded = true) (h0 : ids[0]? = some i0) (h1 : ids[1]? = some i1) :
    behindOmega p d ids = some { d with loc := { d.loc with oOmega := i0, oSp := i1 } } := by
  simp [behindOmega, hS, h0, h1]

end Desc.K14.Honest

#print axioms Desc.K14.Honest.send_left
#print axioms Desc.K14.Honest.send_returns
#print axioms Desc.K14.Honest.sendAt_returns
#print axioms Desc.K14.Honest.ids_zero
#print axioms Desc.K14.Honest.ids_one
#print axioms Desc.K14.Honest.behindU_is
#print axioms Desc.K14.Honest.behindOmega_is
