-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P4R/Back341N.lean.
WHAT IT DOES NOT SHOW. No soundness. NO FACT ON THE STATE AT 341 BUT HOW IT WAS COME BY: three
acceptances in a row. "Reached" (Top/H0/Walk/Reach.lean) is weaker than "the verifier has come
here": it brings no test on the plan: so the third clause hands the lookup's test on the
plan only as an implication from the test of the sub-protocol that stands at 340. The rounds and
columns stand under "there is": no law may speak of "the" rounds.
WORDS. "The verifier's state": the value of type S that the sub-protocols hand on. "Accepts from s
to t": its decision returns t at s, at some rounds and columns.
LETTERS. "There is" in the conclusion: s338, s339, s340: the states at these borders; and each
sub-protocol's own arguments (p, n, HP; Q, sent, laid). start, z: free.
WHICH FAMILY. Reach 0 c.blocksInOrder start: reached by the sub-protocols' own steps: THE WIDER OF THE TWO in
Top/H0/Walk/Reach.lean. The family that a piece's acceptances hand on steps by the
wrapped sub-protocols (ReachAt.lean: RchAt); that file's reach_raw and rchAt_raw lead from it to
this one: so what is shown here holds of it.
OBJECT. In the goals' scope, at the opened value of the IOP as written in Lean (IM.Open): the flat
list of its first chain's sub-protocols, at the numbers 338, 339, 340: the first three places of the
head's link.
USER. Every fact on the reached state in front of the output head's own sub-protocol that is made at
one of the three places and kept at those behind it.
WHAT IT IS. THE WALK BACK FROM 341: WHOEVER IS REACHED AT 341 CAME BY THREE ACCEPTANCES, EACH SAID
IN ITS OWN SUB-PROTOCOL's TERM.
  reach_last        "reached" one border on: its last step (by cases; kind-free).
  step_yes          a step that accepts is a decision that accepts.
  head_behind_338   behind the next token's place the state stands in the head's link.
  back_341          the statement. 338: the entry of the head's link, then the next token's
                    (P4R/ReplyTiedN.lean: k7_left_seat). 339: the code switching's, then the step
                    that opens the head's link: IMR/K2Seat.lean's K2Is leaves four dresses: the
                    mute never accepts; the finish's has no link; a plain link's accepts only
                    between the links (Top/H0/Tw/K2C/StandsBy.lean: between_of_link), and here the
                    state stands in the head's. 340: the lookup on the calls
                    (Law/CallsLedgerKept.lean: stated_via3).

-/
import Johnson.IMR.K2Seat
import Johnson.IMR.K3Seat
import Johnson.IMR.FlatScope
import Johnson.P4R.ReplyTiedN
import Johnson.Top.H0.Walk.Reach
import Johnson.Top.H0.Tw.K2C.StandsBy
import Johnson.Desc.Kinds.Law.CallsLedgerKept
import Johnson.Desc.Kinds.Law.ReplyRest

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P4

open VerifiableInference.Desc (Block Chain Link FileDescription OpenedColumn KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (headFrontQ headFrontQ_iff codeSwitchKind headOpened P2 HeadPar
  between_of_link)
open VerifiableInference.Desc.Kinds (Reply.blockOf)
open VerifiableInference.Desc.Kinds.Head.Law (place_rest)
open VerifiableInference.Desc.Sound (step_ok_iff)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open ProofFile (Cl)
open Inst.Model (ScalesAndPolicy)

/-- "Reached" one border on: its last step. -/
theorem reach_last {σ C XP : Type} {ft : Nat} {bs : List (Block σ C)} {start : XP → σ} {k : Nat}
    {z : XP} {t : σ} (h : Reach ft bs start (k + 1) (z, t)) :
    ∃ s b, Reach ft bs start k (z, s) ∧ bs[k]? = some b ∧ StepYes ft b s t := by
  cases h with
  | succ h1 hb hy => exact ⟨_, _, h1, hb, hy⟩

/-- A step that accepts is a decision that accepts. -/
theorem step_yes {σ C : Type} {ft : Nat} {b : Block σ C} {s t : σ} (h : StepYes ft b s t) :
    ∃ rs gs, b.decide s rs gs = .ok t := by
  obtain ⟨R, c, -, hs⟩ := h
  exact ⟨_, _, ((step_ok_iff ft b s t R c c.length).1 hs).2.2.2⟩

/-- Behind the next token's place the state stands in the head's link. -/
theorem head_behind_338 (W : OnBytes.Model.Verify.Public) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : ((k7Front W).andThen "H:1" (Reply.blockOf W 24)).decide s rs gs = .ok t) :
    ∃ a, t.here = .head a := by
  obtain ⟨s0, h0, -, -, -, -, -, -, e, -⟩ :=
    place_rest W 24 "H:1" (k7Front W) W.H.tl (k7_front W) s rs gs t h
  obtain ⟨x, s₁, a, k⟩ := (headFrontQ_iff W.H.tl s s0).1 h0
  exact ⟨{ a with fr := x.f }, by rw [e, k.out]⟩

/-- **THE WALK BACK FROM 341.** -/
theorem back_341 {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {XP : Type} {start : XP → S}
    {z : XP} {s0 : S} (h : Reach 0 c.blocksInOrder start 341 (z, s0)) :
    ∃ s338 s339 s340 : S, Reach 0 c.blocksInOrder start 338 (z, s338) ∧
      (∃ rs gs, ((k7Front Bs.G₀.W).andThen "H:1" (Reply.blockOf Bs.G₀.W 24)).decide s338 rs gs =
        .ok s339) ∧
      (∃ (p : P2) (n : String) (HP : HeadPar) (rs : List Fmt.RoundView)
        (gs : List (List (Nat × List UInt64))),
        ((codeSwitchKind p : Block S Unit).andThen n (headOpened n p.place HP)).decide s339 rs gs = .ok s340) ∧
      ∃ (b3 : Block S Cl) (Q : VerifiableInference.Desc.First.Look.P) (sent : List (Nat × Nat))
        (laid : Array Nat) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
        c.blocksInOrder[340]? = some b3 ∧
        (VerifiableInference.Desc.K3.Law.blockVia
          (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm) 3 laid sent Q []).decide s340 rs
          gs = .ok s0 ∧
        (b3.planOk = true → (VerifiableInference.Desc.K3.Law.blockVia
          (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm) 3 laid sent Q []).planOk =
          true) := by
  obtain ⟨s340, b3, h340, e3, y3⟩ := reach_last h
  obtain ⟨s339, b2, h339, e2, y2⟩ := reach_last h340
  obtain ⟨s338, b1, h338, e1, y1⟩ := reach_last h339
  -- 338
  obtain ⟨L1, c1, l1, l2, -, -, hyes, -⟩ := k7_left_seat hS hR O
  have f1 : c.blocksInOrder[338]? = some c1 := by
    have q := IM.hear_at_flat l1 l2
    rwa [IM.flatIx_scope hS hR O (by decide) 0] at q
  obtain rfl : b1 = c1 := Option.some.inj (e1.symm.trans f1)
  obtain ⟨r1, g1, d1⟩ := step_yes y1
  obtain ⟨r1', g1', a1⟩ := hyes _ _ _ _ d1
  obtain ⟨ha, hhead⟩ := head_behind_338 Bs.G₀.W a1
  -- 339
  obtain ⟨L2, c2, x, m1, m2, -, hla2, hK⟩ := IM.k2_head_of hS hR O
  have f2 : c.blocksInOrder[339]? = some c2 := by
    have q := IM.hear_at_flat m1 m2
    rwa [IM.flatIx_scope hS hR O (by decide) 1] at q
  obtain rfl : b2 = c2 := Option.some.inj (e2.symm.trans f2)
  obtain ⟨r2, g2, d2⟩ := step_yes y2
  have a2 : x.decide s339 r2 g2 = .ok s340 :=
    ((IM.yes_alone hla2 (by decide) s339 s340 r2 g2).1 d2).1
  -- 340
  obtain ⟨L3, c3, c3', n1, n2, hk3, hla3⟩ := IM.k3_of hS hR O 24 (by decide) false
  have f3 : c.blocksInOrder[340]? = some c3 := by
    have q := IM.hear_at_flat n1 n2
    have e : IM.flatIx c 24 (IM.k3Ix 24 false) = 340 := IM.flatIx_scope hS hR O (by decide) _
    rwa [e] at q
  obtain rfl : b3 = c3 := Option.some.inj (e3.symm.trans f3)
  obtain ⟨r3, g3, d3⟩ := step_yes y3
  have a3 := ((IM.k3_yes hla3 s340 s0 r3 g3).1 d3).1
  obtain ⟨Q, sent, laid, r3', g3', hv, hp⟩ :=
    VerifiableInference.OnPublicFiles.stated_via3 K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W) Z.first.codes
      Z.first.shape (IM.k3Place 24 false) c3' hk3 (i := 24) rfl rfl s340 s0 r3 g3 a3
  refine ⟨s338, s339, s340, h338, ⟨r1', g1', a1⟩, ?_,
    ⟨b3, Q, sent, laid, r3', g3', f3, hv, fun hb => hp (by rw [← IM.alone_planOk hla3]; exact hb)⟩⟩
  rcases hK with ⟨-, hm⟩ | ⟨Pp, n, -, -, hd⟩
  · obtain ⟨e, he⟩ := hm s339 r2 g2
    rw [he] at a2
    cases a2
  · rcases hd with ⟨hn, -⟩ | ⟨l, HP, -, -, hx⟩ | ⟨l, -, hx⟩
    · cases hn
    · rw [hx] at a2
      exact ⟨_, _, HP, r2, g2, a2⟩
    · rw [hx] at a2
      have hb := between_of_link (snd := _root_.Tw.K2.sendByL8) a2 rfl
      rw [hhead] at hb
      cases hb

end P4

#print axioms P4.reach_last
#print axioms P4.step_yes
#print axioms P4.head_behind_338
#print axioms P4.back_341
