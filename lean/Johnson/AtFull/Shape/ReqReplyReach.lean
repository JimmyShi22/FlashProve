-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ReqReplyReach.lean: UNDER THE HEAD P5J.AtMgA: AT EVERY STATE THAT THE PROOF
FILE's OWN FIRST CHAIN REACHES FROM ITS OWN START, at an instance whose request passes the start's
test: THE STATE's OWN TEST ON THE REQUEST HOLDS; AND FROM BORDER 339 ON THE COVERED POSITIONS CAN BE
MADE: at the public part's own numbers, and at the numbers at which the members' tests on values
ask. A joining of laws; nothing of a model's size is evaluated.

What it closes. ReqAtHead.lean, ReplyKept.lean and ReplyEnds.lean speak of one member at a time, and
left three ties: that the vocabulary's size is at most the field's prime; that the numbers at which
the members' tests ask are those at which the start tests; and the walk along the chain. Here the
first two are paid by the library's laws on the public data in the goals' scope; the third, as far
as "reached", by induction along that family.

  `nums_at`: under the head, with Bs what ProofFile.baseOf returns at the public part: the maker's ground
    holds the public part's own record (IM.Open.W, Johnson/IMR/SeatOpen.lean); the head's count of
    positions and vocabulary's size are the record's own (T_in_scope, V_public,
    Johnson/Goal/Meaning/HeadStartScope.lean); that size is at most the prime (sizes_in_scope,
    Johnson/Goal/Meaning/HeadShapeScope.lean: it is 202048).
  **`reqOk_reach`**: Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a (Johnson/Top/H0/Walk/Reach.lean: THE RAW
    FAMILY: it steps by the chain's own blocks), the request of a.1 passes the start's test: then
    a.2.reqOk Zp.p.X.T Zp.p.X.P.h.V = true. AT EVERY k.
  **`covered_reach`**: and, where 339 ≤ k: a.2.covered Zp.p.X.T Zp.p.X.P.h.V returns.
  `reqOk_reach_head`: the first at 2 ^ lt and V of the head's shape (the output head's own rounds).
  `covered_reach_ground`: the second at the ground's T and V (the head's reads).
  `covered_reach_letters`: the second at the T and V of the head's link's letters
    (P1K2.pureLetters: the quiet step behind the head's code switch).

Limits. OF EVERY REACHED STATE, WHOEVER PLAYS: so nothing here says that anything is reached: THAT
MEMBER 338 SAYS YES AT ANY STATE IS NOT SHOWN: there the prover's reply is tested. The premise on
the request is the start's own test (the library pays it from the description's tests on the
instance: Meaning.K2.okBy_reqOk, Johnson/IMR/RecRun.lean). At a border: a test that a member asks at
a state between its own parts is not reached by these laws. Whoever holds a state in another form
than "reached" owes the step to it: no such step is made here. That the head has a member is shown
in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files, in
a side library. At the format's second hash function. Nothing on soundness, completeness or hiding.

-/
import Johnson.AtFull.Shape.ReplyEnds
import Johnson.Goal.Meaning.HeadStartScope
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open Johnson.Desc.First.Walk.Tied (Reach)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The numbers are one.** -/
theorem nums_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ Bs : ProofFile.PureBase, ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      Bs.G₀.W = Zp.p.X ∧ Zp.p.X.hS.T = Zp.p.X.T ∧ Zp.p.X.hS.V = Zp.p.X.P.h.V ∧
      Zp.p.X.hS.V ≤ pW.toNat := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hp := O.public
  rw [O.W] at hp
  refine ⟨Bs, O.made, O.W, ?_, ?_, ?_⟩
  · exact (VerifiableInference.Desc.Kinds.Head.Law.InScope.T_in_scope h.scope h.reads hp).symm
  · exact (VerifiableInference.Desc.Kinds.Head.Law.InScope.V_public hp).symm
  · rw [(Meaning.HeadS.sizes_in_scope h.scope h.reads hp).2.2.1]
    decide

/-- **At every reached state the state's own test on the request holds.** -/
theorem reqOk_reach (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : Nat} {a : ProofFile.InstPub × S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a)
    (hq : (Zp.s₀.withReq (Verify.words32 a.1.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = true) :
    a.2.reqOk Zp.p.X.T Zp.p.X.P.h.V = true := by
  induction hr with
  | zero z =>
    show (ProofFile.startS Zp z).reqOk _ _ = true
    unfold ProofFile.startS
    dsimp only
    rw [if_pos hq]
    exact hq
  | @succ k z s s' b _ hb hy ih =>
    obtain ⟨R, c, -, hs⟩ := hy
    show s'.reqOk _ _ = true
    rw [reqOk_kept_at h k _ _ b hb 0 s R c s' _ hs]
    exact ih hq

/-- **From border 339 on the covered positions can be made.** -/
theorem covered_reach (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : Nat}
    {a : ProofFile.InstPub × S} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a)
    (hq : (Zp.s₀.withReq (Verify.words32 a.1.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = true)
    (hk : 339 ≤ k) : ∃ cov, a.2.covered Zp.p.X.T Zp.p.X.P.h.V = .ok cov := by
  induction hr with
  | zero z => exact absurd hk (by omega)
  | @succ k z s s' b hr' hb hy ih =>
    obtain ⟨R, c, -, hs⟩ := hy
    show ∃ cov, s'.covered _ _ = .ok cov
    by_cases e : k = 338
    · subst e
      obtain ⟨Bs, hB, hW, -, hV, hp⟩ := nums_at h
      obtain ⟨Bs', hB', hc⟩ := covered_behind_338 h
      obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans hB')
      rw [hW, hV] at hc
      rw [hV] at hp
      exact hc hp _ b hb 0 s R c s' _ hs (reqOk_reach h hr' hq)
    · rw [covered_kept_but h k _ _ e b hb 0 s R c s' _ hs]
      exact ih hq (by omega)

/-- The first at the numbers of the head's shape. -/
theorem reqOk_reach_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : Nat}
    {a : ProofFile.InstPub × S} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a)
    (hq : (Zp.s₀.withReq (Verify.words32 a.1.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = true) :
    a.2.reqOk (2 ^ Zp.p.X.hS.lt) Zp.p.X.hS.V = true := by
  obtain ⟨_, -, -, hT, hV, -⟩ := nums_at h
  have e := reqOk_reach h hr hq
  rw [← hT, ← hV] at e
  exact e

/-- The second at the ground's numbers. -/
theorem covered_reach_ground (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ Bs : ProofFile.PureBase, ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      ∀ {k : Nat} {a : ProofFile.InstPub × S}, Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a →
        (Zp.s₀.withReq (Verify.words32 a.1.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = true →
        339 ≤ k → ∃ cov, a.2.covered Bs.G₀.W.hS.T Bs.G₀.W.hS.V = .ok cov := by
  obtain ⟨Bs, hB, hW, hT, hV, -⟩ := nums_at h
  refine ⟨Bs, hB, fun hr hq hk => ?_⟩
  rw [hW, hT, hV]
  exact covered_reach h hr hq hk

/-- The second at the numbers of the head's link's letters. -/
theorem covered_reach_letters (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ Bs : ProofFile.PureBase, ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      ∀ (l : Nat) (HP : VerifiableInference.Desc.First.K2.HeadPar),
        P1K2.pureLetters Bs.G₀ l = some HP → ∀ {k : Nat} {a : ProofFile.InstPub × S},
        Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a →
        (Zp.s₀.withReq (Verify.words32 a.1.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = true →
        339 ≤ k → ∃ cov, a.2.covered HP.T HP.V = .ok cov := by
  obtain ⟨Bs, hB, hc⟩ := covered_reach_ground h
  refine ⟨Bs, hB, fun l HP hl k a hr hq hk => ?_⟩
  unfold P1K2.pureLetters at hl
  obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hl
  exact hc hr hq hk

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.nums_at
#print axioms Johnson.AtFull.Shape.reqOk_reach
#print axioms Johnson.AtFull.Shape.covered_reach
#print axioms Johnson.AtFull.Shape.reqOk_reach_head
#print axioms Johnson.AtFull.Shape.covered_reach_ground
#print axioms Johnson.AtFull.Shape.covered_reach_letters
