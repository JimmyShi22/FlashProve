-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/SendLater.lean: the calls by which a link of a request's chain receives the
oracle messages of a later moment, on a view: they take the two rounds of one sending and nothing
else.

A sub-proof's later oracle messages are received by ChainCheck.later (OnBytes/Model/ReqChain.lean),
which calls ReqFrame.later (OnBytes/Iop/Req.lean), which calls the sending block sendVerify and then
lets the new messages join the link's group. OnBytes/Tie/Pv/Tail/SendRan.lean says what the sending
block takes off a view. Here: the calls around it leave the channel as it was. Statements and
proofs.

Main names:
  `SendTook.of_ch`: the record of what a sending has taken speaks of the last context's channel
    alone.
  `joinOwn_ch`: the joining leaves the channel as it was.
  `frameLater_view`, `checkLater_view`: the two calls, from a context without an open message.
  `checkLater_rvT`: on the view of a written transcript, as `sendVerify_rvT`.

Limits: those of OnBytes/Tie/Pv/Tail/SendRan.lean. What the calls do to the statement and to the
frame's own record is not followed here.
-/
import OnBytes.Slice.BlkCalls
import OnBytes.Model.ReqChain
import OnBytes.Tie.Pv.Tail.SendRan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open Iop OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Tie.Pv.Switch

/-- The record speaks of the last context's channel alone. -/
theorem SendTook.of_ch {c c1 c' : Ctx} {notices : Array OracleNotice} {ids : Array Nat}
    {r₁ r₂ : Fmt.RoundView} {shapes : List OracleShape} {seeds : List SampleSeed} {ans : List E}
    (T : SendTook c notices ids c1 r₁ r₂ shapes seeds ans) (e : c'.ch = c1.ch) :
    SendTook c notices ids c' r₁ r₂ shapes seeds ans :=
  ⟨by rw [e]; exact T.left, ⟨by rw [e]; exact T.clean.1, by rw [e]; exact T.clean.2⟩, T.idsAre,
    T.shaped, T.none₁, T.cut, T.factor, T.vals₂, T.count⟩

/-- The joining leaves the channel as it was. -/
theorem joinOwn_ch (f j : ReqFrame) (sent : List Params.ReqMessage) (ids : Array Nat) (c c' : Ctx)
    (h : (f.joinOwn sent ids).Yields c j c') : c'.ch = c.ch := by
  unfold ReqFrame.joinOwn at h
  obtain ⟨_, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, rfl⟩ := (Blk.yields_must _ _ _).1 h1
  obtain ⟨_, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨_, rfl⟩ := (Blk.yields_pure _ _ _ _).1 a2
  have k := forIn_inv _ (fun _ _ c _ c' => c'.ch = c.ch) (by
    intro x b c r c1 hy
    obtain ⟨_, d, y1, y2⟩ := (Blk.yields_bind _ _ _ _ _).1 hy
    obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).1 y2
    obtain ⟨_, _, _, _, _, _, _, e⟩ := join_inv _ _ _ _ _ y1
    exact ⟨_, rfl, by rw [e]⟩) _ _ _ _ _ h2
  exact runFold_ch _ (fun _ _ _ _ _ h => h) _ _ _ _ _ k

/-- The frame's call for a later moment. -/
theorem frameLater_view (f : ReqFrame) (r : ReqFrame × Array Nat) (c c' : Ctx)
    (hc : PscRun.Clean c) (h : f.later.Yields c r c') :
    ∃ r₁ r₂ shapes seeds ans,
      SendTook c (ReqFrame.notices (f.atMoment f.moment)) r.2 c' r₁ r₂ shapes seeds ans := by
  unfold ReqFrame.later at h
  obtain ⟨_, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, rfl⟩ := (Blk.yields_get _ _ _ _).1 h1
  obtain ⟨_, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨_, rfl⟩ := (Blk.yields_must _ _ _).1 h2
  obtain ⟨ids, c3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  obtain ⟨j, c4, h4, a4⟩ := (Blk.yields_bind _ _ _ _ _).1 a3
  obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).1 a4
  obtain ⟨r₁, r₂, shapes, seeds, ans, T⟩ := sendVerify_view _ _ _ _ hc h3
  exact ⟨r₁, r₂, shapes, seeds, ans, T.of_ch (joinOwn_ch _ _ _ _ _ _ h4)⟩

/-- The chain's call for a later moment. -/
theorem checkLater_view (k k' : ChainCheck) (c c' : Ctx) (hc : PscRun.Clean c)
    (h : k.later.Yields c k' c') :
    ∃ r₁ r₂ shapes seeds ans,
      SendTook c (ReqFrame.notices (k.frame.atMoment k.frame.moment)) k'.sent c' r₁ r₂ shapes seeds
        ans := by
  unfold ChainCheck.later at h
  obtain ⟨_, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨_, rfl⟩ := (Blk.yields_must _ _ _).1 h1
  obtain ⟨r, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨rfl, rfl⟩ := (Blk.yields_pure _ _ _ _).1 a2
  exact frameLater_view _ _ _ _ hc h2

/-- The chain's call on the view of a written transcript. -/
theorem checkLater_rvT (k k' : ChainCheck) (x x' : Ctx) (hc : PscRun.Clean x)
    (h : k.later.Yields x k' x') (d₁ d₂ : RDT) (ds : List RDT)
    (m₁ : (roundT (Run.ckP .two) d₁).up.Msg) (w₁ : (roundT (Run.ckP .two) d₁).up.Chal)
    (m₂ : (roundT (Run.ckP .two) d₂).up.Msg) (w₂ : (roundT (Run.ckP .two) d₂).up.Chal)
    (τ : Tr (uLT (Run.ckP .two) ds))
    (hl : x.ch.left = rvT (Run.ckP .two) (d₁ :: d₂ :: ds)
      ((m₁, w₁, m₂, w₂, τ) : Tr (uLT (Run.ckP .two) (d₁ :: d₂ :: ds)))) :
    ∃ shapes seeds ans,
      SendTook x (ReqFrame.notices (k.frame.atMoment k.frame.moment)) k'.sent x'
        ⟨Run.PQ.PlainOf.gots d₁.items (GPlain.old (b := d₁.entry.work) m₁.2),
          (Run.ckP .two).dr d₁.entry d₁.kind (GChal.old (b := d₁.entry.work) w₁)⟩
        ⟨Run.PQ.PlainOf.gots d₂.items (GPlain.old (b := d₂.entry.work) m₂.2),
          (Run.ckP .two).dr d₂.entry d₂.kind (GChal.old (b := d₂.entry.work) w₂)⟩
        shapes seeds ans ∧
      x'.ch.left = rvT (Run.ckP .two) ds τ := by
  obtain ⟨r₁, r₂, shapes, seeds, ans, T⟩ := checkLater_view k k' x x' hc h
  obtain ⟨rfl, e⟩ := List.cons.inj (hl.symm.trans T.left)
  obtain ⟨rfl, e'⟩ := List.cons.inj e
  exact ⟨shapes, seeds, ans, T, e'.symm⟩

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.joinOwn_ch
#print axioms OnBytes.Tie.Pv.Tail.frameLater_view
#print axioms OnBytes.Tie.Pv.Tail.checkLater_view
#print axioms OnBytes.Tie.Pv.Tail.checkLater_rvT
