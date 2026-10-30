-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/SendRoot.lean: the routine by which a sub-proof's prover commits to further
arrays, on a view: it takes the two rounds of one sending and nothing else.

rootInH (OnBytes/Model/Trees.lean) calls the chain for the link's next moment and then marks the
arrays as committed. OnBytes/Tie/Pv/Keeps/KeepsLoop.lean takes a run of it apart (rootInH_ran).
OnBytes/Tie/Pv/Tail/SendLater.lean says what the chain's call takes off a view. Both together, so
that the routine's run stands in a row with the draw of the matrix
(OnBytes/Tie/Pv/Tail/RngView.lean) and the draw of the batching element
(OnBytes/Tie/Pv/Tail/BatRan.lean): each hands on the view of the rest. Statements and proofs.

Main names:
  `rootTurns_ctx`: the loop that marks the arrays leaves the context as it was.
  `rootInH_view`: the routine, from a context without an open message.
  `rootInH_rvT`: on the view of a written transcript whose next two rounds are d₁, d₂: the two
    rounds are taken; the seeds are cut out of what the first drew; the answers are the second's
    items; the rounds not yet begun are the view of the rest.

Limits: those of OnBytes/Tie/Pv/Tail/SendRan.lean.
-/
import OnBytes.Tie.Pv.Keeps.KeepsLoop
import OnBytes.Tie.Pv.Tail.SendLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open Iop OnBytes OnBytes.Model OnBytes.Maker

/-- The loop that marks the arrays leaves the context as it was. -/
theorem rootTurns_ctx : ∀ (l : List Nat) (u u' : PUnit) (L L' : LinkCtx) (F F' : Fork)
    (c c' : Ctx), L5.RunFold L5.rootTurn l u (L, F, c) u' (L', F', c') → c' = c
  | [], _, _, _, _, _, _, _, _, h => congrArg (fun s => s.2.2) h.2
  | t :: l, _, u', L, L', F, F', c, c', h => by
    obtain ⟨b1, s1, h1, h2⟩ := h
    have e : s1 = (L, F.rootTaken t 0, c) := h1
    subst e
    exact rootTurns_ctx l b1 u' L L' _ F' c c' h2

/-- The routine, from a context without an open message. -/
theorem rootInH_view (trees : List Nat) (L L' : LinkCtx) (F F' : Fork) (c c' : Ctx)
    (hc : PscRun.Clean c) (h : rootInH trees L F c = .ok ((((), L'), F'), c')) :
    ∃ ids r₁ r₂ shapes seeds ans,
      SendTook c (ReqFrame.notices (L.check.frame.atMoment L.check.frame.moment)) ids c' r₁ r₂
        shapes seeds ans := by
  obtain ⟨-, -, chk, c1, h1, h2⟩ := L5.rootInH_ran trees hc.1 h
  obtain rfl := rootTurns_ctx _ _ _ _ _ _ _ _ _ h2
  obtain ⟨r₁, r₂, shapes, seeds, ans, T⟩ :=
    checkLater_view L.check chk c _ hc ((Blk.yields_iff _ _ _ _).2 h1)
  exact ⟨_, r₁, r₂, shapes, seeds, ans, T⟩

/-- The routine on the view of a written transcript. -/
theorem rootInH_rvT (trees : List Nat) (L L' : LinkCtx) (F F' : Fork) (x x' : Ctx)
    (hc : PscRun.Clean x) (h : rootInH trees L F x = .ok ((((), L'), F'), x')) (d₁ d₂ : RDT)
    (ds : List RDT) (m₁ : (roundT (Run.ckP .two) d₁).up.Msg)
    (w₁ : (roundT (Run.ckP .two) d₁).up.Chal) (m₂ : (roundT (Run.ckP .two) d₂).up.Msg)
    (w₂ : (roundT (Run.ckP .two) d₂).up.Chal) (τ : Tr (uLT (Run.ckP .two) ds))
    (hl : x.ch.left = rvT (Run.ckP .two) (d₁ :: d₂ :: ds)
      ((m₁, w₁, m₂, w₂, τ) : Tr (uLT (Run.ckP .two) (d₁ :: d₂ :: ds)))) :
    ∃ ids shapes seeds ans,
      SendTook x (ReqFrame.notices (L.check.frame.atMoment L.check.frame.moment)) ids x'
        ⟨Run.PQ.PlainOf.gots d₁.items (GPlain.old (b := d₁.entry.work) m₁.2),
          (Run.ckP .two).dr d₁.entry d₁.kind (GChal.old (b := d₁.entry.work) w₁)⟩
        ⟨Run.PQ.PlainOf.gots d₂.items (GPlain.old (b := d₂.entry.work) m₂.2),
          (Run.ckP .two).dr d₂.entry d₂.kind (GChal.old (b := d₂.entry.work) w₂)⟩
        shapes seeds ans ∧
      x'.ch.left = rvT (Run.ckP .two) ds τ := by
  obtain ⟨ids, r₁, r₂, shapes, seeds, ans, T⟩ := rootInH_view trees L L' F F' x x' hc h
  obtain ⟨rfl, e⟩ := List.cons.inj (hl.symm.trans T.left)
  obtain ⟨rfl, e'⟩ := List.cons.inj e
  exact ⟨ids, shapes, seeds, ans, T, e'.symm⟩

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.rootTurns_ctx
#print axioms OnBytes.Tie.Pv.Tail.rootInH_view
#print axioms OnBytes.Tie.Pv.Tail.rootInH_rvT
