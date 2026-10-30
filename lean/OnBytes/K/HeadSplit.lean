-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/HeadSplit.lean: the head's routine, cut before and behind its call of `Head.hear`, with
the steps as clauses. For proofs only; the program does not import this file.

`Head.runForkHidH2` (OnBytes/Model/Head.lean) makes some steps, calls `hear` on the plain scalars of
the link's state with which it was called, and goes on with what `hear` has returned. This file
writes the two parts out as routines of their own and shows (`run_eq`: by unfolding and the laws of
bind) that the library's routine is the one, then `hear`, then the other. The text of the two parts
follows the library's line for line.
  `beforeHear`: the steps before `hear`. It returns the link's state as it was at the call, and the
    number of the tree that the routine needs later.
  `afterHear`: the steps behind `hear`, at what `hear` has returned.
  `run_eq`: the routine is `beforeHear`, then `hear` on that state's plain scalars, then
    `afterHear`.
  `head_split`: where the routine, called with the link's state Lc from the states F and c, returns
    r: `beforeHear` has returned from Lc, F, c; the state that it returns is Lc; `hear` has returned
    x on Lc's plain scalars from the states that `beforeHear` has left; `afterHear` at that very x
    has returned r from the states that `hear` has left; and `x.win` is `winOf cov h.T (tokenOf …)`.
So the second part of the routine has run at that very x. Which of its steps read the field `win` is
not said here.
What is not claimed: what `afterHear` does with x.


-/
import OnBytes.K.ReplyHear
import OnBytes.Model.Head

set_option autoImplicit false

namespace OnBytes.K

open OnBytes OnBytes.Model OnBytes.Model.Head
open OnBytes.Cut (bindL liftS_ok liftB_ok)

/-- The head's routine before its call of `hear`. -/
def beforeHear (h : Shape) (hp : HPlanH2) (b : Border) (O : Owner) (cov : Covered) :
    LinkM (LinkCtx × Nat) := do
  mustAs "internal-h-covered" (cov.sized h.T)
  let C ← get
  mustAs "plan-link" (planHanded hp C.list (← LinkM.fork))
  LinkM.sub (SubM.change fun F => some ({ trees := F.trees } : Fork).fillL)
  mustAs "internal-h-owner-TX" (!O.tl.ix.TX.isEmpty && O.tl.kTX.back? == some b.kxb)
  let iU3 ← getAs "internal-h-tree-list" (hp.tl.ix.U.getD 2 none)
  pure (C, iU3)

/-- The head's routine behind its call of `hear`, at what `hear` has returned. -/
def afterHear (h : Shape) (L : HL) (b : Border) (hp : HPlanH2) (cov : Covered) (wsLay : WsLay)
    (iU3 : Nat) (x : Heard) : LinkM WsForkOut := do
  rootInH [iU3]
  let t ← tablesOf h L hp cov x
  let R : Head.Run :=
    { h := h, L := L, b := b, hp := hp, cov := cov, x := x, t := t, iU3 := iU3 }
  let tl ← getAs "internal-f-fun-closed" (hp.tl.closeFuns t.funs)
  let tl ← tl.transcript
  let claim ← weightsClaim R wsLay
  mustAs "internal-claim-count" (hp.NCL == 1)
  let wo ← wsForkEnd wsLay #[claim] #[x.sV]
  let slot ← SubM.slot
  mustAs "internal-slot-count" (slot == hp.nMsg)
  SubM.setPlanClaims hp.nLin
  t2Batch slot
  let tl ← walk R tl wo
  selfTests R tl wo
  doorH (← getAs "internal-f-draws" tl.equationsLaidF)
  let F ← LinkM.fork
  mustAs "internal-f-draws" (F.nClaim == F.planClaimsF)
  SubM.allTaken
  mustAs "internal-f-draws" tl.foldAllTakenF
  pure wo

/-- The library's routine is the first part, then `hear`, then the second part. -/
theorem run_eq (h : Shape) (L : HL) (b : Border) (hp : HPlanH2) (O : Owner) (cov : Covered)
    (wsLay : WsLay) :
    runForkHidH2 h L b hp O cov wsLay = (do
      let p ← beforeHear h hp b O cov
      let x ← hear h L hp cov p.1.check.plain
      afterHear h L b hp cov wsLay p.2 x) := by
  unfold runForkHidH2 beforeHear afterHear
  simp only [bind_assoc, pure_bind]

/-- What the first part returns is the link's state with which it was called; and its first test was
true. -/
theorem before_state {h : Shape} {hp : HPlanH2} {b : Border} {O : Owner} {cov : Covered}
    {Lc L1 : LinkCtx} {F F1 : Fork} {c c1 : Ctx} {p : LinkCtx × Nat}
    (hr : beforeHear h hp b O cov Lc F c = .ok (((p, L1), F1), c1)) :
    p.1 = Lc ∧ cov.sized h.T = true := by
  unfold beforeHear at hr
  obtain ⟨_, La, Fa, ca, h1, hr⟩ := bindL hr
  obtain ⟨_, _, m1, e1⟩ := liftB_ok h1
  have eL : La = Lc := congrArg (fun t => t.1.1.2) e1
  have hs1 : cov.sized h.T = true := by
    cases hb : cov.sized h.T with
    | true => rfl
    | false =>
      rw [hb] at m1
      cases m1
  obtain ⟨C, Lb, Fb, cb, h2, hr⟩ := bindL hr
  have eC : C = La := by
    have h2' : (Except.ok (((La, La), Fa), ca) : Except Failure _) = .ok (((C, Lb), Fb), cb) := h2
    exact (congrArg (fun t => t.1.1.1) (Except.ok.inj h2')).symm
  obtain ⟨_, _, _, _, _, hr⟩ := bindL hr
  obtain ⟨_, _, _, _, _, hr⟩ := bindL hr
  obtain ⟨_, _, _, _, _, hr⟩ := bindL hr
  obtain ⟨_, _, _, _, _, hr⟩ := bindL hr
  obtain ⟨iU3, _, _, _, _, hr⟩ := bindL hr
  have ep : p = (C, iU3) := (congrArg (fun t => t.1.1.1) (Except.ok.inj hr)).symm
  rw [ep, eC, eL]
  exact ⟨rfl, hs1⟩

/-- **The head's routine, cut before and behind `hear`.** In words: the head of this file. -/
theorem head_split {h : Shape} {L : HL} {b : Border} {hp : HPlanH2} {O : Owner} {cov : Covered}
    {wsLay : WsLay} {Lc : LinkCtx} {F : Fork} {c : Ctx}
    {r : ((WsForkOut × LinkCtx) × Fork) × Ctx}
    (hr : runForkHidH2 h L b hp O cov wsLay Lc F c = .ok r) :
    cov.sized h.T = true ∧
      ∃ iU3 L1 F1 c1 x F2 c2,
        beforeHear h hp b O cov Lc F c = .ok ((((Lc, iU3), L1), F1), c1) ∧
        hear h L hp cov Lc.check.plain F1 c1 = .ok ((x, F2), c2) ∧
        afterHear h L b hp cov wsLay iU3 x L1 F2 c2 = .ok r ∧
        x.win = winOf cov h.T (tokenOf Lc.check.plain) := by
  rw [run_eq] at hr
  obtain ⟨p, L1, F1, c1, h1, hr1⟩ := bindL hr
  clear hr
  obtain ⟨e1, hs⟩ := before_state h1
  obtain ⟨C, iU3⟩ := p
  have e1' : C = Lc := e1
  subst e1'
  obtain ⟨x, L2, F2, c2, h2, hr2⟩ := bindL hr1
  obtain ⟨x', F2', c2', hq, e2⟩ := liftS_ok h2
  have ex : x = x' := congrArg (fun t => t.1.1.1) e2
  have eL : L2 = L1 := congrArg (fun t => t.1.1.2) e2
  have eF : F2 = F2' := congrArg (fun t => t.1.2) e2
  have ec : c2 = c2' := congrArg (fun t => t.2) e2
  subst ex eL eF ec
  exact ⟨hs, iU3, L2, F1, c1, x, F2, c2, h1, hq, hr2, hear_win hq⟩

end OnBytes.K
