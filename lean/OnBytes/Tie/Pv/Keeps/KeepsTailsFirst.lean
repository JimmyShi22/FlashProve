-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Keeps/KeepsTailsFirst.lean: behind a link's first call (ChainCheck.first), on a view,
no message is open; so none is open at any of the four contexts of a call of runLinkH but the first.

Statements and proofs, by the laws of OnBytes/Tie/Pv/Keeps/KeepsTails.lean. The first call ends in a
sending that closes its own round of answers (the first link) or in the switch, and then joins the
messages to the link's group, which leaves the channel as it was.
Main names:
  `close_ends`, `closeEmpty_ends`: behind a closing no message is open.
  `sendVerify_ends`: the same behind a sending that closes its own round of answers.
  `csSigmaVerify_ends`: the same behind the switch (OnBytes/Tie/Pv/Switch/LocClean.lean).
  `first_clean`: the same behind ChainCheck.first.
  `linkStep_clean3`: in one call of runLinkH whose link's routine is `EndsClean`: no message is open
    behind the first call, behind the routine, or at the end of the call.
  `linkStep_took`: so, if none is open where the call began, each of its three stretches
    (OnBytes/Tie/Pv/Keeps/KeepsCut.lean) is what that part took, in whole rounds.
  `LinkStep.unique_all`: two records of one call of runLinkH from one beginning name the same eight
    values and contexts.
Limits: one direction: from a success. Nothing on a dry run.
-/
import OnBytes.Tie.Pv.Keeps.KeepsCutList
import OnBytes.Tie.Pv.Keeps.KeepsTailsLinks
import OnBytes.Tie.Pv.Switch.LocClean

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Keeps.Cut

open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.L5

theorem close_ends (name : String) (kind : Fmt.Kind) (nz : Nat) :
    EndsClean (Blk.close name kind nz) := fun c d c' h hd => by
  obtain ⟨_, _, _, _, _, _, _, _, k, _⟩ := PscRun.close_view name kind nz d c c' hd h
  exact k.2

theorem closeEmpty_ends (name : String) : EndsClean (Blk.closeEmpty name) := by
  unfold Blk.closeEmpty
  exact (close_ends _ _ _).andThen fun _ => LeavesCh.pure _

theorem sendOwn_ends (ids : Array Nat) : EndsClean (Send.verify ids true) := by
  unfold Send.verify
  simp only [↓reduceIte]
  tail_walk (closeEmpty_ends _)

theorem sendVerify_ends (notices : Array OracleNotice) : EndsClean (sendVerify notices true) := by
  unfold sendVerify
  exact EndsClean.behind (by keepsM) fun ids =>
    (sendOwn_ends ids).andThen fun _ => LeavesCh.pure _

theorem csSigmaVerify_ends (old : SingleRows) (T : SwitchTarget) (gp : Nat)
    (others : Array OracleNotice) : EndsClean (csSigmaVerify old T gp others) :=
  fun c out c' h hd => by
    obtain ⟨D, R⟩ :=
      Switch.csSigmaVerify_ran old T gp others out c c' hd ((Blk.yields_iff _ _ _ _).2 h)
    exact (R.clean hd).2

/-- Behind a link's first call, on a view, no message is open. -/
theorem first_clean {k chk : ChainCheck} {c c1 : Ctx} (hd : c.ch.dry = false)
    (h : k.first c = .ok (chk, c1)) : PscRun.Clean c1 := by
  obtain ⟨r, L, G, g, plain, kept, ids, mask, j, c4, c5, c6, c7, P, _, _⟩ :=
    check_first_parts (cEnd := c1) k hd id h
  refine Open.FirstPartsCleanEnd P ⟨P.v7, ?_⟩
  by_cases h0 : (g.link == 0) = true
  · exact sendVerify_ends _ c6 ids c7 (P.sendFirst h0).1 P.v6
  · obtain ⟨s, hs, _, _⟩ := P.switch h0
    exact csSigmaVerify_ends _ _ _ _ c6 s c7 hs P.v6

section Step

variable {links : Array LinkH} {p : Params.First} {wsLay : WsLay} {cEnd : Ctx} {l : Nat}
  {X : LinkH} {check : ChainCheck} {out : Proof.LinksResult} {c : Ctx}
  {r : ChainCheck × Proof.LinksResult} {c' : Ctx} {chk : ChainCheck} {o : Option WsForkOut}
  {C' : LinkCtx} {F' : Fork} {c1 c2 : Ctx}

/-- One call of runLinkH, begun on a view. -/
theorem linkStep_clean3 (hX : EndsClean X.run) (hd : c.ch.dry = false)
    (S : LinkStep links p wsLay cEnd l X check out c r c' chk o C' F' c1 c2) :
    PscRun.Clean c1 ∧ PscRun.Clean c2 ∧ PscRun.Clean c' :=
  ⟨first_clean hd S.first, linkStep_clean hX S⟩

/-- Each of the three stretches is what that part took, in whole rounds. -/
theorem linkStep_took [KeepsM X.run] (hX : EndsClean X.run) (hc : PscRun.Clean c)
    (S : LinkStep links p wsLay cEnd l X check out c r c' chk o C' F' c1 c2) :
    PscRun.Took c (used c c1) c1 ∧ PscRun.Took c1 (used c1 c2) c2 ∧
      PscRun.Took c2 (used c2 c') c' := by
  obtain ⟨k1, k2, k3⟩ := linkStep_clean3 hX hc.1 S
  obtain ⟨q1, q2, q3⟩ := kept_parts S
  exact ⟨took_of_kept q1 hc k1, took_of_kept q2 k1 k2, took_of_kept q3 k2 k3⟩

end Step

/-- One call of runLinkH is determined by where it began: all eight values and contexts. -/
theorem LinkStep.unique_all {links : Array LinkH} {p : Params.First} {wsLay : WsLay}
    {cEnd cEnd' : Ctx} {l : Nat} {X : LinkH} {check : ChainCheck} {out : Proof.LinksResult}
    {c : Ctx} {r r' : ChainCheck × Proof.LinksResult} {c' c'' : Ctx} {chk chk' : ChainCheck}
    {o o' : Option WsForkOut} {C' C'' : LinkCtx} {F' F'' : Fork} {c1 c1' c2 c2' : Ctx}
    (S : LinkStep links p wsLay cEnd l X check out c r c' chk o C' F' c1 c2)
    (S' : LinkStep links p wsLay cEnd' l X check out c r' c'' chk' o' C'' F'' c1' c2') :
    r = r' ∧ c' = c'' ∧ chk = chk' ∧ o = o' ∧ C' = C'' ∧ F' = F'' ∧ c1 = c1' ∧ c2 = c2' := by
  obtain ⟨e1, e2, e3, e4⟩ := LinkStep.unique S S'
  obtain ⟨rfl, _⟩ : chk = chk' ∧ c1 = c1' :=
    Prod.mk.inj (Except.ok.inj (S.first.symm.trans S'.first))
  subst e3
  have e5 := S.run.symm.trans S'.run
  obtain ⟨rfl, rfl, rfl, _⟩ : o = o' ∧ C' = C'' ∧ F' = F'' ∧ c2 = c2' := by
    cases e5
    exact ⟨rfl, rfl, rfl, rfl⟩
  exact ⟨e1, e2, rfl, rfl, rfl, rfl, rfl, e4⟩

end OnBytes.Tie.Pv.Keeps.Cut

#print axioms OnBytes.Tie.Pv.Keeps.Cut.sendVerify_ends
#print axioms OnBytes.Tie.Pv.Keeps.Cut.first_clean
#print axioms OnBytes.Tie.Pv.Keeps.Cut.linkStep_took
#print axioms OnBytes.Tie.Pv.Keeps.Cut.LinkStep.unique_all
