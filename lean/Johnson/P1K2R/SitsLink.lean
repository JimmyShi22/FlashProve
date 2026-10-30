-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/SitsLink.lean (over Johnson/P1K2R/SitsDoor.lean,
Johnson/Top/H0/Tw/K2C/LinkStays.lean and Johnson/Top/H0/Walk/FrameOpened.lean): AT A LINK's FIRST PLACE A YES OF THE
SEATED SWITCH SAYS THAT THE RECORD's FRAME BEARS THE PLACE's OWN LINK NUMBER. NO BLOCK IMPORTS
THIS FILE. Why. The law's premises on the front (FrontNums' third clause, by K2Hands/TiedAt.lean)
are asked at the planner's record number s.check.frame.link: the RECORD's number. That it is the
PLACE's number l is tested by no clause of the switch; but the link's own «opened», which the seat
joins behind the switch, tests it, and the switch leaves the number. So where the two numbers part
the seated block has no yes, and a law at that block holds there idly.
  link_of_yes   Sits b (K2.codeSwitchKind p) (the identity) (leaveOpened f) at p.stands = .link, f the l-th
                row of framesOf, the l-th link's record not the head's: a yes of b's step at s:
                s.check.frame.link = l
LIMITS. The dress «link» alone. That the l-th link's record is not the head's is a premise (in
scope: l < 24). At the head's link the like holds of the head's own part's frame
(K2C/HeadLink.lean), not of s.check.frame. No soundness is claimed.
-/
import Johnson.P1K2R.SitsDoor
import Johnson.Top.H0.Tw.K2C.LinkStays

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 codeSwitchKind)
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf)
open H2K.JointK (Sits)
open ProofFile (Cl)

theorem link_of_yes {built : Array OnBytes.Model.Stages.LinkH} {first : OnBytes.Params.First}
    {W : OnBytes.Model.Verify.Public} {fs : List LinkFrame} {f : LinkFrame} {l : Nat}
    (hfs : framesOf built first W = .ok fs) (hf : fs[l]? = some f)
    {X : OnBytes.Model.Stages.LinkH} (hX : built[l]? = some X) (hk : X.kind ≠ 2)
    {b : Block S Cl} {p : P2} (hp : p.stands = .link)
    (hs : Sits b (codeSwitchKind p : Block S Unit) (fun s => .ok s) (fun s t => leaveOpened f s t))
    {ft : Nat} {s s' : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {k : Nat}
    (h : b.step ft s rs cols = .ok (s', k)) : s.check.frame.link = l := by
  obtain ⟨t, t', e1, e2, e3⟩ := hs.step ft s s' rs cols k h
  obtain rfl : s = t := Except.ok.inj e1
  have hd := ((VerifiableInference.Desc.Sound.step_ok_iff ft _ s t' rs cols k).1 e2).2.2.2
  have k1 := (VerifiableInference.Desc.First.K2.yes_link_stays hp hd).2.1
  have k2 := Johnson.Desc.First.Walk.Tied.opened_at_link hfs hf hX hk (leaveOpened_is e3)
  exact k1.symm.trans k2

end P1K2

#print axioms P1K2.link_of_yes
