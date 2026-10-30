-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/HeadValsOf.lean: the kind "lookup" (K3): when the test
on values `headVals` (Honest/K3/Law/Thread/ClaimReturns.lean) accepts at a state, with each
hypothesis sorted by whose it is to show; and what its acceptance says of the state. Theorems.

Terms. Honest/K3/GLOSSARY.md.

What is shown.
  `headVals_of`: the test accepts under the six hypotheses listed below.
  `headVals_head`: where it accepts, the chain stands in the head's link, and what the head heard
    and its tables are laid.

Hypotheses that remain, in `headVals_of`.
  `ha`, `hx`, `ht`: the chain stands in the head's link, with what the head heard and its tables
    laid. These are for other parts to show.
  `hc`: "covered" returns. This is for another kind's files to show.
  `hL`: the public test `layoutOk` (Honest/K3/Law/Thread/ClaimSizes.lean) accepts.
  `hw`: the checked token of every covered position is an entry of the vocabulary. This is one fact
    on what the head heard.
In `headVals_head`: `h`: the test accepts at the state.

How the proof goes. `weightsClaim_returns` (ClaimReturns.lean) is called at the structure that the
step without a round behind the lookup on the head's digits hands to `weightsClaim`. The file is
written over the library's own files and files of this folder alone.

Users. Honest/K3/Law/Thread/CarriesHeadDigits.lean calls `headVals_head`.

Limits. Neither test is evaluated in this file. Both are evaluated in
Honest/K3/Law/Thread/CarriesGuardsHead.lean [not in this library], at states that the test makes up:
they accept at one of three small synthetic
public parts and reject at the two others. No instance of these hypotheses is exhibited in this
file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ClaimReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc.First.Look (weightsClaim)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **When the test on values accepts.** Conditional on the six hypotheses. -/
theorem headVals_of {X : OnBytes.Model.Verify.Public} {s : FS}
    {a : VerifiableInference.Desc.First.HeadOwn} {x : OnBytes.Model.Head.Heard}
    {tt : OnBytes.Model.Head.Tables} {cov : OnBytes.Model.Head.Covered} (ha : s.here = .head a)
    (hx : a.x = some x) (ht : a.t = some tt) (hc : s.covered X.T X.P.h.V = .ok cov)
    (hL : layoutOk X.HLy X.layers.wsLay = true)
    (hw : ∀ t, t < X.hS.T → cov.hOn.getD t false = true → x.win.getD t 0 < X.hS.V) :
    headVals X s = true := by
  obtain ⟨cl, hcl⟩ := weightsClaim_returns
    (R :=
      { h := X.hS, L := X.HLy, b := OnBytes.Model.Verify.borderOf X.y, hp := X.H, cov := cov,
        x := x, t := tt, iU3 := (X.H.tl.ix.U.getD 2 none).getD 0 })
    (lay := X.layers.wsLay) hL hw
  unfold headVals
  rw [ha]
  dsimp only
  rw [hx, ht, hc]
  dsimp only
  rw [hcl]
  rfl

/-- Where the test accepts, the chain stands in the head's link, and what the head heard and its
tables are laid. -/
theorem headVals_head {X : OnBytes.Model.Verify.Public} {s : FS} (h : headVals X s = true) :
    ∃ a, s.here = .head a ∧ a.x.isSome = true ∧ a.t.isSome = true := by
  unfold headVals at h
  cases hh : s.here with
  | head a =>
    rw [hh] at h
    dsimp only at h
    refine ⟨a, rfl, ?_, ?_⟩
    · cases hx : a.x with
      | none =>
        rw [hx] at h
        exact nomatch h
      | some _ => rfl
    · cases hx : a.x with
      | none =>
        rw [hx] at h
        exact nomatch h
      | some _ =>
        cases ht : a.t with
        | none =>
          rw [hx, ht] at h
          exact nomatch h
        | some _ => rfl
  | _ =>
    rw [hh] at h
    exact nomatch h

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.headVals_of
#print axioms ProofFile.Honest.K3.Law.AtThr.headVals_head
