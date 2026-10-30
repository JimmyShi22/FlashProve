-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Fit/FitTop.lean: wherever the program's planner returns at three configuration files,
every entry of the six plans of a key file's and a proof file's chains, as they are read back from
the chains' parameter bytes, asks few blocks of a hash chain's answer and counts at most two roots:
under caps on two records of sizes.

Main names:
  made_small_planned: from Verify.planned pol KL layout = .ok p, ReqCap of the proof's sizes and
    KeyCap of the key's (OnBytes/Params/Fit/FitPlans.lean): every entry of the six plans as made is
    Small (OnBytes/Params/Fit/FitCalc.lean).
  fits_of_planned_caps: so Six Fits p (SmallRead.lean in this folder): of every entry e of the six
    plans as read back: e.logN ≤ 64, Fmt.blocksFor (Fmt.wordsAtMost e .sealed) + 1 < 2 ^ 48 and
    e.roots ≤ 2.
How it goes: planned's yes is taken apart (PlannedParts.lean); the 32 lines' reader gives the caps
on the setting (OnBytes/Params/Fit/LinesCap.lean, SetCapOf.lean); the sub-proofs' routines keep
Small (FitLinks.lean); so do the six plans' (FitPlans.lean); the plans as read back are the plans as
made with their numbers modulo 2 ^ 64 (ReadNormMade.lean).
Limits: the two caps are premises here (FitPlanned.lean in this folder has the statement without
them). Nothing where the planner refuses. Nothing on the plan of an entry's chain
(Configured.entry), which the planner also makes. "sealed" is the kind of round with the most words.
The program does not import this file.

-/
import OnBytes.Model.Fit.FitLinks
import OnBytes.Model.Fit.PlannedParts
import OnBytes.Model.Fit.SmallRead
import OnBytes.Params.Fit.SetCapOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Model.Verify

open OnBytes.Params (Small ReqCap KeyCap)

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}

theorem made_small_planned (h : planned pol KL layout = .ok p)
    (R : ReqCap p.chains.made.sized.proof) (C : KeyCap p.chains.made.sized.key) :
    ∀ P ∈ p.chains.made.key ++ p.chains.made.proof, ∀ r ∈ P.rounds, Small r.entry := by
  obtain ⟨links, shapes, rest, declared, file, rl, lay, hX, hL, _, h1, h2, hc, _⟩ :=
    planned_parts h
  have S := Params.setCap_of_read hL
  exact Params.made_small hc S R C (sub_keeps hX S h1 h2)

theorem fits_of_planned_caps (h : planned pol KL layout = .ok p)
    (R : ReqCap p.chains.made.sized.proof) (C : KeyCap p.chains.made.sized.key) : Six Fits p :=
  fits_read h (made_small_planned h R C)

end

end OnBytes.Model.Verify

#print axioms OnBytes.Model.Verify.fits_of_planned_caps
