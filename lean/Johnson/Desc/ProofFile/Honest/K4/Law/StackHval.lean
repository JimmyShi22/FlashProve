-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/StackHval.lean: CONDITIONAL.

What is here. The premise hval of StackSecond.lean and of what stands over it: a form that has a
value on the honest reads at the second token sumcheck's end point alone has the same value on the
reads that the batched sumcheck's data hold, which are taken at all points sampled so far.

  `stack_hval`   **hval**

Limits. Equations between machine words. Premises: the maker of the job's data returns; the lookup's
point is not empty; the second token sumcheck's end point has a coordinate for each bit of a token's
number. The law on the reads is Johnson/Road/K4/C/ReadsAgree.lean's; here it is called at the data's
own letters. No property is claimed.
-/
import Johnson.Road.K4.C.ReadsAgree
import Johnson.Road.K4.C.StackSidesOf
import Johnson.Road.K4.C.TermsAtOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Aff)
open OnBytes.Road.K4.C (valAffQ_agree tok_named sides_fields stack_open)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In Pts StackData stackData valAff?)

/-- **A form's value on the reads at the token point alone is its value on the data's reads.** -/
theorem stack_hval {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {D : StackData}
    (hD : stackData Q w p shownT = some D) (he : p.fo.zx.isEmpty = false)
    (hs : p.rt.size = Q.P.y.h.lt) :
    ∀ R, D.S.readsTok p.rt = some R → ∀ (a : Aff) (y : E),
      valAff? D.S.v R (fun _ => zeroE) a = some y →
        valAff? D.S.v D.R (fun _ => zeroE) a = some y := by
  intro R hR a y h
  obtain ⟨hS, hR', _⟩ := stack_open hD
  obtain ⟨eQ, ew, efo, hv, ⟨Z, hZ, ez⟩, _, _⟩ := sides_fields hS
  have hR0 : OnBytes.Desc.First.K4.Honest.readsAt Q w p.fo
      (OnBytes.Road.K4.C.tokPts (Z.extract 0 Q.P.y.ls) p.rt) = some R := by
    have h0 : OnBytes.Desc.First.K4.Honest.readsAt D.S.Q D.S.w D.S.fo
        (OnBytes.Road.K4.C.tokPts D.S.zlow p.rt) = some R := hR
    rw [eQ, ew, efo, ez] at h0
    exact h0
  -- the verifier's list of tables is laid: the structure that the forms read is made of it
  have hl : ∃ r, OnBytes.Model.Layer.layTables (OnBytes.Desc.First.K4.Honest.matsOf Q)
      (OnBytes.Model.Layer.tableAsks Q.P.y Q.P.rd Q.g) 0 = some r := by
    unfold OnBytes.Desc.First.K4.Honest.envOf at hv
    obtain ⟨_, _, hv⟩ := Option.bind_eq_some_iff.mp hv
    obtain ⟨r, hr, _⟩ := Option.bind_eq_some_iff.mp hv
    exact ⟨r, hr⟩
  obtain ⟨r, hl⟩ := hl
  exact valAffQ_agree hR0 hR' hl (tok_named hZ he hs) h

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.stack_hval
