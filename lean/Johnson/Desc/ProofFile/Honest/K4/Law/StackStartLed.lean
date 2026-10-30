-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/StackStartLed.lean: CONDITIONAL.

What is here. The premise on the start (hσ) of StackOwn.lean and StackLed.lean: the start form that
the verifier's text makes (`joinStart`, OnBytes/Desc/First/K4/Hear.lean) is worth the reading of the
total of the honest job's cube.

What is shown. Whatever start form the verifier's text returns is the library's `startOf` at the
factors that it has made (`joinStart_startOf`, Johnson/Road/K4/JoinTie.lean); its worth is the
total, by StackStart.lean's `stack_sigma` with StackPass.lean (the total is the two passes' sums)
and StackSecond.lean (the second pass's sum). One statement and its proof.

  `stack_sigma_of`   **the start form's worth**

Limits. At the reading `Reading.gl`. THREE HYPOTHESES BEAR THE CONTENT. `JoinWorth`
(StackStart.lean), at the factors that the verifier's text makes: THE FIRST PASS IS THE LOOKUP's
JOIN: it crosses into the lookup's own rounds and the keys' arithmetic, and nothing here shows it.
hKT: the form that the second token sumcheck leaves is worth the honest side's summand at that
sumcheck's end point on the values as the job's data hold them (TermsTop.lean has the like, written
with the masked end values: that the two are one number is not shown here). hval: a form that has a
value on the reads at the token point alone has the same value on the reads at all points sampled so
far. Beside them: the maker of the job's data returns; the summand returns; the honest side's two
weights are the verifier's. No example of the premises together is known. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.StackSecond
import Johnson.Road.K4.JoinTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork World Tsc)
open OnBytes.K.Kc (Tape)
open OnBytes.Desc.First.K4 (engFl)
open OnBytes.Desc.First.K4.Honest

/-- **The start form that the verifier's text makes is worth the total of the honest job's cube.**
sT: the second token sumcheck's summand at its end point on the values that the job's data hold as
shown. -/
theorem stack_sigma_of {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {D : StackData}
    (hD : stackData Q w p shownT = some D) {v : OnBytes.Model.Layer.Env}
    {H : OnBytes.Model.Layer.Heard} {om : Array E} (hom : p.om = om) (Wd : World Cb.Gl.E) {sT : E}
    (hs : D.S.summand shownT p.rt = some sT)
    (hval : ∀ R, D.S.readsTok p.rt = some R → ∀ a y,
      valAff? D.S.v R (fun _ => zeroE) a = some y →
        valAff? D.S.v D.R (fun _ => zeroE) a = some y)
    (hKT : H.KT.value Reading.gl Wd = Reading.gl.val sT)
    (hJ : ∀ (weighed : Array _) (parts : List Aff) (tT : Tsc),
      v.y.calls.mapM v.weighedOf = some weighed →
      ((v.y.calls.zip weighed).toList.zipIdx.mapM fun x =>
        v.joinPart H.fo.alpha H.fo.theta x.2 x.1.1 x.1.2) = some parts →
      H.tT = some tT → JoinWorth H tT parts Wd D)
    {C : Aff} {F F' : Fork} {t t' : Tape}
    (hC : OnBytes.Desc.First.K4.joinStart engFl v H om F t = some (C, F', t')) :
    C.value Reading.gl Wd = Reading.gl.val (jobStackOn D).cube.total := by
  obtain ⟨weighed, parts, _, tT, hw, hp, _, _, _, hT, rfl, _, _⟩ :=
    OnBytes.Road.K4.joinStart_startOf hC
  have hD' := hD
  unfold stackData at hD'
  obtain ⟨S, _, hS⟩ := Option.bind_eq_some_iff.mp hD'
  have eS : D.S = S := (stackDataOn_open hS).1
  rw [eS] at hs hval
  exact stack_sigma H om parts hT Wd D sT (stack_total_of hD)
    (by rw [← hom]; exact second_pass hS hs hval) hKT (hJ weighed parts tT hw hp hT)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.stack_sigma_of
