-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/StackCube.lean: CONDITIONAL.

What is here. The batched sumcheck's honest job (`jobStackOn`, Johnson/Desc/K4/Honest/Stack.lean)
against the premises that FlatStack.lean asks of a job.

What is shown. The job's degree in the further variable is 2. At as many challenges as the cube has
variables the true end values are made, and are as many as the call says. Along the masked line the
job's summand is a polynomial of degree at most 2, and it reads its values through the reading
(StackAffine.lean, at the job). The cube's summand at the challenges is the product of the two long
vectors' extensions at the point that the challenges make. Statements and proofs.

  `stack_fit_parts`   what fitting the call says of this job
  `stack_ends_some`, `stack_hn`   the true end values are made; their number
  `stack_hP`, `stack_hA`   a polynomial along the masked line; through the reading
  `stack_summandAt`   **the cube's summand at the challenges**
  `stack_hE`   the fifth premise, from hsides

Limits. At the reading `Reading.gl`. One premise: the job fits its call (`k4JobFits`,
Johnson/Desc/ProofFile/Honest/K4/Part.lean). THE FIFTH PREMISE OF FlatStack.lean (hE: on the true
end values the job's summand is the cube's) IS NOT SHOWN HERE: `stack_hE` has it from one hypothesis
(hsides; Johnson/Road/K4/C/StackTrue.lean has that): that the two numbers which the verifier's
function makes of the true end values read as the two long vectors' extensions at the challenges. No
example is known. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.StackAffine
import Johnson.Desc.ProofFile.Honest.K4.Law.AtEnds
import Johnson.Desc.K4.Honest.Law.Cube

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE mulE)
open OnBytes.Model (Reading orderDefault)
open OnBytes.Road (pt)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw

variable {D : StackData} {n : ℕ}

/-- What fitting the call says of this job: its cube fits; at lamS zeros it has n end values. -/
theorem stack_fit_parts (h : k4JobFits (k4PlainShape D.S.Q.hp.lamS 2 n) (jobStackOn D) = true) :
    (jobStackOn D).cube.fits = true ∧
      ((jobStackOn D).ends (List.replicate D.S.Q.hp.lamS zeroE)).length = n := by
  unfold k4JobFits k4PlainShape at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.length_replicate] at h
  exact ⟨h.1.1.1.1.1, h.2.2⟩

/-- The job's number of end values, at as many challenges as the cube has variables. -/
theorem stack_hn (h : k4JobFits (k4PlainShape D.S.Q.hp.lamS 2 n) (jobStackOn D) = true)
    (rs : List E) (hr : rs.length = (jobStackOn D).cube.n) :
    ((jobStackOn D).ends rs).length = n := by
  rw [stack_ends_len D (rs₀ := List.replicate D.S.Q.hp.lamS zeroE)
    (by rw [List.length_replicate]; exact hr)]
  exact (stack_fit_parts h).2

/-- **The true end values are made** at as many challenges as the cube has variables, where the
call says that there is an end value. -/
theorem stack_ends_some (h : k4JobFits (k4PlainShape D.S.Q.hp.lamS 2 n) (jobStackOn D) = true)
    (hn : 0 < n) (rs : List E) (hr : rs.length = (jobStackOn D).cube.n) :
    ∃ l, D.endsAt rs.toArray.reverse = some l ∧ (jobStackOn D).ends rs = l := by
  have hl := stack_hn h rs hr
  have hl' : ((D.endsAt rs.toArray.reverse).getD []).length = n := hl
  cases he : D.endsAt rs.toArray.reverse with
  | none =>
    rw [he] at hl'
    have : (0 : ℕ) = n := hl'
    omega
  | some l =>
    refine ⟨l, rfl, ?_⟩
    show (D.endsAt rs.toArray.reverse).getD [] = l
    rw [he]
    rfl

/-- Along the masked line the job's summand is a polynomial of degree at most the job's. -/
theorem stack_hP (D : StackData) (rs m : List E) :
    PolyOn (jobStackOn D).dY fun y =>
      (jobStackOn D).atEnds rs (maskedEnds ((jobStackOn D).ends rs) m y) :=
  summandOn_poly D rs.toArray.reverse _ m

/-- It reads its values through the reading. -/
theorem stack_hA (D : StackData) (rs : List E) : ReadsAlike ((jobStackOn D).atEnds rs) :=
  summandOn_alike D rs.toArray.reverse

/-- **The cube's summand at the challenges**: the product of the two long vectors' extensions at the
point that the challenges make. -/
theorem stack_summandAt (D : StackData) (hfit : (jobStackOn D).cube.fits = true) (rs : List E)
    (hr : rs.length = D.S.Q.hp.lamS) :
    Reading.gl.val ((jobStackOn D).cube.summandAt rs) =
      Blocks.ext D.S.Q.hp.lamS (fun i => Reading.gl.val (D.SA.getD i zeroE))
          (pt Reading.gl rs.toArray) *
        Blocks.ext D.S.Q.hp.lamS (fun i => Reading.gl.val (D.SB.getD i zeroE))
          (pt Reading.gl rs.toArray) := by
  have hp : (jobStackOn D).cube.pointOf rs = rs.toArray := pointOf_default _ hfit rfl rs hr
  have hz : rs.toArray.size = D.S.Q.hp.lamS := by simpa using hr
  rw [summandAt_read]
  show Reading.gl.val oneE *
    (Reading.gl.val (((jobStackOn D).cube.valuesAt rs).getD 0 zeroE) *
      Reading.gl.val (((jobStackOn D).cube.valuesAt rs).getD 1 zeroE)) + 0 = _
  rw [valuesAt_mle Reading.gl _ hfit rs hr, valuesAt_mle Reading.gl _ hfit rs hr, hp,
    Reading.gl.one, one_mul, add_zero]
  show Reading.gl.val (mle D.SA rs.toArray) * Reading.gl.val (mle D.SB rs.toArray) = _
  rw [mle_ext, mle_ext, hz]

/-- **The fifth premise**, from the hypothesis that the two numbers which the verifier's function
makes of the true end values read as the two long vectors' extensions. -/
theorem stack_hE (h : k4JobFits (k4PlainShape D.S.Q.hp.lamS 2 n) (jobStackOn D) = true)
    (hn : 0 < n)
    (hsides : ∀ (rb : Array E) (l : List E), rb.size = D.S.Q.hp.lamS → D.endsAt rb = some l →
      ∃ x, D.sidesOn rb l.toArray = some x ∧
        Reading.gl.val x.1 = Blocks.ext D.S.Q.hp.lamS
          (fun i => Reading.gl.val (D.SA.getD i zeroE)) (pt Reading.gl rb.reverse) ∧
        Reading.gl.val x.2 = Blocks.ext D.S.Q.hp.lamS
          (fun i => Reading.gl.val (D.SB.getD i zeroE)) (pt Reading.gl rb.reverse))
    (rs : List E) (hr : rs.length = (jobStackOn D).cube.n) :
    Reading.gl.val ((jobStackOn D).atEnds rs ((jobStackOn D).ends rs)) =
      Reading.gl.val ((jobStackOn D).cube.summandAt rs) := by
  obtain ⟨l, he, el⟩ := stack_ends_some h hn rs hr
  obtain ⟨x, hx, h1, h2⟩ := hsides rs.toArray.reverse l
    (by rw [Array.size_reverse, List.size_toArray]; exact hr) he
  rw [el, stack_summandAt D (stack_fit_parts h).1 rs hr]
  show Reading.gl.val ((D.summandOn rs.toArray.reverse l.toArray).getD zeroE) = _
  unfold StackData.summandOn
  rw [hx]
  show Reading.gl.val (mulE x.1 x.2) = _
  rw [Reading.gl.mul, h1, h2, Array.reverse_reverse]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.stack_fit_parts
#print axioms ProofFile.Honest.K4.stack_hn
#print axioms ProofFile.Honest.K4.stack_ends_some
#print axioms ProofFile.Honest.K4.stack_hP
#print axioms ProofFile.Honest.K4.stack_hA
#print axioms ProofFile.Honest.K4.stack_summandAt
#print axioms ProofFile.Honest.K4.stack_hE
