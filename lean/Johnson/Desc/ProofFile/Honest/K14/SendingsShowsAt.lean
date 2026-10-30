-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsShowsAt.lean: SendShapes
(Honest/K14/SendingsShows.lean) follows from a test with code on public data (carriersFit,
Honest/K14/SendingsShapes.lean: a conjunct of the one test sendingsFit), and holds at the small
shape of Johnson/Desc/K14/Honest/Toy.lean and at the two typed shapes.

  vecShape_of, sendShapes_of   where the test accepts, VecShape and SendShapes hold
  sendShapes_toy, sendShapes_key, sendShapes_real   by kernel evaluation of the test
  The #guard commands: the test accepts the small shape, and rejects it with o_u's entries over the
  base field, and with a mask row at o_omega.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

Limits. That a proof's sizes at the release's files are the typed ones is not claimed; the typed
sizes over a proof file's own codes hold numbers that are written by hand. HalfIn, the other premise
of showsU_of and showsO_of on a field of O, is shown at one laid term of the open letters, where the
shape splits, in Honest/K14/Thread2Full.lean (halfIn_full).
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingsShows
import Johnson.Desc.ProofFile.Honest.K14.SendingsShapes
import Johnson.Desc.ProofFile.Honest.K14.Thread2Member
import Johnson.Desc.K14.Honest.Toy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params OnBytes.Params.Prices OnBytes.Plan Johnson.G
open VerifiableInference.Desc.K1 (realSized)
open Lk6.AtPlan (keyFull)
open Desc.K14 (P14)

/-- Where the test on one shape accepts, VecShape holds. -/
theorem vecShape_of {codes : Codes} {s : OracleShape} (h : vecShapeFits codes s = true) :
    VecShape codes s := by
  unfold vecShapeFits at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2⟩

/-- Where the test accepts, SendShapes holds. -/
theorem sendShapes_of (Q : P14) (h : carriersFit Q.codes Q.S = true) : SendShapes Q := by
  unfold carriersFit at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨vecShape_of h.1.1.1, vecShape_of h.1.1.2, ?_⟩
  show ((Desc.K14.parK1 Q 2 "o_u and the first mask"
    ((Desc.K14.withU Q.S).getD #[])).sent.getD 1 default).shape.mainRows = 0
  rw [Desc.K14.Law.parK1_sent]
  exact h.1.2

/-- At the small shape. -/
theorem sendShapes_toy : SendShapes Desc.K14.Honest.Toy.P :=
  sendShapes_of _ (by decide +kernel)

/-- At the typed sizes of a key of full size. -/
theorem sendShapes_key (item : Nat) (bp : List (Nat × Nat)) :
    SendShapes ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩ :=
  sendShapes_of _ (by
    show carriersFit keyFull.codes keyFull.once.shape = true
    decide +kernel)

/-- At the typed sizes over a proof file's own codes. -/
theorem sendShapes_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧
    ∀ (item : Nat) (bp : List (Nat × Nat)),
      SendShapes ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩ := by
  obtain ⟨x, _, _, hx, _⟩ := VerifiableInference.Desc.K1.real_members
  refine ⟨x, hx, fun item bp => sendShapes_of _ ?_⟩
  have h : (realSized.all fun p => carriersFit codesFull2 p.1.shape) = true := by decide +kernel
  rw [hx] at h
  exact h

-- tests: the test accepts the small shape; two negative tests: it rejects that shape turned in one
-- number
#guard carriersFit Desc.K14.Honest.Toy.P.codes Desc.K14.Honest.Toy.P.S
#guard !carriersFit Desc.K14.Honest.Toy.P.codes { Desc.K14.Honest.Toy.P.S with
  fold := { Desc.K14.Honest.Toy.P.S.fold with
    u := { Desc.K14.Honest.Toy.P.S.fold.u with mainDeg := 1 } } }
#guard !carriersFit Desc.K14.Honest.Toy.P.codes { Desc.K14.Honest.Toy.P.S with
  omega := { Desc.K14.Honest.Toy.P.S.omega with maskRows := 1 } }

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.vecShape_of
#print axioms ProofFile.Honest.K14.sendShapes_of
#print axioms ProofFile.Honest.K14.sendShapes_toy
#print axioms ProofFile.Honest.K14.sendShapes_key
#print axioms ProofFile.Honest.K14.sendShapes_real
