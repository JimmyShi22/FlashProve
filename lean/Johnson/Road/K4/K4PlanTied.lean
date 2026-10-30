-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PlanTied.lean: THE CLOSED FACTS OF Johnson/Road/K4/K4PlanWritten.lean CARRIED TO
THE PUBLIC PARAMETERS Z. Where five parts of Z are the written values (`WrittenAt Z`: what other
files' pins compare whole or lay), the letters of Johnson/Road/K4/K4PlanAt.lean are the written
terms, by Johnson/P5T/'s ties `planSeats_at`, `planSeatsAll_at`, `psFull_is`, `seatsAllFull_is`; so
each closed fact is the test's yes at Z. One Lean structure of five equations and eleven theorems:
one closed fact by the kernel, ten without an evaluation.

  `WrittenAt Z`: Z.made.proof, Z.first.shape, .codes, .layout and the declared rounds' entries are
    the written ones.
  `shape_one`: the two written shapes (`shapeFull`, the pin's
    `proofSizedFull.request`) are one value: by the kernel.
  `seatsAt_written`, `allSeatsAt_written`, `numbersAt_written`, `arrAt_written`, `numAt_written`,
    `lists0At_written`, `lastAt_written`: K4PlanAt.lean's letters at Z are the written terms.
  `seamClosed_at`: `seamClosedB` accepts at Z's letters at every seam 0 < g < 12.
  `programs_at`: the programs' three tests accept at `sentAt Z`.
  `groups_at`: `groupsAreMembers` accepts at Z's letters.

Limits. K04_law IS NOT PROVED BY THIS. `WrittenAt Z` IS A PREMISE: that the verifier's accept, or
the goals' scope, gives its five equations is other files' to show (pins' laws): not called here.
`shapesTiedB` and the twelve tests at the groups are not here.
-/
import Johnson.Road.K4.K4PlanWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.Desc.First (groupsAreMembers)
open Johnson.G (layoutFull proofSendsFull)

/-- **Five parts of the public parameters are the written values.** -/
structure WrittenAt (Z : ProofFile.Pub) : Prop where
  proof : Z.made.proof = proofSendsFull
  shape : Z.first.shape = shapeFull
  codes : Z.first.codes = proofSizedFull.codes
  layout : Z.first.layout = layoutFull
  entries : (Z.D.1.map (·.entry), Z.D.2.1.map (·.entry), Z.D.2.2.map (·.entry)) = P5T.esFull

/-- The two written shapes are one value. -/
theorem shape_one : shapeFull = proofSizedFull.request := by decide +kernel

variable {Z : ProofFile.Pub} (W : WrittenAt Z)
include W

theorem seatsAt_written : seatsAt Z = P5T.psFull := by
  unfold seatsAt
  rw [P5T.planSeats_at, W.proof, W.shape, show Z.D.1.map (·.entry) = P5T.esFull.1 from
    congrArg Prod.fst W.entries]
  exact P5T.psFull_is

theorem allSeatsAt_written : allSeatsAt Z = P5T.seatsAllFull := by
  unfold allSeatsAt
  rw [P5T.planSeatsAll_at, W.proof, W.shape, W.entries]
  exact P5T.seatsAllFull_is

theorem numbersAt_written : numbersAt Z = P5T.N0Full := by
  unfold numbersAt
  rw [seatsAt_written W]
  rfl

theorem arrAt_written : arrAt Z = arrW := by
  unfold arrAt
  rw [allSeatsAt_written W]
  rfl

theorem numAt_written : numAt Z = numW := by
  unfold numAt
  rw [allSeatsAt_written W]
  rfl

theorem lists0At_written : lists0At Z = listsW := by
  unfold lists0At
  rw [seatsAt_written W, W.proof]
  rfl

theorem lastAt_written : lastAt Z = lastW := by
  unfold lastAt lastW
  rw [W.shape, shape_one]

/-- **At Z's letters the test at the seam accepts, at every seam.** -/
theorem seamClosed_at {g : ℕ} (h0 : 0 < g) (hg : g < 12) :
    seamClosedB (sentAt Z).layout (numAt Z) (arrAt Z) (numbersAt Z) g = true := by
  rw [show (sentAt Z).layout = layoutFull from W.layout, numAt_written W, arrAt_written W,
    numbersAt_written W]
  have e := List.all_eq_true.1 seamClosed_written_all (g - 1) (List.mem_range.2 (by omega))
  rwa [show g - 1 + 1 = g by omega] at e

/-- **The programs' three tests accept at `sentAt Z`.** -/
theorem programs_at :
    (sentAt Z).codes.lengthsOk = true ∧ OnBytes.reqShapeOk (sentAt Z).shape = true ∧
      OnBytes.reqLayoutOk (sentAt Z).codes (sentAt Z).shape (sentAt Z).layout = true := by
  rw [show (sentAt Z).codes = proofSizedFull.codes from W.codes,
    show (sentAt Z).shape = proofSizedFull.request from W.shape.trans shape_one,
    show (sentAt Z).layout = layoutFull from W.layout]
  exact ⟨lengths_written, shape_written, layout_written⟩

/-- **Every seat of every group is a member's, at Z's letters.** -/
theorem groups_at : groupsAreMembers (numbersAt Z) (lastAt Z) (lists0At Z) = true := by
  rw [numbersAt_written W, lastAt_written W, lists0At_written W]
  exact groups_written

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.shape_one
#print axioms OnBytes.Road.K4.seatsAt_written
#print axioms OnBytes.Road.K4.allSeatsAt_written
#print axioms OnBytes.Road.K4.numbersAt_written
#print axioms OnBytes.Road.K4.lists0At_written
#print axioms OnBytes.Road.K4.lastAt_written
#print axioms OnBytes.Road.K4.seamClosed_at
#print axioms OnBytes.Road.K4.programs_at
#print axioms OnBytes.Road.K4.groups_at
