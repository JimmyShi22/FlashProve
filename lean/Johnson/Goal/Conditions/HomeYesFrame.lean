-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/HomeYesFrame.lean: the written set of true instances (yesAt,
Johnson/Goal/Conditions/HomeServed.lean) lies in the relation of the top theorems' interface at the
full size (Meaning.frameRel, Johnson/Goal/Meaning/Frame.lean), at the table of scales and policy
that the reader returns at the public files: where a request is true under the files' policy at the
index of some weights, the matrix written of these weights is in range, and it holds an index at
which some trace meets the relaxed relation with the cost ledger. IT STATES NO GOAL. A statement and
its proof.

Main names (namespace FlashProve).
  holds_backB   the matrix written of given weights holds their index.
  frameRel_of_yesAt   THE STATEMENT. No premise beside yesAt and that the reader returns a table.

Why. What is shown of the honest provers at a larger set of true instances serves at every smaller
one (HonFit.mono, Johnson/Prover/All/OfHonest.lean). A theorem that speaks at the interface's own
relation can so be carried to yesAt.

How. Calls alone: the written matrix is Flat.matrixOf of the weights' index (backO,
Johnson/PV/DescribeBinds.lean), which holds it (Flat.holds_matrixOf, Johnson/Flat/ThreeFull.lean);
frameRel_iff_says (Johnson/Goal/Meaning/Frame.lean) with tieSays (Johnson/Goal/Meaning/TieR.lean);
the table by ppAtFiles_of_read (Johnson/Flat/PolicyAtFrame.lean); lawful_of_read and polCond_of_read
(Johnson/Meaning/Scope.lean).

Limits. On a relation, not on a protocol. Johnson/Goal/Meaning/Frame.lean shows frameRel to be the
configuration's field Rno; nothing is said here of its field Ryes. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.HomeServed
import Johnson.Goal.Meaning.Frame
import Johnson.Meaning.Scope
import Johnson.Flat.PolicyAtFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace FlashProve
open VerifierAndGoals VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat

variable (b : PublicFiles → ℕ) (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy}

/-- The matrix written of given weights holds their index. -/
theorem holds_backB (hr : readFiles Z = .ok pp) (w : ModelWeights (settingsOfRead pp)) :
    Flat.Holds (backB b Z (settingsOfRead pp) w) (indexOfWeights (valid_of_read hr) w) := by
  unfold backB backThe
  rw [dif_pos (valid_of_read hr)]
  exact Flat.holds_matrixOf _

/-- **The written set of true instances lies in the interface's relation**, at the table that the
reader returns at the public files. -/
theorem frameRel_of_yesAt (hr : readFiles Z = .ok pp) (i : (homeR b Z).Index) (x : (homeR b Z).Instance)
    (h : yesAt b Z hr i x) :
    Meaning.frameRel (ppAtFiles (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL) i (valB b Z x) := by
  obtain ⟨w, rfl, ht⟩ := h
  rw [show ppAtFiles (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL = pp from ppAtFiles_of_read hr]
  exact (Meaning.frameRel_iff_says (OnBytes.Road.L5.lawful_of_read hr)
    (OnBytes.Road.L5.polCond_of_read hr) _ _).2
    ⟨_, holds_backB b Z hr w, (Meaning.tieSays pp _ _).2 ht⟩

end FlashProve
