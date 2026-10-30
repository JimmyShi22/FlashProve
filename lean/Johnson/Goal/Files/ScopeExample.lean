-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Files/ScopeExample.lean: THE TEST OF SCOPE (`InScope`, Ladder.lean) AT THE RELEASE's
OWN PUBLIC FILES, WITH A BENT TWIN: an example for every statement that begins "for all public
files in scope". Statements and proofs; nothing is evaluated here: the kernel checks each.

  `inScope_full`, `inScope_gap`: the stored full-size example's three public files, and the same
    with the other named policy, are in scope: `VerifierAndGoals.filesRead`'s two first halves
    (Johnson/Goal/Files/FilesReadProof.lean: five `decide +kernel` over the stored bytes), by name.
  `push_ne`: an array of bytes with one byte more is another array.
  `outOfScope_of_lay`: files whose layout file is not the stored one are out of scope.
  **`inScope_bent`**: THE BENT TWIN: the stored full-size files with ONE BYTE MORE at the layout
    file's end are out of scope: the test can say no.

OBJECT: `InScope`. USER: files of Johnson/AtFull/, so Johnson/AtFull/Shape/AtX.lean, at their
premise "InScope Z = true", by `inScope_full`. LETTERS: none.

Limits. An example shows that a premise can be met: no soundness follows from it. THE SECOND NAMED
SET (`zGap`) IS IN SCOPE: it is no bent twin. The twin is bent at the layout file alone: that the
test says no to a bent parameter file or scale file is not shown here.
-/
import Johnson.Goal.Files.FilesReadProof

set_option autoImplicit false

namespace VerifierAndGoals

/-- The stored full-size example's public files are in scope. -/
theorem inScope_full : InScope storedPublicFiles = true := filesRead.full.1

/-- So are the same files with the other named policy. -/
theorem inScope_gap : InScope zGap = true := filesRead.other.1

/-- An array of bytes with one byte more is another array. -/
theorem push_ne (b : ByteArray) (x : UInt8) : b.push x ≠ b := by
  intro h
  have h1 : (b.push x).size = b.size := congrArg ByteArray.size h
  rw [ByteArray.size_push] at h1
  omega

/-- Files whose layout file is not the stored one are out of scope. -/
theorem outOfScope_of_lay {Z : PublicFiles} (h : Z.lay ≠ storedPublicFiles.lay) : InScope Z = false := by
  unfold InScope
  rw [decide_eq_false h, Bool.false_and]

/- The named files stay folded from here on: left to unfold them, Lean compares whole files byte by
byte and runs out of stack (Johnson/Goal/Files/FilesReadProof.lean's own note). -/
attribute [local irreducible] storedPublicFiles

/-- **The bent twin**: one byte more at the layout file's end. -/
theorem inScope_bent : InScope ⟨storedPublicFiles.pol, storedPublicFiles.lay.push 0, storedPublicFiles.KL⟩ = false :=
  outOfScope_of_lay (Z := ⟨storedPublicFiles.pol, storedPublicFiles.lay.push 0, storedPublicFiles.KL⟩) (push_ne storedPublicFiles.lay 0)

end VerifierAndGoals

#print axioms VerifierAndGoals.inScope_full
#print axioms VerifierAndGoals.inScope_gap
#print axioms VerifierAndGoals.push_ne
#print axioms VerifierAndGoals.outOfScope_of_lay
#print axioms VerifierAndGoals.inScope_bent
