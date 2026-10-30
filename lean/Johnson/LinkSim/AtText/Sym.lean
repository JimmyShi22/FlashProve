-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/Sym.lean: the prover's code-word symbol is the symbol of
Johnson/LinkSim/Tail.lean, so a change of a row's message is compensated by a change of its tail.
General lemmas.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. symG (Johnson/Prover/Link/Base.lean) is the symbol that the prover's
algorithm computes for a row at a position: the row's polynomial, tail first and then message,
evaluated at the position's point.
  symG_eq        symG C x m r = sym C.r C.l (ptG C.a x) m r: it is the symbol sym of
                 Johnson/LinkSim/Tail.lean at the point of x.
  symG_shift     let Q be a list of at most C.r positions (C.r is the tail's length), read through
                 any map red (the identity, or "modulo the mask code's length"). At each x in Q,
                 symG C (red x) (m + dm) t = symG C (red x) m (t + t'), where the compensating
                 tail t' is tailShift at the points of Q (Johnson/LinkSim/Tail.lean).
  symG_add, formG_add   symG, and the linear form formG that the claim applies to a message, are
                 additive.
  wr_congr       the written list of a function's first n values depends on these values alone.

How it fits. ShiftDefs.lean's tailAt is this compensating tail. symG_shift is used once: Step.lean
proves symG_tailAt from it, and Step.lean and FrontStep.lean then use symG_tailAt to prove that the
two runs' trees have equal columns at the opened positions. ptG is used in ShiftDefs.lean,
MustFail.lean, ShortTail.lean and ShortTailPts.lean; symG_eq in MustFail.lean and ShortTail.lean;
wr_congr in Cols.lean. Under Johnson/LinkSim/ no file uses symG_add or formG_add.

The other names.
  ptG a x        the point of position x of a code with 2^a positions, in the extension field GE.

Limits.
  - The compensating tail is a function of the list of positions and of dm.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.Base
import Johnson.LinkSim.Tail

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Slice Cb
open Johnson.Prover.Link
open Fmt.M1 (Code point)

/-- The point of a position, in the extension field GE. -/
def ptG (a x : ℕ) : GE := algebraMap GF GE (toF (point a x))

theorem symG_eq (C : Code) (x : ℕ) (m r : ℕ → GE) :
    symG C x m r = sym C.r C.l (ptG C.a x) m r := by
  unfold symG sym msgPart ptG
  simp only [map_pow]

open Classical in
/-- At each of at most C.r positions, the message m + dm with the tail t has the symbol of the
message m with the tail t plus the compensating tail (tailShift). -/
theorem symG_shift (C : Code) (Q : List ℕ) (red : ℕ → ℕ) (hQ : Q.length ≤ C.r) (m dm t : ℕ → GE)
    {x : ℕ} (hx : x ∈ Q) :
    symG C (red x) (m + dm) t =
      symG C (red x) m (t + tailShift C.r C.l (Q.map fun y => ptG C.a (red y)).toFinset dm) := by
  rw [symG_eq, symG_eq]
  exact sym_shift_list C.r C.l Q (fun y => ptG C.a (red y)) hQ m dm t hx

theorem symG_add (C : Code) (x : ℕ) (m m' r r' : ℕ → GE) :
    symG C x (m + m') (r + r') = symG C x m r + symG C x m' r' := by
  have h := symG_line C x m m' r r' 1
  simp only [one_mul] at h
  exact h

theorem formG_add (n : ℕ) (c : Array Fmt.M1.E) (m m' : ℕ → GE) :
    formG n c (m + m') = formG n c m + formG n c m' := by
  have h := formG_line n c m m' 1
  simp only [one_mul] at h
  exact h

theorem wr_congr (n : ℕ) (f g : ℕ → GE) (h : ∀ j, j < n → f j = g j) : wr n f = wr n g :=
  List.map_congr_left fun j hj => by rw [h j (List.mem_range.mp hj)]

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.symG_eq
#print axioms OnBytes.LinkSim.AtText.symG_shift
#print axioms OnBytes.LinkSim.AtText.symG_add
