-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/ExtIsStrAt.lean: THE EXTERNAL STRING OF A VALUE OF THE STRUCTURE FOR THE
INDEX COMMITTER'S SHARE (`ProofFile.Honest.Committer.ext`, Johnson/Desc/ProofFile/Honest/Committer.lean)
IS `strAt` (Johnson/Bind/ForProver/SevenAt.lean), WHERE THAT VALUE'S ENCODER GIVES `encAt`'S
COLUMNS. Statements and proofs; general in the sizes and in that value.

Why. The frame for an honest prover reads a session's external string off a value of the structure
`Committer`: at a position its number and the value's column there, as words. `strAt` has the same
text over `encAt`. The laws of this folder on `strAt` (that it is the library's table of code words;
that at the input of the library's typed compiler it is that input's encoding) speak of such a
value's string once the two are joined. The sizes are variables here, so that a caller at the full
size's numerals has nothing to unfold.

Main names (namespace `Bind.ForProver`).
   `strAt_apply`: `strAt` at a position, written out. By its definition's text.
   `ext_apply_eq_strAt`: at one position x: if the value's encoder gives `encAt`'s column at x, the
      value's external string at x is `strAt` at x.
   **`ext_eq_strAt`**: so the two strings are one, if that holds at every position.
Limits. THE TWO TEXTS ARE ONE BUT FOR THE ENCODER: these equations unfold two definitions and
rewrite by the premise: they say nothing else. THE PREMISE IS THE CALLER'S: that a value's `enc` is
`encAt` at some shape, plain entries and coins is shown here of no value. The value, its six types
and its private input w are letters; of w the index and the coins alone are read. The number of
positions is the sizes' 2^a; that it is the shape's is not asked here (`encAt` gives nothing from
the shape's 2^a on, and both strings then have no word). One committed table; which of the
protocol's tables it is, the first or a copy, is not said here. No hash function, no query, no
coin's law. This file writes no honest prover. Nothing on completeness, on index privacy, on
soundness or on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.SevenAt
import Johnson.Desc.ProofFile.Honest.Committer

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.ForProver
open OnBytes.Slice (Sz ofF)
open ProofFile.Honest (TableRand Committer)
open Bind.Twin (Shape)

/-- `strAt` at a position, written out. By its definition's text. -/
theorem strAt_apply (S : Sz) (sh : Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand) (x : S.Pos) :
    strAt S sh entry ρ x = (x.val, ((encAt sh entry ρ x.val).getD []).map ofF) :=
  rfl

section
variable {W₀ Rc Sd X Xi Ky : Type} (Cm : Committer W₀ Rc Sd X Xi Ky) (S : Sz) (sh : Shape)
  (entry : ℕ → ℕ → UInt64) (ρ : TableRand) (w : W₀ × Rc × Sd)

/-- At one position: where the value's encoder gives `encAt`'s column, the value's external string
is `strAt`. It unfolds the two definitions and rewrites by the premise. -/
theorem ext_apply_eq_strAt (x : S.Pos)
    (h : Cm.enc w.1 w.2.1 x.val = encAt sh entry ρ x.val) :
    Cm.ext S.P.T.a w x = strAt S sh entry ρ x := by
  show (x.val, ((Cm.enc w.1 w.2.1 x.val).getD []).map ofF) =
    (x.val, ((encAt sh entry ρ x.val).getD []).map ofF)
  rw [h]

/-- **The value's external string is `strAt`**, where the value's encoder gives `encAt`'s column at
every position. The premise is the caller's. -/
theorem ext_eq_strAt (h : ∀ x : S.Pos, Cm.enc w.1 w.2.1 x.val = encAt sh entry ρ x.val) :
    Cm.ext S.P.T.a w = strAt S sh entry ρ :=
  funext fun x => ext_apply_eq_strAt Cm S sh entry ρ w x (h x)

end

end Bind.ForProver

end

#print axioms Bind.ForProver.strAt_apply
#print axioms Bind.ForProver.ext_apply_eq_strAt
#print axioms Bind.ForProver.ext_eq_strAt
