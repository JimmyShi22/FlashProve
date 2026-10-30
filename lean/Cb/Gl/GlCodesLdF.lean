-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/Gl/GlCodesLdF.lean: list sizes and mutual correlated agreement of
several interleaved Reed-Solomon codes over p = 2^64 - 2^32 + 1 (words over its cubic extension E),
queried at common positions, below the Johnson radius, under the hypotheses of its statement, one of
them the named proposition BCHKS46F F.

Exactly: families of plain Reed-Solomon codes over p under an even reading, below the Johnson radius
of the group: from the narrower hypothesis BCHKS46F F (Cb/Gen/CodeListRSF.lean: the statement
on codes for the finite extensions of F and points in F only).

One statement (`Cb.Gl.Spec.gl_group_proxF`) and its proof. The statement of Cb/Gl/GlCodesLd.lean's
`gl_group_prox`, word for word, with BCHKS46F F in the place of BCHKS46. The hypothesis is not
proved here and is no axiom.

Terms: lean/GLOSSARY.md.
-/
import Cb.Gl.GlCodesLd
import Cb.Gen.CodeListRSF

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks

def Spec.gl_group_proxF : Prop :=
  Cb.BCHKS46F F →
  ∀ (A : Type) [Fintype A] (a k msg r : A → ℕ), (∀ i, a i ≤ 32) →
    (∀ i, 0 < k i) → (∀ i, k i < 2 ^ a i) →
    ∀ T : Reading (grp a k msg r), T.Even →
      ∀ D : ℕ, (∀ i, D ≤ T.mult i * (2 ^ a i - k i)) →
        ∀ (R : A → Type) [∀ i, Finite (R i)], T.Prox E R
          (fun e => InJohnson (Fintype.card T.P) D e ∧ ∀ i, T.mult i ≤ e)
          (fun e => listMax (Fintype.card T.P) D e)
          (fun e => ∑ i, ⌊Cb.bchksBound (2 ^ a i) (k i) (e / T.mult i)⌋₊)

theorem gl_group_proxF : Spec.gl_group_proxF := fun H A _ a k msg r ha hk0 hk T hT D hD R _ =>
  rs_group_proxF F H E A (fun i => 2 ^ a i) k msg r (fun i => pts (a i))
    (fun i => gl_pts_inj (a i) (ha i)) hk0 hk T hT D hD R

end Cb.Gl
