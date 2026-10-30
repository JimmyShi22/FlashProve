-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/OodDecPadPow.lean: out-of-domain samples, continued. Several sample rows with pads for one
vector: independent seeds, a pad of its own for each answer.

Definitions and statements (Cb.Spec.ood_*); proofs in Cb/Gen/OodDecPadPowProofs.lean. It builds on
Cb/Gen/OodDecPad.lean, which has the row with a pad (`Sample.pad`).

Main names:
  `Sample.padPow`: a seed is a list of s seeds (z_i, β_i) of the row with a pad (β_i in a finite
    non-empty set B), drawn independently. The entries are J₀ ⊕ (Fin s × P): the entries proper, and
    for each answer i a pad block of its own. Row i has the coefficient eq(z_i, pl j) at the entry
    j, b(β_i) w_p at the place p of its block, and 0 at the other blocks.
  `ood_val_padPow`: answer i is the answer of the one row, at the seed (z_i, β_i), on
    `padBlock i v`.
  `ood_okOn_padPow`: if b is never 0, and pl, b and c ↦ ∑ w_p c_p on F^P are injective: a
    zero-evader (`Sample.OKOn`, Cb/Gen/OodDecPad.lean) on the vectors whose pad part lies in F, with
    err = (err of one row)^s. Why the power holds: if the entries proper are not all 0, every row
    reads a vector other than 0, and the rows are independent; if they are all 0, some block is not
    0, and its row is b(β_i) times an element other than 0.
  `ood_private_padPow`: under `PadBasis F w`, at every seed with all b(β_i) ≠ 0 the s answers, over
    uniform pads in F, are uniform and independent (`Sample.Private`); `ood_privateSim_padPow`:
    under `PadBasis F w`, with a simulator, if b is never 0.

Limits: if b may be 0 the power is lost: a vector that is 0 but for one pad block is annihilated
whenever b(β_i) = 0 for that block, whatever s: a fraction 1/|B| of the seeds. So where β is drawn
from all of E, the seeds with some β_i = 0 have to be set apart as bad; the statement here asks that
b is never 0. On pad entries in E with the coefficients of a basis over a smaller field the row is
no zero-evader (Cb/Gen/OodDecPad.lean, under "Why": the property holds on `PadInF F` only). What the
head of Cb/Gen/OodDecPad.lean lists as not said is not said here either, but for how s > 1 rows for
one vector are drawn, which this file says.
Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.OodDecPad
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.Ood
open Prob Blocks Alg

open Classical in
/-- s rows with pads: independent seeds, a pad block for each answer. -/
@[reducible] def Sample.padPow (E μ J₀ P B : Type) [Field E] [Fintype E] [Fintype μ]
    [DecidableEq μ] [Fintype B] [Nonempty B] (pl : J₀ → μ → Bool) (w : P → E) (b : B → E) (s : ℕ) :
    Sample E (J₀ ⊕ Fin s × P) :=
  { D := Fin s → (μ → E) × B, S := Fin s,
    mat := fun ρ i =>
        Sum.elim (fun j => eqk (ρ i).1 (pl j)) fun n => if n.1 = i then b (ρ i).2 * w n.2 else 0,
    err := (Sample.pad E μ J₀ P B pl w b).err ^ s }

/-- The entries proper with the pad block i. -/
def padBlock {E J₀ P : Type} {s : ℕ} (i : Fin s) (v : J₀ ⊕ Fin s × P → E) : J₀ ⊕ P → E :=
  Sum.elim (fun j => v (Sum.inl j)) fun p => v (Sum.inr (i, p))

end Cb.Ood

namespace Cb.Spec
open Prob Blocks Alg Cb.Ood

def ood_val_padPow : Prop :=
  ∀ (E μ J₀ P B : Type) [Field E] [Fintype E] [Fintype μ] [DecidableEq μ] [Fintype B] [Nonempty B]
      [Fintype J₀] [Fintype P] (pl : J₀ → μ → Bool) (w : P → E) (b : B → E) (s : ℕ)
      (ρ : Fin s → (μ → E) × B) (v : J₀ ⊕ Fin s × P → E) (i : Fin s),
    (Sample.padPow E μ J₀ P B pl w b s).val ρ v i =
      (Sample.pad E μ J₀ P B pl w b).val (ρ i) (padBlock i v) ()

/-- The power holds, if b is never 0, under the other hypotheses below: the s rows are a zero-evader
on `PadInF F` with err = (err of one row)^s. -/
def ood_okOn_padPow : Prop :=
  ∀ (F E μ J₀ P B : Type) [Field F] [Field E] [Algebra F E] [Fintype E] [Fintype μ]
      [DecidableEq μ] [Fintype B] [Nonempty B] [Fintype J₀] [Fintype P] (pl : J₀ → μ → Bool)
      (w : P → E) (b : B → E) (s : ℕ),
    Function.Injective pl → Function.Injective b → (∀ β, b β ≠ 0) →
    Function.Injective (padVal (F := F) w) → (Sample.padPow E μ J₀ P B pl w b s).OKOn (PadInF F)

def ood_private_padPow : Prop :=
  ∀ (F E μ J₀ P B : Type) [Field F] [Fintype F] [Field E] [Algebra F E] [Fintype E] [Fintype μ]
      [DecidableEq μ] [Fintype B] [Nonempty B] [Fintype J₀] [Fintype P] (pl : J₀ → μ → Bool)
      (w : P → E) (b : B → E) (s : ℕ),
    PadBasis F w → (Sample.padPow E μ J₀ P B pl w b s).Private F fun ρ => ∀ i, b (ρ i).2 ≠ 0

def ood_privateSim_padPow : Prop :=
  ∀ (F E μ J₀ P B : Type) [Field F] [Fintype F] [Field E] [Algebra F E] [Fintype E] [Fintype μ]
      [DecidableEq μ] [Fintype B] [Nonempty B] [Fintype J₀] [Fintype P] (pl : J₀ → μ → Bool)
      (w : P → E) (b : B → E) (s : ℕ),
    PadBasis F w → (∀ β, b β ≠ 0) → (Sample.padPow E μ J₀ P B pl w b s).PrivateSim F

/-- A message over E: one pad entry for an answer. -/
def ood_padBasis_one : Prop := ∀ (E : Type) [Field E], PadBasis E fun _ : Unit => (1 : E)

end Cb.Spec
