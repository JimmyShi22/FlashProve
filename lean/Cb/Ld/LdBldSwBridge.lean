-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldSwBridge.lean: coefficients by which a seed combines many rows into one (a zero-evader:
`Evader E R`, Cb/Gen/BatEvader.lean), for any finite type of rows; if there are at most 2^gb rows,
every vector other than 0 is annihilated by at most err seeds (`Evader.OK`).

It is the equality zero-evader, each row at a corner of a cube, meant for the bridges of the whole
tests (their rows: the rows of a claim and all sample rows of a group's members).

Definitions, statements and proofs. Generic: any finite field, any rows. Nothing assumed beyond the
hypotheses of the statements and whatever the arguments hold as proofs.
By reading, a write-up of ours (lean/CREDITS.md) takes for a bridge, as for the batching
inside a code switch, the equality zero-evader: a seed is a point of E^gb, the row with the number x
has the equality weight of the point at the corner of x (first coordinate = least significant bit);
at its reference parameters on at most 2^12 rows.

Main names:
  `brZN E gb no`: rows R numbered by no : R ≃ Fin n: `swZb` (Cb/Ld/LdBldSw.lean; equality weights:
    that head) at the corners of the rows' numbers. No choice.
  `brZ E R gb`: the same at an enumeration of R (by choice: `Fintype.equivFin`): for rows whose
    order nobody has fixed.
  `Spec.bldSwB_no` (of `brZN`), `Spec.bldSwB_ch` (of `brZ`): if n ≤ 2^gb (|R| ≤ 2^gb), the evader is
    of one of the forms of zero-evaders that have a theorem in this library (`Evader.Form`,
    Cb/Req1/LdReqJohnEvForm.lean), and so it is a zero-evader (`Evader.OK`); without that
    hypothesis: the number `err` is gb q^(gb-1), of q^gb seeds, q = |E|; for 1 ≤ gb the fraction is
    gb / q.
  `Spec.bldSwB_row`: for |G.Row B| ≤ 2^gb, the case of a group's rows `G.Row B`
    (Cb/Ld/LdBatSig.lean), without the fraction.

Limits: declared: `brZ` fixes no order of the rows. This file does not say that gb / q times a list
is small. It does not say which rows a bridge has.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdBldSwOrdProofs
import Cb.Ld.LdBatSig
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Prob Blocks Alg Cb.Ood Cb.Bld

namespace Bld

/-- The equality zero-evader on numbered rows. -/
@[reducible] def brZN (E : Type) [Field E] [Fintype E] {R : Type} {n : ℕ}
    (gb : ℕ) (no : R ≃ Fin n) : Evader E R :=
  swZb E gb fun x => bitsL gb (no x).val

/-- The same at an enumeration. -/
@[reducible] def brZ (E R : Type) [Field E] [Fintype E] [Fintype R] (gb : ℕ) :
    Evader E R :=
  brZN E gb (Fintype.equivFin R)

end Bld

namespace Spec

def bldSwB_no : Prop :=
  ∀ (E R : Type) [Field E] [Fintype E] [Fintype R] (n gb : ℕ) (no : R ≃ Fin n),
    (n ≤ 2 ^ gb → (brZN E gb no).Form ∧ (brZN E gb no).OK) ∧
    (brZN E gb no).err = gb * Fintype.card E ^ (gb - 1) ∧
    Fintype.card (brZN E gb no).D = Fintype.card E ^ gb ∧
    (1 ≤ gb → (brZN E gb no).err * Fintype.card E = gb * Fintype.card (brZN E gb no).D)

def bldSwB_ch : Prop :=
  ∀ (E R : Type) [Field E] [Fintype E] [Fintype R] (gb : ℕ),
    (Fintype.card R ≤ 2 ^ gb → (brZ E R gb).Form ∧ (brZ E R gb).OK) ∧
    (brZ E R gb).err = gb * Fintype.card E ^ (gb - 1) ∧
    Fintype.card (brZ E R gb).D = Fintype.card E ^ gb ∧
    (1 ≤ gb → (brZ E R gb).err * Fintype.card E = gb * Fintype.card (brZ E R gb).D)

/-- On the rows that a test on a group takes in. -/
def bldSwB_row : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (G : Grp S) (B : Type) [Fintype B] (gb : ℕ),
    Fintype.card (G.Row B) ≤ 2 ^ gb →
    (brZ E (G.Row B) gb).Form ∧
    (brZ E (G.Row B) gb).OK ∧
    (brZ E (G.Row B) gb).err = gb * Fintype.card E ^ (gb - 1) ∧
    Fintype.card (brZ E (G.Row B) gb).D = Fintype.card E ^ gb

end Spec

theorem bldSwB_no : Spec.bldSwB_no := by
  intro E R _ _ _ n gb no
  have hN := bldSw_nums E Unit Unit _ R (Equiv.refl (Unit ⊕ (Unit ⊕ Unit))) 0 (fun _ i => i.elim0)
    gb (fun x => bitsL gb (no x).val)
  have hF := bldSw_frac E Unit Unit _ R (Equiv.refl (Unit ⊕ (Unit ⊕ Unit))) 0 (fun _ i => i.elim0)
    gb (fun x => bitsL gb (no x).val)
  refine ⟨fun h => ?_, hN.2.2.1, hN.2.2.2, hF.2⟩
  have hi : Function.Injective fun x => bitsL gb (no x).val := fun x y e =>
    no.injective (Fin.ext (bitsL_inj (lt_of_lt_of_le (no x).2 h) (lt_of_lt_of_le (no y).2 h) e))
  have hf := bldSw_zb E R gb _ hi
  exact ⟨hf, evForm_ok E _ _ hf⟩

theorem bldSwB_ch : Spec.bldSwB_ch := fun E R _ _ _ gb =>
  bldSwB_no E R (Fintype.card R) gb (Fintype.equivFin R)

theorem bldSwB_row : Spec.bldSwB_row := fun E _ _ _ G B _ gb h =>
  have g := bldSwB_ch E (G.Row B) gb
  ⟨(g.1 h).1, (g.1 h).2, g.2.1, g.2.2.1⟩

end Cb
