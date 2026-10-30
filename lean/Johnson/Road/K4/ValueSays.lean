-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/ValueSays.lean: WHAT IS CLAIMED BEFORE THE FIRST ROUND OF THE CHAIN OF A LAYERS'
SUB-PROOF's OWN ROUNDS, AT THE VALUE OF Johnson/Road/K4/Value.lean, WRITTEN OUT IN THE VALUE's OWN
LETTERS. Four definitions and two theorems: `kEnd_eq` by lemmas on finite sums alone, `pT_iff` by it
and by `own_pT` and `jn_iff`.

  `Plan4.cells m`, `Plan4.weights m`: the cells and the group's weights that the value reads off a
    tuple of messages.
  `Plan4.kEnd_eq`: what the lookup's end leaves is its public part less the sum, over the slots of
    the own mask row, of its coefficient times the mask entry. No other entry occurs in it.
  `Plan4.Idn m`: all 17 identities of every norm at every position hold of the cells.
  `Plan4.Keys x m`: the sum over the lookup's calls of weight times KF (the library's
    Inst/Model/FF/Objects.lean) at the lookup's point is what the lookup's end leaves.
  `Plan4.pT_iff`: under the three conditions of `jn_iff` (Cb/Pv/Lay/At/Fore.lean; the
    third is the value's own field hf): what is claimed before the first round is
    `Idn m ∧ Keys x m`.

Limits. That KF is the extension of a call's key vector is not shown here (Fore.lean's limit). That
the letters zOf, kTg, kIncS are what a program's lookup left is not said. The identity that the
selector's entries sum to 1 is no part of `Idn`.
-/
import Johnson.Road.K4.Value

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Finset
open Inst.Model (Scl)
open Inst.Model.FFSeg (Cell LW layerR dJ wc KF)

noncomputable section

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type}

namespace Plan4
variable (Q : Plan4 E M X)

/-- The cells that the value reads off a tuple of messages. -/
def cells (m : M) : Cell → E := Q.rd (Q.msg m)

/-- The group's weights that the value reads off a tuple of messages. -/
def weights (m : M) : ℕ → LW E := fun l => layerR Q.D.P Q.kW (Q.Wn (Q.msg m)) (Q.L0 + l)

/-- What the lookup's end leaves reads the own mask row alone. -/
theorem kEnd_eq (x : X) (m : M) :
    Q.full.kEnd x m = Q.kTg x - ∑ s : Fin (Q.ns + 1), Q.kIncS x s * Q.maskAt m s := by
  show Q.kTg x - ∑ j : Q.J, Q.kInc x j * Q.msg m j = _
  congr 1
  simp only [Fintype.sum_sum_type, kInc, msg, zero_mul, sum_const_zero, zero_add, add_zero]

/-- All 17 identities of every norm at every position. -/
def Idn (m : M) : Prop :=
  ∀ k : ℕ × Fin Q.D.nNu, ∀ Y < 2 ^ Q.D.lT, dJ Q.D (Q.cells m) k.1 k.2 Y = 0

/-- The lookup's join in the library's key vectors. -/
def Keys (x : X) (m : M) : Prop :=
  ∑ c, wc Q.D (Q.zOf x) c * KF Q.D (Q.cells m) Q.tb Q.L0 (Q.weights m) (Q.zOf x) c =
    Q.kTg x - ∑ s : Fin (Q.ns + 1), Q.kIncS x s * Q.maskAt m s

/-- **What is claimed before the chain's first round, in the value's own letters.** -/
theorem pT_iff (C : Q.D.ChOK)
    (hk : ∀ l, l < Q.D.nl →
      (Q.D.Pl l).kq = (Q.D.Pl l).kk ∨ (16 ≤ (Q.D.Pl l).kq ∧ 16 ≤ (Q.D.Pl l).kk))
    (x : X) (m : M) : Q.full.own.pT x m ↔ Q.Idn m ∧ Q.Keys x m := by
  rw [Q.full.own_pT x m, Q.full.jn_iff C hk Q.hf x m, Q.kEnd_eq x m]
  exact Iff.rfl

end Plan4
end
end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4.kEnd_eq
#print axioms OnBytes.Road.K4.Plan4.pT_iff
