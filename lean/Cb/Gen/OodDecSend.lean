-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/OodDecSend.lean: an upper bound on the number of verifier seeds that are bad for one
out-of-domain sample on several words that are sent together: the sample row with a pad on the
entries of a code complex.

Definitions and statements (Cb.Spec.ood_*); proofs in Cb/Gen/OodDecSendProofs.lean.
A code complex (`Cx`, Cb/Gen/Code.lean) is a finite family of named components, each a table of
interleaved rows under one code. A reading (`Reading`, Cb/Gen/CodeRep.lean) is even if each position
of the component a is read exactly mult a > 0 times. At a collision (`Cx.CollU`,
Cb/Gen/OodDecRep.lean) two different messages, each with an encoding within the radius (`Cx.NearU`),
have the same answer at the seed; a seed is bad if some answer has a collision. `Cx.decMinU` is in
the same file; `InJohnson` and `listMax` are in Cb/Gen/JohnsonList.lean.
The row with a pad (Cb/Gen/OodDecPad.lean) speaks of vectors on J₀ ⊕ P (entries proper, pad
entries); a code complex has its own set of entries (`Cx.Ent`). A renaming σ : Cx.Ent ≃ J₀ ⊕ P says
which entries of the message are the pad.

Main names:
  `Sample.comap Z σ`: the definition takes any map σ; the statements take a bijection.
  `ood_cx_padInF`: if the pad entries are in components with entries in F, the difference of two
    messages has its pad part in F.
  `ood_send`: the count after a sending. The words of a complex are fixed; they are read under an
    even reading T with joint distance D (D ≤ mult a · d a); the radius e is below the Johnson
    radius for (number of long positions, D); L = `listMax`. The verifier draws (z, β). Then: 2 ·
    (number of seeds at which some answer has a collision) · |B| ≤ L² · (m + 1) · (number of seeds),
    m = |μ|. As a probability: at most (L² / 2) (m + 1) / |B|. Hypotheses: place (msg + r ≤ k), the
    distance of the generators, pl and b injective, c ↦ ∑ w_i c_i injective on F^P, the pad entries
    in components over F, B non-empty. No hypothesis on lists; nothing from the literature.
  `ood_send_good`: at every other seed, for every answer: the decoder by a constrained minimum
    returns m if and only if some encoding of m is within the radius and m has the answer; whatever
    the fixed order.

Limits: for L² (m + 1) ≥ 2 |B| the count says nothing. No protocol: who sends what in which round,
and what a statement means at a bad seed, is not here. This file says nothing on privacy of the row:
Cb/Gen/OodDecPad.lean.
Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.OodDecRep

set_option autoImplicit false

namespace Cb.Ood

/-- A sample map under a renaming of the entries. -/
@[reducible] def Sample.comap {E J J' : Type} (Z : Sample E J) (σ : J' → J) : Sample E J' :=
  { D := Z.D, S := Z.S, mat := fun ρ s j' => Z.mat ρ s (σ j'), err := Z.err }

end Cb.Ood

namespace Cb.Spec
open Prob Blocks Cb.Ood

def ood_val_comap : Prop :=
  ∀ (E J J' : Type) [Field E] [Fintype J] [Fintype J'] (Z : Sample E J)
      (σ : J' ≃ J) (ρ : Z.D) (u : J' → E),
    (Z.comap σ).val ρ u = Z.val ρ fun j => u (σ.symm j)

def ood_okOn_comap : Prop :=
  ∀ (E J J' : Type) [Field E] [Fintype J] [Fintype J'] (Z : Sample E J)
      (σ : J' ≃ J) (V : (J → E) → Prop),
    Z.OKOn V → (Z.comap σ).OKOn fun u => V fun j => u (σ.symm j)

section
variable (F : Type) [Field F] [Fintype F] (E : Type) [Field E] [Fintype E] [Algebra F E]

def ood_cx_padInF : Prop :=
  ∀ (K : Cx F) (J₀ P : Type) (σ : K.Ent ≃ J₀ ⊕ P),
    (∀ i : P, (K.comp (σ.symm (Sum.inr i)).1).overF = true) →
    ∀ m m' : K.Msg E, PadInF F fun n => (K.ents m - K.ents m') (σ.symm n)

/-- The count after a sending. -/
def ood_send : Prop :=
  ∀ (K : Cx F) (T : Reading K.cods) (D e : ℕ) (μ J₀ P B : Type) [Fintype μ] [DecidableEq μ]
      [Fintype J₀] [Fintype P] [Fintype B] [Nonempty B] (pl : J₀ → μ → Bool) (w : P → E) (b : B → E)
      (σ : K.Ent ≃ J₀ ⊕ P) (y : (K.ext E).Str),
    (∀ a, (K.comp a).code.msg + (K.comp a).code.r ≤ (K.comp a).code.k) → T.Even →
    (∀ a, HasDist (K.comp a).code.G (K.comp a).code.d) → (∀ a, D ≤ T.mult a * (K.comp a).code.d) →
    InJohnson (Fintype.card T.P) D e → Function.Injective pl → Function.Injective b →
    Function.Injective (padVal (F := F) w) →
    (∀ i : P, (K.comp (σ.symm (Sum.inr i)).1).overF = true) →
    2 * cnt (fun ρ : (μ → E) × B =>
          ∃ v, K.CollU E T e ((Sample.pad E μ J₀ P B pl w b).comap σ) y ρ v) * Fintype.card B ≤
      listMax (Fintype.card T.P) D e ^ 2 * ((Fintype.card μ + 1) * Fintype.card ((μ → E) × B))

/-- At every other seed (no answer has a collision there), for every answer. -/
def ood_send_good : Prop :=
  ∀ (K : Cx F) (T : Reading K.cods) (rank : K.Msg E × K.Rnd E → ℕ) (e : ℕ) (Z : Sample E K.Ent)
      (y : (K.ext E).Str) (ρ : Z.D),
    (¬ ∃ v, K.CollU E T e Z y ρ v) →
    ∀ (v : Z.S → E) (m : K.Msg E),
      K.decMinU E T rank e Z y ρ v = some m ↔ K.NearU E T e y m ∧ K.ans Z ρ m = v

end
end Cb.Spec
