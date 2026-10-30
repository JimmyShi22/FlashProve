-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldWfCount.lean: cardinalities, in closed form, of the finite types of names that
Cb/Ld/LdBldWf.lean and Cb/Ld/LdBldWfTwo.lean use.

Statements and proofs. Generic: any numbers x, any finite field. Nothing assumed beyond the
hypotheses of the statements and whatever the arguments hold as proofs.

Main names:
  `x.own f`: the number of own masks of the lookup on forest f, in closed form (that of
    Cb/Ld/LdLkpMaskPlaces2.lean at v' f, d f, w f, nd f).
  `Spec.bldWfC_emb`: finite types α, β with |α| ≤ |β|: there is an embedding of α into β.
  `Spec.bldWfC_bit`: the digits: |x.Bit| = Σ over the forests f ≤ n of 2^(d f) · 2^(w f).
  `Spec.bldWfC_last`: the inner masks of the last levels: 2 (n + 1).
  `Spec.bldWfC_one`: the first message's masks: |x.Msk1 E| + 2 (n + 1) = Σ over the forests of x.own
    f.
  `Spec.bldWfC_two`: the second message's masks: |x.Msk2 E| = 2 (n + 1) + (1 + 2 k).

Notation: `x`: the numbers (`BldWfN`, Cb/Ld/LdBldWf.lean); `n`: the forests are 0 .. n; `k`: the
number of column variables; `d f`: of table variables of forest f; `w f`: of its variables of digit
positions; `nd f`: nd f + 1 digits count; `v' f`: rv f + k - 1 (on ℕ: 0 if rv f + k = 0), with rv f
key row variables; `x.Bit`: the digits of the multiplicities; `x.Msk1 E`, `x.Msk2 E`, `x.Last E s`:
Cb/Ld/LdBldWfTwo.lean.

Limits: this file says nothing on numerals. It does not say how many data and free entries a message
has.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBldWfTwo
import Cb.Ld.LdLkpMaskPlaces2Proofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Finset Cb.LdLkp Cb.Lkp

/-- the number of own masks of the lookup on forest f -/
def BldWfN.own (x : BldWfN) (f : ℕ) : ℕ :=
  6 * (x.nd f + 1) + 3 + (x.v' f + 1) ^ 2 + 4 * (x.v' f + 1) + x.d f ^ 2 +
    (2 * x.w f + 8) * x.d f + 4 * x.w f

namespace Spec

def bldWfC_emb : Prop :=
  ∀ (α β : Type) [Finite α] [Finite β], Nat.card α ≤ Nat.card β → Nonempty (α ↪ β)

def bldWfC_bit : Prop := ∀ x : BldWfN, Nat.card x.Bit = ∑ f ∈ range (x.n + 1), 2 ^ x.d f * 2 ^ x.w f

def bldWfC_last : Prop :=
  ∀ (x : BldWfN) (E : Type) [Field E] [Fintype E],
    Nat.card {s : Σ f : x.Fo, x.LkM E f.1 // x.Last E s} = 2 * (x.n + 1)

def bldWfC_one : Prop :=
  ∀ (x : BldWfN) (E : Type) [Field E] [Fintype E],
    Nat.card (x.Msk1 E) + 2 * (x.n + 1) = ∑ f ∈ range (x.n + 1), x.own f

def bldWfC_two : Prop :=
  ∀ (x : BldWfN) (E : Type) [Field E] [Fintype E],
    Nat.card (x.Msk2 E) = 2 * (x.n + 1) + (1 + 2 * x.k)

end Spec

theorem bldWfC_emb : Spec.bldWfC_emb := by
  intro α β _ _ h
  haveI := Fintype.ofFinite α
  haveI := Fintype.ofFinite β
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  exact Function.Embedding.nonempty_of_card_le h

section
variable (x : BldWfN)

theorem bldWfC_finFo : Finite x.Fo := letI := x.finFo; inferInstance

theorem bldWfC_finBit : Finite x.Bit := haveI := bldWfC_finFo x; inferInstance

/-- a sum over the forests -/
theorem bldWfC_sumFo (g : ℕ → ℕ) : (letI := x.finFo; ∑ f : x.Fo, g f.1) = ∑ f ∈ range (x.n + 1), g f := by
  letI := x.finFo
  rw [Finset.sum_range]
  exact (Fintype.sum_equiv
    (Fin.equivSubtype.trans (Equiv.subtypeEquivRight fun _ => Nat.lt_succ_iff))
    (fun i : Fin (x.n + 1) => g i) (fun f : x.Fo => g f.1) fun _ => rfl).symm

theorem bldWfC_cardFo : Nat.card x.Fo = x.n + 1 := by
  rw [Nat.card_congr
        (Fin.equivSubtype.trans
          (Equiv.subtypeEquivRight fun _ => Nat.lt_succ_iff) : Fin (x.n + 1) ≃ x.Fo).symm,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem bldWfC_bit : Spec.bldWfC_bit := by
  intro x
  letI := x.finFo
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma, ← bldWfC_sumFo x fun f => 2 ^ x.d f * 2 ^ x.w f]
  exact Finset.sum_congr rfl fun f _ => by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

variable (E : Type) [Field E] [Fintype E]

theorem bldWfC_finSg : Finite (Σ f : x.Fo, x.LkM E f.1) :=
  letI := x.finFo
  letI := fun f : x.Fo => x.finLkM E f.1
  inferInstance

theorem bldWfC_fin1 : Finite (x.Msk1 E) := haveI := bldWfC_finSg x E; inferInstance

theorem bldWfC_fin2 : Finite (x.Msk2 E) := haveI := bldWfC_finSg x E; inferInstance

/-- all own masks of all lookups -/
theorem bldWfC_all : Nat.card (Σ f : x.Fo, x.LkM E f.1) = ∑ f ∈ range (x.n + 1), x.own f := by
  letI := x.finFo
  letI := fun f : x.Fo => x.finLkM E f.1
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma, ← bldWfC_sumFo x x.own]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← Nat.card_eq_fintype_card]
  exact ldLkpPlaces2_card E (lkBare E (x.v' f.1) (x.d f.1) (x.w f.1) (x.nd f.1))

/-- the inner masks of the last levels: a forest and a bit -/
def bldWfC_lastEq : x.Fo × Bool ≃ {s : Σ f : x.Fo, x.LkM E f.1 // x.Last E s} :=
  Equiv.ofBijective (fun fc => ⟨⟨fc.1, .k (x.v' fc.1.1) (le_refl _) (Sum.inr fc.2)⟩, le_refl _, fc.2, rfl⟩) (by
    constructor
    · rintro ⟨f, c⟩ ⟨f', c'⟩ h
      have h1 := congrArg Subtype.val h
      obtain rfl : f = f' := congrArg Sigma.fst h1
      have h2 := eq_of_heq (Sigma.mk.inj h1).2
      injection h2 with _ h3
      exact Prod.ext rfl (Sum.inr.inj h3)
    · rintro ⟨⟨f, a⟩, h, c, hc⟩
      refine ⟨(f, c), Subtype.ext ?_⟩
      have hc' : a = .k (x.v' f.1) h (Sum.inr c) := hc
      show (⟨f, .k (x.v' f.1) (le_refl _) (Sum.inr c)⟩ : Σ f : x.Fo, x.LkM E f.1) = ⟨f, a⟩
      exact congrArg (Sigma.mk f) hc'.symm)

end

theorem bldWfC_last : Spec.bldWfC_last := by
  intro x E _ _
  haveI := bldWfC_finFo x
  rw [← Nat.card_congr (bldWfC_lastEq x E), Nat.card_prod, bldWfC_cardFo, Nat.card_eq_fintype_card,
    Fintype.card_bool, Nat.mul_comm]

theorem bldWfC_one : Spec.bldWfC_one := by
  intro x E _ _
  classical
  haveI := bldWfC_finSg x E
  rw [← bldWfC_all x E, ← bldWfC_last x E, Nat.add_comm, ← Nat.card_sum]
  exact Nat.card_congr (Equiv.sumCompl fun s => x.Last E s)

theorem bldWfC_two : Spec.bldWfC_two := by
  intro x E _ _
  haveI := bldWfC_finSg x E
  rw [Nat.card_sum, bldWfC_last x E, Nat.card_eq_fintype_card, card_pidx0 E]

end Cb
