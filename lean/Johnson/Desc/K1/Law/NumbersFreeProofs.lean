-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/NumbersFreeProofs.lean: K01_law, rows N1 and N2 | N3: the proofs of the two statements of
Johnson/Desc/K1/Law/NumbersFree.lean.

  `eachOnce_nodup`, `eq_of_nodup_map`: two helpers on lists. `groupsPart : GroupsPart`: row N1.
  `told_succ`: what one block more tells. `bookFitSucc : BookFitSucc`: rows N2 | N3.

Limits. Plain data: the numbers N stay a letter; that either test says yes at the plan's numbers is
shown by nothing here. K01_law is not proved by this. Nothing on soundness.
-/
import Johnson.Desc.K1.Law.NumbersFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open VerifiableInference.Desc.First (Numbers rowsAtFit bookFit bookFit_at eachOnce treesTold
  msgsTold)

/-! ## Row N1 -/

/-- A yes of `eachOnce`: no member stands twice. -/
theorem eachOnce_nodup : ∀ l : List (Nat × Nat), eachOnce l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    simp only [eachOnce, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.2 ⟨fun hm => ?_, eachOnce_nodup l h.2⟩
    have c : l.contains x = true := List.contains_iff_mem.2 hm
    rw [h.1] at c
    cases c

/-- Where the images of a list's members stand once each, two members with one image are one. -/
theorem eq_of_nodup_map {α β : Type} (f : α → β) :
    ∀ l : List α, (l.map f).Nodup → ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b
  | [], _, _, ha, _, _, _ => absurd ha List.not_mem_nil
  | x :: l, h, a, ha, b, hb, e => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd (List.mem_map.2 ⟨b, hb', e.symm⟩) h.1
    · exact absurd (List.mem_map.2 ⟨a, ha', e⟩) h.1
    · exact eq_of_nodup_map f l h.2 a ha' b hb' e

/-- **Row N1**: under a yes of `rowsAtFit` no two segments up to n have one group. -/
theorem groupsPart : GroupsPart := by
  intro N n m m' h hm hm' e
  unfold rowsAtFit at h
  simp only [Bool.and_eq_true] at h
  refine eq_of_nodup_map (fun m => (N.groupAt m, 0)) _ (eachOnce_nodup _ h.1) m'
    (List.mem_range.2 (Nat.lt_succ_of_le hm')) m (List.mem_range.2 (Nat.lt_succ_of_le hm)) ?_
  show (N.groupAt m', 0) = (N.groupAt m, 0)
  rw [e]

/-! ## Rows N2 | N3 -/

/-- What one block more tells. -/
theorem told_succ (told : List (List Oracle)) (k : Nat) (os : List Oracle)
    (h : told[k]? = some os) :
    treesTold told (k + 1) = treesTold told k + os.length ∧
      msgsTold told (k + 1) = msgsTold told k + (os.map fun o => o.tenants.length).sum := by
  unfold treesTold msgsTold
  rw [List.take_add_one, h]
  simp

/-- **Rows N2 | N3**: under a yes of `bookFit`, past block k the two numbers by place grow by what
the block tells. -/
theorem bookFitSucc : BookFitSucc := by
  intro N ps told k os hf hk ht
  have a := bookFit_at N ps told hf k (Nat.le_of_lt hk)
  have b := bookFit_at N ps told hf (k + 1) hk
  have c := told_succ told k os ht
  exact ⟨by rw [b.1, a.1, c.1], by rw [b.2, a.2, c.2]⟩

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.eachOnce_nodup
#print axioms VerifiableInference.Desc.K1.eq_of_nodup_map
#print axioms VerifiableInference.Desc.K1.groupsPart
#print axioms VerifiableInference.Desc.K1.told_succ
#print axioms VerifiableInference.Desc.K1.bookFitSucc
