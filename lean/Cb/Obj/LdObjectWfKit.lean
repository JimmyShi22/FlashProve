-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectWfKit.lean: assembly of the holographic IOP from its sub-protocols: one "what is
left" under a preamble and the test that follows it: the claim replaced by an equivalent one; a
tensor row written in two ways.

Statements and proofs.
`ConfigurationWithOutOfDomainSample.Left` (Hiop/RecConf.lean) is what a preamble hands to the test after it: oracles under an
encoding, explicit claims, and the predicate `holds` that says when a claim is true of the record,
the message of the encoded index and the message of these oracles. The four items
(Hiop/RecSubs.lean): `PreKnowR`, `LinKnowR` are round-by-round knowledge soundness of a preamble and
of the test; `PreListR`, `LinListR` are their parameter lists, all items but knowledge soundness.

Why: `SubsR` (Hiop/RecSubs.lean) has one datum "what the preamble leaves" (`ConfigurationWithOutOfDomainSample.Left`) for a
preamble and for the test for linear constraints that follows it. The preamble (`LdWfP.left`,
Cb/Ld/LdWf.lean) and the test (`LdOL.left`, Cb/Obj/LdObjectLin.lean) build theirs by
`sigLeft C S Cl holds` (Cb/Ld/LdWfClose.lean), each with its own predicate "holds": the preamble's
says what its last block leaves, the test's what its first block takes.
`sigLeft`'s types (oracles, explicit part, messages, randomness) do not read "holds". So a term that
is typed over the one is typed over the other, by definition, and only the four items have to be
moved.

Main names:
  `Spec.ldOWk_left`: predicates that are equivalent give the same datum.
  `Spec.ldOWk_pre`, `Spec.ldOWk_lin`: the two items of a preamble (`PreListR`, `PreKnowR`), the two
    items of the test (`LinListR`, `LinKnowR`), are kept when "holds" is replaced by an equivalent
    predicate. No cast occurs.
  `Spec.ldOWk_ten`: the multilinear extension, at a point z, of the vector aᵀM on the columns of a
    matrix M is the double sum over rows and columns of a_y · eq(z', c) · M'(y, c), where the column
    variables (a finite type ι) are split in two groups by a bijection e, z' is z read along e, and
    M' is M with its columns named along e.

Limits: No protocol's claims are compared here (Cb/Obj/LdObjectWf.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfClose

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

namespace Spec
section
variable (E : Type) [Field E]

def ldOWk_left : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (Cl : Type) (h h' : Cl → C.Rec → C.Msg → S.Msg → Prop),
    (∀ cl rec U m, h cl rec U m ↔ h' cl rec U m) → sigLeft C S Cl h = sigLeft C S Cl h'

/-- The two items of a preamble. -/
def ldOWk_pre : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (Cl : Type) (h h' : Cl → C.Rec → C.Msg → S.Msg → Prop) (Xi Wi Wr : Type)
      (F : IOR Xi C.E0 ((sigLeft C S Cl h).Xl × C.Rec) (sigLeft C S Cl h).El)
      (H : F.Honest Wi (C.PIdx × (sigLeft C S Cl h).WAux)) (rc : Xi → C.Rec) (px : Wi → C.PIdx)
      (Ri : Xi → C.E0.Str → Wi → Prop) (P : PreNums F) (on : Xi × C.E0.Str → Prop)
      (RiR : Xi × C.E0.Str → Wr → Prop)
      (ext : Xi × C.E0.Str → Tr F.shape → (sigLeft C S Cl h).AMsg → Wr) (ε : Err F.shape),
    (∀ cl rec U m, h cl rec U m ↔ h' cl rec U m) →
    (PreListR (sigLeft C S Cl h) F H rc px Ri P → PreListR (sigLeft C S Cl h') F H rc px Ri P) ∧
    (PreKnowR (sigLeft C S Cl h) F on RiR ext ε → PreKnowR (sigLeft C S Cl h') F on RiR ext ε)

/-- The two items of the test. -/
def ldOWk_lin : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (Cl : Type) (h h' : Cl → C.Rec → C.Msg → S.Msg → Prop)
      (Q : IOR ((sigLeft C S Cl h).Xl × C.Rec) (sigLeft C S Cl h).El Unit extNone)
      (H : Q.Honest (C.PIdx × (sigLeft C S Cl h).WAux) Unit) (P : LinNumsR Q.shape)
      (d0 : (sigLeft C S Cl h).AMsg) (ε : Err Q.shape),
    (∀ cl rec U m, h cl rec U m ↔ h' cl rec U m) →
    (LinListR (sigLeft C S Cl h) Q H P → LinListR (sigLeft C S Cl h') Q H P) ∧
    (LinKnowR (sigLeft C S Cl h) Q d0 ε → LinKnowR (sigLeft C S Cl h') Q d0 ε)

/-- A tensor row, written in two ways. -/
def ldOWk_ten : Prop :=
  ∀ (Rw ι ι₁ ι₂ : Type) [Fintype Rw] [Fintype ι] [DecidableEq ι] [Fintype ι₁] [Fintype ι₂]
      [DecidableEq ι₁] [DecidableEq ι₂] (e : ι ≃ ι₁ ⊕ ι₂) (a : Rw → E) (M : Rw × (ι → Bool) → E)
      (M' : Rw → (ι₁ ⊕ ι₂ → Bool) → E) (z : ι → E),
    (∀ r c, M (r, fun i => c (e i)) = M' r c) →
    Alg.mle (fun c => ∑ r, a r * M (r, c)) z =
      ∑ y, ∑ c, a y *
        Alg.eqk (Sum.elim (fun i => z (e.symm (Sum.inl i))) fun i => z (e.symm (Sum.inr i))) c *
        M' y c

end
end Spec

section
variable {E : Type} [Field E]

theorem ldOWk_left : Spec.ldOWk_left E := fun C S Cl h h' hh => by
  have e : h = h' :=
    funext fun cl => funext fun rec => funext fun U => funext fun m => propext (hh cl rec U m)
  rw [e]

theorem ldOWk_pre :
    Spec.ldOWk_pre E := fun C S Cl h h' Xi Wi Wr F H rc px Ri P on RiR ext ε hh => by
  have e : h = h' :=
    funext fun cl => funext fun rec => funext fun U => funext fun m => propext (hh cl rec U m)
  subst e
  exact ⟨fun x => x, fun x => x⟩

theorem ldOWk_lin : Spec.ldOWk_lin E := fun C S Cl h h' Q H P d0 ε hh => by
  have e : h = h' :=
    funext fun cl => funext fun rec => funext fun U => funext fun m => propext (hh cl rec U m)
  subst e
  exact ⟨fun x => x, fun x => x⟩

theorem ldOWk_ten : Spec.ldOWk_ten E := by
  intro Rw ι ι₁ ι₂ _ _ _ _ _ _ _ e a M M' z hM
  have hz : (Sum.elim (fun i => z (e.symm (Sum.inl i))) fun i => z (e.symm (Sum.inr i))) =
      fun i => z (e.symm i) := by
    funext i
    cases i <;> rfl
  rw [hz]
  have h1 : Alg.mle (fun c => ∑ r, a r * M (r, c)) z =
      Alg.mle (fun c : ι₁ ⊕ ι₂ → Bool => ∑ r, a r * M' r c) (fun i => z (e.symm i)) := by
    have h := Alg.mle_equiv e (fun c : ι₁ ⊕ ι₂ → Bool => ∑ r, a r * M' r c) (fun i => z (e.symm i))
    rw [← h]
    congr 1
    · funext c
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← hM]
      simp only [Equiv.symm_apply_apply]
    · funext i
      rw [Equiv.symm_apply_apply]
  rw [h1]
  unfold Alg.mle
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

end
end Cb
