-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Sub/Late.lean: claims that read a message which is sent late: a ledger on early and late entries,
pulled back to the early entries along public affine forms; and a block seen at a larger tuple of
messages.

Definitions, statements and their proofs. It stands beside Cb/Sub/Joint.lean.
In a sub-proof most claims read entries of a message that is committed behind the rounds whose end
values they tie. This file serves one way of typing that: the late entries are taken as functions of
what was fixed before the chain's first round. That no other way can be typed is NOT shown here, nor
anywhere in Lean that this file knows of. Here these functions are affine forms
`a i` in the early entries, with public coefficients (`TWhole.Aff`, Cb/G6/Led.lean). The ledger that
the verifier keeps reads early and late entries. Its meaning in the joints in front of the late
message is its pull-back. Where the late entries agree with the forms, the two say the same.

Main names:
  `pullF a f`, `pullL a L`: a form, a ledger on J₁ ⊕ J₂ pulled back to J₁ along `a : J₂ → Aff E J₁`.
  `Agree a m u`: each late entry is the value of its form.
  `pullF_holds`, `pullL_holds`: the pull-back holds of m iff the form (ledger) holds of m with the
    forms' values as late entries. `pullL_length`. `late_holds`: the same at any u that agrees.
  `comapM π A`, `comapM_knowAt`: a joint and a block at the tuples M, seen at tuples M' through
    π : M' → M. At M' := M × U the part U is then held FIXED while the block runs: this is a step of
    book-keeping, not a statement on a message that is sent behind the block.

Limits: nothing on an honest prover. That the late entries agree is another block's claim: none is
given here. The forms' coefficients are data here: that they are fixed before the claims that read
them are batched is the chain's matter.
Terms: lean/GLOSSARY.md.
-/
import Cb.Sub.Joint

set_option autoImplicit false

namespace Cb.Sub
open Iop Prob Hiop TWhole IOR

section Pull
variable {E J₁ J₂ : Type} [Field E] [Fintype J₁] [Fintype J₂]

/-- A form on early and late entries, pulled back to the early ones. -/
def pullF (a : J₂ → Aff E J₁) (f : Form E (J₁ ⊕ J₂)) : Form E J₁ :=
  ⟨fun j => f.co (.inl j) + ∑ i, f.co (.inr i) * (a i).co j,
    f.tg - ∑ i, f.co (.inr i) * (a i).c0⟩

/-- A ledger, pulled back claim by claim. -/
def pullL (a : J₂ → Aff E J₁) (L : Ledger E (J₁ ⊕ J₂)) : Ledger E J₁ := L.map (pullF a)

/-- Each late entry is the value of its form. -/
def Agree (a : J₂ → Aff E J₁) (m : J₁ → E) (u : J₂ → E) : Prop := ∀ i, u i = (a i).val m

theorem pullF_holds (a : J₂ → Aff E J₁) (f : Form E (J₁ ⊕ J₂)) (m : J₁ → E) :
    (pullF a f).Holds m ↔ f.Holds (Sum.elim m fun i => (a i).val m) := by
  have e : (pullF a f).gap m = f.gap (Sum.elim m fun i => (a i).val m) := by
    have h : ∑ j, (∑ i, f.co (.inr i) * (a i).co j) * m j =
        ∑ i, f.co (.inr i) * ∑ j, (a i).co j * m j := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    show ∑ j, (f.co (.inl j) + ∑ i, f.co (.inr i) * (a i).co j) * m j -
        (f.tg - ∑ i, f.co (.inr i) * (a i).c0) =
      ∑ j, f.co j * (Sum.elim m fun i => (a i).val m) j - f.tg
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, add_mul, Finset.sum_add_distrib, Aff.val, mul_add]
    rw [h]
    ring
  unfold Form.Holds
  rw [e]

theorem pullL_holds (a : J₂ → Aff E J₁) (L : Ledger E (J₁ ⊕ J₂)) (m : J₁ → E) :
    Ledger.Holds (pullL a L) m ↔ Ledger.Holds L (Sum.elim m fun i => (a i).val m) := by
  unfold Ledger.Holds pullL
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact forall₂_congr fun f _ => pullF_holds a f m

omit [Field E] [Fintype J₁] in
theorem pullL_length [Field E] (a : J₂ → Aff E J₁) (L : Ledger E (J₁ ⊕ J₂)) :
    (pullL a L).length = L.length := List.length_map _

/-- Where the late entries agree with their forms, the ledger and its pull-back say the same. -/
theorem late_holds (a : J₂ → Aff E J₁) (L : Ledger E (J₁ ⊕ J₂)) (m : J₁ → E) (u : J₂ → E)
    (h : Agree a m u) : Ledger.Holds L (Sum.elim m u) ↔ Ledger.Holds (pullL a L) m := by
  rw [pullL_holds, show u = fun i => (a i).val m from funext h]

end Pull

/-- A joint at the tuples M, seen at tuples M'. -/
def comapM {K X M M' Wp : Type} {Ex : ExtSpec} (π : M' → M) (A : Rels K X Ex (M × Wp)) :
    Rels K X Ex (M' × Wp) :=
  ⟨fun x y w => A.rel x y (π w.1, w.2), fun a w => A.relR a (π w.1, w.2), A.on,
    fun w => A.core (π w.1, w.2)⟩

/-- A block at the tuples M is a block at the tuples M'. At M' := M × U this holds the part U
fixed while the block runs. It says nothing on a prover that picks that part behind the block's
challenges. -/
theorem comapM_knowAt {K X X' M M' Wp : Type} {Ei Eo : ExtSpec} {R : IOR X Ei X' Eo}
    {A : Rels K X Ei (M × Wp)} {B : Rels K X' Eo (M × Wp)} {ε : Err R.shape} (π : M' → M)
    (h : KnowAt R A B idW ε) : KnowAt R (comapM π A) (comapM π B) idW ε :=
  ⟨h.point, h.isLocal, h.onOut, fun m' => h.know (π m')⟩

end Cb.Sub
