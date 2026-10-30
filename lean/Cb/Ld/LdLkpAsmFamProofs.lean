-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpAsmFamProofs.lean: the proofs of the statements of Cb/Ld/LdLkpAsmFam.lean (the assembled
lookup with its rows as a family of fixed size: no list is filed).
-/
import Cb.Ld.LdLkpAsmFam
import Cb.Ld.LdLkpAsmPullProofs
import Cb.Ld.LdLkpSuppProofs

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

/-- a list of n rows holds if and only if its rows, as a family over Fin n (as in `toFam`), do -/
theorem fam_rows {E N : Type} [Field E] [Fintype N] (n : ℕ) (rs : List (Row E N))
    (μ : N → E) (hn : rs.length = n) :
    (∀ i : Fin n, (rs.getD i ⟨fun _ => 0, 0⟩).Holds μ) ↔ RowsHold rs μ := by
  constructor
  · intro h r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
    have h1 := h ⟨i, by rw [← hn]; exact hi⟩
    rw [show rs.getD (((⟨i, by rw [← hn]; exact hi⟩ : Fin n)) : ℕ) ⟨fun _ => 0, 0⟩ = rs[i]
        from List.getD_eq_getElem _ _ hi] at h1
    exact h1
  · intro h i
    have hi : (i : ℕ) < rs.length := by rw [hn]; exact i.2
    rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)

theorem ldLkpAsmF_fam : Spec.ldLkpAsmF_fam := fun _ _ _ _ _ _ _ _ _ ent n x m' hn =>
  and_congr Iff.rfl (and_congr (fam_rows n x.2.2 (ent m') hn) Iff.rfl)

section
variable (E : Type) [Field E] [Fintype E]

theorem rdN_len (A : LkAsm E) {N : Type} (ι : N → A.J) (o : A.Q.XB) :
    (A.rdN ι o).2.2.length = A.nRows :=
  (List.length_map _).trans (ldLkpAsm_len E A o)

theorem ldLkpAsmF_base : Spec.ldLkpAsmF_base E := by
  intro p _ A N _ ι Mu Ex Kc M Wp R0 msg hι hP hA hMu
  have g := A.chain_good E p Mu Ex Kc M Wp R0 msg hA hMu
  have hf : ∀ (o : A.Q.XB) (m : A.J → E),
      A.lk.outF id (A.entN ι) (A.rdF ι o) m ↔ A.lk.out id id (A.rd o) m := fun o m =>
    (ldLkpAsmF_fam E A.St (A.J → E) (A.J → E) N A.lk id (A.entN ι) A.nRows (A.rdN ι o)
        m (rdN_len E A ι o)).trans
      (A.outN_iff E N ι hι hP o m)
  unfold BkA.Good at g ⊢
  refine goodAt_postMap Kc M _ _ _ Ex Ex Wp Wp _ _ _ _ _ _ _ (A.rdF ι) g ?_ ?_ ?_ ?_
  · intro o y w h
    exact ⟨h.1,
      (hf o _).mpr ((A.out_iff o _).mpr ⟨⟨⟨⟨h.2.1.1.1.1, trivial⟩, h.2.1.1.2⟩, h.2.1.2⟩, h.2.2⟩)⟩
  · exact fun _ _ h => h
  · exact fun _ => rfl
  · intro o y w _ h
    exact ⟨h.1, (A.out_iff o _).mp ((hf o _).mp h.2)⟩

theorem plain_chainA (A : LkAsm E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) :
    (A.chainA Ex M Wp Kc msg).Plain :=
  plain_seq (plain_seq (plain_head Ex M Wp Kc A.H msg) (plain_segK Ex M Wp Kc A.IK A.v' A.tK msg))
    (plain_segT Ex M Wp Kc A.Q msg)

theorem ldLkpAsmF_plain : Spec.ldLkpAsmF_plain E := fun A _ ι Ex M Wp Kc msg =>
  plain_postM (plain_chainA E A Ex M Wp Kc msg) (A.rdF ι)

theorem ldLkpAsmF_pass : Spec.ldLkpAsmF_pass E := fun A _ ι Ex M Wp Kc msg =>
  (((pass_head Ex M Wp Kc A.H msg).seq
    (passes_map (pass_segK Ex M Wp Kc A.IK A.v' A.tK msg) fun x => (A.b2 x).1)).seq
    (passes_map (pass_segT Ex M Wp Kc A.Q msg) fun x => (A.b2 (A.o4 x)).1)).post _ _ fun o x' e => by
      obtain rfl := Option.some.inj e
      rfl

theorem ldLkpAsmF_noOrcs : Spec.ldLkpAsmF_noOrcs E := fun A _ _ Ex M Wp Kc msg =>
  noOrcs_base Ex M Wp Kc A msg

theorem ldLkpAsmF_shape : Spec.ldLkpAsmF_shape E := fun _ _ _ _ _ _ _ _ => rfl

omit [Fintype E] in
theorem ldLkpAsmF_supp : Spec.ldLkpAsmF_supp E := fun _ _ _ _ ι _ _ =>
  ⟨supp_pushJ ι _ _ fun n hn => absurd ⟨n, rfl⟩ hn,
    fun _ => supp_pushJ ι _ _ fun n hn => absurd ⟨n, rfl⟩ hn⟩

end
end Cb
