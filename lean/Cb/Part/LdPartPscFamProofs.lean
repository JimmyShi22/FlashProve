-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartPscFamProofs.lean: the proofs of the statements of Cb/Part/LdPartPscFam.lean (a
family of conditions ↦ the sumcheck on its sum predicate).
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Of general use: `ldPartNames_map`, `ldPartNames_len`; `ldPart_ext_deg` (the multilinear extension
of a numbered vector, read on functions, has degree at most 1 in each coordinate);
`ldPart_atom_deg` (so has every well-formed atom's extension at the format's sizes Φ.h, Φ.hi +
Φ.lo, at all matrices over E). Nothing else is said here.
-/
import Cb.Part.LdPartPscFam
import Cb.Part.LdPartPscProofs
import Cb.Part.LdPartProofs
import Cb.Req.ReqSumCubeProofs
import Cb.Req.ReqSumTermsProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

theorem ldPartNames_map {β : Type} (na : ℕ) (l : List ℕ) (h : ∀ j ∈ l, j < na) (Y : ℕ → β) :
    (ldPartNames na l).map (fun a : Fin na => Y a.val) = l.map Y := by
  induction l with
  | nil => rfl
  | cons j l ih =>
      have hj : j < na := h j List.mem_cons_self
      have ih' := ih fun i hi => h i (List.mem_cons_of_mem _ hi)
      unfold ldPartNames at ih' ⊢
      rw [List.filterMap_cons_some (dif_pos hj), List.map_cons, List.map_cons, ih']

theorem ldPartNames_len (na : ℕ) (l : List ℕ) : (ldPartNames na l).length ≤ l.length :=
  List.length_filterMap_le _ _

section
variable {X E : Type} [Field E]

theorem ldPart_ext_deg (V : ℕ) (u : ℕ → E) :
    Alg.DegLE (fun _ : Fin V => 1) fun z : Fin V → E => Blocks.ext V u (Blocks.nat z) := by
  have e : (fun z : Fin V → E => Blocks.ext V u (Blocks.nat z)) =
      Alg.mle fun b : Fin V → Bool => u (Alg.num b) :=
    funext fun z => Req.ext_nat E V u z
  rw [e]
  exact Alg.DegLE.mle _

theorem ldPart_atom_deg {F : Type} [Field F] [Algebra F E] (Φ : IdxFmt F) (a : Atom X E) (v : ℕ)
    (x : X) (WE : ℕ → ℕ → E) (A : ℕ → ℕ → ℕ → E) (hw : a.WF Φ v) :
    Alg.DegLE (fun _ : Fin v => 1) fun z : Fin v → E =>
      a.ext Φ.h (Φ.hi + Φ.lo) v x WE A (Blocks.nat z) := by
  match a, hw with
  | .base (.cell c), _ => exact ldPart_ext_deg v _
  | .base (.idx a), hw =>
      have e : (fun z : Fin v → E =>
            (Atom.base (X := X) (.idx a)).ext Φ.h (Φ.hi + Φ.lo) v x WE A (Blocks.nat z)) =
          fun z : Fin v → E =>
            Blocks.ext v (fun b => formE Φ.h (Φ.hi + Φ.lo) (a.g (vtx v b)) (a.ψ (vtx v b)) WE)
                (Blocks.nat z) :=
        funext fun z => (ldPart_idx F E Φ v a hw WE (Blocks.nat z)).symm
      rw [e]
      exact ldPart_ext_deg v _
  | .sum w P, _ => exact ldPart_ext_deg v _

end

section
variable (X E : Type) [Field E] [Fintype E]

omit [Fintype E] in
theorem ldPartFam_val : Spec.ldPartFam_val X E := by
  intro f h k ve St J rx rp rd st m z hn
  show ((f.terms.map fun t =>
      (⟨fun st z => Blocks.ext f.v (t.coef (rx st)) (Blocks.nat z),
        ldPartNames f.na t.atoms⟩ : LdPartTm E St (Fin f.na) f.v)).map fun t =>
          t.coef st z *
            (t.atoms.map fun a : Fin f.na =>
              (f.atom a).ext h k f.v (rx st) (rd.W m) (rd.A m) (Blocks.nat z)).prod).sum = _
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  exact congrArg (Blocks.ext f.v (t.coef (rx st)) (Blocks.nat z) * ·)
    (congrArg List.prod
      (ldPartNames_map f.na t.atoms (hn t ht) fun j =>
        (f.atom j).ext h k f.v (rx st) (rd.W m) (rd.A m) (Blocks.nat z)))

theorem ldPartFam_ok : Spec.ldPartFam_ok X E := by
  intro F _ _ Φ f ve St J rx rp rd M hw hn hd
  have hl : ∀ t ∈ f.terms, (ldPartNames f.na t.atoms).length ≤ f.deg := fun t ht =>
    (ldPartNames_len f.na t.atoms).trans (Req.le_maxLen f.lists t.atoms (List.mem_map_of_mem ht))
  refine ⟨fun st m a => ldPart_atom_deg Φ (f.atom a) f.v (rx st) (rd.W m) (rd.A m) (hw.2 a a.2),
    fun t ht => ?_,
    fun _ i _ => le_trans (Nat.le_add_left 1 _) (hn i),
    fun t ht => ?_⟩
  · obtain ⟨t0, h0, rfl⟩ := List.mem_map.1 ht
    refine ⟨fun _ => 1, fun st => ldPart_ext_deg f.v _, fun i => ?_⟩
    have h1 : ((ldPartNames f.na t0.atoms).map fun _ => 1).sum =
        (ldPartNames f.na t0.atoms).length := by simp
    have h2 := hl t0 h0
    have h3 := hn i
    show 1 + ((ldPartNames f.na t0.atoms).map fun _ => 1).sum ≤ M.n i
    rw [h1]
    omega
  · obtain ⟨t0, h0, rfl⟩ := List.mem_map.1 ht
    exact (hl t0 h0).trans hd

theorem ldPartFam_sum : Spec.ldPartFam_sum X E := by
  intro f h k ve St J _ rx rp rd M τ st m hn hv
  have e : ∑ b : Fin f.v → Bool, (∏ i, ldPartWt ((f.partSm h k ve rx rp rd).w st i) (b i)) *
        (f.partSm h k ve rx rp rd).val st m (Alg.corner b) =
      Blocks.ext ve
        (fun b =>
          ∑ j ∈ Finset.range (2 ^ (f.v - ve)),
            f.ext h k (rx st) (rd.W m) (rd.A m) (vtx f.v (b * 2 ^ (f.v - ve) + j))) (rp st) := by
    rw [← Req.wsum_split E f.v ve (f.v - ve) (rp st)
        (fun c => f.ext h k (rx st) (rd.W m) (rd.A m) (vtx f.v c)) (by omega)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [ldPartFam_val X E f h k ve St J rx rp rd st m (Alg.corner b) hn, Req.vtx_num]
    refine congrArg (· * _) (Finset.prod_congr rfl fun i _ => ?_)
    show ldPartWt (if i.val < ve then some (rp st i) else none) (b i) = _
    unfold Req.wts
    by_cases hi : i.val < ve <;> simp [hi, ldPartWt]
  exact (ldPartPsc_sum E St J _ M τ st m).trans
    (Eq.congr (congrArg (· + ∑ j, M.slS st j * m j) e) rfl)

theorem ldPartFam_all : Spec.ldPartFam_all X E := by
  intro f h k St J _ rx rp rd M τ st m hn
  simpa using ldPartFam_sum X E f h k f.v St J rx rp rd M τ st m hn le_rfl

theorem ldPartFam_allV : Spec.ldPartFam_allV X E := by
  intro F _ _ Φ f St J _ rx rp rd M τ st m W hw hW
  rw [ldPartFam_all X E f Φ.h (Φ.hi + Φ.lo) St J rx rp rd M τ st m hw.1, hW,
    Blocks.ext_congr fun b hb => (ldPart_vtx X F E Φ (rx st) W (rd.A m)).2.2.2 f b hw hb]

theorem ldPartFam_atom : Spec.ldPartFam_atom X E := by
  intro P h k v w St J _ rx rp rd M τ st m hn hP
  have hw : P.v - v = w := by omega
  refine (ldPartFam_sum X E P.toFam h k v St J rx rp rd M τ st m
    hn (show v ≤ P.v by omega)).trans ?_
  show Blocks.ext v
          (fun b =>
            ∑ j ∈ Finset.range (2 ^ (P.v - v)),
              P.ext h k (rx st) (rd.W m) (rd.A m) (vtx P.v (b * 2 ^ (P.v - v) + j))) (rp st) + _ =
      τ ↔
    Blocks.ext v (fun b =>
            ∑ j ∈ Finset.range (2 ^ w),
              P.ext h k (rx st) (rd.W m) (rd.A m) (vtx (v + w) (b * 2 ^ w + j))) (rp st) + _ = τ
  rw [hw, hP]

theorem ldPartFam_row : Spec.ldPartFam_row X E := fun f h k ve St J _ rx rp rd M o m a =>
  ldPartPsc_val E St J (f.partSm h k ve rx rp rd) M o m a

theorem ldPartFam_next : Spec.ldPartFam_next X E := by
  intro f h k ve St St' J _ rx rp rx' rp' rd M a w P M' o st' m ha hn hP hx hp hs
  refine (ldPartFam_row X E f h k ve St J rx rp rd M o m a).trans ?_
  refine Iff.trans ?_
    (ldPartFam_atom X E P h k f.v w St' J rx' rp' rd M' (o.vals a) st' m hn hP).symm
  rw [ha, hx, hp, hs]

end
end Cb
