-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdReadProofs.lean: the statements of Cb/Ld/LdRead.lean, proved.

The step without rounds (`ldRead_step`) rests on unique packing (`rngPk_cells`, `rngPk_iff_cells`,
Cb/Ld/LdRngAlgProofs.lean). `ldRead_goodT` takes the sending from Cb/Ld/LdSigSumProofs.lean
(`ldSendSig_goodT`) and the rules for a step before a reduction from
Ior/KnowCollRulesFrameProofs.lean (`goodB_pre`, `exact_pre`). `ldRead_rng` takes the range check
from Cb/Ld/LdRngProofs.lean (`ldRng_goodT`).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRead
import Cb.Ld.LdRngProofs
import Ior.KnowCollRulesFrameProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk IOR

theorem ldRead_cellmap : Spec.ldRead_cellmap := by
  intro E Bq I Rw C _ _ _ _ _ _ rowOf φ ψ cF cι Y hφ hψ
  have hp : ∀ ι c,
      ∑ r, placed (fun b => rowOf (b, ι)) φ r * Y r c = ∑ b, φ b * Y (rowOf (b, ι)) c :=
    fun ι c => ldRng_placed Bq Rw E _ φ (fun r => Y r c)
  simp_rw [hp]
  have h1 : ∑ b, ∑ c, φ b * ψ c * cF = cF := by
    simp_rw [← Finset.sum_mul]
    rw [← Finset.sum_mul_sum, hφ, hψ]
    ring
  have h2 : ∑ ι, cι ι * ∑ c, ψ c * ∑ b, φ b * Y (rowOf (b, ι)) c =
      ∑ b, ∑ c, ∑ ι, φ b * ψ c * (cι ι * Y (rowOf (b, ι)) c) := by
    calc ∑ ι, cι ι * ∑ c, ψ c * ∑ b, φ b * Y (rowOf (b, ι)) c
        = ∑ ι, ∑ c, ∑ b, φ b * ψ c * (cι ι * Y (rowOf (b, ι)) c) := by
          refine Finset.sum_congr rfl fun ι _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by ring
      _ = ∑ ι, ∑ b, ∑ c, φ b * ψ c * (cι ι * Y (rowOf (b, ι)) c) :=
        Finset.sum_congr rfl fun ι _ => Finset.sum_comm
      _ = ∑ b, ∑ ι, ∑ c, φ b * ψ c * (cι ι * Y (rowOf (b, ι)) c) := Finset.sum_comm
      _ = ∑ b, ∑ c, ∑ ι, φ b * ψ c * (cι ι * Y (rowOf (b, ι)) c) :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
  rw [h2]
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [h1]

theorem ldRead_iff : Spec.ldRead_iff := by
  intro E St J _ _ pp _ p b W cl st mpk mrd e hU hR
  have h := ((rngPk_iff_cells E pp p.Rp p.Rd p.C p.P b p.rdx (W st) mpk mrd hU).1 hR).2
  have e1 : readsOf (W st) (cells p.P b p.rdx mpk) = mrd :=
    funext fun k => funext fun c => (h k c).symm
  unfold ReadCl.OnCells
  rw [e1]

theorem ldRead_step : Spec.ldRead_step := by
  intro E St Kc Wp J _ _ pp _ E₀ p S c cl A₀ h hU
  refine ⟨extMap_isLocal.1 _, ?_, ?_, fun x w => rfl, ?_⟩
  · intro x y w hw
    obtain ⟨hE, hA, hP, hC, hR⟩ := hw
    have ec := rngPk_cells E pp p.Rp p.C p.P (2 * p.D) p.B p.rdx _ _ hU h.BD hP
    refine ⟨rfl, hE, hA, ⟨hP, fun k c => rfl⟩, ?_, hR⟩
    unfold ReadCl.OnCells at hC
    rw [ec] at hC
    exact hC
  · intro x y x' ho hf
    cases hf
    exact ho
  · intro x y x' w' ho hf hw
    cases hf
    obtain ⟨hd, hR, hC, hA⟩ := hw
    exact ⟨hd,
      ((rngPk_iff_cells E pp p.Rp p.Rd p.C p.P (2 * p.D) p.rdx (c.W x.1) _ _ hU).1 hR).1,
      (ldRead_iff E St J pp p (2 * p.D) c.W cl x.1 _ _ _ hU hR).2 hC,
      hA⟩

theorem ldRead_joint : Spec.ldRead_joint := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl

theorem ldRead_goodT : Spec.ldRead_goodT := by
  intro E St Kc Wp J _ _ pp _ E₀ p S N c cl A₀ get Sd Dn L t h hU hC hF hL hE hD hB hZ
  have st := ldRead_step E St Kc Wp J pp E₀ p S c cl A₀ h hU
  have g := ldSendSig_goodT E S N Sd Kc St (Wp × p.Rds E) Wp E₀ (readMid p c cl A₀) (readBk p N get)
    Dn L t hC hF hL hE hD hB hZ
  obtain ⟨gb, ge⟩ := (goodT_iff _ _ _ _ _ _ _ _ _ _ _ _ _).1 g
  have gb' := goodB_pre Kc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun _ _ w => (S.left N (T := OMsg.Wit) w.1, w.2)) _ _ _ _ _ st gb (fun a x₁ τ w hf => rfl)
  have ge' := exact_pre _ _ _ _ _ _ _ _ _ _ _ _ (S.over (readIn p c cl A₀)).rel _ _ _
    (readM p S c A₀) (extMap_isLocal.1 _) (fun x y w hw => st.acc x y w hw) ge
  rw [← ldRead_joint E St Kc Wp J E₀ p S N c cl A₀ get]
  exact (goodT_cf_in _ _ _ _ _ _ _ _ _ _ _ _ _).1
    ((goodT_iff _ _ _ _ _ _ _ _ _ _ _ _ _).2 ⟨gb', ge'⟩)

theorem ldRead_rounds : Spec.ldRead_rounds := fun _ _ _ _ _ _ _ => rfl

theorem ldRead_rng : Spec.ldRead_rng := by
  intro E St Kc Wp J _ _ pp _ E₀ p S N N' c cl A₀ get Sd Dn L t get' Sd' Dn' L' t' h hU hC hF hL hE
    hD hB hZ hC' hF' hL' hE' hD' hB' hZ'
  have g₁ := ldRead_goodT E St Kc Wp J pp E₀ p S N c cl A₀ get Sd Dn L t h hU hC hF hL hE hD hB hZ
  have g₂ := ldRng_goodT E St Kc Wp E₀ p (S.sum N) N'
    (c.withReads p S N get) (S.grow N (readRows p c cl A₀) (readBk p N get))
    get' Sd' Dn' L' t' h hC' hF' hL' hE' hD' hB' hZ'
  exact goodT_seq_ext Kc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g₁ g₂ (fun a τ₁ τ₂ b w hb => rfl)

theorem ldRead_rows : Spec.ldRead_rows := by
  intro E St J _ _ _ p cl at' st v
  have hrow : ∀ j, ∑ n, readRow cl at' j st n * v n =
      ∑ k, ∑ c, cl.cw st j k c * v (at' k c) + ∑ n, cl.ms st j n * v n := by
    intro j
    show ∑ n, (placed (fun x : p.Rd × p.C => at' x.1 x.2) (fun x => cl.cw st j x.1 x.2) n +
          cl.ms st j n) * v n = _
    simp only [add_mul, Finset.sum_add_distrib]
    rw [ldRng_placed (p.Rd × p.C) J E _ _ v, Fintype.sum_prod_type]
  constructor
  · intro h j
    show ∑ n, readRow cl at' j st n * v n = cl.v st j - cl.k0 st j
    rw [hrow]
    linear_combination h j
  · intro h j
    have h1 : ∑ n, readRow cl at' j st n * v n = cl.v st j - cl.k0 st j := h j
    rw [hrow] at h1
    linear_combination h1

end Cb
