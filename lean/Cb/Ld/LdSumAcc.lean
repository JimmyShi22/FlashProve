-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumAcc.lean: proofs of `Spec.ld_sum_point`, `Spec.ld_sum_local` and `Spec.ld_sum_acc`
(Cb/Ld/LdSum.lean): strings (`Shape.IsPoint`), locality (`IOR.IsLocal`), perfect completeness of the
zero-knowledge sumcheck, each under the hypotheses of its statement.
Also, for a code with `C.Laws` (Cb/Ld/LdRel.lean): folding commutes with its linear encoder
(`enc_fold`) and with its linear transformation (`T_fold`).
-/
import Cb.Ld.LdSumHon

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

section Fold
variable {E P : Type} [Field E] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem enc_fold (C : LdCode E P) (hC : C.Laws) (γ : ι → E)
    (m : (C.il (ι → Bool)).J → E) (r : (C.il (ι → Bool)).Q → E) :
    SumPar.foldW C γ ((C.il (ι → Bool)).enc m r) = C.enc (foldV γ m) (foldV γ r) := by
  have e : ((foldV γ m, foldV γ r) : (C.J → E) × (C.Q → E)) =
      ∑ b, Alg.eqk γ b • ((fun j => m (b, j), fun q => r (b, q)) : (C.J → E) × (C.Q → E)) := by
    refine Prod.ext ?_ ?_
    · funext j
      simp [foldV, Prod.fst_sum, Finset.sum_apply]
    · funext q
      simp [foldV, Prod.snd_sum, Finset.sum_apply]
  have h := map_sum (IsLinearMap.mk' _ hC.encLin)
    (fun b => Alg.eqk γ b • ((fun j => m (b, j), fun q => r (b, q)) : (C.J → E) × (C.Q → E)))
    Finset.univ
  rw [← e] at h
  have h' : C.enc (foldV γ m) (foldV γ r) =
      ∑ b, Alg.eqk γ b • C.enc (fun j => m (b, j)) (fun q => r (b, q)) := by
    refine h.trans (Finset.sum_congr rfl fun b _ => ?_)
    exact (IsLinearMap.mk' _ hC.encLin).map_smul _ _
  rw [h']
  funext p s
  simp [SumPar.foldW, foldV, Finset.sum_apply]

theorem T_fold (C : LdCode E P) (hC : C.Laws) (γ : ι → E)
    (f : (C.il (ι → Bool)).Word) (x : P) (α : C.Aa) :
    C.T (SumPar.foldW C γ f) x α = ∑ b, Alg.eqk γ b * (C.il (ι → Bool)).T f x (b, α) := by
  have e : SumPar.foldW C γ f = ∑ b, Alg.eqk γ b • (fun p s => f p (b, s) : C.Word) := by
    funext p s
    simp [SumPar.foldW, foldV, Finset.sum_apply]
  have h := map_sum (IsLinearMap.mk' _ hC.tLin)
    (fun b => Alg.eqk γ b • (fun p s => f p (b, s) : C.Word)) Finset.univ
  rw [← e] at h
  have h' : C.T (SumPar.foldW C γ f) = ∑ b, Alg.eqk γ b • C.T (fun p s => f p (b, s)) := by
    refine h.trans (Finset.sum_congr rfl fun b _ => ?_)
    exact (IsLinearMap.mk' _ hC.tLin).map_smul _ _
  rw [h']
  simp [Finset.sum_apply]

end Fold

namespace SumPar
variable {E P : Type} [Field E] (Y : SumPar E P)

theorem out_of (x : Y.Xi) (τ : Tr Y.shape) (ρ : Rho Y.shape) (μ : E) (q : RIdx Y.vars → E)
    (h1 : Y.qs τ.plains = q) (h2 : Y.mu τ.plains = μ) (h3 : τ.rho = ρ) :
    Y.out x τ =
      open Classical in if HCons Y.vars (μ + x.1 * Y.eps ρ) q (Y.gam ρ) then
        some (Y.newX x ρ (hFin Y.vars (μ + x.1 * Y.eps ρ) q (Y.gam ρ)))
      else none := by
  unfold SumPar.out
  rw [h1, h2, h3]

theorem imp_of (y : Y.Cin.Word) (τ : Tr Y.shape) (ρ : Rho Y.shape) (h3 : τ.rho = ρ) :
    Y.imp y τ =
      LdCode.mkW (foldW Y.C (Y.pt ρ) (LdCode.fstW y))
        (LdCode.mkW (C₁ := Y.Z) (C₂ := Y.Zw) (foldW Y.Z (Y.pre (Y.pt ρ)) (LdCode.sndW y))
          (foldW Y.Zw (Y.pre (Y.pt ρ)) τ.1.1)) := by
  unfold SumPar.imp
  rw [h3]

end SumPar

def sRound_point (E Ch : Type) [Field E] [Fintype Ch] [Nonempty Ch] (n : ℕ) :
    (sRound E Ch n).IsPoint where
  finPos := inferInstanceAs (Fintype Empty)
  decPos := inferInstanceAs (DecidableEq Empty)
  ofSyms := fun _ => ()
  rd_ofSyms := fun _ p => p.elim
  ofSyms_rd := fun _ => rfl
  zero := fun _ => ()

def sRounds_point (E Ch : Type) [Field E] [Fintype Ch] [Nonempty Ch] (n : ℕ) :
    (k : ℕ) → Shape.IsPoint (List.replicate k (sRound E Ch n))
  | 0 => ()
  | k + 1 => (sRound_point E Ch n, sRounds_point E Ch n k)

theorem ld_sum_point (E P : Type) [Field E] [Fintype E] : Spec.ld_sum_point E P := fun Y =>
  ⟨(⟨inferInstanceAs (Fintype Y.Cw.NP), inferInstanceAs (DecidableEq Y.Cw.NP), fun f => f,
      fun _ _ => rfl, fun _ => rfl, fun _ _ => 0⟩,
    sRounds_point E Y.Ch Y.n Y.k)⟩

theorem ld_sum_local (E P : Type) [Field E] [Fintype E] : Spec.ld_sum_local E P := by
  intro Y hC hZ hW
  refine ⟨?_, ?_⟩
  · intro x y y' τ τ' hρ hpl _ _
    show Y.out x τ = Y.out x τ'
    rw [Y.out_of x τ τ'.rho (Y.mu τ'.plains) (Y.qs τ'.plains)
          (congrArg Y.qs hpl) (congrArg Y.mu hpl) hρ,
      Y.out_of x τ' _ _ _ rfl rfl rfl]
    rfl
  · intro y y' τ τ' q hρ hpl hE hO
    have hq : Y.Cin.T y q = Y.Cin.T y' q := hE q (Finset.mem_singleton_self q)
    show Y.Cout.T (Y.imp y τ) q = Y.Cout.T (Y.imp y' τ') q
    rw [Y.imp_of y τ τ'.rho hρ, Y.imp_of y' τ' τ'.rho rfl]
    funext α
    rcases α with α | α | α
    · show Y.C.T (SumPar.foldW Y.C (Y.pt τ'.rho) (LdCode.fstW y)) q α =
        Y.C.T (SumPar.foldW Y.C (Y.pt τ'.rho) (LdCode.fstW y')) q α
      rw [T_fold Y.C hC, T_fold Y.C hC]
      exact Finset.sum_congr rfl fun b _ => congrArg _ (congrFun hq (.inl (b, α)))
    · show Y.Z.T (SumPar.foldW Y.Z (Y.pre (Y.pt τ'.rho)) (LdCode.sndW y)) q α =
        Y.Z.T (SumPar.foldW Y.Z (Y.pre (Y.pt τ'.rho)) (LdCode.sndW y')) q α
      rw [T_fold Y.Z hZ, T_fold Y.Z hZ]
      exact Finset.sum_congr rfl fun b _ => congrArg _ (congrFun hq (.inr (b, α)))
    · show Y.Zw.T (SumPar.foldW Y.Zw (Y.pre (Y.pt τ'.rho)) τ.1.1) q α =
        Y.Zw.T (SumPar.foldW Y.Zw (Y.pre (Y.pt τ'.rho)) τ'.1.1) q α
      refine congrFun (hW.loc _ _ q fun p hp => ?_) α
      have h1 : τ.read (.inl p) = τ'.read (.inl p) := hO (.inl p) (Finset.mem_map.2 ⟨p, hp, rfl⟩)
      have h2 : τ.1.1 p = τ'.1.1 p := h1
      show foldV _ (τ.1.1 p) = foldV _ (τ'.1.1 p)
      rw [h2]

theorem ld_sum_acc (E P : Type) [Field E] [Fintype E] : Spec.ld_sum_acc E P := by
  intro Y hn hP hC hZ hW x y w c ρ hR _
  obtain ⟨r1, r2, r3, r4⟩ := ld_sum_run E P Y w x c ρ
  obtain ⟨hy, hcl⟩ := hR
  have hcl' : ∑ j, Y.slIn x.2 j * w.1 j = x.1 := hcl
  obtain ⟨k1, k2⟩ := hRounds_cons Y.vars _ _ _ (Y.honQ_rounds hn w x c.1 (Y.eps ρ) (Y.gam ρ))
  rw [Y.summand_sum hn, hcl'] at k1 k2
  refine ⟨?_, ?_, ?_⟩
  · show Y.out x ((Y.hon.strat w x c).run ρ).1 = _
    rw [Y.out_of x _ ρ _ _ r1 r2 r3, if_pos k1, r4]
    rfl
  · rw [r4]
    show Y.imp y ((Y.hon.strat w x c).run ρ).1 =
      Y.Cout.enc (Y.honW w c (sPt Y.n Y.k (Y.gam ρ))).1 (Y.honW w c (sPt Y.n Y.k (Y.gam ρ))).2
    rw [Y.imp_of y _ ρ r3, hy]
    funext p
    rcases p with p | p | p
    · exact congrFun (enc_fold Y.C hC (Y.pt ρ) (fun a => w.1 (.inl a)) (fun a => w.2 (.inl a))) p
    · exact congrFun
        (enc_fold Y.Z hZ (Y.pre (Y.pt ρ)) (fun a => w.1 (.inr a)) (fun a => w.2 (.inr a))) p
    · exact congrFun (enc_fold Y.Zw hW (Y.pre (Y.pt ρ)) (Y.pk c.1) c.2) p
  · rw [r4]
    show ∑ j, Y.slOut (Y.honEnd w x c (Y.eps ρ) (Y.gam ρ)).1.2 j *
        (Y.honW w c (sPt Y.n Y.k (Y.gam ρ))).1 j =
      hFin Y.vars _ _ _
    rw [k2, Fintype.sum_sum_type, Fintype.sum_sum_type]
    unfold SumPar.summand
    rw [hP]
    have a1 : ∀ (A B : Y.C.J → E) (e : E),
        ∑ c, A c * e * B c = e * ∑ c, A c * B c := fun A B e => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
    have a2 : ∀ (A B : Y.Z.J → E) (e : E),
        ∑ c, A c * e * B c = e * ∑ c, A c * B c := fun A B e => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
    show ∑ c, Y.sl.fix (x.2.1, sPt Y.n Y.k (Y.gam ρ)) c * Y.eps ρ *
          foldV (sPt Y.n Y.k (Y.gam ρ)) (fun a => w.1 (.inl a)) c +
        (∑ c, Y.slS.fix (x.2.2, Y.pre (sPt Y.n Y.k (Y.gam ρ))) c *
            (Y.eps ρ * Y.late (sPt Y.n Y.k (Y.gam ρ))) *
            foldV (Y.pre (sPt Y.n Y.k (Y.gam ρ))) (fun a => w.1 (.inr a)) c +
          ∑ j,
            Y.Qw (sPt Y.n Y.k (Y.gam ρ)) j * foldV (Y.pre (sPt Y.n Y.k (Y.gam ρ))) (Y.pk c.1) j) = _
    rw [a1, a2]
    ring

end Cb
