-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumClaimY.lean: the sums claimed between the rounds of the sumcheck `Y.ior`
(Cb/Ld/LdSum.lean), as linear forms on three tables of messages (`SMsg`); ε stands for the value in
E (`Y.eps`) of the verifier's message of round 0.

Definitions, statements and proofs. The claims (`SStg`) are those of Cb/Ld/LdSumClaim.lean.

Main names:
  `Y.stg0 x ε`: the public side of the claim after the coefficient ε. It has three parts (`Af`,
    `As`, `Aw` of `SStg`): the main form times ε; the mask form times ε and the later variables
    (`Y.late z`); the weights of the hiding polynomial (`Y.Qw`).
  `stg0_val`: the claimed quantity is affine in ε: (sum over the cube of <weights, fresh table>) + ε
    (value of the input form).
  `Y.QwDeg`: what knowledge soundness asks of the weights: degree at most n - 1 in each of the first
    h variables, at most n in the others.
  `stg0_deg`: then, and if 2 ≤ n, the summand has degree at most n in each variable, whatever the
    three tables (main, carried mask, fresh mask).
  `stg_end`: after all rounds the claim is the output form at the verifier's new state.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSumClaim

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

section
variable {E : Type} [Field E] {Jc Jz : Type}

/-- all rounds: `S.next` at each coordinate of γ in turn, down to no variable -/
def SStg.nextAll (n : ℕ) : (k : ℕ) → HPt (sVars E n k) → SStg E Jc Jz k → SStg E Jc Jz 0
  | 0, _, S => S
  | k + 1, γ, S => SStg.nextAll n k γ.2 (S.next γ.1)

theorem SStg.nextAll_eq (n : ℕ) :
    ∀ (k : ℕ) (γ : HPt (sVars E n k)) (S : SStg E Jc Jz k) (z : Fin 0 → E),
      (SStg.nextAll n k γ S).Af z = S.Af (sPt n k γ) ∧
      (SStg.nextAll n k γ S).As z = S.As (sPt n k γ) ∧
      (SStg.nextAll n k γ S).Aw z = S.Aw (sPt n k γ) := by
  intro k
  induction k with
  | zero =>
      intro γ S z
      have e : z = sPt n 0 γ := Subsingleton.elim _ _
      rw [e]
      exact ⟨rfl, rfl, rfl⟩
  | succ k ih => intro γ S z; exact ih γ.2 (S.next γ.1) z

end

namespace SumPar
variable {E P : Type} [Field E] (Y : SumPar E P)

/-- The claim after the coefficient. -/
def stg0 (x : Y.Xi) (ε : E) : SStg E Y.C.J Y.Z.J Y.k :=
  ⟨fun z c => Y.sl.fix (x.2.1, z) c * ε,
    fun z c => Y.slS.fix (x.2.2, Y.pre z) c * (ε * Y.late z),
    Y.Qw⟩

/-- What knowledge soundness asks of the weights. -/
def QwDeg : Prop :=
  ∀ j, Alg.DegLE (fun i : Fin Y.k => if i.val < Y.h then Y.n - 1 else Y.n) fun z => Y.Qw z j

theorem pre_eq (z : Fin Y.k → E) : preP Y.k Y.h z = Y.pre z :=
  funext fun i => dif_pos (show i.val < Y.h + Y.g by have := i.2; omega)

/-- the part of three tables that the input statement is about -/
def inM (m : SMsg E Y.C.J Y.Z.J Y.k Y.h) : Y.Cin.J → E :=
  Sum.elim (fun a => m (.inl a)) fun a => m (.inr (.inl a))

/-- the sum over the cube of <weights, fresh table> -/
def psi0 (m : SMsg E Y.C.J Y.Z.J Y.k Y.h) : E :=
  hSumAll Y.vars fun γ =>
    ∑ c, Y.Qw (sPt Y.n Y.k γ) c * foldV (Y.pre (sPt Y.n Y.k γ)) (fun a => m (.inr (.inr a))) c

theorem stg0_val (x : Y.Xi) (ε : E) (m : SMsg E Y.C.J Y.Z.J Y.k Y.h) :
    (Y.stg0 x ε).val Y.n Y.h m = Y.psi0 m + ε * ∑ j, Y.slIn x.2 j * Y.inM m j := by
  have a1 : ∀ (A B : Y.C.J → E) (e : E), ∑ c, A c * e * B c = e * ∑ c, A c * B c := fun A B e => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
  have a2 : ∀ (A B : Y.Z.J → E) (e : E), ∑ c, A c * e * B c = e * ∑ c, A c * B c := fun A B e => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
  have e : (fun γ => (Y.stg0 x ε).sm Y.h m (sPt Y.n Y.k γ)) =
      fun γ =>
        (∑ c, Y.Qw (sPt Y.n Y.k γ) c *
              foldV (Y.pre (sPt Y.n Y.k γ)) (fun a => m (.inr (.inr a))) c) +
            ε • sCl Y.n Y.k (Y.tabL x) (Y.tabM (Y.inM m)) γ := by
    funext γ
    rw [Y.sCl_tab]
    unfold SStg.sm
    rw [Y.pre_eq]
    show ∑ c,
          Y.sl.fix (x.2.1, sPt Y.n Y.k γ) c * ε * foldV (sPt Y.n Y.k γ) (fun a => m (.inl a)) c +
        (∑ c, Y.slS.fix (x.2.2, Y.pre (sPt Y.n Y.k γ)) c * (ε * Y.late (sPt Y.n Y.k γ)) *
            foldV (Y.pre (sPt Y.n Y.k γ)) (fun a => m (.inr (.inl a))) c +
          ∑ c,
            Y.Qw (sPt Y.n Y.k γ) c * foldV (Y.pre (sPt Y.n Y.k γ)) (fun a => m (.inr (.inr a))) c) =
      ∑ c, Y.Qw (sPt Y.n Y.k γ) c * foldV (Y.pre (sPt Y.n Y.k γ)) (fun a => m (.inr (.inr a))) c +
        ε * (∑ c,
              Y.sl.fix (x.2.1, sPt Y.n Y.k γ) c * foldV (sPt Y.n Y.k γ) (fun a => m (.inl a)) c +
            (∑ c, Y.slS.fix (x.2.2, Y.pre (sPt Y.n Y.k γ)) c *
                foldV (Y.pre (sPt Y.n Y.k γ)) (fun a => m (.inr (.inl a))) c) *
              Y.late (sPt Y.n Y.k γ))
    rw [a1, a2]
    ring
  unfold SStg.val
  rw [e, hSumAll_add_smul, sCl_sum, Y.sBl_tab]
  rfl

theorem deg_fix {St J : Type} {k : ℕ} (sl : Slf E St ((Fin k → Bool) × J)) (st : St) (c : J) :
    Alg.DegLE (fun _ => 1) fun z : Fin k → E => sl.fix (st, z) c :=
  Alg.DegLE.sum Finset.univ fun b _ => (Alg.DegLE.eqk b).const_mul (sl st (b, c))

theorem deg_foldV {J : Type} {k : ℕ} (v : (Fin k → Bool) × J → E) (c : J) :
    Alg.DegLE (fun _ => 1) fun z : Fin k → E => foldV z v c :=
  Alg.DegLE.sum Finset.univ fun b _ => (Alg.DegLE.eqk b).mul_const (v (b, c))

theorem deg_pre {g : (Fin Y.h → E) → E} (hg : Alg.DegLE (fun _ => 1) g) :
    Alg.DegLE (fun i : Fin Y.k => if i.val < Y.h then 1 else 0) fun z => g (Y.pre z) :=
  hg.comp (Fin.castAdd Y.g) (Fin.castAdd_injective _ _) _ fun v => by simp

theorem deg_late :
    Alg.DegLE (fun i : Fin Y.k => if i.val < Y.h then 0 else 1) fun z => Y.late z := by
  have h := (Alg.DegLE.eqk (K := E) fun _ : Fin Y.g => true).comp (Fin.natAdd Y.h)
    (Fin.natAdd_injective _ _) (fun i : Fin Y.k => if i.val < Y.h then 0 else 1) fun v => by simp
  have e : (fun z : Fin Y.k → E => Alg.eqk (fun v => z (Fin.natAdd Y.h v)) fun _ => true) =
      fun z => Y.late z := by
    funext z; simp [Alg.eqk, late]
  rwa [e] at h

theorem stg0_deg (hn : 2 ≤ Y.n) (hQ : Y.QwDeg) (x : Y.Xi) (ε : E) : (Y.stg0 x ε).Deg Y.n Y.h := by
  intro m
  unfold SStg.sm
  simp only [Y.pre_eq]
  refine Alg.DegLE.add (Alg.DegLE.sum _ fun c _ => ?_)
    (Alg.DegLE.add (Alg.DegLE.sum _ fun c _ => ?_) (Alg.DegLE.sum _ fun c _ => ?_))
  · exact (((deg_fix Y.sl x.2.1 c).mul_const ε).mul (deg_foldV _ c)).mono fun _ => hn
  · refine (((Y.deg_pre (deg_fix Y.slS x.2.2 c)).mul (Y.deg_late.const_mul ε)).mul
        (Y.deg_pre (deg_foldV _ c))).mono fun i => ?_
    dsimp only
    split_ifs <;> omega
  · refine ((hQ c).mul (Y.deg_pre (deg_foldV _ c))).mono fun i => ?_
    dsimp only
    split_ifs <;> omega

/-- After all rounds: the claim is the output form at the verifier's new state. -/
theorem stg_end (x : Y.Xi) (ε : E) (γ : HPt Y.vars) (z : Fin 0 → E) (M : Y.Cout.J → E) :
    ∑ c, (SStg.nextAll Y.n Y.k γ (Y.stg0 x ε)).Af z c * M (.inl c) +
        (∑ c, (SStg.nextAll Y.n Y.k γ (Y.stg0 x ε)).As z c * M (.inr (.inl c)) +
          ∑ c, (SStg.nextAll Y.n Y.k γ (Y.stg0 x ε)).Aw z c * M (.inr (.inr c))) =
      ∑ j, Y.slOut
          (((x.2.1, sPt Y.n Y.k γ), ε),
            (((x.2.2, Y.pre (sPt Y.n Y.k γ)), ε * Y.late (sPt Y.n Y.k γ)), sPt Y.n Y.k γ)) j *
        M j := by
  obtain ⟨e1, e2, e3⟩ := SStg.nextAll_eq Y.n Y.k γ (Y.stg0 x ε) z
  rw [e1, e2, e3, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rfl

end SumPar
end Cb
