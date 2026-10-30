-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CountsGrTot.lean: the privacy bound of the scheme with proof-of-work bits for one
bound t on all the adversary's queries (`zetaBGTot`, Compile/Batch/SpecTotalG.lean), from bounds on
the scheme's counts and on M.zT, M.zL, M.zO (words of this library: lean/GLOSSARY.md).

  `muOf`, `sqOf`  The two hash terms as formulas in five numbers: a (leaves of all trees), b
                  (Fiat-Shamir queries without further attempts), bG (all attempts), s (searches), r
                  (queries to g: `xReq`, Compile/Batch/Counts.lean).
  `muB_le_of`, `hashSqBG_le_of`, `zetaBGTot_le_of`  Monotone in the counts. (`zetaBGTot_le_of`: also
                                                    in M.zT, M.zL, M.zO)
  `gSearchL_le`, `gSearch_le`  With Ns slots, the searches that can reach attempt k + 1 are at most
                               Ns times the rounds with such bits (`gSearchL_le`: Test, Link;
                               `gSearch_le`: Batch, Ns ≥ 1).

The part that is linear in the adversary's t queries is t · max(a / 2^sMT, a / 2^λ, b / 2^min(sFS,
λ), r / 2^λ): no number of attempts occurs in it; in the part without t the number of all attempts
occurs once, times the number of searches.

Limits: those in the header of Compile/Batch/SpecTotalG.lean. No statement here is a security level.
-/
import Compile.Batch.TotalAtGrind

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP
open scoped ENNReal

/-- a formula meant to bound the probability that one query of the adversary hits a marked query -/
def muOf (p : Params) (lam a b r : ℕ) : ℝ≥0∞ :=
  max ((a : ℝ≥0∞) / 2 ^ p.sMT)
    (max ((a : ℝ≥0∞) / 2 ^ lam) (max ((b : ℝ≥0∞) / 2 ^ (min p.sFS lam)) ((r : ℝ≥0∞) / 2 ^ lam)))

/-- the hash terms that do not depend on the adversary's number of queries, as a formula -/
def sqOf (p : Params) (lam a b bG s r : ℕ) : ℝ≥0∞ :=
  (a : ℝ≥0∞) * (0 + a : ℕ) / 2 ^ p.sMT + (a : ℝ≥0∞) * (0 + a : ℕ) / 2 ^ lam +
    ((b : ℝ≥0∞) * (0 + b : ℕ) / 2 ^ (min p.sFS lam) + (s : ℝ≥0∞) * (bG : ℕ) / 2 ^ (min p.sFS lam)) +
    3 * ((r : ℝ≥0∞) * (0 + r : ℕ) / 2 ^ lam)

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {W : QueryLayout lam L} {p : Params}

theorem muB_le_of {n a b r : ℕ} (ha : xTree W p n ≤ a)
    (hb : xFb (L := L) p n ≤ b) (hr : xReq L n ≤ r) :
    muB W p n ≤ muOf p lam a b r := by
  have a1 : ((xTree W p n : ℕ) : ℝ≥0∞) ≤ (a : ℝ≥0∞) := by exact_mod_cast ha
  have b1 : ((xFb (L := L) p n : ℕ) : ℝ≥0∞) ≤ (b : ℝ≥0∞) := by exact_mod_cast hb
  have r1 : ((xReq L n : ℕ) : ℝ≥0∞) ≤ (r : ℝ≥0∞) := by exact_mod_cast hr
  unfold muB muOf
  exact max_le_max (by gcongr) (max_le_max (by gcongr) (max_le_max (by gcongr) (by gcongr)))

theorem hashSqBG_le_of {n a b bG s r : ℕ} (ha : xTree W p n ≤ a) (hb : xFb (L := L) p n ≤ b)
    (hG : xFbG W p n ≤ bG) (hs : xGr W p n ≤ s) (hr : xReq L n ≤ r) :
    hashSqBG W p n ≤ sqOf p lam a b bG s r := by
  have a1 : ((xTree W p n : ℕ) : ℝ≥0∞) ≤ (a : ℝ≥0∞) := by exact_mod_cast ha
  have a2 : ((0 + xTree W p n : ℕ) : ℝ≥0∞) ≤ ((0 + a : ℕ) : ℝ≥0∞) := by
    exact_mod_cast Nat.add_le_add_left ha 0
  have b1 : ((xFb (L := L) p n : ℕ) : ℝ≥0∞) ≤ (b : ℝ≥0∞) := by exact_mod_cast hb
  have b2 : ((0 + xFb (L := L) p n : ℕ) : ℝ≥0∞) ≤ ((0 + b : ℕ) : ℝ≥0∞) := by
    exact_mod_cast Nat.add_le_add_left hb 0
  have g1 : ((xFbG W p n : ℕ) : ℝ≥0∞) ≤ (bG : ℝ≥0∞) := by exact_mod_cast hG
  have s1 : ((xGr W p n : ℕ) : ℝ≥0∞) ≤ (s : ℝ≥0∞) := by exact_mod_cast hs
  have r1 : ((xReq L n : ℕ) : ℝ≥0∞) ≤ (r : ℝ≥0∞) := by exact_mod_cast hr
  have r2 : ((0 + xReq L n : ℕ) : ℝ≥0∞) ≤ ((0 + r : ℕ) : ℝ≥0∞) := by
    exact_mod_cast Nat.add_le_add_left hr 0
  unfold hashSqBG sqOf
  gcongr

theorem zetaBGTot_le_of {M : LH.Nums} {t n a b bG s r : ℕ} {zT zL zO : ℝ≥0∞} (ha : xTree W p n ≤ a)
    (hb : xFb (L := L) p n ≤ b) (hG : xFbG W p n ≤ bG) (hs : xGr W p n ≤ s) (hr : xReq L n ≤ r)
    (h1 : M.zT ≤ zT) (h2 : M.zL ≤ zL) (h3 : M.zO ≤ zO) :
    zetaBGTot W p M t n ≤
      (p.leaves * binTail n p.leaves p.s1 +
          ((t : ℝ≥0∞) * muOf p lam a b r + sqOf p lam a b bG s r)) +
        (zT + p.leaves * zL + n * (L.maxBatchSize * zO)) := by
  have m := muB_le_of (W := W) (p := p) ha hb hr
  have q := hashSqBG_le_of (W := W) (p := p) ha hb hG hs hr
  unfold zetaBGTot zetaHashBGTot
  gcongr

/-! ## The searches, at most -/

variable {Wn : Type}

/-- the number of rounds with proof-of-work bits -/
def nTests : (s : Shape) → GBits s → ℕ
  | [], _ => 0
  | _ :: s, (b, g) => (if b = 0 then 0 else 1) + nTests s g

theorem gSearchL_le (D : GrData Wn) (k Ns : ℕ) :
    ∀ (s : Shape) (g : GBits s), gSearchL D k Ns s g ≤ Ns * nTests s g
  | [], _ => Nat.zero_le _
  | _ :: s, (0, g) => by
      show 0 + gSearchL D k Ns s g ≤ Ns * (0 + nTests s g)
      rw [Nat.zero_add, Nat.zero_add]
      exact gSearchL_le D k Ns s g
  | _ :: s, (b + 1, g) => by
      show Ns * (if k < D.mo (b + 1) then 1 else 0) + gSearchL D k Ns s g ≤ Ns * (1 + nTests s g)
      rw [Nat.mul_add]
      exact Nat.add_le_add (Nat.mul_le_mul_left _ (by split <;> omega)) (gSearchL_le D k Ns s g)

theorem gSearch_le (D : GrData Wn) (k Ns : ℕ) (hN : 1 ≤ Ns) :
    ∀ (s : Shape) (A : RoundSplits s) (g : GBits s), gSearch D k Ns s A g ≤ Ns * nTests s g
  | [], _, _ => Nat.zero_le _
  | _ :: s, (a, A), (0, g) => by
      have e : gSearch D k Ns (_ :: s) (a, A) (0, g) = 0 + gSearch D k Ns s A g := by
        show (match a.kind, 0 with
          | _, 0 => 0
          | .lo, b + 1 => Ns * (if k < D.mo (b + 1) then 1 else 0)
          | .sh, b + 1 => (if k < D.mo (b + 1) then 1 else 0)) + gSearch D k Ns s A g = _
        cases a.kind <;> rfl
      rw [e]
      show 0 + gSearch D k Ns s A g ≤ Ns * (0 + nTests s g)
      rw [Nat.zero_add, Nat.zero_add]
      exact gSearch_le D k Ns hN s A g
  | _ :: s, (a, A), (b + 1, g) => by
      have e : gSearch D k Ns (_ :: s) (a, A) (b + 1, g) ≤ Ns * 1 + gSearch D k Ns s A g := by
        show (match a.kind, b + 1 with
          | _, 0 => 0
          | .lo, b + 1 => Ns * (if k < D.mo (b + 1) then 1 else 0)
          | .sh, b + 1 => (if k < D.mo (b + 1) then 1 else 0)) + gSearch D k Ns s A g ≤ _
        refine Nat.add_le_add ?_ (le_refl _)
        cases a.kind with
        | lo =>
            show Ns * (if k < D.mo (b + 1) then 1 else 0) ≤ Ns * 1
            exact Nat.mul_le_mul_left _ (by split <;> omega)
        | sh =>
            show (if k < D.mo (b + 1) then 1 else 0) ≤ Ns * 1
            split <;> omega
      refine le_trans e ?_
      show Ns * 1 + gSearch D k Ns s A g ≤ Ns * (1 + nTests s g)
      rw [Nat.mul_add]
      exact Nat.add_le_add (le_refl _) (gSearch_le D k Ns hN s A g)

end Compile.Batch
