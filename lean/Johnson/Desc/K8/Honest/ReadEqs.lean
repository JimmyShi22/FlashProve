-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/ReadEqs.lean: THE SMALLNESS TEST: THE VERIFIER's TEST ON THE READS' WEIGHTS
(`readWeightsHeld`, OnBytes/Model/Tail.lean: the column weights that the adding of all the segment's
claims has left on the reads' row of the digits' array are those of a second computation) SAYS YES
BEHIND THE ADDING, WHERE NO PLAIN CLAIM BEARS ON THAT ROW. The first computation's value is another
file's (`Added8.weight`, Johnson/Desc/K8/Honest/Added8.lean; `reads_cut`,
Johnson/Desc/K8/Honest/LinkedFew.lean); the second computation's is
Johnson/Desc/K8/Honest/ReadAgainVal.lean's; both are one sum over the reads; and both sides are
words below the prime, so equal values are equal words. What a yes of the test means is the
library's (`readWeightsHeld_iff`, Johnson/Desc/First/TailClaims/AgainMeans.lean;
`readWeightsHeld_eq`, Johnson/Desc/First/TailClaims/AgainAgrees.lean). None of the library's goals.

  `off_sum`   the plan's first columns are the running sum of the matrices' rows, from `ColsFacts`
                   (Johnson/Desc/K8/Honest/TiesLaidOf.lean)
  `read_mem`   a read of the list lies on a matrix of the list, and its segment begins inside the
                   matrix's rows: from the library's `mem_readsList`
                   (OnBytes/Tie/Pv/Tail/EndLoopsB.lean)
  `val_ite`   · `seg_coef` what a read lays on a column, by its value: the two stretches of its
                   segment
  **`readAgain_val`**   ColsFacts tl · x < 2 * tl.mz ⊢ the value of entry x of the second
                   computation = the sum over readsList tl tl.funs of θ ^ (planClaims + firstAgain
                   NM + q * pow2Again tau) * the value of readCoefE tl y x
  **`Added8.readEqs`**   what a yes of the batching block opens (Added8) · nbW = tl.zzBlocks ·
                   tiesLaid tl · two bounds by 2 ^ 64 (the number of combinations; a third of each
                   matrix's rows) · ColsFacts tl · the reads' row begins at column 0 in the ledger
                   in front · no plain claim bears on the reads' row ⊢ tl'.readWeightsHeld (coefBody
                   tl' g G) ‹the reads' row's weights› = true
Limits. AN IMPLICATION, UNDER EIGHT PREMISES, NONE PAID HERE: `Added8` IS MADE BY ANOTHER FILE UNDER
ITS OWN PREMISES; "NO PLAIN CLAIM BEARS ON THE READS' ROW" (`PlainOff` at each of its 2 mz columns)
HANGS ON OTHER KINDS' CLAIMS; five are on the data in front, on public numbers alone (nbW =
tl.zzBlocks, tiesLaid, the two bounds, ColsFacts); one is on the ledger in front.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.ReadAgainVal
import Johnson.Desc.K8.Honest.TieWords
import Johnson.Desc.K8.Honest.TiesLaidOf
import Johnson.Desc.First.TailClaims.AgainAgrees
import Johnson.Desc.First.TailClaims.AgainMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

local notation "K" => Cb.Gl.E
local notation "val" => Reading.gl.val

/-- The plan's first columns are the running sum of the matrices' rows. -/
theorem off_sum {tl : HTailF2} (C : ColsFacts tl) : ∀ mu : Nat, mu < tl.NM →
    tl.off.getD mu 0 = rowsBefore tl mu
  | 0, _ => C.first
  | mu + 1, h => by
    have h1 := C.next mu (by omega)
    rw [if_pos h, off_sum C mu (by omega)] at h1
    rw [rowsBefore_succ, h1]

/-- A read of the list lies on a matrix of the list; its segment begins inside the rows. -/
theorem read_mem (tl : HTailF2) (funs : Array HFun) (y : HFun × Nat)
    (h : y ∈ readsList tl funs) :
    y.1.mat < tl.NM ∧ y.2 * y.1.len < (tl.mats.getD y.1.mat {}).m := by
  obtain ⟨Fn, sg⟩ := y
  obtain ⟨-, h1, -, hs⟩ := (mem_readsList tl funs Fn sg).1 h
  have hl : 0 < Fn.len := by
    rcases Nat.eq_zero_or_pos Fn.len with e | e
    · rw [e, Nat.div_zero] at hs
      omega
    · exact e
  refine ⟨h1, ?_⟩
  show sg * Fn.len < (tl.mats.getD Fn.mat {}).m
  calc sg * Fn.len < ((tl.mats.getD Fn.mat {}).m / Fn.len) * Fn.len :=
        Nat.mul_lt_mul_of_pos_right hs hl
    _ ≤ (tl.mats.getD Fn.mat {}).m := Nat.div_mul_le_self _ _

theorem val_ite (c : Prop) [Decidable c] (a : E) :
    val (if c then a else zeroE) = if c then val a else 0 := by
  split
  · rfl
  · exact Reading.gl.zero

/-- **What a read lays on a column, by its value.** -/
theorem seg_coef (tl : HTailF2) (y : HFun × Nat) (x : Nat) (h1 : y.1.mat < tl.NM)
    (h2 : y.2 * y.1.len < (tl.mats.getD y.1.mat {}).m) :
    val (readCoefE tl y x) =
      segAt tl.mz (tl.off.getD y.1.mat 0 + y.2 * y.1.len) y.1.len y.1.phi x := by
  have z0 : (tl.zzCol y.1.mat 0 (y.2 * y.1.len)).getD 0 =
      tl.off.getD y.1.mat 0 + y.2 * y.1.len := by
    unfold HTailF2.zzCol
    rw [if_pos (by
      rw [decide_eq_true h1, decide_eq_true (Nat.zero_le 1), decide_eq_true h2]
      rfl)]
    show 0 * tl.mz + tl.off.getD y.1.mat 0 + y.2 * y.1.len = _
    omega
  have z1 : (tl.zzCol y.1.mat 1 (y.2 * y.1.len)).getD 0 =
      tl.mz + (tl.off.getD y.1.mat 0 + y.2 * y.1.len) := by
    unfold HTailF2.zzCol
    rw [if_pos (by
      rw [decide_eq_true h1, decide_eq_true (Nat.le_refl 1), decide_eq_true h2]
      rfl)]
    show 1 * tl.mz + tl.off.getD y.1.mat 0 + y.2 * y.1.len = _
    omega
  have e10 : ((2 ^ t2D0 : Nat) : K) = (2 : K) ^ 10 := by
    norm_num [t2D0]
  unfold readCoefE segAt colAt
  rw [z0, z1, Reading.gl.add, highDigit_val Reading.gl, val_ite, val_ite, e10]

/-- **The value of an entry of the second computation, in the first computation's letters.** -/
theorem readAgain_val {tl : HTailF2} (C : ColsFacts tl) (F : Fork) (x : Nat)
    (hx : x < 2 * tl.mz) :
    val ((tl.readWeightsAgain F).getD x zeroE) =
      sumFrom (fun q y => val F.theta ^
        (F.planClaimsF + tl.firstAgain tl.NM + q * pow2Again tl.tau) * val (readCoefE tl y x)) 0
        (readsList tl tl.funs) := by
  rw [readAgain_sum tl F x hx]
  refine sumFrom_congr _ _ _ _ fun q y hy => ?_
  obtain ⟨h1, h2⟩ := read_mem tl tl.funs y hy
  unfold readLays
  rw [seg_coef tl y x h1 h2, off_sum C _ h1]

section
variable {tl tl' : HTailF2} {funs : Array HFun} {Y G F₁ F₂ : Fork} {fr k8 bk : List Claim}
  {n₀ : Nat}

/-- **THE TEST ON THE READS' WEIGHTS SAYS YES BEHIND THE ADDING.** -/
theorem Added8.readEqs (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) (g : Forest.Heard)
    (nbW : Nat) (hn : nbW = tl.zzBlocks) (hL : tiesLaid tl = true) (hτ : tl.tau ≤ 2 ^ 64)
    (hrows : ∀ nu, nu < tl.NM → ((tl.mats.getD nu {}).m + 2) / 3 ≤ 2 ^ 64) (C : ColsFacts tl)
    (hz : ((Y.trees.getD tl.ix.ZZ {}).rows.getD tl.zzRowReads {}).L0 = 0)
    (hoff : ∀ x, x < 2 * tl.mz → PlainOff fr k8 bk tl.ix.ZZ tl.zzRowReads x) :
    tl'.readWeightsHeld (coefBody tl' g G)
      (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * nbW) {}).L = true := by
  obtain ⟨cθ, cp, -, cok⟩ := A.core
  have bθ : (coefBody tl' g G).theta = Y.theta :=
    (congrArg (·.2.1) (K9L.core_coefBody tl' g G)).trans cθ
  have bp : (coefBody tl' g G).planClaimsF = Y.planClaimsF :=
    (congrArg (·.2.2.2) (K9L.core_coefBody tl' g G)).trans cp
  have eI : tl'.ix = tl.ix :=
    eq_same (·.ix) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  have eM : tl'.mz = tl.mz :=
    eq_same (·.mz) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  have eW : tl'.readWeightsAgain (coefBody tl' g G) = tl.readWeightsAgain (coefBody tl' g G) :=
    eq_same (fun t : HTailF2 => t.readWeightsAgain (coefBody tl' g G)) A.eq (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  have eR : 2 * nbW = tl.zzRowReads := by
    unfold HTailF2.zzRowReads
    rw [hn]
  have eL : (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * nbW) {}).L =
      weightsOf G tl.ix.ZZ tl.zzRowReads := by
    rw [eI, eR]
    exact weights_coefBody tl' g G _ _
  have eF : tl.funs = funs := (eq_funs A.eq).symm
  have e1 : tl.firstAgain tl.NM = firstOf tl tl.NM :=
    firstAgain_eq tl hτ tl.NM fun nu hnu => ⟨hrows nu hnu, (A.mS nu hnu).2⟩
  have h := (readWeightsHeld_iff tl' (coefBody tl' g G)
    (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * nbW) {}).L).2 (by
      rw [eL, eW, eM]
      intro x hx
      refine word_of_val cok (readAgain_ok tl _ x) ?_
      obtain ⟨tl1, hP, -, etl, hv⟩ := A.weight tl.ix.ZZ tl.zzRowReads x hz (hoff x hx)
      rw [hv, reads_cut A.eq etl hP hL x, ← stepTerms_sum, readAgain_val C _ x hx, bθ, bp, eF,
        e1, pow2Again_tau tl hτ, A.th, A.pl])
  rw [readWeightsHeld_eq] at h
  exact h

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.off_sum
#print axioms VerifiableInference.Desc.First.K8.Honest.read_mem
#print axioms VerifiableInference.Desc.First.K8.Honest.val_ite
#print axioms VerifiableInference.Desc.First.K8.Honest.seg_coef
#print axioms VerifiableInference.Desc.First.K8.Honest.readAgain_val
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.readEqs
