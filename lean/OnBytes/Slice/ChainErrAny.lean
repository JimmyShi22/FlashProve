-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ChainErrAny.lean: the error counts of the rounds after the link's fifth, for any
three stages, and when each of them is at most a given share.

OnBytes/Slice/ChainErr.lean writes out the list of these counts at the stages of the small test
configuration, where a fold's repeated round occurs three times and twice. This file has the list
for stages that are variables, so a fold may have any number of rounds. Nothing in it is of one
configuration.


Main definition.
 `chainErr`     the counts in a row: the batching's, the first fold's, the first code switch's, the
                second fold's, the second code switch's, the base case's, at three radii and with
                lists of one member. It is a list over the blocks' shapes joined, `tailShOf` of
                OnBytes/Slice/ChainCloses.lean. `joinErr` of that file, at these six, is this list
                carried to the shape of the list of rounds.
Main theorems.
 `fold_below`   every count of a fold is at most εs as a share of its round's challenge values, if
                these are: the count 1 in the first round; e + 3 in the repeated round; and, where
                the stage has mask variables, 3 (e + 1) + 2 in the repeated round.
 `cs_below`, `base_below`   such a statement for a code switch's two rounds and the base case's.
 `chain_below`  every count of `chainErr` is at most εs as a share of its round's challenge values,
                from eleven inequalities on counts that are written out.

How it is proved: by induction on the number of a fold's rounds and by the rule for two lists in a
row. No list is written out and no number is computed.

What this file does not claim. Nothing on the sizes of the counts: the eleven inequalities are
hypotheses. Nothing on whether the prover has lost with these counts.
-/
import OnBytes.Slice.ChainCloses
import OnBytes.Slice.ChainErr
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run
open scoped ENNReal

/-- A smaller count meets every bound that a larger count of the same round meets. -/
theorem round_mono (d : PQ.RD) (c : ℝ≥0∞) (e e' : ℕ) (h : e ≤ e')
    (H : ((e' * wOf d : ℕ) : ℝ≥0∞) ≤ c) : ((e * wOf d : ℕ) : ℝ≥0∞) ≤ c :=
  _root_.le_trans (Nat.cast_le.2 (Nat.mul_le_mul_right _ h)) H

/-- The k equal rounds of a fold: if every count of the library's is at most M, and M meets the
bound in the written round, then every count of the written rounds meets it. -/
theorem foldT_below (dT : PQ.RD) (εs : ℝ≥0∞) (M : ℕ)
    (H : ((M * wOf dT : ℕ) : ℝ≥0∞) ≤ εs * (Fintype.card (wRound dT).Chal : ℝ≥0∞)) :
    ∀ (k : ℕ) (f : ℕ → ℕ), (∀ i, f i ≤ M) →
      Err.Below (mulErr (PQ.uL (ckP .two) (List.replicate k dT))
        (List.replicate k (sRound GE GE 2)) (wsT dT k) (sErr 2 k f)) εs
  | 0, _, _ => trivial
  | k + 1, f, hf =>
      ⟨round_mono dT _ (f 0) M (hf 0) H, foldT_below dT εs M H k (fun j => f (j + 1))
        fun i => hf (i + 1)⟩

/-- Every count of a fold at the radius e, with lists of one member, is at most εs as a share of its
round's challenge values, if these are: the count 1 in the first round; the count e + 3 in the
repeated round; and, where the stage has mask variables, the count 3 (e + 1) + 2 in the repeated
round. These are the library's counts: 3 (e + 1) + 2 while mask rows are folded too, then e + 3. -/
theorem fold_below (s : Sg) (dE dT : PQ.RD) (e : ℕ) (εs : ℝ≥0∞)
    (hE : ((1 * wOf dE : ℕ) : ℝ≥0∞) ≤ εs * (Fintype.card (wRound dE).Chal : ℝ≥0∞))
    (hT : (((e + 3) * wOf dT : ℕ) : ℝ≥0∞) ≤ εs * (Fintype.card (wRound dT).Chal : ℝ≥0∞))
    (hM : s.h ≠ 0 → (((e + 1 + (e + 1 + (e + 1)) + 2) * wOf dT : ℕ) : ℝ≥0∞) ≤
      εs * (Fintype.card (wRound dT).Chal : ℝ≥0∞)) :
    Err.Below (foldErr s dE dT (fun _ => 1) (fun _ => e + 1) (fun _ => e + 1) (fun _ => e + 1))
      εs := by
  by_cases h0 : s.h = 0
  · exact ⟨hE, foldT_below dT εs _ hT (s.h + s.g) _ fun i => by
      show e + 1 + (if i + 1 ≤ s.h then e + 1 + (e + 1) else 0) + 1 * 2 ≤ _
      rewrite [if_neg (by omega)]
      omega⟩
  · exact ⟨hE, foldT_below dT εs _ (hM h0) (s.h + s.g) _ fun i => by
      show e + 1 + (if i + 1 ≤ s.h then e + 1 + (e + 1) else 0) + 1 * 2 ≤ _
      split_ifs <;> omega⟩

/-- Both counts of a code switch at the radius e, with lists of one member, are at most εs as shares
of their rounds' challenge values, if the second round's count is. The first round's count is 0. -/
theorem cs_below {s s' : Sg} (hf : CsFit s s') (e : ℕ) (dS dC : PQ.RD) (εs : ℝ≥0∞)
    (hC : (((csSw hf).W.err2 e 1 * wOf dC : ℕ) : ℝ≥0∞) ≤
      εs * (Fintype.card (wRound dC).Chal : ℝ≥0∞)) :
    Err.Below (csErr hf e 1 dS dC) εs := by
  have hS : (((csSw hf).W.err1 1 * wOf dS : ℕ) : ℝ≥0∞) ≤
      εs * (Fintype.card (wRound dS).Chal : ℝ≥0∞) := by
    rw [err1_one, Nat.zero_mul, Nat.cast_zero]
    exact zero_le _
  exact ⟨hS, hC, trivial⟩

/-- Both counts of the base case at the radius e, with lists of one member, are at most εs as shares
of their rounds' challenge values, if these are: the count e + 2 in the first round, and in the
second round the count (n - e - 1)^t, with n the number of positions and t the number of draws. -/
theorem base_below (s : Sg) (e : ℕ) (dL dB : PQ.RD) (εs : ℝ≥0∞)
    (hL : (((e + 1 + 1) * wOf dL : ℕ) : ℝ≥0∞) ≤ εs * (Fintype.card (wRound dL).Chal : ℝ≥0∞))
    (hB : (((2 ^ s.C.a - e - 1) ^ s.t * wOf dB : ℕ) : ℝ≥0∞) ≤
      εs * (Fintype.card (wRound dB).Chal : ℝ≥0∞)) :
    Err.Below (baseErr s e (e + 1) 1 dL dB) εs :=
  ⟨hL, hB, trivial⟩

section
variable (S : Sz) (s1 s2 s3 : Sg) (hf12 : CsFit s1 s2) (hf23 : CsFit s2 s3) (eU e2 e3 : ℕ)
  (dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB : PQ.RD)

/-- The blocks' error counts in a row, for any three stages and any rounds. eU, e2, e3: the radii
at the three stages. All lists have one member. -/
def chainErr : Err (tailShOf s1 s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB) :=
  (batErr S 1 dA,
    Err.app (foldErr s1 dE1 dT1 (fun _ => 1) (fun _ => eU + 1) (fun _ => eU + 1)
      (fun _ => eU + 1))
    (Err.app (csErr hf12 eU 1 dS2 dC1)
    (Err.app (foldErr s2 dE2 dT2 (fun _ => 1) (fun _ => e2 + 1) (fun _ => e2 + 1)
      (fun _ => e2 + 1))
    (Err.app (csErr hf23 e2 1 dS3 dC2) (baseErr s3 e3 (e3 + 1) 1 dL dB)))))

/-- Every count of the list is at most εs as a share of its round's challenge values, if each count
that is written out in the hypotheses is. Nothing is asked of the two rounds in which a tree is
sent: their counts are 0. -/
theorem chain_below (εs : ℝ≥0∞)
    (hA : ((1 * (S.nRows - 1) * wOf dA : ℕ) : ℝ≥0∞) ≤ εs * (Fintype.card (wRound dA).Chal : ℝ≥0∞))
    (hE1 : ((1 * wOf dE1 : ℕ) : ℝ≥0∞) ≤ εs * (Fintype.card (wRound dE1).Chal : ℝ≥0∞))
    (hT1 : (((eU + 3) * wOf dT1 : ℕ) : ℝ≥0∞) ≤ εs * (Fintype.card (wRound dT1).Chal : ℝ≥0∞))
    (hM1 : s1.h ≠ 0 → (((eU + 1 + (eU + 1 + (eU + 1)) + 2) * wOf dT1 : ℕ) : ℝ≥0∞) ≤
      εs * (Fintype.card (wRound dT1).Chal : ℝ≥0∞))
    (hC1 : (((csSw hf12).W.err2 eU 1 * wOf dC1 : ℕ) : ℝ≥0∞) ≤
      εs * (Fintype.card (wRound dC1).Chal : ℝ≥0∞))
    (hE2 : ((1 * wOf dE2 : ℕ) : ℝ≥0∞) ≤ εs * (Fintype.card (wRound dE2).Chal : ℝ≥0∞))
    (hT2 : (((e2 + 3) * wOf dT2 : ℕ) : ℝ≥0∞) ≤ εs * (Fintype.card (wRound dT2).Chal : ℝ≥0∞))
    (hM2 : s2.h ≠ 0 → (((e2 + 1 + (e2 + 1 + (e2 + 1)) + 2) * wOf dT2 : ℕ) : ℝ≥0∞) ≤
      εs * (Fintype.card (wRound dT2).Chal : ℝ≥0∞))
    (hC2 : (((csSw hf23).W.err2 e2 1 * wOf dC2 : ℕ) : ℝ≥0∞) ≤
      εs * (Fintype.card (wRound dC2).Chal : ℝ≥0∞))
    (hL : (((e3 + 1 + 1) * wOf dL : ℕ) : ℝ≥0∞) ≤ εs * (Fintype.card (wRound dL).Chal : ℝ≥0∞))
    (hB : (((2 ^ s3.C.a - e3 - 1) ^ s3.t * wOf dB : ℕ) : ℝ≥0∞) ≤
      εs * (Fintype.card (wRound dB).Chal : ℝ≥0∞)) :
    Err.Below (chainErr S s1 s2 s3 hf12 hf23 eU e2 e3 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB)
      εs :=
  ⟨hA, Err.Below.app (fold_below s1 dE1 dT1 eU εs hE1 hT1 hM1)
    (Err.Below.app (cs_below hf12 eU dS2 dC1 εs hC1)
    (Err.Below.app (fold_below s2 dE2 dT2 e2 εs hE2 hT2 hM2)
    (Err.Below.app (cs_below hf23 e2 dS3 dC2 εs hC2) (base_below s3 e3 dL dB εs hL hB))))⟩

end

end OnBytes.Slice

#print axioms OnBytes.Slice.round_mono
#print axioms OnBytes.Slice.foldT_below
#print axioms OnBytes.Slice.fold_below
#print axioms OnBytes.Slice.cs_below
#print axioms OnBytes.Slice.base_below
#print axioms OnBytes.Slice.chain_below
