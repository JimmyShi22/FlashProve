-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadPolicy.lean: tools for the four claims of the acceptance policy in the output
head's sub-proof.

The check of the output head's sub-proof adds four claims on the six hidden numbers of the positions
that have a cost (claimPolicy in OnBytes/Model/Head.lean). The library has four clauses on the same
numbers (sB2, sB3, dB4, dZ in Inst/Model/Head/Trace.lean): two sums over the counted positions, and
two identities at each position. Johnson/Road/HeadPolicyForms.lean names the four forms and says
what they are worth. This file has the parts of that work which speak of no claim: in what sense two
further kinds of table are true, what one of the six numbers is worth when it is read in a table,
and the algebra of the clause on the sum of the looked-up values.

Main definitions: SumAt (a table under weights 0 and 1: a plain sum over the positions), FlatAt (a
long table with the weight 1 on each feature of a block).
Main theorems: sum_rhoC (the counted positions are NB in number); gap_sums, gap_cellsK (one of the
six numbers, read in the table of plain sums and in the table under the weights of a point); ext_dZ
(the extension of the clause on the sum of the looked-up values, in its pieces); flat_blocks (the
cells of one limb of the looked-up values, read block by block).

What is not claimed. Nothing on which claims the routine adds or on what a claim is worth. Nothing
is said about when a world is true, about the weights' origin, or about what a verifier's acceptance
shows. Which weights the name of a table stands for is not shown here. The theorems on a reader
begin "if the routine succeeds": none says that it does. The program does not import this file.
-/
import Johnson.Road.HeadLinesC
import Johnson.Road.HeadLedger

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open OnBytes.Model (Reading World Aff Fork SubM)
open Inst.Model (NormPar)
open HeadSizes (Sizes)

variable {K : Type} [Field K]

/-! ## The number of counted positions -/

/-- Among the first T positions, the counted ones are min (min e (z.T - 1)) T - r in number. -/
theorem sum_rhoC_upto (z : Sizes) (y : Inst.Model.Head.Req) : ∀ T : ℕ,
    ∑ i ∈ range T, ((HeadSizes.rhoC z y i : ℤ) : K) =
      ((min (min y.e (z.T - 1)) T - y.r : ℕ) : K)
  | 0 => by simp
  | T + 1 => by
    rw [Finset.sum_range_succ, sum_rhoC_upto z y T]
    unfold HeadSizes.rhoC
    by_cases hc : y.r ≤ T ∧ T < min y.e (z.T - 1)
    · have e : min (min y.e (z.T - 1)) (T + 1) - y.r = min (min y.e (z.T - 1)) T - y.r + 1 := by
        omega
      rw [if_pos hc, e, Nat.cast_add, Nat.cast_one, Int.cast_one]
    · have e : min (min y.e (z.T - 1)) (T + 1) - y.r = min (min y.e (z.T - 1)) T - y.r := by
        omega
      rw [if_neg hc, e, Int.cast_zero, add_zero]

/-- The counted positions are NB in number. -/
theorem sum_rhoC (z : Sizes) (y : Inst.Model.Head.Req) :
    ∑ i ∈ range z.T, ((HeadSizes.rhoC z y i : ℤ) : K) = ((HeadSizes.NB z y : ℕ) : K) := by
  rw [sum_rhoC_upto z y z.T]
  have e : min (min y.e (z.T - 1)) z.T - y.r = HeadSizes.NB z y := by
    unfold HeadSizes.NB
    omega
  rw [e]

/-! ## True tables -/

section Tables

variable (W : World K)

/-- The short table with the name nm is true of the cells c under weights that are 0 or 1: every
entry that a form can name holds its feature's cells, summed over the first T positions. The weights
are part of c. -/
def SumAt (R : Model.Head.Run) (K3 : ℕ) (nm : String) (T : ℕ) (c : ℕ → ℕ → K) : Prop :=
  ∀ tb, Starts R nm tb → ∀ φ, Valid R tb φ → rdW W R.iU3 K3 (tb + φ) = ∑ i ∈ range T, c φ i

/-- The long table with the name nm is true of the cells c at the point u, with the weight 1 on each
feature of a block: every entry that a form can name holds the cells of its block of 2^ls features,
summed over the features and, under the equality weights of u, over the 2^lt positions. -/
def FlatAt (R : Model.Head.Run) (K3 : ℕ) (nm : String) (ls lt : ℕ) (u : ℕ → K)
    (c : ℕ → ℕ → K) : Prop :=
  ∀ tb, Starts R nm tb → ∀ b, Valid R tb b →
    rdW W R.iU3 K3 (tb + b) = ∑ s ∈ range (2 ^ ls), Blocks.ext lt (fun i => c (b * 2 ^ ls + s) i) u

end Tables

variable {ρ : Reading K} {W : World K}

/-- The name of the table of the matrix hr under the indicator of the positions with a cost. -/
theorem hr_rhoC : "hr@" ++ "rhoC" = "hr@rhoC" := by decide

/-- One of the six numbers of the cost ledger, read in the table of plain sums, on cells. The table
holds the cells hr under the weights c of the positions, and wE is the sum of these weights. -/
theorem gap_sums (hρ : Numerals ρ) {R : Model.Head.Run} {i o n T K3 : ℕ} {wE : E}
    {F G : Fork} {C D : Ctx} {a : Aff} {c : ℕ → K} {hr : ℕ → ℕ → K} (hXL : R.h.XL = 5)
    (hg : Model.ledG.getD i (0, 0) = (o, n)) (hK : colsOf F R.iU3 = K3)
    (hC : SumAt W R K3 "hr@rhoC" T (fun φ j => c j * hr φ j))
    (hw : ρ.val wE = ∑ j ∈ range T, c j)
    (h : Ok (Model.Head.gapAt R "rhoC" i wE) F C a G D) :
    G = F ∧ D = C ∧ a.value ρ W = ∑ j ∈ range T,
      c j * Inst.Model.Ledger.b256 (fun m => 128 + hr m j) (99 + o) n := by
  obtain ⟨e1, e2, tb, hst, hval, hv⟩ := gapAt_value ρ W hρ h
  refine ⟨e1, e2, ?_⟩
  have e99 : Model.ledNR 5 = 99 := rfl
  rw [hr_rhoC] at hst
  rw [hg, hXL, e99] at hval
  rw [hg, hXL, e99, hK] at hv
  dsimp only at hval hv
  have s1 : ∀ l, l < n → rdW W R.iU3 K3 (tb + (99 + o + l)) + 128 * ρ.val wE =
      ∑ j ∈ range T, c j * (128 + hr (99 + o + l) j) := by
    intro l hl
    rw [hC tb hst _ (hval l hl), hw, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => by ring
  have s2 : ∑ l ∈ range n, (256 : K) ^ l *
        (rdW W R.iU3 K3 (tb + (99 + o + l)) + 128 * ρ.val wE) =
      ∑ l ∈ range n, (256 : K) ^ l * ∑ j ∈ range T, c j * (128 + hr (99 + o + l) j) :=
    sum_congr rfl fun l hl => by rw [s1 l (mem_range.mp hl)]
  rw [hv, s2]
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  show ∑ l ∈ range n, (256 : K) ^ l * (c j * (128 + hr (99 + o + l) j)) =
    c j * ∑ l ∈ range n, (256 : K) ^ l * (128 + hr (99 + o + l) j)
  rw [mul_sum]
  exact sum_congr rfl fun l _ => by ring

/-- The same in the table under the weights of the call's point, with the number of columns as a
letter. -/
theorem gap_cellsK (hρ : Numerals ρ) {R : Model.Head.Run} {i o n K3 : ℕ} {wE : E}
    {F G : Fork} {C D : Ctx} {a : Aff} {u c : ℕ → K} {hr : ℕ → ℕ → K} (hXL : R.h.XL = 5)
    (hg : Model.ledG.getD i (0, 0) = (o, n)) (hK : colsOf F R.iU3 = K3)
    (hC : ShortAt W R K3 "hr@phiC" R.h.lt u (fun φ j => c j * hr φ j))
    (hw : ρ.val wE = Blocks.ext R.h.lt c u)
    (h : Ok (Model.Head.gapAt R "phiC" i wE) F C a G D) :
    G = F ∧ D = C ∧ a.value ρ W = Blocks.ext R.h.lt
      (fun j => c j * Inst.Model.Ledger.b256 (fun m => 128 + hr m j) (99 + o) n) u :=
  gap_cells hρ hXL hg (by rw [hK]; exact hC) hw h

/-! ## The sum of the looked-up values -/

/-- The extension of the clause on the sum of the looked-up values, in its pieces. c: the indicator
of the counted positions; S: the hidden number zs; k plus the three limbs h: a looked-up value. -/
theorem ext_dZ (lt : ℕ) (u : ℕ → K) (V : ℕ) (c S : ℕ → K) (h : ℕ → ℕ → ℕ → K) (k m : K) :
    Blocks.ext lt (fun i => c i *
        (S i + ∑ v ∈ range V, (k + ∑ l ∈ range 3, (256 : K) ^ l * h l v i) - m)) u =
      Blocks.ext lt (fun i => c i * S i) u + ((V : K) * k - m) * Blocks.ext lt c u +
        ∑ l ∈ range 3, (256 : K) ^ l * ∑ v ∈ range V, Blocks.ext lt (fun i => c i * h l v i) u := by
  have e : (fun i => c i *
        (S i + ∑ v ∈ range V, (k + ∑ l ∈ range 3, (256 : K) ^ l * h l v i) - m)) = fun i =>
      c i * S i + ((V : K) * k - m) * c i +
        ∑ l ∈ range 3, (256 : K) ^ l * ∑ v ∈ range V, c i * h l v i := by
    funext i
    have a1 : c i * ∑ v ∈ range V, ∑ l ∈ range 3, (256 : K) ^ l * h l v i =
        ∑ l ∈ range 3, (256 : K) ^ l * ∑ v ∈ range V, c i * h l v i := by
      rw [sum_comm, mul_sum]
      refine sum_congr rfl fun l _ => ?_
      rw [mul_sum, mul_sum]
      exact sum_congr rfl fun v _ => by ring
    rw [← a1, sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
    ring
  rw [e, Blocks.ext_add, Blocks.ext_add, Blocks.ext_smul, Blocks.ext_sum]
  congr 1
  exact sum_congr rfl fun l _ => by rw [Blocks.ext_smul, Blocks.ext_sum]

/-- The cells of one limb of the looked-up values, read block by block in a table with the weight 1
on each feature: the sum over the n blocks is the sum over the n 2^ls features. -/
theorem flat_blocks {R : Model.Head.Run} {K3 lt OFF n tb : ℕ} {nm : String} {u : ℕ → K}
    {c : ℕ → ℕ → K} (hZ : FlatAt W R K3 nm R.h.ls lt u c) (hst : Starts R nm tb)
    (hd : 2 ^ R.h.ls ∣ OFF) (hv : ∀ xh, xh < n → Valid R tb (OFF / R.h.S2 + xh)) :
    ∑ xh ∈ range n, rdW W R.iU3 K3 (tb + (OFF / R.h.S2 + xh)) =
      ∑ x ∈ range (n * 2 ^ R.h.ls), Blocks.ext lt (fun i => c (OFF + x) i) u := by
  rw [sum_blocks]
  refine sum_congr rfl fun xh hxh => ?_
  rw [hZ tb hst _ (hv xh (mem_range.mp hxh))]
  refine sum_congr rfl fun s _ => ?_
  have hS : R.h.S2 = 2 ^ R.h.ls := rfl
  have hpos : 0 < 2 ^ R.h.ls := by positivity
  obtain ⟨q, hq⟩ := hd
  have e : (OFF / R.h.S2 + xh) * 2 ^ R.h.ls + s = OFF + (xh * 2 ^ R.h.ls + s) := by
    rw [hS, hq, Nat.mul_div_cancel_left q hpos]
    ring
  rw [e]

#print axioms sum_rhoC
#print axioms gap_sums
#print axioms gap_cellsK
#print axioms ext_dZ
#print axioms flat_blocks

end OnBytes.Road.Hd
