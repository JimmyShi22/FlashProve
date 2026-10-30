-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/End/Last.lean: the reading forms of the last four sumchecks of an attention sub-proof,
with what they are worth.

Definitions, statements and proofs. For the value product on the diagonal tiles (step s12), the
score at the index (step s16), the key at the index (step 18) and the bits of the index (step s21
with any number kap of variables that number a bit) this file names the tables that the claims on
the end values read, writes the reading forms (Cb/Pv/Att/End/Tabs.lean), and shows that each, with
every late entry at its meant value, is worth the step's map at the sumcheck's point, or the
library's rule value.

Main names:
  ptOn: the point at which step s12 reads the softmax weights. aext12_on: the first map of step s12
    is the extension of the softmax weights at ptOn.
  rA12, rB12: the softmax weight and the drawn element plus the value. rM6: the row maximum. rA16:
  the query. rKC, rIBP: the key of a layer and a bit of the index, at the point of step 18. rA21:
  the sum over the bits of a position.
  rA12_val, rB12_val, rM6_val, rA16_val, rKC_val, rIBP_val, rA21_val: what they are worth.

Limits: those of Cb/Pv/Att/End/Tabs.lean. No form is written for the second end values of the score
at the index, which no claim ties to a table, nor for the second end values of the bits, whose claim
reads no table.


-/
import Cb.Pv.Att.End.First
import Cb.Pv.Att.Mean.ReadsOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.End
open TWhole Cb Cb.Sub Finset Blocks
open Inst.Model.AttSeg

variable {E : Type} [Field E] {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂]
  [DecidableEq J₁] [DecidableEq J₂]

/-! ### The point of the softmax weights on the diagonal tiles -/

section Point
variable (D : Dim) (C : Calls) (p : Pub E)

/-- The point at which step s12 reads the softmax weights: the step's coordinates of (g | I), the
lookup's coordinates of the row in a tile, the step's coordinates of the column in a tile. -/
def ptOn (ξ : ℕ → E) : ℕ → E :=
  cat (D.lg + (D.lP + 1)) ξ (cat D.lB (yi' D C p.z) (sh ξ (D.lg + (D.lP + 1))))

/-- The first map of step s12 is the extension of the softmax weights over the entries of the region
of the diagonal tiles, at ptOn. -/
theorem aext12_on (t : Raw → E) (b : ℕ) (ξ : ℕ → E) :
    Aext D C p t .s12 b ξ = Blocks.ext D.lD (wtV t .D b) (ptOn D C p ξ) := by
  refine aext12 D C p t b ξ (ptOn D C p ξ) (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_)
  · simp only [ptOn, cat, if_pos hk]
  · have n1 : ¬ D.lg + (D.lP + 1) + k < D.lg + (D.lP + 1) := by omega
    have n2 : D.lg + (D.lP + 1) + k - (D.lg + (D.lP + 1)) = k := by omega
    simp only [ptOn, cat, if_neg n1, n2, if_pos hk]
  · have n1 : ¬ D.lg + (D.lP + 1) + D.lB + k < D.lg + (D.lP + 1) := by omega
    have n2 : D.lg + (D.lP + 1) + D.lB + k - (D.lg + (D.lP + 1)) = D.lB + k := by omega
    have n3 : ¬ D.lB + k < D.lB := by omega
    have n4 : D.lB + k - D.lB = k := by omega
    simp only [ptOn, cat, if_neg n1, n2, if_neg n3, n4]
    rfl

end Point

variable (cellJ : Raw → J₁) (D : Dim) (C : Calls) (ls lmS : ℕ) (Y : LateLay AttTab J₂)

/-! ### The reading forms. ξ: the sumcheck's point; b: the pair -/

/-- The softmax weight on the diagonal tiles: its low byte, which is stored less 128, and 256 times
its high byte. -/
def rA12 (p : Pub E) (ξ : ℕ → E) (b : ℕ) : Aff E (J₁ ⊕ J₂) :=
  aAdd (aAdd (rdCol lmS Y .tVD D.lD (ptOn D C p ξ) (.c .D 3 b 0)) (aConst 128))
    (aSmul 256 (rdCol lmS Y .tVD D.lD (ptOn D C p ξ) (.c .D 4 b 0)))
/-- The drawn element plus the value. -/
def rB12 (p : Pub E) (ξ : ℕ → E) (b : ℕ) : Aff E (J₁ ⊕ J₂) :=
  aAdd (aConst p.th) (rdLong D ls Y .qVD ξ (yn D C p.z) 2 fun k g => .val k (D.lamOf b) g 0 0)
/-- The row maximum, at the drawn point. -/
def rM6 (p : Pub E) (b : ℕ) : Aff E (J₁ ⊕ J₂) := rdRow D Y .hT p.tg 4 fun k g => .mx k b g 0
/-- The query, at the point of the score at the index. -/
def rA16 (ξ : ℕ → E) (b : ℕ) : Aff E (J₁ ⊕ J₂) :=
  rdLong D ls Y .qF (sh ξ D.lT) (sh ξ (D.lT + D.lg)) 2 fun k g => .qry k b g 0 0
/-- The key of layer lam, at the point of the key at the index. -/
def rKC (p : Pub E) (ξ : ℕ → E) (lam : ℕ) : Aff E (J₁ ⊕ J₂) :=
  rdLong D ls Y .qKx (sh ξ D.lT) p.fn 2 fun k g => .key k lam g 0 0
/-- Bit k of the index of pair b, at the point of the key at the index. -/
def rIBP (ξ : ℕ → E) (b k : ℕ) : Aff E (J₁ ⊕ J₂) :=
  rdRow D Y .hPi (sh ξ D.lT) 1 fun _ g => .ib k b g 0
/-- The sum over the bits k of a position of the equality weight of k times bit k of the index, at
the point of the bits. kap: the variables that number a bit. -/
def rA21 (kap : ℕ) (ξ : ℕ → E) (b : ℕ) : Aff E (J₁ ⊕ J₂) :=
  aSum (range D.lT) fun k => aSmul (eqN kap 0 (sh ξ (D.lT + D.lg)) k)
    (rdRow D Y .hR2 (sh ξ D.lT) 1 fun _ g => .ib k b g 0)

/-! ### What they are worth -/

section Val
variable (tb : AttTab → TabW E) (p : Pub E) (ξ : ℕ → E) (m : J₁ → E)

/-- The softmax weight's form is worth the first map of step s12. -/
theorem rA12_val (hl : lmS ≤ D.lD)
    (hT : tb .tVD = .col (eqN lmS (D.lD - lmS) (ptOn D C p ξ))) (b : ℕ)
    (hg : ∀ jj < 5, ∀ hi < 2 ^ (D.lD - lmS),
      Y.good (.tVD, (Raw.c .D jj b 0).addX (hi * 2 ^ lmS))) :
    (rA12 (J₁ := J₁) D C lmS Y p ξ b).val (late (lateA cellJ D ls lmS Y tb) m) =
      Aext D C p (rdOf cellJ m) .s12 b ξ := by
  unfold rA12
  rw [val_aAdd, val_aAdd, val_aConst, val_aSmul,
    rdCol_val cellJ D ls lmS Y tb m hl _ hT _ (hg 3 (by norm_num)),
    rdCol_val cellJ D ls lmS Y tb m hl _ hT _ (hg 4 (by norm_num)), aext12_on]
  have hw : wtV (rdOf cellJ m) .D b = fun y =>
      (m (cellJ ((Raw.c .D 3 b 0).addX y)) + 128) + 256 * m (cellJ ((Raw.c .D 4 b 0).addX y)) := by
    funext y
    simp only [Raw.addX, Nat.zero_add]
    rfl
  rw [hw, Blocks.ext_add, Blocks.ext_add, Blocks.ext_const, Blocks.ext_smul]

/-- The form of the drawn element plus the value is worth the second map of step s12. -/
theorem rB12_val (hls : ls ≤ D.ln)
    (hT : tb .qVD = .long (eqN ls (D.ln - ls) (yn D C p.z)) (eqT D (sh ξ D.lg))) (b : ℕ)
    (hg : ∀ g < D.nG, ∀ ch < 2 ^ (D.ln - ls), ∀ k < 2,
      Y.good (.qVD, (Raw.val k (D.lamOf b) g 0 0).addN (ch * 2 ^ ls))) :
    (rB12 (J₁ := J₁) D C ls Y p ξ b).val (late (lateA cellJ D ls lmS Y tb) m) =
      Bext D C p (rdOf cellJ m) .s12 b ξ := by
  unfold rB12
  rw [val_aAdd, val_aConst, rdLong_val cellJ D ls lmS Y tb m hls ξ _ hT 2 _ hg, bext12]
  congr 1
  exact rd3_limbs cellJ D m _ _ _ _ _ fun g i x => by
    simp only [Raw.addN, Raw.atPos, Nat.zero_add]
    rfl

/-- The row maximum's form is worth the library's rule value. -/
theorem rM6_val (hT : tb .hT = .row (eqT D p.ti)) (b : ℕ)
    (hg : ∀ g < D.nG, ∀ k < 4, Y.good (.hT, .mx k b g 0)) :
    (rM6 (J₁ := J₁) D Y p b).val (late (lateA cellJ D ls lmS Y tb) m) =
      rvM6 D p (rdOf cellJ m) b := by
  unfold rM6
  rw [rdRow_val cellJ D ls lmS Y tb m hT p.tg 4 _ hg]
  rfl

/-- The query's form is worth the first map of step s16. -/
theorem rA16_val (hls : ls ≤ D.ln)
    (hT : tb .qF = .long (eqN ls (D.ln - ls) (sh ξ (D.lT + D.lg))) (eqT D ξ)) (b : ℕ)
    (hg : ∀ g < D.nG, ∀ ch < 2 ^ (D.ln - ls), ∀ k < 2,
      Y.good (.qF, (Raw.qry k b g 0 0).addN (ch * 2 ^ ls))) :
    (rA16 (J₁ := J₁) D ls Y ξ b).val (late (lateA cellJ D ls lmS Y tb) m) =
      Aext D C p (rdOf cellJ m) .s16 b ξ := by
  unfold rA16
  rw [rdLong_val cellJ D ls lmS Y tb m hls _ _ hT 2 _ hg, aext16]
  exact rd3_limbs cellJ D m _ _ _ _ _ fun g i x => by
    simp only [Raw.addN, Raw.atPos, Nat.zero_add]
    rfl

/-- The key's form is worth the library's rule value. -/
theorem rKC_val (hls : ls ≤ D.ln)
    (hT : tb .qKx = .long (eqN ls (D.ln - ls) p.fn) (eqT D ξ)) (lam : ℕ)
    (hg : ∀ g < D.nG, ∀ ch < 2 ^ (D.ln - ls), ∀ k < 2,
      Y.good (.qKx, (Raw.key k lam g 0 0).addN (ch * 2 ^ ls))) :
    (rKC (J₁ := J₁) D ls Y p ξ lam).val (late (lateA cellJ D ls lmS Y tb) m) =
      rvKC D p (rdOf cellJ m) ξ lam := by
  unfold rKC
  rw [rdLong_val cellJ D ls lmS Y tb m hls _ _ hT 2 _ hg]
  unfold rvKC
  exact rd3_limbs cellJ D m _ _ _ _ _ fun g i x => by
    simp only [Raw.addN, Raw.atPos, Nat.zero_add]
    rfl

/-- One limb spells itself. -/
theorem one_limb (f : ℕ → E) : ∑ k ∈ range 1, (256 : E) ^ k * f k = f 0 := by
  rw [sum_range_one, pow_zero, one_mul]

/-- The form of a bit of the index is worth the library's rule value. -/
theorem rIBP_val (hT : tb .hPi = .row (eqT D (sh ξ (D.lT + D.lg)))) (b k : ℕ)
    (hg : ∀ g < D.nG, Y.good (.hPi, .ib k b g 0)) :
    (rIBP (J₁ := J₁) D Y ξ b k).val (late (lateA cellJ D ls lmS Y tb) m) =
      rvIBP D (rdOf cellJ m) ξ b k := by
  unfold rIBP
  rw [rdRow_val cellJ D ls lmS Y tb m hT _ 1 _ fun g hg' _ _ => hg g hg']
  unfold rvIBP
  exact congrArg _ (funext fun g => funext fun i => one_limb _)

/-- The form of the sum over the bits is worth the extension of the first map of the sumcheck for
the bits. -/
theorem rA21_val (kap : ℕ) (hK : D.lT ≤ 2 ^ kap) (hT : tb .hR2 = .row (eqT D ξ)) (b : ℕ)
    (hg : ∀ k < D.lT, ∀ g < D.nG, Y.good (.hR2, .ib k b g 0)) :
    (rA21 (J₁ := J₁) D Y kap ξ b).val (late (lateA cellJ D ls lmS Y tb) m) =
      Blocks.ext (D.lT + D.lg + kap) (bitCube kap D (rdOf cellJ m) b) ξ := by
  unfold rA21
  rw [val_aSum, bitCube_ext D (rdOf cellJ m) kap hK b ξ]
  refine sum_congr rfl fun k hk => ?_
  rw [val_aSmul, rdRow_val cellJ D ls lmS Y tb m hT _ 1 _
    fun g hg' _ _ => hg k (mem_range.mp hk) g hg']
  congr 1
  exact congrArg _ (funext fun g => funext fun i => one_limb _)

end Val

end Cb.Pv.Att.End

#print axioms Cb.Pv.Att.End.rA12_val
#print axioms Cb.Pv.Att.End.rB12_val
#print axioms Cb.Pv.Att.End.rM6_val
#print axioms Cb.Pv.Att.End.rA16_val
#print axioms Cb.Pv.Att.End.rKC_val
#print axioms Cb.Pv.Att.End.rIBP_val
#print axioms Cb.Pv.Att.End.rA21_val
