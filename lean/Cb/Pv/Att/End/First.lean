-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/End/First.lean: the names of the tables of an attention sub-proof, and the reading forms
of its first four sumchecks with what they are worth.

Definitions, statements and proofs. For the steps s6b, s6d (the scores of a unit below and on the
diagonal), s8 (the denominator times the output) and s11 (the value product below the diagonal) this
file writes the forms through which the claims on the end values read the tables
(Cb/Pv/Att/End/Tabs.lean), and shows that each, with the late entries at their meant values, is
worth the step's map at the sumcheck's point. With stepCl_out (Cb/Pv/Att/End/Step.lean) the ledger
of the step, pulled back, then gives the block's output claims.

Main names:
  AttTab: the names of the tables, but for those of the lookup's own claims.
  rA8, rB8, rA6d, rB6d, rA6b, rB6b, rA11, rB11: the reading forms. ξ: the sumcheck's point.
  rA8_val and so on: what they are worth. Each takes as given what its table's weights are (hT) and
    that the names which it reads are names of late entries (hg).

Limits: those of Cb/Pv/Att/End/Tabs.lean and Cb/Pv/Att/End/Step.lean.


-/
import Cb.Pv.Att.End.Tabs
import Cb.Pv.Att.End.Step
import Cb.Pv.Att.Mean.ReadsTiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.End
open TWhole Cb Cb.Sub Finset Blocks
open Inst.Model.AttSeg

/-- The names of the tables. On the matrix of the regions' entries: tA (at the lookup's point), tVM,
tVD (at the points of the value products). For the unit of the scores below the diagonal: tMm (the
row maxima), tQm (the queries), tKm (the keys); on the diagonal: tMd, tQd, tKd. On single features:
hW, hX (at the lookup's points on tokens), hE, hT, hPi, hR2 (at tokens of sumchecks and draws). On
blocks of features: tO (the remainders' high parts), qO (the outputs), qVM, qVD (the values), qF
(the query of the score at the index), qKx (its key). -/
inductive AttTab
  | tA | tVM | tVD | tMm | tQm | tKm | tMd | tQd | tKd | hW | hX | hE | hT | hPi | hR2 | tO | qO
  | qVM | qVD | qF | qKx
  deriving DecidableEq

variable {E : Type} [Field E] {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂]
  [DecidableEq J₁] [DecidableEq J₂]

variable (cellJ : Raw → J₁) (D : Dim) (C : Calls) (ls lmS : ℕ) (Y : LateLay AttTab J₂)

/-! ### The reading forms. ξ: the sumcheck's point; b: the pair -/

/-- The denominator. -/
def rA8 (ξ : ℕ → E) (b : ℕ) : Aff E (J₁ ⊕ J₂) := rdRow D Y .hE ξ 4 fun k g => .den k b g 0
/-- The output, at the lookup's point on the features. -/
def rB8 (p : Pub E) (ξ : ℕ → E) (b : ℕ) : Aff E (J₁ ⊕ J₂) :=
  rdLong D ls Y .qO ξ (yn D C p.z) 2 fun k g => .out k b g 0 0
/-- The query, on the diagonal. -/
def rA6d (ξ : ℕ → E) (b : ℕ) : Aff E (J₁ ⊕ J₂) :=
  rdLong D ls Y .tQd ξ (sh ξ (D.lg + (D.lP + 1))) 2 fun k g => .qry k b g 0 0
/-- The key, on the diagonal. -/
def rB6d (ξ : ℕ → E) (b : ℕ) : Aff E (J₁ ⊕ J₂) :=
  rdLong D ls Y .tKd ξ (sh ξ (D.lg + (D.lP + 1))) 2 fun k g => .key k (D.lamOf b) g 0 0
/-- The query, below the diagonal. -/
def rA6b (ξ : ℕ → E) (b : ℕ) : Aff E (J₁ ⊕ J₂) :=
  rdLong D ls Y .tQm ξ (sh ξ (D.lg + D.lP + (D.lP + 1))) 2 fun k g => .qry k b g 0 0
/-- The key, below the diagonal. -/
def rB6b (ξ : ℕ → E) (b : ℕ) : Aff E (J₁ ⊕ J₂) :=
  rdLong D ls Y .tKm ξ (sh ξ (D.lg + D.lP + (D.lP + 1))) 2 fun k g => .key k (D.lamOf b) g 0 0
/-- The softmax weight below the diagonal: its low byte, which is stored less 128, and 256 times its
high byte. -/
def rA11 (p : Pub E) (ξ : ℕ → E) (b : ℕ) : Aff E (J₁ ⊕ J₂) :=
  aAdd (aAdd (rdCol lmS Y .tVM D.lM (ptBelow D C p ξ) (.c .M 3 b 0)) (aConst 128))
    (aSmul 256 (rdCol lmS Y .tVM D.lM (ptBelow D C p ξ) (.c .M 4 b 0)))
/-- The drawn element plus the value. -/
def rB11 (p : Pub E) (ξ : ℕ → E) (b : ℕ) : Aff E (J₁ ⊕ J₂) :=
  aAdd (aConst p.th) (rdLong D ls Y .qVM ξ (yn D C p.z) 2 fun k g => .val k (D.lamOf b) g 0 0)

/-! ### What they are worth -/

variable (tb : AttTab → TabW E) (p : Pub E) (ξ : ℕ → E) (m : J₁ → E)

omit [Fintype J₁] [DecidableEq J₁] in
/-- A read of the array that two limbs of a tensor spell, from the names' form. -/
theorem rd3_limbs (vg Ψ vn : ℕ → E) (base : ℕ → ℕ → Raw) (arr : ℕ → ℕ → ℕ → E)
    (h : ∀ g i x, ∑ k ∈ range 2, (256 : E) ^ k * m (cellJ (((base k g).addN x).atPos i)) =
      arr g i x) :
    (rd3 D vg Ψ vn fun g i x =>
      ∑ k ∈ range 2, 256 ^ k * m (cellJ (((base k g).addN x).atPos i))) = rd3 D vg Ψ vn arr := by
  unfold rd3
  exact sum_congr rfl fun g _ => sum_congr rfl fun i _ => sum_congr rfl fun x _ => by
    beta_reduce
    rw [h]

/-- The denominator's form is worth the first map of step s8. -/
theorem rA8_val (hT : tb .hE = .row (eqT D (sh ξ D.lg))) (b : ℕ)
    (hg : ∀ g < D.nG, ∀ k < 4, Y.good (.hE, .den k b g 0)) :
    (rA8 (J₁ := J₁) D Y ξ b).val (late (lateA cellJ D ls lmS Y tb) m) =
      Aext D C p (rdOf cellJ m) .s8 b ξ := by
  unfold rA8
  rw [rdRow_val cellJ D ls lmS Y tb m hT ξ 4 _ hg, aext8]
  rfl

/-- The output's form is worth the second map of step s8. -/
theorem rB8_val (hls : ls ≤ D.ln)
    (hT : tb .qO = .long (eqN ls (D.ln - ls) (yn D C p.z)) (eqT D (sh ξ D.lg))) (b : ℕ)
    (hg : ∀ g < D.nG, ∀ ch < 2 ^ (D.ln - ls), ∀ k < 2,
      Y.good (.qO, (Raw.out k b g 0 0).addN (ch * 2 ^ ls))) :
    (rB8 (J₁ := J₁) D C ls Y p ξ b).val (late (lateA cellJ D ls lmS Y tb) m) =
      Bext D C p (rdOf cellJ m) .s8 b ξ := by
  unfold rB8
  rw [rdLong_val cellJ D ls lmS Y tb m hls ξ _ hT 2 _ hg, bext8]
  exact rd3_limbs cellJ D m _ _ _ _ _ fun g i x => by
    simp only [Raw.addN, Raw.atPos, Nat.zero_add]
    rfl

/-- The query's form is worth the first map of step s6d. -/
theorem rA6d_val (hls : ls ≤ D.ln)
    (hT : tb .tQd = .long (eqN ls (D.ln - ls) (sh ξ (D.lg + (D.lP + 1))))
      (psiDiag D (sh ξ D.lg) (zi' D C p.z))) (b : ℕ)
    (hg : ∀ g < D.nG, ∀ ch < 2 ^ (D.ln - ls), ∀ k < 2,
      Y.good (.tQd, (Raw.qry k b g 0 0).addN (ch * 2 ^ ls))) :
    (rA6d (J₁ := J₁) D ls Y ξ b).val (late (lateA cellJ D ls lmS Y tb) m) =
      Aext D C p (rdOf cellJ m) .s6d b ξ := by
  unfold rA6d
  rw [rdLong_val cellJ D ls lmS Y tb m hls ξ _ hT 2 _ hg, aext6d]
  exact rd3_limbs cellJ D m _ _ _ _ _ fun g i x => by
    simp only [Raw.addN, Raw.atPos, Nat.zero_add]
    rfl

/-- The key's form is worth the second map of step s6d. -/
theorem rB6d_val (hls : ls ≤ D.ln)
    (hT : tb .tKd = .long (eqN ls (D.ln - ls) (sh ξ (D.lg + (D.lP + 1))))
      (psiDiag D (sh ξ D.lg) (zj' D C p.z))) (b : ℕ)
    (hg : ∀ g < D.nG, ∀ ch < 2 ^ (D.ln - ls), ∀ k < 2,
      Y.good (.tKd, (Raw.key k (D.lamOf b) g 0 0).addN (ch * 2 ^ ls))) :
    (rB6d (J₁ := J₁) D ls Y ξ b).val (late (lateA cellJ D ls lmS Y tb) m) =
      Bext D C p (rdOf cellJ m) .s6d b ξ := by
  unfold rB6d
  rw [rdLong_val cellJ D ls lmS Y tb m hls ξ _ hT 2 _ hg, bext6d]
  exact rd3_limbs cellJ D m _ _ _ _ _ fun g i x => by
    simp only [Raw.addN, Raw.atPos, Nat.zero_add]
    rfl

/-- The query's form is worth the first map of step s6b. -/
theorem rA6b_val (hls : ls ≤ D.ln)
    (hT : tb .tQm = .long (eqN ls (D.ln - ls) (sh ξ (D.lg + D.lP + (D.lP + 1))))
      (psiRow D (sh ξ D.lg) (sh ξ (D.lg + D.lP)) (zi' D C p.z))) (b : ℕ)
    (hg : ∀ g < D.nG, ∀ ch < 2 ^ (D.ln - ls), ∀ k < 2,
      Y.good (.tQm, (Raw.qry k b g 0 0).addN (ch * 2 ^ ls))) :
    (rA6b (J₁ := J₁) D ls Y ξ b).val (late (lateA cellJ D ls lmS Y tb) m) =
      Aext D C p (rdOf cellJ m) .s6b b ξ := by
  unfold rA6b
  rw [rdLong_val cellJ D ls lmS Y tb m hls ξ _ hT 2 _ hg, aext6b]
  exact rd3_limbs cellJ D m _ _ _ _ _ fun g i x => by
    simp only [Raw.addN, Raw.atPos, Nat.zero_add]
    rfl

/-- The key's form is worth the second map of step s6b. -/
theorem rB6b_val (hls : ls ≤ D.ln)
    (hT : tb .tKm = .long (eqN ls (D.ln - ls) (sh ξ (D.lg + D.lP + (D.lP + 1))))
      (psiCol D (sh ξ D.lg) (sh ξ (D.lg + D.lP)) (zj' D C p.z))) (b : ℕ)
    (hg : ∀ g < D.nG, ∀ ch < 2 ^ (D.ln - ls), ∀ k < 2,
      Y.good (.tKm, (Raw.key k (D.lamOf b) g 0 0).addN (ch * 2 ^ ls))) :
    (rB6b (J₁ := J₁) D ls Y ξ b).val (late (lateA cellJ D ls lmS Y tb) m) =
      Bext D C p (rdOf cellJ m) .s6b b ξ := by
  unfold rB6b
  rw [rdLong_val cellJ D ls lmS Y tb m hls ξ _ hT 2 _ hg, bext6b]
  exact rd3_limbs cellJ D m _ _ _ _ _ fun g i x => by
    simp only [Raw.addN, Raw.atPos, Nat.zero_add]
    rfl

/-- The softmax weight's form is worth the first map of step s11. -/
theorem rA11_val (hl : lmS ≤ D.lM)
    (hT : tb .tVM = .col (eqN lmS (D.lM - lmS) (ptBelow D C p ξ))) (b : ℕ)
    (hg : ∀ jj < 5, ∀ hi < 2 ^ (D.lM - lmS),
      Y.good (.tVM, (Raw.c .M jj b 0).addX (hi * 2 ^ lmS))) :
    (rA11 (J₁ := J₁) D C lmS Y p ξ b).val (late (lateA cellJ D ls lmS Y tb) m) =
      Aext D C p (rdOf cellJ m) .s11 b ξ := by
  unfold rA11
  rw [val_aAdd, val_aAdd, val_aConst, val_aSmul,
    rdCol_val cellJ D ls lmS Y tb m hl _ hT _ (hg 3 (by norm_num)),
    rdCol_val cellJ D ls lmS Y tb m hl _ hT _ (hg 4 (by norm_num)), aext11]
  have hw : wtV (rdOf cellJ m) .M b = fun y =>
      (m (cellJ ((Raw.c .M 3 b 0).addX y)) + 128) + 256 * m (cellJ ((Raw.c .M 4 b 0).addX y)) := by
    funext y
    simp only [Raw.addX, Nat.zero_add]
    rfl
  rw [hw, Blocks.ext_add, Blocks.ext_add, Blocks.ext_const, Blocks.ext_smul]

/-- The value's form is worth the second map of step s11. -/
theorem rB11_val (hls : ls ≤ D.ln)
    (hT : tb .qVM = .long (eqN ls (D.ln - ls) (yn D C p.z))
      (psiCol D (sh ξ D.lg) (sh ξ (D.lg + D.lP)) (sh ξ (D.lg + D.lP + (D.lP + 1))))) (b : ℕ)
    (hg : ∀ g < D.nG, ∀ ch < 2 ^ (D.ln - ls), ∀ k < 2,
      Y.good (.qVM, (Raw.val k (D.lamOf b) g 0 0).addN (ch * 2 ^ ls))) :
    (rB11 (J₁ := J₁) D C ls Y p ξ b).val (late (lateA cellJ D ls lmS Y tb) m) =
      Bext D C p (rdOf cellJ m) .s11 b ξ := by
  unfold rB11
  rw [val_aAdd, val_aConst, rdLong_val cellJ D ls lmS Y tb m hls ξ _ hT 2 _ hg, bext11]
  congr 1
  exact rd3_limbs cellJ D m _ _ _ _ _ fun g i x => by
    simp only [Raw.addN, Raw.atPos, Nat.zero_add]
    rfl

end Cb.Pv.Att.End

#print axioms Cb.Pv.Att.End.rA8_val
#print axioms Cb.Pv.Att.End.rB8_val
#print axioms Cb.Pv.Att.End.rA6d_val
#print axioms Cb.Pv.Att.End.rB6d_val
#print axioms Cb.Pv.Att.End.rA6b_val
#print axioms Cb.Pv.Att.End.rB6b_val
#print axioms Cb.Pv.Att.End.rA11_val
#print axioms Cb.Pv.Att.End.rB11_val
