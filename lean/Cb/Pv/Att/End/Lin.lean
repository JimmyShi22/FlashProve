-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/End/Lin.lean: the scalars of an attention sub-proof that one claim ties to a table: the
reading forms, and that they are worth the library's rule values.

Definitions, statements and proofs. Most scalars that the prover of an attention sub-proof sends
beside its sumchecks are tied by one claim each: the scalar's hidden value less a sum, over the
pairs, of the weight of the pair's piece times a form that reads a table is 0. The library gives
each such scalar a rule value on the cells (rv in Inst/Model/Att/KeyForms.lean). This file writes
the sums as forms on the late entries (Cb/Pv/Att/End/Tabs.lean) and shows that each, with the late
entries at their meant values, is worth the rule value.

Main names:
  rvF k: the reading form of the named scalar k; the form 0 at the four names that no single claim
    ties to a table (ss M, ss D, zo, acc).
  LinTabs: what the weights of the seven tables are that these forms read.
  LinGood: the names that these forms read are names of late entries.
  rvF_val: under these, rvF k is worth rv D C p t k, for each k that one claim ties to a table.
  hidF, linF, linF_pull: the hidden value of a sent scalar as a form; the claim; its pull-back says
    that the hidden value is the rule value.

Limits: those of Cb/Pv/Att/End/Tabs.lean. One table on the regions' entries serves all four
families of planes (m1, d1, m2, d2): LinTabs asks that its weights are the equality weights of the
last coordinates of each of these families' inner points; that these agree is shown in
Cb/Pv/Att/End/Cl.lean (planes_agree), if the first two calls have the same size.


-/
import Cb.Pv.Att.End.First
import Cb.Pv.Att.Mean.RowSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.End
open TWhole Cb Cb.Sub Finset Blocks
open Inst.Model.AttSeg

variable {E : Type} [Field E] {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂]
  [DecidableEq J₁] [DecidableEq J₂]

variable (cellJ : Raw → J₁) (D : Dim) (C : Calls) (ls lmS : ℕ) (Y : LateLay AttTab J₂)

/-- The sum over the pairs of the weight of the pair's piece in family u times a form. -/
def overPairs (z : ℕ → E) (u : Fam) (f : ℕ → Aff E (J₁ ⊕ J₂)) : Aff E (J₁ ⊕ J₂) :=
  aSum (range D.nb) fun b => aSmul (wp D C z u b) (f b)

omit [DecidableEq J₁] [DecidableEq J₂] in
theorem val_overPairs (z : ℕ → E) (u : Fam) (f : ℕ → Aff E (J₁ ⊕ J₂)) (x : J₁ ⊕ J₂ → E) :
    (overPairs D C z u f).val x = ∑ b ∈ range D.nb, wp D C z u b * (f b).val x := by
  unfold overPairs
  rw [val_aSum]
  exact sum_congr rfl fun b _ => val_aSmul x _ _

/-- The reading form of a named scalar. -/
def rvF (z : ℕ → E) : KSc → Aff E (J₁ ⊕ J₂)
  | .cell u jj => overPairs D C z u fun b =>
      rdCol lmS Y .tA (u.l D) (inn D C z u) (.c u.reg jj b 0)
  | .ms .M => overPairs D C z .m2 fun b => rdRow D Y .tMm (zg D C z) 4 fun k g => .mx k b g 0
  | .ms .D => overPairs D C z .d2 fun b => rdRow D Y .tMd (zgD D C z) 4 fun k g => .mx k b g 0
  | .zc => overPairs D C z .w3 fun b => rdRow D Y .hW (yg D C z) 4 fun k g => .den k b g 0
  | .ib k => overPairs D C z .x3 fun b => rdRow D Y .hX (xg D C z) 1 fun _ g => .ib k b g 0
  | .rh => overPairs D C z .w3 fun b =>
      rdLong D ls Y .tO (yg D C z) (yn D C z) 1 fun _ g => .qh b g 0 0
  | .rh' => overPairs D C z .w3 fun b =>
      rdLong D ls Y .tO (yg D C z) (yn D C z) 1 fun _ g => .qh' b g 0 0
  | .rg => overPairs D C z .f4 fun b =>
      rdLong D ls Y .tO (yg D C z) (yn D C z) 1 fun _ g => .qh b g 0 0
  | .rg' => overPairs D C z .f4 fun b =>
      rdLong D ls Y .tO (yg D C z) (yn D C z) 1 fun _ g => .qh' b g 0 0
  | _ => aConst 0

/-- The four families of planes of the regions' entries. -/
def IsPlane : Fam → Prop
  | .m1 => True
  | .d1 => True
  | .m2 => True
  | .d2 => True
  | _ => False

/-- The named scalars that one claim ties to a table. -/
def LinK : KSc → Prop
  | .cell u jj => IsPlane u ∧ jj < 5
  | .ib k => k < D.lT
  | .ss _ => False
  | .zo => False
  | .acc => False
  | _ => True

/-- What the weights of the tables are that the forms rvF read. -/
structure LinTabs (tb : AttTab → TabW E) (z : ℕ → E) : Prop where
  tA : ∀ u : Fam, IsPlane u → tb .tA = .col (eqN lmS (u.l D - lmS) (inn D C z u))
  tMm : tb .tMm = .row (psiRow D (zP D C z) (zs D C z) (zi' D C z))
  tMd : tb .tMd = .row (eqT D (cat (D.lP + 1) (zID D C z) (zi' D C z)))
  hW : tb .hW = .row (eqT D (yi D C z))
  hX : tb .hX = .row (eqT D (xi D C z))
  tO : tb .tO = .long (eqN ls (D.ln - ls) (yn D C z)) (eqT D (yi D C z))

/-- The names that the forms rvF read are names of late entries. -/
structure LinGood : Prop where
  tA : ∀ (u : Fam) (jj b : ℕ), IsPlane u → jj < 5 → b < D.nb → ∀ hi < 2 ^ (u.l D - lmS),
    Y.good (.tA, (Raw.c u.reg jj b 0).addX (hi * 2 ^ lmS))
  tMm : ∀ b < D.nb, ∀ g < D.nG, ∀ k < 4, Y.good (.tMm, .mx k b g 0)
  tMd : ∀ b < D.nb, ∀ g < D.nG, ∀ k < 4, Y.good (.tMd, .mx k b g 0)
  hW : ∀ b < D.nb, ∀ g < D.nG, ∀ k < 4, Y.good (.hW, .den k b g 0)
  hX : ∀ k < D.lT, ∀ b < D.nb, ∀ g < D.nG, Y.good (.hX, .ib k b g 0)
  tO : ∀ b < D.nb, ∀ g < D.nG, ∀ ch < 2 ^ (D.ln - ls),
    Y.good (.tO, (Raw.qh b g 0 0).addN (ch * 2 ^ ls)) ∧
      Y.good (.tO, (Raw.qh' b g 0 0).addN (ch * 2 ^ ls))

variable (tb : AttTab → TabW E) (p : Pub E) (m : J₁ → E)

/-- The library's extension atY of an array on (g, i, n) is the read of the array at the lookup's
point. -/
theorem rd3_atY' (a : ℕ → ℕ → ℕ → E) :
    rd3 D (yg D C p.z) (eqT D (yi D C p.z)) (yn D C p.z) a = atY D C p a := by
  rw [atY_rd2]
  unfold rd3 rd2 conN
  refine sum_congr rfl fun g _ => sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun n _ => by ring

omit [Fintype J₁] [DecidableEq J₁] in
/-- A read of one limb, from the names' form. -/
theorem rd3_one (vg Ψ vn : ℕ → E) (base : ℕ → Raw) (arr : ℕ → ℕ → ℕ → E)
    (h : ∀ g i x, m (cellJ (((base g).addN x).atPos i)) = arr g i x) :
    (rd3 D vg Ψ vn fun g i x =>
      ∑ k ∈ range 1, 256 ^ k * m (cellJ (((base g).addN x).atPos i))) = rd3 D vg Ψ vn arr := by
  unfold rd3
  exact sum_congr rfl fun g _ => sum_congr rfl fun i _ => sum_congr rfl fun x _ => by
    beta_reduce
    rw [sum_range_one, pow_zero, one_mul, h]

/-- Each reading form is worth the rule value of its scalar. -/
theorem rvF_val (hls : ls ≤ D.ln) (hl : ∀ u : Fam, IsPlane u → lmS ≤ u.l D)
    (hT : LinTabs D C ls lmS tb p.z) (hG : LinGood D ls lmS Y) (k : KSc) (hk : LinK D k) :
    (rvF (J₁ := J₁) D C ls lmS Y p.z k).val (late (lateA cellJ D ls lmS Y tb) m) =
      rv D C p (rdOf cellJ m) k := by
  cases k with
  | ss r => exact hk.elim
  | zo => exact hk.elim
  | acc => exact hk.elim
  | cell u jj =>
    show (overPairs D C p.z u _).val _ = _
    rw [val_overPairs]
    refine sum_congr rfl fun b hb => ?_
    rw [rdCol_val cellJ D ls lmS Y tb m (hl u hk.1) _ (hT.tA u hk.1) _
      (hG.tA u jj b hk.1 hk.2 (mem_range.mp hb))]
    have e : (fun y => m (cellJ ((Raw.c u.reg jj b 0).addX y))) =
        fun x => rdOf cellJ m (.c u.reg jj b x) := by
      funext x
      simp only [Raw.addX, Nat.zero_add]
      rfl
    rw [e]
  | ms r =>
    cases r with
    | M =>
      show (overPairs D C p.z .m2 _).val _ = _
      rw [val_overPairs]
      refine sum_congr rfl fun b hb => ?_
      rw [rdRow_val cellJ D ls lmS Y tb m hT.tMm _ 4 _ (hG.tMm b (mem_range.mp hb))]
      rfl
    | D =>
      show (overPairs D C p.z .d2 _).val _ = _
      rw [val_overPairs]
      refine sum_congr rfl fun b hb => ?_
      rw [rdRow_val cellJ D ls lmS Y tb m hT.tMd _ 4 _ (hG.tMd b (mem_range.mp hb))]
      rfl
  | zc =>
    show (overPairs D C p.z .w3 _).val _ = _
    rw [val_overPairs]
    refine sum_congr rfl fun b hb => ?_
    rw [rdRow_val cellJ D ls lmS Y tb m hT.hW _ 4 _ (hG.hW b (mem_range.mp hb))]
    rfl
  | ib j =>
    show (overPairs D C p.z .x3 _).val _ = _
    rw [val_overPairs]
    refine sum_congr rfl fun b hb => ?_
    rw [rdRow_val cellJ D ls lmS Y tb m hT.hX _ 1 _
      (fun g hg _ _ => hG.hX j hk b (mem_range.mp hb) g hg)]
    congr 1
    unfold rd2
    refine sum_congr rfl fun g _ => sum_congr rfl fun i _ => ?_
    beta_reduce
    rw [sum_range_one, pow_zero, one_mul]
    rfl
  | rh =>
    show (overPairs D C p.z .w3 _).val _ = _
    rw [val_overPairs]
    refine sum_congr rfl fun b hb => ?_
    rw [rdLong_val cellJ D ls lmS Y tb m hls _ _ hT.tO 1 _
      (fun g hg ch hch _ _ => (hG.tO b (mem_range.mp hb) g hg ch hch).1),
      rd3_one cellJ D m _ _ _ (fun g => Raw.qh b g 0 0)
        (fun g i n => rdOf cellJ m (.qh b g i n)) (fun g i x => by
          simp only [Raw.addN, Raw.atPos, Nat.zero_add]
          rfl), rd3_atY']
  | rh' =>
    show (overPairs D C p.z .w3 _).val _ = _
    rw [val_overPairs]
    refine sum_congr rfl fun b hb => ?_
    rw [rdLong_val cellJ D ls lmS Y tb m hls _ _ hT.tO 1 _
      (fun g hg ch hch _ _ => (hG.tO b (mem_range.mp hb) g hg ch hch).2),
      rd3_one cellJ D m _ _ _ (fun g => Raw.qh' b g 0 0)
        (fun g i n => rdOf cellJ m (.qh' b g i n)) (fun g i x => by
          simp only [Raw.addN, Raw.atPos, Nat.zero_add]
          rfl), rd3_atY']
  | rg =>
    show (overPairs D C p.z .f4 _).val _ = _
    rw [val_overPairs]
    refine sum_congr rfl fun b hb => ?_
    rw [rdLong_val cellJ D ls lmS Y tb m hls _ _ hT.tO 1 _
      (fun g hg ch hch _ _ => (hG.tO b (mem_range.mp hb) g hg ch hch).1),
      rd3_one cellJ D m _ _ _ (fun g => Raw.qh b g 0 0)
        (fun g i n => rdOf cellJ m (.qh b g i n)) (fun g i x => by
          simp only [Raw.addN, Raw.atPos, Nat.zero_add]
          rfl), rd3_atY']
  | rg' =>
    show (overPairs D C p.z .f4 _).val _ = _
    rw [val_overPairs]
    refine sum_congr rfl fun b hb => ?_
    rw [rdLong_val cellJ D ls lmS Y tb m hls _ _ hT.tO 1 _
      (fun g hg ch hch _ _ => (hG.tO b (mem_range.mp hb) g hg ch hch).2),
      rd3_one cellJ D m _ _ _ (fun g => Raw.qh' b g 0 0)
        (fun g i n => rdOf cellJ m (.qh' b g i n)) (fun g i x => by
          simp only [Raw.addN, Raw.atPos, Nat.zero_add]
          rfl), rd3_atY']

/-! ### The claim on a sent scalar -/

/-- The hidden value of a sent scalar: what was sent, less the mask entry at place j. -/
def hidF (v : E) (j : J₁) : Aff E (J₁ ⊕ J₂) := aSub (aConst v) (aEnt (.inl j))

theorem val_hidF (al : J₂ → Aff E J₁) (v : E) (j : J₁) :
    (hidF (J₂ := J₂) v j).val (late al m) = v - m j := by
  unfold hidF
  rw [val_aSub, val_aConst, val_aEnt]
  rfl

/-- The claim that the hidden value of a sent scalar is what the form r reads. -/
def linF (v : E) (j : J₁) (r : Aff E (J₁ ⊕ J₂)) : TWhole.Form E (J₁ ⊕ J₂) :=
  (aSub (hidF v j) r).claim

/-- Its pull-back. -/
theorem linF_pull (al : J₂ → Aff E J₁) (v : E) (j : J₁) (r : Aff E (J₁ ⊕ J₂)) :
    (pullF al (linF v j r)).Holds m ↔ v - m j = r.val (late al m) := by
  unfold linF
  rw [claim_pull, val_aSub, val_hidF, sub_eq_zero]

end Cb.Pv.Att.End

#print axioms Cb.Pv.Att.End.rvF_val
#print axioms Cb.Pv.Att.End.linF_pull
