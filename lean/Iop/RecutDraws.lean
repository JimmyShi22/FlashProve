-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/RecutDraws.lean: challenge samplers carried along a plan of splits and merges.

A challenge sampler (`BS`, Iop/Draw.lean; for a record of protocols `BatchProtocol.Draws`,
Iop/BatchWireDraw.lean) computes a challenge from hash blocks. The plans are those of Iop/Recut.lean
and Iop/BatchRecut.lean.
  `Shape.Draws.recut P ds`: at a split `BS.unit` (no hash block) for the first part, the round's
      sampler for the remainder; at a merge by (J1) of Iop/Join.lean the second round's sampler; by
      (J2) `BS.prod d1 d2`: the hash blocks of the first challenge, then those of the second
  `Shape.Draws.totB_recut_le`: the number of hash blocks of all rounds does not grow
  `Shape.Draws.maxB_recut_le`: the largest number of hash blocks of a round grows at most by the
      factor `P.maxRun` (the largest number of old rounds whose errors are in a new round; it also
      counts merges by (J1), which add no hash block; `recutDrawsPropsB` is stated with
      `(dr.recut ..).K` itself, not with this bound)
  `Shape.Draws.Good.recut`: the bound on the samplers' bias, `Shape.Draws.Good κ₀`, is preserved
      with the same κ₀

Notation: `lam`: the number of bits of a hash block (`BS`, Iop/Draw.lean); `d.b`: the number of
blocks of the sampler d; `dr : L.Draws lam`: the challenge samplers of the three protocols; `dr.K`:
the largest number of hash blocks of a round (Iop/BatchWireDraw.lean); `M : LH.Nums`: all numbers of
the interface (Iop/InteractiveOracleProof.lean); `L.maxBatchSize` (a field of `BatchProtocol`, Iop/Batch.lean): the number of slots;
`Shape.Draws.LeW w m` (Iop/JoinDraws.lean): the first round has at most w * m blocks, the others at
most m.
-/
import Iop.BatchRecutProofs
import Iop.JoinDraws

namespace Iop
open Prob
open scoped ENNReal

variable {lam : ℕ}

/-- The challenge samplers of the new list of rounds. -/
def Shape.Draws.recut : {s : Shape} → (P : XPlan s) → s.Draws lam → P.shape.Draws lam
  | _, .nil => fun _ => ()
  | _, .keep r P => fun (d : BS lam r.Chal × Shape.Draws lam _) => (d.1, Shape.Draws.recut P d.2)
  | _, .cut _ P => fun d => (BS.unit, Shape.Draws.recut P d)
  | _, .msg r1 r2 (s := s) _ P =>
    fun (d : BS lam r1.Chal × BS lam r2.Chal × s.Draws lam) =>
      Shape.Draws.recut P (show Shape.Draws lam (r1.joinMsg r2 :: s) from d.2)
  | _, .chal r1 r2 (s := s) _ P => fun (d : BS lam r1.Chal × BS lam r2.Chal × s.Draws lam) =>
      Shape.Draws.recut P
        (show Shape.Draws lam (r1.joinChal r2 :: s) from (BS.prod d.1 d.2.1, d.2.2))

theorem Shape.Draws.totB_recut_le {s : Shape} (P : XPlan s) :
    ∀ ds : s.Draws lam, Shape.Draws.totB P.shape (ds.recut P) ≤ Shape.Draws.totB s ds := by
  induction P with
  | nil => intro _; exact Nat.le_refl _
  | keep r P ih =>
      rintro ⟨d, ds⟩
      exact Nat.add_le_add_left (ih ds) d.b
  | cut c P ih =>
      rintro ⟨d, ds⟩
      exact (le_of_eq (Nat.zero_add _)).trans (ih (d, ds))
  | msg r1 r2 u P ih =>
      rintro ⟨d1, d2, ds⟩
      exact (ih (d2, ds)).trans (Nat.le_add_left _ _)
  | chal r1 r2 np P ih =>
      rintro ⟨d1, d2, ds⟩
      refine (ih (BS.prod d1 d2, ds)).trans (le_of_eq ?_)
      show d1.b + d2.b + Shape.Draws.totB _ ds = d1.b + (d2.b + Shape.Draws.totB _ ds)
      exact Nat.add_assoc _ _ _

theorem Shape.Draws.maxB_recut_aux {s : Shape} (P : XPlan s) (m : ℕ) :
    ∀ (w : ℕ) (ds : s.Draws lam),
      Shape.Draws.LeW w m ds → Shape.Draws.maxB P.shape (ds.recut P) ≤ P.maxRunFrom w * m := by
  induction P with
  | nil => intro _ _ _; exact Nat.zero_le _
  | keep r P ih =>
      rintro w ⟨d, ds⟩ h
      exact max_le (h.1.trans (Nat.mul_le_mul_right m (le_max_left _ _)))
        ((ih 1 ds (Shape.Draws.leW_one ds h.2)).trans (Nat.mul_le_mul_right m (le_max_right _ _)))
  | cut c P ih =>
      rintro w ⟨d, ds⟩ h
      exact max_le (Nat.zero_le _) (ih w (d, ds) h)
  | msg r1 r2 u P ih =>
      rintro w ⟨d1, d2, ds⟩ h
      refine ih (w + 1) (d2, ds) ⟨?_, (le_max_right _ _).trans h.2⟩
      exact ((le_max_left _ _).trans h.2).trans (Nat.le_mul_of_pos_left m (Nat.succ_pos w))
  | chal r1 r2 np P ih =>
      rintro w ⟨d1, d2, ds⟩ h
      refine ih (w + 1) (BS.prod d1 d2, ds) ⟨?_, (le_max_right _ _).trans h.2⟩
      show d1.b + d2.b ≤ (w + 1) * m
      rw [Nat.succ_mul]
      exact Nat.add_le_add h.1 ((le_max_left _ _).trans h.2)

theorem Shape.Draws.maxB_recut_le {s : Shape} (P : XPlan s) (ds : s.Draws lam) :
    Shape.Draws.maxB P.shape (ds.recut P) ≤ P.maxRun * Shape.Draws.maxB s ds :=
  Shape.Draws.maxB_recut_aux P _ 1 ds (Shape.Draws.leW_one ds (Nat.le_refl _))

theorem Shape.Draws.Good.recut {κ₀ : ℝ≥0∞} {s : Shape} (P : XPlan s) :
    ∀ ds : s.Draws lam, Shape.Draws.Good κ₀ s ds → Shape.Draws.Good κ₀ P.shape (ds.recut P) := by
  induction P with
  | nil => intro _ _; trivial
  | keep r P ih =>
      rintro ⟨d, ds⟩ h
      exact ⟨h.1, ih ds h.2⟩
  | cut c P ih =>
      rintro ⟨d, ds⟩ h
      exact ⟨by rw [show (BS.unit (lam := lam)).b = 0 from rfl, pow_zero]; exact BS.unit_good,
        ih (d, ds) h⟩
  | msg r1 r2 u P ih =>
      rintro ⟨d1, d2, ds⟩ h
      exact ih (d2, ds) h.2
  | chal r1 r2 np P ih =>
      rintro ⟨d1, d2, ds⟩ h
      refine ih (BS.prod d1 d2, ds) ⟨?_, h.2.2⟩
      show (BS.prod d1 d2).Good (κ₀ ^ (d1.b + d2.b))
      rw [pow_add]
      exact BS.prod_good h.1 h.2.1

variable {I X : Type} {L : BatchProtocol I X}

/-- The challenge samplers of the new record of protocols. -/
def BatchProtocol.Draws.recut (dr : L.Draws lam) (XT : XPlan L.offline.shape) (XL : XPlan L.link.shape)
    (XB : XPlan L.onlineBatch.loc.shape) (ZB : AXPlan XB L.onlineBatch.ann) (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB) :
    (L.recut XT XL XB ZB hK).Draws lam :=
  ⟨dr.T.recut XT, dr.Lk.recut XL, dr.B.recut XB⟩

variable {dr : L.Draws lam} (XT : XPlan L.offline.shape) (XL : XPlan L.link.shape)
  (XB : XPlan L.onlineBatch.loc.shape) (ZB : AXPlan XB L.onlineBatch.ann) (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB)

theorem BatchProtocol.Draws.TotLe.recut {n : ℕ} (h : dr.TotLe n) : (dr.recut XT XL XB ZB hK).TotLe n :=
  ⟨(Shape.Draws.totB_recut_le XT dr.T).trans h.1,
    (Shape.Draws.totB_recut_le XL dr.Lk).trans h.2.1,
    (Shape.Draws.totB_recut_le XB dr.B).trans h.2.2⟩

theorem BatchProtocol.Draws.Good.recut {κ₀ : ℝ≥0∞} (h : dr.Good κ₀) : (dr.recut XT XL XB ZB hK).Good κ₀ :=
  ⟨Shape.Draws.Good.recut XT dr.T h.1,
    Shape.Draws.Good.recut XL dr.Lk h.2.1,
    Shape.Draws.Good.recut XB dr.B h.2.2⟩

theorem BatchProtocol.Draws.K_recut_le
    {k : ℕ} (kT : XT.maxRun ≤ k) (kL : XL.maxRun ≤ k) (kB : XB.maxRun ≤ k) :
    (dr.recut XT XL XB ZB hK).K ≤ k * dr.K := by
  have a : ∀ {s : Shape} (P : XPlan s) (ds : s.Draws lam), P.maxRun ≤ k →
      Shape.Draws.maxB s ds ≤ dr.K → Shape.Draws.maxB P.shape (ds.recut P) ≤ k * dr.K :=
    fun P ds hk hd => (Shape.Draws.maxB_recut_le P ds).trans (Nat.mul_le_mul hk hd)
  exact max_le (a XT dr.T kT (le_max_left _ _))
    (max_le (a XL dr.Lk kL ((le_max_left _ _).trans (le_max_right _ _)))
      (a XB dr.B kB ((le_max_right _ _).trans (le_max_right _ _))))

/-- Split and merge, then derive challenges from hash blocks: under the hypotheses below,
`BatchProtocol.Props` (all properties together, Iop/Batch.lean) holds with `M.pullB κ K L.maxBatchSize`
(Iop/BatchPull.lean) for M, at κ = κ₀ ^ (dr.recut ..).K and K = κ₀ ^ n: εs is multiplied by κ; zT,
zL, pT, pL, pO by K; zO by K ^ L.maxBatchSize. -/
theorem recutDrawsPropsB {Ryes Rno : I → X → Prop} {M : LH.Nums} {n : ℕ} {κ₀ : ℝ≥0∞} (h1 : 1 ≤ κ₀)
    (hg : dr.Good κ₀) (hn : dr.TotLe n) (h : (L.recut XT XL XB ZB hK).Props Ryes Rno M) :
    ((L.recut XT XL XB ZB hK).draws (dr.recut XT XL XB ZB hK)).Props
      Ryes Rno (M.pullB (κ₀ ^ (dr.recut XT XL XB ZB hK).K) (κ₀ ^ n) L.maxBatchSize) :=
  drawsPropsB I X (L.recut XT XL XB ZB hK) Ryes Rno M lam n (dr.recut XT XL XB ZB hK) κ₀ h1
    (hg.recut XT XL XB ZB hK) (hn.recut XT XL XB ZB hK) h

end Iop
