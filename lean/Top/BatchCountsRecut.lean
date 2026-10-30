-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Top/BatchCountsRecut.lean: the counts `CountsB` (Top/BatchBoundsGen.lean) of a record of protocols
after plans split and merge its rounds (`BatchProtocol.recut`, Iop/BatchRecut.lean). Only for plans whose
merges are all by (J2), the merge of two challenges (`XPlan.NoMsg`); (J1) is the merge of two prover
messages (both: Iop/Join.lean). Top/BatchCountsPlans.lean explains the counts and why (J1) is left
out.
  `depths_recutK_le`                   The largest depth of a tree does not grow.
  `XPlan.extra`, `leaves_recutK_le`    The leaves grow at most by the trees of the first parts of
                                       split rounds.
  `AXPlan.extraJ`, `AXPlan.extra0`, `lvJ_recutK_le`, `lv0_recutK_le`:
      the same by components, under `AXPlan.OK`.
  `CountsB.recut`                      Under its hypotheses, among them `AXPlan.OK` for Batch's
                                       annotated plan: rounds and leaves grow by bounds on the
                                       splits and on the trees of the first parts; all else stays.
                                       The bound on the largest error is a new hypothesis: εs' is
                                       any number with `he : εs' ≤ c.e`. That the new record has
                                       the numbers `{ M with εs := εs' }` is `Spec.recutPropsB`
                                       (Iop/BatchRecut.lean), under the hypotheses of its statement,
                                       among them soundness at the bound εs'.

Notation: `CountsB`: what the record of counts (`CountNumsB`) must bound; record of protocols,
`BatchProtocol`: an encoder, a decoder and the protocols Test, Link and Batch (Iop/Batch.lean); `XPlan`: a
plan of splits and merges for a list of rounds (Iop/Recut.lean); `AXPlan`: for each split of the
plan, its annotation; `AXPlan.OK` (Iop/BatchRecut.lean): the annotation of every split satisfies
`ACut.OK` (Iop/BatchSplit.lean); first part: of the two parts into which a split cuts a prover
message (`RCut`, Iop/Split.lean); components: the shared and a slot's component of a prover message
of Batch (`RAnn`, Iop/Batch.lean).

(Terms: lean/GLOSSARY.md.)

The counts are bounds, not sharp: the rounds and padding leaves that the merges remove are not
subtracted, and after a split the remainder is still counted with the tree of the whole round.
-/
import Top.BatchCountsPlans
import Iop.RecutKit
import Iop.BatchRecutProofs

set_option autoImplicit false

namespace Iop
open Blocks

/-- The leaves of the trees of the first parts of split rounds. -/
def XPlan.extra : {s : Shape} → (P : XPlan s) → P.Kits → ℕ
  | _, .nil => fun _ => 0
  | _, .keep _ P => fun K => P.extra K
  | _, .cut c P => fun (K : RKit c.fst × RKit c.snd × P.Kits) => 2 ^ depthR K.1.pt + P.extra K.2.2
  | _, .msg _ _ _ P => fun K => P.extra K
  | _, .chal _ _ _ P => fun K => P.extra K

/-- The leaves of a slot's trees over the first parts of split rounds. -/
def AXPlan.extraJ : {s : Shape} → (P : XPlan s) → P.Kits → (A : RoundSplits s) → AXPlan P A → ℕ
  | _, .nil => fun _ _ _ => 0
  | _, .keep r P => fun K (A : RAnn r × RoundSplits _) Z => AXPlan.extraJ P K A.2 Z
  | _, .cut (r := r) (s := s) c P =>
      fun (K : RKit c.fst × RKit c.snd × P.Kits) (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × AXPlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) =>
      2 ^ Nat.clog 2 (Z.1.ann1.cardJ K.1.pt) +
        AXPlan.extraJ P K.2.2 (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2
  | _, .msg r1 r2 (s := s) _ P =>
    fun K (A : RAnn r1 × RAnn r2 × RoundSplits s) Z =>
      AXPlan.extraJ P K (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2)) Z
  | _, .chal r1 r2 (s := s) _ P =>
    fun K (A : RAnn r1 × RAnn r2 × RoundSplits s) Z =>
      AXPlan.extraJ P K (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2)) Z

/-- The leaves of the shared trees over the first parts of split rounds. -/
def AXPlan.extra0 : {s : Shape} → (P : XPlan s) → P.Kits → (A : RoundSplits s) → AXPlan P A → ℕ
  | _, .nil => fun _ _ _ => 0
  | _, .keep r P => fun K (A : RAnn r × RoundSplits _) Z => AXPlan.extra0 P K A.2 Z
  | _, .cut (r := r) (s := s) c P =>
      fun (K : RKit c.fst × RKit c.snd × P.Kits) (A : RAnn r × RoundSplits s)
          (Z : (b : ACut c A.1) × AXPlan P (show RoundSplits (c.snd :: s) from (b.ann2, A.2))) =>
      2 ^ Nat.clog 2 (Z.1.ann1.card0 K.1.pt) +
        AXPlan.extra0 P K.2.2 (show RoundSplits (c.snd :: s) from (Z.1.ann2, A.2)) Z.2
  | _, .msg r1 r2 (s := s) _ P =>
    fun K (A : RAnn r1 × RAnn r2 × RoundSplits s) Z =>
      AXPlan.extra0 P K (show RoundSplits (r1.joinMsg r2 :: s) from (A.1.joinMsg A.2.1, A.2.2)) Z
  | _, .chal r1 r2 (s := s) _ P =>
    fun K (A : RAnn r1 × RAnn r2 × RoundSplits s) Z =>
      AXPlan.extra0 P K (show RoundSplits (r1.joinChal r2 :: s) from (A.1.joinChal r2, A.2.2)) Z

/-! ### Plans without splits; concatenated plans -/

theorem XPlan.extra_noCut {s : Shape} (P : XPlan s) (h : P.NoCut) :
    P.extra (XPlan.Kits.noCut P h) = 0 := by
  induction P with
  | nil => rfl
  | keep r P ih => exact ih h
  | cut c P ih => exact h.elim
  | msg r1 r2 u P ih => exact ih h
  | chal r1 r2 np P ih => exact ih h

theorem AXPlan.extraJ_noCut {s : Shape} (P : XPlan s) (h : P.NoCut) :
    ∀ A : RoundSplits s, AXPlan.extraJ P (XPlan.Kits.noCut P h) A (AXPlan.noCut P h A) = 0 := by
  induction P with
  | nil => intro _; rfl
  | keep r P ih => exact fun A => ih h A.2
  | cut c P ih => exact h.elim
  | msg r1 r2 u P ih => exact fun A => ih h (A.1.joinMsg A.2.1, A.2.2)
  | chal r1 r2 np P ih => exact fun A => ih h (A.1.joinChal r2, A.2.2)

theorem AXPlan.extra0_noCut {s : Shape} (P : XPlan s) (h : P.NoCut) :
    ∀ A : RoundSplits s, AXPlan.extra0 P (XPlan.Kits.noCut P h) A (AXPlan.noCut P h A) = 0 := by
  induction P with
  | nil => intro _; rfl
  | keep r P ih => exact fun A => ih h A.2
  | cut c P ih => exact h.elim
  | msg r1 r2 u P ih => exact fun A => ih h (A.1.joinMsg A.2.1, A.2.2)
  | chal r1 r2 np P ih => exact fun A => ih h (A.1.joinChal r2, A.2.2)

theorem XPlan.extra_app {s t : Shape} (P : XPlan s) (Q : XPlan t) (y : Q.Kits) :
    ∀ x : P.Kits, (XPlan.app P Q).extra (XPlan.Kits.app P Q x y) = P.extra x + Q.extra y := by
  induction P with
  | nil => intro _; exact (Nat.zero_add _).symm
  | keep r P ih => exact fun x => ih x
  | cut c P ih => exact fun x => (congrArg (2 ^ depthR x.1.pt + ·) (ih x.2.2)).trans (Nat.add_assoc _ _ _).symm
  | msg r1 r2 u P ih => exact fun x => ih x
  | chal r1 r2 np P ih => exact fun x => ih x

theorem AXPlan.extraJ_app {s t : Shape} (P : XPlan s) (Q : XPlan t) (y : Q.Kits)
    (B : RoundSplits t) (W : AXPlan Q B) :
    ∀ (x : P.Kits) (A : RoundSplits s) (Z : AXPlan P A),
      AXPlan.extraJ (XPlan.app P Q) (XPlan.Kits.app P Q x y)
          (RoundSplits.app A B) (AXPlan.app P Q A B Z W) =
        AXPlan.extraJ P x A Z + AXPlan.extraJ Q y B W := by
  induction P with
  | nil => intro _ _ _; exact (Nat.zero_add _).symm
  | keep r P ih => exact fun x A Z => ih x A.2 Z
  | cut c P ih =>
    exact fun x A Z =>
      (congrArg (2 ^ Nat.clog 2 (Z.1.ann1.cardJ x.1.pt) + ·) (ih x.2.2 (Z.1.ann2, A.2) Z.2)).trans
        (Nat.add_assoc _ _ _).symm
  | msg r1 r2 u P ih => exact fun x A Z => ih x (A.1.joinMsg A.2.1, A.2.2) Z
  | chal r1 r2 np P ih => exact fun x A Z => ih x (A.1.joinChal r2, A.2.2) Z

theorem AXPlan.extra0_app {s t : Shape} (P : XPlan s) (Q : XPlan t) (y : Q.Kits)
    (B : RoundSplits t) (W : AXPlan Q B) :
    ∀ (x : P.Kits) (A : RoundSplits s) (Z : AXPlan P A),
      AXPlan.extra0 (XPlan.app P Q) (XPlan.Kits.app P Q x y)
          (RoundSplits.app A B) (AXPlan.app P Q A B Z W) =
        AXPlan.extra0 P x A Z + AXPlan.extra0 Q y B W := by
  induction P with
  | nil => intro _ _ _; exact (Nat.zero_add _).symm
  | keep r P ih => exact fun x A Z => ih x A.2 Z
  | cut c P ih =>
    exact fun x A Z =>
      (congrArg (2 ^ Nat.clog 2 (Z.1.ann1.card0 x.1.pt) + ·) (ih x.2.2 (Z.1.ann2, A.2) Z.2)).trans
        (Nat.add_assoc _ _ _).symm
  | msg r1 r2 u P ih => exact fun x A Z => ih x (A.1.joinMsg A.2.1, A.2.2) Z
  | chal r1 r2 np P ih => exact fun x A Z => ih x (A.1.joinChal r2, A.2.2) Z

end Iop

namespace Top
open Iop Blocks Top.BatchLeaves
open scoped ENNReal

theorem depths_recutK_le {s : Shape} (P : XPlan s) (hP : P.NoMsg) :
    ∀ (K : P.Kits) (pts : s.IsPoint), depths P.shape (pts.recutK P K) ≤ depths s pts := by
  induction P with
  | nil => intro _ _; exact Nat.le_refl _
  | keep r P ih =>
      rintro K ⟨pt, pts⟩
      exact max_le_max (le_refl _) (ih hP K pts)
  | cut c P ih =>
      rintro ⟨K1, K2, K⟩ ⟨pt, pts⟩
      exact max_le ((depthR_fst_le c pt K1.pt).trans (le_max_left _ _))
        ((ih hP K (K2.pt, pts)).trans (max_le_max (depthR_snd_le c pt K2.pt) (le_refl _)))
  | msg r1 r2 u P ih => exact hP.elim
  | @chal r1 r2 s np P ih =>
      rintro K ⟨p1, p2, pts⟩
      exact (ih hP K (p1.joinChal r2, pts)).trans (max_le_max (le_refl _) (le_max_right _ _))

theorem leaves_recutK_le {s : Shape} (P : XPlan s) (hP : P.NoMsg) :
    ∀ (K : P.Kits) (pts : s.IsPoint),
      leaves P.shape (pts.recutK P K) ≤ leaves s pts + P.extra K := by
  induction P with
  | nil => intro _ _; exact Nat.le_refl _
  | keep r P ih =>
      rintro K ⟨pt, pts⟩
      show 2 ^ depthR pt + leaves P.shape (pts.recutK P K) ≤
        2 ^ depthR pt + leaves _ pts + P.extra K
      have := ih hP K pts
      omega
  | @cut r s c P ih =>
      rintro ⟨K1, K2, K⟩ ⟨pt, pts⟩
      have h1 : leaves P.shape (Shape.IsPoint.recutK P K (K2.pt, pts)) ≤
          2 ^ depthR K2.pt + leaves s pts + P.extra K :=
        ih hP K (K2.pt, pts)
      have h2 : 2 ^ depthR K2.pt ≤ 2 ^ depthR pt :=
        Nat.pow_le_pow_right (by decide) (depthR_snd_le c pt K2.pt)
      show 2 ^ depthR K1.pt + leaves P.shape (Shape.IsPoint.recutK P K (K2.pt, pts)) ≤
        2 ^ depthR pt + leaves s pts + (2 ^ depthR K1.pt + P.extra K)
      omega
  | msg r1 r2 u P ih => exact hP.elim
  | @chal r1 r2 s np P ih =>
      rintro K ⟨p1, p2, pts⟩
      have h1 : leaves P.shape (Shape.IsPoint.recutK P K (p1.joinChal r2, pts)) ≤
          2 ^ depthR p1 + leaves s pts + P.extra K :=
        ih hP K (p1.joinChal r2, pts)
      show leaves P.shape (Shape.IsPoint.recutK P K (p1.joinChal r2, pts)) ≤
        2 ^ depthR p1 + (2 ^ depthR p2 + leaves s pts) + P.extra K
      generalize 2 ^ depthR p2 = e2
      omega

theorem lvJ_recutK_le {s : Shape} (P : XPlan s) (hP : P.NoMsg) :
    ∀ (K : P.Kits) (A : RoundSplits s) (Z : AXPlan P A), AXPlan.OK P A Z →
      ∀ pts : s.IsPoint,
        lvJ P.shape (A.recut P Z) (pts.recutK P K) ≤ lvJ s A pts + AXPlan.extraJ P K A Z := by
  induction P with
  | nil => intro _ _ _ _ _; exact Nat.le_refl _
  | keep r P ih =>
      rintro K ⟨a, A⟩ Z hZ ⟨pt, pts⟩
      show 2 ^ Nat.clog 2 (a.cardJ pt) + lvJ P.shape (A.recut P Z) (pts.recutK P K) ≤
        2 ^ Nat.clog 2 (a.cardJ pt) + lvJ _ A pts + AXPlan.extraJ P K A Z
      have := ih hP K A Z hZ pts
      omega
  | @cut r s c P ih =>
      rintro ⟨K1, K2, K⟩ ⟨a, A⟩ ⟨b, Z⟩ hZ ⟨pt, pts⟩
      have h1 : lvJ P.shape (RoundSplits.recut P (b.ann2, A) Z) (Shape.IsPoint.recutK P K (K2.pt, pts)) ≤
          2 ^ Nat.clog 2 (b.ann2.cardJ K2.pt) + lvJ s A pts + AXPlan.extraJ P K (b.ann2, A) Z :=
        ih hP K (b.ann2, A) Z hZ.2 (K2.pt, pts)
      have h2 : 2 ^ Nat.clog 2 (b.ann2.cardJ K2.pt) ≤ 2 ^ Nat.clog 2 (a.cardJ pt) :=
        Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right 2 (cardJ_snd_le hZ.1 pt K2.pt))
      show 2 ^ Nat.clog 2 (b.ann1.cardJ K1.pt) +
          lvJ P.shape (RoundSplits.recut P (b.ann2, A) Z) (Shape.IsPoint.recutK P K (K2.pt, pts)) ≤
        2 ^ Nat.clog 2 (a.cardJ pt) + lvJ s A pts +
          (2 ^ Nat.clog 2 (b.ann1.cardJ K1.pt) + AXPlan.extraJ P K (b.ann2, A) Z)
      omega
  | msg r1 r2 u P ih => exact hP.elim
  | @chal r1 r2 s np P ih =>
      rintro K ⟨a1, a2, A⟩ Z hZ ⟨p1, p2, pts⟩
      have h1 : lvJ P.shape (RoundSplits.recut P (a1.joinChal r2, A) Z)
            (Shape.IsPoint.recutK P K (p1.joinChal r2, pts)) ≤
          2 ^ Nat.clog 2 (a1.cardJ p1) + lvJ s A pts + AXPlan.extraJ P K (a1.joinChal r2, A) Z :=
        ih hP K (a1.joinChal r2, A) Z hZ (p1.joinChal r2, pts)
      show lvJ P.shape (RoundSplits.recut P (a1.joinChal r2, A) Z)
          (Shape.IsPoint.recutK P K (p1.joinChal r2, pts)) ≤
        2 ^ Nat.clog 2 (a1.cardJ p1) + (2 ^ Nat.clog 2 (a2.cardJ p2) + lvJ s A pts) +
          AXPlan.extraJ P K (a1.joinChal r2, A) Z
      generalize 2 ^ Nat.clog 2 (a2.cardJ p2) = e2
      omega

theorem lv0_recutK_le {s : Shape} (P : XPlan s) (hP : P.NoMsg) :
    ∀ (K : P.Kits) (A : RoundSplits s) (Z : AXPlan P A), AXPlan.OK P A Z →
      ∀ pts : s.IsPoint,
        lv0 P.shape (A.recut P Z) (pts.recutK P K) ≤ lv0 s A pts + AXPlan.extra0 P K A Z := by
  induction P with
  | nil => intro _ _ _ _ _; exact Nat.le_refl _
  | keep r P ih =>
      rintro K ⟨a, A⟩ Z hZ ⟨pt, pts⟩
      show 2 ^ Nat.clog 2 (a.card0 pt) + lv0 P.shape (A.recut P Z) (pts.recutK P K) ≤
        2 ^ Nat.clog 2 (a.card0 pt) + lv0 _ A pts + AXPlan.extra0 P K A Z
      have := ih hP K A Z hZ pts
      omega
  | @cut r s c P ih =>
      rintro ⟨K1, K2, K⟩ ⟨a, A⟩ ⟨b, Z⟩ hZ ⟨pt, pts⟩
      have h1 : lv0 P.shape (RoundSplits.recut P (b.ann2, A) Z) (Shape.IsPoint.recutK P K (K2.pt, pts)) ≤
          2 ^ Nat.clog 2 (b.ann2.card0 K2.pt) + lv0 s A pts + AXPlan.extra0 P K (b.ann2, A) Z :=
        ih hP K (b.ann2, A) Z hZ.2 (K2.pt, pts)
      have h2 : 2 ^ Nat.clog 2 (b.ann2.card0 K2.pt) ≤ 2 ^ Nat.clog 2 (a.card0 pt) :=
        Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right 2 (card0_snd_le hZ.1 pt K2.pt))
      show 2 ^ Nat.clog 2 (b.ann1.card0 K1.pt) +
          lv0 P.shape (RoundSplits.recut P (b.ann2, A) Z) (Shape.IsPoint.recutK P K (K2.pt, pts)) ≤
        2 ^ Nat.clog 2 (a.card0 pt) + lv0 s A pts +
          (2 ^ Nat.clog 2 (b.ann1.card0 K1.pt) + AXPlan.extra0 P K (b.ann2, A) Z)
      omega
  | msg r1 r2 u P ih => exact hP.elim
  | @chal r1 r2 s np P ih =>
      rintro K ⟨a1, a2, A⟩ Z hZ ⟨p1, p2, pts⟩
      have h1 : lv0 P.shape (RoundSplits.recut P (a1.joinChal r2, A) Z)
            (Shape.IsPoint.recutK P K (p1.joinChal r2, pts)) ≤
          2 ^ Nat.clog 2 (a1.card0 p1) + lv0 s A pts + AXPlan.extra0 P K (a1.joinChal r2, A) Z :=
        ih hP K (a1.joinChal r2, A) Z hZ (p1.joinChal r2, pts)
      show lv0 P.shape (RoundSplits.recut P (a1.joinChal r2, A) Z)
          (Shape.IsPoint.recutK P K (p1.joinChal r2, pts)) ≤
        2 ^ Nat.clog 2 (a1.card0 p1) + (2 ^ Nat.clog 2 (a2.card0 p2) + lv0 s A pts) +
          AXPlan.extra0 P K (a1.joinChal r2, A) Z
      generalize 2 ^ Nat.clog 2 (a2.card0 p2) = e2
      omega

/-- Under the hypotheses below, the counts after the plans. Among the hypotheses: kT, kL, kB bound
the splits of Test, Link and Batch (`XPlan.cuts`); xT, xL bound the leaves of the trees of the first
parts in Test and Link (`XPlan.extra`); xJ, x0 bound those in Batch, by components
(`AXPlan.extraJ`, `AXPlan.extra0`). -/
theorem CountsB.recut {I X : Type} {L : BatchProtocol I X} {pT : L.offline.shape.IsPoint}
    {pL : L.link.shape.IsPoint} {pB : L.onlineBatch.loc.shape.IsPoint} {ax : L.Aux pT pL pB} {M : LH.Nums}
    {c : CountNumsB} (h : CountsB L pT pL pB ax M c) {XT : XPlan L.offline.shape}
    {XL : XPlan L.link.shape} {XB : XPlan L.onlineBatch.loc.shape} {ZB : AXPlan XB L.onlineBatch.ann}
    (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB) (hZ : AXPlan.OK XB L.onlineBatch.ann ZB) (nT : XT.NoMsg)
    (nL : XL.NoMsg) (nB : XB.NoMsg) (K : L.RecutKits XT XL XB ZB) {kT kL kB xT xL xJ x0 : ℕ}
    (hkT : XT.cuts ≤ kT) (hkL : XL.cuts ≤ kL) (hkB : XB.cuts ≤ kB) (hxT : XT.extra K.T ≤ xT)
    (hxL : XL.extra K.Lk ≤ xL) (hxJ : AXPlan.extraJ XB K.B L.onlineBatch.ann ZB ≤ xJ)
    (hx0 : AXPlan.extra0 XB K.B L.onlineBatch.ann ZB ≤ x0) {εs' : ℝ≥0∞} (he : εs' ≤ c.e) :
    CountsB (L.recut XT XL XB ZB hK) (pT.recutK XT K.T) (pL.recutK XL K.Lk) (pB.recutK XB K.B)
      (ax.recut hK K) { M with εs := εs' }
      { c with
        rT := c.rT + kT, rL := c.rL + kL, rO := c.rO + kB, lT := c.lT + xT, lL := c.lL + xL,
        lJ := c.lJ + xJ, l0 := c.l0 + x0 } where
  N := h.N
  rT := (Nat.le_add_right _ _).trans ((recutLength _ XT).le.trans (Nat.add_le_add h.rT hkT))
  rL := (Nat.le_add_right _ _).trans ((recutLength _ XL).le.trans (Nat.add_le_add h.rL hkL))
  rO := (Nat.le_add_right _ _).trans ((recutLength _ XB).le.trans (Nat.add_le_add h.rO hkB))
  dT := (max_le_max (le_refl _) (depths_recutK_le XT nT K.T pT)).trans h.dT
  dL := (max_le_max (le_refl _) (depths_recutK_le XL nL K.Lk pL)).trans h.dL
  dO := (max_le_max (le_refl _) (depths_recutK_le XB nB K.B pB)).trans h.dO
  dR := h.dR
  lI := h.lI
  lT := (leaves_recutK_le XT nT K.T pT).trans (Nat.add_le_add h.lT hxT)
  lL := (leaves_recutK_le XL nL K.Lk pL).trans (Nat.add_le_add h.lL hxL)
  lJ := (lvJ_recutK_le XB nB K.B L.onlineBatch.ann ZB hZ pB).trans (Nat.add_le_add h.lJ hxJ)
  l0 := (lv0_recutK_le XB nB K.B L.onlineBatch.ann ZB hZ pB).trans (Nat.add_le_add h.l0 hx0)
  e := he
  pT := h.pT
  pL := h.pL
  pO := h.pO
  zT := h.zT
  zL := h.zL
  zO := h.zO

end Top
