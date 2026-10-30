-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Top/BatchCountsRecutMsg.lean: the counts `CountsB` (Top/BatchBoundsGen.lean) of a record of
protocols after plans split and merge its rounds, including merges by (J1), the merge of two prover
messages. For Batch's plan `CountsB.recutM` asks `AXPlan.Kinds` and `AXPlan.OK`. Plans that merge
only by (J2), the merge of two challenges, are in Top/BatchCountsRecut.lean. (Terms:
lean/GLOSSARY.md.)

At a merge by (J1) the oracles of two rounds come under one tree: n1 + n2 positions, padded to a
power of two. That tree can be deeper than both old trees, and can have almost twice as many leaves
as the two together (2^24 positions and 1 position: 2^25 leaves).
  `leaves_recutK_le_two`   The leaves are at most twice the old leaves, plus the trees of the first
                           parts of split rounds, however many rounds are merged into one.
  `CountsB.recutM`         The counts of the new record of protocols. Among the hypotheses is a
                           bound on the largest round error: εs' is any number with
                           `he : εs' ≤ c.e`. That the new record has the numbers
                           `{ M with εs := εs' }` is `Spec.recutPropsB` (Iop/BatchRecut.lean),
                           under the hypotheses of its statement, among them soundness at
                           the bound εs'.
The counts are bounds, not sharp. Where the numbers of positions are known, one can do better round
by round.
-/
import Top.BatchCountsRecut

set_option autoImplicit false

namespace Top
open Iop Blocks Top.BatchLeaves
open scoped ENNReal

/-! ## 1. Numbers of positions -/

/-- The number of positions of a round with `IsPoint`. -/
def nPos {r : Round} (pt : r.IsPoint) : ℕ := @Fintype.card r.Pos pt.finPos

theorem depthR_eq {r : Round} (pt : r.IsPoint) : depthR pt = Nat.clog 2 (nPos pt) := rfl

theorem nPos_joinMsg {r1 r2 : Round} (h1 : r1.IsPoint) (h2 : r2.IsPoint) :
    nPos (h1.joinMsg h2) = nPos h1 + nPos h2 :=
  @Fintype.card_sum _ _ h1.finPos h2.finPos

theorem nPos_fst_le {r : Round} (c : RCut r) (pt : r.IsPoint) (p1 : c.fst.IsPoint) :
    nPos p1 ≤ nPos pt :=
  @Fintype.card_le_of_injective _ _ p1.finPos pt.finPos (fun p : c.PosA => c.pos (.inl p))
    fun _ _ e => Sum.inl.inj (c.pos.injective e)

theorem nPos_snd_le {r : Round} (c : RCut r) (pt : r.IsPoint) (p2 : c.snd.IsPoint) :
    nPos p2 ≤ nPos pt :=
  @Fintype.card_le_of_injective _ _ p2.finPos pt.finPos (fun p : c.PosB => c.pos (.inr p))
    fun _ _ e => Sum.inr.inj (c.pos.injective e)

theorem cardJ_joinMsg {r1 r2 : Round} (a1 : RAnn r1) (a2 : RAnn r2)
    (h1 : r1.IsPoint) (h2 : r2.IsPoint) :
    (a1.joinMsg a2).cardJ (h1.joinMsg h2) = a1.cardJ h1 + a2.cardJ h2 := by
  letI := h1.finPos
  letI := h2.finPos
  exact (Fintype.card_congr
      (Equiv.subtypeSum (p := fun p : r1.Pos ⊕ r2.Pos => (a1.joinMsg a2).own p = true))).trans
    Fintype.card_sum

theorem card0_joinMsg {r1 r2 : Round} (a1 : RAnn r1) (a2 : RAnn r2)
    (h1 : r1.IsPoint) (h2 : r2.IsPoint) :
    (a1.joinMsg a2).card0 (h1.joinMsg h2) = a1.card0 h1 + a2.card0 h2 := by
  letI := h1.finPos
  letI := h2.finPos
  exact (Fintype.card_congr
      (Equiv.subtypeSum (p := fun p : r1.Pos ⊕ r2.Pos => (a1.joinMsg a2).own p = false))).trans
    Fintype.card_sum

/-- A tree over n ≤ v positions, 1 ≤ v, has at most 2 v leaves. -/
theorem two_pow_clog_le {n v : ℕ} (hn : n ≤ v) (hv : 1 ≤ v) : 2 ^ Nat.clog 2 n ≤ 2 * v := by
  rcases Nat.lt_or_ge 1 n with h | h
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by decide) h
    have hc : 0 < Nat.clog 2 n := Nat.clog_pos (by decide) h
    obtain ⟨c, hc'⟩ : ∃ c, Nat.clog 2 n = c + 1 := ⟨Nat.clog 2 n - 1, by omega⟩
    rw [hc'] at h1 ⊢
    rw [Nat.pred_succ] at h1
    rw [Nat.pow_succ]
    omega
  · rw [Nat.clog_of_right_le_one h]
    omega

/-! ## 2. Depths -/

/-- Every round has at most B positions. -/
def PosAll (B : ℕ) : {s : Shape} → s.IsPoint → Prop
  | [], _ => True
  | _ :: _, (pt, pts) => nPos pt ≤ B ∧ PosAll B pts

/-- The first round has at most w B positions, the others at most B. -/
def PosW (w B : ℕ) : {s : Shape} → s.IsPoint → Prop
  | [], _ => True
  | _ :: _, (pt, pts) => nPos pt ≤ w * B ∧ PosAll B pts

theorem PosAll.posW {B : ℕ} : ∀ {s : Shape} {pts : s.IsPoint}, PosAll B pts → PosW 1 B pts
  | [], _, _ => trivial
  | _ :: _, (_, _), h => ⟨by rw [Nat.one_mul]; exact h.1, h.2⟩

theorem posAll_of_depths {D : ℕ} :
    ∀ {s : Shape} {pts : s.IsPoint}, depths s pts ≤ D → PosAll (2 ^ D) pts
  | [], _, _ => trivial
  | _ :: _, (pt, _), h =>
      ⟨(Nat.le_pow_clog (by decide) _).trans
          (Nat.pow_le_pow_right (by decide) ((le_max_left _ _).trans h)),
        posAll_of_depths ((le_max_right _ _).trans h)⟩

theorem depths_of_posAll {B : ℕ} :
    ∀ {s : Shape} {pts : s.IsPoint}, PosAll B pts → depths s pts ≤ Nat.clog 2 B
  | [], _, _ => Nat.zero_le _
  | _ :: _, (_, _), h => max_le (Nat.clog_mono_right 2 h.1) (depths_of_posAll h.2)

theorem le_maxRunFrom {r : Round} {s : Shape} (P : XPlan (r :: s)) : ∀ w, w ≤ P.maxRunFrom w := by
  generalize hs : r :: s = t at P
  induction P generalizing r s with
  | nil => exact absurd hs (List.cons_ne_nil _ _)
  | keep r' P ih => exact fun w => le_max_left _ _
  | cut c P ih => exact fun w => ih rfl w
  | msg r1 r2 u P ih => exact fun w => (Nat.le_succ w).trans (ih rfl (w + 1))
  | chal r1 r2 np P ih => exact fun w => (Nat.le_succ w).trans (ih rfl (w + 1))

theorem posAll_recutK {k B : ℕ} {s : Shape} (P : XPlan s) :
    ∀ (w : ℕ) (K : P.Kits) (pts : s.IsPoint),
      P.maxRunFrom w ≤ k → PosW w B pts → PosAll (k * B) (pts.recutK P K) := by
  induction P with
  | nil => intro _ _ _ _ _; trivial
  | keep r P ih =>
      rintro w K ⟨pt, pts⟩ hm h
      exact ⟨h.1.trans (Nat.mul_le_mul_right B ((le_max_left _ _).trans hm)),
        ih 1 K pts ((le_max_right _ _).trans hm) h.2.posW⟩
  | cut c P ih =>
      rintro w ⟨K1, K2, K⟩ ⟨pt, pts⟩ hm h
      exact ⟨((nPos_fst_le c pt K1.pt).trans h.1).trans
          (Nat.mul_le_mul_right B ((le_maxRunFrom P w).trans hm)),
        ih w K (K2.pt, pts) hm ⟨(nPos_snd_le c pt K2.pt).trans h.1, h.2⟩⟩
  | msg r1 r2 u P ih =>
      rintro w K ⟨p1, p2, pts⟩ hm h
      refine ih (w + 1) K (p1.joinMsg p2, pts) hm ⟨?_, h.2.2⟩
      rw [nPos_joinMsg, Nat.succ_mul]
      exact Nat.add_le_add h.1 h.2.1
  | chal r1 r2 np P ih =>
      rintro w K ⟨p1, p2, pts⟩ hm h
      exact ih (w + 1) K (p1.joinChal r2, pts) hm
        ⟨h.1.trans (Nat.mul_le_mul_right B (Nat.le_succ w)), h.2.2⟩

/-- Old depths at most D, at most k old rounds in a new one: new depths at most D + ⌈log₂ k⌉. -/
theorem depths_recutK_le_run {k D : ℕ} {s : Shape} (P : XPlan s) (K : P.Kits) (pts : s.IsPoint)
    (hm : P.maxRun ≤ k) (h : depths s pts ≤ D) :
    depths P.shape (pts.recutK P K) ≤ D + Nat.clog 2 k := by
  refine (depths_of_posAll (posAll_recutK P 1 K pts hm (posAll_of_depths h).posW)).trans ?_
  refine Nat.clog_le_of_le_pow ?_
  rw [Nat.add_comm, Nat.pow_add]
  exact Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) k)

/-! ## 3. Leaves -/

/-- v in the place of the leaves of the first round's tree, plus the leaves of the trees of the
other rounds; 0 for the empty list. -/
def leavesW (v : ℕ) : {s : Shape} → s.IsPoint → ℕ
  | [], _ => 0
  | _ :: s, (_, pts) => v + leaves s pts

def HeadLe (v : ℕ) : {s : Shape} → s.IsPoint → Prop
  | [], _ => True
  | _ :: _, (pt, _) => nPos pt ≤ v ∧ 1 ≤ v

theorem headLe_self :
    ∀ {s : Shape} (pts : s.IsPoint), ∃ v, HeadLe v pts ∧ leavesW v pts = leaves s pts
  | [], _ => ⟨0, trivial, rfl⟩
  | _ :: _, (pt, _) => ⟨2 ^ depthR pt, ⟨Nat.le_pow_clog (by decide) _, Nat.one_le_two_pow⟩, rfl⟩

theorem leaves_recutK_aux {s : Shape} (P : XPlan s) :
    ∀ (v : ℕ) (K : P.Kits) (pts : s.IsPoint),
      HeadLe v pts → leaves P.shape (pts.recutK P K) ≤ 2 * leavesW v pts + P.extra K := by
  induction P with
  | nil => intro _ _ _ _; exact Nat.zero_le _
  | @keep r s P ih =>
      rintro v K ⟨pt, pts⟩ h
      obtain ⟨v', h', e'⟩ := headLe_self pts
      have h1 := ih v' K pts h'
      rw [e'] at h1
      have h2 : 2 ^ depthR pt ≤ 2 * v := two_pow_clog_le h.1 h.2
      show 2 ^ depthR pt + leaves P.shape (pts.recutK P K) ≤ 2 * (v + leaves s pts) + P.extra K
      omega
  | @cut r s c P ih =>
      rintro v ⟨K1, K2, K⟩ ⟨pt, pts⟩ h
      have h1 : leaves P.shape (Shape.IsPoint.recutK P K (K2.pt, pts)) ≤
          2 * (v + leaves s pts) + P.extra K :=
        ih v K (K2.pt, pts) ⟨(nPos_snd_le c pt K2.pt).trans h.1, h.2⟩
      show 2 ^ depthR K1.pt + leaves P.shape (Shape.IsPoint.recutK P K (K2.pt, pts)) ≤
        2 * (v + leaves s pts) + (2 ^ depthR K1.pt + P.extra K)
      omega
  | @msg r1 r2 s u P ih =>
      rintro v K ⟨p1, p2, pts⟩ h
      have h1 : leaves P.shape (Shape.IsPoint.recutK P K (p1.joinMsg p2, pts)) ≤
          2 * (v + 2 ^ depthR p2 + leaves s pts) + P.extra K :=
        ih (v + 2 ^ depthR p2) K (p1.joinMsg p2, pts)
          ⟨by rw [nPos_joinMsg]; exact Nat.add_le_add h.1 (Nat.le_pow_clog (by decide) _),
            h.2.trans (Nat.le_add_right _ _)⟩
      show leaves P.shape (Shape.IsPoint.recutK P K (p1.joinMsg p2, pts)) ≤
        2 * (v + (2 ^ depthR p2 + leaves s pts)) + P.extra K
      omega
  | @chal r1 r2 s np P ih =>
      rintro v K ⟨p1, p2, pts⟩ h
      have h1 : leaves P.shape (Shape.IsPoint.recutK P K (p1.joinChal r2, pts)) ≤
          2 * (v + leaves s pts) + P.extra K :=
        ih v K (p1.joinChal r2, pts) h
      show leaves P.shape (Shape.IsPoint.recutK P K (p1.joinChal r2, pts)) ≤
        2 * (v + (2 ^ depthR p2 + leaves s pts)) + P.extra K
      generalize 2 ^ depthR p2 = e2
      omega

/-- At most twice the old leaves, and the trees of the first parts. -/
theorem leaves_recutK_le_two {s : Shape} (P : XPlan s) (K : P.Kits) (pts : s.IsPoint) :
    leaves P.shape (pts.recutK P K) ≤ 2 * leaves s pts + P.extra K := by
  obtain ⟨v, h, e⟩ := headLe_self pts
  have := leaves_recutK_aux P v K pts h
  rwa [e] at this

/-! ## 4. Leaves, by components: a slot's trees -/

def lvJW (v : ℕ) : {s : Shape} → RoundSplits s → s.IsPoint → ℕ
  | [], _, _ => 0
  | _ :: s, (_, A), (_, pts) => v + lvJ s A pts

def HeadLeJ (v : ℕ) : {s : Shape} → RoundSplits s → s.IsPoint → Prop
  | [], _, _ => True
  | _ :: _, (a, _), (pt, _) => a.cardJ pt ≤ v ∧ 1 ≤ v

theorem headLeJ_self :
    ∀ {s : Shape} (A : RoundSplits s) (pts : s.IsPoint), ∃ v, HeadLeJ v A pts ∧ lvJW v A pts = lvJ s A pts
  | [], _, _ => ⟨0, trivial, rfl⟩
  | _ :: _, (a, _), (pt, _) =>
    ⟨2 ^ Nat.clog 2 (a.cardJ pt), ⟨Nat.le_pow_clog (by decide) _, Nat.one_le_two_pow⟩, rfl⟩

theorem lvJ_recutK_aux {s : Shape} (P : XPlan s) :
    ∀ (v : ℕ) (K : P.Kits) (A : RoundSplits s) (Z : AXPlan P A), AXPlan.OK P A Z →
      ∀ pts : s.IsPoint, HeadLeJ v A pts →
        lvJ P.shape (A.recut P Z) (pts.recutK P K) ≤ 2 * lvJW v A pts + AXPlan.extraJ P K A Z := by
  induction P with
  | nil => intro _ _ _ _ _ _ _; exact Nat.zero_le _
  | @keep r s P ih =>
      rintro v K ⟨a, A⟩ Z hZ ⟨pt, pts⟩ h
      obtain ⟨v', h', e'⟩ := headLeJ_self A pts
      have h1 := ih v' K A Z hZ pts h'
      rw [e'] at h1
      have h2 : 2 ^ Nat.clog 2 (a.cardJ pt) ≤ 2 * v := two_pow_clog_le h.1 h.2
      show 2 ^ Nat.clog 2 (a.cardJ pt) + lvJ P.shape (A.recut P Z) (pts.recutK P K) ≤
        2 * (v + lvJ s A pts) + AXPlan.extraJ P K A Z
      omega
  | @cut r s c P ih =>
      rintro v ⟨K1, K2, K⟩ ⟨a, A⟩ ⟨b, Z⟩ hZ ⟨pt, pts⟩ h
      have h1 : lvJ P.shape (RoundSplits.recut P (b.ann2, A) Z) (Shape.IsPoint.recutK P K (K2.pt, pts)) ≤
          2 * (v + lvJ s A pts) + AXPlan.extraJ P K (b.ann2, A) Z :=
        ih v K (b.ann2, A) Z hZ.2 (K2.pt, pts) ⟨(cardJ_snd_le hZ.1 pt K2.pt).trans h.1, h.2⟩
      show 2 ^ Nat.clog 2 (b.ann1.cardJ K1.pt) +
          lvJ P.shape (RoundSplits.recut P (b.ann2, A) Z) (Shape.IsPoint.recutK P K (K2.pt, pts)) ≤
        2 * (v + lvJ s A pts) +
          (2 ^ Nat.clog 2 (b.ann1.cardJ K1.pt) + AXPlan.extraJ P K (b.ann2, A) Z)
      omega
  | @msg r1 r2 s u P ih =>
      rintro v K ⟨a1, a2, A⟩ Z hZ ⟨p1, p2, pts⟩ h
      have h1 : lvJ P.shape (RoundSplits.recut P (a1.joinMsg a2, A) Z)
            (Shape.IsPoint.recutK P K (p1.joinMsg p2, pts)) ≤
          2 * (v + 2 ^ Nat.clog 2 (a2.cardJ p2) + lvJ s A pts) +
            AXPlan.extraJ P K (a1.joinMsg a2, A) Z :=
        ih (v + 2 ^ Nat.clog 2 (a2.cardJ p2)) K (a1.joinMsg a2, A) Z hZ (p1.joinMsg p2, pts)
          ⟨by rw [cardJ_joinMsg]; exact Nat.add_le_add h.1 (Nat.le_pow_clog (by decide) _),
            h.2.trans (Nat.le_add_right _ _)⟩
      show lvJ P.shape (RoundSplits.recut P (a1.joinMsg a2, A) Z)
          (Shape.IsPoint.recutK P K (p1.joinMsg p2, pts)) ≤
        2 * (v + (2 ^ Nat.clog 2 (a2.cardJ p2) + lvJ s A pts)) +
          AXPlan.extraJ P K (a1.joinMsg a2, A) Z
      omega
  | @chal r1 r2 s np P ih =>
      rintro v K ⟨a1, a2, A⟩ Z hZ ⟨p1, p2, pts⟩ h
      have h1 : lvJ P.shape (RoundSplits.recut P (a1.joinChal r2, A) Z)
            (Shape.IsPoint.recutK P K (p1.joinChal r2, pts)) ≤
          2 * (v + lvJ s A pts) + AXPlan.extraJ P K (a1.joinChal r2, A) Z :=
        ih v K (a1.joinChal r2, A) Z hZ (p1.joinChal r2, pts) h
      show lvJ P.shape (RoundSplits.recut P (a1.joinChal r2, A) Z)
          (Shape.IsPoint.recutK P K (p1.joinChal r2, pts)) ≤
        2 * (v + (2 ^ Nat.clog 2 (a2.cardJ p2) + lvJ s A pts)) +
          AXPlan.extraJ P K (a1.joinChal r2, A) Z
      generalize 2 ^ Nat.clog 2 (a2.cardJ p2) = e2
      omega

theorem lvJ_recutK_le_two {s : Shape} (P : XPlan s) (K : P.Kits) (A : RoundSplits s) (Z : AXPlan P A)
    (hZ : AXPlan.OK P A Z) (pts : s.IsPoint) :
    lvJ P.shape (A.recut P Z) (pts.recutK P K) ≤ 2 * lvJ s A pts + AXPlan.extraJ P K A Z := by
  obtain ⟨v, h, e⟩ := headLeJ_self A pts
  have := lvJ_recutK_aux P v K A Z hZ pts h
  rwa [e] at this

/-! ## 5. Leaves, by components: the shared trees -/

def lv0W (v : ℕ) : {s : Shape} → RoundSplits s → s.IsPoint → ℕ
  | [], _, _ => 0
  | _ :: s, (_, A), (_, pts) => v + lv0 s A pts

def HeadLe0 (v : ℕ) : {s : Shape} → RoundSplits s → s.IsPoint → Prop
  | [], _, _ => True
  | _ :: _, (a, _), (pt, _) => a.card0 pt ≤ v ∧ 1 ≤ v

theorem headLe0_self :
    ∀ {s : Shape} (A : RoundSplits s) (pts : s.IsPoint), ∃ v, HeadLe0 v A pts ∧ lv0W v A pts = lv0 s A pts
  | [], _, _ => ⟨0, trivial, rfl⟩
  | _ :: _, (a, _), (pt, _) =>
    ⟨2 ^ Nat.clog 2 (a.card0 pt), ⟨Nat.le_pow_clog (by decide) _, Nat.one_le_two_pow⟩, rfl⟩

theorem lv0_recutK_aux {s : Shape} (P : XPlan s) :
    ∀ (v : ℕ) (K : P.Kits) (A : RoundSplits s) (Z : AXPlan P A), AXPlan.OK P A Z →
      ∀ pts : s.IsPoint, HeadLe0 v A pts →
        lv0 P.shape (A.recut P Z) (pts.recutK P K) ≤ 2 * lv0W v A pts + AXPlan.extra0 P K A Z := by
  induction P with
  | nil => intro _ _ _ _ _ _ _; exact Nat.zero_le _
  | @keep r s P ih =>
      rintro v K ⟨a, A⟩ Z hZ ⟨pt, pts⟩ h
      obtain ⟨v', h', e'⟩ := headLe0_self A pts
      have h1 := ih v' K A Z hZ pts h'
      rw [e'] at h1
      have h2 : 2 ^ Nat.clog 2 (a.card0 pt) ≤ 2 * v := two_pow_clog_le h.1 h.2
      show 2 ^ Nat.clog 2 (a.card0 pt) + lv0 P.shape (A.recut P Z) (pts.recutK P K) ≤
        2 * (v + lv0 s A pts) + AXPlan.extra0 P K A Z
      omega
  | @cut r s c P ih =>
      rintro v ⟨K1, K2, K⟩ ⟨a, A⟩ ⟨b, Z⟩ hZ ⟨pt, pts⟩ h
      have h1 : lv0 P.shape (RoundSplits.recut P (b.ann2, A) Z) (Shape.IsPoint.recutK P K (K2.pt, pts)) ≤
          2 * (v + lv0 s A pts) + AXPlan.extra0 P K (b.ann2, A) Z :=
        ih v K (b.ann2, A) Z hZ.2 (K2.pt, pts) ⟨(card0_snd_le hZ.1 pt K2.pt).trans h.1, h.2⟩
      show 2 ^ Nat.clog 2 (b.ann1.card0 K1.pt) +
          lv0 P.shape (RoundSplits.recut P (b.ann2, A) Z) (Shape.IsPoint.recutK P K (K2.pt, pts)) ≤
        2 * (v + lv0 s A pts) +
          (2 ^ Nat.clog 2 (b.ann1.card0 K1.pt) + AXPlan.extra0 P K (b.ann2, A) Z)
      omega
  | @msg r1 r2 s u P ih =>
      rintro v K ⟨a1, a2, A⟩ Z hZ ⟨p1, p2, pts⟩ h
      have h1 : lv0 P.shape (RoundSplits.recut P (a1.joinMsg a2, A) Z)
            (Shape.IsPoint.recutK P K (p1.joinMsg p2, pts)) ≤
          2 * (v + 2 ^ Nat.clog 2 (a2.card0 p2) + lv0 s A pts) +
            AXPlan.extra0 P K (a1.joinMsg a2, A) Z :=
        ih (v + 2 ^ Nat.clog 2 (a2.card0 p2)) K (a1.joinMsg a2, A) Z hZ (p1.joinMsg p2, pts)
          ⟨by rw [card0_joinMsg]; exact Nat.add_le_add h.1 (Nat.le_pow_clog (by decide) _),
            h.2.trans (Nat.le_add_right _ _)⟩
      show lv0 P.shape (RoundSplits.recut P (a1.joinMsg a2, A) Z)
          (Shape.IsPoint.recutK P K (p1.joinMsg p2, pts)) ≤
        2 * (v + (2 ^ Nat.clog 2 (a2.card0 p2) + lv0 s A pts)) +
          AXPlan.extra0 P K (a1.joinMsg a2, A) Z
      omega
  | @chal r1 r2 s np P ih =>
      rintro v K ⟨a1, a2, A⟩ Z hZ ⟨p1, p2, pts⟩ h
      have h1 : lv0 P.shape (RoundSplits.recut P (a1.joinChal r2, A) Z)
            (Shape.IsPoint.recutK P K (p1.joinChal r2, pts)) ≤
          2 * (v + lv0 s A pts) + AXPlan.extra0 P K (a1.joinChal r2, A) Z :=
        ih v K (a1.joinChal r2, A) Z hZ (p1.joinChal r2, pts) h
      show lv0 P.shape (RoundSplits.recut P (a1.joinChal r2, A) Z)
          (Shape.IsPoint.recutK P K (p1.joinChal r2, pts)) ≤
        2 * (v + (2 ^ Nat.clog 2 (a2.card0 p2) + lv0 s A pts)) +
          AXPlan.extra0 P K (a1.joinChal r2, A) Z
      generalize 2 ^ Nat.clog 2 (a2.card0 p2) = e2
      omega

theorem lv0_recutK_le_two {s : Shape} (P : XPlan s) (K : P.Kits) (A : RoundSplits s) (Z : AXPlan P A)
    (hZ : AXPlan.OK P A Z) (pts : s.IsPoint) :
    lv0 P.shape (A.recut P Z) (pts.recutK P K) ≤ 2 * lv0 s A pts + AXPlan.extra0 P K A Z := by
  obtain ⟨v, h, e⟩ := headLe0_self A pts
  have := lv0_recutK_aux P v K A Z hZ pts h
  rwa [e] at this

/-! ## 6. The counts -/

/-- Under the hypotheses below (among them `AXPlan.Kinds`, `AXPlan.OK`, and `he : εs' ≤ c.e`): the
counts after the plans. kT, kL, kB bound the numbers of splits; DT, DL, DB the old depths; k the old
rounds in one new round; xT, xL, xJ, x0 the leaves of the trees of the first parts. -/
theorem CountsB.recutM {I X : Type} {L : BatchProtocol I X} {pT : L.offline.shape.IsPoint}
    {pL : L.link.shape.IsPoint} {pB : L.onlineBatch.loc.shape.IsPoint} {ax : L.Aux pT pL pB} {M : LH.Nums}
    {c : CountNumsB} (h : CountsB L pT pL pB ax M c) {XT : XPlan L.offline.shape}
    {XL : XPlan L.link.shape} {XB : XPlan L.onlineBatch.loc.shape} {ZB : AXPlan XB L.onlineBatch.ann}
    (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB) (hZ : AXPlan.OK XB L.onlineBatch.ann ZB)
    (K : L.RecutKits XT XL XB ZB) {kT kL kB k DT DL DB xT xL xJ x0 : ℕ} (hkT : XT.cuts ≤ kT)
    (hkL : XL.cuts ≤ kL) (hkB : XB.cuts ≤ kB) (mT : XT.maxRun ≤ k) (mL : XL.maxRun ≤ k)
    (mB : XB.maxRun ≤ k) (dT : depths _ pT ≤ DT) (dL : depths _ pL ≤ DL) (dB : depths _ pB ≤ DB)
    (hxT : XT.extra K.T ≤ xT) (hxL : XL.extra K.Lk ≤ xL)
    (hxJ : AXPlan.extraJ XB K.B L.onlineBatch.ann ZB ≤ xJ) (hx0 : AXPlan.extra0 XB K.B L.onlineBatch.ann ZB ≤ x0)
    {εs' : ℝ≥0∞} (he : εs' ≤ c.e) :
    CountsB (L.recut XT XL XB ZB hK) (pT.recutK XT K.T) (pL.recutK XL K.Lk) (pB.recutK XB K.B)
      (ax.recut hK K) { M with εs := εs' }
      { c with
        rT := c.rT + kT, rL := c.rL + kL, rO := c.rO + kB, dT := max c.dT (DT + Nat.clog 2 k),
        dL := max c.dL (DL + Nat.clog 2 k), dO := max c.dO (DB + Nat.clog 2 k), lT := 2 * c.lT + xT,
        lL := 2 * c.lL + xL, lJ := 2 * c.lJ + xJ, l0 := 2 * c.l0 + x0 } where
  N := h.N
  rT := (Nat.le_add_right _ _).trans ((recutLength _ XT).le.trans (Nat.add_le_add h.rT hkT))
  rL := (Nat.le_add_right _ _).trans ((recutLength _ XL).le.trans (Nat.add_le_add h.rL hkL))
  rO := (Nat.le_add_right _ _).trans ((recutLength _ XB).le.trans (Nat.add_le_add h.rO hkB))
  dT := max_le (((le_max_left _ _).trans h.dT).trans (le_max_left _ _))
    ((depths_recutK_le_run XT K.T pT mT dT).trans (le_max_right _ _))
  dL := max_le (((le_max_left _ _).trans h.dL).trans (le_max_left _ _))
    ((depths_recutK_le_run XL K.Lk pL mL dL).trans (le_max_right _ _))
  dO := max_le (((le_max_left _ _).trans h.dO).trans (le_max_left _ _))
    ((depths_recutK_le_run XB K.B pB mB dB).trans (le_max_right _ _))
  dR := h.dR
  lI := h.lI
  lT := (leaves_recutK_le_two XT K.T pT).trans (Nat.add_le_add (Nat.mul_le_mul_left 2 h.lT) hxT)
  lL := (leaves_recutK_le_two XL K.Lk pL).trans (Nat.add_le_add (Nat.mul_le_mul_left 2 h.lL) hxL)
  lJ := (lvJ_recutK_le_two XB K.B L.onlineBatch.ann ZB hZ pB).trans
    (Nat.add_le_add (Nat.mul_le_mul_left 2 h.lJ) hxJ)
  l0 := (lv0_recutK_le_two XB K.B L.onlineBatch.ann ZB hZ pB).trans
    (Nat.add_le_add (Nat.mul_le_mul_left 2 h.l0) hx0)
  e := he
  pT := h.pT
  pL := h.pL
  pO := h.pO
  zT := h.zT
  zL := h.zL
  zO := h.zO

end Top
