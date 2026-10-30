-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/CountsRecut.lean: upper bounds on the compiler's counts of hash queries and blocks after
one pass in which rounds of an interface's three IOPs are cut and joined, against the counts before
the pass.

Definitions, statements and proofs. Generic: any interface, any plans, any kits (`BatchProtocol.RecutKits`,
Iop/RecutData.lean); what is asked of the annotations of the cuts is told with the names.
A plan (`XPlan s`, Iop/Recut.lean) goes through the rounds of a shape s: it keeps the first round,
cuts a first piece off it, or joins it with the second. The pass on an interface is `BatchProtocol.recut`
(Iop/BatchRecut.lean), on the compiler's data `DataK.recut` (CompileK/FitRecut.lean). `XPlan.cuts`
is a plan's number of cuts, `XPlan.maxRun` the largest number of old rounds whose errors stand in a
new round.

Why: the bounds α, ε, ζ of the compiler's theorem read four
functions of the data: `tVB` (the verifier's queries on one proof), `dr.K` (the largest number of
blocks of a round), `xTree` and `xFb` (the honest parties' evaluations of the leaf oracle and of
the Fiat-Shamir oracles in setup and n batches). Where a theorem is stated at the data after the
pass, numerals need these four there. `FitK.recut` carries the side conditions, not the counts.

Main names, by the parts of the file:
  Part 1, ordinary shapes. `Shape.pS`: the number of positions of all oracles. `pS_recutK_le`: a
    pass makes no position (a cut parts the positions of a round: `nPos_cut`; a join puts them side
    by side). `length_recut_le`: rounds after ≤ rounds before + cuts. `lvLoc_recutK_le`: the leaves
    of all trees after the pass ≤ 2 · (the leaves before) + (rounds before + cuts) (a tree over c
    positions has at most 2 c + 1 leaves and at least c). `dpLoc_recutK_le`: the deepest tree
    ≤ D + ⌈log₂ k⌉, if the old depths are at most D and `maxRun` ≤ k: k old rounds at most in a new
    one (Top/BatchCountsRecutMsg.lean).
  Part 2, batch shapes, by components, for a plan whose cuts' annotations obey their laws
    (`AXPlan.OK`): `Shape.pSJ`, `Shape.pS0`, `cardJ_cut`, `card0_cut`, `pSJ_recutK_le`,
    `pS0_recutK_le`, `lvJ_recutK_le`, `lv0_recutK_le` (the same bound). `dpB_recutK_le` (it does
    not ask `AXPlan.OK`), with D and k as in Part 1: ≤ D + 1 + ⌈log₂ k⌉ (`nPos_eq_cards`: a
    position is a slot's or shared).
  Part 3, blocks: `BatchProtocol.Draws.K_le_of_totLe` (from `Shape.Draws.maxB_le_totB`,
    Blocks/DrawsSum.lean).
  Part 4, at `D.recut hK K` (p, the announced numbers of openings, the depth of the request tree
    and the trees over encoded indices are unchanged by the pass):
  `K_recut_le_tot`: dr.K after ≤ any bound nb on the blocks of all rounds of each of the three
    protocols (`BatchProtocol.Draws.TotLe`) before the pass (`BatchProtocol.Draws.K_recut_le`, Iop/RecutDraws.lean, has
    ≤ k · K).
  `xFb_recut_le`: xFb after ≤ xFb before + cutsFb,
    `cutsFb` = 2 cuts_T + leaves · 2 cuts_L + n (maxBatchSize + 1) cuts_B.
  `xTree_recut_le`: under `AXPlan.OK`, xTree after ≤ 2 · xTree before + xFb before + cutsFb.
  `tVB_recut_le`: tVB after ≤ tVB before + (the cuts of the three plans), if the trees over the
    encoded indices stay the deepest (old depths + ⌈log₂ k⌉, + 1 for the batch IOP, ≤ dE).
    `tVB_recut_le_of`: with free numbers, without that condition. Both ask `maxRun` ≤ k of the
    three plans.
So the plans enter these bounds through their cuts and a bound k on `XPlan.maxRun` only. Beside
these, Part 2 (but for `dpB_recutK_le`) and `xTree_recut_le` ask that the annotations are lawful
(`AXPlan.OK`), and `D.recut` takes `AXPlan.Kinds`.

Limits: the bounds are crude. The factor 2 on leaves is nearly met where a join puts a small oracle
beside one whose length is a power of two, or where a cut leaves pieces a little longer than a
power of two; elsewhere it is far off. The rounds that joins take away are not counted. An instance
that knows its numbers of positions can do better round by round. This file says nothing on
numerals, nothing on the numbers of any particular plan, nothing on other moves of the protocol
than this pass, and nothing on security.

Terms: lean/GLOSSARY.md.
-/
import CompileK.Counts
import CompileK.FitRecut
import Top.BatchCountsRecutMsg
import Iop.RecutProofs
import Blocks.DrawsSum

set_option autoImplicit false

namespace Iop
open Blocks Top

/-! ## Part 1. Ordinary shapes: sums of numbers of positions -/

namespace Shape

/-- the number of positions of all oracles of an ordinary IOP -/
def pS : (s : Shape) → s.IsPoint → ℕ
  | [], _ => 0
  | _ :: s, (pt, pts) => nPos pt + pS s pts

theorem pS_le_lvLoc : ∀ (s : Shape) (pts : s.IsPoint), pS s pts ≤ lvLoc s pts
  | [], _ => le_rfl
  | _ :: s, (pt, pts) => Nat.add_le_add (Nat.le_pow_clog (by decide) _) (pS_le_lvLoc s pts)

theorem lvLoc_le_pS : ∀ (s : Shape) (pts : s.IsPoint), lvLoc s pts ≤ 2 * pS s pts + s.length
  | [], _ => le_rfl
  | _ :: s, (pt, pts) => by
      have h1 := lvOf_le (nPos pt)
      have h2 := lvLoc_le_pS s pts
      show lvOf (nPos pt) + lvLoc s pts ≤ 2 * (nPos pt + pS s pts) + (s.length + 1)
      omega

theorem dpLoc_eq : ∀ (s : Shape) (pts : s.IsPoint), dpLoc s pts = depths s pts
  | [], _ => rfl
  | _ :: s, (pt, pts) => congrArg (max (depthR pt)) (dpLoc_eq s pts)

end Shape

theorem nPos_cut {r : Round} (c : RCut r) (pt : r.IsPoint)
    (p1 : c.fst.IsPoint) (p2 : c.snd.IsPoint) :
    nPos p1 + nPos p2 = nPos pt := by
  letI := pt.finPos
  letI : Fintype c.PosA := p1.finPos
  letI : Fintype c.PosB := p2.finPos
  exact (Fintype.card_sum (α := c.PosA) (β := c.PosB)).symm.trans (Fintype.card_congr c.pos)

/-- A pass of cuts and joins makes no position. -/
theorem pS_recutK_le {s : Shape} (P : XPlan s) :
    ∀ (K : P.Kits) (pts : s.IsPoint), Shape.pS P.shape (pts.recutK P K) ≤ Shape.pS s pts := by
  induction P with
  | nil => exact fun _ _ => le_rfl
  | @keep r s P ih =>
      rintro K ⟨pt, pts⟩
      exact Nat.add_le_add_left (ih K pts) _
  | @cut r s c P ih =>
      rintro ⟨K1, K2, K⟩ ⟨pt, pts⟩
      have h1 : Shape.pS P.shape (Shape.IsPoint.recutK P K (K2.pt, pts)) ≤
          nPos K2.pt + Shape.pS s pts :=
        ih K (K2.pt, pts)
      have h2 := nPos_cut c pt K1.pt K2.pt
      show nPos K1.pt + Shape.pS P.shape (Shape.IsPoint.recutK P K (K2.pt, pts)) ≤
        nPos pt + Shape.pS s pts
      omega
  | @msg r1 r2 s u P ih =>
      rintro K ⟨p1, p2, pts⟩
      have h1 : Shape.pS P.shape (Shape.IsPoint.recutK P K (p1.joinMsg p2, pts)) ≤
          nPos (p1.joinMsg p2) + Shape.pS s pts :=
        ih K (p1.joinMsg p2, pts)
      rw [nPos_joinMsg] at h1
      show Shape.pS P.shape (Shape.IsPoint.recutK P K (p1.joinMsg p2, pts)) ≤
        nPos p1 + (nPos p2 + Shape.pS s pts)
      omega
  | @chal r1 r2 s np P ih =>
      rintro K ⟨p1, p2, pts⟩
      have h1 : Shape.pS P.shape (Shape.IsPoint.recutK P K (p1.joinChal r2, pts)) ≤
          nPos p1 + Shape.pS s pts :=
        ih K (p1.joinChal r2, pts)
      show Shape.pS P.shape (Shape.IsPoint.recutK P K (p1.joinChal r2, pts)) ≤
        nPos p1 + (nPos p2 + Shape.pS s pts)
      omega

theorem length_recut_le {s : Shape} (P : XPlan s) : P.shape.length ≤ s.length + P.cuts := by
  have := recutLength s P
  omega

/-- The leaves of all trees after the pass: at most twice the old ones, and one for each old round
and each cut. -/
theorem lvLoc_recutK_le {s : Shape} (P : XPlan s) (K : P.Kits) (pts : s.IsPoint) :
    Shape.lvLoc P.shape (pts.recutK P K) ≤ 2 * Shape.lvLoc s pts + (s.length + P.cuts) := by
  have h1 := Shape.lvLoc_le_pS P.shape (pts.recutK P K)
  have h2 := pS_recutK_le P K pts
  have h3 := Shape.pS_le_lvLoc s pts
  have h4 := length_recut_le P
  omega

/-- The deepest tree after the pass. -/
theorem dpLoc_recutK_le {k D : ℕ} {s : Shape} (P : XPlan s) (K : P.Kits) (pts : s.IsPoint)
    (hm : P.maxRun ≤ k) (h : Shape.dpLoc s pts ≤ D) :
    Shape.dpLoc P.shape (pts.recutK P K) ≤ D + Nat.clog 2 k := by
  rw [Shape.dpLoc_eq] at h ⊢
  exact depths_recutK_le_run P K pts hm h

/-! ## Part 2. Batch shapes: by components -/

namespace Shape

/-- the number of positions of the components of one slot; `pS0`: of the shared components -/
def pSJ : (s : Shape) → RoundSplits s → s.IsPoint → ℕ
  | [], _, _ => 0
  | _ :: s, (a, A), (pt, pts) => a.cardJ pt + pSJ s A pts
def pS0 : (s : Shape) → RoundSplits s → s.IsPoint → ℕ
  | [], _, _ => 0
  | _ :: s, (a, A), (pt, pts) => a.card0 pt + pS0 s A pts

theorem pSJ_le_lvJ : ∀ (s : Shape) (A : RoundSplits s) (pts : s.IsPoint), pSJ s A pts ≤ lvJ s A pts
  | [], _, _ => le_rfl
  | _ :: s, (_, A), (_, pts) => Nat.add_le_add (Nat.le_pow_clog (by decide) _) (pSJ_le_lvJ s A pts)
theorem pS0_le_lv0 : ∀ (s : Shape) (A : RoundSplits s) (pts : s.IsPoint), pS0 s A pts ≤ lv0 s A pts
  | [], _, _ => le_rfl
  | _ :: s, (_, A), (_, pts) => Nat.add_le_add (Nat.le_pow_clog (by decide) _) (pS0_le_lv0 s A pts)

theorem lvJ_le_pSJ :
    ∀ (s : Shape) (A : RoundSplits s) (pts : s.IsPoint), lvJ s A pts ≤ 2 * pSJ s A pts + s.length
  | [], _, _ => le_rfl
  | _ :: s, (a, A), (pt, pts) => by
      have h1 := lvOf_le (a.cardJ pt)
      have h2 := lvJ_le_pSJ s A pts
      show lvOf (a.cardJ pt) + lvJ s A pts ≤ 2 * (a.cardJ pt + pSJ s A pts) + (s.length + 1)
      omega
theorem lv0_le_pS0 :
    ∀ (s : Shape) (A : RoundSplits s) (pts : s.IsPoint), lv0 s A pts ≤ 2 * pS0 s A pts + s.length
  | [], _, _ => le_rfl
  | _ :: s, (a, A), (pt, pts) => by
      have h1 := lvOf_le (a.card0 pt)
      have h2 := lv0_le_pS0 s A pts
      show lvOf (a.card0 pt) + lv0 s A pts ≤ 2 * (a.card0 pt + pS0 s A pts) + (s.length + 1)
      omega

end Shape

theorem cardJ_le_nPos {r : Round} (a : RAnn r) (pt : r.IsPoint) : a.cardJ pt ≤ nPos pt := by
  letI := pt.finPos
  exact Fintype.card_subtype_le _

theorem card0_le_card {r : Round} (a : RAnn r) (pt : r.IsPoint) : a.card0 pt ≤ nPos pt := by
  letI := pt.finPos
  exact Fintype.card_subtype_le _

/-- every position is a slot's or shared -/
theorem nPos_eq_cards {r : Round} (a : RAnn r) (pt : r.IsPoint) :
    nPos pt = a.cardJ pt + a.card0 pt := by
  letI := pt.finPos
  have e : {p : r.Pos // a.own p = true} ⊕ {p : r.Pos // ¬ a.own p = true} ≃ r.Pos :=
    Equiv.sumCompl fun p => a.own p = true
  have e2 : {p : r.Pos // ¬ a.own p = true} ≃ {p : r.Pos // a.own p = false} :=
    Equiv.subtypeEquivRight fun p => by simp
  exact (Fintype.card_congr e).symm.trans
    (Fintype.card_sum.trans (congrArg _ (Fintype.card_congr e2)))

namespace Shape

/-- the depths by components against the depths of whole rounds -/
theorem dpB_le_depths : ∀ (s : Shape) (A : RoundSplits s) (pts : s.IsPoint), dpB s A pts ≤ depths s pts
  | [], _, _ => le_rfl
  | _ :: s, (a, A), (pt, pts) =>
    max_le_max
      (max_le (Nat.clog_mono_right 2 (card0_le_card a pt))
        (Nat.clog_mono_right 2 (cardJ_le_nPos a pt)))
      (dpB_le_depths s A pts)

theorem depths_le_dpB : ∀ (s : Shape) (A : RoundSplits s) (pts : s.IsPoint), depths s pts ≤ dpB s A pts + 1
  | [], _, _ => Nat.zero_le _
  | _ :: s, (a, A), (pt, pts) => by
      have h1 := depths_le_dpB s A pts
      have h2 : depthR pt ≤ max (Nat.clog 2 (a.card0 pt)) (Nat.clog 2 (a.cardJ pt)) + 1 := by
        refine Nat.clog_le_of_le_pow ?_
        show nPos pt ≤ _
        rw [nPos_eq_cards a pt, pow_succ, Nat.mul_two]
        exact Nat.add_le_add
          ((Nat.le_pow_clog (by decide) _).trans
            (Nat.pow_le_pow_right (by decide) (le_max_right _ _)))
          ((Nat.le_pow_clog (by decide) _).trans
            (Nat.pow_le_pow_right (by decide) (le_max_left _ _)))
      show max (depthR pt) (depths s pts) ≤
        max (max (Nat.clog 2 (a.card0 pt)) (Nat.clog 2 (a.cardJ pt))) (dpB s A pts) + 1
      omega

end Shape

section OneCut
variable {r : Round} {c : RCut r} {a : RAnn r} {b : ACut c a}

theorem cardJ_cut (hb : b.OK) (pt : r.IsPoint) (p1 : c.fst.IsPoint) (p2 : c.snd.IsPoint) :
    b.ann1.cardJ p1 + b.ann2.cardJ p2 = a.cardJ pt := by
  letI := pt.finPos
  letI : Fintype c.PosA := p1.finPos
  letI : Fintype c.PosB := p2.finPos
  have e1 : {q : c.PosA ⊕ c.PosB // a.own (c.pos q) = true} ≃ {p : r.Pos // a.own p = true} :=
    c.pos.subtypeEquiv fun _ => Iff.rfl
  have e2 := Equiv.subtypeSum (p := fun q : c.PosA ⊕ c.PosB => a.own (c.pos q) = true)
  have eA : {p : c.PosA // b.A.own p = true} ≃ {p : c.PosA // a.own (c.pos (.inl p)) = true} :=
    Equiv.subtypeEquivRight fun p => by rw [hb.ownA]
  have eB : {p : c.PosB // b.B.own p = true} ≃ {p : c.PosB // a.own (c.pos (.inr p)) = true} :=
    Equiv.subtypeEquivRight fun p => by rw [hb.ownB]
  exact (Fintype.card_sum.symm.trans
      (Fintype.card_congr ((Equiv.sumCongr eA eB).trans e2.symm))).trans
    (Fintype.card_congr e1)

theorem card0_cut (hb : b.OK) (pt : r.IsPoint) (p1 : c.fst.IsPoint) (p2 : c.snd.IsPoint) :
    b.ann1.card0 p1 + b.ann2.card0 p2 = a.card0 pt := by
  letI := pt.finPos
  letI : Fintype c.PosA := p1.finPos
  letI : Fintype c.PosB := p2.finPos
  have e1 : {q : c.PosA ⊕ c.PosB // a.own (c.pos q) = false} ≃ {p : r.Pos // a.own p = false} :=
    c.pos.subtypeEquiv fun _ => Iff.rfl
  have e2 := Equiv.subtypeSum (p := fun q : c.PosA ⊕ c.PosB => a.own (c.pos q) = false)
  have eA : {p : c.PosA // b.A.own p = false} ≃ {p : c.PosA // a.own (c.pos (.inl p)) = false} :=
    Equiv.subtypeEquivRight fun p => by rw [hb.ownA]
  have eB : {p : c.PosB // b.B.own p = false} ≃ {p : c.PosB // a.own (c.pos (.inr p)) = false} :=
    Equiv.subtypeEquivRight fun p => by rw [hb.ownB]
  exact (Fintype.card_sum.symm.trans
      (Fintype.card_congr ((Equiv.sumCongr eA eB).trans e2.symm))).trans
    (Fintype.card_congr e1)

end OneCut

theorem pSJ_recutK_le {s : Shape} (P : XPlan s) :
    ∀ (K : P.Kits) (A : RoundSplits s) (Z : AXPlan P A), AXPlan.OK P A Z →
      ∀ pts : s.IsPoint, Shape.pSJ P.shape (A.recut P Z) (pts.recutK P K) ≤ Shape.pSJ s A pts := by
  induction P with
  | nil => exact fun _ _ _ _ _ => le_rfl
  | @keep r s P ih =>
      rintro K ⟨a, A⟩ Z hZ ⟨pt, pts⟩
      exact Nat.add_le_add_left (ih K A Z hZ pts) _
  | @cut r s c P ih =>
      rintro ⟨K1, K2, K⟩ ⟨a, A⟩ ⟨b, Z⟩ hZ ⟨pt, pts⟩
      have h1 : Shape.pSJ P.shape (RoundSplits.recut P (b.ann2, A) Z)
            (Shape.IsPoint.recutK P K (K2.pt, pts)) ≤
          b.ann2.cardJ K2.pt + Shape.pSJ s A pts :=
        ih K (b.ann2, A) Z hZ.2 (K2.pt, pts)
      have h2 : b.ann1.cardJ K1.pt + b.ann2.cardJ K2.pt = a.cardJ pt :=
        cardJ_cut hZ.1 pt K1.pt K2.pt
      show b.ann1.cardJ K1.pt +
          Shape.pSJ P.shape (RoundSplits.recut P (b.ann2, A) Z) (Shape.IsPoint.recutK P K (K2.pt, pts)) ≤
        a.cardJ pt + Shape.pSJ s A pts
      omega
  | @msg r1 r2 s u P ih =>
      rintro K ⟨a1, a2, A⟩ Z hZ ⟨p1, p2, pts⟩
      have h1 : Shape.pSJ P.shape (RoundSplits.recut P (a1.joinMsg a2, A) Z)
            (Shape.IsPoint.recutK P K (p1.joinMsg p2, pts)) ≤
          (a1.joinMsg a2).cardJ (p1.joinMsg p2) + Shape.pSJ s A pts :=
        ih K (a1.joinMsg a2, A) Z hZ (p1.joinMsg p2, pts)
      rw [cardJ_joinMsg] at h1
      show Shape.pSJ P.shape (RoundSplits.recut P (a1.joinMsg a2, A) Z)
          (Shape.IsPoint.recutK P K (p1.joinMsg p2, pts)) ≤
        a1.cardJ p1 + (a2.cardJ p2 + Shape.pSJ s A pts)
      omega
  | @chal r1 r2 s np P ih =>
      rintro K ⟨a1, a2, A⟩ Z hZ ⟨p1, p2, pts⟩
      have h1 : Shape.pSJ P.shape (RoundSplits.recut P (a1.joinChal r2, A) Z)
            (Shape.IsPoint.recutK P K (p1.joinChal r2, pts)) ≤
          a1.cardJ p1 + Shape.pSJ s A pts :=
        ih K (a1.joinChal r2, A) Z hZ (p1.joinChal r2, pts)
      show Shape.pSJ P.shape (RoundSplits.recut P (a1.joinChal r2, A) Z)
          (Shape.IsPoint.recutK P K (p1.joinChal r2, pts)) ≤
        a1.cardJ p1 + (a2.cardJ p2 + Shape.pSJ s A pts)
      omega

theorem pS0_recutK_le {s : Shape} (P : XPlan s) :
    ∀ (K : P.Kits) (A : RoundSplits s) (Z : AXPlan P A), AXPlan.OK P A Z →
      ∀ pts : s.IsPoint, Shape.pS0 P.shape (A.recut P Z) (pts.recutK P K) ≤ Shape.pS0 s A pts := by
  induction P with
  | nil => exact fun _ _ _ _ _ => le_rfl
  | @keep r s P ih =>
      rintro K ⟨a, A⟩ Z hZ ⟨pt, pts⟩
      exact Nat.add_le_add_left (ih K A Z hZ pts) _
  | @cut r s c P ih =>
      rintro ⟨K1, K2, K⟩ ⟨a, A⟩ ⟨b, Z⟩ hZ ⟨pt, pts⟩
      have h1 : Shape.pS0 P.shape (RoundSplits.recut P (b.ann2, A) Z)
            (Shape.IsPoint.recutK P K (K2.pt, pts)) ≤
          b.ann2.card0 K2.pt + Shape.pS0 s A pts :=
        ih K (b.ann2, A) Z hZ.2 (K2.pt, pts)
      have h2 : b.ann1.card0 K1.pt + b.ann2.card0 K2.pt = a.card0 pt :=
        card0_cut hZ.1 pt K1.pt K2.pt
      show b.ann1.card0 K1.pt +
          Shape.pS0 P.shape (RoundSplits.recut P (b.ann2, A) Z) (Shape.IsPoint.recutK P K (K2.pt, pts)) ≤
        a.card0 pt + Shape.pS0 s A pts
      omega
  | @msg r1 r2 s u P ih =>
      rintro K ⟨a1, a2, A⟩ Z hZ ⟨p1, p2, pts⟩
      have h1 : Shape.pS0 P.shape (RoundSplits.recut P (a1.joinMsg a2, A) Z)
            (Shape.IsPoint.recutK P K (p1.joinMsg p2, pts)) ≤
          (a1.joinMsg a2).card0 (p1.joinMsg p2) + Shape.pS0 s A pts :=
        ih K (a1.joinMsg a2, A) Z hZ (p1.joinMsg p2, pts)
      rw [card0_joinMsg] at h1
      show Shape.pS0 P.shape (RoundSplits.recut P (a1.joinMsg a2, A) Z)
          (Shape.IsPoint.recutK P K (p1.joinMsg p2, pts)) ≤
        a1.card0 p1 + (a2.card0 p2 + Shape.pS0 s A pts)
      omega
  | @chal r1 r2 s np P ih =>
      rintro K ⟨a1, a2, A⟩ Z hZ ⟨p1, p2, pts⟩
      have h1 : Shape.pS0 P.shape (RoundSplits.recut P (a1.joinChal r2, A) Z)
            (Shape.IsPoint.recutK P K (p1.joinChal r2, pts)) ≤
          a1.card0 p1 + Shape.pS0 s A pts :=
        ih K (a1.joinChal r2, A) Z hZ (p1.joinChal r2, pts)
      show Shape.pS0 P.shape (RoundSplits.recut P (a1.joinChal r2, A) Z)
          (Shape.IsPoint.recutK P K (p1.joinChal r2, pts)) ≤
        a1.card0 p1 + (a2.card0 p2 + Shape.pS0 s A pts)
      omega

theorem lvJ_recutK_le {s : Shape} (P : XPlan s) (K : P.Kits) (A : RoundSplits s) (Z : AXPlan P A)
    (hZ : AXPlan.OK P A Z) (pts : s.IsPoint) :
    Shape.lvJ P.shape (A.recut P Z) (pts.recutK P K) ≤
      2 * Shape.lvJ s A pts + (s.length + P.cuts) := by
  have h1 := Shape.lvJ_le_pSJ P.shape (A.recut P Z) (pts.recutK P K)
  have h2 := pSJ_recutK_le P K A Z hZ pts
  have h3 := Shape.pSJ_le_lvJ s A pts
  have h4 := length_recut_le P
  omega

theorem lv0_recutK_le {s : Shape} (P : XPlan s) (K : P.Kits) (A : RoundSplits s) (Z : AXPlan P A)
    (hZ : AXPlan.OK P A Z) (pts : s.IsPoint) :
    Shape.lv0 P.shape (A.recut P Z) (pts.recutK P K) ≤
      2 * Shape.lv0 s A pts + (s.length + P.cuts) := by
  have h1 := Shape.lv0_le_pS0 P.shape (A.recut P Z) (pts.recutK P K)
  have h2 := pS0_recutK_le P K A Z hZ pts
  have h3 := Shape.pS0_le_lv0 s A pts
  have h4 := length_recut_le P
  omega

theorem dpB_recutK_le {k D : ℕ} {s : Shape} (P : XPlan s) (K : P.Kits) (A : RoundSplits s) (Z : AXPlan P A)
    (pts : s.IsPoint) (hm : P.maxRun ≤ k) (h : Shape.dpB s A pts ≤ D) :
    Shape.dpB P.shape (A.recut P Z) (pts.recutK P K) ≤ D + 1 + Nat.clog 2 k :=
  (Shape.dpB_le_depths _ _ _).trans
    (depths_recutK_le_run P K pts hm ((Shape.depths_le_dpB s A pts).trans (Nat.succ_le_succ h)))

/-! ## Part 3. Blocks -/

/-- the largest number of blocks of a round is at most any bound on the blocks of all rounds of a
protocol (`BatchProtocol.Draws.TotLe`) -/
theorem BatchProtocol.Draws.K_le_of_totLe
    {I X : Type} {L : BatchProtocol I X} {lam : ℕ} {dr : L.Draws lam} {n : ℕ} (h : dr.TotLe n) : dr.K ≤ n :=
  max_le ((Shape.Draws.maxB_le_totB _ _).trans h.1)
    (max_le ((Shape.Draws.maxB_le_totB _ _).trans h.2.1)
      ((Shape.Draws.maxB_le_totB _ _).trans h.2.2))

end Iop

/-! ## Part 4. The compiler's counts after the pass -/

namespace Compile.Batch
open Iop

variable {I X : Type} {L : BatchProtocol I X} {lam : ℕ} {XT : XPlan L.offline.shape} {XL : XPlan L.link.shape}
  {XB : XPlan L.onlineBatch.loc.shape} {ZB : AXPlan XB L.onlineBatch.ann}
variable (D : DataK L lam) (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB) (K : L.RecutKits XT XL XB ZB)

/-- what the cuts add to the count of Fiat-Shamir evaluations in setup and n batches -/
def cutsFb (L : BatchProtocol I X) (XT : XPlan L.offline.shape) (XL : XPlan L.link.shape)
    (XB : XPlan L.onlineBatch.loc.shape) (p : Params) (n : ℕ) : ℕ :=
  2 * XT.cuts + p.leaves * (2 * XL.cuts) + n * ((L.maxBatchSize + 1) * XB.cuts)

/-- The largest number of blocks of a round after the pass: at most any bound on the blocks of all
rounds of a protocol before the pass. (not all hypotheses are named here: see the statement
below) -/
theorem K_recut_le_tot {nb : ℕ} (h : D.dr.TotLe nb) : (D.recut hK K).dr.K ≤ nb :=
  BatchProtocol.Draws.K_le_of_totLe (h.recut XT XL XB ZB hK)

/-- Fiat-Shamir evaluations after the pass. -/
theorem xFb_recut_le (n : ℕ) :
    xFb (L := (D.recut hK K).L) (D.recut hK K).p n ≤
      xFb (L := D.L) D.p n + cutsFb L XT XL XB D.p n := by
  rw [xFb_data, xFb_data]
  have hT : XT.shape.length ≤ L.offline.shape.length + XT.cuts := length_recut_le XT
  have hL : XL.shape.length ≤ L.link.shape.length + XL.cuts := length_recut_le XL
  have hB : XB.shape.length ≤ L.onlineBatch.loc.shape.length + XB.cuts := length_recut_le XB
  show 2 * XT.shape.length + D.p.leaves * (2 * XL.shape.length) +
      n * ((L.maxBatchSize + 1) * XB.shape.length) ≤ _
  calc
    2 * XT.shape.length + D.p.leaves * (2 * XL.shape.length) + n * ((L.maxBatchSize + 1) * XB.shape.length) ≤
        2 * (L.offline.shape.length + XT.cuts) + D.p.leaves * (2 * (L.link.shape.length + XL.cuts)) +
          n * ((L.maxBatchSize + 1) * (L.onlineBatch.loc.shape.length + XB.cuts)) := by gcongr
    _ = _ := by unfold cutsFb; ring

/-- Under `AXPlan.Kinds` and `AXPlan.OK`, the evaluations of the leaf oracle after the pass are at
most twice the old count, plus the old count of Fiat-Shamir evaluations and `cutsFb`. -/
theorem xTree_recut_le (hZ : AXPlan.OK XB L.onlineBatch.ann ZB) (n : ℕ) :
    xTree (D.recut hK K).W (D.recut hK K).p n ≤
      2 * xTree D.W D.p n + (xFb (L := D.L) D.p n + cutsFb L XT XL XB D.p n) := by
  rw [xTree_data, xTree_data, xFb_data]
  have lT : XT.shape.length ≤ L.offline.shape.length + XT.cuts := length_recut_le XT
  have lL : XL.shape.length ≤ L.link.shape.length + XL.cuts := length_recut_le XL
  have vT := lvLoc_recutK_le XT K.T D.pT
  have vL := lvLoc_recutK_le XL K.Lk D.pL
  have vJ := lvJ_recutK_le XB K.B L.onlineBatch.ann ZB hZ D.pB
  have v0 := lv0_recutK_le XB K.B L.onlineBatch.ann ZB hZ D.pB
  have hT : Shape.lvLoc XT.shape (D.pT.recutK XT K.T) + XT.shape.length ≤
      2 * (L.offline.shape.lvLoc D.pT + L.offline.shape.length) + 2 * XT.cuts := by omega
  have hL : Shape.lvLoc XL.shape (D.pL.recutK XL K.Lk) + XL.shape.length ≤
      2 * (L.link.shape.lvLoc D.pL + L.link.shape.length) + 2 * XL.cuts := by omega
  have hB : L.maxBatchSize * Shape.lvJ XB.shape (L.onlineBatch.ann.recut XB ZB) (D.pB.recutK XB K.B) +
        Shape.lv0 XB.shape (L.onlineBatch.ann.recut XB ZB) (D.pB.recutK XB K.B) ≤
      2 * (L.maxBatchSize * L.onlineBatch.loc.shape.lvJ L.onlineBatch.ann D.pB + L.onlineBatch.loc.shape.lv0 L.onlineBatch.ann D.pB) +
        (L.maxBatchSize + 1) * (L.onlineBatch.loc.shape.length + XB.cuts) :=
    calc
      _ ≤ L.maxBatchSize * (2 * L.onlineBatch.loc.shape.lvJ L.onlineBatch.ann D.pB + (L.onlineBatch.loc.shape.length + XB.cuts)) +
            (2 * L.onlineBatch.loc.shape.lv0 L.onlineBatch.ann D.pB + (L.onlineBatch.loc.shape.length + XB.cuts)) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ vJ) v0
      _ = _ := by ring
  show (D.p.leaves + 1) * 2 ^ D.dE + (Shape.lvLoc XT.shape (D.pT.recutK XT K.T) + XT.shape.length) +
      D.p.leaves * (Shape.lvLoc XL.shape (D.pL.recutK XL K.Lk) + XL.shape.length) +
      n * (L.maxBatchSize * Shape.lvJ XB.shape (L.onlineBatch.ann.recut XB ZB) (D.pB.recutK XB K.B) +
          Shape.lv0 XB.shape (L.onlineBatch.ann.recut XB ZB) (D.pB.recutK XB K.B)) ≤ _
  calc
    _ ≤ (D.p.leaves + 1) * 2 ^ D.dE +
          (2 * (L.offline.shape.lvLoc D.pT + L.offline.shape.length) + 2 * XT.cuts) +
          D.p.leaves * (2 * (L.link.shape.lvLoc D.pL + L.link.shape.length) + 2 * XL.cuts) +
          n * (2 * (L.maxBatchSize * L.onlineBatch.loc.shape.lvJ L.onlineBatch.ann D.pB + L.onlineBatch.loc.shape.lv0 L.onlineBatch.ann D.pB) +
              (L.maxBatchSize + 1) * (L.onlineBatch.loc.shape.length + XB.cuts)) :=
        Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left hT _) (Nat.mul_le_mul_left _ hL))
          (Nat.mul_le_mul_left _ hB)
    _ ≤ _ := by
        unfold cutsFb
        generalize (D.p.leaves + 1) * 2 ^ D.dE = a
        nlinarith [Nat.zero_le a, Nat.zero_le (D.p.leaves * L.link.shape.length),
          Nat.zero_le L.offline.shape.length]

/-- The verifier's queries on one proof after the pass, with free numbers (`tVB_le_of`,
CompileK/Counts.lean): r bounds the old rounds, c the cuts, o the openings, k the old rounds in a
new one; d bounds dE and the old depths + ⌈log₂ k⌉, + 1 for the batch IOP. (not all hypotheses are
named here: see the statement below) -/
theorem tVB_recut_le_of (r c o d k : ℕ)
    (hr : L.offline.shape.length + L.link.shape.length + L.onlineBatch.loc.shape.length ≤ r)
    (hc : XT.cuts + XL.cuts + XB.cuts ≤ c) (ho : D.no.T + D.no.L + D.no.O ≤ o) (kT : XT.maxRun ≤ k)
    (kL : XL.maxRun ≤ k) (kB : XB.maxRun ≤ k) (hE : D.dE ≤ d)
    (hT : L.offline.shape.dpLoc D.pT + Nat.clog 2 k ≤ d)
    (hL : L.link.shape.dpLoc D.pL + Nat.clog 2 k ≤ d)
    (hB : L.onlineBatch.loc.shape.dpB L.onlineBatch.ann D.pB + 1 + Nat.clog 2 k ≤ d) :
    tVB (D.recut hK K).W ≤ r + c + 3 + o * (d + 1) + 3 * (D.ax.depthReq + 1) :=
  tVB_le_of (D.recut hK K) (r + c) o d
    (by
      have lT : XT.shape.length ≤ L.offline.shape.length + XT.cuts := length_recut_le XT
      have lL : XL.shape.length ≤ L.link.shape.length + XL.cuts := length_recut_le XL
      have lB : XB.shape.length ≤ L.onlineBatch.loc.shape.length + XB.cuts := length_recut_le XB
      show XT.shape.length + XL.shape.length + XB.shape.length ≤ r + c
      omega)
    ho hE ((dpLoc_recutK_le XT K.T D.pT kT le_rfl).trans hT)
    ((dpLoc_recutK_le XL K.Lk D.pL kL le_rfl).trans hL)
    ((dpB_recutK_le XB K.B L.onlineBatch.ann ZB D.pB kB le_rfl).trans hB)

/-- Under the hypotheses below, the same against the old count: where the trees over the encoded
indices stay the deepest, the pass adds at most one query for each cut. -/
theorem tVB_recut_le (k : ℕ) (kT : XT.maxRun ≤ k) (kL : XL.maxRun ≤ k) (kB : XB.maxRun ≤ k)
    (hT : L.offline.shape.dpLoc D.pT + Nat.clog 2 k ≤ D.dE)
    (hL : L.link.shape.dpLoc D.pL + Nat.clog 2 k ≤ D.dE)
    (hB : L.onlineBatch.loc.shape.dpB L.onlineBatch.ann D.pB + 1 + Nat.clog 2 k ≤ D.dE) :
    tVB (D.recut hK K).W ≤ tVB D.W + (XT.cuts + XL.cuts + XB.cuts) := by
  rw [tVB_data, tVB_data]
  have lT : XT.shape.length ≤ L.offline.shape.length + XT.cuts := length_recut_le XT
  have lL : XL.shape.length ≤ L.link.shape.length + XL.cuts := length_recut_le XL
  have lB : XB.shape.length ≤ L.onlineBatch.loc.shape.length + XB.cuts := length_recut_le XB
  have dT : max D.dE (Shape.dpLoc XT.shape (D.pT.recutK XT K.T)) ≤
      max D.dE (L.offline.shape.dpLoc D.pT) :=
    max_le (le_max_left _ _)
      (((dpLoc_recutK_le XT K.T D.pT kT le_rfl).trans hT).trans (le_max_left _ _))
  have dL : max D.dE (Shape.dpLoc XL.shape (D.pL.recutK XL K.Lk)) ≤
      max D.dE (L.link.shape.dpLoc D.pL) :=
    max_le (le_max_left _ _)
      (((dpLoc_recutK_le XL K.Lk D.pL kL le_rfl).trans hL).trans (le_max_left _ _))
  have dB : max D.dE (Shape.dpB XB.shape (L.onlineBatch.ann.recut XB ZB) (D.pB.recutK XB K.B)) ≤
      max D.dE (L.onlineBatch.loc.shape.dpB L.onlineBatch.ann D.pB) :=
    max_le (le_max_left _ _)
      (((dpB_recutK_le XB K.B L.onlineBatch.ann ZB D.pB kB le_rfl).trans hB).trans (le_max_left _ _))
  have mT := Nat.mul_le_mul_left D.no.T (Nat.add_le_add_right dT 1)
  have mL := Nat.mul_le_mul_left D.no.L (Nat.add_le_add_right dL 1)
  have mB := Nat.mul_le_mul_left D.no.O (Nat.add_le_add_right dB 1)
  show (XT.shape.length + 1 +
        (D.no.T * (max D.dE (Shape.dpLoc XT.shape (D.pT.recutK XT K.T)) + 1) +
          (D.ax.depthReq + 1))) +
      (XL.shape.length + 1 +
        (D.no.L * (max D.dE (Shape.dpLoc XL.shape (D.pL.recutK XL K.Lk)) + 1) +
          (D.ax.depthReq + 1))) +
      (XB.shape.length + 1 +
        (D.no.O * (max D.dE (Shape.dpB XB.shape (L.onlineBatch.ann.recut XB ZB) (D.pB.recutK XB K.B)) + 1) +
          (D.ax.depthReq + 1))) ≤ _
  generalize D.no.T * (max D.dE (Shape.dpLoc XT.shape (D.pT.recutK XT K.T)) + 1) = a1 at mT ⊢
  generalize D.no.L * (max D.dE (Shape.dpLoc XL.shape (D.pL.recutK XL K.Lk)) + 1) = a2 at mL ⊢
  generalize D.no.O *
      (max D.dE (Shape.dpB XB.shape (L.onlineBatch.ann.recut XB ZB) (D.pB.recutK XB K.B)) + 1) = a3 at mB ⊢
  generalize D.no.T * (max D.dE (L.offline.shape.dpLoc D.pT) + 1) = b1 at mT ⊢
  generalize D.no.L * (max D.dE (L.link.shape.dpLoc D.pL) + 1) = b2 at mL ⊢
  generalize D.no.O * (max D.dE (L.onlineBatch.loc.shape.dpB L.onlineBatch.ann D.pB) + 1) = b3 at mB ⊢
  omega

end Compile.Batch
