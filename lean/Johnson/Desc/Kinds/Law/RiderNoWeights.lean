-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RiderNoWeights.lean: THE RIDER's ROAD (Law/RiderRoad.lean) WITHOUT THE STORED
WEIGHTS: the two guests clip and table read of the cells their table of integers alone: so the road
asks that the two readings of the cells agree on the four tables of integers, and NOTHING ON THE
WEIGHTS. Statements and proofs.

WHY. At a witness whose stored table holds no index K6's and K7's files' reading of the weights
is 0 and the closed caller's is the lift of two bytes: the two part.
The item "rider" reads no weight: only the bundle SameCells dragged them in.

  SameBut c c'     the two structures of cells agree on what the head's relation names, but for the
                   weights.
  clipAt_cell, tableAt_cell   the two guests at a corner hang on the table of integers alone.
  sums_but         so do the two sums.
  outRider_but, rider_arm_but   Law/RiderRoad.lean's two tops under SameBut.

WHAT IT IS NOT. All that Law/RiderRoad.lean's head says, with SameBut in SameCells' place. Nothing
on soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RiderRoad

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE OracleShape)
open OnBytes.Model (HTailF2 Fork Reading)
open Norm (lt ls d S2 T)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First.Look

section Classes

variable [Sizes] [Policy] [Request]

/-- Two structures of cells agree on what the head's relation names, but for the weights. -/
structure SameBut (c c' : NCells) : Prop where
  wide : ∀ f t, f < 4 * d + 6 * JV → t < T → c.cell .wide f t = c'.cell .wide f t
  act : ∀ f t, f < 2 * d → t < T → c.cell .act f t = c'.cell .act f t
  row : ∀ f t, f < NR + 21 → t < T → c.cell .row f t = c'.cell .row f t
  stream : ∀ f t, f < 5 * d → t < T → c.stream f t = c'.stream f t

theorem SameCells.but {c c' : NCells} (h : SameCells c c') : SameBut c c' :=
  ⟨h.wide, h.act, h.row, h.stream⟩

/-- The guest clip at a corner hangs on the table of integers alone. -/
theorem clipAt_cell [Token] (c c' : Cells) (hc : c.cell = c'.cell) {t : Nat} (ht : t < T) :
    clipAt c (corner 0 t) = clipAt c' (corner 0 t) := by
  refine eq_of_rd (okE_clipAt _ _) (okE_clipAt _ _) ?_
  rw [rd_clip ht, rd_clip ht]
  obtain ⟨cell, Wh⟩ := c
  obtain ⟨cell', Wh'⟩ := c'
  obtain rfl : cell = cell' := hc
  rfl

/-- The guest table's. -/
theorem tableAt_cell [Token] (c c' : Cells) (hc : c.cell = c'.cell) (P : PlanFacts) {t : Nat}
    (ht : t < T) : tableAt c (corner 0 t) = tableAt c' (corner 0 t) := by
  refine eq_of_rd (okE_tableAt _ _) (okE_tableAt _ _) ?_
  rw [rd_table P ht, rd_table P ht]
  obtain ⟨cell, Wh⟩ := c
  obtain ⟨cell', Wh'⟩ := c'
  obtain rfl : cell = cell' := hc
  rfl

/-- The two sums hang on the four tables of integers alone. -/
theorem sums_but (y : ℕ) (c c' : NCells) (h : SameBut c c') (P : PlanFacts) (zt : Point) :
    clipSum y zt c.toCells = clipSum y zt c'.toCells ∧
      tableSum y zt c.toCells = tableSum y zt c'.toCells := by
  have hS : SameCells c { c' with Wh := c.Wh } :=
    ⟨h.wide, h.act, h.row, h.stream, fun _ _ _ _ => rfl⟩
  obtain ⟨e1, e2⟩ := sums_same y c _ hS P zt
  letI : Token := ⟨y⟩
  refine ⟨e1.trans (Came.sumTo_congr T fun t ht => ?_),
    e2.trans (Came.sumTo_congr T fun t ht => ?_)⟩
  · rw [clipAt_cell ({ c' with Wh := c.Wh } : NCells).toCells c'.toCells rfl ht]
  · rw [tableAt_cell ({ c' with Wh := c.Wh } : NCells).toCells c'.toCells rfl P ht]

end Classes

section Front

variable (adr : HeadAdr) (x : First.Look.Place) (tl : HTailF2) (D : Sent) (rad : OracleShape → ℕ)
  (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ) (Ex : Iop.ExtSpec)
  (Wp : Type)

/-- **THE RIDER's ROAD, NOTHING ASKED OF THE WEIGHTS.** -/
theorem outRider_but (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Par)
    (s : VerifiableInference.Desc.First.S) (c : NCells) (hf : FrontRider p (seatAt h iU3) s c)
    (gk : OnBytes.Model.Forest.Heard) (hk : s.lookHeard? = some gk) (y0 : ℕ)
    (hy : Reply.token (seatAt h iU3).toSeat s = some y0) (F' : Fork)
    (m : (laySg x D rad oW).Msg) :
    letI := p.sizes
    letI := p.policy
    letI : Request := (seatAt h iU3).request s
    PlanFacts → SameBut c (headCells adr x tl D rad oW wOf nr nc m) → gk.zx.size = x.fs.dT →
      lt ≤ x.fs.dT →
      K3OutRider (headRider adr x tl D rad oW wOf nr nc Ex Wp) x.lm x.F.next y0 m gk F' := by
  letI := p.sizes
  letI := p.policy
  letI : Request := (seatAt h iU3).request s
  intro hP hL1 hs hn
  obtain ⟨g, hg, h1, h2⟩ := hf
  obtain ⟨z, y, hz, hy', _, rfl⟩ := Came.given_ok p _ s g hg
  obtain rfl : y = y0 := Option.some.inj (hy'.symm.trans hy)
  have hz' : (seatAt h iU3).lookup s = some (gk.zx, fun c => gk.zk.getD c #[]) := by
    show (s.lookHeard?.map fun g => (g.zx, fun c => g.zk.getD c #[])) = _
    rw [hk]
    rfl
  obtain rfl : z = (gk.zx, fun c => gk.zk.getD c #[]) := Option.some.inj (hz.symm.trans hz')
  have k1 : clipSum y (Point.last gk.zx lt) c.toCells = 0 := h1
  have k2 : tableSum y (Point.last gk.zx lt) c.toCells = 0 := h2
  obtain ⟨e1, e2⟩ := sums_but y c _ hL1 hP (Point.last gk.zx lt)
  have hsz : (Point.last gk.zx lt).size = lt := by
    have q := congrArg List.length (Came.toList_last gk.zx lt)
    rw [Array.length_toList, List.length_drop, Array.length_toList] at q
    omega
  exact outRider_of_sums adr x tl D rad oW wOf nr nc Ex Wp y m gk F' (Point.last gk.zx lt) hsz
    (isTail_last gk lt x.fs.dT hs hn) (e1.symm.trans k1) (e2.symm.trans k2)

/-- **THE SAME IN THE SHAPE OF THE FILLING's ARM "rider".** -/
theorem rider_arm_but (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Par)
    (s : VerifiableInference.Desc.First.S) (c : NCells) (hf : FrontRider p (seatAt h iU3) s c)
    (y0 : ℕ) (hy : Reply.token (seatAt h iU3).toSeat s = some y0) (hr : s.replyTok? = some y0)
    (m : (laySg x D rad oW).Msg) :
    letI := p.sizes
    letI := p.policy
    letI : Request := (seatAt h iU3).request s
    PlanFacts → SameBut c (headCells adr x tl D rad oW wOf nr nc m) →
      (∀ g, s.lookHeard? = some g → g.zx.size = x.fs.dT) → lt ≤ x.fs.dT →
      ∀ (g : OnBytes.Model.Forest.Heard) (F' : Fork), s.lookHeard? = some g →
        K3OutRider (headRider adr x tl D rad oW wOf nr nc Ex Wp) x.lm x.F.next
          (s.replyTok?.getD 0) m g F' := by
  intro hP hL1 hs hn g F' hk
  rw [hr]
  exact outRider_but adr x tl D rad oW wOf nr nc Ex Wp h iU3 p s c hf g hk y0 hy F' m hP hL1
    (hs g hk) hn

end Front

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.sums_but
#print axioms VerifiableInference.Desc.Kinds.Head.Law.outRider_but
#print axioms VerifiableInference.Desc.Kinds.Head.Law.rider_arm_but
