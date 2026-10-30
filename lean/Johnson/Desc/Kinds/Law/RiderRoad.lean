-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RiderRoad.lean: THE RIDER's ROAD: FROM WHAT THE OUTPUT HEAD's LAW CLOSES IN
FRONT OF ITS OWN BLOCK ON THE TWO GUESTS (Law/RowFront.lean: FrontRider: the two sums under the
weights of the lookup's point on the positions are 0) TO THE SENTENCE THAT THE TABLE OF JOINTS'
FILLING HOLDS AT worth m 3 "rider" AT THE HEAD (Johnson/Top/H/K3RowOutRider.lean: K3OutRider, at the
closed caller with its riders: Johnson/Desc/First/Look/K3CallerHead.lean: headRider).
Statements and proofs.

  heardPt g        the key point that what the lookup heard pins (rider_of_point: "it
                   needs no rounds and no ledger").
  atCoords_two     at any caller with two arrays over the positions: both worth 0 under the weights
                   of a point's tail: the riders' clause at that point.
  outRider_of_sums the two sums at the closed caller's own cells (headCells ... m), at a point zt of
                   lt coordinates that is the tail of heardPt g: K3OutRider.
  sums_same        the two sums hang on what the head's relation names of the cells alone.
  isTail_last      the last n coordinates of the heard first point are the tail of heardPt.
  outRider_of_front   MAIN: FrontRider at a verifier's state and cells c; what the lookup has heard
                   there; the heard token; c and the closed caller's cells agree on what the
                   relation names (hL1); the first point's size: K3OutRider at the kind's letters
                   of the state.
  rider_arm        the same in the shape of the filling's arm "rider".

WHAT IT IS NOT. Implications. ONE NAMED PREMISE THAT NOBODY PAYS: **hL1**: SameCells c (headCells
... m): two readings of one witness's messages (at c := the cells that compCut reads off the
witness: owed by K6's and K7's files with the lookup's). THE TAIL (IsTail: the text's point on the
positions, read, is the last lt places of the key point) IS PAID HERE DOWN TO A SIZE (isTail_last):
left: the heard first point has x.fs.dT coordinates, and lt is no more than that. The tests on the
plan. WHAT WAS HEARD IS WHAT S.lookHeard? SHOWS: the table's filling's reader heardC is
that reader, by an abbreviation (First/Look/K3FillWorth.lean: by reading). THE TOKEN is the one that
Reply.token shows at the seat; the filling has S.replyTok?'s, or 0. That
the kind's letters of the state are the table's (its Request is "of the public part") is the
promise's clause on the request's words. Nothing on soundness.
LETTERS. gk, y0: tied by the state's own readers.

-/
import Mathlib
import Johnson.Desc.First.Look.K3CallerHead
import Johnson.Top.H.K3RowOutRider
import Johnson.Desc.Kinds.Law.CellsAlike
import Johnson.Desc.Kinds.Law.RowFront
import Johnson.Desc.Kinds.Law.FromGiven

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

/-- The key point that what the lookup heard pins: its two points, read, one behind the
other. -/
def heardPt (g : OnBytes.Model.Forest.Heard) : ℕ → Cb.Gl.E :=
  fun t => (_root_.Fo.rdA Reading.gl g.zx ++ _root_.Fo.rdA Reading.gl g.zy).getD t 0

/-- **THE TAIL, PAID DOWN TO A SIZE**: the last n coordinates of the heard first point are
the tail of the key point that it pins, where that first point has dT coordinates. -/
theorem isTail_last (g : OnBytes.Model.Forest.Heard) (n dT : ℕ) (hs : g.zx.size = dT)
    (hn : n ≤ dT) : IsTail Reading.gl (Point.last g.zx n) (heardPt g) dT := by
  have hl := Came.toList_last g.zx n
  have hsz : (Point.last g.zx n).size = n := by
    have h1 := congrArg List.length hl
    rw [Array.length_toList, List.length_drop, Array.length_toList] at h1
    omega
  intro t ht
  rw [hsz] at ht ⊢
  have hi : dT - n + t < g.zx.toList.length := by
    rw [Array.length_toList]
    omega
  have e1 : (Point.last g.zx n).getD t OnBytes.zeroE = g.zx.toList[dT - n + t] := by
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hl, List.getElem?_drop, hs,
      List.getElem?_eq_getElem hi]
    rfl
  rw [e1]
  unfold heardPt _root_.Fo.rdA
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [List.length_map]; exact hi),
    List.getElem?_map, List.getElem?_eq_getElem hi]
  rfl

/-- **AT ANY CALLER WITH TWO ARRAYS OVER THE POSITIONS**: where both are worth 0 under the equality
weights of the tail of a point: the riders' clause at that point. -/
theorem atCoords_two {c : LookupCCaller} (n : ℕ) (r1 r2 : List c.Sg.O)
    (g1 g2 : c.St₀ → c.Sg.Msg → ℕ → Cb.Gl.E) (st : c.St₀) (m : c.Sg.Msg) (pt : ℕ → Cb.Gl.E)
    (h1 : ∑ t ∈ Finset.range (2 ^ n),
      Blocks.eqN n 0 (fun t => pt (c.h.dT - n + t)) t * g1 st m t = 0)
    (h2 : ∑ t ∈ Finset.range (2 ^ n),
      Blocks.eqN n 0 (fun t => pt (c.h.dT - n + t)) t * g2 st m t = 0) :
    Cb.Rider.AtCoords (riderOf c (tailIds n [(r1, g1), (r2, g2)])).g
      (riderOf c (tailIds n [(r1, g1), (r2, g2)])).sel
      (riderOf c (tailIds n [(r1, g1), (r2, g2)])).f st pt m := by
  intro i
  obtain ⟨k, hk⟩ := i
  have hk2 : k < 2 := hk
  interval_cases k
  · exact (tailId_val n r1 g1 st m pt).trans h1
  · exact (tailId_val n r2 g2 st m pt).trans h2

section Classes

variable [Sizes] [Policy] [Request]
variable (adr : HeadAdr) (x : First.Look.Place) (tl : HTailF2) (D : Sent) (rad : OracleShape → ℕ)
  (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ) (Ex : Iop.ExtSpec)
  (Wp : Type)

/-- The guest clip's sum under the weights of a point on the positions, at a token. -/
def clipSum (y : ℕ) (zt : Point) (c : Cells) : E :=
  letI : Token := ⟨y⟩
  ∑ t < T, eq zt t * clipAt c (corner 0 t)

/-- The guest table's. -/
def tableSum (y : ℕ) (zt : Point) (c : Cells) : E :=
  letI : Token := ⟨y⟩
  ∑ t < T, eq zt t * tableAt c (corner 0 t)

theorem rd_clipSum (y : ℕ) {zt : Point} {pt : ℕ → K} {dT : ℕ} (h : IsTail Reading.gl zt pt dT)
    (hz : zt.size = lt) (c : Cells) :
    rd (clipSum y zt c) = ∑ t ∈ Finset.range (2 ^ lt),
      Blocks.eqN lt 0 (fun s => pt (dT - lt + s)) t *
        (letI : Token := ⟨y⟩
         rd (clipAt c (corner 0 t))) :=
  letI : Token := ⟨y⟩
  rd_outSum h hz fun t => clipAt c (corner 0 t)

theorem rd_tableSum (y : ℕ) {zt : Point} {pt : ℕ → K} {dT : ℕ} (h : IsTail Reading.gl zt pt dT)
    (hz : zt.size = lt) (c : Cells) :
    rd (tableSum y zt c) = ∑ t ∈ Finset.range (2 ^ lt),
      Blocks.eqN lt 0 (fun s => pt (dT - lt + s)) t *
        (letI : Token := ⟨y⟩
         rd (tableAt c (corner 0 t))) :=
  letI : Token := ⟨y⟩
  rd_outSum h hz fun t => tableAt c (corner 0 t)

/-- **FROM THE TWO SUMS AT THE CLOSED CALLER's OWN CELLS TO THE ROW OUT's FOURTH ITEM.** -/
theorem outRider_of_sums (y : ℕ) (m : (laySg x D rad oW).Msg) (g : OnBytes.Model.Forest.Heard)
    (F' : Fork) (zt : Point) (hz : zt.size = lt)
    (hTail : IsTail Reading.gl zt (heardPt g) x.fs.dT)
    (h1 : clipSum y zt (headCells adr x tl D rad oW wOf nr nc m).toCells = 0)
    (h2 : tableSum y zt (headCells adr x tl D rad oW wOf nr nc m).toCells = 0) :
    K3OutRider (headRider adr x tl D rad oW wOf nr nc Ex Wp) x.lm x.F.next y m g F' := by
  have e1 := rd_clipSum y hTail hz (headCells adr x tl D rad oW wOf nr nc m).toCells
  have e2 := rd_tableSum y hTail hz (headCells adr x tl D rad oW wOf nr nc m).toCells
  rw [h1, rd_zero] at e1
  rw [h2, rd_zero] at e2
  have hA := atCoords_two (c := headCaller adr x tl D rad oW wOf nr nc Ex Wp) lt (allO x D rad oW)
    (allO x D rad oW) (headClip adr x tl D rad oW wOf nr nc) (headTable adr x tl D rad oW wOf nr nc)
    y m (heardPt g) e1.symm e2.symm
  exact rider_of_point (headRider adr x tl D rad oW wOf nr nc Ex Wp) x.lm x.F.next y m g F' hA

/-- The two sums hang on what the head's relation names of the cells alone. -/
theorem sums_same (y : ℕ) (c c' : NCells) (h : SameCells c c') (P : PlanFacts) (zt : Point) :
    clipSum y zt c.toCells = clipSum y zt c'.toCells ∧
      tableSum y zt c.toCells = tableSum y zt c'.toCells :=
  letI : Token := ⟨y⟩
  ⟨Came.sumTo_congr T fun t ht => by rw [Came.clip_same h ht],
    Came.sumTo_congr T fun t ht => by rw [Came.table_same h P ht]⟩

end Classes

section Front

variable (adr : HeadAdr) (x : First.Look.Place) (tl : HTailF2) (D : Sent) (rad : OracleShape → ℕ)
  (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ) (Ex : Iop.ExtSpec)
  (Wp : Type)

/-- **THE RIDER's ROAD.** -/
theorem outRider_of_front (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Par)
    (s : VerifiableInference.Desc.First.S) (c : NCells) (hf : FrontRider p (seatAt h iU3) s c)
    (gk : OnBytes.Model.Forest.Heard) (hk : s.lookHeard? = some gk) (y0 : ℕ)
    (hy : Reply.token (seatAt h iU3).toSeat s = some y0) (F' : Fork)
    (m : (laySg x D rad oW).Msg) :
    letI := p.sizes
    letI := p.policy
    letI : Request := (seatAt h iU3).request s
    PlanFacts → SameCells c (headCells adr x tl D rad oW wOf nr nc m) → gk.zx.size = x.fs.dT →
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
  obtain ⟨e1, e2⟩ := sums_same y c _ hL1 hP (Point.last gk.zx lt)
  have hsz : (Point.last gk.zx lt).size = lt := by
    have q := congrArg List.length (Came.toList_last gk.zx lt)
    rw [Array.length_toList, List.length_drop, Array.length_toList] at q
    omega
  exact outRider_of_sums adr x tl D rad oW wOf nr nc Ex Wp y m gk F' (Point.last gk.zx lt) hsz
    (isTail_last gk lt x.fs.dT hs hn) (e1.symm.trans k1) (e2.symm.trans k2)

/-- **THE SAME IN THE SHAPE OF THE FILLING's ARM "rider"** (First/Look/K3HeadFill.lean: worthHead):
at whatever the state shows as heard, and every ledger, at S.replyTok?'s token or 0. -/
theorem rider_arm (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Par)
    (s : VerifiableInference.Desc.First.S) (c : NCells) (hf : FrontRider p (seatAt h iU3) s c)
    (y0 : ℕ) (hy : Reply.token (seatAt h iU3).toSeat s = some y0) (hr : s.replyTok? = some y0)
    (m : (laySg x D rad oW).Msg) :
    letI := p.sizes
    letI := p.policy
    letI : Request := (seatAt h iU3).request s
    PlanFacts → SameCells c (headCells adr x tl D rad oW wOf nr nc m) →
      (∀ g, s.lookHeard? = some g → g.zx.size = x.fs.dT) → lt ≤ x.fs.dT →
      ∀ (g : OnBytes.Model.Forest.Heard) (F' : Fork), s.lookHeard? = some g →
        K3OutRider (headRider adr x tl D rad oW wOf nr nc Ex Wp) x.lm x.F.next
          (s.replyTok?.getD 0) m g F' := by
  intro hP hL1 hs hn g F' hk
  rw [hr]
  exact outRider_of_front adr x tl D rad oW wOf nr nc Ex Wp h iU3 p s c hf g hk y0 hy F' m hP hL1
    (hs g hk) hn

end Front

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.isTail_last
#print axioms VerifiableInference.Desc.Kinds.Head.Law.atCoords_two
#print axioms VerifiableInference.Desc.Kinds.Head.Law.outRider_of_sums
#print axioms VerifiableInference.Desc.Kinds.Head.Law.sums_same
#print axioms VerifiableInference.Desc.Kinds.Head.Law.outRider_of_front
#print axioms VerifiableInference.Desc.Kinds.Head.Law.rider_arm
