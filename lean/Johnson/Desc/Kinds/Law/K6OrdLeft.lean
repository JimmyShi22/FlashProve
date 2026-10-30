--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/K6OrdLeft.lean: the assemblies at one record (Law/K6Cut.lean's k06_ord,
Law/K6Tie.lean's k06_ord_tie) from what stands in front of the block that a lot seats.

Law/K6Cut.lean's k6OwnCutBy, at a block that meets Law/K6Steps.lean's record as the seated value
does (k6Steps_seated), has K6Left as its condition in front. The two assemblies, which
spend the item that the block closes, ask K6On: three clauses more. Inside the block's own law these
are paid by the plan's yes and by the step's yes; whoever spends the closed item later has no step
in hand. Here the three are taken from the plan's yes and from the record's own test on the request.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law; the last two in Came).
  k6On_of_start: seatedClaims W l ms = some b, b.planOk = true, startOk W s = true and K6Left W s
      give K6On W s. (Law/SeatedSays.lean's k6On_seated takes the test on the request from a step's
      yes.)
  k06_ord_left, k06_ord_tie_left: the two assemblies with K6On replaced by these four.

Every letter under "there is": none.
What it does not say. THAT startOk W s0 HOLDS: it is the carried record's own test on the request's
words (S.reqOk at the kind's numbers): at the border in front of the head's block the table's
public item on the request is meant to give it: not shown. All that the two assemblies do not say.
Nothing on soundness.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.K6Tie

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model.Verify (borderOf)
open Inst.Model.Layout (kRef hRef)
open VerifiableInference.OnPublicFiles.Flat (GE Holds)
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT)


/-- **K6On, from the plan's yes, the record's test on the request, and K6Left.** -/
theorem k6On_of_start {W : OnBytes.Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) (hp : b.planOk = true) {s : S}
    (hs : startOk W s = true) (hL : K6Left W s) : K6On W s := by
  obtain ⟨hok, hl⟩ := seatedClaims_plan h hp
  rw [laidOk_is] at hl
  exact ⟨hL.1, hok, (laid_says _ _ hl).1, start_pays W s hs, hL.2.1, hL.2.2⟩

namespace Came

/-- **Law/K6Cut.lean's assembly, from what stands in front of the seated block.** -/
theorem k06_ord_left {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
    (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
    (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
    (pl : Nat → Nat × Bool × Nat × Nat) (hr0 : rows ≤ hRef) (hc0 : cols ≤ 2 ^ kRef) (s0 : S)
    (y : Nat) (x : Inst.Model.Instance Inst.Model.ppref) (i : Cm.Idx) (tab : Nat → Nat)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) {mB : List (Nat × Nat)}
    {b6 : Block S Claim} (hb6 : seatedClaims Wp 24 mB = some b6) (hplan : b6.planOk = true)
    (hstart : startOk Wp s0 = true) (hL : K6Left Wp s0)
    (hin : K6In Wp s0 (compCut cs arr msR N s seat Wp pl w))
    (hy : Reply.token (seatAt Wp.hS (readsOf Wp)).toSeat s0 = some y)
    (hlook : LookCallsAt Wp tab s0 y (compCut cs arr msR N s seat Wp pl w).1)
    (hrider : RiderAt Wp s0 y (compCut cs arr msR N s seat Wp pl w).1)
    (hSm : OnBytes.Road.Hd.SmallH Wp.hS Wp.HLy (borderOf Wp.y) (P5J.ownQ cs arr msR N s seat w 24))
    (hF : OnBytes.Road.Hd.FullH Wp.hS) (hNum : OnBytes.Road.Hd.NumH Wp.hS Wp.HLy)
    (hBd : OnBytes.Road.Hd.BorderH (borderOf Wp.y)) (h8 : Wp.hS.digSh = 8) (hr : s0.rowR = x.r)
    (he : s0.rowE = x.e) (htok : ∀ t, t < 1024 → s0.tokv.getD t 0 = x.tok t) (hyx : y = x.y.val)
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u) (hH : Holds w.cells i)
    (hy0 : x.e < Inst.Model.ppref.T → ((x.y.val : Nat) : ZMod Cb.Gl.p) = 0) :
    OnBytes.Road.Hd.HeadOrdLB Wp.hS Wp.HLy Wp.y (OnBytes.Road.Hd.npOf Wp.hS)
      (OnBytes.Road.Hd.polOf Wp.hS) i.mat x (P5J.ownQ cs arr msR N s seat w 24) :=
  k06_ord cs arr msR N s seat Wp pl hr0 hc0 s0 y x i tab w (k6On_of_start hb6 hplan hstart hL) hin
    hy hlook hrider hSm hF hNum hBd h8 hr he htok hyx htab hH hy0

/-- **Law/K6Tie.lean's assembly, likewise.** -/
theorem k06_ord_tie_left {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
    (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
    (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
    (pl : Nat → Nat × Bool × Nat × Nat) (hr0 : rows ≤ hRef) (hc0 : cols ≤ 2 ^ kRef) (s0 : S)
    (y : Nat) (x : Inst.Model.Instance Inst.Model.ppref) (i : Cm.Idx) (tab : Nat → Nat)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (cL : NCells) {mB : List (Nat × Nat)}
    {b6 : Block S Claim} (hb6 : seatedClaims Wp 24 mB = some b6) (hplan : b6.planOk = true)
    (hstart : startOk Wp s0 = true) (hL : K6Left Wp s0)
    (hin : K6In Wp s0 (compCut cs arr msR N s seat Wp pl w))
    (hy : Reply.token (seatAt Wp.hS (readsOf Wp)).toSeat s0 = some y)
    (hsame : SameAt Wp cL (compCut cs arr msR N s seat Wp pl w).1)
    (hlook : LookCallsAt Wp tab s0 y cL) (hrider : RiderAt Wp s0 y cL)
    (hSm : OnBytes.Road.Hd.SmallH Wp.hS Wp.HLy (borderOf Wp.y) (P5J.ownQ cs arr msR N s seat w 24))
    (hF : OnBytes.Road.Hd.FullH Wp.hS) (hNum : OnBytes.Road.Hd.NumH Wp.hS Wp.HLy)
    (hBd : OnBytes.Road.Hd.BorderH (borderOf Wp.y)) (h8 : Wp.hS.digSh = 8) (hr : s0.rowR = x.r)
    (he : s0.rowE = x.e) (htok : ∀ t, t < 1024 → s0.tokv.getD t 0 = x.tok t) (hyx : y = x.y.val)
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u) (hH : Holds w.cells i)
    (hy0 : x.e < Inst.Model.ppref.T → ((x.y.val : Nat) : ZMod Cb.Gl.p) = 0) :
    OnBytes.Road.Hd.HeadOrdLB Wp.hS Wp.HLy Wp.y (OnBytes.Road.Hd.npOf Wp.hS)
      (OnBytes.Road.Hd.polOf Wp.hS) i.mat x (P5J.ownQ cs arr msR N s seat w 24) :=
  k06_ord_tie cs arr msR N s seat Wp pl hr0 hc0 s0 y x i tab w cL
    (k6On_of_start hb6 hplan hstart hL) hin hy hsame hlook hrider hSm hF hNum hBd h8 hr he htok hyx
    htab hH hy0

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6On_of_start
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k06_ord_left
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k06_ord_tie_left
