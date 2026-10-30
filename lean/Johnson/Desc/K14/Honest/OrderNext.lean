-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Honest/OrderNext.lean: the eight sub-protocols of the linear claim's shared rounds:
a statement that is in order stays in order.

That a statement is in order (OnBytes.Means.InOrder) is what makes a constraint say the same when
the statement grows. It is public: it hangs on no value that a prover sends.
Johnson/Desc/K14/Honest/ItemsEach.lean has it only as one half of AllMet, under premises on what is
shown. Here it is handed on by each of the eight wherever that sub-protocol's function returns. A
sending asks beside: its kind's test on the plan, and rounds that fit; "SPLIT": two codes.

Main names:
  order_next1, order_next3, order_next4, order_next6, order_next7, order_next8   at a place's
                      function that returns
  order_nextSend      at a sending (the library's send_order: Johnson/Desc/Key/Laid/SendLaid.lean)
  Public8.order1, …, order8   along a run, from the run up to there
                      (Johnson/Desc/K14/Honest/RunsTo.lean)

What is not claimed. That a run is there. Nothing on what the statement's constraints say. Nothing
on soundness, on completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.RunsTo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Means (InOrder)
open VerifiableInference.Desc (roundsFit)
open VerifiableInference.Desc.K1 (planOkOwn)
open VerifiableInference.Desc.Key.LaidW (inFrontOf send_order)
open Desc.K14.Law (linZeta_inv split_inv)

/-! ## Sub-protocol by sub-protocol, at any state -/

/-- **"LIN point"**: where its function returns, a statement in order stays in order. -/
theorem order_next1 (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : linPoint p d rs = some d')
    (hI : InOrder d.st) : InOrder d'.st := by
  unfold linPoint at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨u0, _, ⟨gU, d1⟩, h1, h2⟩ := h
    have k1 := Means.newGroupP_keeps h1 hI
    split at h2
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
      obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
      show InOrder d2.st
      exact Means.newGroupP_keeps h3 k1
    · simp only [Option.bind_some, Option.some.injEq] at h2
      subst h2
      exact k1
  · cases h

/-- **A sending**: where decideSend has returned and the note is made, a statement in order stays in
order. -/
theorem order_nextSend {Q : VerifiableInference.Desc.K1.Par} {note : St → Array Nat → Option St}
    {d d' : St} {ra rb : Fmt.RoundView} {x : DState (Array Nat)} {ids : Array Nat}
    (h : SentTo Q note d d' ra rb x ids) (hB : planOkOwn Q = true)
    (hf : roundsFit (VerifiableInference.Desc.K1.rounds Q) [ra, rb] = true) (hI : InOrder d.st) :
    InOrder d'.st := by
  rw [h.st]
  exact send_order Q none (inFrontOf d) x ra rb ids hB hf h.sent hI

/-- **"(rec_gamma)"**: where its function returns, a statement in order stays in order. -/
theorem order_next3 (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : laysRec p d rs = some d')
    (hI : InOrder d.st) : InOrder d'.st := by
  unfold laysRec at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨u0, _, d1, hj, rows, _, ha⟩ := h
  exact Means.addRowsP_keeps ha (Means.joinP_keeps hj hI)

/-- **"LOC"**: where its function returns, a statement in order stays in order. -/
theorem order_next4 (p : Par) (d d' : St) (r : Fmt.RoundView) (cols : List (Nat × List UInt64))
    (h : loc p d [r] [cols] = some d') (hI : InOrder d.st) : InOrder d'.st := by
  unfold loc at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨rows, _, ha⟩ := h
  exact Means.addRowsP_keeps ha hI

/-- **The joinings**: where their function returns, a statement in order stays in order. -/
theorem order_next6 (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : joins p d rs = some d')
    (hI : InOrder d.st) : InOrder d'.st := by
  unfold joins at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨u0, _, d1, h1, h2⟩ := h
  have k1 := Means.joinP_keeps h1 hI
  split at h2
  · simp only [Option.bind_eq_some_iff] at h2
    obtain ⟨d2, h3, h4⟩ := h2
    exact Means.joinP_keeps h4 (Means.joinP_keeps h3 k1)
  · simp only [Option.some.injEq] at h2
    subst h2
    exact k1

/-- **"LIN zeta"**: it leaves the statement. -/
theorem order_next7 (d d' : St) (r : Fmt.RoundView) (h : linZeta d [r] = some d') (hI : InOrder d.st) :
    InOrder d'.st := by
  rw [linZeta_inv d d' r h]
  exact hI

/-- **"SPLIT"**, where the shape has two codes: where its function returns, a statement in order
stays in order. -/
theorem order_next8 (p : Par) (hS : p.S.sharedSplitNeeded = true) (d d' : St) (r : Fmt.RoundView)
    (h : split p d [r] = some d') (hI : InOrder d.st) : InOrder d'.st := by
  obtain ⟨row, x, G, kappa, d₁, d₂, _, _, _, _, hk, h2, h3⟩ := split_inv p d d' r hS h
  exact (Means.addRowP_keeps h3 (Means.addRowP_keeps h2 (Means.takeMaskP_keeps hk hI)).1).1

/-! ## Along a run, from the run up to each sub-protocol -/

variable {P : P14} {sentU : Array OracleNotice} {layO : TreeLay} {d0 : St} {V : View8}
  {D : States8}

/-- Behind "LIN point" the statement is in order, if the first one is. -/
theorem Public8.order1 (_S : Public8 P sentU layO d0) (u : To1 P d0 V D) (h0 : InOrder d0.st) :
    InOrder D.d1.st :=
  order_next1 P.par d0 D.d1 _ u.k1 h0

/-- Behind the sending of o_u the statement is in order, if the first one is. -/
theorem Public8.order2 (S : Public8 P sentU layO d0) (u : To2 P sentU d0 V D)
    (h0 : InOrder d0.st) : InOrder D.d2.st :=
  order_nextSend u.s2 S.planU u.fitsU (S.order1 u.front h0)

/-- Behind "(rec_gamma)" the statement is in order, if the first one is. -/
theorem Public8.order3 (S : Public8 P sentU layO d0) (u : To3 P sentU d0 V D)
    (h0 : InOrder d0.st) : InOrder D.d3.st :=
  order_next3 P.par D.d2 D.d3 _ u.k3 (S.order2 u.front h0)

/-- Behind "LOC" the statement is in order, if the first one is. -/
theorem Public8.order4 (S : Public8 P sentU layO d0) (u : To4 P sentU d0 V D)
    (h0 : InOrder d0.st) : InOrder D.d4.st :=
  order_next4 P.par D.d3 D.d4 _ _ u.k4 (S.order3 u.front h0)

/-- Behind the sending of o_omega and o_sp the statement is in order, if the first one is. -/
theorem Public8.order5 (S : Public8 P sentU layO d0) (u : To5 P sentU d0 V D)
    (h0 : InOrder d0.st) : InOrder D.d5.st :=
  order_nextSend u.s5 S.planO u.fitsO (S.order4 u.front h0)

/-- Behind the joinings the statement is in order, if the first one is. -/
theorem Public8.order6 (S : Public8 P sentU layO d0) (u : To6 P sentU d0 V D)
    (h0 : InOrder d0.st) : InOrder D.d6.st :=
  order_next6 P.par D.d5 D.d6 _ u.k6 (S.order5 u.front h0)

/-- Behind "LIN zeta" the statement is in order, if the first one is. -/
theorem Public8.order7 (S : Public8 P sentU layO d0) (u : To7 P sentU d0 V D)
    (h0 : InOrder d0.st) : InOrder D.d7.st :=
  order_next7 D.d6 D.d7 _ u.k7 (S.order6 u.front h0)

/-- Behind "SPLIT" the statement is in order, if the first one is. -/
theorem Public8.order8 (S : Public8 P sentU layO d0) (u : To8 P sentU d0 V D)
    (h0 : InOrder d0.st) : InOrder D.d8.st :=
  order_next8 P.par S.facts.two D.d7 D.d8 _ u.k8 (S.order7 u.front h0)

end Desc.K14.Honest

#print axioms Desc.K14.Honest.order_next1
#print axioms Desc.K14.Honest.order_nextSend
#print axioms Desc.K14.Honest.order_next3
#print axioms Desc.K14.Honest.order_next4
#print axioms Desc.K14.Honest.order_next6
#print axioms Desc.K14.Honest.order_next7
#print axioms Desc.K14.Honest.order_next8
#print axioms Desc.K14.Honest.Public8.order1
#print axioms Desc.K14.Honest.Public8.order2
#print axioms Desc.K14.Honest.Public8.order3
#print axioms Desc.K14.Honest.Public8.order4
#print axioms Desc.K14.Honest.Public8.order5
#print axioms Desc.K14.Honest.Public8.order6
#print axioms Desc.K14.Honest.Public8.order7
#print axioms Desc.K14.Honest.Public8.order8
