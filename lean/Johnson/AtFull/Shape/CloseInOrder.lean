-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/CloseInOrder.lean: THE CLOSING OF A SEGMENT (kind K10), AT ALL 25 LINKS OF THE
PROOF FILE's OWN FIRST CHAIN, IN THE FRAME's OWN FORM, WITH A LIGHTER TEST ON VALUES; AND THAT TEST
ACCEPTS AT EVERY REACHED STATE. Under the head `P5J.AtMgA`; a joining of laws; nothing is evaluated.

What it does. CloseFrames.lean has two of the premises that the rule for acceptance asks, `Carries`
and `Returns` (Johnson/Desc/ProofFile/Honest/Thread/Shape.lean), at the 25 closings, with the test
on values `closeOrdB` (Johnson/Desc/K10/Honest/AtPair.lean): every tensor of every row that goes
into the batching passes `Tensor.ok`. The law beneath spends less: that these rows are in order
(`OrderRow`, OnBytes/Slice/BlkProxOrder.lean: each written-out variable is named once and has the
pair (1, 1)); `Tensor.ok`'s other two clauses (at most 63 variables; the slice lies inside its
vector) are not spent. Here the test is cut to what is spent, the frame is shown anew at the lighter
test, and the lighter test is shown to accept at every state that the chain reaches at a border up
to the last code switch (TakenRowsOrder.lean). Each closing's number is such a border (`ixK10_le`).
So at a state that is reached in front of a closing, with the test on the words in front of each
decision, the test on values is no matter of the prover's values or of the draws.

Main names.
* `inOrdB`, `inOrdB_iff`; `rowInOrdB`, `rowInOrdB_iff`: "in order" with code, of a tensor and of a
  row; each says yes just where the library's sentence holds.
* `closeInOrdB t`: each row that goes into the batching at the live frame's group is in order.
  `closeInOrdB_of_ordB`: it asks less than `closeOrdB`. `inOrd_gives`: what it gives at the record's
  own data.
* `close_frame_ord` (l < 25): CloseFrames.lean's `close_frame` to the letter, but for the test: for
  every table vals with vals (LPFK10.ixK10 l) s rs gs = closeInOrdB s. "Returns" by `yields_gives`
  (AtPair.lean) and `close_returnsM` (Johnson/Desc/K10/Honest/AtMakes.lean), called directly.
* `closeInOrdB_reached`: under the head, k ≤ 353: closeInOrdB s = true at every state s reached at
  border k.
* `ixK10_le`: LPFK10.ixK10 l ≤ 353 for l < 25. `closeInOrdB_at_closing`: so the test accepts at
  every state reached at border LPFK10.ixK10 l.

Limits. TWO OF THE PREMISES OF THE RULE AT 25 OF 358 MEMBERS. G and vals are letters: no table is
laid here. close_frame_ord does not say that a member stands at LPFK10.ixK10 l (its proof has it,
from closing_atF): where none stood, `Carries` and `Returns` would say nothing: both begin "for
every member at that number". "Returns" stands under "the step on shapes returns", which is shown of
no state. "REACHED" IS TAKEN WITH THE TEST ON THE WORDS IN FRONT OF EACH DECISION (`Reach 0
(cF.blocksInOrder.map below) …`); whoever holds a state in another form owes that. THE RULE's OWN ROAD HANDS
A REACH OVER IN ANOTHER FORM (inside shape_at, Thread/Shape.lean: `Reach T.ft T.bs (fun _ : Unit =>
s₀) b ((), s)`). Here the first tree's number is 0, the blocks are `below b`, the start is
ProofFile.startS Zp, and what is reached is a pair (p, s) with p : ProofFile.InstPub. NO THEOREM OF THIS FILE
JOINS THE ACCEPTANCE TO THE RULE's PREMISE `Values`. That the head has a member is shown in scope,
where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that
these three hold together, at two named sets of public files, in a side library. At the format's
second hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.TakenRowsOrder
import Johnson.AtFull.Shape.CloseFrames
import Johnson.Desc.Own.ShapesAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Slice.ProxRun (OrderRow OrderForm)
open VerifiableInference.Desc (Block Chain noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest (Carries Returns carries_seat returns_seat)
open ProofFile.Honest.K10.YesFree

/-! ## 1 "In order" with code -/

/-- Each written-out variable of the tensor is named once and has the pair (1, 1). -/
def inOrdB (v : Tensor) : Bool :=
  distinctNats v.denseVars && v.denseVars.all fun d => v.pairs[d]? == some (oneE, oneE)

/-- The test says yes just where the tensor is in order. -/
theorem inOrdB_iff (v : Tensor) : inOrdB v = true ↔ v.InOrder := by
  unfold inOrdB Tensor.InOrder
  rw [Bool.and_eq_true, VerifiableInference.Desc.Own.distinct_agrees, decide_eq_true_iff,
    List.all_eq_true]
  exact ⟨fun h => ⟨h.1, fun d hd => beq_iff_eq.1 (h.2 d hd)⟩,
    fun h => ⟨h.1, fun d hd => beq_iff_eq.2 (h.2 d hd)⟩⟩

/-- Every tensor among the row's terms and in its forms is so. -/
def rowInOrdB (r : OnBytes.Row) : Bool :=
  (r.terms.toList.all fun t => inOrdB t.v) && r.forms.toList.all fun f => f.c.tensors.all inOrdB

/-- The test says yes just where the row is in order. -/
theorem rowInOrdB_iff (r : OnBytes.Row) : rowInOrdB r = true ↔ OrderRow r := by
  unfold rowInOrdB OrderRow OrderForm
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  exact ⟨fun h => ⟨fun t ht => (inOrdB_iff _).1 (h.1 t ht),
      fun f hf v hv => (inOrdB_iff _).1 (List.all_eq_true.1 (h.2 f hf) v hv)⟩,
    fun h => ⟨fun t ht => (inOrdB_iff _).2 (h.1 t ht),
      fun f hf => List.all_eq_true.2 fun v hv => (inOrdB_iff _).2 (h.2 f hf v hv)⟩⟩

/-- **THE CLOSING's TEST ON VALUES, CUT TO WHAT ITS LAW SPENDS**: each row that goes into the
batching at the live frame's group is in order. Yes where there is no such group. -/
def closeInOrdB (t : S) : Bool :=
  match t.st.groups[(VerifiableInference.Desc.K9.recOf t).frame.group]? with
  | some G => (runRows t.st G).toList.all rowInOrdB
  | none => true

/-- It asks less than the test with Tensor.ok. -/
theorem closeInOrdB_of_ordB {t : S} (h : closeOrdB t = true) : closeInOrdB t = true := by
  unfold closeOrdB at h
  unfold closeInOrdB
  split
  · rename_i G hG
    rw [hG] at h
    exact List.all_eq_true.2 fun r hr =>
      (rowInOrdB_iff r).2 (rowOrder_of (List.all_eq_true.1 h r hr))
  · rfl

/-- What it gives at the record's own data. -/
theorem inOrd_gives {t : S} {D : BaseData}
    (hD : baseData (VerifiableInference.Desc.K9.recOf t) = some D) (hO : closeInOrdB t = true) :
    ∀ r ∈ (runRows t.st D.G).toList, OrderRow r := by
  obtain ⟨_, _, _, h4⟩ := baseData_some hD
  unfold closeInOrdB at hO
  have h4' : t.st.groups[(VerifiableInference.Desc.K9.recOf t).frame.group]? = some D.G := h4
  rw [h4'] at hO
  exact fun r hr => (rowInOrdB_iff r).1 (List.all_eq_true.1 hO r hr)

/-! ## 2 The frame -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE CLOSING OF A SEGMENT, AT ALL 25 LINKS, IN THE FRAME's OWN FORM, AT THE LIGHTER TEST.** -/
theorem close_frame_ord (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (p : VerifiableInference.Desc.K9.Where) (Q : Par),
      IM.k9At Zp l = some p ∧ ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) p = some Q ∧
      ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (LPFK10.ixK10 l) = optE (closeGF Q) →
        (∀ s rs gs, vals (LPFK10.ixK10 l) s rs gs = closeInOrdB s) →
        Carries cF.blocksInOrder ft (firstZA G vals) (LPFK10.ixK10 l) ∧
          Returns cF.blocksInOrder ft (firstZA G vals) (LPFK10.ixK10 l) := by
  obtain ⟨p, Q, b, hp, hQ, hn, hb, hf, hc, -, -⟩ := closing_atF h l hl
  refine ⟨p, Q, hp, hQ, fun ft G vals hG hv => ⟨?_, ?_⟩⟩
  · refine carries_seat hn fun rs cols _ s s' u hd hu => ?_
    have hu' : G (LPFK10.ixK10 l) (shA s) = .ok u := hu
    rw [hG] at hu'
    have hd' : closeGF Q (shA s) = some (chainF s') := hc s s' _ _ hd
    exact Option.some.inj ((optE_ok.1 hu').symm.trans hd')
  · refine returns_seat hn fun rs cols hF s u hu hvv => ?_
    have hu' : G (LPFK10.ixK10 l) (shA s) = .ok u := hu
    rw [hG] at hu'
    have hvv' : vals (LPFK10.ixK10 l) s (rs.map noDigest) (b.shown ft rs cols) = true := hvv
    rw [hv] at hvv'
    obtain ⟨f1, f2⟩ := (hf ft rs cols).1 hF
    obtain ⟨hGB, Dd, hD, hV⟩ := yields_gives (optE_ok.1 hu')
    rw [hb]
    exact close_returnsM hD hGB hV (inOrd_gives hD hvv') _ _ (by rw [List.length_map]; exact f1)
      (shapedAll_noDigest f2)

/-- **THE LIGHTER TEST ACCEPTS AT EVERY STATE THAT IS REACHED AT A BORDER UP TO THE LAST CODE
SWITCH.** -/
theorem closeInOrdB_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : Nat} (hk : k ≤ 353)
    {p : ProofFile.InstPub} {s : S} (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k (p, s)) :
    closeInOrdB s = true := by
  unfold closeInOrdB
  split
  · rename_i G hG
    exact List.all_eq_true.2 fun q hq => (rowInOrdB_iff q).2 (taken_order_reached h hk hr hG q hq)
  · rfl

/-- The closings stand in front of the last code switch. -/
theorem ixK10_le (l : Nat) (hl : l < 25) : LPFK10.ixK10 l ≤ 353 := by
  unfold LPFK10.ixK10
  rw [IM.hear_len_at]
  split <;> omega

/-- **SO IT ACCEPTS AT EVERY STATE THAT IS REACHED IN FRONT OF A CLOSING.** -/
theorem closeInOrdB_at_closing (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25)
    {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (LPFK10.ixK10 l) (p, s)) :
    closeInOrdB s = true :=
  closeInOrdB_reached h (ixK10_le l hl) hr

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.inOrdB_iff
#print axioms Johnson.AtFull.Shape.rowInOrdB_iff
#print axioms Johnson.AtFull.Shape.closeInOrdB_of_ordB
#print axioms Johnson.AtFull.Shape.inOrd_gives
#print axioms Johnson.AtFull.Shape.close_frame_ord
#print axioms Johnson.AtFull.Shape.closeInOrdB_reached
#print axioms Johnson.AtFull.Shape.ixK10_le
#print axioms Johnson.AtFull.Shape.closeInOrdB_at_closing
#print axioms Johnson.AtFull.Shape.inOrdB
#print axioms Johnson.AtFull.Shape.rowInOrdB
#print axioms Johnson.AtFull.Shape.closeInOrdB
