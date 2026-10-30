-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/SwitchOnesPlain.lean: THE CODE SWITCH's TEST ON VALUES (`onesV`,
Johnson/Desc/First/Shape/SwitchFrontFits.lean) ACCEPTS AT EVERY STATE THAT THE PROOF FILE's OWN
FIRST CHAIN REACHES AT A BORDER UP TO THE LAST CODE SWITCH, AT THE CARRIED ROWS OF EVERY COPY OF THE
LINKS' FRAME THAT THE STATE HOLDS. Under the head `P5J.AtMgA`; a joining of laws; nothing is
evaluated.

What it does. `onesV T old` asks that at each written-out variable the pair is (1, 1): in the
carried form, in the kept forms, and in the terms of the kept members' stored sample rows. No stored
sample row has a written-out variable at such a state (`SamplesPlain`, TakenRowsOrder.lean): so the
third clause holds there for nothing. The carried form and the kept forms are in order at every
reached state (CarriedRowsOrder.lean): that gives the first two (`onesF_of_order`,
Johnson/Desc/First/Shape/Ones.lean).

Main names.
* `onesT_of_plain`: a tensor without a written-out factor passes the test on the pairs.
* `onesV_of_plain`: GENERAL: SamplesPlain T: onesV T old = (onesF old.c && old.kept.toList.all fun f
  => onesF f.c).
* `onesV_reached`: under the head, k ≤ 353: that equation at every state reached at border k, at
  every old.
* `onesV_true_reached`: under the head, k ≤ 353: onesV s.st f.rows = true at every state s reached
  at border k and every copy f of the frame in s (`Meaning.K2.framesIn`,
  Johnson/Goal/Meaning/RecAll.lean).

Limits. "Reached" is taken with the test on the words in front of each decision (`Reach 0
(cF.blocksInOrder.map below) …`), and borders up to 353 alone: both for the third clause. It is one test on
values: the code switch's law asks a guard on the shape and tests on its rounds besides. That the
head has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files, in
a side library. At the format's second hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.TakenRowsOrder
import Johnson.AtFull.Shape.CarriedRowsOrder
import Johnson.Desc.First.Shape.SwitchFrontFits
import Johnson.Desc.First.Shape.Ones

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Meaning.K2 (framesIn)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- A tensor without a written-out factor passes the test on the pairs for nothing. -/
theorem onesT_of_plain {v : Tensor} (h : v.denseVars = []) : onesT v = true := by
  unfold onesT
  rw [h]
  rfl

/-- **Where no stored sample row has a written-out factor, the third clause of the code switch's
test on values accepts**: the test is its first two clauses, on the carried forms. -/
theorem onesV_of_plain {T : Statement} (hP : SamplesPlain T) (old : SingleRows) :
    onesV T old = (onesF old.c && old.kept.toList.all fun f => onesF f.c) := by
  have h3 : ((switchKept old).toList.all fun o =>
      (T.oracles.getD o default).sampleRows.toList.all fun r =>
        r.terms.toList.all fun t => onesT t.v) = true := by
    refine List.all_eq_true.2 fun o _ => List.all_eq_true.2 fun r hr => List.all_eq_true.2
      fun t ht => ?_
    cases hx : T.oracles[o]? with
    | none =>
      have e : T.oracles.getD o default = default := by
        rw [Array.getD_eq_getD_getElem?, hx]
        rfl
      rw [e] at hr
      cases hr
    | some x =>
      have e : T.oracles.getD o default = x := by
        rw [Array.getD_eq_getD_getElem?, hx]
        rfl
      rw [e] at hr
      exact onesT_of_plain ((hP o x hx r hr).1 t ht)
  unfold onesV
  rw [h3, Bool.and_true]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head, at every state reached at a border up to the last code switch.** -/
theorem onesV_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : Nat} (hk : k ≤ 353)
    {p : ProofFile.InstPub} {s : S} (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k (p, s))
    (old : SingleRows) :
    onesV s.st old = (onesF old.c && old.kept.toList.all fun f => onesF f.c) :=
  onesV_of_plain (samplesPlain_reached h hk hr) old

/-- **UNDER THE HEAD, AT EVERY STATE REACHED AT A BORDER UP TO THE LAST CODE SWITCH: THE TEST
ACCEPTS AT THE CARRIED ROWS OF EVERY COPY OF THE FRAME.** -/
theorem onesV_true_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : Nat} (hk : k ≤ 353)
    {p : ProofFile.InstPub} {s : S} (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k (p, s)) :
    ∀ f ∈ framesIn s, onesV s.st f.rows = true := by
  intro f hf
  obtain ⟨-, rs, cols, hfold⟩ := (reach_raw hr).fold
  obtain ⟨c1, c2⟩ := carried_order_reached h k 0 p rs cols _ hfold f hf
  rw [onesV_reached h hk hr, onesF_of_order c1, Bool.true_and]
  exact List.all_eq_true.2 fun g hg => onesF_of_order (c2 g hg)

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.onesT_of_plain
#print axioms Johnson.AtFull.Shape.onesV_of_plain
#print axioms Johnson.AtFull.Shape.onesV_reached
#print axioms Johnson.AtFull.Shape.onesV_true_reached
