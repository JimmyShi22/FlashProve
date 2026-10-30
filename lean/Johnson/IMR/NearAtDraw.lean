-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/NearAtDraw.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: A PAYMENT BENEATH THE
KIND's FROZEN CONDITION: THE FIELD near OF K8LeftT (Johnson/P1K8R/TightAt.lean) FROM THE HEAD ALONE,
AT ALL 25 LINKS, at n₀ := n0At Zp l (Johnson/P1K8R/FoldAtDraw.lean). A definition with code and
theorems, proved.
NO SOUNDNESS.
Compiled with the whole library.

"near" is a test with code on seven public values (aheadPlanSizeB,
Johnson/Desc/First/Batch/SmallNearSize.lean): the digits' array is of link l; the layout has it; the
shape has its message; that message's moment is not 0; the plan has a seat for it at that moment;
the seat is one of the link's group; and the message's number is at least n₀.
  near_congr   the test reads its list of arrays and its number ONLY THROUGH THE ONE ENTRY arr[t]?.
  nearFullB    the test at all 25 links AT THE WRITTEN VALUES (N0Full, layoutFull,
    proofSizedFull.request), at the one-entry list #[(l, "ZZ")]. A closed term. ASKED OF NOBODY: it
    stands in no condition and no verifier runs it.
  near_full    it says yes: by Lean's kernel. near_tight: A NEGATIVE TEST: with n₀ + 1 in n₀'s place
    it says no AT EVERY ONE of the 25: so the comparison holds with equality, and the test can fail.
  k08_near_at  **THE FIELD, TO THE LETTER, UNDER THE HEAD.**
HOW. Five of the seven values are the written ones: at_written
(Johnson/Top/H0/K2Ties/WrittenAt.lean) under the pin, which AtMg.pins
(Johnson/P5T/FenceAtMg.lean) gives from the head; layout_at (Johnson/P1K8R/FoldAtDraw.lean). The two
that no tie reaches, Xl.arrayOf and Xl.tl.ix.ZZ, meet in one entry: zz_at_ground
(Johnson/IMR/ZzNamed.lean): the
digits' array bears the link's number and the name "ZZ": a law of the maker's text.

OBJECT: no block's text: public values. USER: K8LeftT's field near. LETTERS: none.

What is not claimed. That the head can be met: its owners' to show. UNDER THE PIN THAT THE HEAD
HOLDS (madeRow: AtMg.pins draws it from the head's field laid): by WrittenAt.lean's own head,
verify() at the sealed version does not ask that pin. AT OnBytes.secondHashFunction ALONE. No other field of
K8LeftT. IT SPENDS OF THE HEAD ALSO scope AND THE WHOLE FIELD laid. No soundness.
-/
import Johnson.IMR.ZzNamed
import Johnson.P1K8R.FoldAtDraw
import Johnson.Top.H0.K2Ties.WrittenAt
import Johnson.P5T.FenceAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open OnBytes OnBytes.Model OnBytes.Maker
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (aheadPlanB aheadPlanSizeB msgOfArray)
open VerifiableInference.Desc.First.K2Ties (at_written)
open VerifiableInference.PlanWritten (proofSizedFull pinnedAt_of_row)
open P5T (N0Full)
open ProofFile (Cl)

/-- **The test reads the list of arrays through one entry alone.** -/
theorem near_congr {n₀ : Nat} {sent : Nat → List (Nat × Nat)} {own : List (Nat × Nat)}
    {arr arr' : Array (Nat × String)} {lay : Params.ReqLayout} {shape : Params.ReqShape}
    {l t t' : Nat} (h : arr[t]? = arr'[t']?) :
    aheadPlanSizeB n₀ sent own arr lay shape l t =
      aheadPlanSizeB n₀ sent own arr' lay shape l t' := by
  unfold aheadPlanSizeB aheadPlanB msgOfArray
  rw [h]

/-- **The test at all 25 links, at the written values.** -/
def nearFullB : Bool :=
  (List.range 25).all fun l =>
    aheadPlanSizeB
      (Meaning.K2.msgsAt proofSizedFull.request l 0 + Meaning.K2.msgsAt proofSizedFull.request l 1)
      (N0Full.sent l) (N0Full.group l) #[(l, "ZZ")] Johnson.G.layoutFull proofSizedFull.request l 0

set_option maxRecDepth 1000000 in
/-- It says yes. -/
theorem near_full : nearFullB = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one more than n₀, and every link says no. -/
theorem near_tight : ((List.range 25).any fun l =>
    aheadPlanSizeB
      (Meaning.K2.msgsAt proofSizedFull.request l 0 + Meaning.K2.msgsAt proofSizedFull.request l 1
        + 1)
      (N0Full.sent l) (N0Full.group l) #[(l, "ZZ")] Johnson.G.layoutFull proofSizedFull.request l
      0) = false := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **K8LeftT's FIELD near, TO THE LETTER, FROM THE HEAD ALONE, AT ALL 25 LINKS.** -/
theorem k08_near_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24) {Xl : LinkH}
    (e3 : G.built[l]? = some Xl) :
    VerifiableInference.Desc.K9.aheadPlanSizeB (P1K8T.n0At Zp l) ((P5J.At.N Zp cF).sent l)
      ((P5J.At.N Zp cF).group l) Xl.arrayOf G.first.layout Zp.first.shape l Xl.tl.ix.ZZ = true := by
  have W := at_written h.scope h.laid (pinnedAt_of_row (by rw [h.toAtMg.pins.1, Bool.or_true]))
  have hsh : Zp.first.shape = proofSizedFull.request := W.shape
  have hlay : G.first.layout = Johnson.G.layoutFull := (P1K8T.layout_at hG).trans W.layout
  have hz : Xl.arrayOf[Xl.tl.ix.ZZ]? = (#[(l, "ZZ")] : Array (Nat × String))[0]? :=
    Own.zz_at_ground h.laid.pub hG e3
  rw [near_congr hz]
  unfold P1K8T.n0At
  rw [hsh, hlay, W.sent, W.group l]
  exact List.all_eq_true.1 near_full l (List.mem_range.2 (by omega))

end IM

#print axioms IM.near_congr
#print axioms IM.near_full
#print axioms IM.near_tight
#print axioms IM.k08_near_at
