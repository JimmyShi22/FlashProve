-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FrontsFull.lean: the code switch's law: THE ONE TEST ON THE PLAN FOR THE 25
PLACES OF THE KIND (k2FrontsB, FrontsB.lean) SAYS YES AT THE WRITTEN VALUES OF THE FULL SIZE: A
CLOSED FACT, BY LEAN's KERNEL; with negative tests, one a clause. A law file; no running text
imports it.

THE THREE LETTERS OF THE PLAN, AT THEIR WRITTEN VALUES (declared in other files): the codes
proofSizedFull.codes and the request's shape proofSizedFull.request
(Johnson/Desc/Ok/PlanWritten/SizedLit.lean); the listed shapes of the first chain's oracle messages
msgsOfChain proofSendsFull.1 (Johnson/Desc/K12/Door/MsgShapes.lean; Johnson/G/SendsWritten.lean).
That the public part's own three letters ARE these, in scope and under the verifier's test on the
plan, is MadeInScope.lean's to show (first_written_in_scope, sends_in_scope): not called here.

  csW, shW, MW     the three written values, by short names.
  MList, sends_sorted, MW_eq   the written sendings stand in the order of their entries, so MW is
                   their shapes in the written order: Lean's kernel does not unfold the sorting in
                   msgsOfChain, so the closed facts are had at MList and carried to MW.
  place_full       placeB at each of the 25 entries, as one list of Bools: all true.
  k2Fronts_list, k2Fronts_full   k2FrontsB tableFullLit n0Full oldsFull csW shW MW = true.
  clauseAt         a clause of closedList by its name, at entry i, with letters that can be bent.
  neg_*            NEGATIVE TESTS, at entry 0, each by the kernel: with one letter bent the named
                   clause is false (and true unbent: pos_all).
Limits. Closed facts on written values. That n0Full and oldsFull are the run's numbers is the
walk's. Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.FrontsB
import Johnson.Top.H0.K2Caller.LitRows
import Johnson.Desc.Ok.PlanWritten.SizedLit
import Johnson.Desc.K12.Door.MsgShapes
import Johnson.G.SendsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit full24)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (fxAt proofSendsFull)

def csW : Codes := proofSizedFull.codes

def shW : Params.ReqShape := proofSizedFull.request

def MW : List OracleShape := K12.Door.msgsOfChain proofSendsFull.1

/-- The same shapes, off the written sendings in the order in which they are written. -/
def MList : List OracleShape := K12.Door.msgsOf (proofSendsFull.1.sends.map (·.sent))

set_option maxRecDepth 1000000 in
/-- The written sendings stand in the order of their entries. -/
theorem sends_sorted : proofSendsFull.1.sends.Pairwise
    (fun a b => decide (a.entry ≤ b.entry) = true) := by decide +kernel

/-- So sorting them changes nothing. (Lean's kernel does not unfold the sorting.) -/
theorem MW_eq : MW = MList := by
  unfold MW MList K12.Door.msgsOfChain
  rw [List.mergeSort_of_pairwise sends_sorted]

set_option maxRecDepth 1000000 in
theorem place_full : ((List.range 25).map fun i => (tableFullLit[i]?).map fun r =>
    placeB csW shW MList r (i + 1) (n0Full.getD (i + 1) 0) (oldsFull.getD i [])) =
      List.replicate 25 (some true) := by decide +kernel

set_option maxRecDepth 1000000 in
theorem k2Fronts_list : k2FrontsB tableFullLit n0Full oldsFull csW shW MList = true := by
  decide +kernel

/-- **The test says yes at the written values.** -/
theorem k2Fronts_full : k2FrontsB tableFullLit n0Full oldsFull csW shW MW = true := by
  rw [MW_eq]
  exact k2Fronts_list

/-- A clause by its name. -/
def clauseAt (name : String) (x₀ : _root_.Tw.K2.Front) (W₀ : Option SwitchFrame) (cs : Codes)
    (M : List OracleShape) (n0 : ℕ) (olds : List ℕ) (code maskCode : ℕ) : Option Bool :=
  W₀.bind fun W => ((closedList x₀ W cs M n0 olds code maskCode).find? (·.1 == name)).map (·.2)

/-- Entry 0's written front and its frame. -/
def x0W : _root_.Tw.K2.Front := fxAt (tableFullLit.getD 0 full24)

def w0W : Option SwitchFrame := K2.frameAt x0W

set_option maxRecDepth 1000000 in
theorem pos_all : (["codes", "shapes", "below", "below0", "keptRows", "logEll", "ell"].map fun n =>
    clauseAt n x0W w0W csW MList 7 [1, 2] shW.code shW.maskCode) =
      List.replicate 7 (some true) := by decide +kernel

set_option maxRecDepth 1000000 in
theorem neg_codes : clauseAt "codes" x0W w0W { csW with base := csW.base.pop } MList 7 [1, 2]
    shW.code shW.maskCode = some false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem neg_shapes : clauseAt "shapes" x0W w0W csW [] 7 [1, 2] shW.code shW.maskCode =
    some false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem neg_shapes_olds : clauseAt "shapes" x0W w0W csW MList 7 [0, 2] shW.code shW.maskCode =
    some false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem neg_below : clauseAt "below" x0W w0W csW MList 2 [1, 2] shW.code shW.maskCode =
    some false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem neg_below0 : clauseAt "below0" { x0W with st := { x0W.st with oracles := #[] } } w0W csW
    MList 7 [1, 2] shW.code shW.maskCode = some false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem neg_keptRows : clauseAt "keptRows" x0W w0W csW MList 7 [1] shW.code shW.maskCode =
    some false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem neg_logEll : clauseAt "logEll" x0W w0W csW MList 7 [1, 2] csW.base.size shW.maskCode =
    some false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem neg_ell : clauseAt "ell" x0W (w0W.map fun W => { W with zk := { W.zk with ell := 0 } }) csW
    MList 7 [1, 2] shW.code shW.maskCode = some false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The next group's target is not like entry 0's. -/
theorem neg_target : ((reqGroups shW)[2]?).map (fun g => targetLikeB g.target x0W.T) =
    some false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- With one of the places' numbers turned the whole test says no. -/
theorem neg_whole : k2FrontsB tableFullLit n0Full (oldsFull.set 1 [8]) csW shW MList = false := by
  decide +kernel

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.k2Fronts_full
#print axioms VerifiableInference.Desc.First.K2Hands.place_full
#print axioms VerifiableInference.Desc.First.K2Hands.MW_eq
#print axioms VerifiableInference.Desc.First.K2Hands.pos_all
#print axioms VerifiableInference.Desc.First.K2Hands.neg_whole
