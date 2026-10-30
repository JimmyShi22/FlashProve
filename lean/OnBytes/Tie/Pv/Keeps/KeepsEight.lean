-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/KeepsEight.lean: the eight facts that a note of this project asks (the note is
not in this library), over the two definitions as that note writes them (KeepsViewB, KeepsMark;
OnBytes/Tie/Pv/Keeps/KeepsKit.lean). Each is stated for every argument of the routine. That is more
than the note's letters ask in four: (a) for every shape and layout, (e), (g), (h) for every shape
of the table's test, where the note has those of one p or c.
-/
import OnBytes.Tie.Pv.Keeps.KeepsIop
import OnBytes.Model.ReqChain
import OnBytes.Model.StagesLinks

namespace OnBytes.L5

open OnBytes OnBytes.Model

/-! ## The calls over the links (OnBytes/Model/ReqChain.lean) -/

instance keeps_chainStart (s : Params.ReqShape) (l : Params.ReqLayout) :
    Keeps (ChainCheck.start s l) := by
  unfold ChainCheck.start; keeps
instance keeps_chainFirst (k : ChainCheck) : Keeps k.first := by unfold ChainCheck.first; keeps
instance keeps_chainLater (k : ChainCheck) : Keeps k.later := by unfold ChainCheck.later; keeps
instance keeps_chainClose (k : ChainCheck) (eq : ReqEquation) : Keeps (k.close eq) := by
  unfold ChainCheck.close; keeps
instance keeps_chainFinish (k : ChainCheck) : Keeps k.finish := by
  unfold ChainCheck.finish; keeps

/-! ## Two parts of a link's run (OnBytes/Model/Frame.lean, StagesLinks.lean) -/

instance keeps_refuse {α : Type} (n : String) : Keeps (refuse n : Blk α) := by
  unfold refuse; keeps
instance keeps_mustAs (n : String) (b : Bool) : Keeps (mustAs n b) := by unfold mustAs; keeps
instance keeps_indexMasksH (links : Array Stages.LinkH) (p : Params.First) (k : ChainCheck) :
    Keeps (Stages.indexMasksH links p k) := by
  unfold Stages.indexMasksH; keeps
instance keeps_pendingRowH (wsLay : WsLay) (i : Nat) (o : WsForkOut) (n : Nat)
    (S : Params.LinShape) : Keeps (Stages.pendingRowH wsLay i o n S) := by
  unfold Stages.pendingRowH; keeps

/-! ## The eight -/

/-- (a) The start of the calls over a request's links keeps a run on a view a run on a view. -/
theorem fact_a (s : Params.ReqShape) (l : Params.ReqLayout) :
    KeepsViewB (ChainCheck.start s l) := Keeps.viewB _
/-- (b) A link's first call does. -/
theorem fact_b (k : ChainCheck) : KeepsViewB k.first := Keeps.viewB _
/-- (c) The call after the last link does. -/
theorem fact_c (k : ChainCheck) : KeepsViewB k.finish := Keeps.viewB _
/-- (d) The test on the index-mask message, after the first link's first call, does. -/
theorem fact_d (links : Array Stages.LinkH) (p : Params.First) (k : ChainCheck) :
    KeepsViewB (Stages.indexMasksH links p k) := Keeps.viewB _
/-- (e) The row that a sub-proof leaves on the weight table: making it does. -/
theorem fact_e (wsLay : WsLay) (i : Nat) (o : WsForkOut) (n : Nat) (S : Params.LinShape) :
    KeepsViewB (Stages.pendingRowH wsLay i o n S) := Keeps.viewB _
/-- (f) The call that ends a link does. -/
theorem fact_f (k : ChainCheck) (eq : ReqEquation) : KeepsViewB (k.close eq) := Keeps.viewB _
/-- (g) The first part of the test on the table does. -/
theorem fact_g (S : Params.LinShape) (i : Nat) (pend : List TensorRow) :
    KeepsViewB (memberFirstVerify S i pend) := Keeps.viewB _
/-- (h) The first part of the test on the table, in a run on a view, wipes no mark of a failed named
test. -/
theorem fact_h (S : Params.LinShape) (i : Nat) (pend : List TensorRow) :
    KeepsMark (memberFirstVerify S i pend) := Keeps.mark _

#print axioms keeps_chainLater
#print axioms fact_a
#print axioms fact_b
#print axioms fact_c
#print axioms fact_d
#print axioms fact_e
#print axioms fact_f
#print axioms fact_g
#print axioms fact_h

end OnBytes.L5
