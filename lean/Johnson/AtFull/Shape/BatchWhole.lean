-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/BatchWhole.lean: FROM A SLOT AND A Bool FOR EACH RUN THAT A LINK's ORDER NAMES
TO THE BATCHING MEMBER's FRAME: a joint of the bridge at K9's 25 batching members of the proof
file's own first chain. It joins RunsLaw.ofSlots (Johnson/Desc/First/Batch/Shape/BatchBuild.lean)
with batch_frame (BatchFrames.lean). Nothing is evaluated.

  `RunLawB.ofEq`: a RunLaw whose pre IS "V n s = true" has V as its Bool.
  `RunLawB.ofPre`: a Bool for one law serves another law of the same pre.
  `ofSlotsB`: from a Bool for each slot's bare law to the Bools of the built RunsLaw.
  **`batch_of_slots`** (l < 25): Lk · p · w tied as in batch_named: for every family of slots T for
    the pairs of Lk.order and every family of Bools B for their laws: for every ft, G with
    G ‹number› = liftQ (batchGS p.rows w.1 ‹the built laws' runG› Lk.order) and vals with
    vals ‹number› = batchV p ‹the built RunsLaw› ‹its Bools› Lk.order: CarriesV and Returns.
    WHAT A RUN's HOUSE GIVES: its RunLaw; "keeps the reply"; "leaves the statement"; one Bool with
    one lemma. WHAT THE SEAT GIVES: that the lot's sub-protocol is seated at the member and states
    the run.

Limits. A BRIDGE: no family of slots is laid here (whole links' rows: BatchCells.lean and
BatchCellsAtt.lean, by a further joint, which calls this one: BatchTable.lean). That batchV accepts
at a state of a run is not shown. UNDER THE HEAD: that it has a member is shown in scope, where the
reader returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three
hold together, at two named sets of public files, in a side library. At the earlier hash. Nothing on
soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.BatchFrames
import Johnson.Desc.First.Batch.Shape.BatchBuild

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.K9 (testsWhere SegSort TWhere Where)
open VerifiableInference.Desc.K9.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest (Returns)

/-- A RunLaw whose pre is "V n s = true" has V as its Bool. -/
def RunLawB.ofEq {run : VerifiableInference.Desc.K9.Shape.Run} (R : RunLaw run)
    (V : Nat → S → Bool) (h : R.pre = fun n s => V n s = true) : RunLawB R where
  preB := V
  pays := fun n s hv => by rw [h]; exact hv

/-- A Bool for one law serves another law of the same pre. -/
def RunLawB.ofPre {run run' : VerifiableInference.Desc.K9.Shape.Run} {R : RunLaw run}
    {R' : RunLaw run'} (h : R'.pre = R.pre) (B : RunLawB R) : RunLawB R' where
  preB := B.preB
  pays := fun n s hv => by rw [h]; exact B.pays n s hv

/-- From a Bool for each slot's bare law to the Bools of the built RunsLaw. Outside the order: the
Bool that always rejects (nothing is asked there). -/
def ofSlotsB {same : S → S → Bool} {bs : List (Block S Claim)} {order : List (Nat × String)}
    (T : ∀ o, o ∈ order → Slot same bs o) (B : ∀ o (ho : o ∈ order), RunLawB (T o ho).law)
    (o : Nat × String) : RunLawB ((RunsLaw.ofSlots T).law o) :=
  if h : o ∈ order then RunLawB.ofPre (ofSlots_pre T o h) (B o h)
  else ⟨fun _ _ => false, fun _ _ hv => nomatch hv⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem batch_of_slots (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (Lk : Link S ProofFile.Cl) (p : Where) (w : SegSort × Nat × TWhere),
      cF.links[l]? = some Lk ∧ IM.k9At Zp l = some p ∧ testsWhere Zp.p.X l 0 = some w ∧
      ∀ (T : ∀ o, o ∈ Lk.order → Slot ProofFile.sameReply Lk.hear o)
        (B : ∀ o (ho : o ∈ Lk.order), RunLawB (T o ho).law)
        (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (14 * l + Lk.hear.length + 2) =
          liftQ (batchGS p.rows w.1 (fun o => ((RunsLaw.ofSlots T).law o).runG) Lk.order) →
        vals (14 * l + Lk.hear.length + 2) =
          batchV p (RunsLaw.ofSlots T) (ofSlotsB T B) Lk.order →
        CarriesV cF.blocksInOrder ft (firstZA G vals) (14 * l + Lk.hear.length + 2) ∧
          Returns cF.blocksInOrder ft (firstZA G vals) (14 * l + Lk.hear.length + 2) := by
  obtain ⟨Lk, p, w, a1, a2, a3, hN⟩ := batch_frame h l hl
  exact ⟨Lk, p, w, a1, a2, a3, fun T B ft G vals hG hv =>
    hN (RunsLaw.ofSlots T) (ofSlotsB T B)
      (fun o ho n a cs a' hr => ofSlots_still T o ho n a a' cs hr) ft G vals hG hv⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.RunLawB.ofEq
#print axioms Johnson.AtFull.Shape.RunLawB.ofPre
#print axioms Johnson.AtFull.Shape.ofSlotsB
#print axioms Johnson.AtFull.Shape.batch_of_slots
