-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ReadyOfClosing.lean: the kind "the code switch" (K2): WHERE THE
CLOSING AS THE KIND's LOT LAYS IT (`lotClosingAt`, Honest/K2/Exact.lean) RETURNS AT A SWITCH, THE
FILLING LAYS EACH OWN MESSAGE OF THAT SWITCH's OWN SENDING AT NO CHALLENGE: `heardAt` = 0 at its
address: the premise h0 of `hd_at_head` (Honest/K2/Law/OwnAtSender.lean, which this file does not
import) out of a return that its callers hold already. Statements with their proofs; no definition.

  `ownLaid_ready`      where `ownLaid` (Honest/K2/AtPlan.lean) returns, its second loop threw
                       nowhere: `readyAt []` says yes at each own message of the switch's own
                       sending
  `heardAt_of_ready`   `readyAt []` says yes: so `heardAt` is 0
  `lotClosingAt_laid`  where `lotClosingAt` returns, `ownLaid` has returned
  `h0_of_closing`      THE END

By: `forIn_each` (Johnson/Desc/First/Att/K05PublicOfBuilt.lean): a loop that returns, none of whose
steps ends it early: each member's step went on. Kin: `ownLaid_of_light`
(Honest/K2/Law/LaidLight.lean, a file that is not in this library) goes the other way: from a test's
yes to the return.

Limits. Of what `ownLaid`'s return says one clause of its second loop alone is drawn out: nothing on
its first loop, nor on `arraysLaid`. On a filling D as a letter: no coin, no book, no input. Nothing
on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Exact
import Johnson.Desc.ProofFile.Honest.K2.Law.Reads
import Johnson.Desc.First.Att.K05PublicOfBuilt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left)
open VerifiableInference.Desc.First.Att.P (forIn_each)
open Reads

/-- Where `ownLaid` returns, its second loop threw nowhere. -/
theorem ownLaid_ready {D : RowData} {lay : OnBytes.Params.ReqLayout} {p : SwitchPlace}
    {segs : List SegmentPub} (h : ownLaid D lay p segs = .ok ()) :
    ∀ n ∈ (p.others.toList.take (p.others.size - 1)).zipIdx,
      D.readyAt [] (p.ownAddr n.2) = true := by
  unfold ownLaid at h
  obtain ⟨u, -, h2⟩ := bind_ok h
  obtain ⟨u', h3, -⟩ := bind_ok h2
  intro n hn
  have hy := forIn_each _ (fun a s hs => by
    dsimp only at hs
    split at hs
    · cases hs
    · simp only [pure_bind] at hs
      split at hs
      · cases hs
      · exact (Except.ok.inj hs).symm) _ u' h3 n hn
  dsimp only at hy
  split at hy
  · cases hy
  · simp only [pure_bind] at hy
    split at hy
    · cases hy
    · rename_i hr
      simpa using hr

theorem heardAt_of_ready {D : RowData} {a : MsgAddr} (h : D.readyAt [] a = true) :
    D.heardAt a = 0 := by
  unfold RowData.readyAt RowData.heardOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.length_nil] at h
  omega

theorem lotClosingAt_laid {lay : OnBytes.Params.ReqLayout} {segs : List SegmentPub}
    {p : SwitchPlace} {D : RowData} {Rd : Readers} {heard : List Fmt.Drawn}
    {k : Nat → Except String Stretch} {W : Left}
    (h : lotClosingAt lay segs p D Rd heard k = .ok W) :
    ownLaid D lay p (segs.take p.link) = .ok () := by
  unfold lotClosingAt at h
  obtain ⟨u, hu, -⟩ := bind_ok' h
  exact hu

/-- **THE END.** -/
theorem h0_of_closing {lay : OnBytes.Params.ReqLayout} {segs : List SegmentPub}
    {p : SwitchPlace} {D : RowData} {Rd : Readers} {heard : List Fmt.Drawn}
    {k : Nat → Except String Stretch} {W : Left}
    (h : lotClosingAt lay segs p D Rd heard k = .ok W) :
    ∀ m, m < p.others.size - 1 → D.heardAt (p.ownAddr m) = 0 := by
  intro m hm
  have hlen : m < (p.others.toList.take (p.others.size - 1)).length := by
    rw [List.length_take, Array.length_toList]
    omega
  have hmem : ((p.others.toList.take (p.others.size - 1))[m], m) ∈
      (p.others.toList.take (p.others.size - 1)).zipIdx := by
    refine List.mem_of_getElem? (i := m) ?_
    rw [List.getElem?_zipIdx, List.getElem?_eq_getElem hlen]
    simp
  exact heardAt_of_ready (ownLaid_ready (lotClosingAt_laid h) _ hmem)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.ownLaid_ready
#print axioms ProofFile.Honest.K2.Law.heardAt_of_ready
#print axioms ProofFile.Honest.K2.Law.lotClosingAt_laid
#print axioms ProofFile.Honest.K2.Law.h0_of_closing
