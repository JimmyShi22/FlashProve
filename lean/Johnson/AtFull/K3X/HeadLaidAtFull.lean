-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/HeadLaidAtFull.lean: at the full size's written numbers the host's count of
padding keys at the output head's lookup (laidHead, Johnson/Desc/First/Look/Laid.lean) returns the
nine written numbers, at whatever layout Head.layout returns there. A join of laws, and one small
closed fact proved by evaluation in Lean's kernel. No sub-protocol imports this file.

  withFs_at       a closed fact withFs f = true (Johnson/AtFull/Head/LayoutAtFull.lean) speaks of
                  whatever letters the three makers return.
  headFitB, headFit_W  [Lean's kernel] the tree of each call's last column is one of the lookup's
                  trees: six comparisons of small numbers. It reads of a call its number of columns.
  headFit_no      a negative test: with one tree fewer the comparison fails (at the last call).
  laidHead_at     at the makers' letters: laidHead = some pubNine. How: laidHead_eq
                  (Johnson/AtFull/K3X/HeadLaidLaw.lean) turns the host's count into the fold that
                  pubOf_eq has for the layout's count; pub_nine
                  (Johnson/AtFull/Head/PubAtFull.lean) has that fold's value by a closed form.
  laidHead_W      for every x with LaidW x: x = .ok HLy and laidHead Cond.hFull HLy = some pubNine.
  pubNine_written the nine are the written list of the lookups' table of values, pubW 3 false
                  (Johnson/AtFull/Desc/Lots/K3Written.lean).

Limits. The full size, at the stored free numbers alone: at the library's second written set of
public files (VerifierAndGoals.zGap), whose acceptance policy is another, the head's shape is not Cond.hFull,
and nothing here speaks of it. The host's count and the layout's count are
made of the same lists of columns: that they agree shows no fault in a list or inside a key form. No
soundness is claimed. On hiding nothing.
-/
import Johnson.AtFull.K3X.HeadLaidLaw
import Johnson.AtFull.Head.PubAtFull
import Johnson.AtFull.Desc.Lots.K3Written

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.K3X
open OnBytes OnBytes.Model OnBytes.Model.Head
open VerifiableInference.Desc.First.Look (laidHead)
open VerifiableInference.Desc.Kinds.Head.Law (Cond.hFull)
open _root_.AtFull.Head (withFs withFs_true csW clW form_W formB facts_W pub_nine pubNine laidOf
  LaidW pubOf_eq)

/-- A closed fact at the makers speaks of whatever they return. -/
theorem withFs_at {f : HL → List CallD → Forest.Shape → Bool} (h : withFs f = true) {L : HL}
    {calls : List CallD} {fs : Forest.Shape} (hL : numbers Cond.hFull = .ok L)
    (hc : callsOf Cond.hFull L = .ok calls)
    (hf : Forest.shapeNoAsk (clW calls) Cond.hFull.LIDB = .ok fs) : f L calls fs = true := by
  obtain ⟨L', calls', fs', hL', hc', hf', hT⟩ := withFs_true h
  obtain rfl : L' = L := Except.ok.inj (hL'.symm.trans hL)
  obtain rfl : calls' = calls := Except.ok.inj (hc'.symm.trans hc)
  obtain rfl : fs' = fs := Except.ok.inj (hf'.symm.trans hf)
  exact hT

/-- The tree of each call's last column is one of the lookup's trees. -/
def headFitB (_ : HL) (calls : List CallD) (fs : Forest.Shape) : Bool :=
  calls.zipIdx.all fun x => decide (fs.first.getD x.2 0 + (x.1.J - 1) / 2 ^ csW fs < fs.NT)

/-- **By the kernel.** -/
theorem headFit_W : withFs headFitB = true := by decide +kernel

/-- A negative test: with one tree fewer. (withFs is false also where a maker refuses: that the
three makers return is headFit_W's: it is the control.) -/
theorem headFit_no : withFs (fun _ calls fs => calls.zipIdx.all fun x =>
    decide (fs.first.getD x.2 0 + (x.1.J - 1) / 2 ^ csW fs + 1 < fs.NT)) = false := by
  decide +kernel

/-- The host's count at whatever letters the makers return. -/
theorem laidHead_at {L : HL} {calls : List CallD} {fs : Forest.Shape} (kb : Nat)
    (hL : numbers Cond.hFull = .ok L) (hc : callsOf Cond.hFull L = .ok calls)
    (hf : Forest.shapeNoAsk (clW calls) Cond.hFull.LIDB = .ok fs) :
    laidHead Cond.hFull (laidOf L calls fs kb) = some pubNine := by
  obtain ⟨-, H1, H2⟩ := facts_W hL hc hf
  have hT := withFs_at form_W hL hc hf
  have hU := withFs_at headFit_W hL hc hf
  unfold formB at hT
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hT
  unfold headFitB at hU
  simp only [decide_eq_true_eq, List.all_eq_true] at hU
  have e : _ = pubNine := pub_nine hL hc hf (pubOf_eq Cond.hFull L fs calls H1 H2)
  refine (laidHead_eq Cond.hFull (laidOf L calls fs kb) calls rfl (fun cd hcd => ?_) hT.2
    (fun cd hcd g hg hp => ?_) hU).trans (congrArg some e)
  · obtain ⟨name, kind, asks, fl, e1, -⟩ := (OnBytes.Road.Hd.callsOf_spec hc).1 cd hcd
    exact ⟨name, kind, asks, fl, e1⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcd
    exact H2 (calls[i], i) (List.mem_iff_getElem.2 ⟨i, by simpa using hi, by simp⟩) g hg hp

/-- **The host's count at what the head's layout returns is the nine.** -/
theorem laidHead_W {x : Except String HL} (h : LaidW x) :
    ∃ HLy, x = .ok HLy ∧ laidHead Cond.hFull HLy = some pubNine := by
  obtain ⟨L, calls, fs, kb, hL, hc, hf, -, hx⟩ := h.opens
  exact ⟨_, hx, laidHead_at kb hL hc hf⟩

/-- The nine are the written list of the lookups' table of values. -/
theorem pubNine_written : pubNine = Lots.K3.pubW 3 false := rfl

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.withFs_at
#print axioms Johnson.AtFull.K3X.headFit_W
#print axioms Johnson.AtFull.K3X.headFit_no
#print axioms Johnson.AtFull.K3X.laidHead_at
#print axioms Johnson.AtFull.K3X.laidHead_W
#print axioms Johnson.AtFull.K3X.pubNine_written
