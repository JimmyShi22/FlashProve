-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/Back/PartsOfHeadOrd.lean: THE CONVERSE OF `headOrd_of_parts`
(Johnson/Desc/Kinds/Law/HeadCutsK6.lean). That theorem goes from the output head's four parts
(`partsAtX` at idn, lookCalls, rider, small) to the library's `Hd.HeadOrdLB` at the integers that
`ownQ` reads at sub-proof 24. Here: from `Hd.HeadOrdLB` at that list back to the four parts. One
statement with its proof.

What it is not. An implication: the nine public premises, "the stored table holds the index" and
`Hd.HeadOrdLB` are premises: this file shows them of no public parameters, witness or request. The
letter pl is idle: the parts read the first component of `compCut`, and pl stands in the second
alone. The full size alone. No chance in it. Nothing on soundness, completeness or hiding.

  `parts_of_headOrd`   CONDITIONAL on `headOrd_of_parts`' own nine premises, "the stored table holds
                       the index" and `Hd.HeadOrdLB` at ownQ ... w 24: `partsAtX` at each part of
                       parts4

How. (1) The parts read the list cut to the four ranges in which the head's cells lie (`ownCut`).
The cut list and the list agree inside these ranges (`agreeH_cut`), agreement is symmetric, and
`Hd.HeadOrdLB` reads nothing outside them (`Meaning.headOrd_congr`): so it holds at the cut list
too. (2) Its second clause is `Policy.HeadCl` at the library's cells made of `compCut`'s: by
unfolding (`comp_cells`). (3) The weights off the stored table are the index's output matrix
(`whOf_holds`). (4) `parts_atX` gives idn, lookCalls and rider. (5) The part small is the first
clause of `Hd.HeadOrdLB` at the uncut list, as it stands.

Of the folder Johnson/Goal/ this file names `Meaning.headOrd_congr` and `AgreeH.symm` (written
`.symm`), and through them the definition `AgreeH`: all three in
Johnson/Goal/Meaning/HidHeadCongr.lean; no other name of that folder stands in its text.

-/
import Mathlib
import Johnson.Desc.K6.Honest.Law.Back.PartsAtX
import Johnson.Desc.Kinds.Law.HeadCutsK6

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes.Model.Verify (borderOf)
open Inst.Model (ppref Instance)
open Inst.Model.Layout (kRef hRef)
open VerifiableInference.OnPublicFiles.Flat (GE Holds)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT)

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
  (pl : Nat → Nat × Bool × Nat × Nat)

/-- **THE LANDED HeadOrdLB AT SEGMENT 24's OWN INTEGERS GIVES THE FOUR PARTS BACK**: the converse of
`headOrd_of_parts` (Johnson/Desc/Kinds/Law/HeadCutsK6.lean), under that theorem's own nine premises
and "the stored table holds the index". -/
theorem parts_of_headOrd (hr0 : rows ≤ hRef) (hc0 : cols ≤ 2 ^ kRef) (tab : Nat → Nat)
    (i : Cm.Idx) (x : Instance ppref) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (hF : OnBytes.Road.Hd.FullH Wp.hS) (hNum : OnBytes.Road.Hd.NumH Wp.hS Wp.HLy)
    (hBd : OnBytes.Road.Hd.BorderH (borderOf Wp.y)) (h8 : Wp.hS.digSh = 8)
    (hplan : (parOf Wp.hS (workOf Wp)).ok = true) (h3 : Inst.Model.Head3 x)
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u) (hH : Holds w.cells i)
    (O : OnBytes.Road.Hd.HeadOrdLB Wp.hS Wp.HLy Wp.y (OnBytes.Road.Hd.npOf Wp.hS)
      (OnBytes.Road.Hd.polOf Wp.hS) i.mat x (P5J.ownQ cs arr msR N s seat w 24)) :
    ∀ p ∈ P5J.parts4, partsAtX cs arr msR N s seat Wp pl tab i x w p := by
  -- (1) from the list to the list cut to the four ranges
  have O' : OnBytes.Road.Hd.HeadOrdLB Wp.hS Wp.HLy Wp.y (OnBytes.Road.Hd.npOf Wp.hS)
      (OnBytes.Road.Hd.polOf Wp.hS) i.mat x (ownCut cs arr msR N s seat Wp w) :=
    Meaning.headOrd_congr hNum hBd
      (agreeH_cut Wp.hS Wp.HLy (borderOf Wp.y) (P5J.ownQ cs arr msR N s seat w 24)).symm O
  -- (2) its second clause, at the library's cells made of compCut's: by unfolding
  have hC : _root_.Policy.HeadCl (OnBytes.Road.Hd.npOf Wp.hS) (OnBytes.Road.Hd.polOf Wp.hS) i.mat x
      (HeadJoin.cellsN (compCut cs arr msR N s seat Wp pl w).1) := O'.2.1
  -- (3), (4) the three parts beneath
  obtain ⟨hidn, hcalls, hrider⟩ := parts_atX Wp.hS (workOf Wp) x i.mat tab
    (compCut cs arr msR N s seat Wp pl w).1 hF h8 hplan h3 htab (whOf_holds hr0 hc0 hH) hC
  -- the four parts, one by one
  intro p hp
  unfold P5J.parts4 at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact hidn
  · exact ⟨hH, fun call hc col _ t ht => hcalls call hc col t ht⟩
  · exact hrider
  · exact O.1

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.parts_of_headOrd
