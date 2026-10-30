-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ReadsHeadAt.lean: THE OUTPUT HEAD's PART OF THE RELAXED RELATION READS OF THE WITNESS
ONLY WHAT THE TABLE BOOKS FOR IT: the field `head` of `HidReads`
(Johnson/Desc/Sound/ReadsConstr.lean) at the closed constant. Two theorems.
Why. Every kind's fifth tie asks, of each item that rides past its sub-protocol, that the item's
sentence read the witness through the booked components alone. For the items `constr k p` that
comes down to five congruences (`HidReads`); this is the one on `headPart`.
  `headPartK6_reads`: general in the hidden integers' structure H, under hK : `PutKeeps put` and
    hplan : `(parOf …).ok = true`: two witnesses that are one on
    the messages and pads of segment 24's group; on the stored table's cells where p is lookCalls
    or lookCallsHeard; and whose hidden tokens are one where p is lookCalls: give `headPartK6 … p
    i a y` one truth value in one direction. p is not lookDigits.
  `AtMgA.hidReads_head h`: so at the constant's `h.𝔇.headPart`, under `SameAt h.𝔇 At.links
    (headLink (At.X Zp)) p w w'`: the field's own text.
How: ANOTHER AUTHOR's PROOF OF `constrK6_side` (Johnson/Desc/Kinds/Law/ReadsSideK6.lean), arm by
arm, one step beneath its wrapper, by the same lemmas of that author: `headPartK6_side`,
`callsPart_congr` (Law/HeadCutsK6.lean), `ownQ_same`, `comp_of_cut`, `oneOn_of_reads`
(Law/ReadsOkK6.lean). That theorem speaks of the whole sentence `constrQAt 24 …` at one H; the
field asks `headPart` alone, at every index, at the constant's H. At the constant:
`headLink_in_scope` (Johnson/P5J/RowsAtMg.lean), `ok_in_scope`
(Johnson/Goal/Meaning/HeadCondScope.lean), `putReq_keeps`.
Limits: NO PROMISE AND NO "REACHED" IS SPENT: the head's scope, reads and pubOne alone. The head h
is a premise. The other four fields of `HidReads` are not touched. No soundness is claimed.

-/
import Mathlib
import Johnson.Desc.Sound.ReadsConstr
import Johnson.Desc.Kinds.Law.ReadsSideK6
import Johnson.Goal.Meaning.HeadCondScope
import Johnson.P5J.MgAtAll
import Johnson.P5J.RowsAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open VerifiableInference.Desc.Kinds VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law VerifiableInference.Desc.Kinds.Head.Law.Came

open Inst.Model (ppref)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (Numbers Item Comp ModelPart)
open VerifiableInference.Desc.Sound (Mem MsgT sameQ)

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
  (pl : Nat → Nat × Bool × Nat × Nat)

/-- **The head's part alone, general in the hidden integers' structure.** -/
theorem headPartK6_reads {P : Type} (tab : Nat → Nat) (put : P5J.TReq → Fin ppref.V → P5J.TReq)
    (H : P5J.HidAt Wp P (Wit (Fin rows → Fin cols → GE) Tok MsgT) rows cols)
    (tokH : P × P5J.TS → Fin ppref.V) (hK : PutKeeps put)
    (hplan : (parOf Wp.hS (workOf Wp)).ok = true) (p : P5J.TPart) (hp : p ≠ .lookDigits)
    (i : Cm.Idx) (a : P × P5J.TS) (y : Strs) (w w' : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (hG : OneOn arr (N.group 24) w w')
    (hc : p = .lookCalls ∨ p = .lookCallsHeard → w.cells = w'.cells)
    (ht : p = .lookCalls → (H.hid w).tok = (H.hid w').tok)
    (h : headPartK6 cs arr msR N s seat Wp pl tab put H tokH p i a y w) :
    headPartK6 cs arr msR N s seat Wp pl tab put H tokH p i a y w' := by
  have hO := ownQ_same cs arr msR N s seat w w' hG
  obtain ⟨c1, c2⟩ := comp_of_cut cs arr msR N s seat Wp pl w w' (by unfold ownCut; rw [hO])
  have hcomp : w.cells = w'.cells → (compCut cs arr msR N s seat Wp pl w).1 =
      (compCut cs arr msR N s seat Wp pl w').1 := by
    intro hcells
    unfold compCut compOf ownCut
    rw [hO, hcells]
  cases p with
  | lookDigits => exact absurd rfl hp
  | idn =>
    exact headPartK6_side cs arr msR N s seat Wp pl tab put H tokH hK hplan i i a y y w w' .idn c1
      c2 (fun _ => hO) (Or.inl rfl) h
  | rider =>
    exact headPartK6_side cs arr msR N s seat Wp pl tab put H tokH hK hplan i i a y y w w' .rider
      c1 c2 (fun _ => hO) (Or.inr (Or.inl rfl)) h
  | small =>
    exact headPartK6_side cs arr msR N s seat Wp pl tab put H tokH hK hplan i i a y y w w' .small
      c1 c2 (fun _ => hO) (Or.inr (Or.inr rfl)) h
  | lookCalls =>
    have hcells := hc (Or.inl rfl)
    have h3 : partsAtX cs arr msR N s seat Wp pl tab i (put (H.req a) (H.hid w).tok).val w
        .lookCalls := h
    show partsAtX cs arr msR N s seat Wp pl tab i (put (H.req a) (H.hid w').tok).val w' .lookCalls
    rw [← ht rfl, ← callsPart_congr cs arr msR N s seat Wp pl tab i _ w w' hcells (hcomp hcells)]
    exact h3
  | lookCallsHeard =>
    have hcells := hc (Or.inr rfl)
    have h3 : partsAtX cs arr msR N s seat Wp pl tab i (put (H.req a) (tokH a)).val w
        .lookCalls := h
    show partsAtX cs arr msR N s seat Wp pl tab i (put (H.req a) (tokH a)).val w' .lookCalls
    rw [← callsPart_congr cs arr msR N s seat Wp pl tab i _ w w' hcells (hcomp hcells)]
    exact h3

end P5J

namespace P5J
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (Item Comp)
open VerifiableInference.Desc.Sound (SameAt sameQ)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.Kinds.Head.Law (Came.oneOn_of_reads Came.putReq_keeps)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The field `head` of `HidReads`, at the constant.** -/
theorem AtMgA.hidReads_head (h : AtMgA o Z D r Zp Np cF x) :
    ∀ p i a y w w', p ≠ .lookDigits → SameAt h.𝔇 At.links (headLink (At.X Zp)) p w w' →
      h.𝔇.headPart p i a y w → h.𝔇.headPart p i a y w' := by
  intro p i a y w w' hp hs hw
  have h24 : headLink (At.X Zp) = 24 := headLink_in_scope h.scope h.reads h.pubOne
  rw [h24] at hs
  have hG := Came.oneOn_of_reads (At.arr Zp) (At.N Zp cF) At.links (.constr 24 p) w w' hs
  have hcells : p = .lookCalls ∨ p = .lookCallsHeard → w.cells = w'.cells := by
    intro e
    refine hs Comp.cells ?_
    unfold Item.reads
    refine List.mem_append_right _ ?_
    rcases e with rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_self
  have htok : p = .lookCalls → w.tok = w'.tok := by
    rintro rfl
    refine hs Comp.tok ?_
    unfold Item.reads
    refine List.mem_append_right _ ?_
    exact List.mem_cons_of_mem _ (by decide)
  exact headPartK6_reads (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) _ _ (At.X Zp) _
    _ _ _ _ Came.putReq_keeps
    (VerifiableInference.Desc.Kinds.Head.Law.InScope.ok_in_scope h.scope h.reads h.pubOne _) p hp
    i a y w w' hG hcells (fun e => congrArg tokVOf (htok e)) hw

end P5J

#print axioms P5J.headPartK6_reads
#print axioms P5J.AtMgA.hidReads_head
