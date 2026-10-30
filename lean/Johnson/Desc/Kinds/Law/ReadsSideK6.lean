-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ReadsSideK6.lean: THE WITNESS's SIDE OF THE RIDING AT THE HEAD's FIVE PARTS,
FREE OF THE TABLE's LIST AND OF THE RECORD OF CONDITIONS PlanK6: what the sentences of
Law/HeadCutsK6.lean's filling read of a witness, BY REPORT, NOT SHOWN HERE, and that they read no
more. Definitions, statements and proofs. Over the tools of Law/ReadsOkK6.lean.

  constrK6_side    for each part p but lookDigits: two witnesses that are one on the tenants of
                   segment 24's group (each tenant's message and pad), and, at lookCalls and
                   lookCallsHeard, have one stored table, and, at lookCalls, one token, have the
                   item constr 24 p together.
  readsK6W         THE LIST, WRITTEN OUT: at constr 24 p: the group's tenants' messages and pads; at
                   lookCalls and lookCallsHeard the cells; at lookCalls the token; [] at lookDigits
                   and at every other item.
  readsK6W_ok      two witnesses that are one on that list give the sentence one truth value, at
                   every record and strings.

  readsK6W_sub     the list is a part of what the table books there (Item.reads).
  readsOk_k6       so: the riding frame's own form (ReadsOkQ) at the head's five items.

AGAINST THE TABLE. The list is no copy of the table's Item.reads: "readsK6W i is a part of
Item.reads i" can fail: at a table in which rider and lookCalls are booked at the
tenants sent at moment 0 alone, readsK6W_sub's proof does not go through; at this library's
table it is a theorem.

WHAT IT IS NOT. Implications. PREMISES: put turns the reply alone · the kind's tests on the plan
(Par.ok) · SeatsNamed and GroupsSeated, which stand in hidAtSeat's own type. At H := hidAtSeat.
The numeral 24. Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Desc.Kinds.Law.ReadsOkK6

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open Inst.Model (ppref)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (Numbers Item Comp ModelPart)
open VerifiableInference.Desc.Sound (Mem MsgT SeatsNamed GroupsSeated sameQ)

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
  (pl : Nat → Nat × Bool × Nat × Nat)

/-- **THE WITNESS's SIDE, FREE OF THE TABLE's LIST AND OF PlanK6.** -/
theorem constrK6_side {P : Type} (tab : Nat → Nat) (put : P5J.TReq → Fin ppref.V → P5J.TReq)
    (tokV : Tok → Fin ppref.V) (req : P × P5J.TS → P5J.TReq)
    (dec : P × P5J.TS → Strs → Option (Fin rows → Fin cols → GE))
    (hSN : SeatsNamed arr N s seat) (hGS : GroupsSeated msR N) (tokH : P × P5J.TS → Fin ppref.V)
    (digitsPart : Nat → P × P5J.TS → Strs → Wit (Fin rows → Fin cols → GE) Tok MsgT → Prop)
    (hK : PutKeeps put) (hplan : (parOf Wp.hS (workOf Wp)).ok = true) (p : P5J.TPart)
    (hp : p ≠ .lookDigits) (a : P × P5J.TS) (y : Strs)
    (w w' : Wit (Fin rows → Fin cols → GE) Tok MsgT) (hG : OneOn arr (N.group 24) w w')
    (hc : p = .lookCalls ∨ p = .lookCallsHeard → w.cells = w'.cells)
    (ht : p = .lookCalls → w.tok = w'.tok)
    (h : P5J.constrQAt 24 put (P5J.hidAtSeat Wp cs arr msR N s seat tokV req dec hSN hGS)
      (headPartK6 cs arr msR N s seat Wp pl tab put
        (P5J.hidAtSeat Wp cs arr msR N s seat tokV req dec hSN hGS) tokH) digitsPart 24 p a y w) :
    P5J.constrQAt 24 put (P5J.hidAtSeat Wp cs arr msR N s seat tokV req dec hSN hGS)
      (headPartK6 cs arr msR N s seat Wp pl tab put
        (P5J.hidAtSeat Wp cs arr msR N s seat tokV req dec hSN hGS) tokH) digitsPart 24 p a y
      w' := by
  have hO := ownQ_same cs arr msR N s seat w w' hG
  obtain ⟨c1, c2⟩ := comp_of_cut cs arr msR N s seat Wp pl w w' (by unfold ownCut; rw [hO])
  have hcomp : w.cells = w'.cells → (compCut cs arr msR N s seat Wp pl w).1 =
      (compCut cs arr msR N s seat Wp pl w').1 := by
    intro hcells
    unfold compCut compOf ownCut
    rw [hO, hcells]
  unfold P5J.constrQAt at h ⊢
  rw [if_neg hp] at h ⊢
  obtain ⟨hb, hh⟩ := h
  cases p with
  | lookDigits => exact absurd rfl hp
  | idn =>
    refine ⟨fun e => absurd e (by decide), fun M i hM hi => ?_⟩
    have h2 := hh M i hM hi
    rw [if_pos rfl] at h2 ⊢
    exact headPartK6_side cs arr msR N s seat Wp pl tab put _ tokH hK hplan i i a y y w w' .idn c1
      c2 (fun _ => hO) (Or.inl rfl) h2
  | rider =>
    refine ⟨fun e => absurd e (by decide), fun M i hM hi => ?_⟩
    have h2 := hh M i hM hi
    rw [if_pos rfl] at h2 ⊢
    exact headPartK6_side cs arr msR N s seat Wp pl tab put _ tokH hK hplan i i a y y w w' .rider c1
      c2 (fun _ => hO) (Or.inr (Or.inl rfl)) h2
  | small =>
    refine ⟨fun _ => ?_, fun M i hM hi => ?_⟩
    · have hb' := hb rfl
      rw [P5J.base_at] at hb' ⊢
      rw [← readAt_same cs arr msR N 24 w w' hG]
      exact hb'
    · have h2 := hh M i hM hi
      rw [if_pos rfl] at h2 ⊢
      exact headPartK6_side cs arr msR N s seat Wp pl tab put _ tokH hK hplan i i a y y w w' .small
        c1 c2 (fun _ => hO) (Or.inr (Or.inr rfl)) h2
  | lookCalls =>
    have hcells := hc (Or.inl rfl)
    have htok := ht rfl
    refine ⟨fun e => absurd e (by decide), fun M i hM hi => ?_⟩
    have h2 := hh M i hM hi
    rw [if_pos rfl] at h2 ⊢
    have h3 : partsAtX cs arr msR N s seat Wp pl tab i (put (req a) (tokV w.tok)).val w
        .lookCalls := h2
    show partsAtX cs arr msR N s seat Wp pl tab i (put (req a) (tokV w'.tok)).val w' .lookCalls
    rw [← htok, ← callsPart_congr cs arr msR N s seat Wp pl tab i _ w w' hcells (hcomp hcells)]
    exact h3
  | lookCallsHeard =>
    have hcells := hc (Or.inr rfl)
    refine ⟨fun e => absurd e (by decide), fun M i hM hi => ?_⟩
    have h2 := hh M i hM hi
    rw [if_pos rfl] at h2 ⊢
    have h3 : partsAtX cs arr msR N s seat Wp pl tab i (put (req a) (tokH a)).val w
        .lookCalls := h2
    show partsAtX cs arr msR N s seat Wp pl tab i (put (req a) (tokH a)).val w' .lookCalls
    rw [← callsPart_congr cs arr msR N s seat Wp pl tab i _ w w' hcells (hcomp hcells)]
    exact h3

/-- **WHICH COMPONENTS OF THE WITNESS THE SENTENCES OF THIS LAYER READ, WRITTEN OUT.** -/
def _root_.VerifiableInference.Desc.Kinds.Head.Law.readsK6W (arr : Nat → Nat → Nat) (N : Numbers) :
    Item → List Comp
  | .constr 24 p =>
    if p = .lookDigits then []
    else ((N.group 24).flatMap fun x => [Comp.msg (arr x.1 x.2), Comp.pad x.1 x.2]) ++
      (if p = .lookCalls ∨ p = .lookCallsHeard then [Comp.cells] else []) ++
      (if p = .lookCalls then [Comp.tok] else [])
  | _ => []

/-- **TWO WITNESSES THAT ARE ONE ON readsK6W GIVE THE SENTENCE ONE TRUTH VALUE.** -/
theorem readsK6W_ok {P : Type} (tab : Nat → Nat) (put : P5J.TReq → Fin ppref.V → P5J.TReq)
    (tokV : Tok → Fin ppref.V) (req : P × P5J.TS → P5J.TReq)
    (dec : P × P5J.TS → Strs → Option (Fin rows → Fin cols → GE))
    (hSN : SeatsNamed arr N s seat) (hGS : GroupsSeated msR N) (tokH : P × P5J.TS → Fin ppref.V)
    (digitsPart : Nat → P × P5J.TS → Strs → Wit (Fin rows → Fin cols → GE) Tok MsgT → Prop)
    (hK : PutKeeps put) (hplan : (parOf Wp.hS (workOf Wp)).ok = true) (p : P5J.TPart)
    (hp : p ≠ .lookDigits) (a : P × P5J.TS) (y : Strs)
    (w w' : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (hs : ∀ c ∈ readsK6W arr N (.constr 24 p), sameQ c w w') :
    P5J.constrQAt 24 put (P5J.hidAtSeat Wp cs arr msR N s seat tokV req dec hSN hGS)
      (headPartK6 cs arr msR N s seat Wp pl tab put
        (P5J.hidAtSeat Wp cs arr msR N s seat tokV req dec hSN hGS) tokH) digitsPart 24 p a y w ↔
    P5J.constrQAt 24 put (P5J.hidAtSeat Wp cs arr msR N s seat tokV req dec hSN hGS)
      (headPartK6 cs arr msR N s seat Wp pl tab put
        (P5J.hidAtSeat Wp cs arr msR N s seat tokV req dec hSN hGS) tokH) digitsPart 24 p a y
      w' := by
  have hs' : ∀ c ∈ ((N.group 24).flatMap fun x => [Comp.msg (arr x.1 x.2), Comp.pad x.1 x.2]) ++
      (if p = .lookCalls ∨ p = .lookCallsHeard then [Comp.cells] else []) ++
      (if p = .lookCalls then [Comp.tok] else []), sameQ c w w' := by
    intro c hc
    refine hs c ?_
    show c ∈ (if p = .lookDigits then [] else _)
    rw [if_neg hp]
    exact hc
  have hG : OneOn arr (N.group 24) w w' := by
    intro x hx
    have hm : ∀ c ∈ [Comp.msg (arr x.1 x.2), Comp.pad x.1 x.2], sameQ c w w' := fun c hc =>
      hs' c (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨x, hx, hc⟩)))
    exact ⟨hm (Comp.msg (arr x.1 x.2)) (by simp), hm (Comp.pad x.1 x.2) (by simp)⟩
  have hc : p = .lookCalls ∨ p = .lookCallsHeard → w.cells = w'.cells := fun e =>
    hs' Comp.cells (List.mem_append_left _ (List.mem_append_right _ (by rw [if_pos e]; simp)))
  have ht : p = .lookCalls → w.tok = w'.tok := fun e =>
    hs' Comp.tok (List.mem_append_right _ (by rw [if_pos e]; simp))
  have hG' : OneOn arr (N.group 24) w' w := fun x hx => ⟨(hG x hx).1.symm, (hG x hx).2.symm⟩
  exact ⟨constrK6_side cs arr msR N s seat Wp pl tab put tokV req dec hSN hGS tokH digitsPart hK
      hplan p hp a y w w' hG hc ht,
    constrK6_side cs arr msR N s seat Wp pl tab put tokV req dec hSN hGS tokH digitsPart hK
      hplan p hp a y w' w hG' (fun e => (hc e).symm) fun e => (ht e).symm⟩

/-- **THE LIST IS A PART OF WHAT THE TABLE BOOKS**, at the head's segment. -/
theorem readsK6W_sub (links : List ModelPart) (hl : links[24]? = some .head) (p : P5J.TPart) :
    ∀ c ∈ readsK6W arr N (.constr 24 p), c ∈ (Item.constr 24 p).reads arr N links := by
  intro c hc
  by_cases hp : p = .lookDigits
  · subst hp
    exact absurd hc (by simp [readsK6W])
  · have hc' : c ∈ ((N.group 24).flatMap fun x => [Comp.msg (arr x.1 x.2), Comp.pad x.1 x.2]) ++
        (if p = .lookCalls ∨ p = .lookCallsHeard then [Comp.cells] else []) ++
        (if p = .lookCalls then [Comp.tok] else []) := by
      have h1 : c ∈ (if p = .lookDigits then [] else _) := hc
      rw [if_neg hp] at h1
      exact h1
    unfold Item.reads
    rcases List.mem_append.1 hc' with h1 | h1
    · rcases List.mem_append.1 h1 with h2 | h2
      · exact List.mem_append_left _ h2
      · refine List.mem_append_right _ ?_
        cases p <;> simp_all
    · refine List.mem_append_right _ ?_
      cases p <;> simp_all

/-- **THE WITNESS's SIDE IN THE RIDING FRAME's OWN FORM** (Johnson/Desc/Sound/BordersSides.lean:
ReadsOkQ) at the head's five items. -/
theorem readsOk_k6 {P : Type} (links : List ModelPart) (hl : links[24]? = some .head)
    (tab : Nat → Nat) (put : P5J.TReq → Fin ppref.V → P5J.TReq) (tokV : Tok → Fin ppref.V)
    (req : P × P5J.TS → P5J.TReq)
    (dec : P × P5J.TS → Strs → Option (Fin rows → Fin cols → GE))
    (hSN : SeatsNamed arr N s seat) (hGS : GroupsSeated msR N) (tokH : P × P5J.TS → Fin ppref.V)
    (digitsPart : Nat → P × P5J.TS → Strs → Wit (Fin rows → Fin cols → GE) Tok MsgT → Prop)
    (hK : PutKeeps put) (hplan : (parOf Wp.hS (workOf Wp)).ok = true) (p : P5J.TPart)
    (hp : p ≠ .lookDigits) (a : P × P5J.TS) (y : Strs)
    (w w' : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (hs : ∀ c ∈ (Item.constr 24 p).reads arr N links, sameQ c w w')
    (h : P5J.constrQAt 24 put (P5J.hidAtSeat Wp cs arr msR N s seat tokV req dec hSN hGS)
      (headPartK6 cs arr msR N s seat Wp pl tab put
        (P5J.hidAtSeat Wp cs arr msR N s seat tokV req dec hSN hGS) tokH) digitsPart 24 p a y w) :
    P5J.constrQAt 24 put (P5J.hidAtSeat Wp cs arr msR N s seat tokV req dec hSN hGS)
      (headPartK6 cs arr msR N s seat Wp pl tab put
        (P5J.hidAtSeat Wp cs arr msR N s seat tokV req dec hSN hGS) tokH) digitsPart 24 p a y
      w' :=
  (readsK6W_ok cs arr msR N s seat Wp pl tab put tokV req dec hSN hGS tokH digitsPart hK hplan p hp
    a y w w' fun c hc => hs c (readsK6W_sub arr N links hl p c hc)).1 h

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.readsK6W_sub
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.readsOk_k6
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.constrK6_side
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.readsK6W_ok
