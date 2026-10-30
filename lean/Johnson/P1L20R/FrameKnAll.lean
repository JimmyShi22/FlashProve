-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--



/-
Johnson/P1L20R/FrameKnAll.lean:
THE FIELD kn OF FrameOwed4 (FrameFourAll.lean), TO THE LETTER, UNDER THE ONE HEAD ALONE:
of every statement that is reached at the seated term and bears no mark, the tight list KnTight 0
(FrameKn.lean): the book is in order from tree 0 on, it fits, and the rows that the last closing has
returned name oracle messages for which the book has a place. One statement with its proof, and a
check by Lean that it fits the field.
  kn_atAll        h : AtMgA secondHashFunction Z D r Zp Np cF x ⊢
                  ∀ k a, h.toAtMg.rch k a → a.1.2.failed = none →
                  KnTight 0 k (a.1.1, a.1.2) (strsOf (FrAll D) a.2)
BY CALLS ALONE: bookInOrder_field | bookFits_field (Johnson/IMR/AtReach.lean) and
rowsSent_field (Johnson/IMR/RowsSent.lean), general in Rch and at_, laid at Rch := h.toAtMg.rch and
at_ := fun a => a.1, with the bridges raw_of_below | fold_of_below | bookHas_fold
(Johnson/IMR/AtReachFits.lean) and flat_planOk (Johnson/Desc/AtSeats/FoldFactsPaid.lean): as in the
literal of foldFacts_of_rest in AtReachFits.lean. OUT OF THE HEAD: the
scope, the reading of the files, the opening of the maker (h.laid.opened), the tests on the plan
(h.laid.planOk). «Reached» is the first half of AtMg.rch: RchAt (F0T …) k a, which unfolds to
Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k a.1.
Limits. AtMgA is shown at nothing here: NO MEMBER; where nothing is reached the statement is free.
Nothing on soundness.
-/
import Johnson.P1L20R.FrameFourAll
import Johnson.IMR.AtReachFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)
open P5J (AtMgA Free F0T)
open Meaning.K2 (bookInOrder_field bookFits_field rowsSent_field flat_planOk raw_of_below
  fold_of_below bookHas_fold)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **FrameOwed4.kn, under the one head alone.** -/
theorem kn_atAll (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ k a, h.toAtMg.rch k a → a.1.2.failed = none →
      KnTight 0 k (a.1.1, a.1.2) (strsOf (FrAll D) a.2) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hp := flat_planOk O.desc h.laid.planOk
  have hRch : ∀ k a, h.toAtMg.rch k a →
      Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) k a.1 := fun _ _ h' => h'.1
  intro k a hr hu _
  exact ⟨bookInOrder_field O hp h.toAtMg.rch (fun a => a.1) (raw_of_below hRch) k a hr hu,
    bookFits_field O hp h.toAtMg.rch (fun a => a.1) (raw_of_below hRch) k a hr hu,
    rowsSent_field O hp h.toAtMg.rch (fun a => a.1) (fold_of_below hRch)
      (fun k a h' =>
        let ⟨_, _, _, _, f⟩ := fold_of_below hRch k a h'
        bookHas_fold h.scope h.reads O hp f) k a hr hu⟩

/-- THE FIT, HELD BY THE BUILD: the statement is the field's own type: Lean takes kn_atAll h for the
field kn of FrameOwed4 h L, at every L. -/
example (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) (W : FrameOwed4 h L) :
    FrameOwed4 h L :=
  { W with kn := kn_atAll h }

end P1L20

#print axioms P1L20.kn_atAll
