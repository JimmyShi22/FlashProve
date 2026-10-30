-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/WindowDebt.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: WHAT
IS OWED FOR THE ONE STOP OF ITS PART THAT SPEAKS (a combination leaves its window), IN THE FORM OF
THE FRAME's LAWS ON SHARES (`StopDebt`, Johnson/Desc/ProofFile/Honest/Law/SharesParts.lean): at the
stated share's own value. A lemma on one stop of one part, under a premise on the cells; none of the
library's goals, and no statement of completeness or of hiding.
A measure of the set at which the part's OWN SECOND STOP speaks: no bound on falls; under a premise
on the hidden input (cellsSmall), which nothing here pays. A caller names the premise on the cells.

  `stopAt_quiet`   what `Part.stopAt` yields at the quiet part with a second stop
                   (Honest/K9/QuietMember.lean), behind one round: "the second stop" just if that
                   stop speaks at one of its two askings
  **`small_stopDebt`**   AT EVERY INPUT v WITH ITS TRACE WHOSE CELLS PASS `cellsSmall` at the
                   place's matrices: StopDebt (Run.ckP .two) (· == some Why.hid) (Face.own.sees v) p
                   [d] p.hidShare.val, p the one part of the kind's row (`small_parts`,
                   Honest/K8/QuietForm.lean), d any data of a round whose entry and kind are those
                   of the kind's own declared round
By `stop_at_round` (Honest/K8/ShareLaw.lean).
THE KIT IS NO LETTER: the bound beneath is no count of challenges: it is a tail bound over a uniform
typed matrix, carried to written messages at the kit `Run.ckP .two` alone.
Limits. THAT THE CELLS OF A VALID INPUT's TRACE PASS `cellsSmall` IS A PREMISE: it reads the hidden
input, and nothing here pays it. That the chain's data of the kind's round have that entry and kind
is a premise. One round of one request; the uniform law on that round's messages. What the head of
Honest/K8/ShareLaw.lean says of one round, one place and one fixed front, of the premise on the
cells, and of the subtraction in windowBits holds of this law too. `StopDebt`
(Johnson/Desc/ProofFile/Honest/Law/SharesParts.lean) measures over the kit's messages of the part's
own rounds alone (Iop.Rho (uLT C dsp)), at every list of challenges in front; input and part are
fixed.
-/
import Johnson.Desc.ProofFile.Honest.K8.ShareLaw
import Johnson.Desc.ProofFile.Honest.K8.QuietForm
import Johnson.Desc.ProofFile.Honest.Law.SharesParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open Prob Iop
open OnBytes.Maker (RDT uLT drawnT)
open OnBytes.Slice (wRound)
open VerifiableInference.Desc.First.K8 (Par round rd)
open VerifiableInference.Desc.First.K8.Honest
open ProofFile.Honest.K9 (quietStop)
open scoped ENNReal

variable {W₀ Rc Xi Tr X V W : Type}

/-- What `stopAt` yields at the quiet part with a second stop, behind one round. -/
theorem stopAt_quiet (h : V → List Fmt.Drawn → List Fmt.Drawn → Option String) (sh : Odds)
    (v : Option V) (loc : List Fmt.Drawn) (d : Fmt.Drawn) :
    (quietStop h sh : Part V W X).stopAt v loc [d] =
      (if (v.bind fun u => h u loc []).isSome then some Why.hid
       else if (v.bind fun u => h u loc [d]).isSome then some Why.hid else none) := by
  simp only [Part.stopAt, quietStop, quietPart, List.range_succ, List.findSome?,
    List.length_replicate, List.range_zero, List.nil_append, List.cons_append, List.take_zero,
    Option.isSome_none, Bool.false_eq_true, if_false, Nat.reduceBEq, Nat.reduceAdd,
    List.take_succ_cons, List.take_nil]
  cases (v.bind fun u => h u loc []).isSome <;> cases (v.bind fun u => h u loc [d]).isSome <;> rfl

/-- **What is owed for the window's stop.** -/
theorem small_stopDebt (cells : Tr → Cells) (P : Par × List (Nat × String × Nat)) (d : RDT)
    (he : d.entry = (round P.1).entry) (hk : d.kind = .entries) (v : Local W₀ Rc Xi Tr)
    (hP : cellsSmall P.1 (askOfInput cells P.2 v).cell = true) :
    StopDebt (Run.ckP .two) (· == some Why.hid) (Face.own.sees v)
      (quietStop (smallStop cells P) (windowShare P.1) :
        Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X) [d]
      (quietStop (smallStop cells P) (windowShare P.1) :
        Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).hidShare.val := by
  intro fr
  obtain ⟨⟨entry, kind, items, trees, opens⟩, stored⟩ := d
  dsimp only at he hk
  subst he hk
  refine le_trans ?_ (stop_at_round P.1 (askOfInput cells P.2 v) fr hP)
  have h1 : ∀ A : Set (wRound (rd P.1)).Chal,
      pr (unif ((wRound (rd P.1)).Chal × Unit)) (Prod.fst ⁻¹' A) =
        pr (unif (wRound (rd P.1)).Chal) A := by
    intro A
    rw [← pr_map, map_fst_unif]
  refine le_trans (pr_mono _ ?_) (le_of_eq (h1 _))
  rintro ⟨c, u⟩ hρ
  have hρ' : ((quietStop (smallStop cells P) (windowShare P.1) :
      Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).stopAt (Face.own.sees v) fr
        [(Run.ckP .two).dr (round P.1).entry .entries
          (GChal.old (b := (round P.1).entry.work) c)] == some Why.hid) = true := hρ
  rw [stopAt_quiet] at hρ'
  have e0 : ((Face.own.sees v).bind fun u => smallStop cells P u fr []) = none := rfl
  rw [e0] at hρ'
  show (smallHid P.1 (askOfInput cells P.2 v) fr _).isSome = true
  cases hn : (smallHid P.1 (askOfInput cells P.2 v) fr
      [(Run.ckP .two).dr (round P.1).entry .entries
        (GChal.old (b := (round P.1).entry.work) c)]).isSome with
  | true => exact hn
  | false =>
    have e1 : (((Face.own.sees v).bind fun u => smallStop cells P u fr
        [(Run.ckP .two).dr (round P.1).entry .entries
          (GChal.old (b := (round P.1).entry.work) c)]).isSome) = false := hn
    rw [e1] at hρ'
    simp at hρ'

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.stopAt_quiet
#print axioms ProofFile.Honest.K8.small_stopDebt
