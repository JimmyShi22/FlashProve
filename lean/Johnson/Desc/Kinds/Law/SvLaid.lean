-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/SvLaid.lean: FOR K11's FENCE "x.sV's value at every yes": WHERE THE OUTPUT HEAD's BLOCK SAYS YES, THE RECORD BEHIND HOLDS x WITH x.sV = THE LAST NUMBER THAT
THE BLOCK's HEARING TOOK: the number of the second end value of the head's own sumcheck; it is filled.
  ends_at      where a sumcheck with two end values returns, from a ledger with a place for each number: the two end values' variables are the bare slots F1.next - 2 and F1.next - 1.
  sv_at_yes    (blockAt h iU3 work l).decide s rs gs = .ok s', the ledger in front WellLaid: the record behind stands in the head's link with x = some x', and: x'.tH.sEnd + 2 = the next number of the ledger behind · x'.sV = x'.tH.sEnd + 1 [the
               definition] · that number is filled in the ledger behind · it is at least the next number of the ledger in front.
  sv_of        the same for blockOf W l.
WHAT IT IS NOT. Nothing on soundness. Not the NUMBER in the plan's numbers (Law/Takes.lean: the hearing takes 41 + 4 lt + 4 |zt| + 4 lPd numbers: so x'.sV is the front's next + that count - 1; |zt| = lt is not shown there). Nothing on what lies hidden under it (Law/K06Statement.lean:
WeightTrue is a premise of the row). That no block between H:4 and the merge turns x: the fold's.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.TakesAt
import Johnson.Desc.Kinds.Law.Lemma2b
import Johnson.Desc.Kinds.Law.RowAtDecide
import Johnson.Desc.Kinds.Law.KeepsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Aff Fork)
open OnBytes.PscRun (Sized)
open Norm (lt ls d lPd T S2)
open VerifiableInference.Desc.First (S)

/-- Where a sumcheck with two end values returns: their variables are the last two numbers taken. -/
theorem ends_at {z : Point} {F0 F1 : Fork} {t : List Fmt.RoundView} {Sm : Sum} (hF : Sized F0)
    (h : sumcheck z 2 F0 t = some (Sm, F1, [])) :
    ∃ j, j + 2 = F1.next ∧ F0.next ≤ j ∧ (Sm.end_ 0).var = Aff.slot j ∧
      (Sm.end_ 1).var = Aff.slot (j + 1) := by
  have hn := (takes_sumcheck hF h).next
  obtain ⟨ld, cA, Fa, G, hd, es, _, a2, a3, a4, _, a6, hS⟩ := sumcheck_spec h
  obtain ⟨_, Tt, R, _, _, hhd, _⟩ := Part.MaskedSum.hear_spec a4
  have hna := ((takes_hide hF a3).cast (lead_length a2)).next
  have hsE : hd.sEnd = Fa.next + (2 * z.size + 3) := by
    rw [hhd]
    show Fa.next + Part.MaskedSum.ownSlots (callOf 1 z 2).all = _
    rw [own_callOf]
  obtain ⟨E0, E1⟩ := hiddenFrom_two a6
  have hl : (callOf 1 z 2).lead = 1 := rfl
  refine ⟨hd.sEnd, by rw [hsE, hn, hna, hl]; omega, by rw [hsE, hna]; omega, ?_, ?_⟩
  · rw [hS]
    show (es.getD 0 {}).var = _
    rw [E0]
  · rw [hS]
    show (es.getD 1 {}).var = _
    rw [E1]

section At

variable (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat)

/-- **x.sV AT EVERY YES.** -/
theorem sv_at_yes (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hWL : WellLaid ((seatAt h iU3).ledger s))
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    ∃ (o' : VerifiableInference.Desc.First.HeadOwn) (x' : OnBytes.Model.Head.Heard),
      s'.here = .head o' ∧ o'.x = some x' ∧
      x'.tH.sEnd + 2 = ((seatAt h iU3).ledger s').next ∧ x'.sV = x'.tH.sEnd + 1 ∧
      OnBytes.PscRun.Filled ((seatAt h iU3).ledger s') x'.sV ∧
      ((seatAt h iU3).ledger s).next ≤ x'.tH.sEnd := by
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) (parOf h work)
      (seatAt h iU3) s rs = .ok s' := hd
  obtain ⟨g, H, F, w, s1, s2, hg, hhear, e1, e2, hs'⟩ := Came.decide_hears hd'
  have hs2 : s' = s2 := hs'
  subst hs2
  have hsz : Sized ((seatAt h iU3).ledger s) := ⟨hWL.2.1, hWL.2.2, hWL.1⟩
  have TT := hear_takes hsz hhear
  obtain ⟨F0, t, hL0, hsum⟩ := hear_last hhear
  obtain ⟨j, hj, hj0, E0, E1⟩ := ends_at (hL0.sized hsz) hsum
  have hled : (seatAt h iU3).ledger s' = F := seatAt_fit h iU3 s F H w s1 s' e1 e2
  obtain ⟨o, x, ho, hx, rfl⟩ := setHeard_form h iU3 e2
  have hsE : slotOf (H.2.2.logits.end_ 0) = j := by
    unfold slotOf
    rw [E0]
    rfl
  refine ⟨_, _, rfl, rfl, ?_, rfl, ?_, ?_⟩
  · rw [hled]
    show slotOf (H.2.2.logits.end_ 0) + 2 = F.next
    rw [hsE, hj]
  · rw [hled]
    show OnBytes.PscRun.Filled F (slotOf (H.2.2.logits.end_ 0) + 1)
    rw [hsE]
    have h1 := hL0.next
    exact TT.full (j + 1) (by omega) (by rw [← TT.next]; omega)
  · show _ ≤ slotOf (H.2.2.logits.end_ 0)
    rw [hsE]
    have h1 := hL0.next
    omega

/-- The same for the block as it rides. -/
theorem sv_of (W : OnBytes.Model.Verify.Public) (b : Block S Unit) (hb : blockOf W l = some b)
    (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hWL : WellLaid (s.fork?.getD {})) (hd : b.decide s rs gs = .ok s') :
    ∃ (o' : VerifiableInference.Desc.First.HeadOwn) (x' : OnBytes.Model.Head.Heard),
      s'.here = .head o' ∧ o'.x = some x' ∧ x'.tH.sEnd + 2 = (s'.fork?.getD {}).next ∧
      x'.sV = x'.tH.sEnd + 1 ∧ OnBytes.PscRun.Filled (s'.fork?.getD {}) x'.sV ∧
      (s.fork?.getD {}).next ≤ x'.tH.sEnd := by
  obtain ⟨iU3, _, rfl⟩ := Option.map_eq_some_iff.mp hb
  exact sv_at_yes W.hS iU3 _ l s s' rs gs hWL hd

end At

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.ends_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.sv_at_yes
#print axioms VerifiableInference.Desc.Kinds.Head.Law.sv_of
