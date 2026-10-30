-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/SvLaidHeard.lean: A RIDER TO Law/SvLaid.lean (whose bytes do not turn): x.sV IS THE NUMBER OF THE SECOND END VALUE OF THE HEAD's OWN SUMCHECK, AS IT WAS HEARD: the clause that the merge asks for: WITH THE HEARING's OWN
EQUATION (without it "there is an H whose second end value's variable is that slot" would be empty: any H will do).
  sv_heard   where (blockAt h iU3 work l).decide s rs gs = .ok s' from a WellLaid ledger: there are the letters g that given returns at s, and H, with hear (the ledger in front) rs = some (H, THE LEDGER BEHIND, []), the record behind holds x = some x', and
             (H.2.2.logits.end_ 0).var = Aff.slot x'.tH.sEnd · (H.2.2.logits.end_ 1).var = Aff.slot x'.sV.
WHAT IT IS NOT: as Law/SvLaid.lean's head. Nothing on soundness.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.SvLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Aff Fork)
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc.First (S)

theorem sv_heard (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hWL : WellLaid ((seatAt h iU3).ledger s))
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    ∃ (g : Given) (H : HeardAll) (o' : VerifiableInference.Desc.First.HeadOwn)
      (x' : OnBytes.Model.Head.Heard),
      given (parOf h work) (seatAt h iU3) s = .ok g ∧
      hear ((seatAt h iU3).ledger s) rs = some (H, (seatAt h iU3).ledger s', []) ∧
      s'.here = .head o' ∧ o'.x = some x' ∧
      (H.2.2.logits.end_ 0).var = Aff.slot x'.tH.sEnd ∧
      (H.2.2.logits.end_ 1).var = Aff.slot x'.sV := by
  have hd' : decideBy (fun _ => rounds) (fun _ => hear) (fun _ _ => forTheMerge) (parOf h work)
      (seatAt h iU3) s rs = .ok s' := hd
  obtain ⟨g, H, F, w, s1, s2, hg, hhear, e1, e2, hs'⟩ := Came.decide_hears hd'
  have hs2 : s' = s2 := hs'
  subst hs2
  have hsz : Sized ((seatAt h iU3).ledger s) := ⟨hWL.2.1, hWL.2.2, hWL.1⟩
  obtain ⟨F0, t, hL0, hsum⟩ := hear_last hhear
  obtain ⟨j, hj, hj0, E0, E1⟩ := ends_at (hL0.sized hsz) hsum
  have hled : (seatAt h iU3).ledger s' = F := seatAt_fit h iU3 s F H w s1 s' e1 e2
  obtain ⟨o, x, ho, hx, rfl⟩ := setHeard_form h iU3 e2
  have hsE : slotOf (H.2.2.logits.end_ 0) = j := by
    unfold slotOf
    rw [E0]
    rfl
  refine ⟨g, H, _, _, hg, by rw [hled]; exact hhear, rfl, rfl, ?_, ?_⟩
  · rw [E0]
    show Aff.slot j = Aff.slot (slotOf (H.2.2.logits.end_ 0))
    rw [hsE]
  · rw [E1]
    show Aff.slot (j + 1) = Aff.slot (slotOf (H.2.2.logits.end_ 0) + 1)
    rw [hsE]

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.sv_heard
