-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/LPFK10R/CloseShareR.lean:
K10's 25 OF THE 358 «Hands», IN SCOPE, IN THE FORM THAT COUNTS: IM.HandsR Fk AT EVERY FENCE Fk, UNDER ONE PREMISE: «more», FENCED. CloseShare.lean's and CloseShareScope.lean's three theorems with HandsR for Hands. Statements and proofs.
  close_k10R         ∀ l < 25, ∀ Q: IM.HandsR Fk N LW PW E ft (14 * l + nA l + 4 + 1) (K9.closing Q).retype: under bookFit N PW told, «the sub-protocol at that number tells nothing», and hE.
  close_k10R_field   the same at x with (K9.closeOf p Q)[1]? = some x.
  close_k10R_scope   InScope P · readFiles P = .ok pp · IM.Open …: the same at the numbers N.withTold PW (toldC c): UNDER hE ALONE:
                     hE : ∀ l < 25, ∀ s s', Fk (14 * l + nA l + 5) s → K10Step s s' → s.failed = none → XK (N.withTold PW (toldC c)) LW PW E (14 * l + nA l + 5) s = true → E (14 * l + nA l + 5 + 1) s' = true.
WHERE THE TESTS ON THE LISTS ARE PAID: closersFit | closersNext at LW, PW: fit_w | next_w (CloseShare.lean: the landed closersFit_real | closersNext_real with the kernel's sorts_are_w) · «number 14 l + nA l + 5 of PW is of the kind K10»: k10_place_w (the kernel) · bookFit at the filled numbers: book_fit_w · «tells nothing»: told_at_ix (CloseShareScope.lean).
LIMITS. hE is a premise: E and Fk are letters. In scope, at OnBytes.secondHashFunction. Nothing on soundness.

-/
import Johnson.LPFK10R.CloseShareScope
import Johnson.LPFK10R.HandsAtK10R

set_option autoImplicit false

namespace LPFK10
open VerifiableInference.Desc (Block Chain Link FileDescription Place Oracle KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers bookFit)
open VerifiableInference.Desc.First.Close (Par K10Step)
open ProofFile (Cl)
open IM

theorem close_k10R (Fk : Nat → S → Prop) (N : Numbers) (E : Nat → S → Bool) (ft : Nat)
    (told : List (List Oracle)) (hB : bookFit N PW told = true)
    (hn : ∀ l < 25, told[14 * l + nA l + 5]? = some [])
    (hE : ∀ l < 25, ∀ s s', Fk (14 * l + nA l + 5) s → K10Step s s' → s.failed = none →
      IM.XK N LW PW E (14 * l + nA l + 5) s = true → E (14 * l + nA l + 5 + 1) s' = true) :
    ∀ l < 25, ∀ Q : Par, IM.HandsR Fk N LW PW E ft (14 * l + nA l + 4 + 1)
      (VerifiableInference.Desc.K9.closing Q : Block S Unit).retype := by
  intro l hl Q
  obtain ⟨p, hp, hk⟩ := k10_place_w hl
  exact hands_k10R_lot Fk N LW PW E ft (14 * l + nA l + 5) p Q fit_w next_w hp hk told hB
    (hn l hl) (hE l hl)

theorem close_k10R_field (Fk : Nat → S → Prop) (N : Numbers) (E : Nat → S → Bool) (ft : Nat)
    (told : List (List Oracle)) (hB : bookFit N PW told = true)
    (hn : ∀ l < 25, told[14 * l + nA l + 5]? = some [])
    (hE : ∀ l < 25, ∀ s s', Fk (14 * l + nA l + 5) s → K10Step s s' → s.failed = none →
      IM.XK N LW PW E (14 * l + nA l + 5) s = true → E (14 * l + nA l + 5 + 1) s' = true) :
    ∀ l < 25, ∀ (p : VerifiableInference.Desc.K9.Where) (Q : Par) (x : Block S Unit),
      (VerifiableInference.Desc.K9.closeOf p Q : List (Block S Unit))[1]? = some x →
      IM.HandsR Fk N LW PW E ft (14 * l + nA l + 4 + 1) x.retype := by
  intro l hl p Q x hx
  obtain rfl : (VerifiableInference.Desc.K9.closing Q : Block S Unit) = x := Option.some.inj hx
  exact close_k10R Fk N E ft told hB hn hE l hl Q

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **K10's 25, in scope, at the filled numbers, under a fence: «more», fenced, alone is left.** -/
theorem close_k10R_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (Fk : Nat → S → Prop)
    (N : Numbers) (E : Nat → S → Bool) (ft : Nat)
    (hE : ∀ l < 25, ∀ s s', Fk (14 * l + nA l + 5) s → K10Step s s' → s.failed = none →
      IM.XK (N.withTold PW (toldC c)) LW PW E (14 * l + nA l + 5) s = true →
      E (14 * l + nA l + 5 + 1) s' = true) :
    ∀ l < 25, ∀ (p : VerifiableInference.Desc.K9.Where) (Q : Par) (x : Block S Unit),
      (VerifiableInference.Desc.K9.closeOf p Q : List (Block S Unit))[1]? = some x →
      IM.HandsR Fk (N.withTold PW (toldC c)) LW PW E ft (14 * l + nA l + 4 + 1) x.retype :=
  close_k10R_field Fk (N.withTold PW (toldC c)) E ft (toldC c) (book_fit_w N (toldC c))
    (fun _ hl => told_at_ix hS hR O hl) hE

end

end LPFK10

#print axioms LPFK10.close_k10R
#print axioms LPFK10.close_k10R_field
#print axioms LPFK10.close_k10R_scope
