-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TotalItems.lean: FOR THE ITEM "totalB": `ItemBack` (Honest/K9/TotalFront.lean) AT THE
FILLING OF Honest/K9/TotalFill.lean: THE ENTRIES THAT COST NOTHING, AND THE SPLIT AT THE APPROXIMATE RANGE PROOF's
EQUATIONS. Statements and proofs; no goal is stated. THE THREAD T IS A VARIABLE.
  `termsBack_nil`    `TermsBack` at terms that are the empty list, at every letter Front
  `guests_nil`       the library's terms at an entry "guests" (a run that makes no claim) are the empty list
  **`itemBack_guests_lay`**, **`_att`**, **`_head`**   so `ItemBack` holds at every entry (j, "guests") of the three
      sorts' orders, at every Front: these entries are nobody's debt (two in each sort's order, by the library's
      `order_layers`, `order_attention`, `order_head`, Johnson/Desc/First/Link/Law/LinkJoinPay.lean)
  **`itemBack_eqs_lay`**, **`_att`**, **`_head`**   at the entry (j, "K8.equations"): `ItemBack` from `TermsBack` at
      the library's `tmFour` (the first four terms) and `TermsBack` at `tmRest pi8` (the ties' and reads' equations):
      by `termsBack_append` (Honest/K9/TotalJoin.lean) and the sort's table's own text
No member; called by no line.
WHAT IS NOT CLAIMED. `TermsBack` at `tmFour` or at `tmRest`. `ItemBack` at any other entry. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalFill
import Johnson.Desc.ProofFile.Honest.K9.TotalJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.StillRun (valsStill fsNone)

section
variable {α : Type} {Lk : Link S Claim} {p : Desc.K9.Where} {φ : S → α} {Ok : α × Option Pub9 → Prop}
  {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Claim V W X Pb} {b : ℕ} {own : List (ℕ × ℕ)}
  {rdW : T.Wt → ℕ × ℕ → Sound.MsgQ}

/-- `TermsBack` at no term. -/
theorem termsBack_nil (tm : ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (h : ∀ n q y, tm n q y = []) (Front : S → T.Wt → Prop) : TermsBack Lk p φ Ok T b own rdW tm Front := by
  intro κ s m En ds y cols s' x z G _ a v _ _ _ n c hc
  rw [h] at hc
  exact nomatch hc

end

/-- A run that makes no claim has no term. -/
theorem guests_nil (n : ℕ) (q : Phi BetaAll × Option Pub9) (y : Bound Cb.Gl.E) :
    plainTm (valsStill Reading.gl fsNone entUnit) n q y = [] := by
  unfold plainTm valsStill
  cases q.2 <;> rfl

variable {Lk : Link S Claim} {p : Desc.K9.Where} {tlD : HTailF2} {Ok : Phi BetaAll × Option Pub9 → Prop}
  {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Claim V W X Pb} {b : ℕ} {own : List (ℕ × ℕ)}
  {rdW : T.Wt → ℕ × ℕ → Sound.MsgQ} {pC pD : First.Look.P}

theorem itemBack_guests_lay (p4 : OnBytes.Desc.First.K4.Par) (j : ℕ) (Front : S → T.Wt → Prop) :
    ItemBack Lk p (phiFill tlD) Ok (tmFillLay p4 pC pD) T b own rdW (j, "guests") Front :=
  termsBack_nil _ guests_nil Front

theorem itemBack_guests_att (A : Attention.Plan) (j : ℕ) (Front : S → T.Wt → Prop) :
    ItemBack Lk p (phiFill tlD) Ok (tmFillAtt A pC pD) T b own rdW (j, "guests") Front :=
  termsBack_nil _ guests_nil Front

theorem itemBack_guests_head (Wp : Verify.Public) (j : ℕ) (Front : S → T.Wt → Prop) :
    ItemBack Lk p (phiFill tlD) Ok (tmFillHead Wp pC pD) T b own rdW (j, "guests") Front :=
  termsBack_nil _ guests_nil Front

theorem itemBack_eqs_lay (p4 : OnBytes.Desc.First.K4.Par) (j : ℕ) (F₁ F₂ : S → T.Wt → Prop)
    (h₁ : TermsBack Lk p (phiFill tlD) Ok T b own rdW tmFour F₁)
    (h₂ : TermsBack Lk p (phiFill tlD) Ok T b own rdW (fun _ => tmRest pi8) F₂) :
    ItemBack Lk p (phiFill tlD) Ok (tmFillLay p4 pC pD) T b own rdW (j, "K8.equations") (fun s v => F₁ s v ∧ F₂ s v) :=
  termsBack_append tmFour (fun _ => tmRest pi8) F₁ F₂ h₁ h₂

theorem itemBack_eqs_att (A : Attention.Plan) (j : ℕ) (F₁ F₂ : S → T.Wt → Prop)
    (h₁ : TermsBack Lk p (phiFill tlD) Ok T b own rdW tmFour F₁)
    (h₂ : TermsBack Lk p (phiFill tlD) Ok T b own rdW (fun _ => tmRest pi8) F₂) :
    ItemBack Lk p (phiFill tlD) Ok (tmFillAtt A pC pD) T b own rdW (j, "K8.equations") (fun s v => F₁ s v ∧ F₂ s v) :=
  termsBack_append tmFour (fun _ => tmRest pi8) F₁ F₂ h₁ h₂

theorem itemBack_eqs_head (Wp : Verify.Public) (j : ℕ) (F₁ F₂ : S → T.Wt → Prop)
    (h₁ : TermsBack Lk p (phiFill tlD) Ok T b own rdW tmFour F₁)
    (h₂ : TermsBack Lk p (phiFill tlD) Ok T b own rdW (fun _ => tmRest pi8) F₂) :
    ItemBack Lk p (phiFill tlD) Ok (tmFillHead Wp pC pD) T b own rdW (j, "K8.equations") (fun s v => F₁ s v ∧ F₂ s v) :=
  termsBack_append tmFour (fun _ => tmRest pi8) F₁ F₂ h₁ h₂

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.termsBack_nil
#print axioms ProofFile.Honest.K9.guests_nil
#print axioms ProofFile.Honest.K9.itemBack_guests_lay
#print axioms ProofFile.Honest.K9.itemBack_guests_att
#print axioms ProofFile.Honest.K9.itemBack_guests_head
#print axioms ProofFile.Honest.K9.itemBack_eqs_lay
#print axioms ProofFile.Honest.K9.itemBack_eqs_att
#print axioms ProofFile.Honest.K9.itemBack_eqs_head
