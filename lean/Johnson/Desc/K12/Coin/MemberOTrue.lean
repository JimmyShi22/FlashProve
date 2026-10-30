-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- (Where this and lean/THEOREM.md differ, the page holds.)
/-
Johnson/Desc/K12/Coin/MemberOTrue.lean: THE MEMBER AT THE PROXIMITY TEST O OF THE SMALLER STORED PROOF, OVER THE TRUE NAMES. One-line proofs over Johnson/Desc/K12/Law/MemberOf.lean | MemberO.lean, whose FixesP · PayKP · PayYP · PayRecP · PayNumP are Fixes · PayK · PayY · PayRec · PayNum lifted by program, the names alone turned. NO SOUNDNESS IS CLAIMED.
  fixes_eq … payNum_eq: each twin IS its original: by rfl.
  member_O_true: what the record fixes is there ∧ PayK at 768 ∧ PayY at 768 ∧ PayRec ∧ PayNum, at piO · rO · tO.
A MEMBER OF PayK | PayY, NOT OF THE PROMISE: the promise of k12_lawPaidO | k12_lawPaidYO is FirstOpensOwn ∧ PayK | PayY; AtPlaceOwn is not shown either.
-/
import Johnson.Desc.K12.Coin.PaidY
import Johnson.Desc.K12.Law.BatValsPayAt
import Johnson.Desc.K12.Law.MemberO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open H2K.Member (FixesP PayKP PayYP PayRecP PayNumP piO tO rO member_O payY_O payRec_O payNum_O o_v0)

theorem fixes_eq : @Fixes = @FixesP := rfl
theorem payK_eq : @H2K.Pin.PayK = @PayKP := rfl
theorem payY_eq : @PayY = @PayYP := rfl
theorem payRec_eq : @H2K.Pin.PayRec = @PayRecP := rfl
theorem payNum_eq : @H2K.Pin.PayNum = @PayNumP := rfl

theorem member_O_true :
    (∃ a rest G0 Ly D, Fixes piO tO a rest G0 Ly D) ∧
    H2K.Pin.PayK piO (fun s => rO s.st) 768 tO ∧ PayY piO (fun s => rO s.st) 768 tO ∧
    H2K.Pin.PayRec piO tO ∧ H2K.Pin.PayNum piO tO := by
  have h := member_O.2.1
  rw [o_v0] at h
  exact ⟨member_O.1, h, payY_O, payRec_O, payNum_O⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.fixes_eq
#print axioms VerifiableInference.Desc.K12.Coin.payK_eq
#print axioms VerifiableInference.Desc.K12.Coin.payY_eq
#print axioms VerifiableInference.Desc.K12.Coin.payRec_eq
#print axioms VerifiableInference.Desc.K12.Coin.payNum_eq
#print axioms VerifiableInference.Desc.K12.Coin.member_O_true
