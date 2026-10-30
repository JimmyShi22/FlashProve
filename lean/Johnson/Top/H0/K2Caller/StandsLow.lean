-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/StandsLow.lean: code switching: THE DRESS OF THE NUMBERS ProofFile.pAtK2 Z m
(Johnson/Desc/ProofFile/CarryAt.lean) AT THE SWITCHES INTO A SEGMENT: A LINK's AT m BELOW 23, THE
HEAD's AT m = 23: under the test spotsFitB Z (K2Caller/PAtSeated.lean) and «25 links». NO
SUB-PROTOCOL IMPORTS THIS FILE.
  stands_low      where pAtK2? Z m answers, m below 24: the dress is the head's at 23, else a link's
                  (the place opens group m + 1, which is not 25: so it has the link m + 1; its dress
                  goes by its link: the test's second half)
  stands_open     in the goals' scope, at an opening whose description's test on the list of rounds
                  accepts: the same without «answers» (pAt_answers_low, Opts/SpotsAnswer.lean)
  stands23        so: (ProofFile.pAtK2 Z 23).stands = .head
LIMITS. At m = 24 see stands24 (K2Caller/Stands24.lean: not the head's) and k02_sits_pAt
(K2Caller/SitsAtP.lean: the finish's). spotsFitB IS A NAMED TEST THAT THE VERIFIER DOES NOT RUN. «25
links» is a premise. No soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.Stands24
import Johnson.Top.H0.Opts.SpotsAnswer

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 At)
open ProofFile (Cl)

theorem stands_low {Z : ProofFile.Pub} (hT : spotsFitB Z = true)
    (hL : Z.s₀.check.frame.shape.link.length = 25) {m : Nat} (hm : m < 24)
    (hs : (ProofFile.pAtK2? Z m).isSome = true) :
    (ProofFile.pAtK2 Z m).stands = if m = 23 then .head else .link := by
  unfold ProofFile.pAtK2? at hs
  unfold ProofFile.pAtK2 ProofFile.pAtK2?
  cases hf : (ProofFile.k2SpotsAt Z).find? (fun x => x.2.grp == m + 1) with
  | none =>
    rw [hf] at hs
    cases hs
  | some y =>
    have hy := List.mem_of_find?_eq_some hf
    have hg : y.2.grp = m + 1 := by simpa using List.find?_some hf
    unfold spotsFitB at hT
    rw [Bool.and_eq_true] at hT
    have hD := of_decide_eq_true (List.all_eq_true.1 hT.2 y hy)
    have hgr := spot_group hy
    rw [hg, hL] at hgr
    have hl : y.1.place.link = some (m + 1) := by
      cases e : y.1.place.link with
      | none =>
        rw [e] at hgr
        have : m + 1 = 25 := hgr
        omega
      | some l =>
        rw [e] at hgr
        have : m + 1 = l := hgr
        rw [this]
    show y.2.stands = _
    rw [hD, hL, hl]
    show (if m + 1 + 1 == 25 then At.head else At.link) = _
    by_cases h23 : m = 23
    · subst h23
      rfl
    · rw [if_neg (by simp; omega), if_neg h23]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem stands_open (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : F.planOk = true)
    (hT : spotsFitB Z = true) (hL : Z.s₀.check.frame.shape.link.length = 25) {m : Nat}
    (hm : m < 24) : (ProofFile.pAtK2 Z m).stands = if m = 23 then .head else .link :=
  stands_low hT hL hm (P1K2.pAt_answers_low hS hR O hp m hm)

/-- **At the switch at the output head's segment the numbers stand in the head's dress.** -/
theorem stands23 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : F.planOk = true)
    (hT : spotsFitB Z = true) (hL : Z.s₀.check.frame.shape.link.length = 25) :
    (ProofFile.pAtK2 Z 23).stands = .head :=
  stands_open hS hR O hp hT hL (by omega)

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.stands_low
#print axioms VerifiableInference.Desc.First.K2Caller.stands_open
#print axioms VerifiableInference.Desc.First.K2Caller.stands23
