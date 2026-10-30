--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/Part4/DataOfWAtHead.lean: THE PROOF FILE's LAST CHAIN's PROXIMITY TEST (the place W):
W's DATA AT THE TEST's OWN, LONGER FRONT IS W's DATA AT THE CHALLENGES THAT FIX ITS SENDER's TABLE,
under the library's head.

WHAT IT IS NOT.
  * CONDITIONAL ON THE HEAD h (`P5J.AtMgA` at the format's second hash function; the full size).
  * NOTHING NEW IS PROVED OF THE COUNT: that the filling counts just the rounds in front of number
    356 of the first chain is the library's own `k13_wHeard_is_rounds`
    (AtFullSide/K13/WFillAtHead.lean), called; that a filling's total call reads no more than it counts is another author's
    `w_data_behind` (AtFullSide/K12/FirstArmsK1.lean), called.
  * It says how many challenges the data READS. What the data yields, and whether the filler `pile`
    yields the verifier's pile, is not said: `pile` is a letter.
  * That a thread's table of W's tree is fixed after just that many challenges is the caller's.
  * In the side library. Nothing on completeness, on soundness or on what is hidden.

  `heardOfW`    at every address the filling of W's main rows counts no more challenges than the
                rounds in front of number 356
  `dataOfWAtHead`   at two fronts, the second's challenges the first's cut at that number, and at
                any two numbers of a first tree: the two jobs at W's sending have the same data.
                msg: the sending's messages: a letter here
  `dataOfWBehind`   the same at the written messages, for its caller
-/
import AtFullSide.K12.FirstArmsK1
import AtFullSide.K13.WFillAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12.Part4
open ProofFile.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place} {Xi X : Type}

/-- **The filling of W's main rows counts no more challenges than the rounds in front of number
356.** CONDITIONAL on h. -/
theorem heardOfW (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    (pile : ProofFile.Pub → ProofFile.Ground → K13.PileOf Xi) (G : ProofFile.Ground) (x : Xi) (a : MsgAddr) :
    (K13.wDataAt pile Zp G x).heardAt a ≤ roundsTo cF.blocksInOrder 356 :=
  Nat.le_of_eq (AtFullSide.K13.k13_wHeard_is_rounds h)

/-- **W's data at a front is W's data at that front's challenges cut at the rounds in front of
number 356.** CONDITIONAL on h. -/
theorem dataOfWAtHead (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    (pile : ProofFile.Pub → ProofFile.Ground → K13.PileOf Xi) (G : ProofFile.Ground)
    (msg : Array OnBytes.OracleNotice) (n₁ n₂ : ℕ) (w : K1.PlaceIn Xi) (fr fr' : Front X)
    (hh : fr'.heard = fr.heard.take (roundsTo cF.blocksInOrder 356)) :
    (K1.wJobAt (X := X) Zp.first (K1.wGp Zp) 4 msg n₁ (K13.wDataAt pile Zp G)).data w fr =
      (K1.wJobAt (X := X) Zp.first (K1.wGp Zp) 4 msg n₂ (K13.wDataAt pile Zp G)).data w fr' := by
  funext k i j
  exact AtFullSide.K12.w_data_behind Zp.first (K1.wGp Zp) msg n₁ n₂ (K13.wDataAt pile Zp G) w fr fr'
    (roundsTo cF.blocksInOrder 356) hh (fun _ => heardOfW h pile G w.x _) k i j

/-- **The same at the written messages of W's sending**, in the order of arguments of its caller
(AtFullSide/K12/Part4/FirstArmsUnderTheHead.lean). CONDITIONAL on h. -/
theorem dataOfWBehind (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    (pile : ProofFile.Pub → ProofFile.Ground → K13.PileOf Xi) (G : ProofFile.Ground) (n₁ n₂ : ℕ)
    (w : K1.PlaceIn Xi) (fr fr' : Front X)
    (hh : fr'.heard = fr.heard.take (roundsTo cF.blocksInOrder 356)) :
    (K1.wJobAt (X := X) Zp.first (K1.wGp Zp) 4 VerifiableInference.Desc.K13.Law.wMsgFull n₁
        (K13.wDataAt pile Zp G)).data w fr =
      (K1.wJobAt (X := X) Zp.first (K1.wGp Zp) 4 VerifiableInference.Desc.K13.Law.wMsgFull n₂
        (K13.wDataAt pile Zp G)).data w fr' :=
  dataOfWAtHead h pile G _ n₁ n₂ w fr fr' hh

end AtFullSide.K12.Part4

#print axioms AtFullSide.K12.Part4.heardOfW
#print axioms AtFullSide.K12.Part4.dataOfWAtHead
#print axioms AtFullSide.K12.Part4.dataOfWBehind
