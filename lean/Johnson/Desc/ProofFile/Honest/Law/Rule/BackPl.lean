-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/BackPl.lean: the six parts of `trWhole`
(Honest/Law/Rule/Back.lean): what the three rounds without a challenge send, and the three chains'
transcripts of what is shown. Eight lemmas, each an equation on `trWhole`; no definition.

  `whole_F`, `whole_1`, `whole_J'`, `whole_J`, `whole_2`, `whole_snd`, `whole_3'`, `whole_3`

A chain's transcript from rounds as produced is compared with the one from what is shown in
Honest/Law/BackChain.lean (`trLaid`, `laid_plains`, `laid_read`).

Limits.
  * Nothing is said on any strategy.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Back

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes.Maker (WholeD chainsOf)
open _root_.Run.PQ (CK)

/-! ## The six parts of the whole transcript -/

section
variable {TF TJ T3 : Type} (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3)
  (v : TF × TJ × T3) (L : Laid) (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh)

theorem whole_F : (chainsOf C D tF tJ t3).msgF (trWhole C D tF tJ t3 v L ρ) = ((), v.1) := rfl

theorem whole_1 : (chainsOf C D tF tJ t3).tr₁ (trWhole C D tF tJ t3 v L ρ) =
    trOff C D.ds₁ (L.first.map (·.2.1)) ((chainsOf C D tF tJ t3).rho₁ ρ) :=
  Iop.Tr.fst_app _ _

theorem whole_J' : (chainsOf C D tF tJ t3).trJ (trWhole C D tF tJ t3 v L ρ) =
    ((((), v.2.1), ((chainsOf C D tF tJ t3).rhoJ ρ).1,
      Iop.Tr.app (trOff C D.ds₂ (L.shared.map (·.2.1)) ((chainsOf C D tF tJ t3).rho₂ ρ))
        ((((), v.2.2), (Iop.Rho.snd (s := (chainsOf C D tF tJ t3).s₂)
            ((chainsOf C D tF tJ t3).rhoJ ρ).2).1,
          trOff C D.ds₃ (L.second.map (·.2.1)) ((chainsOf C D tF tJ t3).rho₃ ρ)) :
          Iop.Tr (chainsOf C D tF tJ t3).sh₃)) : Iop.Tr (chainsOf C D tF tJ t3).shJ) :=
  Iop.Tr.snd_app (s := (chainsOf C D tF tJ t3).s₁) _ _

theorem whole_J : (chainsOf C D tF tJ t3).msgJ (trWhole C D tF tJ t3 v L ρ) = ((), v.2.1) := by
  unfold Compile.Joined.Chains.msgJ
  rw [whole_J']

theorem whole_2 : (chainsOf C D tF tJ t3).tr₂ (trWhole C D tF tJ t3 v L ρ) =
    trOff C D.ds₂ (L.shared.map (·.2.1)) ((chainsOf C D tF tJ t3).rho₂ ρ) := by
  unfold Compile.Joined.Chains.tr₂
  rw [whole_J']
  exact Iop.Tr.fst_app _ _

theorem whole_snd : Iop.Tr.snd (s := (chainsOf C D tF tJ t3).s₂)
    ((chainsOf C D tF tJ t3).trJ (trWhole C D tF tJ t3 v L ρ)).2.2 =
    ((((), v.2.2), (Iop.Rho.snd (s := (chainsOf C D tF tJ t3).s₂)
        ((chainsOf C D tF tJ t3).rhoJ ρ).2).1,
      trOff C D.ds₃ (L.second.map (·.2.1)) ((chainsOf C D tF tJ t3).rho₃ ρ)) :
      Iop.Tr (chainsOf C D tF tJ t3).sh₃) := by
  rw [whole_J']
  exact Iop.Tr.snd_app (s := (chainsOf C D tF tJ t3).s₂) (trOff C D.ds₂ (L.shared.map (·.2.1))
      ((chainsOf C D tF tJ t3).rho₂ ρ)) _

theorem whole_3' : (chainsOf C D tF tJ t3).msg3 (trWhole C D tF tJ t3 v L ρ) = ((), v.2.2) := by
  unfold Compile.Joined.Chains.msg3
  rw [whole_snd]

theorem whole_3 : (chainsOf C D tF tJ t3).tr₃ (trWhole C D tF tJ t3 v L ρ) =
    trOff C D.ds₃ (L.second.map (·.2.1)) ((chainsOf C D tF tJ t3).rho₃ ρ) := by
  unfold Compile.Joined.Chains.tr₃
  rw [whole_snd]

end

end ProofFile.Honest

#print axioms ProofFile.Honest.whole_F
#print axioms ProofFile.Honest.whole_1
#print axioms ProofFile.Honest.whole_J'
#print axioms ProofFile.Honest.whole_J
#print axioms ProofFile.Honest.whole_2
#print axioms ProofFile.Honest.whole_snd
#print axioms ProofFile.Honest.whole_3'
#print axioms ProofFile.Honest.whole_3
