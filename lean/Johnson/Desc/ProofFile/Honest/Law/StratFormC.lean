-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/StratFormC.lean: the two strategies of Honest/StratC.lean in the
form of Honest/Law/StratChainC.lean, by unfolding alone. It is the counterpart of
Honest/Law/StratForm.lean, which has the same for the strategies of Honest/Strat.lean.

  `seamAtC`       what the slot's strategy does from the seam on, from the `Step`s that the first
                  chain has left, the walk at the first chain's end and the shared chain's
                  challenges: the definition that `requestStrategyTrackingVerifier` itself has
  `sharedPartStrategyTrackingVerifier_form`, `requestStrategyTrackingVerifier_form`   the two equations
  `zip_partsC`    the three rounds without a challenge, and the three chains' form, of the
                  transcript that the two produce together, at every verifier's message: the three
                  rounds without a challenge show the `KeyAndJoiningRoundMessages`'s values, at every private input, coin
                  and instance

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.StratChainC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)
open OnBytes.Maker (RDT WholeD uLT chainsOf drawnT)
open _root_.Run.PQ (CK)

variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 : Type}

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi) (B : ProverCoinCounts)
  (H : Prover W₀ Rc Xi Ky Tr X₀ X) (J₀ J : KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3) (sh : Ky → F.S₂)
  (w : W₀ × Rc × Sd) (c₀ : Purse B.shared) (x : Xi) (c : Purse B.first × Purse B.second)

/-- What the slot's strategy does from the seam on: the definition that `requestStrategyTrackingVerifier` itself has. The
last chain's walk is started with the columns of the first and of the shared chain's walks
(`z₁.cols ++ z₂.cols`), as there. -/
def seamAtC (left : List (Step (Local W₀ Rc Xi Tr) X))
    (y₁ : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) X) (ds₂ : List Fmt.Drawn) :
    T3 × Lay × List (Step (Local W₀ Rc Xi Tr) X) × ChainProgress F.S₃ F.Cl (Local W₀ Rc Xi Tr) X :=
  let stored := H.storedWords w.1 w.2.1
  let R := (ready F B H w.1 w.2.1 x ⟨c.1, c₀, c.2⟩).toOption
  let a := sharedChainStart F B H sh w.1 w.2.1 (J.keyOf w.1 w.2.1 w.2.2) c₀
  let y := advanceOverRounds ⟨0, 0, stored, treeOwn⟩ left [⟨[], [], [], none⟩] y₁
  let z₁ := if sealQuiet y.laid then y else y.halt
  let z₂ := advanceOverRounds ⟨1, 0, stored, treeOwn⟩ a.1 ds₂ a.2
  let L₃ : Lay := ⟨2, F.lastChainFirstTreeNumber, stored, treeThird z₁.laid z₂.laid⟩
  (J.seam w.1 w.2.1 w.2.2 x, L₃, (R.map (·.second)).getD [],
    chainStartOrHalted L₃ F.second.blocksInOrder
      (R.bind fun R => z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ H m₁ m₂)
      (door₃ F x z₁.ver z₂.ver) (z₁.cols ++ z₂.cols))

theorem sharedPartStrategyTrackingVerifier_form : sharedPartStrategyTrackingVerifier C D tF tJ t3 F B H J₀ sh w c₀ =
    sharedOfC C D tF tJ t3 (J₀.join w.1 w.2.1 w.2.2) ⟨1, 0, H.storedWords w.1 w.2.1, treeOwn⟩
      (sharedChainStart F B H sh w.1 w.2.1 (J₀.keyOf w.1 w.2.1 w.2.2) c₀).1
      (sharedChainStart F B H sh w.1 w.2.1 (J₀.keyOf w.1 w.2.1 w.2.2) c₀).2 := rfl

theorem requestStrategyTrackingVerifier_form : requestStrategyTrackingVerifier C D tF tJ t3 F B H J sh w c₀ x c =
    slotOfC C D tF tJ t3 (J.front w.1 w.2.1 w.2.2 x) ⟨0, 0, H.storedWords w.1 w.2.1, treeOwn⟩
      (((ready F B H w.1 w.2.1 x ⟨c.1, c₀, c.2⟩).toOption.map (·.first)).getD [])
      (chainStartOrHalted ⟨0, 0, H.storedWords w.1 w.2.1, treeOwn⟩ F.first.blocksInOrder
        ((ready F B H w.1 w.2.1 x ⟨c.1, c₀, c.2⟩).toOption.map fun R => R.start₁ H)
        (some (F.start₁ (F.pub x))) [])
      (seamAtC F B H J sh w c₀ x c) := rfl

/-- **The six parts of the two strategies' transcript, at every verifier's message.** Of the three
chains it says the form alone: each is `trOfC` at some `Lay`, `Step`s and walk, which it does not
name (`parts_of_zipC` with `sharedPartStrategyTrackingVerifier_form` and `requestStrategyTrackingVerifier_form` names them). -/
theorem zip_partsC (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) :
    (chainsOf C D tF tJ t3).msgF ((Iop.SStrat.zip (sharedPartStrategyTrackingVerifier C D tF tJ t3 F B H J₀ sh w c₀)
      (requestStrategyTrackingVerifier C D tF tJ t3 F B H J sh w c₀ x c)).run ρ).1 = ((), J.front w.1 w.2.1 w.2.2 x) ∧
    (∃ L ss z, (chainsOf C D tF tJ t3).tr₁ ((Iop.SStrat.zip
      (sharedPartStrategyTrackingVerifier C D tF tJ t3 F B H J₀ sh w c₀)
      (requestStrategyTrackingVerifier C D tF tJ t3 F B H J sh w c₀ x c)).run ρ).1 =
        trOfC (S := F.S₁) (Cl := F.Cl) (W := Local W₀ Rc Xi Tr) (Y := X) C L D.ds₁ ss z
          ((chainsOf C D tF tJ t3).rho₁ ρ)) ∧
    (chainsOf C D tF tJ t3).msgJ ((Iop.SStrat.zip (sharedPartStrategyTrackingVerifier C D tF tJ t3 F B H J₀ sh w c₀)
      (requestStrategyTrackingVerifier C D tF tJ t3 F B H J sh w c₀ x c)).run ρ).1 = ((), J₀.join w.1 w.2.1 w.2.2) ∧
    (∃ L ss z, (chainsOf C D tF tJ t3).tr₂ ((Iop.SStrat.zip
      (sharedPartStrategyTrackingVerifier C D tF tJ t3 F B H J₀ sh w c₀)
      (requestStrategyTrackingVerifier C D tF tJ t3 F B H J sh w c₀ x c)).run ρ).1 =
        trOfC (S := F.S₂) (Cl := F.Cl) (W := Common W₀ Rc Ky) (Y := X₀) C L D.ds₂ ss z
          ((chainsOf C D tF tJ t3).rho₂ ρ)) ∧
    (chainsOf C D tF tJ t3).msg3 ((Iop.SStrat.zip (sharedPartStrategyTrackingVerifier C D tF tJ t3 F B H J₀ sh w c₀)
      (requestStrategyTrackingVerifier C D tF tJ t3 F B H J sh w c₀ x c)).run ρ).1 = ((), J.seam w.1 w.2.1 w.2.2 x) ∧
    ∃ L ss z, (chainsOf C D tF tJ t3).tr₃ ((Iop.SStrat.zip
      (sharedPartStrategyTrackingVerifier C D tF tJ t3 F B H J₀ sh w c₀)
      (requestStrategyTrackingVerifier C D tF tJ t3 F B H J sh w c₀ x c)).run ρ).1 =
        trOfC (S := F.S₃) (Cl := F.Cl) (W := Local W₀ Rc Xi Tr) (Y := X) C L D.ds₃ ss z
          ((chainsOf C D tF tJ t3).rho₃ ρ) := by
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := parts_of_zipC C D tF tJ t3 _ _ _ _ _ _ _ _ _ ρ
    ((Iop.SStrat.zip (sharedPartStrategyTrackingVerifier C D tF tJ t3 F B H J₀ sh w c₀)
      (requestStrategyTrackingVerifier C D tF tJ t3 F B H J sh w c₀ x c)).run ρ).1
    (by rw [sharedPartStrategyTrackingVerifier_form, requestStrategyTrackingVerifier_form]) _ rfl
  exact ⟨m1, ⟨_, _, _, m2⟩, m3, ⟨_, _, _, m4⟩, m5, ⟨_, _, _, m6⟩⟩

end

end ProofFile.Honest

#print axioms ProofFile.Honest.sharedPartStrategyTrackingVerifier_form
#print axioms ProofFile.Honest.requestStrategyTrackingVerifier_form
#print axioms ProofFile.Honest.zip_partsC
#print axioms ProofFile.Honest.seamAtC
