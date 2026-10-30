-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/StratForm.lean: the two strategies of Honest/Strat.lean in the
form of Honest/Law/StratShape.lean, by unfolding alone.

  `seamAt`        what the slot's strategy does from the seam on, from the state at which the first
                  chain ends and from the shared chain's challenges: the definition that `requestStrategy`
                  itself has
  `sharedPartStrategy_form`, `requestStrategy_form`   the two equations
  `zip_parts`     of the transcript that the two produce together, at every verifier's message: the
                  front round's, the joining round's and the seam's messages; and of each chain,
                  that its transcript is `trOf` at some `Step`s and some state

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.StratShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)
open OnBytes.Maker (RDT WholeD uLT chainsOf drawnT)
open _root_.Run.PQ (CK)

variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 : Type}

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi) (B : ProverCoinCounts)
  (H : Prover W₀ Rc Xi Ky Tr X₀ X) (J₀ J : KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3) (w : W₀ × Rc × Sd)
  (c₀ : Purse B.shared) (x : Xi) (c : Purse B.first × Purse B.second)

/-- What the slot's strategy does from the seam on, from the state at which the first chain ends and
from the shared chain's challenges: the definition that `requestStrategy` itself has. -/
def seamAt (m₁ : Option (Mid (Local W₀ Rc Xi Tr) X)) (ds₂ : List Fmt.Drawn) :
    T3 × List (Step (Local W₀ Rc Xi Tr) X) × Option (Mid (Local W₀ Rc Xi Tr) X) :=
  let ky := J.keyOf w.1 w.2.1 w.2.2
  let R := (ready F B H w.1 w.2.1 x ⟨c.1, c₀, c.2⟩).toOption
  let ss := (readyShared F B H w.1 w.2.1 ky c₀).toOption
  let first := (R.map (·.first)).getD []
  let e₁ := m₁.bind fun m =>
    (((play (first.drop D.ds₁.length) [⟨[], [], [], none⟩] [] m).bind sealTest).toOption.map
      (·.2))
  let e₂ := ss.bind fun l =>
    ((play l ds₂ [] (startShared H ⟨w.1, w.2.1, ky⟩)).toOption.map (·.2))
  let m₃ := R.bind fun R => e₁.bind fun a => e₂.map fun b => R.start₃ H a b
  (J.seam w.1 w.2.1 w.2.2 x, (R.map (·.second)).getD [], m₃)

theorem sharedPartStrategy_form : strat0 C D tF tJ t3 F B H J₀ w c₀ =
    sharedOf C D tF tJ t3 (J₀.join w.1 w.2.1 w.2.2)
      ((readyShared F B H w.1 w.2.1 (J₀.keyOf w.1 w.2.1 w.2.2) c₀).toOption.getD [])
      ((readyShared F B H w.1 w.2.1 (J₀.keyOf w.1 w.2.1 w.2.2) c₀).toOption.map fun _ =>
        startShared H ⟨w.1, w.2.1, J₀.keyOf w.1 w.2.1 w.2.2⟩) := rfl

theorem requestStrategy_form : requestStrategy C D tF tJ t3 F B H J w c₀ x c =
    slotOf C D tF tJ t3 (J.front w.1 w.2.1 w.2.2 x)
      (((ready F B H w.1 w.2.1 x ⟨c.1, c₀, c.2⟩).toOption.map (·.first)).getD [])
      ((ready F B H w.1 w.2.1 x ⟨c.1, c₀, c.2⟩).toOption.map fun R => R.start₁ H)
      (seamAt D F B H J w c₀ x c) := rfl

/-- **The three rounds without a challenge, and the form of the three chains' transcripts, at every
verifier's message.** Of each chain it says that there are `Step`s and a state at which `trOf` gives
its transcript, not which: `parts_of_zip` with `sharedPartStrategy_form` and `requestStrategy_form` says which. -/
theorem zip_parts (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) :
    (chainsOf C D tF tJ t3).msgF ((Iop.SStrat.zip (strat0 C D tF tJ t3 F B H J₀ w c₀)
      (requestStrategy C D tF tJ t3 F B H J w c₀ x c)).run ρ).1 = ((), J.front w.1 w.2.1 w.2.2 x) ∧
    (∃ ss m, (chainsOf C D tF tJ t3).tr₁ ((Iop.SStrat.zip (strat0 C D tF tJ t3 F B H J₀ w c₀)
      (requestStrategy C D tF tJ t3 F B H J w c₀ x c)).run ρ).1 =
        trOf (W := Local W₀ Rc Xi Tr) (Y := X) C D.ds₁ ss m ((chainsOf C D tF tJ t3).rho₁ ρ)) ∧
    (chainsOf C D tF tJ t3).msgJ ((Iop.SStrat.zip (strat0 C D tF tJ t3 F B H J₀ w c₀)
      (requestStrategy C D tF tJ t3 F B H J w c₀ x c)).run ρ).1 = ((), J₀.join w.1 w.2.1 w.2.2) ∧
    (∃ ss m, (chainsOf C D tF tJ t3).tr₂ ((Iop.SStrat.zip (strat0 C D tF tJ t3 F B H J₀ w c₀)
      (requestStrategy C D tF tJ t3 F B H J w c₀ x c)).run ρ).1 =
        trOf (W := Common W₀ Rc Ky) (Y := X₀) C D.ds₂ ss m ((chainsOf C D tF tJ t3).rho₂ ρ)) ∧
    (chainsOf C D tF tJ t3).msg3 ((Iop.SStrat.zip (strat0 C D tF tJ t3 F B H J₀ w c₀)
      (requestStrategy C D tF tJ t3 F B H J w c₀ x c)).run ρ).1 = ((), J.seam w.1 w.2.1 w.2.2 x) ∧
    ∃ ss m, (chainsOf C D tF tJ t3).tr₃ ((Iop.SStrat.zip (strat0 C D tF tJ t3 F B H J₀ w c₀)
      (requestStrategy C D tF tJ t3 F B H J w c₀ x c)).run ρ).1 =
        trOf (W := Local W₀ Rc Xi Tr) (Y := X) C D.ds₃ ss m ((chainsOf C D tF tJ t3).rho₃ ρ) := by
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := parts_of_zip C D tF tJ t3 _ _ _ _ _ _ _ ρ
    ((Iop.SStrat.zip (strat0 C D tF tJ t3 F B H J₀ w c₀)
      (requestStrategy C D tF tJ t3 F B H J w c₀ x c)).run ρ).1
    (by rw [sharedPartStrategy_form, requestStrategy_form]) _ rfl
  exact ⟨m1, ⟨_, _, m2⟩, m3, ⟨_, _, m4⟩, m5, ⟨_, _, m6⟩⟩

end

end ProofFile.Honest

#print axioms ProofFile.Honest.sharedPartStrategy_form
#print axioms ProofFile.Honest.requestStrategy_form
#print axioms ProofFile.Honest.zip_parts
