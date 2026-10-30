-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/StratShape.lean: the whole transcript that a shared part's and a
slot's strategy of the form of Honest/Strat.lean produce together, taken apart into the six parts
that the library's slot reads (Compile/Joined/Types.lean: the front's message, chain 1, the joining
round's message, chain 2, the seam's message, chain 3). No description and no prover is named.

  `sharedOf`, `slotOf`, `sharedEnd`, `sharedJ`, `slotEnd`, `slotJ`   the two strategies' form, by
  what they send and play; that `strat0` and `requestStrategy` have this form is proved in
  Honest/Law/StratForm.lean
  `rhoT_trOf`   the challenges in a chain's transcript are the given ones
  `parts_of_zip`   the six parts

Limits.
  * Nothing is said of `play`, of a view or of a run.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.StratChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes.Maker (RDT WholeD uLT roundT drawnT rhoT chainsOf)
open _root_.Run.PQ (CK)

variable {TF TJ T3 W₁ Y₁ W₂ Y₂ W Y : Type}

theorem rhoT_trOf (C : CK) : ∀ (ds : List RDT) (ss : List (Step W Y)) (m : Option (Mid W Y))
    (ρ : Iop.Rho (uLT C ds)), rhoT C ds (trOf C ds ss m ρ) = ρ
  | [], _, _, () => rfl
  | d :: ds, ss, m, (c, ρ) =>
    congrArg (fun (z : Iop.Rho (uLT C ds)) => ((c, z) : Iop.Rho (uLT C (d :: ds))))
      (rhoT_trOf C ds ss.tail (hearAt ss.head? (tellAt ss.head? m) (drOf C d c) m) ρ)

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3)

/-- What comes after chain 2 in the shared part's strategy. -/
def sharedEnd : Iop.SStrat (chainsOf C D tF tJ t3).sh₃ (chainsOf C D tF tJ t3).ann₃ :=
  ((), fun (_ : Unit) => hushSEnd C D.ds₃)

/-- The shared part's strategy from the joining round on. -/
def sharedJ (jn : TJ) (sh : List (Step W₂ Y₂)) (st₂ : Option (Mid W₂ Y₂)) :
    Iop.SStrat (chainsOf C D tF tJ t3).shJ (chainsOf C D tF tJ t3).annJ :=
  ((((), jn) : Unit × TJ), fun (_ : Unit) => speakS C D.ds₂ sh st₂ (sharedEnd C D tF tJ t3))

/-- **The shared part's strategy, by what it sends**: `jn` in the joining round; `sh`, from `st₂`,
in chain 2. -/
def sharedOf (jn : TJ) (sh : List (Step W₂ Y₂)) (st₂ : Option (Mid W₂ Y₂)) :
    Iop.SStrat (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann :=
  ((), fun (_ : Unit) => hushS C D.ds₁ (sharedJ C D tF tJ t3 jn sh st₂))

/-- The slot's strategy from the seam on. `z`: what the seam sends; chain 3's rounds; the state at
which it starts. -/
def slotEnd (z : T3 × List (Step W₁ Y₁) × Option (Mid W₁ Y₁)) :
    Iop.LStrat (chainsOf C D tF tJ t3).sh₃ (chainsOf C D tF tJ t3).ann₃ :=
  ((((), z.1) : Unit × T3), fun (_ : Unit) => speakLEnd C D.ds₃ z.2.1 z.2.2)

/-- The slot's strategy from the joining round on. -/
def slotJ (K : List Fmt.Drawn → T3 × List (Step W₁ Y₁) × Option (Mid W₁ Y₁)) :
    Iop.LStrat (chainsOf C D tF tJ t3).shJ (chainsOf C D tF tJ t3).annJ :=
  ((), fun (_ : Unit) => hushL C D.ds₂ [] fun ds₂ => slotEnd C D tF tJ t3 (K ds₂))

/-- **A slot's strategy, by what it sends**: `fr` in the front round; `first`, from `st₁`, in chain
1; and `K`, which gives, from the state at which chain 1 ends and from chain 2's challenges, what
the seam sends, chain 3's rounds, and the state at which chain 3 starts. -/
def slotOf (fr : TF) (first : List (Step W₁ Y₁)) (st₁ : Option (Mid W₁ Y₁))
    (K : Option (Mid W₁ Y₁) → List Fmt.Drawn → T3 × List (Step W₁ Y₁) × Option (Mid W₁ Y₁)) :
    Iop.LStrat (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann :=
  ((((), fr) : Unit × TF), fun (_ : Unit) =>
    speakL C D.ds₁ first st₁ fun m₁ => slotJ C D tF tJ t3 (K m₁))

/-- **The six parts of the transcript that the two produce together.** -/
theorem parts_of_zip (jn : TJ) (sh : List (Step W₂ Y₂)) (st₂ : Option (Mid W₂ Y₂)) (fr : TF)
    (first : List (Step W₁ Y₁)) (st₁ : Option (Mid W₁ Y₁))
    (K : Option (Mid W₁ Y₁) → List Fmt.Drawn → T3 × List (Step W₁ Y₁) × Option (Mid W₁ Y₁))
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh)
    (τ : Iop.Tr (chainsOf C D tF tJ t3).sh)
    (hτ : τ = ((Iop.SStrat.zip (sharedOf C D tF tJ t3 jn sh st₂)
      (slotOf C D tF tJ t3 fr first st₁ K)).run ρ).1)
    (z : T3 × List (Step W₁ Y₁) × Option (Mid W₁ Y₁))
    (hz : z = K (endOf C D.ds₁ first st₁ ((chainsOf C D tF tJ t3).rho₁ ρ))
      (drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ))) :
    (chainsOf C D tF tJ t3).msgF τ = ((), fr) ∧
    (chainsOf C D tF tJ t3).tr₁ τ = trOf C D.ds₁ first st₁ ((chainsOf C D tF tJ t3).rho₁ ρ) ∧
    (chainsOf C D tF tJ t3).msgJ τ = ((), jn) ∧
    (chainsOf C D tF tJ t3).tr₂ τ = trOf C D.ds₂ sh st₂ ((chainsOf C D tF tJ t3).rho₂ ρ) ∧
    (chainsOf C D tF tJ t3).msg3 τ = ((), z.1) ∧
    (chainsOf C D tF tJ t3).tr₃ τ = trOf C D.ds₃ z.2.1 z.2.2 ((chainsOf C D tF tJ t3).rho₃ ρ) := by
  subst hτ hz
  have e1 : (((Iop.SStrat.zip (sharedOf C D tF tJ t3 jn sh st₂)
      (slotOf C D tF tJ t3 fr first st₁ K)).run ρ).1).2.2 =
      Iop.Tr.app (trOf C D.ds₁ first st₁ ((chainsOf C D tF tJ t3).rho₁ ρ))
        ((Iop.SStrat.zip (sharedJ C D tF tJ t3 jn sh st₂)
          (slotJ C D tF tJ t3 (K (endOf C D.ds₁ first st₁
            ((chainsOf C D tF tJ t3).rho₁ ρ))))).run ((chainsOf C D tF tJ t3).rhoJ ρ)).1 :=
    zip_speakL C D.ds₁ first st₁ (fun m₁ => slotJ C D tF tJ t3 (K m₁))
      (sharedJ C D tF tJ t3 jn sh st₂) ρ.2
  have eJ : (chainsOf C D tF tJ t3).trJ ((Iop.SStrat.zip (sharedOf C D tF tJ t3 jn sh st₂)
      (slotOf C D tF tJ t3 fr first st₁ K)).run ρ).1 =
      ((Iop.SStrat.zip (sharedJ C D tF tJ t3 jn sh st₂)
        (slotJ C D tF tJ t3 (K (endOf C D.ds₁ first st₁
          ((chainsOf C D tF tJ t3).rho₁ ρ))))).run ((chainsOf C D tF tJ t3).rhoJ ρ)).1 := by
    unfold Compile.Joined.Chains.trJ
    rw [e1, Iop.Tr.snd_app]
  have e2 : (((Iop.SStrat.zip (sharedJ C D tF tJ t3 jn sh st₂)
        (slotJ C D tF tJ t3 (K (endOf C D.ds₁ first st₁
          ((chainsOf C D tF tJ t3).rho₁ ρ))))).run ((chainsOf C D tF tJ t3).rhoJ ρ)).1).2.2 =
      Iop.Tr.app (trOf C D.ds₂ sh st₂ ((chainsOf C D tF tJ t3).rho₂ ρ))
        ((Iop.SStrat.zip (sharedEnd C D tF tJ t3)
          (slotEnd C D tF tJ t3 (K (endOf C D.ds₁ first st₁ ((chainsOf C D tF tJ t3).rho₁ ρ))
            ([] ++ drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ))))).run
          (Iop.Rho.snd (s := uLT C D.ds₂) ((chainsOf C D tF tJ t3).rhoJ ρ).2)).1 :=
    zip_speakS C D.ds₂ sh st₂ (sharedEnd C D tF tJ t3) []
      (fun ds₂ => slotEnd C D tF tJ t3 (K (endOf C D.ds₁ first st₁
        ((chainsOf C D tF tJ t3).rho₁ ρ)) ds₂)) ((chainsOf C D tF tJ t3).rhoJ ρ).2
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Compile.Joined.Chains.tr₁
    rw [e1, Iop.Tr.fst_app]
  · unfold Compile.Joined.Chains.msgJ
    rw [eJ]
    rfl
  · unfold Compile.Joined.Chains.tr₂
    rw [eJ, e2, Iop.Tr.fst_app]
  · unfold Compile.Joined.Chains.msg3
    rw [eJ, e2, Iop.Tr.snd_app]
    rfl
  · unfold Compile.Joined.Chains.tr₃
    rw [eJ, e2, Iop.Tr.snd_app]
    exact zip_speakLEnd C D.ds₃ _ _ _

end

end ProofFile.Honest

#print axioms ProofFile.Honest.rhoT_trOf
#print axioms ProofFile.Honest.parts_of_zip
