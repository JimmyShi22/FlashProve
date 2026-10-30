-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/StratChainC.lean: a chain's transcript as a speaker of
Honest/StratC.lean writes it, and the state of the chain's walk after it. It is the counterpart of
Honest/Law/StratChain.lean, which has the same for the speakers of Honest/Strat.lean. The lemmas are
general in the chain's data, its rounds and the walk.

  1  `trOfC`, `endOfC`   the transcript; the `Step`s that are left and the walk at the end
  2  `zip_speakLC`, `zip_speakSC`, `zip_speakLEndC`   a speaker, while the other strategy is silent
  3  `rhoT_trOfC`   the transcript's challenges are the verifier's message
  4  `sharedOfC`, `slotOfC`, `sharedJC`, `slotEndC`, `slotJC`, `parts_of_zipC`   the two strategies'
     form, and the six parts of the transcript that they produce together (as in
     Honest/Law/StratShape.lean); that `sharedPartStrategyTrackingVerifier` and `requestStrategyTrackingVerifier` have this form is proved in
     Honest/Law/StratFormC.lean

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.StratC
import Johnson.Desc.ProofFile.Honest.Law.StratShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD uLT roundT drawnT rhoT chainsOf)
open _root_.Run.PQ (CK)

variable {S Cl W Y : Type}

/-! ## 1 A chain's transcript -/

/-- A chain's transcript as a speaker of Honest/StratC.lean writes it. -/
def trOfC (C : CK) (L : Lay) : (ds : List RDT) → List (Step W Y) → ChainProgress S Cl W Y →
    Iop.Rho (uLT C ds) → Iop.Tr (uLT C ds)
  | [], _, _, _ => ()
  | d :: ds, ss, z, (c, ρ) =>
    (msgOf C d (tellC z ss.head?), c, trOfC C L ds ss.tail (progressAfterChallenge L z ss.head? (drOf C d c)) ρ)

/-- The `Step`s that are left, and the state of the walk then. -/
def endOfC (C : CK) (L : Lay) : (ds : List RDT) → List (Step W Y) → ChainProgress S Cl W Y →
    Iop.Rho (uLT C ds) → List (Step W Y) × ChainProgress S Cl W Y
  | [], ss, z, _ => (ss, z)
  | d :: ds, ss, z, (c, ρ) => endOfC C L ds ss.tail (progressAfterChallenge L z ss.head? (drOf C d c)) ρ

/-! ## 2 A speaker, while the other strategy is silent -/

section
variable (C : CK) (L : Lay) {rest : Iop.Shape} {A : Iop.RoundSplits rest}

theorem zip_speakLC : ∀ (ds : List RDT) (ss : List (Step W Y)) (z : ChainProgress S Cl W Y)
    (k : List (Step W Y) → ChainProgress S Cl W Y → Iop.LStrat rest A) (k₀ : Iop.SStrat rest A)
    (ρ : Iop.Rho (uLT C ds ++ rest)),
    ((Iop.SStrat.zip (hushS C ds k₀) (requestStrategyOverSeparateChain C L ds ss z k)).run ρ).1 =
      Iop.Tr.app (trOfC C L ds ss z (Iop.Rho.fst ρ))
        ((Iop.SStrat.zip k₀ (k (endOfC C L ds ss z (Iop.Rho.fst ρ)).1
          (endOfC C L ds ss z (Iop.Rho.fst ρ)).2)).run (Iop.Rho.snd (s := uLT C ds) ρ)).1
  | [], _, _, _, _, _ => rfl
  | d :: ds, ss, z, k, k₀, (c, ρ) =>
    congrArg (fun (τ : Iop.Tr (uLT C ds ++ rest)) =>
        ((msgOf C d (tellC z ss.head?), c, τ) : Iop.Tr (uLT C (d :: ds) ++ rest)))
      (zip_speakLC ds ss.tail (progressAfterChallenge L z ss.head? (drOf C d c)) k k₀ ρ)

theorem zip_speakSC : ∀ (ds : List RDT) (ss : List (Step W Y)) (z : ChainProgress S Cl W Y)
    (k₀ : Iop.SStrat rest A) (acc : List Fmt.Drawn) (k : List Fmt.Drawn → Iop.LStrat rest A)
    (ρ : Iop.Rho (uLT C ds ++ rest)),
    ((Iop.SStrat.zip (sharedStrategyOverSharedChain C L ds ss z k₀) (hushL C ds acc k)).run ρ).1 =
      Iop.Tr.app (trOfC C L ds ss z (Iop.Rho.fst ρ))
        ((Iop.SStrat.zip k₀ (k (acc ++ drawnT C ds (Iop.Rho.fst ρ)))).run
          (Iop.Rho.snd (s := uLT C ds) ρ)).1
  | [], _, _, k₀, acc, k, ρ => by
    show ((Iop.SStrat.zip k₀ (k acc)).run ρ).1 = ((Iop.SStrat.zip k₀ (k (acc ++ []))).run ρ).1
    rw [List.append_nil]
  | d :: ds, ss, z, k₀, acc, k, (c, ρ) => by
    have ih := zip_speakSC ds ss.tail (progressAfterChallenge L z ss.head? (drOf C d c)) k₀
      (acc ++ [drOf C d c]) k ρ
    rw [List.append_assoc] at ih
    exact congrArg (fun (τ : Iop.Tr (uLT C ds ++ rest)) =>
      ((msgOf C d (tellC z ss.head?), c, τ) : Iop.Tr (uLT C (d :: ds) ++ rest))) ih

end

theorem zip_speakLEndC (C : CK) (L : Lay) : ∀ (ds : List RDT) (ss : List (Step W Y))
    (z : ChainProgress S Cl W Y) (ρ : Iop.Rho (uLT C ds)),
    ((Iop.SStrat.zip (hushSEnd C ds) (speakLEndC C L ds ss z)).run ρ).1 = trOfC C L ds ss z ρ
  | [], _, _, _ => rfl
  | d :: ds, ss, z, (c, ρ) =>
    congrArg (fun (τ : Iop.Tr (uLT C ds)) =>
        ((msgOf C d (tellC z ss.head?), c, τ) : Iop.Tr (uLT C (d :: ds))))
      (zip_speakLEndC C L ds ss.tail (progressAfterChallenge L z ss.head? (drOf C d c)) ρ)

/-! ## 3 The challenges -/

theorem rhoT_trOfC (C : CK) (L : Lay) : ∀ (ds : List RDT) (ss : List (Step W Y))
    (z : ChainProgress S Cl W Y) (ρ : Iop.Rho (uLT C ds)), rhoT C ds (trOfC C L ds ss z ρ) = ρ
  | [], _, _, () => rfl
  | d :: ds, ss, z, (c, ρ) =>
    congrArg (fun (y : Iop.Rho (uLT C ds)) => ((c, y) : Iop.Rho (uLT C (d :: ds))))
      (rhoT_trOfC C L ds ss.tail (progressAfterChallenge L z ss.head? (drOf C d c)) ρ)

/-! ## 4 The two strategies' form, and the six parts -/

section
variable {TF TJ T3 S₁ S₂ S₃ W₁ Y₁ W₂ Y₂ : Type}
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3)

/-- The shared part's strategy from the joining round on. -/
def sharedJC (jn : TJ) (L₂ : Lay) (sh : List (Step W₂ Y₂)) (z₂ : ChainProgress S₂ Cl W₂ Y₂) :
    Iop.SStrat (chainsOf C D tF tJ t3).shJ (chainsOf C D tF tJ t3).annJ :=
  ((((), jn) : Unit × TJ), fun (_ : Unit) => sharedStrategyOverSharedChain C L₂ D.ds₂ sh z₂ (sharedEnd C D tF tJ t3))

/-- The shared part's strategy, by what it sends and plays. -/
def sharedOfC (jn : TJ) (L₂ : Lay) (sh : List (Step W₂ Y₂)) (z₂ : ChainProgress S₂ Cl W₂ Y₂) :
    Iop.SStrat (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann :=
  ((), fun (_ : Unit) => hushS C D.ds₁ (sharedJC C D tF tJ t3 jn L₂ sh z₂))

/-- A slot's strategy from the seam on. -/
def slotEndC (z : T3 × Lay × List (Step W₁ Y₁) × ChainProgress S₃ Cl W₁ Y₁) :
    Iop.LStrat (chainsOf C D tF tJ t3).sh₃ (chainsOf C D tF tJ t3).ann₃ :=
  ((((), z.1) : Unit × T3), fun (_ : Unit) => speakLEndC C z.2.1 D.ds₃ z.2.2.1 z.2.2.2)

/-- From the joining round on. -/
def slotJC (K : List Fmt.Drawn → T3 × Lay × List (Step W₁ Y₁) × ChainProgress S₃ Cl W₁ Y₁) :
    Iop.LStrat (chainsOf C D tF tJ t3).shJ (chainsOf C D tF tJ t3).annJ :=
  ((), fun (_ : Unit) => hushL C D.ds₂ [] fun ds₂ => slotEndC C D tF tJ t3 (K ds₂))

/-- A slot's strategy, by what it sends and plays. -/
def slotOfC (fr : TF) (L₁ : Lay) (first : List (Step W₁ Y₁)) (z₁ : ChainProgress S₁ Cl W₁ Y₁)
    (K : List (Step W₁ Y₁) → ChainProgress S₁ Cl W₁ Y₁ → List Fmt.Drawn →
      T3 × Lay × List (Step W₁ Y₁) × ChainProgress S₃ Cl W₁ Y₁) :
    Iop.LStrat (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann :=
  ((((), fr) : Unit × TF), fun (_ : Unit) =>
    requestStrategyOverSeparateChain C L₁ D.ds₁ first z₁ fun left y₁ => slotJC C D tF tJ t3 (K left y₁))

/-- **The six parts of the transcript that two strategies of that form produce together.** -/
theorem parts_of_zipC (jn : TJ) (L₂ : Lay) (sh : List (Step W₂ Y₂)) (z₂ : ChainProgress S₂ Cl W₂ Y₂)
    (fr : TF) (L₁ : Lay) (first : List (Step W₁ Y₁)) (z₁ : ChainProgress S₁ Cl W₁ Y₁)
    (K : List (Step W₁ Y₁) → ChainProgress S₁ Cl W₁ Y₁ → List Fmt.Drawn →
      T3 × Lay × List (Step W₁ Y₁) × ChainProgress S₃ Cl W₁ Y₁)
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) (τ : Iop.Tr (chainsOf C D tF tJ t3).sh)
    (hτ : τ = ((Iop.SStrat.zip (sharedOfC C D tF tJ t3 jn L₂ sh z₂)
      (slotOfC C D tF tJ t3 fr L₁ first z₁ K)).run ρ).1)
    (z : T3 × Lay × List (Step W₁ Y₁) × ChainProgress S₃ Cl W₁ Y₁)
    (hz : z = K (endOfC C L₁ D.ds₁ first z₁ ((chainsOf C D tF tJ t3).rho₁ ρ)).1
      (endOfC C L₁ D.ds₁ first z₁ ((chainsOf C D tF tJ t3).rho₁ ρ)).2
      (drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ))) :
    (chainsOf C D tF tJ t3).msgF τ = ((), fr) ∧
    (chainsOf C D tF tJ t3).tr₁ τ =
      trOfC C L₁ D.ds₁ first z₁ ((chainsOf C D tF tJ t3).rho₁ ρ) ∧
    (chainsOf C D tF tJ t3).msgJ τ = ((), jn) ∧
    (chainsOf C D tF tJ t3).tr₂ τ = trOfC C L₂ D.ds₂ sh z₂ ((chainsOf C D tF tJ t3).rho₂ ρ) ∧
    (chainsOf C D tF tJ t3).msg3 τ = ((), z.1) ∧
    (chainsOf C D tF tJ t3).tr₃ τ =
      trOfC C z.2.1 D.ds₃ z.2.2.1 z.2.2.2 ((chainsOf C D tF tJ t3).rho₃ ρ) := by
  subst hτ hz
  have e1 : (((Iop.SStrat.zip (sharedOfC C D tF tJ t3 jn L₂ sh z₂)
      (slotOfC C D tF tJ t3 fr L₁ first z₁ K)).run ρ).1).2.2 =
      Iop.Tr.app (trOfC C L₁ D.ds₁ first z₁ ((chainsOf C D tF tJ t3).rho₁ ρ))
        ((Iop.SStrat.zip (sharedJC C D tF tJ t3 jn L₂ sh z₂)
          (slotJC C D tF tJ t3 (K (endOfC C L₁ D.ds₁ first z₁
            ((chainsOf C D tF tJ t3).rho₁ ρ)).1 (endOfC C L₁ D.ds₁ first z₁
            ((chainsOf C D tF tJ t3).rho₁ ρ)).2))).run ((chainsOf C D tF tJ t3).rhoJ ρ)).1 :=
    zip_speakLC C L₁ D.ds₁ first z₁ (fun left y₁ => slotJC C D tF tJ t3 (K left y₁))
      (sharedJC C D tF tJ t3 jn L₂ sh z₂) ρ.2
  have eJ : (chainsOf C D tF tJ t3).trJ ((Iop.SStrat.zip (sharedOfC C D tF tJ t3 jn L₂ sh z₂)
      (slotOfC C D tF tJ t3 fr L₁ first z₁ K)).run ρ).1 =
      ((Iop.SStrat.zip (sharedJC C D tF tJ t3 jn L₂ sh z₂)
        (slotJC C D tF tJ t3 (K (endOfC C L₁ D.ds₁ first z₁
          ((chainsOf C D tF tJ t3).rho₁ ρ)).1 (endOfC C L₁ D.ds₁ first z₁
          ((chainsOf C D tF tJ t3).rho₁ ρ)).2))).run ((chainsOf C D tF tJ t3).rhoJ ρ)).1 := by
    unfold Compile.Joined.Chains.trJ
    rw [e1, Iop.Tr.snd_app]
  have e2 : (((Iop.SStrat.zip (sharedJC C D tF tJ t3 jn L₂ sh z₂)
        (slotJC C D tF tJ t3 (K (endOfC C L₁ D.ds₁ first z₁
          ((chainsOf C D tF tJ t3).rho₁ ρ)).1 (endOfC C L₁ D.ds₁ first z₁
          ((chainsOf C D tF tJ t3).rho₁ ρ)).2))).run ((chainsOf C D tF tJ t3).rhoJ ρ)).1).2.2 =
      Iop.Tr.app (trOfC C L₂ D.ds₂ sh z₂ ((chainsOf C D tF tJ t3).rho₂ ρ))
        ((Iop.SStrat.zip (sharedEnd C D tF tJ t3)
          (slotEndC C D tF tJ t3 (K (endOfC C L₁ D.ds₁ first z₁
            ((chainsOf C D tF tJ t3).rho₁ ρ)).1 (endOfC C L₁ D.ds₁ first z₁
            ((chainsOf C D tF tJ t3).rho₁ ρ)).2
            ([] ++ drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ))))).run
          (Iop.Rho.snd (s := uLT C D.ds₂) ((chainsOf C D tF tJ t3).rhoJ ρ).2)).1 :=
    zip_speakSC C L₂ D.ds₂ sh z₂ (sharedEnd C D tF tJ t3) []
      (fun ds₂ => slotEndC C D tF tJ t3 (K (endOfC C L₁ D.ds₁ first z₁
        ((chainsOf C D tF tJ t3).rho₁ ρ)).1 (endOfC C L₁ D.ds₁ first z₁
        ((chainsOf C D tF tJ t3).rho₁ ρ)).2 ds₂)) ((chainsOf C D tF tJ t3).rhoJ ρ).2
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
    exact zip_speakLEndC C _ D.ds₃ _ _ _

end

end ProofFile.Honest

#print axioms ProofFile.Honest.zip_speakLC
#print axioms ProofFile.Honest.zip_speakSC
#print axioms ProofFile.Honest.zip_speakLEndC
#print axioms ProofFile.Honest.rhoT_trOfC
#print axioms ProofFile.Honest.parts_of_zipC
