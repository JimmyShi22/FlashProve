-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/MeetsStratLawC.lean: the two strategies of Honest/StratC.lean,
zipped, satisfy `StratLaw` (Johnson/Prover/Print/StratLaw.lean), which is a condition on a
strategy's own run at every verifier's message. Whatever the description, the book, the prover, the
shared chain's first state, the private input, the coins and the instance: the joining round's run
value and the seam's plain part are fixed; and the words of the field elements in every written
round's plain part, and of every symbol of every oracle, read or not, are below the prime; of an
item that is a word or a root `StratLaw` asks nothing. There is no hypothesis. It is the counterpart
of Honest/Law/MeetsStratLaw.lean, which has the same for the strategies of Honest/Strat.lean, and it
uses two of that file's lemmas.

  `meets_stratLawC`   the main lemma

It uses `trOfC_vals_lt`, `trOfC_cols_lt` (Honest/Law/StratCanonC.lean), `zip_partsC`
(Honest/Law/StratFormC.lean), `okF_of_lt` and `wordsP_of_rv` (Honest/Law/MeetsStratLaw.lean).

Limits.
  * The joining round's run value is that of the shared strategy's `KeyAndJoiningRoundMessages` (the parameter J₀); the
    seam's plain part is that of the slot's (J).
  * Nothing is said on acceptance.
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.MeetsStratLaw
import Johnson.Desc.ProofFile.Honest.Law.StratCanonC
import Johnson.Desc.ProofFile.Honest.Law.StratFormC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription fieldPrimeWord)
open OnBytes.Maker (RDT WholeD uLT rvT chainsOf FrontMsg)
open Johnson.Prover.Print (StratLaw)
open Compile.Joined (JoinMsg)
open _root_.Run.PQ (CK PlainOf)

variable {Xi W₀ Rc Ky Tr X₀ X Sd : Type}

section
variable (C : CK) (D : WholeD) (tF : FrontMsg (List OnBytes.E))
  (tJ : JoinMsg (List OnBytes.E) ByteArray) (t3 : ByteArray) (F : FileDescription Xi) (B : ProverCoinCounts)
  (H : Prover W₀ Rc Xi Ky Tr X₀ X)
  (J₀ J : KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky (FrontMsg (List OnBytes.E)) (JoinMsg (List OnBytes.E) ByteArray)
    ByteArray)
  (sh : Ky → F.S₂) (w : W₀ × Rc × Sd) (c₀ : Purse B.shared) (x : Xi)
  (c : Purse B.first × Purse B.second)

/-- **The two strategies, zipped, satisfy `StratLaw`**: at every description, book, prover, first
state of the shared chain, private input, coins and instance. -/
theorem meets_stratLawC :
    StratLaw C D tF tJ t3
      (Iop.SStrat.zip (sharedPartStrategyTrackingVerifier C D tF tJ t3 F B H J₀ sh w c₀)
        (requestStrategyTrackingVerifier C D tF tJ t3 F B H J sh w c₀ x c))
      (J₀.join w.1 w.2.1 w.2.2).run (J.seam w.1 w.2.1 w.2.2 x) := by
  have key := zip_partsC C D tF tJ t3 F B H J₀ J sh w c₀ x c
  refine ⟨fun ρ => ?_, fun ρ => ?_, fun ρ => ?_, fun ρ => ?_, fun ρ => ?_, fun ρ q => ?_,
    fun ρ q => ?_, fun ρ q => ?_⟩
  · rw [(key ρ).2.2.1]
  · rw [(key ρ).2.2.2.2.1]
  · obtain ⟨L, ss, z, e⟩ := (key ρ).2.1
    rw [e]
    exact wordsP_of_rv C _ _ (trOfC_vals_lt C L _ ss z _)
  · obtain ⟨L, ss, z, e⟩ := (key ρ).2.2.2.1
    rw [e]
    exact wordsP_of_rv C _ _ (trOfC_vals_lt C L _ ss z _)
  · obtain ⟨L, ss, z, e⟩ := (key ρ).2.2.2.2.2
    rw [e]
    exact wordsP_of_rv C _ _ (trOfC_vals_lt C L _ ss z _)
  · obtain ⟨L, ss, z, e⟩ := (key ρ).2.1
    rw [e]
    exact fun a ha => okF_of_lt (trOfC_cols_lt C L _ ss z _ q a ha)
  · obtain ⟨L, ss, z, e⟩ := (key ρ).2.2.2.1
    rw [e]
    exact fun a ha => okF_of_lt (trOfC_cols_lt C L _ ss z _ q a ha)
  · obtain ⟨L, ss, z, e⟩ := (key ρ).2.2.2.2.2
    rw [e]
    exact fun a ha => okF_of_lt (trOfC_cols_lt C L _ ss z _ q a ha)

end

end ProofFile.Honest

#print axioms ProofFile.Honest.meets_stratLawC
