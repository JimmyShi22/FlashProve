-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/StratWords.lean: four definitions in which the lemmas on the
strategies of Honest/Strat.lean are stated. No theorem. The data are the library's structures from
which the space of the verifier's messages is built: an `RDT` for each round, and a `WholeD`, which
gathers the three chains' lists with the depth and the rest.

  `drawsAt`       the verifier's messages of the whole shape, as Honest/Frame.lean's lists of
                  challenges (`Draws`)
  `rowsOfChain`   a chain's declared rounds, each with its declared oracle messages
  `DataFits`      what ties the data of a file's rounds to the description, as far as the views read
                  them
  `trAt`          the transcript that the two strategies produce together

Limits.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.StratPlay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD chainsOf drawnT)
open _root_.Run.PQ (CK)

variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 S Cl : Type}

/-- The verifier's messages of the whole shape, as Honest/Frame.lean's lists of challenges. The
sealing round's empty challenge is appended to the first chain's. -/
def drawsAt (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3)
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) : Draws :=
  ⟨drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ) ++ [⟨[], [], [], none⟩],
    drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ),
    drawnT C D.ds₃ ((chainsOf C D tF tJ t3).rho₃ ρ)⟩

/-- A chain's declared rounds, each with its declared oracle messages. -/
def rowsOfChain (bs : List (Block S Cl)) : List (Fmt.DeclaredRound × List Oracle) :=
  bs.flatMap fun b => b.rounds.zip b.oracles

/-- What ties the data to the description, as far as the views read them. -/
structure DataFits (F : FileDescription Xi) (D : WholeD) : Prop where
  depth : D.a = F.tableDepth
  wants : WantsAre F D
  keys : KeysAre F D
  first : List.Forall₂ RoundFits D.ds₁ (rowsOfChain F.first.blocksInOrder).dropLast
  shared : List.Forall₂ RoundFits D.ds₂ (rowsOfChain F.shared.blocksInOrder)
  second : List.Forall₂ RoundFits D.ds₃ (rowsOfChain F.second.blocksInOrder)

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi) (B : ProverCoinCounts)
  (H : Prover W₀ Rc Xi Ky Tr X₀ X) (J₀ J : KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3) (w : W₀ × Rc × Sd)
  (c₀ : Purse B.shared) (x : Xi) (c : Purse B.first × Purse B.second)

/-- The transcript that the two strategies produce together. `J₀`: the shared part's `KeyAndJoiningRoundMessages`; `J`:
the slot's. -/
def trAt (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh) : Iop.Tr (chainsOf C D tF tJ t3).sh :=
  ((Iop.SStrat.zip (strat0 C D tF tJ t3 F B H J₀ w c₀)
    (requestStrategy C D tF tJ t3 F B H J w c₀ x c)).run ρ).1

end

end ProofFile.Honest
