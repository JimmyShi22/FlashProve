-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PricesSharedQ.lean: "EACH BLOCK's ERRORS ARE THE PLAN's PRICES", as a proposition on a row
of pieces. Definitions. NOTHING IS PROVED IN THIS FILE. `EachPricedW`: at the plan's WHOLE errors, `wholePricesOf`;
the two names are taken over from the work on the row `fold_slots`.

  `errOf cnt s πs`: a list of errors over the rounds s, made of a list of (price, bits of work): round by
    round `cnt r π work`: THE LETTER cnt: how many of the written round r's challenges a price stands for.
  `Piece.Priced cnt p πs`: the piece's field `err` IS that list, and there are as many prices as rounds.
  `EachPriced cnt bs P k l`: every piece of a row has it, at the plan's prices of its block's rounds
    (Johnson/Desc/Shared/PricesShared.lean: `pricesOf`, `worksOf`), block number k first. AT THE BARE ERRORS: NOT WHAT A LAW "AT THE
    PLAN's PRICES" IS MEANT AT.
  `EachPricedW cnt bs P k l`: THE SAME AT `wholePricesOf`: with the draws' distance from uniform: the number that the planner's verdict compares: THE ONE
    THAT IS MEANT.

What it is for. The row of laws owed "the shared chain's blocks pay for N slots AT THE PLAN's PRICES" is
then: `roundsArePlans bs P = true` (a test, run) · `EachPricedW cnt bs P 0 (p :: l)` (by the pieces' make) ·
`EachPaysN N onQ₂ relQ₂ …` (the laws).

Limits. cnt IS A LETTER: at cnt := "all of the round's challenges" every law holds and says nothing. It is
owed by the row on the reading of a written round (price, work, the draws' distance from uniform).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Shared.PricesShared
import Johnson.Desc.Sound.ChainRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj OnBytes.Params
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Err Shape Round)
open VerifiableInference.Desc.Shared

/-- Errors over the rounds s, made of prices with their bits of work. Where the list is too short: 0. -/
def errOf (cnt : Round → Binary → ℕ → ℕ) : (s : Shape) → List (Binary × ℕ) → Err s
  | [], _ => ()
  | r :: s, [] => (0, errOf cnt s [])
  | r :: s, π :: πs => (cnt r π.1 π.2, errOf cnt s πs)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- The piece's errors are these prices, as counts. -/
def Piece.Priced (cnt : Round → Binary → ℕ → ℕ) (p : Piece C F S Cl W) (πs : List (Binary × ℕ)) :
    Prop :=
  πs.length = (uLT C p.ds).length ∧ p.err = errOf cnt (uLT C p.ds) πs

/-- **Every piece's errors are the plan's prices of its block's rounds.** bs: the chain's blocks; k: the
number of the first piece's block. -/
def EachPriced {S₀ : Type} (cnt : Round → Binary → ℕ → ℕ) (bs : List (Block S₀ Cl)) (P : Planned) :
    ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | k, p :: l =>
    p.Priced cnt ((pricesOf bs P k).zip (worksOf bs P k)) ∧ EachPriced cnt bs P (k + 1) l

/-- **Every piece's errors are the plan's WHOLE prices of its block's rounds**: with the draws' distance from uniform. -/
def EachPricedW {S₀ : Type} (cnt : Round → Binary → ℕ → ℕ) (bs : List (Block S₀ Cl)) (P : Planned) :
    ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | k, p :: l =>
    p.Priced cnt ((wholePricesOf bs P k).zip (worksOf bs P k)) ∧ EachPricedW cnt bs P (k + 1) l

end VerifiableInference.Desc.Sound
