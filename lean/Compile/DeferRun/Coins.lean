-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/DeferRun/Coins.lean: a fresh token of an erased token program as one of the coins that
another program is handed at its start. Two lemmas, general in the family of oracles.

General lemmas. This file states no goal of the release.

`erase` (Compile/Star.lean) turns "a fresh token of ℓ bits" into one draw of a number below 2^ℓ, of
which the bits are read. Rom/Handle/Coins.lean has the calculus that compares a program which is
handed all its coins first with one that draws each coin where it is used. Here its step is said for
that form of a draw.

  coinsFirst_bits          the step (CoinsFirst.draw) at a draw of ℓ bits in erase's form.
  coinsFirst_erase_fresh   the same, with the erased program written out.
In both the list of the members of the type of ℓ bits is a letter (ft): in two files Lean may find
two such lists, which are equal but costly to compare.

-/
import Compile.Step1_life2_Erase
import Rom.Handle.Coins

set_option autoImplicit false

noncomputable section

namespace Compile
namespace DeferRun
open Rom Prob

variable {S : OSpec} {sp : Split S} {U α : Type} {μ : PMF U}

/-- The step at a draw of ℓ bits: if one coordinate of the coins is ℓ uniform bits, independent of
the rest, go on with the program in which the drawn bits are laid into the coins. -/
theorem coinsFirst_bits (ℓ : ℕ) {ft : Fintype (Fin ℓ → Bool)} {upd : (Fin ℓ → Bool) → U → U}
    {prog : U → OComp S α} (hμ : Resamples μ (@unif (Fin ℓ → Bool) ft _) upd)
    {k' : (Fin ℓ → Bool) → OComp S α}
    (hk : ∀ x, CoinsFirst μ (fun u => prog (upd x u)) (k' x)) :
    CoinsFirst μ prog (.sample (2 ^ ℓ - 1) fun r => k' fun i => r.val.testBit i) :=
  CoinsFirst.draw (Life2.bitsE ℓ) (@map_unif_equiv _ _ _ _ ft _ (Life2.bitsE ℓ)) hμ hk

/-- The same at the erasure of "a fresh token of ℓ bits, then k". -/
theorem coinsFirst_erase_fresh (ℓ : ℕ) (k : Tok → Step S sp α) (vs : List Bits)
    {ft : Fintype (Fin ℓ → Bool)} {upd : (Fin ℓ → Bool) → U → U}
    {prog : U → OComp S (α × List Bits)} (hμ : Resamples μ (@unif (Fin ℓ → Bool) ft _) upd)
    (hk : ∀ x, CoinsFirst μ (fun u => prog (upd x u))
      (erase (k vs.length) (vs ++ [List.ofFn x]))) :
    CoinsFirst μ prog (erase (.fresh ℓ k) vs) :=
  coinsFirst_bits ℓ hμ (k' := fun x => erase (k vs.length) (vs ++ [List.ofFn x])) hk

end DeferRun
end Compile

#print axioms Compile.DeferRun.coinsFirst_bits
#print axioms Compile.DeferRun.coinsFirst_erase_fresh
