-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Shares.lean: an executable test on the stated shares: no stated share
has the denominator 0. Executable definitions, and tests; no theorem.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

Why. A stated share is a pair num of den (`Odds`, Honest/Frame.lean). That type's default is 0 of 0,
and the sum of two shares (`Odds.plus`) multiplies the denominators. So 0 of 0 absorbs whatever is
added to it: one part that states it, by a slip or by `default`, makes the sum over all parts
(`statedShares`) 0 of 0, whatever the others state.

  `Odds.ok`, `halvesSharesOk`, `Prover.sharesOk`, `Sides.sharesOk`

Limits.
  * It compares no share with its stop or with its fall's test.
  * Nothing calls it: neither `ready` nor `Owed`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Fall
import Johnson.Desc.ProofFile.Honest.ForKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)

variable {Xi W₀ Rc Ky Tr X₀ X V W Y : Type}

/-- The share's denominator is not 0. -/
def Odds.ok (o : Odds) : Bool := o.den != 0

/-- Both stated shares of every part of every prover's side have a denominator other than 0. -/
def halvesSharesOk (hs : List (Placed V W Y)) : Bool :=
  hs.all fun h => h.parts.all fun p => p.badShare.ok && p.hidShare.ok

/-- **No share that a prover's parts state has the denominator 0.** -/
def Prover.sharesOk (H : Prover W₀ Rc Xi Ky Tr X₀ X) : Bool :=
  halvesSharesOk H.first && halvesSharesOk H.shared && halvesSharesOk H.second

/-- The same for the sides of one description, with the falls' shares. -/
def Sides.sharesOk {F : FileDescription Xi} {Bk : ProverCoinCounts} (G : Sides F Bk W₀ Rc Ky Tr X₀ X)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) : Bool :=
  (G.prover H).sharesOk && G.falls₁.all (·.share.ok) && G.falls₂.all (·.share.ok) &&
    G.falls₃.all (·.share.ok)

-- the trap: the type's default; what it does to a sum, from either side
#guard (default : Odds) == ⟨0, 0⟩ && (⟨0, 0⟩ : Odds).plus ⟨1, 2⟩ == ⟨0, 0⟩ &&
  (⟨1, 2⟩ : Odds).plus ⟨0, 0⟩ == ⟨0, 0⟩
-- the test passes at a part that states 0 of 1 twice, and fails if one of the two is the default
#guard halvesSharesOk [(⟨⟨1, none, 0, .K9⟩, [quietPart]⟩ : Placed Unit Unit Unit)]
#guard !halvesSharesOk
  [(⟨⟨1, none, 0, .K9⟩, [quietPart, { quietPart with hidShare := default }]⟩ :
    Placed Unit Unit Unit)]
#guard !halvesSharesOk
  [(⟨⟨1, none, 0, .K9⟩, [{ quietPart with badShare := ⟨3, 0⟩ }]⟩ : Placed Unit Unit Unit)]

end ProofFile.Honest
