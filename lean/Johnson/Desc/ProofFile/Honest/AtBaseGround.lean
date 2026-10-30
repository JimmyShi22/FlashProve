-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtBaseGround.lean: the segments' records without a request in the
library's `PureBase` (`PureBase.G₀`, Johnson/Desc/ProofFile/OnlineDescriptionFromBlockTables.lean) and in what `onlineProverFromPublicFiles` returns
(`OnlineProverWithDescription.G`, Honest/AtPure.lean) are the same value. Lemmas with their proofs; no definition.

  `base_ground`   where `baseOf Z (pureSeat o Z)` returns Bs: `blankBy pureRoad.links Z` returns
     `Bs.G₀`
  `base_ground_atPure`   so `Bs.G₀ = A.G`, where `onlineProverFromPublicFiles` returns A and `A.Z` is that Z
  `base_of_atPure`   where `onlineProverFromPublicFiles` returns A, `baseOf A.Z (pureSeat o A.Z)` returns, and its `G₀`
     is `A.G`

Why they are the same. `baseOf` and `onlineProverFromPublicFiles` both call `blankBy` (Johnson/Desc/ProofFile/Pub.lean)
at the public part; `baseOf` at the field `links` of its `PureSeat`, which in `pureSeat`
(Johnson/Desc/ProofFile/OnlineDescription.lean) is `pureRoad.links`; `onlineProverFromPublicFiles` at `pureRoad.links`.

What it is for. Some lemmas on the honest side name the ground as `Bs.G₀`, others as `A.G`.

Related lemmas. `atPure_ok` (Honest/AtPureLaw.lean): what each field of A is. `descPure_parts`,
`orSay_ok` (Johnson/Desc/ProofFile/Law/PureMade.lean), which are called here.

Limits.
  * That `baseOf` returns, or that `onlineProverFromPublicFiles` returns, is a hypothesis of each lemma.
  * In `base_of_atPure` the function that stands for the format's second hash function is the same in
    `onlineProverFromPublicFiles` and in `pureSeat`. In `base_ground_atPure` the two may differ.
  * Nothing is said of the other fields of `PureBase`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.Desc.ProofFile.Law.PureMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

variable {W₀ Rc Tr X₀ X : Type}

/-- Where `baseOf` returns at `pureSeat`, its `G₀` is what `blankBy pureRoad.links` returns. -/
theorem base_ground {o : SecondHashFunctionArgument} {Z : Pub} {Bs : PureBase}
    (hB : baseOf Z (pureSeat o Z) = .ok Bs) : blankBy pureRoad.links Z = some Bs.G₀ := by
  unfold baseOf at hB
  obtain ⟨ps, -, hB⟩ := bind_ok hB
  obtain ⟨sh, -, hB⟩ := bind_ok hB
  obtain ⟨G, hG, hB⟩ := bind_ok hB
  have e := Except.ok.inj hB
  rw [← e]
  exact ProofFile.Law.orSay_ok hG

/-- **The two grounds are one value.** o, o': what stands for the format's second hash function in
`pureSeat` and in `onlineProverFromPublicFiles`. -/
theorem base_ground_atPure {o o' : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} {Zp : Pub} {Bs : PureBase}
    (hB : baseOf Zp (pureSeat o Zp) = .ok Bs) (hA : onlineProverFromPublicFiles o' pol lay KL P = .ok A)
    (hZ : A.Z = Zp) : Bs.G₀ = A.G := by
  have h1 := base_ground hB
  have h2 := (atPure_ok hA).2.1
  rw [hZ, h1] at h2
  exact Option.some.inj h2

/-- **Where `onlineProverFromPublicFiles` returns, `baseOf` returns at its public part, with its ground.** -/
theorem base_of_atPure {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {P : OnlineProverParts W₀ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) :
    ∃ Bs, baseOf A.Z (pureSeat o A.Z) = .ok Bs ∧ Bs.G₀ = A.G := by
  obtain ⟨hZ, -, hF, -⟩ := atPure_ok hA
  obtain ⟨Z, B, _, _, _, _, hZ', hB, -⟩ := ProofFile.Law.descPure_parts hF
  have e : Z = A.Z := by
    have h3 : pubPlain o pol lay KL = .ok Z := hZ'
    rw [hZ] at h3
    exact (Except.ok.inj h3).symm
  subst e
  exact ⟨B, hB, base_ground_atPure hB hA rfl⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.base_ground
#print axioms ProofFile.Honest.base_ground_atPure
#print axioms ProofFile.Honest.base_of_atPure
