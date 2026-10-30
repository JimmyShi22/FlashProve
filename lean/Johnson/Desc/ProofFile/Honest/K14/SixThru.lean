-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/SixThru.lean: the linear claim's shared rounds (kind K14): THE
KIND's SIX PROVER's SIDES ARE NATURAL IN THEIR TWO READERS. A side reads the prover's input through
two functions: `weights` reads the matrix off the index, `rand` reads the committed table's pads and
tails off the committer's randomness. Reading the whole input through a pair of maps g, rd
(Placed.thru at Common.thru g rd, Honest/Thru.lean) gives the same side at the readers composed with
g and rd.

Why. A filling of the prover's sides can be read through such a pair of maps (OnlineProverParts.through,
Honest/ThruK13.lean). By these equations what then lies at this kind's places is this kind's own
sides again, at the composed readers. AtFullSide/K14/SixAtBase.lean spends them so (thru_shared).

  placed_lift_thru   a side with one lifted part, read through, is that side with the part lifted at
                     the readers composed
  halves_thru        **the kind's own sides**
  sendHalves_thru    **the two sendings' sides**
  sixOf_thru         **the maker of the six**: it returns at the composed readers just where it
                     returns at the readers, and then the list read through

What is not claimed. Nothing on what a side plays. Nothing on completeness, soundness or hiding.
Terms. A side is the prover's list of parts at one place (Placed, Honest/Frame.lean).
-/
import Johnson.Desc.ProofFile.Honest.Thru
import Johnson.Desc.ProofFile.Honest.K14.Six

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Place Block)

/-- A side with one lifted part, read through. -/
theorem placed_lift_thru {V V' V'' W W' W'' X Y : Type} (see' : V'' → V') (wit' : W'' → W')
    (see : V' → V) (wit : W' → W) (get : X → Y) (set : X → Y → X) (pl : Place) (p : Part V W Y) :
    Placed.thru see' wit' ⟨pl, [p.lift see wit get set]⟩ =
      ⟨pl, [p.lift (see ∘ see') (wit ∘ wit') get set]⟩ :=
  congrArg (fun q => (⟨pl, [q]⟩ : Placed V'' W'' X)) (Part.lift_thru see' wit' see wit get set p)

variable {W₀ W₀' Rc Rc' Ky X S Cl : Type}

/-- **The kind's own sides, read through, are the kind's own sides at the reader composed with g.**
They read nothing of the committer's randomness. -/
theorem halves_thru (g : W₀' → W₀) (rd : Rc' → Rc) (P : Data) (weights : W₀ → Weights) :
    (proverSidesOfSharedRounds P weights : List (Placed Empty (Common W₀ Rc Ky) X)).map
        (Placed.thru id (Common.thru g rd)) =
      proverSidesOfSharedRounds P (weights ∘ g) := by
  unfold proverSidesOfSharedRounds
  by_cases h : P.S.sharedSplitNeeded = true
  · simp only [if_pos h, List.map_append, List.map_cons, List.map_nil, placed_lift_thru]
    rfl
  · simp only [if_neg h, List.map_append, List.map_cons, List.map_nil, placed_lift_thru]
    rfl

/-- **The two sendings' sides, read through, are the two sendings' sides at the readers composed
with g and rd.** -/
theorem sendHalves_thru (g : W₀' → W₀) (rd : Rc' → Rc) (A : SendPub) (weights : W₀ → Weights)
    (rand : Rc → TableRand) :
    (proverSidesOfSharedSendings A weights rand : List (Placed Empty (Common W₀ Rc Ky) X)).map
        (Placed.thru id (Common.thru g rd)) =
      proverSidesOfSharedSendings A (weights ∘ g) (rand ∘ rd) := by
  unfold proverSidesOfSharedSendings
  simp only [List.map_cons, List.map_nil, placed_lift_thru]
  rfl

/-- **The maker of the six at the composed readers**: its three public tests and its search for the
two places "LIN point" and "LIN zeta" read neither reader, so it returns or rejects alike, with the
same message; where it returns, its list is the list read through. -/
theorem sixOf_thru (g : W₀' → W₀) (rd : Rc' → Rc) (P : Desc.K14.P14) (bs : List (Block S Cl))
    (weights : W₀ → Weights) (rand : Rc → TableRand) :
    (sixOf P bs (weights ∘ g) (rand ∘ rd) :
        Except String (List (Placed Empty (Common W₀' Rc' Ky) X))) =
      (sixOf P bs weights rand).map (List.map (Placed.thru id (Common.thru g rd))) := by
  unfold sixOf
  cases rejection P bs with
  | some e => rfl
  | none =>
    cases dataOf P.S bs with
    | none => rfl
    | some d =>
      show Except.ok _ = Except.ok _
      rw [List.map_append, halves_thru, sendHalves_thru]

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.placed_lift_thru
#print axioms ProofFile.Honest.K14.halves_thru
#print axioms ProofFile.Honest.K14.sendHalves_thru
#print axioms ProofFile.Honest.K14.sixOf_thru
