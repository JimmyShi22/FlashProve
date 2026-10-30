-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/Sim/Through.lean: K14's ONE EQUATION: THE SIX ROWS READ THROUGH ARE THE SIX ROWS. Since a lift read through
is a lift (`Part.lift_thru`, Honest/Thru.lean), the kind's halves read through a total `g` on the index and `rd` on the tables' randomness
are its halves at the readers composed: so the rows, which are general in these two readers, stand at the term as they are: no law on a
side read through is needed at this kind.

  `liftK14_thru`, `liftSend_thru`   the two lifts
  `halves_through`, `sendHalves_through`, `simRows_through`   **the equation**, at the halves
  `now_through`    under the head: what `nowSharedBy` returns, read through, is the six rows' halves at the readers composed
  `six_in_through`  **at a filling whose shared field begins with what `nowSharedBy` returns, `OnlineProverParts.through`'s shared field begins with these halves**

Limits. That the term's filling has that form is the filling's text (`sharedWithUO`). `d'` is free. These are
equations of definitions: no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K14.Sim.AtFilling
import Johnson.Desc.ProofFile.Honest.ThruK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Chain)

variable {W₀ W₀' Rc Rc' Ky X Pb : Type}

/-- K14's lift read through. -/
theorem liftK14_thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : Data) (weights : W₀ → Weights)
    (p : Part Empty Ask Unit) :
    (liftK14 d weights p : Part Empty (Common W₀ Rc Ky) X).thru id (Common.thru g rd) =
      liftK14 d (weights ∘ g) p :=
  Part.lift_thru _ _ _ _ _ _ _

/-- The sendings' lift read through. -/
theorem liftSend_thru {W W' : Type} (wit' : W' → W) (wit : W → Ask) (p : Part Empty Ask Unit) :
    (liftSend wit p : Part Empty W X).thru id wit' = liftSend (wit ∘ wit') p :=
  Part.lift_thru _ _ _ _ _ _ _

/-- **The kind's own halves read through.** -/
theorem halves_through (g : W₀' → W₀) (rd : Rc' → Rc) (d : Data) (weights : W₀ → Weights) :
    ((proverSidesOfSharedRounds d weights : List (Placed Empty (Common W₀ Rc Ky) X)).map
        (Placed.thru id (Common.thru g rd))) =
      proverSidesOfSharedRounds d (weights ∘ g) := by
  rw [halves_eq, halves_eq]
  by_cases hS : d.S.sharedSplitNeeded = true
  · simp only [if_pos hS, List.cons_append, List.nil_append, List.map_cons, List.map_nil, Placed.thru,
      liftK14_thru]
  · simp only [if_neg hS, List.append_nil, List.map_cons, List.map_nil, Placed.thru, liftK14_thru]

/-- **The sendings' halves read through.** -/
theorem sendHalves_through (g : W₀' → W₀) (rd : Rc' → Rc) (A : SendPub) (weights : W₀ → Weights)
    (rand : Rc → TableRand) :
    ((proverSidesOfSharedSendings A weights rand : List (Placed Empty (Common W₀ Rc Ky) X)).map
        (Placed.thru id (Common.thru g rd))) =
      proverSidesOfSharedSendings A (weights ∘ g) (rand ∘ rd) := by
  rw [sendHalves_eq, sendHalves_eq]
  simp only [List.map_cons, List.map_nil, Placed.thru, liftSend_thru]
  rfl

/-- **K14's one equation: the six rows' halves read through are the six rows' halves at the readers composed.** -/
theorem simRows_through (g : W₀' → W₀) (rd : Rc' → Rc) (d : Data) (A : SendPub) (weights : W₀ → Weights)
    (rand : Rc → TableRand) :
    (((simRows d A weights rand : List (Unlettered Empty (Common W₀ Rc Ky) X Pb)).map (·.half)).map
        (Placed.thru id (Common.thru g rd))) =
      ((simRows d A (weights ∘ g) (rand ∘ rd) :
        List (Unlettered Empty (Common W₀' Rc' Ky) X Pb)).map (·.half)) := by
  rw [simRows_half, simRows_half, List.map_append, halves_through, sendHalves_through]

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place} {o : ProofFile.SecondHashFunctionArgument}

/-- **Under the head: at a filling whose shared field begins with what `nowSharedBy` returns, the shared field read through begins with the six
rows' halves at the readers composed.** -/
theorem six_in_through (h : P5J.AtMgA o Z D r₀ Zp Np cF x₀) (weights : W₀ → Weights)
    {Tr X₁ : Type} (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d' : W₀')
    (P : OnlineProverParts W₀ IndexCommitterCoins Tr Unit X₁) (G : Ground)
    (six rest : List (Placed Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit))
    (hsix : nowSharedBy weights Zp = .ok six) (hP : P.shared Zp G = six ++ rest) :
    (OnlineProverParts.through g rd d' P).shared Zp G =
      ((simRows (simData Zp Np) (simPub Zp Np) (weights ∘ g) (randNow (qAt Zp Np) ∘ rd) :
        List (Unlettered Empty (Common W₀' Rc' OnBytes.TableKey) Unit Pb)).map (·.half)) ++
        rest.map (Placed.thru id (Common.thru g rd)) := by
  have e : six = ((simRows (simData Zp Np) (simPub Zp Np) weights (randNow (qAt Zp Np)) :
      List (Unlettered Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit Pb)).map (·.half)) :=
    Except.ok.inj (hsix.symm.trans (simRows_now h weights))
  show (P.shared Zp G).map (Placed.thru id (Common.thru g rd)) = _
  rw [hP, List.map_append, e, simRows_through]

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.liftK14_thru
#print axioms ProofFile.Honest.K14.liftSend_thru
#print axioms ProofFile.Honest.K14.halves_through
#print axioms ProofFile.Honest.K14.sendHalves_through
#print axioms ProofFile.Honest.K14.simRows_through
#print axioms ProofFile.Honest.K14.six_in_through
