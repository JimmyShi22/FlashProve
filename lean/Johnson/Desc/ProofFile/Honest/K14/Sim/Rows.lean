-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/Sim/Rows.lean: K14's SIMULATORS IN THE FRAME's SLOT: the kind's six rows as one list, each
part beside its simulator. A definition and statements on it. Nothing here says that a simulator tells what its part shows:
that is Honest/K14/Sim/Good.lean.

  `simRows`       the six rows: the own four (`ownRows`, Honest/K14/Rows14.lean) and the two sendings' (`sendingRows`,
                  Honest/K14/ExactRows.lean)
  `simRows_half`, `simRows_six`   their halves are the halves that `sixOf` lays
  `SimBlind`, `simRows_blind`   no simulator of the six reads the public part of the input (in the shared chain: the key)
                  or what stands in front of it (`Before`, with the stored tables' columns). By equation, at every argument

Limits. Three places of the kind have no round and no row here. No property of the protocol is
claimed: nothing on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.Rows14
import Johnson.Desc.ProofFile.Honest.K14.ExactRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block)

variable {W₀ Rc Ky X Pb S Cl : Type}

/-- **The kind's six rows**: in `sixOf`'s order, the own rows first and the two sendings behind them. -/
def simRows (d : Data) (A : SendPub) (weights : W₀ → Weights) (rand : Rc → TableRand) :
    List (Unlettered Empty (Common W₀ Rc Ky) X Pb) :=
  ownRows d weights ++ sendingRows A weights rand

/-- The two sendings' rows have the sendings' halves. -/
theorem sendingRows_half (A : SendPub) (weights : W₀ → Weights) (rand : Rc → TableRand) :
    ((sendingRows A weights rand : List (Unlettered Empty (Common W₀ Rc Ky) X Pb)).map (·.half)) =
      proverSidesOfSharedSendings A weights rand := by
  rw [sendHalves_eq]
  rfl

/-- **The six rows' halves are the kind's halves.** -/
theorem simRows_half (d : Data) (A : SendPub) (weights : W₀ → Weights) (rand : Rc → TableRand) :
    ((simRows d A weights rand : List (Unlettered Empty (Common W₀ Rc Ky) X Pb)).map (·.half)) =
      proverSidesOfSharedRounds d weights ++ proverSidesOfSharedSendings A weights rand := by
  unfold simRows
  rw [List.map_append, ownRows_half, sendingRows_half]

/-- **Where `k14Rows` returns, `sixOf` returns the six rows' halves**, at the numbers that `dataOf` makes. -/
theorem simRows_six (P : Desc.K14.P14) (bs : List (Block S Cl)) (weights : W₀ → Weights)
    (rand : Rc → TableRand) (rs : List (Unlettered Empty (Common W₀ Rc Ky) X Pb))
    (h : k14Rows P bs weights = .ok rs) :
    ∃ d, dataOf P.S bs = some d ∧ rs = ownRows d weights ∧
      sixOf P bs weights rand =
        .ok ((simRows d ⟨P, d.atPoint⟩ weights rand :
          List (Unlettered Empty (Common W₀ Rc Ky) X Pb)).map (·.half)) := by
  obtain ⟨d, hd, hr, h6⟩ := k14Rows_six P bs weights rand rs h
  refine ⟨d, hd, hr, ?_⟩
  rw [h6, simRows_half, hr, ownRows_half]

/-- A simulator reads neither the public part of the input nor what stands in front of it. -/
def SimBlind (s : Sim Pb) : Prop :=
  ∀ (p p' : Pb) (f f' : Before) (ds : List Fmt.Drawn) (asks : List (List (List Nat))) (c : Cs s.takes),
    s.tell p f ds asks c = s.tell p' f' ds asks c

/-- **No simulator of the six reads the key or what stands in front of it.** -/
theorem simRows_blind (d : Data) (A : SendPub) (weights : W₀ → Weights) (rand : Rc → TableRand) :
    ∀ r ∈ (simRows d A weights rand : List (Unlettered Empty (Common W₀ Rc Ky) X Pb)),
      ∀ x ∈ r.row, SimBlind x.2 := by
  intro r hr x hx
  rcases List.mem_append.1 hr with h | h
  · unfold ownRows at h
    rcases List.mem_append.1 h with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;>
        · obtain rfl := List.mem_singleton.1 hx
          exact fun _ _ _ _ _ _ _ => rfl
    · split at h
      · obtain rfl := List.mem_singleton.1 h
        obtain rfl := List.mem_singleton.1 hx
        exact fun _ _ _ _ _ _ _ => rfl
      · cases h
  · unfold sendingRows at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;>
      · obtain rfl := List.mem_singleton.1 hx
        exact fun _ _ _ _ _ _ _ => rfl

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.sendingRows_half
#print axioms ProofFile.Honest.K14.simRows_half
#print axioms ProofFile.Honest.K14.simRows_six
#print axioms ProofFile.Honest.K14.simRows_blind
