-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/SeatOAgrees.lean: a yardstick beside Att/SeatO.lean: the claims' seat, the
key forms, the readers, the four runs and the test on the plan are those of Att/SeatH.lean and
Att/SeatC.lean, as equalities; and how the two hearing's seats part.

`seatCO_eq`: seatCO = seatCH. `keysOfO_eq`, `readersOfO_eq`, `runsO_eq`, `claimsOkAtO_eq`: the like.
So whatever is proved of runsH or claimsOkAt holds of runsO and claimsOkAtO.
`lay_o_of_h`: where Att/SeatH.lean's seat lays (s1), Att/SeatO.lean's lays too (s2), and s1 is s2
with the four rebuilt records laid in: every other field is one.
The converse fails where the rebuilding refuses: Att/SeatO.lean's head says what that means.
By Att/LookOAgrees.lean's lookOfO_eq and padOfO_eq and Look/ShapeOwnAgrees.lean's planesOk_eq.
No running text imports this file.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.SeatO
import Johnson.Desc.First.Att.LookOAgrees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model

theorem seatCO_eq : seatCO = seatCH := by
  funext c
  unfold seatCO seatCH seatCS
  rw [lookOfO_eq, padOfO_eq]
  rfl

theorem keysOfO_eq : keysOfO = keysOfH := by
  funext A s
  unfold keysOfO keysOfH
  rw [seatCO_eq]

theorem readersOfO_eq : readersOfO = readersOfH := by
  funext A s
  unfold readersOfO readersOfH
  rw [seatCO_eq]

theorem runsO_eq : runsO = runsH := by
  funext A
  unfold runsO runsH
  rw [seatCO_eq, keysOfO_eq]

theorem claimsOkAtO_eq : claimsOkAtO = claimsOkAt := by
  funext A
  unfold claimsOkAtO claimsOkAt
  rw [padOfO_eq, Look.planesOk_eq]

/-- Where the seat with the rebuilding lays, the seat without it lays too; the two states part in
the four rebuilt records alone. -/
theorem lay_o_of_h (shape : Attention.Shape) (s s1 : First.S) (h : Heard) (G : Fork)
    (e : (seatSH shape).lay s h G = some s1) :
    ∃ (s2 : First.S) (a2 : First.AttOwn) (o : Own), seatSO.lay s h G = some s2 ∧
      s2.here = .att a2 ∧
      s1 = { s2 with here := .att { a2 with planes := some o.planes, scores := some o.scores,
                                            d := o.d, x := o.x } } := by
  unfold seatSH seatS at e
  unfold seatSO
  simp only at e ⊢
  cases hh : s.here with
  | att a =>
    simp only [hh] at e ⊢
    cases hg : a.g with
    | none => simp [hg] at e
    | some g =>
      simp only [hg, Option.bind_some] at e ⊢
      cases ho : Short.toOwn shape g.zk (toShort h) G with
      | none => simp [ho] at e
      | some o =>
        simp only [ho, Option.map_some, Option.bind_some] at e
        unfold First.S.hear5? First.S.hear5 at e ⊢
        simp only at e ⊢
        by_cases h5 : a.heard5.isSome
        · exfalso
          cases hf : s.failed <;>
            simp [h5, First.S.mark, First.S.unmarked, Except.toOption, hf] at e
        · simp only [h5] at e ⊢
          cases hf : s.failed with
          | some m => simp [First.S.unmarked, hf, Except.toOption] at e
          | none =>
            simp only [First.S.unmarked, hf, Except.toOption, Bool.false_eq_true, if_false,
              Option.some.injEq] at e ⊢
            exact ⟨_, _, o, rfl, rfl, e.symm⟩
  | _ => simp [hh] at e

end VerifiableInference.Desc.First.Att.P
