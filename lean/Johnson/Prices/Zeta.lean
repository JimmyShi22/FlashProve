-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prices/Zeta.lean: every plan of a shared chain pays, at its round LIN zeta, for the count of
the points at which a multilinear form that is not zero vanishes.

The seventh round of a shared chain (place 6) is LIN zeta: the verifier draws kRow elements of the
extension field, kRow being the number of bits that index the rows of the matrix. The count to be
paid is kRow |E| ^ (kRow - 1) of the |E| ^ kRow points. `ZetaPaysOf plan` says of a function in the
place of `sharedPlan` that every plan that it returns has the setting that it was given and pays
that count at that place (`PaysAt`, Johnson/Prices/Pays.lean). `zeta_pays`: `sharedPlan` does, at
every setting and all sizes: nothing is evaluated. `zeta_number`: at the format's field, the target
128 and no work the count is within the target for every kRow up to 2 ^ 63, an inequality between
natural numbers; `zeta_number_base`: over the base field alone it is not, at kRow = 22.

Main definitions: `zetaSpec`, `ZetaPaysOf`, `cardGl`.
Main theorems: `linSizeOf_rowsLog`, `zeta_pays`, `not_zetaPaysOf_empty`, `zeta_number`,
`zeta_number_base`.
What is not claimed: that `sharedPlan` returns a plan at any values. That the count bounds a
prover's chance. What the head of Johnson/Prices/Pays.lean does not claim.

-/
import Johnson.Prices.Pays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params.Prices

/-- The description of the round LIN zeta with k drawn elements. -/
def zetaSpec (s : Setting) (k : ℕ) : RoundSpec :=
  .said "LIN zeta" .field (fieldError s k) { drawE := k, priced := .roundItself } 0 0 0

/-- The sizes that the plans read have the shape's number of row bits. -/
theorem linSizeOf_rowsLog {codes : Codes} {x : LinSized} {L : LinSize}
    (h : linSizeOf codes x = some L) : L.rowsLog = x.shape.kRow := by
  unfold linSizeOf at h
  extract_lets at h
  obtain ⟨_, _, h⟩ := opt_bind h
  obtain ⟨_, _, h⟩ := opt_bind h
  obtain ⟨_, _, h⟩ := opt_bind h
  obtain ⟨_, _, h⟩ := opt_bind h
  obtain ⟨_, _, h⟩ := opt_bind h
  cases h
  rfl

/-- Of a function in the place of `sharedPlan`: every plan that it returns has the setting that it
was given, and pays at the place 6, under the name LIN zeta, for kRow |E| ^ (kRow - 1) of the |E| ^
kRow points. -/
def ZetaPaysOf (plan : Setting → Codes → LinSized → Except String Planned) : Prop :=
  ∀ (s : Setting) (codes : Codes) (x : LinSized) (P : Planned), plan s codes x = .ok P →
    P.set = s ∧
      PaysAt P 6 "LIN zeta" x.shape.kRow (x.shape.kRow * s.cardE ^ (x.shape.kRow - 1))

/-- **Every plan of a shared chain pays at LIN zeta.** -/
theorem zeta_pays : ZetaPaysOf sharedPlan := by
  intro s codes x P h
  obtain ⟨L, hL, -, hP⟩ := sharedPlan_is h
  generalize hc : (if x.lines.oneTime = true then Scope.once else Scope.shared) = c at hP
  have hcr : (c == Scope.request) = false := by
    rw [← hc]
    split <;> rfl
  have hk := linSizeOf_rowsLog hL
  have hat : (linSharedTests s c x L ++ [sealRound])[6]? = some (zetaSpec s L.rowsLog) := by
    simp [linSharedTests, linSharedList, zetaSpec]
  have hmem : zetaSpec s L.rowsLog ∈ linSharedTests s c x L ++ [sealRound] :=
    List.mem_of_getElem? hat
  have hb : (zetaSpec s L.rowsLog).bound s c = fieldError s L.rowsLog := by
    simp [zetaSpec, RoundSpec.bound, hcr]
  have hg := hP.good _ hmem
  have hh := hP.holds _ hmem
  have hg1 : (fieldError s L.rowsLog).bad = false := by
    rw [← hb]
    exact hg.1
  have he : ((zetaSpec s L.rowsLog).round s c).error = (fieldError s L.rowsLog).error := by
    rw [← hb]
    rfl
  have hcov := covers_field he hg1 (le_refl (L.rowsLog * s.cardE ^ (L.rowsLog - 1)))
  refine ⟨hP.set, (zetaSpec s L.rowsLog).round s c, ?_, rfl, ⟨hk, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · rw [hP.rounds, List.getElem?_map, hat]
    rfl
  · rw [hP.set]
    exact hg.2.1
  · rw [hP.set, ← hk]
    exact hcov
  · rw [hP.set, ← hk]
    exact within_of_covers hh hcov

/-- A function that returns a plan without rounds does not meet the law. -/
theorem not_zetaPaysOf_empty (codes : Codes) (x : LinSized) :
    ¬ ZetaPaysOf fun s _ _ => .ok ⟨s, []⟩ :=
  fun h => not_paysAt_nil _ _ _ _ _ (h {} codes x _ rfl).2

/-- The number of elements of the format's extension field. -/
def cardGl : ℕ := (2 ^ 64 - 2 ^ 32 + 1) ^ 3

/-- The default setting has the format's field. -/
theorem cardE_default : ({} : Setting).cardE = cardGl := rfl

/-- **At the format's field, the target 128 and no work, the count of LIN zeta is within the target
for every number of row bits up to 2 ^ 63.** -/
theorem zeta_number (k : ℕ) (hk : k ≤ 2 ^ 63) :
    Within 128 0 (k * cardGl ^ (k - 1)) (cardGl ^ k) := by
  unfold Within
  cases k with
  | zero => simp
  | succ j =>
    rw [Nat.add_sub_cancel, pow_succ]
    have h1 : (j + 1) * 2 ^ 128 ≤ cardGl :=
      le_trans (Nat.mul_le_mul_right _ hk) (by unfold cardGl; norm_num)
    calc (j + 1) * cardGl ^ j * 2 ^ 128 = cardGl ^ j * ((j + 1) * 2 ^ 128) := by ring
      _ ≤ cardGl ^ j * cardGl := Nat.mul_le_mul_left _ h1
      _ = 2 ^ 0 * (cardGl ^ j * cardGl) := by simp

/-- Over the base field alone the same count, at 22 row bits, is not within the target. -/
theorem zeta_number_base :
    ¬ Within 128 0 (22 * (2 ^ 64 - 2 ^ 32 + 1) ^ (22 - 1)) ((2 ^ 64 - 2 ^ 32 + 1) ^ 22) := by
  unfold Within
  norm_num

end OnBytes.Params.Prices
