-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/PlacedDot.lean: that the two messages of (Dot) have their tables, from the
public shape's conditions and the messages' shapes in the statement; and what (Dot) means where it
lies among constraints that hold of words.

Main names: SeatedDot (the statement has the codes; the two messages are two and have the shapes
that the public shape names for omega_col and for W), SeatedDot.grows, placedDot_of_seated, dotSays.

What is not claimed. That SeatedDot holds at a chain's state, and that (Dot) lies among a group's
constraints there, is shown where that chain is written. In dotSays the row weights are structured
vectors without a written-out factor: a premise, which the program's own pending rows do not meet:
the general form is dotSaysOk (Johnson/Desc/K14/Law/MeansDotOk.lean). Nothing on soundness.

-/
import Johnson.Desc.K14.Law.MeansDot
import Johnson.Desc.K14.Law.Placed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows)

variable {K : Type} [Field K] (ρ : Reading K)

/-- The statement has the codes; the two messages of (Dot) are two and have the shapes that the
public shape names. -/
structure SeatedDot (T : Statement) (codes : Codes) (S : LinShape) (omega w : Nat) : Prop where
  sameCodes : T.codes = codes
  two : omega ≠ w
  omega : ∃ x, T.oracles[omega]? = some x ∧ x.shape = S.omega
  w : ∃ x, T.oracles[w]? = some x ∧ x.shape = S.w

/-- A statement that grows keeps it. -/
theorem SeatedDot.grows {T T' : Statement} {codes : Codes} {S : LinShape} {omega w : Nat}
    (h : SeatedDot T codes S omega w) (g : Grows T T') : SeatedDot T' codes S omega w := by
  obtain ⟨x, hx, sx⟩ := h.omega
  obtain ⟨y, hy, sy⟩ := h.w
  obtain ⟨x', hx', gx⟩ := g.2.2 _ x hx
  obtain ⟨y', hy', gy⟩ := g.2.2 _ y hy
  exact ⟨g.1.trans h.sameCodes, h.two, ⟨x', hx', gx.1.trans sx⟩, ⟨y', hy', gy.1.trans sy⟩⟩

/-- **The two messages of (Dot) have their tables.** -/
theorem placedDot_of_seated {T : Statement} {codes : Codes} {S : LinShape} {omega w : Nat}
    (h : SeatedDot T codes S omega w) (hok : linOk codes S = true) :
    PlacedDot T S omega (linLayOmega codes S) w (linLayW codes S) := by
  obtain ⟨x, hx, sx⟩ := h.omega
  obtain ⟨y, hy, sy⟩ := h.w
  simp only [linOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hS : S.ok = true := by tauto
  have h5 : S.matrixRows ≤ vectorRoom codes S.omega S.omegaRowsHigh := by tauto
  have h6 : 2 ^ S.kCol ≤ vectorRoom codes S.w S.wRowsHigh := by tauto
  simp only [LinShape.ok, Bool.and_eq_true, decide_eq_true_eq] at hS
  have a7 : LinShape.vectorMessageOk S.omega = true := by tauto
  have a8 : LinShape.vectorMessageOk S.w = true := by tauto
  simp only [LinShape.vectorMessageOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at a7 a8
  have b1 : S.omega.mainRows ≠ 0 := by tauto
  have b2 : S.w.mainRows ≠ 0 := by tauto
  have tO := tableBits_main T _ x hx (by rw [sx]; exact b1) S.omegaRowsHigh
  have tW := tableBits_main T _ y hy (by rw [sy]; exact b2) S.wRowsHigh
  rw [sx, h.sameCodes] at tO
  rw [sy, h.sameCodes] at tW
  refine ⟨h.two, tO.1, tW.1, tO.2, tW.2, ?_, ?_⟩
  · exact ceilLog2_le _ _ (Nat.le_trans h5 (vectorRoom_le _ _ _))
  · exact (Nat.pow_le_pow_iff_right (by decide)).1 (Nat.le_trans h6 (vectorRoom_le _ _ _))

/-- **What (Dot) means where it lies among constraints that hold of words.** -/
theorem dotSays (T : Statement) (codes : Codes) (S : LinShape) (weights : List Tensor)
    (psi : List E) (omega w : Nat) (dot : Row) (rows : List Row) (m : Words K)
    (hrow : linDotRow S weights psi omega (linLayOmega codes S) w (linLayW codes S) = some dot)
    (hd : ∀ g ∈ weights, g.denseVars = []) (hmem : dot ∈ rows)
    (hs : Means.AllSay ρ T rows m) (hSeat : SeatedDot T codes S omega w)
    (hok : linOk codes S = true) :
    DotEq S.matrixRows S.kCol (fun y => (weights.map fun g => ρ.val (g.entry y)).sum)
      (fun y => m omega .main ((linLayOmega codes S).index y)) (psi.map ρ.val)
      (fun c => m w .main ((linLayW codes S).index c)) :=
  (dotMeansW ρ T S weights psi omega _ w _ dot hrow hd (placedDot_of_seated hSeat hok) m).1
    (hs dot hmem)

end Desc.K14.Law
