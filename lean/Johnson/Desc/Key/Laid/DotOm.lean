-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Laid/DotOm.lean: The key file's table's claim «DotOm» out of its claim «Dot», at
what K14's second part of the last chain has laid (`Laid`, Johnson/Desc/Third/Law/LaidDef.lean).
Theorems; no definition.

Main names.
  `weightAt_read`: the tables' weight of a row reads as the sum of the readings.
  `dotOm_iff_dotEq`: the tables' `DotOmAt` at "ρ x = ρ y" is `Desc.K14.Law.DotEq`
    (Johnson/Desc/K14/Law/DotCount.lean) at the readings.
  `dotOm_of_laid`: from `Laid`, four conditions on the record in front and "the own group had one
    open row": if the own group's open row number 1 behind holds of val, `DotOmAt` holds of Omega's
    and W's tables as val has them.

How. The row number 1 behind is (Dot) (`Laid.group'`) · `rowHolds_iff_says_of_rowIn`
(Johnson/Desc/Key/RowHoldsSays.lean) at `Laid.dotIn` · `Desc.K14.Law.dotMeansOk`
(Johnson/Desc/K14/Law/MeansDotOk.lean): what (Dot) says of words is DotEq, under PlacedDot, which
`placedDot_of_seated` (Johnson/Desc/K14/Law/PlacedDot.lean) gives from the two messages' shapes and
`linOk`.

The four conditions, by name: lin: the shape is lawful at the statement's codes · w: the message at
W's number is there and has the plan's shape of W · omega: Omega, in the border's copy, has the
plan's shape of Omega · weights: every vector of the border's row weights is well-formed. They are
`AtDot`'s four (Johnson/Desc/Third/Law/AtDot.lean), stated here at `Laid`'s own letters.

Limits. ρ reads into a field. No record is shown at which the premises hold together. Nothing on
soundness or on hiding.
-/
import Johnson.Desc.Third.Law.LaidDef
import Johnson.Desc.Key.KeyMeaning23
import Johnson.Desc.Key.KeySumRead
import Johnson.Desc.Key.RowHoldsSays
import Johnson.Desc.K14.Law.MeansDotOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Third (S₃ Border Laid)
open _root_.Desc.K14.Law (DotEq eqK entry_eq SeatedDot placedDot_of_seated dotMeansOk)

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

theorem weightAt_read_from (g : List Tensor) (y : Nat) (s : E) :
    ρ.val (g.foldl (fun s t => addE s (t.entry y)) s) =
      ρ.val s + (g.map fun t => ρ.val (t.entry y)).sum := by
  induction g generalizing s with
  | nil => simp
  | cons t g ih =>
    rw [List.foldl_cons, ih, ρ.add, List.map_cons, List.sum_cons, add_assoc]

/-- The weight of a row reads as the sum of the readings. -/
theorem weightAt_read (g : List Tensor) (y : Nat) :
    ρ.val (weightAt g y) = (g.map fun t => ρ.val (t.entry y)).sum := by
  unfold weightAt
  rw [weightAt_read_from, ρ.zero, zero_add]

/-- **The tables' sentence `DotOmAt` and K14's `DotEq` are one.** -/
theorem dotOm_iff_dotEq (S : LinShape) (g : List Tensor) (psi : List E) (om v : Nat → E) :
    DotOmAt (fun a b => ρ.val a = ρ.val b) S g psi om v ↔
      DotEq S.matrixRows S.kCol (fun y => (g.map fun t => ρ.val (t.entry y)).sum)
        (fun y => ρ.val (om y)) (psi.map ρ.val) (fun c => ρ.val (v c)) := by
  unfold DotOmAt evalEq DotEq
  beta_reduce
  rw [sumE_read ρ.val ρ.zero ρ.add, sumE_read ρ.val ρ.zero ρ.add]
  have e1 : ∀ y ∈ Finset.range S.matrixRows, ρ.val (mulE (weightAt g y) (om y)) =
      (g.map fun t => ρ.val (t.entry y)).sum * ρ.val (om y) := fun y _ => by
    rw [ρ.mul, weightAt_read]
  have e2 : ∀ c ∈ Finset.range (2 ^ S.kCol), ρ.val (mulE ((Tensor.eq psi).entry c) (v c)) =
      eqK (psi.map ρ.val) c * ρ.val (v c) := fun c _ => by
    rw [ρ.mul, entry_eq, ρ.one, one_mul]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]

/-- **«DotOm» out of «Dot».** -/
theorem dotOm_of_laid (S : LinShape) {s s' : S₃} {b : Border} {yO : OnBytes.Oracle}
    {G : OnBytes.Group} {dot : OnBytes.Row} (L : Laid S s s' b yO G dot)
    (hlin : linOk s.st.codes S = true)
    (hw : ∃ x, s.st.oracles[s.loc.w]? = some x ∧ x.shape = S.w) (hO : yO.shape = S.omega)
    (hg : ∀ g ∈ b.g, g.ok = true) (one : G.rows.size = 1) (val : Nat → Part → Nat → E)
    (hd : rowsHold (fun a b => ρ.val a = ρ.val b) s'.st val s.loc.own 1 1) :
    DotOmAt (fun a b => ρ.val a = ρ.val b) S b.g b.shared.psi
      (fun y => val s.st.oracles.size .main ((linLayOmega s.st.codes S).index y))
      (fun c => val s.loc.w .main ((linLayW s.st.codes S).index c)) := by
  obtain ⟨x, hx, sx⟩ := hw
  have lt : s.loc.w < s.st.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
  have hS : SeatedDot s'.st s.st.codes S s.st.oracles.size s.loc.w :=
    ⟨L.codes, fun e => absurd lt (by rw [← e]; exact Nat.lt_irrefl _), ⟨_, L.copy, hO⟩,
      ⟨x, (L.old _ lt).trans hx, sx⟩⟩
  have hP := placedDot_of_seated hS hlin
  obtain ⟨G'', hG'', _, _, hall⟩ := hd
  have e := Option.some.inj (hG''.symm.trans L.group')
  have hl : G.rows.toList.length = 1 := by
    rw [Array.length_toList]
    exact one
  have hmem : dot ∈ (G''.rows.toList.drop 1).take 1 := by
    rw [e]
    show dot ∈ ((G.rows.push dot).toList.drop 1).take 1
    rw [Array.toList_push, List.drop_left' hl]
    simp
  have hsay := (rowHolds_iff_says_of_rowIn ρ s'.st _ val dot L.dotIn).1 (hall dot hmem)
  exact (dotOm_iff_dotEq ρ S b.g b.shared.psi _ _).2
    ((dotMeansOk ρ s'.st S b.g b.shared.psi _ _ _ _ dot L.dotIs hg hP _).1 hsay)

end VerifiableInference.Desc.Key
