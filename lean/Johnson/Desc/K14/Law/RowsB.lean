--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/RowsB.lean: two tests with code over a stored table's rows before encoding.

  recRowsB   the key's record holds each row's true answers at the key's seeds. recRows_of_B: its
             yes gives the equations that hrec_of_rows asks
             (Johnson/Desc/K14/Law/HonestRows.lean).
             eqTab: eq(z, k) for all k, made once.
  visB       a vector is the row weights applied to the matrix that the rows hold. vIs_of_B: its yes
             gives VIs (Johnson/Desc/K14/Law/PointGood.lean) at any table that holds the rows.

What is not claimed. The converse of either test. Nothing on soundness, on an honest prover or on
hiding.

-/
import Johnson.Desc.K14.Law.TabOfRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)

/-- eq(z, k) for the k below n, made once. -/
def eqTab (z : List E) (n : Nat) : Array E := (Array.range n).map (eqE z)

theorem eqTab_getD (z : List E) (n k : Nat) (h : k < n) : (eqTab z n).getD k zeroE = eqE z k := by
  unfold eqTab
  simp [Array.getD, h]

/-- **The key's record holds each row's true answers at the key's seeds**: computed. RwF n: row n's
message with its tail, as words of the base field, laid out as u is. -/
def recRowsB (p : Par) (key : TableKey) (RwF : Nat → Nat → UInt64) : Bool :=
  (List.range p.S.fold.index.answers).all fun a =>
    let T := eqTab (key.seeds.getD a default).z p.S.fold.index.plain
    (List.range (2 ^ p.S.fold.index.v)).all fun n =>
      decide (addE (sumE p.S.fold.index.plain fun k =>
            mulE (T.getD k zeroE) (OnBytes.ofF (RwF n k)))
          (sumE 3 fun t => mulE (mulE (key.seeds.getD a default).beta (thetaE t))
            (OnBytes.ofF (RwF n (p.S.fold.index.padPlace a t)))) =
        key.record.getD (n * p.S.fold.index.answers + a) zeroE)

theorem recRows_of_B (p : Par) (key : TableKey) (RwF : Nat → Nat → UInt64)
    (h : recRowsB p key RwF = true) :
    ∀ n < 2 ^ p.S.fold.index.v, ∀ a < p.S.fold.index.answers,
      (∑ k ∈ Finset.range p.S.fold.index.plain,
          eqK ((key.seeds.getD a default).z.map OnBytes.Model.Reading.gl.val) k *
            OnBytes.Model.Reading.gl.val (OnBytes.ofF (RwF n k))) +
        ∑ t ∈ Finset.range 3, OnBytes.Model.Reading.gl.val (key.seeds.getD a default).beta *
          OnBytes.Model.Reading.gl.val (thetaE t) *
            OnBytes.Model.Reading.gl.val (OnBytes.ofF (RwF n (p.S.fold.index.padPlace a t))) =
      OnBytes.Model.Reading.gl.val
        (key.record.getD (n * p.S.fold.index.answers + a) zeroE) := by
  intro n hn a ha
  simp only [recRowsB, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have e := congrArg OnBytes.Model.Reading.gl.val (h a ha n hn)
  simp only [OnBytes.Model.Reading.gl.add, OnBytes.Model.Reading.gl.mul, val_sumE] at e
  rw [← e]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [eqTab_getD _ _ _ (Finset.mem_range.1 hk), val_eqE]

/-- **The vector is the row weights applied to the matrix that the rows hold**: computed. -/
def visB (S : LinShape) (gE : Nat → E) (RwF : Nat → Nat → UInt64) (VE : Nat → E) : Bool :=
  (List.range (2 ^ S.kCol)).all fun c =>
    decide (VE c = sumE S.matrixRows fun y =>
      mulE (gE y) (OnBytes.ofF (RwF (c / 2 ^ S.kLo) (c % 2 ^ S.kLo + 2 ^ S.kLo * y))))

theorem vIs_of_B (S : LinShape) (gE : Nat → E) (RwF : Nat → Nat → UInt64) (VE : Nat → E)
    (Tab : Nat → Nat → GE)
    (hT : ∀ c < 2 ^ S.kCol, ∀ y < S.matrixRows,
      Tab (c / 2 ^ S.kLo) (c % 2 ^ S.kLo + 2 ^ S.kLo * y) =
        OnBytes.Model.Reading.gl.val
          (OnBytes.ofF (RwF (c / 2 ^ S.kLo) (c % 2 ^ S.kLo + 2 ^ S.kLo * y))))
    (h : visB S gE RwF VE = true) :
    VIs S (fun y => OnBytes.Model.Reading.gl.val (gE y)) Tab
      (fun c => OnBytes.Model.Reading.gl.val (VE c)) := by
  intro c hc
  simp only [visB, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have e := congrArg OnBytes.Model.Reading.gl.val (h c hc)
  simp only [OnBytes.Model.Reading.gl.mul, val_sumE] at e
  refine Eq.trans e (Finset.sum_congr rfl fun y hy => ?_)
  unfold matOf
  rw [hT c hc y (Finset.mem_range.1 hy)]

end Desc.K14.Law
