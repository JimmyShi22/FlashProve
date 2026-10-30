--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/TabOfRows.lean: a stored table as a function of its rows before encoding.

  symF            the code's symbol at a location of a row of words of the base field, in the
                  library's base field. symF_lift: lifted, it is genK at the row
                  (Johnson/Desc/K14/Law/NearRows.lean). bitsK_map: a tool.
  tabOfRows       at a location, for each row its symbol, as a word. It is not computed: a real
                  table has millions of locations.
  tabOfRows_col   the column at every location is the code's symbol of each row: the premise hcol of
                  nearAt_of_foldRowsB and of htab_of_cols, as a theorem.

What is not claimed. That tabOfRows of given rows is the table beneath any key's root: no hash is
named here. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K14.Law.HonestRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)

/-- bitsK goes along a map of fields. -/
theorem bitsK_map {K L : Type} [Field K] [Field L] (φ : K →+* L) : ∀ (l : List K) (j : Nat),
    φ (bitsK l j) = bitsK (l.map φ) j
  | [], _ => map_one φ
  | x :: l, j => by
    show φ ((if j % 2 = 1 then x else 1) * bitsK l (j / 2)) =
      (if j % 2 = 1 then φ x else 1) * bitsK (l.map φ) (j / 2)
    rw [map_mul, bitsK_map φ l]
    by_cases h : j % 2 = 1
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, map_one]

/-- The code's symbol at x of a row of words of the base field, in the library's base field. -/
noncomputable def symF (S : FoldeqShape) (x : Nat) (v : Nat → UInt64) : Cb.Gl.F :=
  toF (generatorAt S.index.code x).messageScale *
      (∑ j ∈ Finset.range S.index.code.ell,
        bitsK (((generatorAt S.index.code x).f.map toF).take S.index.code.logEll) j * toF (v j)) +
    toF (generatorAt S.index.code x).tailScale *
      (∑ j ∈ Finset.range S.index.code.r,
        bitsK (((generatorAt S.index.code x).f.map toF).take S.index.code.logR) j *
          toF (v (S.tailFirst + j)))

/-- Lifted, it is genK at the row, lifted by the program and read. -/
theorem symF_lift (S : FoldeqShape) (x : Nat) (v : Nat → UInt64) :
    algebraMap Cb.Gl.F Cb.Gl.E (symF S x v) =
      genK OnBytes.Model.Reading.gl S x
        (fun k => OnBytes.Model.Reading.gl.val (OnBytes.ofF (v k))) := by
  unfold symF genK
  simp only [map_add, map_mul, map_sum, bitsK_map, gl_ofF, List.map_take, List.map_map]
  rfl

/-- **The stored table as a function of its rows before encoding**: at the location x, for each row
its code's symbol, as a word. -/
noncomputable def tabOfRows (S : FoldeqShape) (RwF : Nat → Nat → UInt64) (x : Nat) :
    List UInt64 :=
  (List.range (2 ^ S.index.v)).map fun n => OnBytes.Slice.ofF (symF S x (RwF n))

theorem tabOfRows_col (S : FoldeqShape) (RwF : Nat → Nat → UInt64) (x n : Nat)
    (hn : n < 2 ^ S.index.v) :
    OnBytes.Model.Reading.gl.val (OnBytes.ofF ((tabOfRows S RwF x).toArray.getD n 0)) =
      genK OnBytes.Model.Reading.gl S x
        (fun k => OnBytes.Model.Reading.gl.val (OnBytes.ofF (RwF n k))) := by
  have e : (tabOfRows S RwF x).toArray.getD n 0 = OnBytes.Slice.ofF (symF S x (RwF n)) := by
    unfold tabOfRows
    simp [Array.getD, hn]
  rw [e, gl_ofF, toF_ofF, symF_lift]

end Desc.K14.Law
