-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/VecWords.lean: the vector that lies in W's message, read two ways: off the
words that tables
give at a statement (`wordsOn`, Johnson/Desc/Means/ItemsTab.lean), at W's number under W's layout;
and off W's
own table, cut to its shape's ranges. A definition, and statements with their proofs. No witness's
type and no table of joints stands in it.
Main names:
  `vecAt lay sh M c`: entry c of the vector that lies in the main rows of the table M of a message
    of the shape sh under the layout lay: the low bits of the layout's index name the row, the high
    bits the place.
  `wordsOn_main`: what `wordsOn` gives at a message that is there, in its main table.
  `place_main`: under the test on the codes' lengths an index below the main table's size has a
    place below the code's message length.
  `vec_of_words`: **at a record of (Eval) with its three public facts: the words that the tables T
    give, at W's number and at the layout's index of c, are `vecAt` of any table M that agrees with
    T's at W inside the shape's ranges and is 0 at the rows beyond them.**
  `not_vec_of_words`: a try: at a table M that parts from T's at the entry's own row and place the
    two part.
USER: `hvec_paid` (Johnson/Desc/K13/Law/PointStepBack.lean); `vecAt`: the shared table's (Dot).
Used of `verify-on-bytes`: `VectorLay.index`, `ceilLog2`, as pure functions.

What is not claimed. That a witness's tables are such. Nothing on soundness.

-/
import Johnson.Desc.K13.Law.StepBack
import Johnson.Desc.Means.ItemsLen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Params (LinShape)
open OnBytes.Means (Words wordsOn tableSize realRows ellOf CodeThere place_lt_ell)

/-- Entry c of the vector that lies in the main rows of a table. -/
def vecAt (lay : VectorLay) (sh : OracleShape) (M : Bool → ℕ → ℕ → GE) (c : ℕ) : GE :=
  M false (lay.index c % 2 ^ ceilLog2 sh.mainRows) (lay.index c / 2 ^ ceilLog2 sh.mainRows)

/-- What `wordsOn` gives at a message that is there, in its main table. -/
theorem wordsOn_main (S : Statement) (T : ℕ → Bool → ℕ → ℕ → GE) (o i : ℕ) (x : OnBytes.Oracle)
    (hx : S.oracles[o]? = some x) :
    wordsOn S T o .main i =
      if i % 2 ^ ceilLog2 x.shape.mainRows < x.shape.mainRows then
        T o false (i % 2 ^ ceilLog2 x.shape.mainRows) (i / 2 ^ ceilLog2 x.shape.mainRows)
      else 0 := by
  unfold wordsOn Statement.rowBits realRows
  rw [hx]
  rfl

/-- Under the test on the codes' lengths an index below the main table's size has a place below the
code's message length. -/
theorem place_main (S : Statement) (hc : S.codes.lengthsOk = true) (o i : ℕ) (x : OnBytes.Oracle)
    (hx : S.oracles[o]? = some x) (ht : x.shape.code < S.codes.base.size)
    (hi : i < tableSize S o .main) :
    i / 2 ^ ceilLog2 x.shape.mainRows < (S.codes.base.getD x.shape.code default).ell := by
  have hT : CodeThere S o .main := by
    intro y hy
    rw [hx] at hy
    rw [← Option.some.inj hy]
    exact ht
  have h := place_lt_ell hc hT hi
  unfold Statement.rowBits ellOf at h
  rw [hx] at h
  exact h

/-- **The two readings of the vector agree.** -/
theorem vec_of_words (Sh : LinShape) (D : EvalAt) (hD : D.Ok Sh) (T : ℕ → Bool → ℕ → ℕ → GE)
    (x : OnBytes.Oracle) (hx : D.st.oracles[D.w]? = some x) (hc : D.st.codes.lengthsOk = true)
    (ht : x.shape.code < D.st.codes.base.size) (M : Bool → ℕ → ℕ → GE)
    (hM : ∀ row place, row < x.shape.mainRows →
      place < (D.st.codes.base.getD x.shape.code default).ell →
      M false row place = T D.w false row place)
    (hM0 : ∀ row place, ¬ row < x.shape.mainRows → M false row place = 0) :
    ∀ c < 2 ^ Sh.kCol, wordsOn D.st T D.w .main (D.lay.index c) = vecAt D.lay x.shape M c := by
  intro c hc'
  have hi : D.lay.index c < tableSize D.st D.w .main := by
    rw [hD.2.2.size]
    exact index_lt _ _ (lt_of_lt_of_le hc' (Nat.pow_le_pow_right (by norm_num) hD.1))
  rw [wordsOn_main _ _ _ _ x hx]
  unfold vecAt
  split
  · rename_i h
    exact (hM _ _ h (place_main _ hc _ _ x hx ht hi)).symm
  · rename_i h
    exact (hM0 _ _ h).symm

/-- **A try**: at a table that parts from T's at the entry's own row and place, a real row, the two
readings part. -/
theorem not_vec_of_words (D : EvalAt) (T : ℕ → Bool → ℕ → ℕ → GE) (x : OnBytes.Oracle)
    (hx : D.st.oracles[D.w]? = some x) (M : Bool → ℕ → ℕ → GE) (c : ℕ)
    (hr : D.lay.index c % 2 ^ ceilLog2 x.shape.mainRows < x.shape.mainRows)
    (hne : M false (D.lay.index c % 2 ^ ceilLog2 x.shape.mainRows)
        (D.lay.index c / 2 ^ ceilLog2 x.shape.mainRows) ≠
      T D.w false (D.lay.index c % 2 ^ ceilLog2 x.shape.mainRows)
        (D.lay.index c / 2 ^ ceilLog2 x.shape.mainRows)) :
    wordsOn D.st T D.w .main (D.lay.index c) ≠ vecAt D.lay x.shape M c := by
  rw [wordsOn_main _ _ _ _ x hx, if_pos hr]
  exact fun e => hne e.symm

end VerifiableInference.Desc.K13.Law
