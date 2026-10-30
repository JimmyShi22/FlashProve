-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsArr.lean: AN ARRAY AT A TIME, NOT A SYMBOL: WHAT A YES OF THE LOOKUP's
OWN TEST `symArrB` (Johnson/Desc/First/Look/K3CallerAttReads.lean: one array of a link's
list, by the layout's blocks) HANDS OUT: at every cell below the sizes the first four clauses of
`SymsOne` (Johnson/Road/K4/K4PinsSym.lean), AND the array's one member and the place by `laidPlace`.
THAT FILE's
`sym_seated` concludes "there is a seat, and it fits": it does not say which member, nor which
place. Theorems, by unfolding. No new test.


  `symArr_data`: what a yes gives of the array: its link and name, the layout's entry, the member.
  `seatCalls_of`: `seatCalls` at a cell of an array with a member and a place. Both arms: an array
    of the link's own, and one that an earlier link sent.
  **`symArr_cell`**: at every r < R and c < K: a seat s and a proof that s is a member of l, with:
    `seatCalls D i (.cell t r c) = some s` · s.mask = false · s.row and s.place inside the member's
    main table · s.msg is the array's ONE member · (s.row, s.place) is what `laidPlace` finds in the
    array's blocks.
  `symArrB_none`: the test can fail: where the link's list has no array number t it says no.

OBJECT: none of its own. USER: Johnson/Road/K4/SymsOfLayout.lean; meant: the tests by blocks for
`SymsOne`. LETTERS: D, l, i, t, R, K: free (`SymsOne` speaks at l := `sigListCalls D rad i`).

Limits. K04_law IS NOT PROVED BY THIS. NOTHING IS EVALUATED HERE. `SymsOne`'s LAST TWO CLAUSES (the
row and place are those that the other reading's seats name; the tenant by number is the member's
seat) ARE NOT TOUCHED: the two last conjuncts of `symArr_cell` are meant as their handles. One
direction.
-/
import Johnson.Road.K4.K4PinsSym
import Johnson.Desc.First.Look.K3CallerAttReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open Johnson.Pack
open VerifiableInference.Desc.First.Look (Sent Seat seatCalls laidPlace blocksB laidPlace_some
  msgIn symArrB)

variable {D : Sent} {l : List (OnBytes.OracleShape × ℕ)} {i t R K : ℕ}

/-- What a yes gives of the array. -/
theorem symArr_data (h : symArrB D l i t R K = true) :
    ∃ (bn : ℕ × String) (a : OnBytes.Params.ReqArray) (k : ℕ) (hk : k < l.length),
      (D.arrayOf.getD i #[])[t]? = some bn ∧ OnBytes.reqArray D.layout bn.1 bn.2 = some a ∧
      msgIn D i bn.1 a.message = some k ∧
      blocksB a.blocks R K (l.get ⟨k, hk⟩).1.mainRows (pMain D.codes (l.get ⟨k, hk⟩).1).ell =
        true := by
  unfold symArrB at h
  split at h
  · rename_i bn hbn
    split at h
    · rename_i a ha
      split at h
      · rename_i k hm
        split at h
        · rename_i o ho
          obtain ⟨hk, eo⟩ := List.getElem?_eq_some_iff.1 ho
          refine ⟨bn, a, k, hk, hbn, ha, hm, ?_⟩
          rw [List.get_eq_getElem, eo]
          exact h
        · cases h
      · cases h
    · cases h
  · cases h

/-- `seatCalls` at a cell of an array with a member and a place. -/
theorem seatCalls_of {bn : ℕ × String} {a : OnBytes.Params.ReqArray} {k r c : ℕ} {rp : ℕ × ℕ}
    (hbn : (D.arrayOf.getD i #[])[t]? = some bn)
    (ha : OnBytes.reqArray D.layout bn.1 bn.2 = some a)
    (hm : msgIn D i bn.1 a.message = some k) (hp : laidPlace a.blocks r c = some rp) :
    seatCalls D i (.cell t r c) = some ⟨k, false, rp.1, rp.2⟩ := by
  unfold msgIn at hm
  simp only [seatCalls, hbn, Option.bind_some, ha, hp]
  by_cases hb : (bn.1 == i) = true
  · rw [if_pos hb] at hm ⊢
    rw [Option.some.inj hm]
  · rw [if_neg hb] at hm ⊢
    rw [hm]
    rfl

/-- **Under the test, at every cell below the sizes: the first four clauses of `SymsOne`**, the
array's one member, and the place by `laidPlace`. -/
theorem symArr_cell (h : symArrB D l i t R K = true) :
    ∃ (a : OnBytes.Params.ReqArray) (k : ℕ), ∀ r c, r < R → c < K →
      ∃ (s : Seat) (hk : s.msg < l.length),
        seatCalls D i (.cell t r c) = some s ∧ s.mask = false ∧
        s.row < (l.get ⟨s.msg, hk⟩).1.mainRows ∧
        s.place < (pMain D.codes (l.get ⟨s.msg, hk⟩).1).ell ∧
        s.msg = k ∧ laidPlace a.blocks r c = some (s.row, s.place) := by
  obtain ⟨bn, a, k, hk, hbn, ha, hm, hB⟩ := symArr_data h
  refine ⟨a, k, fun r c hr hc => ?_⟩
  obtain ⟨rp, e1, e2, e3⟩ := laidPlace_some hB hr hc
  exact ⟨⟨k, false, rp.1, rp.2⟩, hk, seatCalls_of hbn ha hm e1, rfl, e2, e3, rfl, e1⟩

/-- **The test can fail**: no array of that number, no yes. -/
theorem symArrB_none (h : (D.arrayOf.getD i #[])[t]? = none) : symArrB D l i t R K = false := by
  unfold symArrB
  rw [h]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.symArr_data
#print axioms OnBytes.Road.K4.seatCalls_of
#print axioms OnBytes.Road.K4.symArr_cell
#print axioms OnBytes.Road.K4.symArrB_none
