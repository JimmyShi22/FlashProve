-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/RowsShapedTest.lean: THE CLOSED FACT `P1Opts.RowsShaped`
(Johnson/Top/H0/Opts/SomeAtRows.lean: the first chain's rows' entry (sending k, place j) has the
shape of the plan's j-th seat with a sample of sending k) AS A TEST WITH CODE ON PUBLIC DATA, WITH
ITS LEMMA "the test accepts → the sentence". It is one of the four premises of `alike_of_rows`
(Johnson/P1K8R/AlikeOfRows.lean: the first half of the field "alike" of `K8LeftT`), and of
`callsSome_of` and `digSome_of` in SomeAtRows.lean itself.
  `rowsShapedB rows ps n`: for each sending k below n and each seat p with a sample of sending k,
    at its place j among these: the rows have an entry at (k, j), and its shape is p's.
  `rowsShaped_of_test`: where every seat's sending is below n: the test's yes gives the sentence.
  `rowsShaped_at`: at the closed letters: ps := `P5J.At.pseats Zp`, n := the number of the first
    chain's sendings: by `P5T.planSeats_send_lt`.
How it parts from two tests that lie. `P5T.radIsB` (Johnson/P5T/MembersByMake.lean) asks that the
rows have a RADIUS at each such (k, j), and which: it does not read the shape. `P5T.membersFault`
(Johnson/P5T/MemberLists.lean) compares whole lists of shapes, and labels too: more than is asked.
Limits. That the test accepts is shown nowhere here; it has run nowhere.
(Where this and lean/THEOREM.md differ, the page holds.) Nothing on soundness or
on hiding.

-/
import Johnson.Top.H0.Opts.SomeAtRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8T

open OnBytes
open P5T (PSeat mineAt firstRows)

/-- The test. -/
def rowsShapedB (rows : List Johnson.G.SendRow) (ps : List PSeat) (n : ℕ) : Bool :=
  (List.range n).all fun k => (mineAt ps k).zipIdx.all fun pj =>
    decide ((((firstRows rows)[k]?).bind (·.sampled[pj.2]?)).map (·.1) = some pj.1.shape)

/-- **The test's yes gives the sentence.** -/
theorem rowsShaped_of_test {rows : List Johnson.G.SendRow} {ps : List PSeat} {n : ℕ}
    (hn : ∀ p ∈ ps, p.send < n) (t : rowsShapedB rows ps n = true) :
    P1Opts.RowsShaped rows ps := by
  intro k j p hp
  have hmem : p ∈ mineAt ps k := List.mem_of_getElem? hp
  have hk : k < n := by
    unfold mineAt at hmem
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hmem
    rw [Bool.and_eq_true] at h2
    have e : p.send = k := eq_of_beq h2.1
    rw [← e]
    exact hn p h1
  have t1 := List.all_eq_true.1 t k (List.mem_range.2 hk)
  have t2 := List.all_eq_true.1 t1 (p, j) (List.mk_mem_zipIdx_iff_getElem?.2 (by simpa using hp))
  obtain ⟨e, he, hs⟩ := Option.map_eq_some_iff.1 (of_decide_eq_true t2)
  obtain ⟨sh, ρ⟩ := e
  obtain rfl : sh = p.shape := hs
  exact ⟨ρ, he⟩

/-- **At the closed letters.** -/
theorem rowsShaped_at (Zp : ProofFile.Pub) {rows : List Johnson.G.SendRow}
    (t : rowsShapedB rows (P5J.At.pseats Zp) Zp.made.proof.1.sends.length = true) :
    P1Opts.RowsShaped rows (P5J.At.pseats Zp) :=
  rowsShaped_of_test (fun p hp => P5T.planSeats_send_lt Zp Zp.D.1 p hp) t

end P1K8T

#print axioms P1K8T.rowsShaped_of_test
#print axioms P1K8T.rowsShaped_at
