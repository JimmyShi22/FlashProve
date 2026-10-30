-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/ClosedAt25.lean: FOUR CLOSED FACTS ON THE 25 WRITTEN ROWS OF THE CODE
SWITCH, AT THE WRITTEN VALUES OF THE FULL SIZE. Tests with code, laws "test = true → the sentence",
the tests' values by the kernel, one negative test each.

The written values: `tableFullLit` (the 25 rows: Johnson/Top/H0/K2Caller/LitRows.lean) ·
`codesFull2` (the codes) · `N0Full` := numbersOf psFull and `seatsAllFull`
(Johnson/P5T/PlanSeatsFull.lean) · `oldsAt` (Johnson/Top/H0/K2Hears/PlaceNums.lean). With r the row
number m, news := N0Full.sent (m + 1) 0, and the two functions written out as
Johnson/Top/H0/K2Caller/SeatsOfN.lean has them (not imported): seatNew i := news.getD i (0, 0) ·
seatOld i := (N0Full.keptOf m).getD (r.kept.idxOf i) (0, 0):
  `cs_at25`      r.cs = codesFull2 (a call of `seats25_says` at `seats25_full`:
                 Johnson/Top/H0/K2Caller/SeatFitsPlan.lean, SeatFitsFull.lean)
  `len_at25`     r.l.length = news.length; `keptLen_at25`: r.kept.length = (N0Full.keptOf m).length
                 (the test `lens25B`; its value `lens25_full`; `lens25_moved`: the negative test)
  `hN_at25`      so news[1 + n]? = some (seatNew ⟨1 + n, ho⟩) at every 1 + n < r.l.length
  `olds_at25`    (oldsAt (m + 1)).length = r.kept.length: BY `oldsAt`'s OWN TEXT: no test is needed
  `hal_at25`     at every member i of r.lo whose number is kept, where r.kept has no number twice:
                 there is v with news[1 + r.kept.idxOf i]? = some v and arr at seatOld i = arr at v,
                 at arr := arrOf seatsAllFull (`keptAlign_at`, Johnson/P5T/KeptAlign.lean; the
                 test's value `align25_full`; `align25_moved`: the negative test;
                 `keptNodup25_full`: no written row keeps a number twice)

What is not claimed. THAT THE WRITTEN VALUES ARE THE CLOSED CONSTANT's LETTERS: (N Zp cF).sent |
keptOf = N0Full's · cs Zp = codesFull2 · arr Zp = arrOf seatsAllFull · the row that the verifier
computes = tableFullLit[m]: none is shown here. The callers' binders over
{a // (plainHd r …).cl a}: not typed here: that set's members are the callers' to bring to "a member
of r.lo whose number is kept". No soundness statement.

-/
import Johnson.Top.H0.K2Caller.SeatFitsFull
import Johnson.Top.H0.K2Hears.PlaceNums
import Johnson.P5T.KeptAlign

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.K2 (oldsAt)
open P5T (N0Full psFull seatsAllFull arrOf keptAlignB keptAlign_at)
open Johnson.G (codesFull2)

/-- The written codes at every written row. -/
theorem cs_at25 {m : ℕ} {r : SwRow} (hr : tableFullLit[m]? = some r) : r.cs = codesFull2 :=
  (seats25_says seats25_full hr).1

/-- A test: row number m has as many new members as group m + 1 sends first, and keeps as many as
segment m's list of kept tenants has. -/
def lens25B (N : Numbers) (rows : List SwRow) : Bool :=
  rows.zipIdx.all fun x =>
    x.1.l.length == (N.sent (x.2 + 1) 0).length && x.1.kept.length == (N.keptOf x.2).length

theorem lens25_says {N : Numbers} {rows : List SwRow} (h : lens25B N rows = true) {m : ℕ}
    {r : SwRow} (hr : rows[m]? = some r) :
    r.l.length = (N.sent (m + 1) 0).length ∧ r.kept.length = (N.keptOf m).length := by
  have h1 := List.all_eq_true.1 h (r, m) (List.mem_zipIdx_iff_getElem?.2 hr)
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  exact h1

set_option maxRecDepth 1000000 in
theorem lens25_full : lens25B N0Full tableFullLit = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the rows moved by one place. -/
theorem lens25_moved : lens25B N0Full (tableFullLit.drop 1) = false := by decide +kernel

theorem len_at25 {m : ℕ} {r : SwRow} (hr : tableFullLit[m]? = some r) :
    r.l.length = (N0Full.sent (m + 1) 0).length := (lens25_says lens25_full hr).1

theorem keptLen_at25 {m : ℕ} {r : SwRow} (hr : tableFullLit[m]? = some r) :
    r.kept.length = (N0Full.keptOf m).length := (lens25_says lens25_full hr).2

/-- The callers' premise hN at news := N0Full.sent (m + 1) 0 and seatNew written out. -/
theorem hN_at25 {m : ℕ} {r : SwRow} (hr : tableFullLit[m]? = some r) :
    ∀ (n : ℕ) (_ho : 1 + n < r.l.length),
      (N0Full.sent (m + 1) 0)[1 + n]? = some ((N0Full.sent (m + 1) 0).getD (1 + n) (0, 0)) := by
  intro n ho
  have h1 : 1 + n < (N0Full.sent (m + 1) 0).length := by rw [← len_at25 hr]; exact ho
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  rfl

/-- As many old messages as the row keeps: by `oldsAt`'s own text. -/
theorem olds_at25 {m : ℕ} {r : SwRow} (hr : tableFullLit[m]? = some r) :
    (oldsAt (m + 1)).length = r.kept.length := by
  unfold oldsAt
  simp [hr]

set_option maxRecDepth 1000000 in
theorem align25_full : keptAlignB (arrOf seatsAllFull) N0Full 25 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the tenants' numbers by the tree alone. -/
theorem align25_moved : keptAlignB (fun j _ => j) N0Full 25 = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem keptNodup25_full : (tableFullLit.all fun r => decide r.kept.Nodup) = true := by
  decide +kernel

theorem rows25 : tableFullLit.length = 25 := by decide +kernel

/-- The callers' premise hal, at a member of r.lo whose number is kept, seatOld written out. -/
theorem hal_at25 {m : ℕ} {r : SwRow} (hr : tableFullLit[m]? = some r) (i : Fin r.lo.length)
    (hi : i.val ∈ r.kept) :
    ∃ v, (N0Full.sent (m + 1) 0)[1 + r.kept.idxOf i.val]? = some v ∧
      arrOf seatsAllFull ((N0Full.keptOf m).getD (r.kept.idxOf i.val) (0, 0)).1
          ((N0Full.keptOf m).getD (r.kept.idxOf i.val) (0, 0)).2 =
        arrOf seatsAllFull v.1 v.2 := by
  have hm : m < 25 := by
    have := (List.getElem?_eq_some_iff.1 hr).1
    rw [rows25] at this
    exact this
  have ha : r.kept.idxOf i.val < (N0Full.keptOf m).length := by
    rw [← keptLen_at25 hr]
    exact List.idxOf_lt_length_iff.2 hi
  have ho : (N0Full.keptOf m)[r.kept.idxOf i.val]? =
      some ((N0Full.keptOf m).getD (r.kept.idxOf i.val) (0, 0)) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha]
    rfl
  exact keptAlign_at _ _ 25 align25_full m hm _ _ ho

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.cs_at25
#print axioms VerifiableInference.Desc.First.K2Caller.lens25_says
#print axioms VerifiableInference.Desc.First.K2Caller.lens25_full
#print axioms VerifiableInference.Desc.First.K2Caller.lens25_moved
#print axioms VerifiableInference.Desc.First.K2Caller.len_at25
#print axioms VerifiableInference.Desc.First.K2Caller.keptLen_at25
#print axioms VerifiableInference.Desc.First.K2Caller.hN_at25
#print axioms VerifiableInference.Desc.First.K2Caller.olds_at25
#print axioms VerifiableInference.Desc.First.K2Caller.align25_full
#print axioms VerifiableInference.Desc.First.K2Caller.align25_moved
#print axioms VerifiableInference.Desc.First.K2Caller.keptNodup25_full
#print axioms VerifiableInference.Desc.First.K2Caller.hal_at25
