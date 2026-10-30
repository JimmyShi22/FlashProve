-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MaskTxtGPub.lean: Six statements with their proofs; all but
the first are CONDITIONAL, each on one hypothesis.

What is here. On `k4MaskTextG` (Lot/MaskTxtG.lean), the text of the member of the feed-forward
layers' own rounds (sub-protocol K4) for its segment's mask row. (1) `k4MaskTextG_isSome`: **WHETHER
THE TEXT ANSWERS IS PUBLIC**: at every run's coins, every input and every list of challenges, it
answers just where the entry lies inside the fences AND the public test
`lendsRow Bk 0 (k4Place Qp) (k4RowIn Qp)` (Honest/Small/LendsRow.lean) is true: on that side stand
the book, Qp and the entry: no coin and no input; cells, weights, tokens and look have fallen out,
since the row seated in the prover's input lends as the unseated one (`k4_lends_row`,
Law/W/LendsK4.lean). (2) `k4MaskTextG_coin`: WHERE IT ANSWERS y, y IS MEMBER NUMBER place - e OF
`rowSpentGl Bk (k.look 0) (k4Place Qp) (k4RowIn Qp).length 0` (Honest/Law/Rule/CoinBack.lean): the
owners' own field elements at the book's entries: no reader of the input, no packing and no reading
stand on that side. (3) `k4MaskTextG_none`: where the public test says false the text answers at no
entry. (4) `k4MaskTextG_alike`: TWO RUNS' COINS k AND k' AT WHICH THE LIST `rowSpentGl` … HAS THE
SAME FIRST `k4Takes` - 1 MEMBERS GIVE ONE TEXT, at all entries, whatever the two inputs and the two
lists of challenges. THE HYPOTHESIS SPEAKS OF JUST THE MEMBERS THAT THE TEXT READS: the list is the
runs that the book's entries for K4's addresses cut off THEIR OWNERS' coins, joined in the book's
order; its last member, which the text does not read, is left free (where the book lends the row the
list has `k4Takes` members; of its length where the book does not lend, nothing is said here).
`k4MaskTextG_alike_whole`: the same from the equation of the whole lists, which asks that one member
more. `k4MaskTextG_alike_runs`: the same where k and k' agree ON EACH RUN that the book's spending
entries for K4's addresses cut off its owner's coins (`sliceGl`; by `rowSpentGl_alike`,
Honest/Law/Rule/CoinBack.lean): a hypothesis on the owners' cuts, of ALL the owners that the entries
name, the last coin's among them. That the text answers at k just where it answers at k' comes of
(1), which is public, not of the hypothesis.

How. `lendRow_isSome` (Honest/Small/LendsRow.lean) and `k4_lends_row`; `mask_lookup_some` and
`k4MaskTextG_val` (Law/W/MaskTxtGIs.lean); `val_rowSpent` (Honest/Law/Rule/CoinBack.lean).

Not shown here. THAT THE PUBLIC TEST IS TRUE, OR FALSE, AT ANY BOOK FOR K4's ROW: no book for it is
written, so (3) is evaluated nowhere. THE TEST STANDS AT THE FIRST CHAIN AND READS THE BOOK's FIRST
TABLE ALONE (`Coins.look`, Honest/Frame.lean): it is false at a book that keeps the row of an owner
of K4's runs in another table, and at one that leaves out an entry for a run that a part states with
the count 0. WHERE THE TEXT ANSWERS NOTHING, A LAYING BY LOTS LAYS ZERO (`Script.ofLots`,
Honest/Thread/ScriptLots.lean): (1) says where that is; it does not take it away.
WHOSE THE MEMBERS OF `rowSpentGl` ARE: runs cut off the coins of the owners that the book's entries
for K4's addresses name: several owners'; whether two members, of one row's list or of two rows'
lists, are one coin of an owner's hangs on the book: nothing is shown. A program's walk from import
to import, which
reads import lines alone and stops unopened at Johnson/Goal/, ThirdParty/, Johnson/D/,
Johnson/Bridge/ and Cb/Bridge*, stopped at 70 modules under Johnson/Goal/, at 7 under
Johnson/Bridge/ and at 1 that begins Cb.Bridge: floors. A LAW, NOT A PART: no file that defines a
part of the proof file's description may import this one. Nothing on soundness, on completeness or
on any other property. No property is claimed.

  `k4MaskTextG_isSome`   **answers or not: a Bool of the book, Qp and the entry**
  `k4MaskTextG_coin`   **what it answers: an owner's own field element**
  `k4MaskTextG_none`   the public test false: no answer anywhere
  `k4MaskTextG_alike`, `k4MaskTextG_alike_whole`, `k4MaskTextG_alike_runs`   the same members read,
      one text
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskTxtGIs
import Johnson.Desc.ProofFile.Honest.Law.Rule.CoinBack
import Johnson.Desc.ProofFile.Honest.K4.Law.W.LendsK4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no standing table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Rt (k4Takes)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X : Type} (cells : Tr → Cells) (weights : W₀ → Weights)
  (tokens : Xi → Array Nat) (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Qp : K4Pub)

/-- **ANSWERS OR NOT IS PUBLIC**: at every run's coins, input and challenges. -/
theorem k4MaskTextG_isSome (e : ℕ) (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn)
    (mask : Bool) (row place : ℕ) :
    (Lot.k4MaskTextG X cells weights tokens look Qp e k w hd mask row place).isSome =
      (decide (mask = true ∧ row = 0 ∧ e ≤ place ∧ place + 1 < e + k4Takes Qp.P Qp.hp Qp.g) &&
        lendsRow Bk 0 (k4Place Qp) (k4RowIn Qp)) := by
  rw [← k4_lends_row (Rc := Rc) (X := X) cells weights tokens look Qp Bk,
    ← lendRow_isSome k 0 (k4Place Qp)]
  unfold Lot.k4MaskTextG
  by_cases hc : mask = true ∧ row = 0 ∧ e ≤ place ∧ place + 1 < e + k4Takes Qp.P Qp.hp Qp.g
  · rw [if_pos hc, decide_eq_true hc, Bool.true_and]
    cases hl : lendRow Bk (Bk.rowsOf 0) (k.look 0) (k4Place Qp)
        (k4Half (Rc := Rc) (X := X) cells weights tokens look Qp).parts 0 with
    | error s => rfl
    | ok c =>
      show (((spentOf _ c)[place - e]?).map Reading.gl.val).isSome = true
      rw [Option.isSome_map]
      exact mask_lookup_some cells weights tokens look Qp c hc.2.2.1 hc.2.2.2
  · rw [if_neg hc, decide_eq_false hc]
    rfl

/-- CONDITIONAL on hy. **What the text answers: an owner's own field element**, by the book's
entries. -/
theorem k4MaskTextG_coin {e : ℕ} {k : Coins Bk} {w : Local W₀ Rc Xi Tr} {hd : List Fmt.Drawn}
    {mask : Bool} {row place : ℕ} {y : Cb.Gl.E}
    (hy : Lot.k4MaskTextG X cells weights tokens look Qp e k w hd mask row place = some y) :
    (rowSpentGl Bk (k.look 0) (k4Place Qp) (k4RowIn Qp).length 0)[place - e]? = some y := by
  obtain ⟨-, c₀, h0, rfl⟩ := k4MaskTextG_val cells weights tokens look Qp hy
  rw [← val_rowSpent, List.getElem?_map, h0]
  rfl

/-- CONDITIONAL on hB. Where the public test says false the text answers at no entry. -/
theorem k4MaskTextG_none (hB : lendsRow Bk 0 (k4Place Qp) (k4RowIn Qp) = false) (e : ℕ)
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) (mask : Bool) (row place : ℕ) :
    Lot.k4MaskTextG X cells weights tokens look Qp e k w hd mask row place = none := by
  have t := k4MaskTextG_isSome (X := X) cells weights tokens look Qp e k w hd mask row place
  rw [hB, Bool.and_false] at t
  cases hx : Lot.k4MaskTextG X cells weights tokens look Qp e k w hd mask row place with
  | none => rfl
  | some y =>
    rw [hx] at t
    cases t

/-- CONDITIONAL on hk. **Two runs' coins that agree in what the text reads give one text**, whatever
the inputs and the challenges: hk equates the list's first `k4Takes` - 1 members and no more. -/
theorem k4MaskTextG_alike {e : ℕ} {k k' : Coins Bk}
    (hk : (rowSpentGl Bk (k.look 0) (k4Place Qp) (k4RowIn Qp).length 0).take
        (k4Takes Qp.P Qp.hp Qp.g - 1) =
      (rowSpentGl Bk (k'.look 0) (k4Place Qp) (k4RowIn Qp).length 0).take
        (k4Takes Qp.P Qp.hp Qp.g - 1))
    (w w' : Local W₀ Rc Xi Tr) (hd hd' : List Fmt.Drawn) (mask : Bool) (row place : ℕ) :
    Lot.k4MaskTextG X cells weights tokens look Qp e k w hd mask row place =
      Lot.k4MaskTextG X cells weights tokens look Qp e k' w' hd' mask row place := by
  have s1 := k4MaskTextG_isSome (X := X) cells weights tokens look Qp e k w hd mask row place
  have s2 := k4MaskTextG_isSome (X := X) cells weights tokens look Qp e k' w' hd' mask row place
  cases ha : Lot.k4MaskTextG X cells weights tokens look Qp e k w hd mask row place with
  | none =>
    cases hb : Lot.k4MaskTextG X cells weights tokens look Qp e k' w' hd' mask row place with
    | none => rfl
    | some y' =>
      rw [ha] at s1
      rw [hb] at s2
      have t : (some y' : Option Cb.Gl.E).isSome = (none : Option Cb.Gl.E).isSome :=
        s2.trans s1.symm
      cases t
  | some y =>
    cases hb : Lot.k4MaskTextG X cells weights tokens look Qp e k' w' hd' mask row place with
    | none =>
      rw [ha] at s1
      rw [hb] at s2
      have t : (some y : Option Cb.Gl.E).isSome = (none : Option Cb.Gl.E).isSome :=
        s1.trans s2.symm
      cases t
    | some y' =>
      obtain ⟨-, -, f1, f2⟩ := (k4MaskTextG_val cells weights tokens look Qp ha).1
      have hi : place - e < k4Takes Qp.P Qp.hp Qp.g - 1 := by omega
      have c1 := k4MaskTextG_coin cells weights tokens look Qp ha
      have c2 := k4MaskTextG_coin cells weights tokens look Qp hb
      rw [← List.getElem?_take_of_lt hi, hk, List.getElem?_take_of_lt hi, c2] at c1
      exact c1.symm

/-- CONDITIONAL on hk. The same where the whole lists are one: it asks one member more than the text
reads, the row's last coin. -/
theorem k4MaskTextG_alike_whole {e : ℕ} {k k' : Coins Bk}
    (hk : rowSpentGl Bk (k.look 0) (k4Place Qp) (k4RowIn Qp).length 0 =
      rowSpentGl Bk (k'.look 0) (k4Place Qp) (k4RowIn Qp).length 0)
    (w w' : Local W₀ Rc Xi Tr) (hd hd' : List Fmt.Drawn) (mask : Bool) (row place : ℕ) :
    Lot.k4MaskTextG X cells weights tokens look Qp e k w hd mask row place =
      Lot.k4MaskTextG X cells weights tokens look Qp e k' w' hd' mask row place :=
  k4MaskTextG_alike cells weights tokens look Qp (congrArg _ hk) w w' hd hd' mask row place

/-- CONDITIONAL on hr. The same where the two runs' coins agree on EACH RUN that the book's spending
entries for K4's addresses cut off its owner's coins. -/
theorem k4MaskTextG_alike_runs {e : ℕ} {k k' : Coins Bk}
    (hr : ∀ i, i < (k4RowIn Qp).length → ∀ a ∈ spentE Bk ⟨k4Place Qp, i⟩,
      sliceGl (k.look 0) a = sliceGl (k'.look 0) a)
    (w w' : Local W₀ Rc Xi Tr) (hd hd' : List Fmt.Drawn) (mask : Bool) (row place : ℕ) :
    Lot.k4MaskTextG X cells weights tokens look Qp e k w hd mask row place =
      Lot.k4MaskTextG X cells weights tokens look Qp e k' w' hd' mask row place :=
  k4MaskTextG_alike_whole cells weights tokens look Qp
    (rowSpentGl_alike Bk (k.look 0) (k'.look 0) (k4Place Qp) (k4RowIn Qp).length 0
      fun i _ h2 a ha => hr i (by omega) a ha) w w' hd hd' mask row place

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4MaskTextG_isSome
#print axioms ProofFile.Honest.K4.W.k4MaskTextG_coin
#print axioms ProofFile.Honest.K4.W.k4MaskTextG_none
#print axioms ProofFile.Honest.K4.W.k4MaskTextG_alike
#print axioms ProofFile.Honest.K4.W.k4MaskTextG_alike_whole
#print axioms ProofFile.Honest.K4.W.k4MaskTextG_alike_runs
