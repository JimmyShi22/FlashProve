-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/CountsAtName.lean: the first table's two counts, of oracle messages and of trees,
at every border of the first chain, at the closed letters `At.N Zp cF` (Johnson/P5J/LettersAt.lean):
in scope, wherever the value is laid, they are the entries of one closed list. So at every place at
which the closed test `stillB` accepts the two counts stand still; and at which places it accepts is
one closed fact.

Row or tool. Laws in scope, general in the border, by calls of named laws; closed facts with
negative tests. Payers for premises of other laws, which take a count at a place, or "the counts
stay at place k", at many places.

Who pays what. That the test on the written cut has accepted: `pins_of_laid`
(Johnson/Goal/Skeleton/PinsOfLaid.lean), through `told_of_laid`
(Johnson/HB/LLHARD/K6NumbersAtName.lean). The counts at the borders: `countsAre_at_toldCut`
(OwedTies.lean) and `told_at` (ToldCounts.lean). No test's accept is a premise.

What is here. PS is `First.flatPlacesOf Sound.linksFull true`, the 358 written places.
  `counts_at_name`: for k up to 358: `countsFull[k]?` is the pair of `(At.N Zp cF).msgsAt PS[k]?`
    and `(At.N Zp cF).treesAt PS[k]?`.
  `msgs_at_name`, `trees_at_name`: the two counts one by one, from an entry of the closed list:
    `countsFull[k]? = some (m, t)` gives m and t.
  `tenFull`: the 25 places of the kind K10 (14 m + 12 for m below 24, and 350), each with its number
    of oracle messages, written out. `tenB`: the test that holds such a list against the closed list
    and the written places. `ten_written`: it accepts at `tenFull`; the list has 25 entries; the
    written places have 25 of that kind. `ten_rejects`: the negative test: with the first number one
    higher it rejects.
  `msgs_at_ten`: so, for each entry (k, m) of `tenFull`: `(At.N Zp cF).msgsAt PS[k]? = m`.
  `stillB k`: a closed test: the closed list has one entry at the borders k and k + 1.
    `still_at_name`: where it accepts, for k below 358: both counts at `PS[k + 1]?` are those at
    `PS[k]?`.
  `tellersFull`: 78 places, written out. `tellers_written`: they are just the places below 358 at
    which `stillB` rejects; so it accepts at the other 280. The list was made by a program that
    reads which rows of the written cut tell something; that these 78 are the places whose
    sub-protocols tell is stated by no theorem here.
  `still_of_not_teller`: for k below 358 that is not in `tellersFull`, `stillB k` accepts.
  `still_357`, `still_at_nine`: examples for callers: place 357; and every place of the kind K9 in
    the written list of places: 75 of them. `still_rejects`: the negative test: at place 342 it
    rejects.
By evaluations in Lean's kernel (`decide +kernel`): `ten_written`, `ten_rejects`, `tellers_written`,
`still_357`, `still_at_nine`, `still_rejects`.

Limits. `countsFull` is a closed list that was made by a walk over written values; that the counts
at the closed letters are its entries holds because the verifier's entry tests compare the cut into
sub-protocols with a written one. Nothing on soundness.


-/
import Johnson.HB.LLHARD.K6NumbersAtName

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open VerifiableInference.Desc
open VerifiableInference.Desc.First (Numbers flatPlacesOf toldCut)
open VerifiableInference.Desc.K13.Law (countsFull told_at countsAre_at_toldCut)

/-- The closed list has one entry at the borders k and k + 1. -/
def stillB (k : ℕ) : Bool := decide (countsFull[k + 1]? = countsFull[k]?)

/-- The places at which the counts move. -/
def tellersFull : List ℕ :=
    [
     2, 5, 7, 16, 19, 21, 30, 33, 35, 44, 47, 49, 58, 61, 63, 72, 75, 77, 86, 89, 91, 100, 103,
     105, 114, 117, 119, 128, 131, 133, 142, 145, 147, 156, 159, 161, 170, 173, 175, 184, 187,
     189, 198, 201, 203, 212, 215, 217, 226, 229, 231, 240, 243, 245, 254, 257, 259, 268, 271,
     273, 282, 285, 287, 296, 299, 301, 310, 313, 315, 324, 327, 329, 339, 342, 344, 353, 354, 356]

set_option maxRecDepth 1000000 in
/-- **They are just the places at which the test rejects.** -/
theorem tellers_written :
    ((List.range 358).filter fun k => !stillB k) = tellersFull ∧ tellersFull.length = 78 := by
  decide +kernel

/-- At every other place below 358 the test accepts. -/
theorem still_of_not_teller {k : ℕ} (hk : k < 358) (h : k ∉ tellersFull) : stillB k = true := by
  by_contra hn
  refine h (tellers_written.1 ▸ List.mem_filter.2 ⟨List.mem_range.2 hk, ?_⟩)
  rw [Bool.not_eq_true] at hn
  rw [hn]
  rfl

set_option maxRecDepth 1000000 in
theorem still_357 : stillB 357 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- At every place of the kind K9: 75 of them. -/
theorem still_at_nine :
    (((List.range 358).filter fun k =>
        ((flatPlacesOf Sound.linksFull true)[k]?).any fun p => p.kind == .K9).all stillB) = true ∧
      ((List.range 358).filter fun k =>
        ((flatPlacesOf Sound.linksFull true)[k]?).any fun p => p.kind == .K9).length = 75 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test. -/
theorem still_rejects : stillB 342 = false := by decide +kernel

/-- The places of the kind K10, each with its number of oracle messages. -/
def tenFull : List (ℕ × ℕ) :=
    [
     (12, 7), (26, 14), (40, 22), (54, 29), (68, 37), (82, 44), (96, 52), (110, 59), (124, 67),
     (138, 74), (152, 82), (166, 89), (180, 97), (194, 104), (208, 112), (222, 119), (236, 127),
     (250, 134), (264, 142), (278, 149), (292, 157), (306, 164), (320, 172), (334, 179),
     (350, 185)]

/-- Holds such a list against the closed list and the written places. -/
def tenB (l : List (ℕ × ℕ)) : Bool :=
  l.all fun x =>
    decide (x.1 ≤ 358) && (countsFull[x.1]?).map (·.1) == some x.2 &&
      ((flatPlacesOf Sound.linksFull true)[x.1]?).any fun p => p.kind == .K10

set_option maxRecDepth 1000000 in
/-- **The 25 numbers.** -/
theorem ten_written :
    tenB tenFull = true ∧ tenFull.length = 25 ∧
      ((flatPlacesOf Sound.linksFull true).filter fun p => p.kind == .K10).length = 25 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: the first number one higher. -/
theorem ten_rejects : tenB ((12, 8) :: tenFull.drop 1) = false := by decide +kernel

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **The two counts at every border.** -/
theorem counts_at_name (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {k : ℕ} (hk : k ≤ 358) :
    countsFull[k]? = some ((At.N Zp cF).msgsAt (flatPlacesOf Sound.linksFull true)[k]?,
      (At.N Zp cF).treesAt (flatPlacesOf Sound.linksFull true)[k]?) := by
  unfold At.N
  rw [told_of_laid hZ L]
  exact told_at _ countsAre_at_toldCut hk

/-- The number of oracle messages, from an entry of the closed list. -/
theorem msgs_at_name (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {k m t : ℕ} (hk : k ≤ 358)
    (h : countsFull[k]? = some (m, t)) :
    (At.N Zp cF).msgsAt (flatPlacesOf Sound.linksFull true)[k]? = m :=
  (Prod.mk.inj (Option.some.inj (h.symm.trans (counts_at_name hZ L hk)))).1.symm

/-- The number of trees. -/
theorem trees_at_name (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {k m t : ℕ} (hk : k ≤ 358)
    (h : countsFull[k]? = some (m, t)) :
    (At.N Zp cF).treesAt (flatPlacesOf Sound.linksFull true)[k]? = t :=
  (Prod.mk.inj (Option.some.inj (h.symm.trans (counts_at_name hZ L hk)))).2.symm

/-- **The numbers of oracle messages at the 25 places of the kind K10.** -/
theorem msgs_at_ten (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {x : ℕ × ℕ} (hx : x ∈ tenFull) :
    (At.N Zp cF).msgsAt (flatPlacesOf Sound.linksFull true)[x.1]? = x.2 := by
  have c := List.all_eq_true.1 (show (tenFull.all _) = true from ten_written.1) x hx
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at c
  obtain ⟨⟨c1, c2⟩, -⟩ := c
  have a := counts_at_name hZ L (k := x.1) c1
  rw [a, Option.map_some] at c2
  exact Option.some.inj c2

/-- **Where the closed test accepts, both counts stand still.** -/
theorem still_at_name (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {k : ℕ} (hk : k < 358)
    (hs : stillB k = true) :
    (At.N Zp cF).treesAt (flatPlacesOf Sound.linksFull true)[k + 1]? =
        (At.N Zp cF).treesAt (flatPlacesOf Sound.linksFull true)[k]? ∧
      (At.N Zp cF).msgsAt (flatPlacesOf Sound.linksFull true)[k + 1]? =
        (At.N Zp cF).msgsAt (flatPlacesOf Sound.linksFull true)[k]? := by
  have a := counts_at_name hZ L (k := k) (by omega)
  have b := counts_at_name hZ L (k := k + 1) (by omega)
  have e : countsFull[k + 1]? = countsFull[k]? := of_decide_eq_true hs
  obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj (b.symm.trans (e.trans a)))
  exact ⟨e2, e1⟩

end

end P5J

#print axioms P5J.tellers_written
#print axioms P5J.still_of_not_teller
#print axioms P5J.still_357
#print axioms P5J.still_at_nine
#print axioms P5J.still_rejects
#print axioms P5J.ten_written
#print axioms P5J.ten_rejects
#print axioms P5J.counts_at_name
#print axioms P5J.msgs_at_name
#print axioms P5J.trees_at_name
#print axioms P5J.msgs_at_ten
#print axioms P5J.still_at_name
