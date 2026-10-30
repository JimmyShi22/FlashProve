-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestView.lean: a test with code, `viewFromB`, for the view's form from
a stage of a proximity test on (`ViewFrom`, Johnson/Desc/K12/Honest/Shape/TestReturns.lean), and the
theorem `viewFrom_of_B`: where the test passes, `ViewFrom` holds. So the hypothesis of
`stages_returns` (TestReturns.lean) on the view follows from one Bool on the stages, the declared
rounds from this stage on, the rounds and the groups of columns. Definitions and theorems, general
in all of these.

In the list: a stage is a `Fmt.M1.Stage`; cur is the present stage. l (`Laid`,
Johnson/Desc/K12/Frame.lean) lists the declared rounds (`Fmt.DeclaredRound`) from this stage on, each
with its oracle messages, which nothing here reads. By the cuts of `stagesFrom` (Frame.lean) a stage
that is not the last has the 1 + `cur.k` rounds of its fold and then the two rounds of its switch;
the last stage has two rounds. The round of the positions is the second of the switch's two, rC
below. A declared round names the trees that it opens (`opens`); a tree's width is the field `W` of
its shape. R lists the rounds as a view has them (`Fmt.RoundView`): each has values (`vals`) and what was
drawn (`drawn`), among that the positions (`poss`). A column is a list of 64-bit words. A group
(`List (ℕ × List UInt64)`) is a list of columns, each with its position. gs lists the groups; the
dealt group of a stage is the one that gs has for it. `Fmt.listOf` (Fmt/Rules6.lean) makes of a list
of numbers the strictly increasing list of its elements; the list of some drawn positions is
`Fmt.listOf` of them.

  `viewFrom_of_B`: where `viewFromB rest cur l R gs` passes, `ViewFrom rest cur l R gs` holds. No
    other hypothesis
  `viewFromB rest cur l R gs`: a definition: the test; rest lists the stages after cur. At the last
    stage (rest is empty): R is two rounds and gs is one group; `roundsFit`
    (Johnson/Desc/Block.lean) passes at the declared rounds of l and R; the group's positions are
    the list of the positions that the second round drew. At every other stage: after its first 1 +
    `cur.k` rounds R has two more, rS and rC, and gs has a first group g; `roundsFit` passes at the
    first 1 + `cur.k` declared rounds of l and these first rounds, and at the next two declared
    rounds and [rS, rC]; the values of rC are one answer; every tree that these two declared rounds
    open has the width `widthOf` of the two; `groupB` passes at a := `(sgOf cur).C.a` (`sgOf`,
    Johnson/Desc/K12/Law/ChainOf.lean), that width, the positions that rC drew and g; and the test
    passes from the next stage on, at l without its first `cur.k` + 3 declared rounds and at what is
    left of R and gs
  `groupB a W poss g`: a definition: a test on one group: the positions of g are the list of the
    positions poss, each reduced modulo 2 ^ a; and every column of g has W words
  `group_of_B`: where `groupB a W poss g` passes, g is that list of positions, each with `colOf W g`
    of it, and `colOf W g x` has W words at every x
  `colOf W g x`: a definition: a column as a function of the position, taken from a group g: the
    column that a look-up in g finds at position x; where it finds none, W zero words
  `find_self`, `group_is`: in a group whose positions are strictly increasing the look-up at an
    element's position finds that element; so the group is its list of positions, each with `colOf`
    of it
  `widthOf cut`: a definition: cut is a list of declared rounds: the width of the first tree that
    they open; 0 if they open none. `viewFromB` calls it at the switch's two declared rounds

What it reads. Of what a round shows: the items' sorts and their number (`roundsFit`,
Johnson/Desc/Block.lean), and that the round of the positions shows one answer: no shown value. Of
what a round draws: how many elements, positions and matrix entries; the drawn positions themselves
(that each is in its round's range; and the dealt group is held against their list); that each drawn
matrix entry is -1, 0 or 1; and what `drawsMarkedNonzeroHaveNonzeroWords` asks of the elements that are drawn as non-zero. Of a
column: its position and its length: no word of it.

By what. `viewFrom_of_B` goes by recursion on the list of stages and unfolds `viewFromB`. At a stage
that is not the last it fills the existential variables of `ViewFrom` with the first 1 + `cur.k`
rounds of R, rS, rC, what is left of R and gs, the answer of rC and, as the column function, `colOf`
at the tested width and the dealt group. `group_of_B` gives the clause on the group and, with the
test on the trees' widths, the clause on the widths. It calls `group_is` and `Fmt.listOf_incr`
(Fmt/Rules6Laws.lean: the list is strictly increasing). `group_is` calls `find_self`, which is an
induction on the group.

Limits.
- One way: the test's "true" gives `ViewFrom`; the converse is not shown.
- Nothing is evaluated here. Johnson/Desc/K12/Honest/Shape/TestReturnsOneToy.lean evaluates
  `viewFromB` at one small made-up place: it passes once (`view1`) and fails at four changes of the
  rounds or the groups (`no1`, `no2`).
- At the last stage the test does not read cur: a caller can pass anything there. It asks no width
  of a column there, and it does not reduce the drawn positions. `ViewFrom` is the same in all
  three.
- The zero words of `colOf` are a default. `ViewFrom` asks for a column function at every position;
  at a position that is not in the group's list it asks only the length.
- Where the two declared rounds open no tree, `widthOf` is 0: the clause on the trees' widths is
  then vacuous, and `groupB` asks columns of no word.
- The clause `decide (1 + cur.k ≤ R.length)` of `viewFromB` adds nothing: that `R.drop (1 + cur.k)`
  has a first element gives it already, and the proof does not use it.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestReturns
import Fmt.Rules6Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)

/-! ## 1 A dealt group as a function of the position -/

/-- The column at position x, taken from a group g: that of the first element of g at x; W zero
words if there is none. -/
def colOf (W : ℕ) (g : List (ℕ × List UInt64)) (x : ℕ) : List UInt64 :=
  ((g.find? (·.1 == x)).map (·.2)).getD (List.replicate W 0)

/-- Where the positions are strictly increasing, the look-up at an element's position finds that
element. -/
theorem find_self : ∀ (g : List (ℕ × List UInt64)), (g.map (·.1)).Pairwise (· < ·) →
    ∀ y ∈ g, g.find? (·.1 == y.1) = some y
  | [], _, _, hy => by cases hy
  | z :: g, hp, y, hy => by
    rw [List.map_cons, List.pairwise_cons] at hp
    rcases List.mem_cons.1 hy with rfl | hy'
    · exact List.find?_cons_of_pos (by simp)
    · have hlt : z.1 < y.1 := hp.1 y.1 (List.mem_map.2 ⟨y, hy', rfl⟩)
      rw [List.find?_cons_of_neg (by simp; omega)]
      exact find_self g hp.2 y hy'

/-- So the group is its list of positions, each with the column that the look-up finds. -/
theorem group_is (W : ℕ) (g : List (ℕ × List UInt64)) (hp : (g.map (·.1)).Pairwise (· < ·)) :
    g = (g.map (·.1)).map fun x => (x, colOf W g x) := by
  rw [List.map_map]
  refine (List.map_id g).symm.trans (List.map_congr_left fun y hy => ?_)
  show y = (y.1, colOf W g y.1)
  unfold colOf
  rw [find_self g hp y hy]
  rfl

/-- A test on one group: its positions are the list (`Fmt.listOf`) of the drawn positions, each
reduced modulo 2 ^ a; each column has the width W. -/
def groupB (a W : ℕ) (poss : List ℕ) (g : List (ℕ × List UInt64)) : Bool :=
  g.map (·.1) == Fmt.listOf (poss.map (· % 2 ^ a)) && g.all (·.2.length == W)

theorem group_of_B {a W : ℕ} {poss : List ℕ} {g : List (ℕ × List UInt64)}
    (h : groupB a W poss g = true) :
    g = (Fmt.listOf (poss.map (· % 2 ^ a))).map (fun x => (x, colOf W g x)) ∧
      ∀ x, (colOf W g x).length = W := by
  unfold groupB at h
  rw [Bool.and_eq_true] at h
  have h1 : g.map (·.1) = Fmt.listOf (poss.map (· % 2 ^ a)) := eq_of_beq h.1
  refine ⟨?_, fun x => ?_⟩
  · have := group_is W g (h1 ▸ Fmt.listOf_incr _)
    rwa [h1] at this
  · unfold colOf
    cases hf : g.find? (·.1 == x) with
    | none => exact List.length_replicate
    | some y => exact eq_of_beq (List.all_eq_true.1 h.2 y (List.mem_of_find?_eq_some hf))

/-! ## 2 The test -/

/-- The width that these declared rounds declare for the first tree that they open; 0 if none. -/
def widthOf (cut : List Fmt.DeclaredRound) : ℕ := (((cut.flatMap (·.opens)).head?).map (·.1.W)).getD 0

/-- The view's form from a stage on (`ViewFrom`), as a test with code. The arguments are those of
`ViewFrom`: the stages after the present one, the present stage (not read at the last stage), the
declared rounds from this stage on, the rounds, the groups of columns. The clause
`decide (1 + cur.k ≤ R.length)` adds nothing to the match above it. -/
def viewFromB : List Fmt.M1.Stage → Fmt.M1.Stage → Laid → List Fmt.RoundView →
    List (List (ℕ × List UInt64)) → Bool
  | [], _, l, R, gs =>
    match R, gs with
    | [_, rB], [g] => roundsFit (l.map (·.1)) R && g.map (·.1) == Fmt.listOf rB.drawn.poss
    | _, _ => false
  | next :: rest, cur, l, R, gs =>
    match R.drop (1 + cur.k), gs with
    | rS :: rC :: R', g :: gs' =>
      decide (1 + cur.k ≤ R.length) &&
      roundsFit ((l.take (1 + cur.k)).map (·.1)) (R.take (1 + cur.k)) &&
      roundsFit (((l.drop (1 + cur.k)).take 2).map (·.1)) [rS, rC] &&
      (match rC.vals with
        | [.answer _] => true
        | _ => false) &&
      ((((l.drop (1 + cur.k)).take 2).map (·.1)).all fun d => d.opens.all fun o =>
        o.1.W == widthOf (((l.drop (1 + cur.k)).take 2).map (·.1))) &&
      groupB (sgOf cur).C.a (widthOf (((l.drop (1 + cur.k)).take 2).map (·.1))) rC.drawn.poss g &&
      viewFromB rest next (l.drop (cur.k + 3)) R' gs'
    | _, _ => false

/-- **Where the test passes, the view has the form.** -/
theorem viewFrom_of_B : ∀ (rest : List Fmt.M1.Stage) (cur : Fmt.M1.Stage) (l : Laid)
    (R : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
    viewFromB rest cur l R gs = true → ViewFrom rest cur l R gs
  | [], cur, l, R, gs, h => by
    unfold viewFromB at h
    split at h
    · rename_i rL rB g
      rw [Bool.and_eq_true] at h
      exact ⟨rL, rB, g, rfl, rfl, h.1, eq_of_beq h.2⟩
    · cases h
  | next :: rest, cur, l, R, gs, h => by
    unfold viewFromB at h
    split at h
    · rename_i rS rC R' g gs' hR
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨_, fitF⟩, fitS⟩, hans⟩, hw⟩, hg⟩, hrest⟩ := h
      obtain ⟨eg, hlen⟩ := group_of_B hg
      obtain ⟨a, ha⟩ : ∃ a, rC.vals = [.answer a] := by
        split at hans
        · exact ⟨_, by assumption⟩
        · cases hans
      refine ⟨R.take (1 + cur.k), rS, rC, R', gs', a,
        colOf (widthOf (((l.drop (1 + cur.k)).take 2).map (·.1))) g, ?_, ?_, fitF, fitS, ha, ?_,
        viewFrom_of_B rest next _ R' gs' hrest⟩
      · rw [← hR, List.take_append_drop]
      · exact congrArg (· :: gs') eg
      · intro d hd o ho x
        rw [hlen x]
        exact (eq_of_beq (List.all_eq_true.1 (List.all_eq_true.1 hw d hd) o ho)).symm
    · cases h

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.find_self
#print axioms ProofFile.Honest.Sh.group_is
#print axioms ProofFile.Honest.Sh.group_of_B
#print axioms ProofFile.Honest.Sh.viewFrom_of_B
#print axioms ProofFile.Honest.Sh.colOf
#print axioms ProofFile.Honest.Sh.groupB
#print axioms ProofFile.Honest.Sh.widthOf
#print axioms ProofFile.Honest.Sh.viewFromB
