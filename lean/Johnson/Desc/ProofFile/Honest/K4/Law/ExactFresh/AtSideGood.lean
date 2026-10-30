-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/AtSideGood.lean: at the side that `k4Side` makes
(Honest/K4/Part.lean): ON LISTS: its sub-protocol has as many rounds as K4's row has moves; and,
CONDITIONAL, `Good` (Honest/Side.lean) at that side as one term, AT A := B := THE SENTENCE THAT
NEVER HOLDS (False). Statements and proofs.

  `lens_of_ok`, `table_length`, `sided_moves`, `rowIn_moves`   counts of rounds and moves.
  `k4Side_count`   the sub-protocol of the side that is made has as many rounds as the row has
      moves.
  `k4_good_side`   **`Good` as one term at that side, at A := B := False**, at every pre.

Limits. As in Law/ExactFresh/Whole.lean's head, of which nothing is taken back: `k4_good_side` IS NO
LAW MORE THAN `k4_fits`, `k4_closed_all`, `k4_fresh_all`: plays and acc hold vacuously; fresh is an
identity that holds of any part of which nothing is spent, AND IS NOT fresh AT THE OWNERS OF THE
RUNS THAT K4 SPENDS; what the term adds is exact. pre IS A FREE LETTER, of which nothing is asked,
tied to no description and to no player: of the term's fields exact alone reads it, in its premise
that `m.opened` is what front holds for the reads of pre: WHERE THAT PREMISE FAILS THE TERM's exact
ASKS NOTHING; at each pre it says no more than `k4_closed_all`. At a state whose `opened` is `none`,
as the players that hand no columns have it, that premise holds only where front lacks a column for
one of these reads (Law/ExactFresh/Whole.lean's head). WHAT IS NEW: the test on the rounds, the row,
the place and the count of rounds are no premises any more: they follow from `k4Side … = some σ`
(`k4Side_is`, Law/ExactFresh/AtSide.lean; the count: `k4Side_count`, here). OF THE ONE TEST ON THE
ROUNDS ITS REST STAYS, WHICH `k4Side` DOES NOT ASK: that no round has an oracle message: it is taken
here from the description's own test on a sub-protocol's shape (`Block.shaped`,
Johnson/Desc/Block.lean): ONE Bool ON PUBLIC DATA. And a premise on the book. fo, tokv: ANY PAIR AT
WHICH `k4Fits` ACCEPTS; TIED TO NO RUN; exact READS NEITHER THAT TEST NOR THE COUNT OF ROUNDS IN
FRONT: of the three tests of `k4Side` the one on the entries alone is spent. Under lighter premises
(a sub-protocol's entries are the table's; it passes the test on its shape) THE COUNT OF ROUNDS AND
THE TEST ON THE ROUNDS stand in Law/ExactFresh/AtSeat.lean: NO TERM OF `Good` AND NO STATEMENT ON
exact STANDS THERE. WHERE A DESCRIPTION's MEMBER AS IT IS WRAPPED BEARS ANOTHER ENTRY THAN THE
VERIFIER's TABLE, `k4Side` YIELDS NONE, AND NOTHING IS SAID. THAT `k4Side` MAKES A SIDE AT ANY
DESCRIPTION's LIST, THAT ITS SUB-PROTOCOL THEN PASSES THE TEST ON ITS SHAPE, AND THAT ANY
DESCRIPTION's BOOK MEETS THE PREMISE ON THE BOOK, IS NOT SHOWN HERE (by the head of
Honest/Small/Field.lean that test does not follow from `ProverCoinCounts.clauses`: it has to be evaluated at the
book).

Kin. `k4_good_side` is `k4_good_seated` (Law/ExactFresh/Whole.lean) at the side that `k4Side` makes:
see Limits; other kinds' terms of `Good`: that file's head. `table_length`: the library's
`k4_rounds_length` (Honest/K13/ReachAtFlat.lean, of other writers) has the number of the table's
rows in the plan's letters, where here it stands as a sum over the listed sorts. The like of
`table_length` at the output head's table: `head_rounds_length`, `headSent_cut`
(Honest/K6/Law/Rounds.lean, of other writers; not beneath this file). `sided_moves` is
`K4Kind.Of.moves` (Law/ExactFresh/Join.lean) over the row. ReachAtFlat.lean does not lie beneath
this file. Sought: by statement, to the letter and up to the bound letters, and by short name, among
the theorems of the library as it lay with the writer, and by short name among the definitions under
Honest/: no hit. The search by statement does not see a statement that has a binder in front of the
colon where ours has it behind, or the other way round. The like at the output head's table was
found by a reader.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.AtSide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.ExactFresh
open OnBytes.Desc.First.K4 (Rd)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Place)
open ProofFile.Honest.Small (noneSpent)
open ProofFile.Honest.SumLaw (betaMarked)

theorem lens_of_ok : ∀ {ks : List K4Kind} {Ls : List (List Rd)},
    List.Forall₂ (fun x L => x.statedB betaMarked (canon L) = true ∧ L.length = x.sent.length)
      ks Ls → Ls.map (·.length) = ks.map (·.sent.length)
  | _, _, .nil => rfl
  | _, _, .cons h t => by rw [List.map_cons, List.map_cons, h.2, lens_of_ok t]

/-- The verifier's table has as many rows as the listed sorts send in rounds. -/
theorem table_length (Q : K4Pub) :
    (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g).length =
      ((k4KindsAll Q).map (·.sent.length)).sum := by
  rw [← k4Rows_flatten, List.length_flatten, lens_of_ok (k4Rows_ok Q)]

section
variable {S Cl W₀ Rc Xi Tr X : Type}

/-- Part by part the row has as many moves as its sort sends in rounds. -/
theorem sided_moves (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights)
    (tokens : Xi → Array Nat) (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard) :
    (k4Sided (Rc := Rc) (X := X) Q cells weights tokens look).map (·.1.moves.length) =
      (k4KindsAll Q).map (·.sent.length) := by
  refine List.ext_getElem? fun i => ?_
  rw [List.getElem?_map, List.getElem?_map]
  cases hx : (k4KindsAll Q)[i]? with
  | none =>
    have hn : (k4Sided (Rc := Rc) (X := X) Q cells weights tokens look)[i]? = none := by
      rw [List.getElem?_eq_none_iff] at hx ⊢
      rw [k4Sided_length]
      exact hx
    rw [hn]
    rfl
  | some x =>
    obtain ⟨y, hy, hof⟩ := k4_kind_all (Rc := Rc) (X := X) Q cells weights tokens look hx
    rw [hy]
    exact congrArg some (hof.moves Q cells weights tokens look)

/-- The row at the small input has these counts too: seating a part keeps its moves' number. -/
theorem rowIn_moves (Q : K4Pub) :
    (k4RowIn Q).map (·.moves.length) = (k4KindsAll Q).map (·.sent.length) := by
  have e := sided_moves (W₀ := Weights) (Rc := Unit) (Xi := Array Nat) (Tr := Cells) (X := Unit) Q
    id id id fun _ => default
  have hlen : (k4Row (W₀ := Weights) (Rc := Unit) (Xi := Array Nat) (Tr := Cells) (X := Unit) Q
      id id id fun _ => default).length = (k4Sims (Xi := Array Nat) Q).length := by
    have e' := congrArg List.length (k4Sorts_parts Q Unit (Array Nat))
    rw [List.length_map, List.length_map] at e'
    unfold k4Row k4RowIn k4Sims
    rw [List.length_map, List.length_map, List.length_zipIdx, List.length_map,
      List.length_zipIdx, e']
  have e3 : (k4Sided (W₀ := Weights) (Rc := Unit) (Xi := Array Nat) (Tr := Cells) (X := Unit) Q
      id id id fun _ => default).map (·.1.moves.length) =
      ((k4Sided (W₀ := Weights) (Rc := Unit) (Xi := Array Nat) (Tr := Cells) (X := Unit) Q
        id id id fun _ => default).map (·.1)).map (·.moves.length) := by
    rw [List.map_map]
    rfl
  rw [← e, e3]
  unfold k4Sided
  rw [map_fst_zip_same _ _ hlen]
  unfold k4Row
  rw [List.map_map]
  exact List.map_congr_left fun p _ => (List.length_map ..).symm

/-- **The sub-protocol of the side that `k4Side` makes has as many rounds as K4's row has
moves.** -/
theorem k4Side_count {bs : List (Block S Cl)} {Q : K4Pub} {cells : Tr → Cells}
    {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : List Fmt.Drawn → OnBytes.Model.Forest.Heard} {fo : OnBytes.Model.Forest.Heard}
    {tokv : Array Nat} {σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (h : k4Side bs Q cells weights tokens look fo tokv = some σ) :
    σ.block.rounds.length = ((k4RowIn Q).map (·.moves.length)).sum := by
  have e := congrArg List.length (k4Side_is h).2
  unfold OnBytes.Desc.First.K4.entries at e
  rw [List.length_map, List.length_map] at e
  rw [e, table_length, rowIn_moves]

/-- **`Good` at the side that `k4Side` makes, as one term, AT A := B := THE SENTENCE THAT NEVER
HOLDS (False): SO plays AND acc HOLD VACUOUSLY. fresh IS AN IDENTITY THAT HOLDS OF ANY PART OF WHICH
NOTHING IS SPENT: IT IS NOT fresh AT THE OWNERS OF THE RUNS THAT K4 SPENDS. WHAT THE TERM ADDS IS
exact. NO LAW MORE THAN `k4_fits`, `k4_closed_all`, `k4_fresh_all`: A CALLER AT ANOTHER A TAKES
THESE.** On and bud are True.
pre: A FREE LETTER, OF WHICH NOTHING IS ASKED, TIED TO NO DESCRIPTION AND TO NO PLAYER. exact alone
reads it, in its premise that `m.opened` is what front holds for the reads of pre: WHERE THAT
PREMISE FAILS THE TERM's exact ASKS NOTHING. The proof drops the premise: at each pre the term's
exact says no more than `k4_closed_all`.
CONDITIONAL: `k4Side` makes the side (fo, tokv: ANY PAIR AT WHICH
`k4Fits` ACCEPTS; TIED TO NO RUN; exact READS NEITHER THAT TEST NOR THE COUNT OF ROUNDS IN FRONT: of
the three tests of `k4Side` the one on the entries alone is spent); its sub-protocol passes the
description's own test on its shape; no entry of the book by which a part spends names a member as
owner. -/
theorem k4_good_side (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Xi) (Bk : ProverCoinCounts)
    (ord : List Place) (chain firstTree : Nat) {bs : List (Block S Cl)} {Q : K4Pub}
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : List Fmt.Drawn → OnBytes.Model.Forest.Heard} {fo : OnBytes.Model.Forest.Heard}
    {tokv : Array Nat} {σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (h : k4Side bs Q cells weights tokens look fo tokv = some σ)
    (hs : σ.block.shaped = true)
    (hb : ∀ u ∈ σ.members, noneSpent Bk ⟨σ.block.place, u.number⟩ = true) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (fun _ _ _ _ => True) (fun _ _ _ => True) :=
  k4_good_seated pre φ σ Bk ord chain firstTree Q cells weights tokens look (k4Side_is h).1
    (k4Side_count h)
    (oracles_of_shaped σ.block hs fun _ hr =>
      entries_roots Q _ ((k4Side_is h).2 ▸ List.mem_map_of_mem hr)).1
    (k4Side_stated_shaped h hs) hb

end

end ProofFile.Honest.K4.ExactFresh

#print axioms ProofFile.Honest.K4.ExactFresh.lens_of_ok
#print axioms ProofFile.Honest.K4.ExactFresh.table_length
#print axioms ProofFile.Honest.K4.ExactFresh.sided_moves
#print axioms ProofFile.Honest.K4.ExactFresh.rowIn_moves
#print axioms ProofFile.Honest.K4.ExactFresh.k4Side_count
#print axioms ProofFile.Honest.K4.ExactFresh.k4_good_side
