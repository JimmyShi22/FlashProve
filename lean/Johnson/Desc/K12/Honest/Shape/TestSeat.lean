-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestSeat.lean: where the members of the group under test and the first
fold's mask are all the parts of one tree: one test with code on the shape in front of a proximity
test and on the plan (`seat1B`), and its law: what the form's half of the stages' invariant
(`FormInv`, Johnson/Prover/Link/FormInv.lean) asks of statement, book and plan on that tree. In
Lean: `seat1B` is a Bool, and `seat1_of_B` proves that where it is true, the text of four fields of
`FormInv` holds: `step`, `seat` (at the group's members, not at a layout's), `log` and `decl`.
`formInv_of_shape` (TestReturnsOne.lean in this folder) derives these four fields from it.
Definitions and theorems. General in the stage, the declared rounds, the structure inside the test,
the message id and the index tN.

In the list: a statement (`Statement`, OnBytes/Iop/Ground.lean) has oracle messages (`oracles`) and
groups (`groups`); a group (`Group`) lists its members: numbers of oracle messages. A book
(`TreeBook`, same file) has the trees sent so far (`trees`) and, for each oracle message, its tree
and its place among that tree's parts (`place`). A tree (`Tree`) has a shape, a `number`, its parts
(the numbers of the oracle messages in it), the flag `oneList` (it is opened at one list of
positions only) and `lists`: at how many lists it has been opened. Its width is `mainWidth` +
`maskWidth` of its shape. The shape c (`CoreSh`, Johnson/Desc/Ground/Shape/Core.lean) is what
`coreSh` reads of a statement, a book and a count of roots, with every field element left out;
`stSh` and `treeSh` read the shapes of a statement (`StSh`) and of a tree (`TreeSh`). t (`T12`,
Johnson/Desc/K12/Join.lean) is the structure inside a proximity test: among its fields are `st`,
`book`, `roots` and the number `g` of the group under test. The plan is here cur and l. cur is a
stage (`Fmt.M1.Stage`, Fmt/M1Types.lean): `cur.C` is its main code, with codewords of length
`2 ^ cur.C.a`. l (`Laid`, Johnson/Desc/K12/Frame.lean) is a list of declared rounds
(`Fmt.DeclaredRound`, Decl/Declared.lean), each with its oracle messages. The cut is
`(l.drop (1 + cur.k)).take 2` without the oracle messages. Where l is the list of rounds from the
stage cur on and cur is not the last stage, these are the two rounds that the proximity test's frame
(`stagesFrom`, Frame.lean) deals to the code switch after the fold of cur.

  `seat1_of_B`: under the two hypotheses below: `t.st` has as many oracle messages as `t.book.place`
    has entries ("in step"); and there is a tree tr such that `ReadSeat`
    (Johnson/Prover/Link/ReadSeat.lean) holds at `t.st`, `t.book`, the members of G, id, tN and tr;
    `tr.shape.logN` is `cur.C.a`; and, if the cut is two rounds dS and dC, then `dC.opens` has one
    element, whose `tree` is `tr.number`, whose `a` is `cur.C.a` and whose `W` is the width of tr.
    `ReadSeat` is a structure of hypotheses: tr is at index tN of the book's trees; the members and
    then id have the places (tN, 0), (tN, 1) and so on; they are all the parts of tr, in this order;
    tr has been opened at no list; `sharesOk` (Johnson/Prover/Link/ReadFront.lean) passes at the
    statement and tr; each of them is a message of the statement
  `seat1B cur l c g id tN`: a definition: a Bool. The statement's shape has as many oracle messages
    as the book's `place` has entries; group number g is there (G) and the tree at index tN is there
    (T); the parts of T are the members of G and then id; T is opened at no list; for every q, the
    book's `place` has (tN, q) for the message that is element number q of that list; `sharesS`
    passes at T; all of them are messages of the statement; `T.shape.logN` is `cur.C.a`; `declB`
    passes at T. The count of roots in c is not read
  `declB cur l T`: a definition: a Bool. The cut has two rounds; the second declares one opened tree
    (`opens` has one element); that element's `tree` is `T.number`, its `a` is `cur.C.a`, and its
    `W` is the width of T
  `sharesS a T`: a definition: a Bool: the guard on shares of a reading, at a tree's shape. a is a
    statement's shape. For each part of T that is a message in a and states an out-of-domain sample
    (`shape.answers` is not 0), take the list of the groups that it belongs to. `sharesOk` of
    Johnson/Desc/Ground/Shape/More.lean tests these lists: all are equal, and each has one group at
    most if `T.oneList` is set
  `sharesS_eq`: at the shapes of a statement S and a tree tr, `sharesS` is the test `sharesOk S tr`
    of ReadFront.lean. No hypothesis

By what. `sharesS_eq` rewrites by `orc_get` (Core.lean); the rest holds by unfolding. `seat1_of_B`
takes the Bool apart clause by clause. `grp_get`, `tree_get`, `place_get` and `orc_size` (Core.lean)
carry the clauses from the shape back to `t.st` and `t.book`, and `sharesS_eq` carries the guard on
shares.

Hypotheses of `seat1_of_B`. h: `seat1B` is true at cur, l, the shape of `t.st`, `t.book` and
`t.roots`, at `t.g`, id and tN. hG: G is group number `t.g` of `t.st`.

Limits.
- Only one direction is proved: the converse is not shown.
- `seat1B` is a test on a shape and on the plan. It reads no value. By type that is so for field
  elements only: a number in a shape can be made of a value (the limits of Core.lean).
- A group whose members are in several trees does not pass.
- Nothing here says that the test is true at any shape.
- cur, l and id are free parameters. Nothing here says that id is the number in `t.mask`, that cur
  is a stage of a plan, or that l is a plan's list of rounds from that stage on.
- Of the cut's second round `declB` reads `opens` only: not the round's name, nor its stored trees.
  Of the one element of `opens` it reads `tree`, `a` and `W`: not `stored`, nor whose tree it is.
  The comment at the field `decl` of `FormInv` calls that round the plan's round "CS".
- The last clause of the conclusion of `seat1_of_B` is an implication, word for word the field
  `decl`: it is vacuous where the cut does not have two rounds. `declB` is false there; the
  conclusion does not say that the cut has two rounds.
- "mask" is the library's name for a message and for rows: nothing is said of what a mask does.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestDoor
import Johnson.Prover.Link.ReadSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open Johnson.Prover.Link (ReadSeat)

/-- The guard on shares, at a tree's shape: `sharesOk` (Johnson/Desc/Ground/Shape/More.lean) at the
flag `T.oneList` and at this list: for each part of T that is a message in the statement's shape a
and whose `shape.answers` is not 0, the groups that it belongs to. A part that is no message in a is
passed over. -/
def sharesS (a : StSh) (T : TreeSh) : Bool :=
  VerifiableInference.Desc.Ground.Sh.sharesOk
    (T.parts.filterMap fun o =>
      (a.oracles[o]?).bind fun x => if x.shape.answers == 0 then none else some x.groups)
    T.oneList

theorem sharesS_eq (S : Statement) (tr : Tree) :
    sharesS (stSh S) (treeSh tr) = Johnson.Prover.Link.sharesOk S tr := by
  have e : ((treeSh tr).parts.filterMap fun o =>
      ((stSh S).oracles[o]?).bind fun x =>
        if x.shape.answers == 0 then none else some x.groups) =
      tr.parts.toList.filterMap fun o =>
        (S.oracles[o]?).bind fun x => if x.shape.answers == 0 then none else some x.groups := by
    show tr.parts.toList.filterMap _ = _
    congr 1
    funext o
    rw [orc_get]
    cases S.oracles[o]? <;> rfl
  unfold sharesS
  rw [e]
  rfl

/-- The one tree that the cut's second round declares is this tree, in number, length and width. The
cut: `(l.drop (1 + cur.k)).take 2`. l: the declared rounds that the proximity test's frame
(`stagesFrom`, Johnson/Desc/K12/Frame.lean) deals to the stages. False where the cut does not have
two rounds, or the second does not declare just one opened tree. -/
def declB (cur : Fmt.M1.Stage) (l : Laid) (T : TreeSh) : Bool :=
  match ((l.drop (1 + cur.k)).take 2).map (·.1) with
  | [_, dC] =>
    match dC.opens with
    | [o] => o.1.tree == T.number && o.1.a == cur.C.a &&
        o.1.W == T.shape.mainWidth + T.shape.maskWidth
    | _ => false
  | _ => false

/-- **The members and the mask are all the parts of one tree**, with code. g: the group under test.
id: the first fold's mask. tN: the tree's index in the book's list `trees`. False where the shape
lacks group number g or a tree at tN. The default 0 of `getD` is not reached: q is below the list's
length. -/
def seat1B (cur : Fmt.M1.Stage) (l : Laid) (c : CoreSh) (g id tN : Nat) : Bool :=
  c.st.oracles.length == c.book.place.length &&
    match c.st.groups[g]?, c.book.trees[tN]? with
    | some G, some T =>
      T.parts == G.members ++ [id] && T.lists == 0 &&
        ((List.range (G.members ++ [id]).length).all fun q =>
          c.book.place[(G.members ++ [id]).getD q 0]? == some (tN, q)) &&
        sharesS c.st T && ((G.members ++ [id]).all fun o => decide (o < c.st.oracles.length)) &&
        T.shape.logN == cur.C.a && declB cur l T
    | _, _ => false

/-- **What the test gives**: the text of the fields `step`, `seat`, `log` and `decl` of `FormInv`
(Johnson/Prover/Link/FormInv.lean), `seat` at the members of G. -/
theorem seat1_of_B {cur : Fmt.M1.Stage} {l : Laid} {t : T12} {G : Group} {id tN : Nat}
    (h : seat1B cur l (coreSh ⟨t.st, t.book, t.roots⟩) t.g id tN = true)
    (hG : t.st.groups[t.g]? = some G) :
    t.st.oracles.size = t.book.place.size ∧ ∃ tr : Tree,
      ReadSeat t.st t.book G.members.toList id tN tr ∧ tr.shape.logN = cur.C.a ∧
      ∀ dS dC, ((l.drop (1 + cur.k)).take 2).map (·.1) = [dS, dC] →
        ∃ o, dC.opens = [o] ∧ o.1.tree = tr.number ∧ o.1.a = cur.C.a ∧
          o.1.W = tr.shape.mainWidth + tr.shape.maskWidth := by
  unfold seat1B at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h0, h⟩ := h
  have e0 : t.st.oracles.size = t.book.place.size := by
    have k : (stSh t.st).oracles.length = (bookSh t.book).place.length := eq_of_beq h0
    rw [orc_size] at k
    simpa [bookSh] using k
  have hg' : (coreSh ⟨t.st, t.book, t.roots⟩).st.groups[t.g]? = some (grpSh G) := by
    show (stSh t.st).groups[t.g]? = _
    rw [grp_get, hG]
    rfl
  rw [hg'] at h
  cases hT : t.book.trees[tN]? with
  | none =>
    have k : (coreSh ⟨t.st, t.book, t.roots⟩).book.trees[tN]? = none := by
      show (bookSh t.book).trees[tN]? = _
      rw [tree_get, hT]
      rfl
    rw [k] at h
    cases h
  | some tr =>
    have k : (coreSh ⟨t.st, t.book, t.roots⟩).book.trees[tN]? = some (treeSh tr) := by
      show (bookSh t.book).trees[tN]? = _
      rw [tree_get, hT]
      rfl
    rw [k] at h
    dsimp only at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := h
    have b1 : tr.parts.toList = G.members.toList ++ [id] := eq_of_beq a1
    refine ⟨e0, tr, ⟨hT, ?_, ?_, eq_of_beq a2, ?_, ?_⟩, eq_of_beq a6, ?_⟩
    · intro q hq
      have k1 := eq_of_beq (List.all_eq_true.1 a3 q (List.mem_range.2 hq))
      have k2 : (bookSh t.book).place[(G.members.toList ++ [id]).getD q 0]? = some (tN, q) := k1
      rw [place_get, List.getD_eq_getElem _ _ hq] at k2
      exact k2
    · rw [← b1]
    · rw [← sharesS_eq]
      exact a4
    · intro o ho
      have k1 : o < (stSh t.st).oracles.length := of_decide_eq_true (List.all_eq_true.1 a5 o ho)
      rwa [orc_size] at k1
    · intro dS dC hcut
      unfold declB at a7
      rw [hcut] at a7
      dsimp only at a7
      split at a7
      · rename_i o ho
        simp only [Bool.and_eq_true, beq_iff_eq] at a7
        exact ⟨o, ho, a7.1.1, a7.1.2, a7.2⟩
      · cases a7

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.sharesS_eq
#print axioms ProofFile.Honest.Sh.seat1_of_B
#print axioms ProofFile.Honest.Sh.sharesS
#print axioms ProofFile.Honest.Sh.declB
#print axioms ProofFile.Honest.Sh.seat1B
