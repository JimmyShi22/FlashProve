-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/Join.lean: CONDITIONAL: at a side whose row is the
row of the layers' own rounds (kind K4; `k4Sided`, Honest/K4/Part.lean): `ExactMember`
(Honest/Small/Field.lean: the text of `Good.exact`, Honest/Side.lean, at one member, without its
hypothesis on the opened columns; it gives that text at every `pre`: `exactAt_of_exact`) at every
member but the row's last two; and the test `Side.fits`. Definitions, statements and proofs.

  `K4Kind`, `K4Kind.sent`, `k4Kinds`   a part's sort with its public letters; how many scalars each
      of its rounds sends; the sorts of the row's parts but the last two, in order.
  `statedByB`, `statedBy_of_B`   `StatedBy` (Honest/SumLaw/Fits.lean) as a test with code; from the
      test to the sentence (the way back is not stated).
  `K4Kind.statedB`, `statedWalk`, `k4StatedB`   the test on one part's rounds; part by part over a
      list of sorts; on the rounds of a sub-protocol, cut part by part.
  `membersOf_at`   a member of a row, by its number.
  `K4Kind.Of`, `k4_kind_of`, `K4Kind.Of.moves`   the row's part number i is the frame's part of the
      sort that `k4Kinds` lists at i: so `k4Kinds` is held against `k4Sorts`; its number of moves.
  `k4Kinds_ok`     the listed shapes pass `shapeOk`, under the two tests on the plan's numbers.
  `take_eq_of_below`, `statedWalk_at`   lists; the test part by part, at one part.
  `k4_exact_at`    **one member**, under the test on its own rounds.
  `k4_exact_row`   **every member but the last two**, under the test on the sub-protocol's rounds.
  `map_fst_zip_same`, `k4Sorts_parts`, `k4Sorts_addrs`, `k4Sorts_addr`, `sims_addr`,
  `all_addr`       lists, counts and addresses of the row.
  `k4_fits`        `Side.fits`, from the place and two counts.

Kin. `membersOf_at` is, to the letter, `membersOf_mem` of the attention segments' files
(Honest/K5/Law/RowIs.lean); that file does not lie beneath this one.
`map_fst_zip_same` is, up to the letters and to where the binders stand, `map_fst_zip_eq`
(Honest/K3/RowAt.lean); `map_fst_zip'` (Johnson/Desc/K13/Honest/ClaimShape.lean) has the same end
where the second list is at least as long, and `map_zip_fst` (Honest/Law/Steps.lean) has it so under
a function of the first member. Of these three files Steps.lean alone lies beneath this one; none of
the three statements is called.
`k4_fits`: `Side.fits` is stated at other kinds' rows, among others: `lookPairs_fits`
(Honest/K3/RowAt.lean: from the place and two counts, as here; its `addrs_fit` is there what
`sims_addr` and `all_addr` are here), `k5_fits` (Honest/K5/Law/RowIs.lean), `head_fits`
(Honest/K6/Law/Row.lean), `switchRow_fits` (Honest/K2/Sim.lean), `send_side_fits`
(Honest/K14/SendingRowsLaw.lean); none of these five files lies beneath this one.
In this folder: `k4_exact_at` and `k4_exact_row` stand again at `betaMarked`, without the premise
`MSForm marked` and without the two tests on the plan's numbers, as `k4_closed_at` and
`k4_closed_row` (Law/ExactFresh/Closed.lean), and at every member of the row as `k4_closed_all`
(Law/ExactFresh/Whole.lean); these two files lie above this one, and their proofs call neither of
the two.
The short name of `K4Kind.Of.moves` stands at `RowSame.moves` (Honest/K3/Law/Keep/RowTwin.lean: two
rows that are alike have the same numbers of moves). Other kinds' files that state `ExactMember` at
every member of a row: see Law/ExactFresh/AtParts.lean's head. Sought: by statement, to the letter
and up to the bound letters, and by short name, among the theorems of the library as it lay with the
writer, and by short name among the definitions under Honest/: `membersOf_mem` and the short names
told here, and no more. That search does not see a statement whose binders stand in front of the
colon where ours stand behind it: the kin of `map_fst_zip_same` were found by a reader, by the text
of their end, those of `k4_fits` by short names that end in "_fits", under the kinds' folders of
Honest/ alone.

Limits. As in Law/ExactFresh/AtParts.lean: equations of two laws, one member at a time; THE TWO ON
`ExactMember` GATHER, OVER THE ROW, WHAT THAT FILE STATES PART BY PART, AND ARE NO LAW MORE. BY CALL
THEY GATHER THE LAWS AND NOT THAT FILE's STATEMENTS: of its nine `k4_exact_quiet` alone is called;
at a round of scalars the proof calls `scalarsPart_exact_lift` (Honest/Small/Scalars.lean), at a
masked sumcheck its own premise, at whatever values or job `K4Kind.Of` leaves: so at such a member
the two have, a second time, that file's statement at the member's number and rounds. They bear the
premise `MSForm marked` at every member, a quiet one too, at a test `marked` that is a variable: BY
THEMSELVES THEY COUNT AS NO LAW SHOWN; the form is shown at `betaMarked` alone, in
Law/ExactFresh/Paid.lean; conditional besides on the two tests on the plan's public numbers
(`k4RowEnds`, `k4TermEnds`: spent at parts 8 · 6 and 9 · 7 alone, borne at every member), and on a
test on the rounds of the side's own sub-protocol: THAT ANY DESCRIPTION's MEMBER PASSES THAT TEST IS
NOT SHOWN (what is shown, of the longer test `k4StatedAllB` on all the row's parts at `betaMarked`:
Law/ExactFresh/AtSide.lean: it accepts all rounds with the entries of the verifier's table and no
oracle message; Law/ExactFresh/BetaMarkedAtMember.lean: `k4_rounds_marked_at_member`: it accepts the
own rounds of the first chain's member at a place of K4's, in the goals' scope, where the files are
read and the blank ground returns, under `LaidAt`). THE ROW's LAST TWO PARTS ARE NOT TOUCHED: so no
term of `Good` is made here. `k4Kinds` types the row's first parts' sorts once more; `k4_kind_of`
holds it against `k4Sorts`. THAT THE LIST LACKS JUST THE ROW's LAST TWO PARTS IS SHOWN BY NO
STATEMENT HERE: `k4_exact_row` is at the members whose number is below `(k4Kinds Q).length`;
`k4Sided_length` (Law/ExactFresh/Whole.lean) counts the row as that list with two sorts more.
`ExactMember` binds the state m by "∀": the two are at every value of `m.opened` at which On holds.
`k4_fits` takes the place and the two counts as premises: that a description's member meets them is
not shown here (the count of rounds at the side that `k4Side` makes: `k4Side_count`,
Law/ExactFresh/AtSideGood.lean). What a caller still owes beside these equations, and none of it is
shown here: `fresh` at the owners of the runs that are spent (the senders of the segment's mask
row); that the book lends these runs; that no coin stands in two runs; the condition on a job that
reads what has been seen (the head of Honest/Sum.lean); `exact` at the parts that carry these coins
later.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.AtParts
import Johnson.Desc.ProofFile.Honest.Law.Steps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Model (ledNS ledNP ledNO)
open OnBytes.Model.Layer (nEndT)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Oracle)
open VerifiableInference.Desc.Part.MaskedSum (Call shapeOk)
open ProofFile.Honest.Small (ExactMember scalarsPart_exact_lift stated_scalars_of)
open ProofFile.Honest.SumLaw (StatedBy)

/-- A part's sort, with its public letters. -/
inductive K4Kind where
  /-- one round in which nothing is sent -/
  | quiet
  /-- one round that sends n scalars -/
  | lone (n : Nat)
  /-- a masked sumcheck of this shape -/
  | ms (k : Call)

/-- How many scalars each round of a part of this sort sends. -/
def K4Kind.sent : K4Kind → List Nat
  | .quiet => [0]
  | .lone n => [n]
  | .ms k => scalarsOf k

/-- **The sorts of the row's parts but the last two**, in order. -/
def k4Kinds (Q : K4Pub) : List K4Kind :=
  [.quiet] ++ (if Q.g == 0 then [.quiet, .quiet] else []) ++
  [.lone (ledNS Q.P.y.h.xl * Q.P.y.NI), .quiet, .ms (k4LevelShape Q.P.rd.muV), .quiet,
   .lone (ledNP Q.P.y.h.xl * Q.P.y.NI),
   .ms (k4TokenShape Q.P.y.h.lt 2 (ledNO Q.P.y.h.xl * Q.P.y.NI)),
   .ms (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)), .quiet,
   .ms (k4PlainShape Q.hp.lamS 2
     (2 + (1 + Q.P.y.LamM) + (Q.hp.NCL - if Q.g == 0 then 1 else 0))),
   .ms (k4LevelShape Q.P.rd.muH), .quiet, .quiet, .ms (k4LevelShape Q.P.rd.muH2), .quiet]

/-- `StatedBy` as a test with code. -/
def statedByB : List Nat → List (Fmt.DeclaredRound × List Oracle) → Bool
  | [], [] => true
  | n :: ns, r :: rs =>
    r.1.items.filter (· != .root) == List.replicate n .e && r.2.isEmpty && statedByB ns rs
  | _, _ => false

/-- From the test to the sentence. -/
theorem statedBy_of_B : ∀ (ns : List Nat) (rs : List (Fmt.DeclaredRound × List Oracle)),
    statedByB ns rs = true → StatedBy ns rs
  | [], [], _ => trivial
  | n :: ns, r :: rs, h => by
    simp only [statedByB, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
    exact ⟨h.1.1, h.1.2, statedBy_of_B ns rs h.2⟩
  | [], _ :: _, h => by simp [statedByB] at h
  | _ :: _, [], h => by simp [statedByB] at h

/-- **The test on one part's rounds.** -/
def K4Kind.statedB (marked : Call → List (Fmt.DeclaredRound × List Oracle) → Bool) (x : K4Kind)
    (rs : List (Fmt.DeclaredRound × List Oracle)) : Bool :=
  statedByB x.sent rs &&
    match x with
    | .ms k => marked k rs
    | _ => true

/-- The test part by part: each part is handed as many rounds as it sends in. -/
def statedWalk (marked : Call → List (Fmt.DeclaredRound × List Oracle) → Bool) :
    List K4Kind → List (Fmt.DeclaredRound × List Oracle) → Bool
  | [], _ => true
  | x :: xs, rs =>
    x.statedB marked (rs.take x.sent.length) && statedWalk marked xs (rs.drop x.sent.length)

/-- **The test on the rounds of a sub-protocol**: public data alone. The rounds behind those of the
row's parts but the last two are not read. -/
def k4StatedB (marked : Call → List (Fmt.DeclaredRound × List Oracle) → Bool) (Q : K4Pub)
    (rs : List (Fmt.DeclaredRound × List Oracle)) : Bool :=
  statedWalk marked (k4Kinds Q) rs

/-- **A member of a row, by its number.** General in the row. -/
theorem membersOf_at {V W X Pb : Type} : ∀ (row : List (Part V W X × Sim Pb)) (j0 : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (u : Member V W X Pb), u ∈ membersOf row j0 rs →
    ∃ t y, row[t]? = some y ∧ u = ⟨j0 + t,
      (rs.drop ((row.map (·.1.moves.length)).take t).sum).take y.1.moves.length, y.1, y.2⟩
  | [], _, _, _, h => by cases h
  | x :: l, j0, rs, u, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨0, x, rfl, rfl⟩
    · obtain ⟨t, y, hy, rfl⟩ := membersOf_at l (j0 + 1) (rs.drop x.1.moves.length) u h
      refine ⟨t + 1, y, hy, ?_⟩
      rw [List.drop_drop, List.map_cons, List.take_succ_cons, List.sum_cons,
        show j0 + 1 + t = j0 + (t + 1) by omega]

/-! ## Counts and addresses of the row -/

/-- The first members of two lists of one length, paired. -/
theorem map_fst_zip_same {α β : Type} : ∀ (A : List α) (B : List β), A.length = B.length →
    (A.zip B).map (·.1) = A
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | a :: A, b :: B, h => by
    rw [List.zip_cons_cons, List.map_cons, map_fst_zip_same A B (by simpa using h)]

/-- The row's parts do not hang on the type of what a simulator is handed. -/
theorem k4Sorts_parts (Q : K4Pub) (Pb Pb' : Type) :
    (k4Sorts (Pb := Pb) Q).map (·.part) = (k4Sorts (Pb := Pb') Q).map (·.part) := by
  unfold k4Sorts
  cases (Q.g == 0) <;> rfl

/-- Each sort's simulator names the address of its number. -/
theorem k4Sorts_addrs (Q : K4Pub) (Pb : Type) :
    (k4Sorts (Pb := Pb) Q).map (fun s n => (s.sim n).addr) =
      List.replicate (k4Sorts (Pb := Pb) Q).length (k4Addr Q) := by
  unfold k4Sorts
  cases (Q.g == 0) <;> rfl

/-- So at one sort of the row and one number. -/
theorem k4Sorts_addr (Q : K4Pub) (Pb : Type) (s : K4Sort Pb) (hs : s ∈ k4Sorts (Pb := Pb) Q)
    (n : Nat) : (s.sim n).addr = k4Addr Q n := by
  have h : (fun n => (s.sim n).addr) ∈ (k4Sorts (Pb := Pb) Q).map (fun s n => (s.sim n).addr) :=
    List.mem_map_of_mem hs
  rw [k4Sorts_addrs] at h
  exact congrFun (List.eq_of_mem_replicate h) n

/-- The simulators of a list of sorts, numbered from k on: number i names the address k + i. -/
theorem sims_addr (Q : K4Pub) {Pb : Type} : ∀ (l : List (K4Sort Pb)) (k i : Nat) (x : Sim Pb),
    (∀ s ∈ l, ∀ n, (s.sim n).addr = k4Addr Q n) →
    ((l.zipIdx k).map fun s => s.1.sim s.2)[i]? = some x → x.addr = k4Addr Q (k + i)
  | [], _, _, _, _, h => by simp at h
  | s :: l, k, 0, x, hl, h => by
    rw [List.zipIdx_cons, List.map_cons, List.getElem?_cons_zero] at h
    obtain rfl := Option.some.inj h
    exact hl s List.mem_cons_self k
  | s :: l, k, i + 1, x, hl, h => by
    rw [List.zipIdx_cons, List.map_cons, List.getElem?_cons_succ] at h
    rw [sims_addr Q l (k + 1) i x (fun t ht => hl t (List.mem_cons_of_mem _ ht)) h,
      Nat.add_assoc, Nat.add_comm 1 i]

/-- A row in which simulator number i names part number k + i of a place passes the first clause of
`Side.fits`. -/
theorem all_addr {α Pb : Type} (P : VerifiableInference.Desc.Place) :
    ∀ (A : List α) (B : List (Sim Pb)) (k : Nat),
    (∀ (i : Nat) (x : Sim Pb), B[i]? = some x → x.addr = ⟨P, k + i⟩) →
    ((A.zip B).zipIdx k).all (fun s => s.1.2.addr == ⟨P, s.2⟩) = true
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | a :: A, b :: B, k, h => by
    rw [List.zip_cons_cons, List.zipIdx_cons, List.all_cons, Bool.and_eq_true]
    refine ⟨beq_iff_eq.2 (h 0 b rfl), all_addr P A B (k + 1) fun i x hx => ?_⟩
    rw [h (i + 1) x (by rw [List.getElem?_cons_succ]; exact hx), Nat.add_assoc,
      Nat.add_comm 1 i]

/-! ## The row's parts by their sorts -/

section
variable {W₀ Rc Xi Tr X : Type} (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights)
  (tokens : Xi → Array Nat) (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard)

/-- **A part with its simulator is of a sort, at the number i**: the frame's part of that sort at
the sort's letters, under the row's way of seating, beside the frame's simulator at the address of
i. -/
def K4Kind.Of (x : K4Kind) (i : Nat)
    (y : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X × Sim Xi) : Prop :=
  match x with
  | .quiet => y = (k4Lift Q cells weights tokens look k4Quiet, quietSim (k4Addr Q i))
  | .lone n => ∃ f, y = (k4Lift Q cells weights tokens look (k4Scalars Q n f i),
      scalarsSim (k4Addr Q i) n)
  | .ms k => ∃ J : SumJob K4In Unit, J.shape = k ∧ ∃ name endName,
      y = (k4Lift Q cells weights tokens look (sumPart name endName J), sumSim (k4Addr Q i) k)

/-- **The row's part number i is of the sort that `k4Kinds` lists at i.** -/
theorem k4_kind_of {i : Nat} {x : K4Kind} (hx : (k4Kinds Q)[i]? = some x) :
    ∃ y, (k4Sided (Rc := Rc) (X := X) Q cells weights tokens look)[i]? = some y ∧
      x.Of Q cells weights tokens look i y := by
  unfold k4Kinds at hx
  unfold k4Sided k4Row k4RowIn k4Sims k4Sorts k4Shapes
  by_cases h : (Q.g == 0) = true
  · simp only [h, ↓reduceIte] at hx ⊢
    exact match i, hx with
    | 0, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 1, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 2, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 3, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl⟩
    | 4, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 5, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 6, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 7, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl⟩
    | 8, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 9, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 10, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 11, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 12, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 13, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 14, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 15, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 16, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | n + 17, hx => by simp at hx
  · rw [Bool.not_eq_true] at h
    simp only [h, Bool.false_eq_true, ↓reduceIte] at hx ⊢
    exact match i, hx with
    | 0, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 1, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl⟩
    | 2, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 3, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 4, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 5, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl⟩
    | 6, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 7, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 8, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 9, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 10, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 11, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 12, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | 13, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, _, rfl, _, _, rfl⟩
    | 14, hx => by
      obtain rfl := Option.some.inj hx
      exact ⟨_, rfl, rfl⟩
    | n + 15, hx => by simp at hx

/-- A part of a sort has as many moves as the sort sends in rounds. -/
theorem K4Kind.Of.moves {x : K4Kind} {i : Nat}
    {y : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X × Sim Xi}
    (h : x.Of Q cells weights tokens look i y) : y.1.moves.length = x.sent.length := by
  cases x with
  | quiet =>
    obtain rfl : y = _ := h
    rfl
  | lone n =>
    obtain ⟨f, rfl⟩ : ∃ f, y = _ := h
    rfl
  | ms k =>
    obtain ⟨J, rfl, name, endName, rfl⟩ : ∃ J : SumJob K4In Unit, J.shape = k ∧ ∃ name endName,
      y = _ := h
    show ((sumPart name endName J).moves.map _).length = (scalarsOf J.shape).length
    rw [List.length_map, SumLaw.moves_length, ← SumLaw.scalarsOf_length]

end

/-- **The shapes that `k4Kinds` lists pass `shapeOk`**, under the two tests on the plan's
numbers. -/
theorem k4Kinds_ok (Q : K4Pub) (hn : k4RowEnds Q = true) (hn' : k4TermEnds Q = true) {i : Nat}
    {k : Call} (hx : (k4Kinds Q)[i]? = some (.ms k)) : shapeOk k = true := by
  unfold k4Kinds at hx
  by_cases h : (Q.g == 0) = true
  · simp only [h, ↓reduceIte] at hx
    exact match i, hx with
    | 0, hx => by cases Option.some.inj hx
    | 1, hx => by cases Option.some.inj hx
    | 2, hx => by cases Option.some.inj hx
    | 3, hx => by cases Option.some.inj hx
    | 4, hx => by cases Option.some.inj hx
    | 5, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeOk_level _
    | 6, hx => by cases Option.some.inj hx
    | 7, hx => by cases Option.some.inj hx
    | 8, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeOk_token _ (by decide) (of_decide_eq_true hn)
    | 9, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeOk_token _ (Nat.le_refl 1) (of_decide_eq_true hn')
    | 10, hx => by cases Option.some.inj hx
    | 11, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeOk_plain _ (by decide) (by omega)
    | 12, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeOk_level _
    | 13, hx => by cases Option.some.inj hx
    | 14, hx => by cases Option.some.inj hx
    | 15, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeOk_level _
    | 16, hx => by cases Option.some.inj hx
    | n + 17, hx => by simp at hx
  · rw [Bool.not_eq_true] at h
    simp only [h, Bool.false_eq_true, ↓reduceIte] at hx
    exact match i, hx with
    | 0, hx => by cases Option.some.inj hx
    | 1, hx => by cases Option.some.inj hx
    | 2, hx => by cases Option.some.inj hx
    | 3, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeOk_level _
    | 4, hx => by cases Option.some.inj hx
    | 5, hx => by cases Option.some.inj hx
    | 6, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeOk_token _ (by decide) (of_decide_eq_true hn)
    | 7, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeOk_token _ (Nat.le_refl 1) (of_decide_eq_true hn')
    | 8, hx => by cases Option.some.inj hx
    | 9, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeOk_plain _ (by decide) (by omega)
    | 10, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeOk_level _
    | 11, hx => by cases Option.some.inj hx
    | 12, hx => by cases Option.some.inj hx
    | 13, hx => by
      obtain rfl := K4Kind.ms.inj (Option.some.inj hx)
      exact shapeOk_level _
    | 14, hx => by cases Option.some.inj hx
    | n + 15, hx => by simp at hx

/-- Two lists of numbers that agree below t have one beginning of length t. -/
theorem take_eq_of_below {A B : List Nat} (t : Nat) (h : ∀ i, i < t → A[i]? = B[i]?) :
    A.take t = B.take t :=
  List.ext_getElem? fun i => by
    rw [List.getElem?_take, List.getElem?_take]
    split
    · exact h i ‹_›
    · rfl

/-- The test part by part, at part number t. -/
theorem statedWalk_at (marked : Call → List (Fmt.DeclaredRound × List Oracle) → Bool) :
    ∀ (xs : List K4Kind) (rs : List (Fmt.DeclaredRound × List Oracle)) (t : Nat) (x : K4Kind),
    statedWalk marked xs rs = true → xs[t]? = some x →
    x.statedB marked
      ((rs.drop ((xs.map (·.sent.length)).take t).sum).take x.sent.length) = true
  | [], _, _, _, _, h => by simp at h
  | y :: xs, rs, 0, x, hw, h => by
    rw [List.getElem?_cons_zero] at h
    obtain rfl := Option.some.inj h
    simp only [statedWalk, Bool.and_eq_true] at hw
    exact hw.1
  | y :: xs, rs, t + 1, x, hw, h => by
    rw [List.getElem?_cons_succ] at h
    simp only [statedWalk, Bool.and_eq_true] at hw
    have e := statedWalk_at marked xs (rs.drop y.sent.length) t x hw.2 h
    rw [List.drop_drop] at e
    rw [List.map_cons, List.take_succ_cons, List.sum_cons]
    exact e

variable {S Cl W₀ Rc Xi Tr X : Type}
  (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Xi)
  (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (chain firstTree : Nat)
  (On : (u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) → CsAll u.part.carries →
    Mid (Local W₀ Rc Xi Tr) X → Before → Prop)
  (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
  (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
  (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard)
  {marked : Call → List (Fmt.DeclaredRound × List Oracle) → Bool}

/-- **One member of K4's side, but the last two**, under the test on its own rounds. CONDITIONAL:
see the head. -/
theorem k4_exact_at (hMS : MSForm marked) (hr : σ.row = k4Sided Q cells weights tokens look)
    (hn : k4RowEnds Q = true) (hn' : k4TermEnds Q = true)
    {u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi} (hu : u ∈ σ.members) {x : K4Kind}
    (hx : (k4Kinds Q)[u.number]? = some x) (h0 : x.statedB marked u.rounds = true) :
    ExactMember φ σ chain firstTree On bud u := by
  obtain ⟨t, y, hy, rfl⟩ := membersOf_at σ.row 0 _ u hu
  rw [hr] at hy
  have hx' : (k4Kinds Q)[t]? = some x := by
    rw [← Nat.zero_add t]
    exact hx
  obtain ⟨y', hy', hof⟩ := k4_kind_of (Rc := Rc) (X := X) Q cells weights tokens look hx'
  obtain rfl : y' = y := Option.some.inj (hy'.symm.trans hy)
  unfold K4Kind.statedB at h0
  rw [Bool.and_eq_true] at h0
  simp only [Nat.zero_add]
  cases x with
  | quiet =>
    obtain rfl : y' = _ := hof
    exact k4_exact_quiet φ σ chain firstTree On bud Q cells weights tokens look t _
      (statedBy_of_B _ _ h0.1)
  | lone n =>
    obtain ⟨f, rfl⟩ : ∃ f, y' = _ := hof
    exact scalarsPart_exact_lift φ σ chain firstTree On bud t _ _ (k4Addr Q t) _ _ _ _ _ _
      (stated_scalars_of (statedBy_of_B _ _ h0.1))
  | ms k =>
    obtain ⟨J, rfl, name, endName, rfl⟩ : ∃ J : SumJob K4In Unit, J.shape = k ∧ ∃ name endName,
      y' = _ := hof
    exact hMS _ _ _ _ _ _ Unit K4In Unit φ σ chain firstTree On bud (fun _ => ())
      (k4Wit Q cells weights tokens look) (fun _ => ()) (fun x _ => x) (fun _ _ => rfl)
      (fun _ => rfl) name endName J t _ (k4Addr Q t) (k4Kinds_ok Q hn hn' hx')
      (statedBy_of_B _ _ h0.1) h0.2

/-- **Every member of K4's side but the last two**, under the test on the rounds of the side's own
sub-protocol. CONDITIONAL: see the head. -/
theorem k4_exact_row (hMS : MSForm marked) (hr : σ.row = k4Sided Q cells weights tokens look)
    (hn : k4RowEnds Q = true) (hn' : k4TermEnds Q = true)
    (h0 : k4StatedB marked Q (σ.block.rounds.zip σ.block.oracles) = true) :
    ∀ u ∈ σ.members, u.number < (k4Kinds Q).length →
      ExactMember φ σ chain firstTree On bud u := by
  intro u hu hlt
  have hx := List.getElem?_eq_getElem hlt
  refine k4_exact_at φ σ chain firstTree On bud Q cells weights tokens look hMS hr hn hn' hu hx ?_
  generalize (k4Kinds Q)[u.number] = x at hx
  obtain ⟨t, y, hy, rfl⟩ := membersOf_at σ.row 0 _ u hu
  have hx' : (k4Kinds Q)[t]? = some x := by
    rw [← Nat.zero_add t]
    exact hx
  have e := statedWalk_at marked (k4Kinds Q) _ t x h0 hx'
  rw [hr] at hy
  obtain ⟨y', hy', hof⟩ := k4_kind_of (Rc := Rc) (X := X) Q cells weights tokens look hx'
  obtain rfl : y' = y := Option.some.inj (hy'.symm.trans hy)
  have hp : ((k4Sided (Rc := Rc) (X := X) Q cells weights tokens look).map
      (·.1.moves.length)).take t = ((k4Kinds Q).map (·.sent.length)).take t := by
    refine take_eq_of_below t fun i hi => ?_
    have hi' : i < (k4Kinds Q).length :=
      Nat.lt_trans hi (List.getElem?_eq_some_iff.1 hx').1
    have hxi := List.getElem?_eq_getElem hi'
    obtain ⟨yi, hyi, hofi⟩ := k4_kind_of (Rc := Rc) (X := X) Q cells weights tokens look hxi
    rw [List.getElem?_map, List.getElem?_map, hyi, hxi]
    exact congrArg some (hofi.moves Q cells weights tokens look)
  show x.statedB marked (((σ.block.rounds.zip σ.block.oracles).drop
    ((σ.row.map (·.1.moves.length)).take t).sum).take y'.1.moves.length) = true
  rw [hr, hp, hof.moves Q cells weights tokens look]
  exact e

/-- **`Side.fits` at K4's row**: the sub-protocol stands at the row's place, has as many rounds as
the row has moves, and as many lists of oracle messages. Two of the three clauses of `Side.fits` are
premises here; what is added is the clause on the simulators' addresses. -/
theorem k4_fits (hr : σ.row = k4Sided Q cells weights tokens look)
    (hp : σ.block.place = k4Place Q)
    (hl : σ.block.rounds.length = ((k4RowIn Q).map (·.moves.length)).sum)
    (ho : σ.block.oracles.length = σ.block.rounds.length) : σ.fits = true := by
  have hlen : (k4Row Q cells weights tokens look :
      List (Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)).length =
      (k4Sims (Xi := Xi) Q).length := by
    have e := congrArg List.length (k4Sorts_parts Q Unit Xi)
    rw [List.length_map, List.length_map] at e
    unfold k4Row k4RowIn k4Sims
    rw [List.length_map, List.length_map, List.length_zipIdx, List.length_map,
      List.length_zipIdx, e]
  unfold Side.fits
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, beq_iff_eq.2 ho⟩
  · rw [hr, hp]
    refine all_addr (k4Place Q) _ _ 0 fun i x hx => ?_
    exact sims_addr Q (k4Sorts (Pb := Xi) Q) 0 i x (k4Sorts_addr Q Xi) hx
  · rw [beq_iff_eq, hl]
    show (σ.row.map (·.1)).foldl (fun n p => n + p.moves.length) 0 = _
    rw [hr]
    unfold k4Sided
    rw [map_fst_zip_same _ _ hlen, foldl_moves, Nat.zero_add]
    unfold k4Row
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
    exact List.length_map ..

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.K4Kind
#print axioms ProofFile.Honest.K4.K4Kind.sent
#print axioms ProofFile.Honest.K4.k4Kinds
#print axioms ProofFile.Honest.K4.statedByB
#print axioms ProofFile.Honest.K4.statedBy_of_B
#print axioms ProofFile.Honest.K4.K4Kind.statedB
#print axioms ProofFile.Honest.K4.statedWalk
#print axioms ProofFile.Honest.K4.k4StatedB
#print axioms ProofFile.Honest.K4.membersOf_at
#print axioms ProofFile.Honest.K4.map_fst_zip_same
#print axioms ProofFile.Honest.K4.k4Sorts_parts
#print axioms ProofFile.Honest.K4.k4Sorts_addrs
#print axioms ProofFile.Honest.K4.k4Sorts_addr
#print axioms ProofFile.Honest.K4.sims_addr
#print axioms ProofFile.Honest.K4.all_addr
#print axioms ProofFile.Honest.K4.K4Kind.Of
#print axioms ProofFile.Honest.K4.k4_kind_of
#print axioms ProofFile.Honest.K4.K4Kind.Of.moves
#print axioms ProofFile.Honest.K4.k4Kinds_ok
#print axioms ProofFile.Honest.K4.take_eq_of_below
#print axioms ProofFile.Honest.K4.statedWalk_at
#print axioms ProofFile.Honest.K4.k4_exact_at
#print axioms ProofFile.Honest.K4.k4_exact_row
#print axioms ProofFile.Honest.K4.k4_fits
