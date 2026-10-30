-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/DoorReturns.lean

What it proves. At the proximity test on G_u of the shared chain the state function doorUF
(DoorsByShape.lean) can be had off its fall-back. Of the eight blocks in front of that test "LOC"
alone reads columns, and these are the committed table's, a stored table: a function of the input
and of the round seen. With the reader colsLoc, which lays these columns as the frame lays them in a
view, the fold over the eight returns at every front of the declared form, and doorUF's state is
what the seat's way in makes of the state behind the eight (doorUF_returns). What is wanted besides
so that this state is the one at which a verifier's fold over the same eight stands is gathered in
one structure of three ties (DoorTies), under which the fold at the verifier's first state and view
returns a state with the same way in (doorUF_at_ties).

Names.
  colsLoc, colsLoc_form, colsLoc_more   the reader; its columns have the keys, positions and widths
      that the library's groupsOf asks; it reads of the rounds seen the one of number 3.
  noInputs   a value of the type Inputs, which the law that is called takes and the part of it that
      is used does not read.
  doorUF_returns   the first theorem.
  foldBlocks_more   a fold that returns with nothing left over returns the same state with more
      behind.
  DoorTies, doorUF_at_ties   the three ties; the second theorem.
  reads_skip, fill_stored, cols_of_reads   the third tie on two texts: the frame's readsOf and
      fillCols against colsLoc.

By what. eight_steps_hold, blocks_rounds (Johnson/Desc/K14/Honest/ChainSteps.lean);
Block.step_ok, foldBlocks_cons_ok (Johnson/Desc/RunLaws.lean).

Limits.
- It moves no count. It does not give SaysAt (AsksWhole.lean): off the fall-back SaysAt is a
  sentence on the prover's values, which nothing shows.
- doorUF_returns has three premises that read the input: hW, hkey, hbeta. Who shows them at every
  input in range is not said here. hbeta is on the key's values: no seed has the factor 0.
- The premises on the rounds seen (hfr, f1 … f8) are on one front. That every front which a play
  reaches meets them is the frame's to show, not shown here.
- In doorUF_at_ties no verifier is named: s₂ and v are free, and the three ties bind them to the
  prover's side. It is the debt, named; none of the three ties is shown at a run here but for the
  form of the third (cols_of_reads).
- With colsLoc the state on entry is made of the stored table's columns: a simulator's state
  function has to make the same of what it is given.
- The test on G_u alone. At the test on G_omega the blocks in front read columns of trees that parts
  of the run have sent with their random values: this road does not go there.
- It stands over files that are not in the library yet, as MarksBehind.lean does.
- Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.DoorsByShape
import Johnson.Desc.K14.Honest.ChainSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (OracleNotice TableKey TreeLay)
open VerifiableInference.Desc (Block OpenedColumn Place foldBlocks roundsFit groupsOf Block.step_ok
  foldBlocks_cons_ok)
open VerifiableInference.Desc.K12 (T12 Seat.enter)
open VerifiableInference.Desc.Own (keyFits allZero)
open VerifiableInference.Desc.K1 (planOkOwn)
open Desc.K14 (P14 St blocks first readsAtLoc)
open Desc.K14.Law (parU parO)
open Desc.K14.Honest (PlanFacts Inputs eight_steps_hold blocks_rounds ReadsNone)
open ProofFile.Honest (Read readsOf fillCols Table)

variable {W X : Type}

/-! ## 1 The reader -/

/-- **The reader of the columns that "LOC" reads.** stored: the stored tables' columns as words, by
the statement's item and the position (in the frame: Prover.storedWords at the input's w₀ and rc).
rs: the shared chain's rounds as seen; "LOC" is its round number 3, from 0. In the text of the
frame's readsOf for a stored read; the empty column where stored has none. -/
def colsLoc (Q : P14) (stored : ℕ → ℕ → Option (List UInt64)) (rs : List Fmt.RoundView) : List OpenedColumn :=
  match rs[3]? with
  | some R =>
    (Fmt.listOf ((Fmt.partOf (readsAtLoc Q.S.fold Q.item) R.drawn.poss).map
      (· % 2 ^ (readsAtLoc Q.S.fold Q.item).sh.a))).map fun x =>
        (Fmt.storedKey (readsAtLoc Q.S.fold Q.item).item, x,
          (stored (readsAtLoc Q.S.fold Q.item).item x).getD [])
  | none => []

/-- The reader's columns have the keys, positions and widths that groupsOf asks at "LOC"'s round. -/
theorem colsLoc_form (Q : P14) (stored : ℕ → ℕ → Option (List UInt64)) (rs : List Fmt.RoundView)
    (R : Fmt.RoundView) (hR : rs[3]? = some R) (e : Fmt.Entry) (ft : ℕ)
    (hW : ∀ x < 2 ^ (readsAtLoc Q.S.fold Q.item).sh.a,
      ((stored Q.item x).getD []).length = Q.S.fold.index.rows) :
    (colsLoc Q stored rs).map (fun c => (c.1, c.2.1, c.2.2.length)) =
      (groupsOf ft [{ entry := e, stored := [readsAtLoc Q.S.fold Q.item] }] [R.drawn]).flatMap
        id := by
  unfold colsLoc
  rw [hR]
  show _ = ([(Fmt.listOf ((Fmt.partOf (readsAtLoc Q.S.fold Q.item) R.drawn.poss).map
    (· % 2 ^ (readsAtLoc Q.S.fold Q.item).sh.a))).map fun x =>
      (Fmt.storedKey (readsAtLoc Q.S.fold Q.item).item, x, (readsAtLoc Q.S.fold Q.item).sh.W)] ++
        [] ++ []).flatMap id
  simp only [List.append_nil, List.flatMap_cons, List.flatMap_nil, id, List.map_map]
  refine List.map_congr_left fun x hx => ?_
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ _).1 hx)
  show (_, _, ((stored Q.item _).getD []).length) = (_, _, Q.S.fold.index.rows)
  rw [hW _ (Nat.mod_lt _ (Nat.two_pow_pos _))]

/-- The reader reads of the rounds seen the one of number 3 alone. -/
theorem colsLoc_more (Q : P14) (stored : ℕ → ℕ → Option (List UInt64)) (rs rest : List Fmt.RoundView)
    (h : 3 < rs.length) : colsLoc Q stored (rs ++ rest) = colsLoc Q stored rs := by
  unfold colsLoc
  rw [List.getElem?_append_left h]

/-! ## 2 The fold returns -/

/-- A value of the type Inputs: all 0. -/
noncomputable def noInputs : Inputs :=
  ⟨fun _ _ _ => 0, fun _ _ => 0, ⟨fun _ _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩,
    ⟨fun _ _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩,
    ⟨fun _ _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩,
    ⟨fun _ _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩⟩

/-- **At the test on G_u the fold in front returns, and doorUF is off its fall-back**, with the
reader colsLoc. The premises, sorted.
Public, on the plan: hP, hBU, hBO, hb.
By make: nothing is asked of the columns' keys and positions: colsLoc lays them as groupsOf does.
On the frame: hfr, f1, f2, f4, f5, f7, f8: what the part has seen of the shared chain are eight
rounds of the declared form: the challenges' form, and the form (not the values) of the items that
the two sendings and "SPLIT" show.
On the input's form: hW: at each position of the committed table's tree the stored column has as
many words as the table has rows (every position that colsLoc lays is cut to that range; a column
that stored does not have is laid as the empty one, which hW refuses where the table has a row);
hkey: the key's sizes fit.
On values, one: hbeta: no seed of the key has the factor 0.
Nothing is asked of what the prover's tables hold or of the values shown: the law that is called is
true of every prover. So this gives no SaysAt: off the fall-back SaysAt is a sentence on the
prover's values. That d8 is the state through which the verifier's fold passes is not said here. -/
theorem doorUF_returns (Q : P14) (sentU : Array OracleNotice) (layO : TreeLay)
    (hP : PlanFacts Q.par Q.codes sentU layO) (hBU : planOkOwn (parU Q sentU) = true)
    (hBO : planOkOwn (parO Q) = true) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (key : W → TableKey)
    (stored : W → ℕ → ℕ → Option (List UInt64)) (w : W) (fr : Front X)
    (R1 R2a R2b R4 R5a R5b R7 R8 : Fmt.RoundView)
    (hfr : fr.seen.rounds = [R1, R2a, R2b, R4, R5a, R5b, R7, R8])
    (f1 : roundsFit b1.rounds [R1] = true) (f2 : roundsFit b2.rounds [R2a, R2b] = true)
    (f4 : roundsFit b4.rounds [R4] = true) (f5 : roundsFit b5.rounds [R5a, R5b] = true)
    (f7 : roundsFit b7.rounds [R7] = true) (f8 : roundsFit b8.rounds [R8] = true)
    (hW : ∀ x < 2 ^ (readsAtLoc Q.S.fold Q.item).sh.a,
      ((stored w Q.item x).getD []).length = Q.S.fold.index.rows)
    (hkey : keyFits (key w) Q.par.S.fold.index = true)
    (hbeta : ((key w).seeds.all (!allZero ·.beta)) = true) :
    ∃ d8 : St,
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first Q.codes (key w)) fr.seen.rounds
        (colsLoc Q (stored w) fr.seen.rounds) = .ok (d8, [], []) ∧
      doorUF Q sentU [b1, b2, b3, b4, b5, b6, b7, b8] key
          (fun w fr => colsLoc Q (stored w) fr.seen.rounds) w fr =
        { st := d8.st, book := d8.book, roots := d8.roots, g := d8.loc.gU, pass := .nothing
          mask := d8.loc.firstMask } := by
  have e4 := (blocks_rounds Q sentU b1 b2 b3 b4 b5 b6 b7 b8 hb hP.goes).2.2.2.1
  have hcs : (colsLoc Q (stored w) fr.seen.rounds).map (fun x => (x.1, x.2.1, x.2.2.length)) =
      (groupsOf 0 b4.rounds [R4.drawn]).flatMap id := by
    rw [e4]
    exact colsLoc_form Q (stored w) _ R4 (by rw [hfr]; rfl) _ 0 hW
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, -, -, -, -, -, -, -, -, hF, -⟩ :=
    eight_steps_hold Q sentU layO hP hBU hBO b1 b2 b3 b4 b5 b6 b7 b8 hb (key w) hkey hbeta
      R1 R2a R2b R4 R5a R5b R7 R8 (colsLoc Q (stored w) fr.seen.rounds) [] [] 0 f1 f2 f4 f5 f7 f8
      hcs noInputs
  rw [List.append_nil, List.append_nil, ← hfr] at hF
  refine ⟨d8, hF, ?_⟩
  unfold doorUF doorOf
  simp only [hF]
  rfl

/-! ## 3 The three ties -/

/-- A fold that returns with nothing left over returns the same state with more rounds and more
columns behind, and leaves these. -/
theorem foldBlocks_more (ft : ℕ) : ∀ (bs : List (Block St Unit)) (s d : St) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn), foldBlocks ft bs s rs cols = .ok (d, [], []) →
    ∀ (rest : List Fmt.RoundView) (more : List OpenedColumn),
      foldBlocks ft bs s (rs ++ rest) (cols ++ more) = .ok (d, rest, more)
  | [], s, d, rs, cols, h, rest, more => by
    have e : (s, rs, cols) = (d, ([] : List Fmt.RoundView), ([] : List OpenedColumn)) := Except.ok.inj h
    obtain rfl : s = d := (Prod.mk.inj e).1
    obtain rfl : rs = [] := (Prod.mk.inj (Prod.mk.inj e).2).1
    obtain rfl : cols = [] := (Prod.mk.inj (Prod.mk.inj e).2).2
    rfl
  | b :: l, s, d, rs, cols, h, rest, more => by
    obtain ⟨hl, s', k, hs, hf⟩ := foldBlocks_cons_ok.1 h
    obtain ⟨a1, a2, a3, a4⟩ := Block.step_ok.1 hs
    have hlen : b.rounds.length ≤ rs.length := by
      rw [List.length_take] at hl
      omega
    have hk : k ≤ cols.length := by
      have := congrArg List.length a2
      rw [List.length_map, List.length_take, ← a4] at this
      omega
    refine foldBlocks_cons_ok.2 ⟨?_, s', k, ?_, ?_⟩
    · rw [List.take_append_of_le_length hlen]
      exact hl
    · rw [List.take_append_of_le_length hlen]
      refine Block.step_ok.2 ⟨a1, ?_, ?_, a4⟩
      · rw [List.take_append_of_le_length hk]
        exact a2
      · rw [List.take_append_of_le_length hk]
        exact a3
    · rw [List.drop_append_of_le_length hlen, List.drop_append_of_le_length hk]
      exact foldBlocks_more ft l s' d _ _ hf rest more

/-- **Three ties that "the state on entry is the verifier's" asks at the test on G_u, in one
structure.** Not the whole of what is asked: besides, the fold has to go (doorUF_returns' premises
on form and input, or a premise that it returns), and the ties have to hold at every stand that a
play reaches: here they are on one front and one view. s₂: the state at which the verifier's fold
over the shared chain stands in front of the eight. v: the shared chain's view. Three ties between
the prover's side (its input w, what its part has seen, fr) and the verifier's (s₂, v). None is on a
value of the prover's tables.
first: (α) a premise on the prover's key: the frame compares the key that the shared parts are given
with what the verifier's start reads of the instance by no type (ProofFile/Honest/Frame.lean).
rounds: (β) what the part has seen are the view's first rounds: the frame's to show.
cols: (γ) the reader's columns are the view's first columns: cols_of_reads below gives it from the
frame's own text for a view's columns. -/
structure DoorTies (Q : P14) (key : W → TableKey) (stored : W → ℕ → ℕ → Option (List UInt64))
    (w : W) (fr : Front X) (s₂ : St) (v : Fmt.View) : Prop where
  first : s₂ = first Q.codes (key w)
  rounds : ∃ rest, v.rounds = fr.seen.rounds ++ rest
  cols : ∃ more, v.opened = colsLoc Q (stored w) fr.seen.rounds ++ more

/-- **Under the three ties the fold over the eight, at s₂ and at the view's rounds and columns,
returns a state of which the seat's way in makes doorUF's state.** What is left over of rounds and
columns is handed on. No verifier is named here: s₂ and v are free, and the ties bind them to the
prover's side: this is doorUF_returns and foldBlocks_more. For the blocks behind the eight the
library's foldBlocks_append_ok (Johnson/Desc/RunLaws.lean) cuts a longer fold at this state. The
other premises are doorUF_returns' own. No SaysAt follows. -/
theorem doorUF_at_ties (Q : P14) (sentU : Array OracleNotice) (layO : TreeLay)
    (hP : PlanFacts Q.par Q.codes sentU layO) (hBU : planOkOwn (parU Q sentU) = true)
    (hBO : planOkOwn (parO Q) = true) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (key : W → TableKey)
    (stored : W → ℕ → ℕ → Option (List UInt64)) (w : W) (fr : Front X)
    (R1 R2a R2b R4 R5a R5b R7 R8 : Fmt.RoundView)
    (hfr : fr.seen.rounds = [R1, R2a, R2b, R4, R5a, R5b, R7, R8])
    (f1 : roundsFit b1.rounds [R1] = true) (f2 : roundsFit b2.rounds [R2a, R2b] = true)
    (f4 : roundsFit b4.rounds [R4] = true) (f5 : roundsFit b5.rounds [R5a, R5b] = true)
    (f7 : roundsFit b7.rounds [R7] = true) (f8 : roundsFit b8.rounds [R8] = true)
    (hW : ∀ x < 2 ^ (readsAtLoc Q.S.fold Q.item).sh.a,
      ((stored w Q.item x).getD []).length = Q.S.fold.index.rows)
    (hkey : keyFits (key w) Q.par.S.fold.index = true)
    (hbeta : ((key w).seeds.all (!allZero ·.beta)) = true)
    (s₂ : St) (v : Fmt.View) (T : DoorTies Q key stored w fr s₂ v) :
    ∃ (d8 : St) (rest : List Fmt.RoundView) (more : List OpenedColumn),
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] s₂ v.rounds v.opened = .ok (d8, rest, more) ∧
      Seat.enter (·.gU) (·.firstMask) d8 =
        .ok (doorUF Q sentU [b1, b2, b3, b4, b5, b6, b7, b8] key
          (fun w fr => colsLoc Q (stored w) fr.seen.rounds) w fr) := by
  obtain ⟨d8, hF, hD⟩ := doorUF_returns Q sentU layO hP hBU hBO b1 b2 b3 b4 b5 b6 b7 b8 hb key
    stored w fr R1 R2a R2b R4 R5a R5b R7 R8 hfr f1 f2 f4 f5 f7 f8 hW hkey hbeta
  obtain ⟨rest, hr⟩ := T.rounds
  obtain ⟨more, hc⟩ := T.cols
  refine ⟨d8, rest, more, ?_, ?_⟩
  · rw [T.first, hr, hc]
    exact foldBlocks_more 0 _ _ _ _ _ hF rest more
  · rw [hD]
    rfl

/-! ## 4 The third tie, on two texts -/

/-- The frame's reads at a declared round that reads no column: those of the rounds behind. -/
theorem reads_skip (chain ft : ℕ) (stored : ℕ → ℕ → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (d : Fmt.DeclaredRound) (h : ReadsNone d)
    (ds : List Fmt.DeclaredRound) (R : Fmt.Drawn) (Rs : List Fmt.Drawn) :
    readsOf chain ft stored tree (d :: ds) (R :: Rs) = readsOf chain ft stored tree ds Rs := by
  conv_lhs => unfold readsOf
  rw [h.1, h.2]
  simp only [List.flatMap_nil, List.nil_append]

/-- Where the frame's fillCols returns at reads of one stored table in front of others, with no
stored run handed, its columns begin with that table's, each as stored has it. -/
theorem fill_stored (key item width : ℕ) (stored : ℕ → Option (List UInt64)) :
    ∀ (l : List ℕ) (B : List Read) (c : List OpenedColumn),
      fillCols (l.map (fun x => (⟨key, x, some item, none, none, stored x, width⟩ : Read)) ++ B)
        [] = .ok c →
      ∃ more, c = l.map (fun x => (key, x, (stored x).getD [])) ++ more
  | [], _, c, _ => ⟨c, rfl⟩
  | x :: l, B, c, h => by
    rw [List.map_cons, List.cons_append] at h
    unfold fillCols at h
    cases hs : stored x with
    | none =>
      simp only [hs, List.head?_nil] at h
      cases h
    | some wd =>
      simp only [hs, List.tail_nil] at h
      split at h
      · cases h
      · cases hq : fillCols (l.map (fun x =>
            (⟨key, x, some item, none, none, stored x, width⟩ : Read)) ++ B) [] with
        | error e =>
          rw [hq] at h
          cases h
        | ok c' =>
          rw [hq] at h
          obtain rfl : (key, x, wd) :: c' = c := Except.ok.inj h
          obtain ⟨more, rfl⟩ := fill_stored key item width stored l B c' hq
          exact ⟨more, by rw [List.map_cons, hs]; rfl⟩

/-- **(γ), on two texts.** The frame lays a view's columns as fillCols of readsOf
(ProofFile/Honest/Frame.lean). Where the declared rounds are three that read nothing, then "LOC"'s,
then others, and no stored run is handed (back = []), the columns that fillCols returns begin with
colsLoc's, at the same function stored. rs: any rounds; their challenges are what readsOf is
given. -/
theorem cols_of_reads (Q : P14) (chain ft : ℕ) (stored : ℕ → ℕ → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (d0 d1 d2 : Fmt.DeclaredRound) (e : Fmt.Entry)
    (post : List Fmt.DeclaredRound) (h0 : ReadsNone d0) (h1 : ReadsNone d1) (h2 : ReadsNone d2)
    (rs : List Fmt.RoundView) (c : List OpenedColumn)
    (h : fillCols (readsOf chain ft stored tree
      (d0 :: d1 :: d2 :: { entry := e, stored := [readsAtLoc Q.S.fold Q.item] } :: post)
      (rs.map (·.drawn))) [] = .ok c) :
    ∃ more, c = colsLoc Q stored rs ++ more := by
  match rs, h with
  | [], _ => exact ⟨c, rfl⟩
  | [_], _ => exact ⟨c, rfl⟩
  | [_, _], _ => exact ⟨c, rfl⟩
  | [_, _, _], _ => exact ⟨c, rfl⟩
  | r0 :: r1 :: r2 :: R :: rest, h =>
    simp only [List.map_cons] at h
    rw [reads_skip _ _ _ _ d0 h0, reads_skip _ _ _ _ d1 h1, reads_skip _ _ _ _ d2 h2] at h
    have e1 : readsOf chain ft stored tree
        ({ entry := e, stored := [readsAtLoc Q.S.fold Q.item] } :: post)
        (R.drawn :: rest.map (·.drawn)) =
        (Fmt.listOf ((Fmt.partOf (readsAtLoc Q.S.fold Q.item) R.drawn.poss).map
          (· % 2 ^ (readsAtLoc Q.S.fold Q.item).sh.a))).map (fun x =>
            (⟨Fmt.storedKey (readsAtLoc Q.S.fold Q.item).item, x,
              some (readsAtLoc Q.S.fold Q.item).item, none, none,
              stored (readsAtLoc Q.S.fold Q.item).item x,
              (readsAtLoc Q.S.fold Q.item).sh.W⟩ : Read)) ++
          readsOf chain ft stored tree post (rest.map (·.drawn)) := by
      conv_lhs => unfold readsOf
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [e1] at h
    exact fill_stored _ _ _ (stored (readsAtLoc Q.S.fold Q.item).item) _ _ c h

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.colsLoc
#print axioms ProofFile.Honest.K12.Light.colsLoc_form
#print axioms ProofFile.Honest.K12.Light.colsLoc_more
#print axioms ProofFile.Honest.K12.Light.doorUF_returns
#print axioms ProofFile.Honest.K12.Light.foldBlocks_more
#print axioms ProofFile.Honest.K12.Light.DoorTies
#print axioms ProofFile.Honest.K12.Light.doorUF_at_ties
#print axioms ProofFile.Honest.K12.Light.reads_skip
#print axioms ProofFile.Honest.K12.Light.fill_stored
#print axioms ProofFile.Honest.K12.Light.cols_of_reads
#print axioms ProofFile.Honest.K12.Light.noInputs
