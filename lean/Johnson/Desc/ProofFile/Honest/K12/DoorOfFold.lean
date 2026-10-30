-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/DoorOfFold.lean

What it proves. Wherever a fold over a list of blocks that begins with the shared chain's front
block and the eight returns at a view, from the seat's start at the instance's key, the state that
doorUF gives with the reader colsLoc (DoorReturns.lean) is the one with which that fold enters the
test on G_u, and doorUF is off its fall-back there (doorUF_of_fold). Beside two public premises on
the plan it asks the three ties of DoorTies and the fold's return. Of the prover's input the two
ties hk and hc alone read anything; no premise asks a form or a value of the input by itself, and
none is on the form of the rounds: the fold's own return has said that.

Names.
  foldBlocks_less   the converse of foldBlocks_more (DoorReturns.lean).
  groups_skip, wanted_eight   the columns that the eight read at given rounds are as many as colsLoc
      lays.
  doorUF_of_fold   the theorem.
  doorUF_of_carried   at the list that the proof file's description folds over.

By what. eight_of_flat (DoorAtChain.lean); groupsOf_app (Johnson/Desc/Sound/Gather.lean);
groupsOf_none (Johnson/Desc/K15/FoldInv.lean); blocks_rounds, send_plain
(Johnson/Desc/K14/Honest/ChainSteps.lean); rounds_of_blocks, one_round
(Johnson/Desc/K14/Law/RoundsMake.lean, LocFits.lean); flatOf_carried
(Johnson/Desc/K14/Honest/FlatForm.lean); Block.step_ok, foldBlocks_cons_ok
(Johnson/Desc/RunLaws.lean).

Limits.
- One front and one view. The three ties are premises: the first is on the prover's key, the second
  is the frame's to show, of the third cols_of_reads (DoorReturns.lean) has the form. Nobody shows
  them at a run of the frame, at every stand that a play reaches.
- It says nothing where the fold fails. That the fold goes is doorUF_returns' sentence, under
  premises that read the input.
- The list may be just the nine: then the fold's return is that of the front block and the eight,
  not the whole chain's acceptance. That the two tests accept an honest prover's rounds is shown
  nowhere.
- It moves no count. It gives no SaysAt (AsksWhole.lean). The test on G_u alone.
- It stands over files that are not in the library yet, as MarksBehind.lean does.
- Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.DoorAtChain
import Johnson.Desc.Sound.Gather
import Johnson.Desc.K15.FoldInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (OracleNotice TableKey)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks groupsOf Block.step_ok foldBlocks_cons_ok)
open VerifiableInference.Desc.K12 (Seat.enter)
open Desc.K14 (P14 St blocks first readsAtLoc chainOf withU)
open Desc.K14.Honest (ReadsNone blocks_rounds send_plain FlatOf flatOf_carried)

variable {W X : Type}

/-! ## 1 The converse of foldBlocks_more -/

/-- The tool: the converse of foldBlocks_more. A fold that returns has taken as many rounds as its
blocks declare and as many columns as groupsOf lists at these rounds; over just these it returns the
same state with nothing left over. -/
theorem foldBlocks_less (ft : ℕ) : ∀ (bs : List (Block St Unit)) (s d : St) (rs rs' : List Fmt.RoundView)
    (cols cols' : List OpenedColumn), foldBlocks ft bs s rs cols = .ok (d, rs', cols') →
    ∃ n m, n = (bs.flatMap (·.rounds)).length ∧ n ≤ rs.length ∧ m ≤ cols.length ∧
      m = ((groupsOf ft (bs.flatMap (·.rounds)) ((rs.take n).map (·.drawn))).flatMap id).length ∧
      rs' = rs.drop n ∧ cols' = cols.drop m ∧
      foldBlocks ft bs s (rs.take n) (cols.take m) = .ok (d, [], [])
  | [], s, d, rs, rs', cols, cols', h => by
    have e : (s, rs, cols) = (d, rs', cols') := Except.ok.inj h
    obtain rfl : s = d := (Prod.mk.inj e).1
    obtain rfl : rs = rs' := (Prod.mk.inj (Prod.mk.inj e).2).1
    obtain rfl : cols = cols' := (Prod.mk.inj (Prod.mk.inj e).2).2
    exact ⟨0, 0, rfl, Nat.zero_le _, Nat.zero_le _, rfl, rfl, rfl, rfl⟩
  | b :: l, s, d, rs, rs', cols, cols', h => by
    obtain ⟨hl, s', k, hs, hf⟩ := foldBlocks_cons_ok.1 h
    obtain ⟨a1, a2, a3, a4⟩ := Block.step_ok.1 hs
    obtain ⟨n', m', i1, i2, i3, i4, i5, i6, i7⟩ := foldBlocks_less ft l s' d _ _ _ _ hf
    have hnb : b.rounds.length ≤ rs.length := by
      rw [List.length_take] at hl
      omega
    have hk : k ≤ cols.length := by
      have := congrArg List.length a2
      rw [List.length_map, List.length_take, ← a4] at this
      omega
    rw [List.length_drop] at i2 i3
    have t1 : rs.take (b.rounds.length + n') =
        rs.take b.rounds.length ++ (rs.drop b.rounds.length).take n' := List.take_add
    have t2 : (rs.take (b.rounds.length + n')).take b.rounds.length = rs.take b.rounds.length := by
      rw [List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)]
    have t3 : (rs.take (b.rounds.length + n')).drop b.rounds.length =
        (rs.drop b.rounds.length).take n' := by
      rw [List.drop_take, Nat.add_sub_cancel_left]
    have c2 : (cols.take (k + m')).take k = cols.take k := by
      rw [List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)]
    have c3 : (cols.take (k + m')).drop k = (cols.drop k).take m' := by
      rw [List.drop_take, Nat.add_sub_cancel_left]
    refine ⟨b.rounds.length + n', k + m', ?_, by omega, by omega, ?_, ?_, ?_, ?_⟩
    · rw [List.flatMap_cons, List.length_append, i1]
    · rw [List.flatMap_cons, t1, List.map_append,
        VerifiableInference.Desc.Sound.groupsOf_app ft _ _ _ _ (by rw [List.length_map]; exact hl),
        List.flatMap_append, List.length_append, ← a4, ← i4]
    · rw [i5, List.drop_drop]
    · rw [i6, List.drop_drop]
    · refine foldBlocks_cons_ok.2 ⟨by rw [t2]; exact hl, s', k, ?_, ?_⟩
      · rw [t2]
        exact Block.step_ok.2 ⟨a1, by rw [c2]; exact a2, by rw [c2]; exact a3, a4⟩
      · rw [t3, c3]
        exact i7

/-! ## 2 How many columns the eight read -/

/-- The library's groupsOf at a declared round that reads no column: that of the rounds behind. -/
theorem groups_skip (ft : ℕ) (d : Fmt.DeclaredRound) (h : ReadsNone d) (ds : List Fmt.DeclaredRound)
    (R : Fmt.Drawn) (Rs : List Fmt.Drawn) :
    groupsOf ft (d :: ds) (R :: Rs) = groupsOf ft ds Rs := by
  conv_lhs => unfold groupsOf
  rw [h.1, h.2]
  rfl

/-- **The columns that the eight read at given rounds are as many as colsLoc lays.** -/
theorem wanted_eight (Q : P14) (sentU : Array OracleNotice)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hU : withU Q.S = some sentU)
    (stored : ℕ → ℕ → Option (List UInt64)) (ft : ℕ) (rs : List Fmt.RoundView) :
    ((groupsOf ft ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds))
      (rs.map (·.drawn))).flatMap id).length = (colsLoc Q stored rs).length := by
  obtain ⟨p1, e2, e3, e4, e5, e6, p7, p8⟩ := blocks_rounds Q sentU b1 b2 b3 b4 b5 b6 b7 b8 hb hU
  obtain ⟨d0, hd0, -⟩ := Desc.K14.Law.one_round
    (Desc.K14.Law.rounds_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hb).1
  have h0 : ReadsNone d0 := p1 d0 (by rw [hd0]; exact List.mem_cons_self)
  have hpost : ∀ d ∈ b5.rounds ++ (b6.rounds ++ (b7.rounds ++ b8.rounds)),
      d.stored = [] ∧ d.opens = [] := by
    intro d hd
    rw [e6, List.nil_append] at hd
    rcases List.mem_append.1 hd with c | c
    · rw [e5] at c
      exact send_plain _ d c
    · rcases List.mem_append.1 c with c | c
      · exact p7 d c
      · exact p8 d c
  have eL : [b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds) =
      d0 :: { entry := VerifiableInference.Desc.K1.seedEntry (Desc.K14.Law.parU Q sentU) } ::
        { entry := VerifiableInference.Desc.K1.answerEntry (Desc.K14.Law.parU Q sentU) } ::
        { entry := Desc.K14.Law.entryAt Q 1, stored := [readsAtLoc Q.S.fold Q.item] } ::
        (b5.rounds ++ (b6.rounds ++ (b7.rounds ++ b8.rounds))) := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, hd0, e2, e3, e4]
    rfl
  rw [eL]
  match rs with
  | [] => rfl
  | [_] =>
    simp only [List.map_cons, List.map_nil]
    rw [groups_skip ft d0 h0]
    rfl
  | [_, _] =>
    simp only [List.map_cons, List.map_nil]
    rw [groups_skip ft d0 h0, groups_skip ft _ ⟨rfl, rfl⟩]
    rfl
  | [_, _, _] =>
    simp only [List.map_cons, List.map_nil]
    rw [groups_skip ft d0 h0, groups_skip ft _ ⟨rfl, rfl⟩, groups_skip ft _ ⟨rfl, rfl⟩]
    rfl
  | r0 :: r1 :: r2 :: R :: rest =>
    simp only [List.map_cons]
    rw [groups_skip ft d0 h0, groups_skip ft _ ⟨rfl, rfl⟩, groups_skip ft _ ⟨rfl, rfl⟩]
    conv_lhs => unfold groupsOf
    rw [VerifiableInference.Desc.groupsOf_none ft _ _ hpost]
    show ((([readsAtLoc Q.S.fold Q.item].map fun s =>
      (Fmt.listOf ((Fmt.partOf s R.drawn.poss).map (· % 2 ^ s.sh.a))).map fun x =>
        (Fmt.storedKey s.item, x, s.sh.W)) ++ [] ++ []).flatMap id).length =
      ((Fmt.listOf ((Fmt.partOf (readsAtLoc Q.S.fold Q.item) R.drawn.poss).map
        (· % 2 ^ (readsAtLoc Q.S.fold Q.item).sh.a))).map _).length
    simp only [List.map_cons, List.map_nil, List.append_nil, List.flatMap_cons, List.flatMap_nil,
      id, List.length_map]

/-! ## 3 The theorem -/

/-- **Wherever the verifier's fold over a list that begins with the shared chain's front block and
the eight returns at the view v, doorUF's state is the one with which that fold enters the test on
G_u.** Of the prover's input no premise but the ties hk and hc reads anything; none asks a form or a
value of it by itself, and none is on the form of the rounds: the fold's own return has said all of
that.
Public, on the plan: hb, hU.
The three ties, on one front and one view. hk: (α) the key that the prover's shared parts are given
is the instance's: a premise on the prover's key. hr, hn: (β) what the part has seen are the view's
first rounds, as many as the eight declare: the frame's to show. hc: (γ) the reader's columns are
the view's first columns (cols_of_reads, DoorReturns.lean, has the form of it).
hv: the verifier's fold returns. Where it fails nothing is said. Through the ties hv says that the
fold goes at the prover's key and stored columns: so it can narrow the input: this theorem moves
that debt into one place and does not pay it. xs may be just the nine: then hv is the return of the
front block and the eight, which doorUF_returns gives, and not the whole chain's acceptance.
The third conjunct: doorUF is off its fall-back there: the fold that doorOf makes returns, with
nothing left over, the same d8. No SaysAt follows. The test on G_u alone. -/
theorem doorUF_of_fold {Cl : Type} (c : OnBytes.Model.Verify.Chains) (Q : P14)
    (sentU : Array OracleNotice) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hU : withU Q.S = some sentU)
    (key : W → TableKey) (stored : W → ℕ → ℕ → Option (List UInt64)) (w : W) (fr : Front X)
    (k : TableKey) (v : Fmt.View) (hk : key w = k)
    (hr : ∃ rest, v.rounds = fr.seen.rounds ++ rest)
    (hn : fr.seen.rounds.length =
      ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length)
    (hc : ∃ more, v.opened = colsLoc Q (stored w) fr.seen.rounds ++ more)
    (xs : List (Block St Cl)) (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (out : St × List Fmt.RoundView × List OpenedColumn)
    (hv : foldBlocks 0 xs (first Q.codes k) v.rounds v.opened = .ok out) :
    ∃ (d8 : St) (rest : List Fmt.RoundView) (more : List OpenedColumn),
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first Q.codes k) v.rounds v.opened =
        .ok (d8, rest, more) ∧
      foldBlocks 0 (xs.drop 9) d8 rest more = .ok out ∧
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first Q.codes (key w)) fr.seen.rounds
        (colsLoc Q (stored w) fr.seen.rounds) = .ok (d8, [], []) ∧
      Seat.enter (·.gU) (·.firstMask) d8 =
        .ok (doorUF Q sentU [b1, b2, b3, b4, b5, b6, b7, b8] key
          (fun w fr => colsLoc Q (stored w) fr.seen.rounds) w fr) := by
  obtain ⟨d8, rs', cols', g1, g2⟩ := eight_of_flat c xs F _ _ _ out hv
  obtain ⟨n, m, j1, -, -, j4, -, -, j7⟩ := foldBlocks_less 0 _ _ _ _ _ _ _ g1
  obtain ⟨rest, hr⟩ := hr
  obtain ⟨more, hc⟩ := hc
  have en : v.rounds.take n = fr.seen.rounds := by
    rw [hr, j1, ← hn, List.take_left']
    rfl
  rw [en, wanted_eight Q sentU b1 b2 b3 b4 b5 b6 b7 b8 hb hU (stored w) 0 fr.seen.rounds] at j4
  have em : v.opened.take m = colsLoc Q (stored w) fr.seen.rounds := by
    rw [hc, j4, List.take_left']
    rfl
  rw [en, em, ← hk] at j7
  refine ⟨d8, rs', cols', g1, g2, j7, ?_⟩
  unfold doorUF doorOf
  simp only [j7]
  rfl

/-- **At the list that the proof file's description folds over**: the library's shared chain carried
to the description's own type of claims (flatOf_carried): doorUF_of_fold there. -/
theorem doorUF_of_carried {Cl : Type} (c : OnBytes.Model.Verify.Chains) (Q : P14)
    (sentU : Array OracleNotice) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hU : withU Q.S = some sentU)
    (key : W → TableKey) (stored : W → ℕ → ℕ → Option (List UInt64)) (w : W) (fr : Front X)
    (k : TableKey) (v : Fmt.View) (hk : key w = k)
    (hr : ∃ rest, v.rounds = fr.seen.rounds ++ rest)
    (hn : fr.seen.rounds.length =
      ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length)
    (hc : ∃ more, v.opened = colsLoc Q (stored w) fr.seen.rounds ++ more)
    (tests : List (Block St Unit)) (last : List (Block St Unit) → Block St Unit)
    (out : St × List Fmt.RoundView × List OpenedColumn)
    (hv : foldBlocks 0 ((chainOf c Q tests last).retype (Cl' := Cl)).blocksInOrder (first Q.codes k) v.rounds
      v.opened = .ok out) :
    ∃ (d8 : St) (rest : List Fmt.RoundView) (more : List OpenedColumn),
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first Q.codes k) v.rounds v.opened =
        .ok (d8, rest, more) ∧
      foldBlocks 0 (((chainOf c Q tests last).retype (Cl' := Cl)).blocksInOrder.drop 9) d8 rest more =
        .ok out ∧
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first Q.codes (key w)) fr.seen.rounds
        (colsLoc Q (stored w) fr.seen.rounds) = .ok (d8, [], []) ∧
      Seat.enter (·.gU) (·.firstMask) d8 =
        .ok (doorUF Q sentU [b1, b2, b3, b4, b5, b6, b7, b8] key
          (fun w fr => colsLoc Q (stored w) fr.seen.rounds) w fr) :=
  doorUF_of_fold c Q sentU b1 b2 b3 b4 b5 b6 b7 b8 hb hU key stored w fr k v hk hr hn hc _
    (flatOf_carried c Q b1 b2 b3 b4 b5 b6 b7 b8 tests last hb) out hv

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.foldBlocks_less
#print axioms ProofFile.Honest.K12.Light.groups_skip
#print axioms ProofFile.Honest.K12.Light.wanted_eight
#print axioms ProofFile.Honest.K12.Light.doorUF_of_fold
#print axioms ProofFile.Honest.K12.Light.doorUF_of_carried
