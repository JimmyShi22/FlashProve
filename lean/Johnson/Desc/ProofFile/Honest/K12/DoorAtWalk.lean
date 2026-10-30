-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/DoorAtWalk.lean

What it proves. The door at the proximity test on G_u, in a walk of the shared chain by the frame's
prover that asks the description's own step (walk, ProofFile/Honest/Walk.lean). Where the walk has
returned and one of the rounds behind the eight's was made by a prover's side, the fold that doorOf
makes over the eight, at the rounds produced so far and the reader colsLoc (DoorReturns.lean) at the
walk's own function for the stored tables' columns, returns with nothing left over: so doorUF
(DoorsByShape.lean) is off its fall-back, and its state is what the seat's way in makes of the state
that the fold over the eight returns from the walk's own start. That the fold goes is concluded here
from the run itself: no premise on the form of the rounds, on the key's sizes or values, or on the
stored columns' widths.

Names.
  rounds_eight   the eight's declared rounds: three that read nothing, "LOC"'s, then others.
  door_of_cols   from a fold over the front block and the eight that has returned at columns which
      fillCols has laid.
  door_at_walk   the theorem.

By what. called_fold (CalledFold.lean); cols_of_reads (DoorReturns.lean); foldBlocks_less,
wanted_eight (DoorOfFold.lean); fold_like, peel_front (Johnson/Desc/K14/Honest/FlatSteps.lean);
FlatOf, Like (FlatForm.lean, there); blocks_rounds (ChainSteps.lean, there); rounds_of_blocks,
one_round (Johnson/Desc/K14/Law/).

Limits.
- It is of the walk (runC), not of play (run). The frame's run plays with no verifier beside it and
  reaches stands at which the verifier would long have refused (a seed of the key with the factor 0;
  a stored column of another width): there the fold fails and doorUF falls back as before. The walk
  calls no part there: that is why the premises can go. What is had: at every stand at which a walk
  calls the test's part.
- Three equations stay the caller's: the reader key gives the key of the walk's start; the reader
  stored is the walk's; the front has seen just the rounds produced.
- bs, k, the Lay and front₀ (the columns that ChainProgress.start is handed) are free: that they are a
  description's own, or a run's, is the caller's.
- Nothing on whether a walk returns or calls the part.
- It moves no count. It gives no SaysAt (AsksWhole.lean). The test on G_u alone.
- It stands over files that are not in the library yet, as MarksBehind.lean does.
- Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.CalledFold
import Johnson.Desc.ProofFile.Honest.K12.DoorOfFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (OracleNotice TableKey)
open VerifiableInference.Desc (Block OpenedColumn Place foldBlocks)
open VerifiableInference.Desc.K12 (Seat.enter)
open Desc.K14 (P14 St blocks first readsAtLoc withU frontBlock)
open Desc.K14.Honest (ReadsNone blocks_rounds send_plain FlatOf Like fold_like peel_front)
open ProofFile.Honest (Lay ChainProgress Mid Step Played Table walk roundsOf readsOf fillCols envOf)

/-- The eight's declared rounds: three that read no column, then "LOC"'s round, then others. -/
theorem rounds_eight (Q : P14) (sentU : Array OracleNotice)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hU : withU Q.S = some sentU) :
    ∃ (d0 d1 d2 : Fmt.DeclaredRound) (e : Fmt.Entry) (post : List Fmt.DeclaredRound),
      ReadsNone d0 ∧ ReadsNone d1 ∧ ReadsNone d2 ∧
      [b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds) = d0 :: d1 :: d2 ::
        { entry := e, stored := [readsAtLoc Q.S.fold Q.item] } :: post := by
  obtain ⟨p1, e2, e3, e4, -⟩ := blocks_rounds Q sentU b1 b2 b3 b4 b5 b6 b7 b8 hb hU
  obtain ⟨d0, hd0, -⟩ := Desc.K14.Law.one_round
    (Desc.K14.Law.rounds_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hb).1
  have h0 : ReadsNone d0 := p1 d0 (by rw [hd0]; exact List.mem_cons_self)
  refine ⟨d0, { entry := VerifiableInference.Desc.K1.seedEntry (Desc.K14.Law.parU Q sentU) },
    { entry := VerifiableInference.Desc.K1.answerEntry (Desc.K14.Law.parU Q sentU) },
    Desc.K14.Law.entryAt Q 1, b5.rounds ++ (b6.rounds ++ (b7.rounds ++ (b8.rounds ++ []))), h0,
    ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ?_⟩
  simp only [List.flatMap_cons, List.flatMap_nil, hd0, e2, e3, e4]
  rfl

/-- **From a fold over the front block and the eight that has returned, with nothing left over, at
columns which fillCols has laid for their reads**: the fold over the eight at the reader colsLoc
returns the same state; and doorUF gives what the seat's way in makes of it, at every input and
front whose three readers agree with k, stored and rs. -/
theorem door_of_cols {Cl V X : Type} (c : OnBytes.Model.Verify.Chains) (Q : P14)
    (sentU : Array OracleNotice) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hU : withU Q.S = some sentU)
    (pre : List (Block St Cl))
    (hpre : List.Forall₂ Like pre [frontBlock c, b1, b2, b3, b4, b5, b6, b7, b8])
    (chain : ℕ) (stored : ℕ → ℕ → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (k : TableKey) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (s : St)
    (hfold : foldBlocks 0 pre (first Q.codes k) rs cols = .ok (s, [], []))
    (hfill : fillCols (readsOf chain 0 stored tree
      ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)) (rs.map (·.drawn))) [] = .ok cols) :
    foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first Q.codes k) rs (colsLoc Q stored rs) =
        .ok (s, [], []) ∧
      ∀ (key : V → TableKey) (st : V → ℕ → ℕ → Option (List UInt64)) (w : V) (fr : Front X),
        key w = k → st w = stored → fr.seen.rounds = rs →
        Seat.enter (·.gU) (·.firstMask) s =
          .ok (doorUF Q sentU [b1, b2, b3, b4, b5, b6, b7, b8] key
            (fun w fr => colsLoc Q (st w) fr.seen.rounds) w fr) := by
  have g := peel_front c 0 _ _ _ _ _ (fold_like 0 pre _ hpre _ _ _ _ hfold)
  obtain ⟨d0, d1, d2, e, post, h0, h1, h2, eq⟩ :=
    rounds_eight Q sentU b1 b2 b3 b4 b5 b6 b7 b8 hb hU
  rw [eq] at hfill
  obtain ⟨more, hc⟩ := cols_of_reads Q chain 0 stored tree d0 d1 d2 e post h0 h1 h2 rs cols hfill
  obtain ⟨n, m, -, -, -, j4, j5, -, j7⟩ := foldBlocks_less 0 _ _ _ _ _ _ _ g
  have en : rs.take n = rs := List.take_of_length_le (List.drop_eq_nil_iff.1 j5.symm)
  rw [en, wanted_eight Q sentU b1 b2 b3 b4 b5 b6 b7 b8 hb hU stored 0 rs] at j4
  have em : cols.take m = colsLoc Q stored rs := by
    rw [hc, j4, List.take_left']
    rfl
  rw [en, em] at j7
  refine ⟨j7, fun key st w fr hk hs hfr => ?_⟩
  unfold doorUF doorOf
  simp only [hk, hs, hfr, j7]
  rfl

/-- **The door at the test on G_u, in a walk of the shared chain.** bs: a list of blocks that begins
with the shared chain's front block and the eight (FlatOf) and goes on with a block that has a round
(the test on G_u). The walk starts at the verifier's state first Q.codes k. Where it has returned
and one of the rounds behind the eight's was made by a prover's side: the fold that doorOf makes,
over the eight, at the rounds produced so far and the reader colsLoc at the walk's own function
stored, returns, with nothing left over; so at every input w and front fr whose key is k, whose
stored is the walk's and which has seen just these rounds, doorUF is off its fall-back, and its
state is what the seat's way in makes of the state that the fold over the eight returns from the
walk's own start.
Public, on the plan: hb, hU, F, h9. On the Lay: hft, hL. On the walk: ha, hz, ht. No premise on the
form of the rounds, on the key's sizes or values, or on the stored columns' widths: they follow.
It is of the walk (runC), not of play (run). No SaysAt follows. The test on G_u alone. -/
theorem door_at_walk {Cl W Y V X : Type} (c : OnBytes.Model.Verify.Chains) (Q : P14)
    (sentU : Array OracleNotice) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hU : withU Q.S = some sentU)
    (bs : List (Block St Cl)) (F : FlatOf bs c b1 b2 b3 b4 b5 b6 b7 b8)
    (h9 : ∃ t9 tl, bs.drop 9 = t9 :: tl ∧ 0 < t9.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {taken : ℕ → ℕ → Option (Place × Table)}
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) (m₀ : ProofFile.Honest.Mid W Y)
    (k : TableKey)
    {a z : ChainProgress St Cl W Y} {ss : List (Step W Y)} {ds : List Fmt.Drawn} {front₀ : List OpenedColumn}
    (ha : ChainProgress.start L bs (some m₀) (some (first Q.codes k)) front₀ = .ok a)
    (hz : walk L ss ds a = .ok z)
    (ht : ∃ p ∈ z.laid.drop ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length,
      p.told = true) :
    ∃ d8 : St,
      foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first Q.codes k)
        (roundsOf (z.laid.take ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length))
        (colsLoc Q L.stored
          (roundsOf (z.laid.take ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length))) =
        .ok (d8, [], []) ∧
      ∀ (key : V → TableKey) (stored : V → ℕ → ℕ → Option (List UInt64)) (w : V) (fr : Front X),
        key w = k → stored w = L.stored →
        fr.seen.rounds =
          roundsOf (z.laid.take ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length) →
        Seat.enter (·.gU) (·.firstMask) d8 =
          .ok (doorUF Q sentU [b1, b2, b3, b4, b5, b6, b7, b8] key
            (fun w fr => colsLoc Q (stored w) fr.seen.rounds) w fr) := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  obtain ⟨t9, tl', h9e, h9p⟩ := h9
  have etl : tl = t9 :: tl' := h9e
  subst etl
  have eR : [x0, x1, x2, x3, x4, x5, x6, x7, x8].flatMap (·.rounds) =
      [b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds) := by
    simp only [List.flatMap_cons, List.flatMap_nil, l0.rounds, l1.rounds, l2.rounds, l3.rounds,
      l4.rounds, l5.rounds, l6.rounds, l7.rounds, l8.rounds]
    rfl
  obtain ⟨s, cols, more, hfold, hfill, -⟩ := called_fold L hL [x0, x1, x2, x3, x4, x5, x6, x7, x8]
    t9 tl' h9p m₀ (first Q.codes k) ha hz (by rw [eR]; exact ht)
  rw [eR, hft] at hfold hfill
  have ed : (z.laid.take ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length).map
      (·.drawn) = (roundsOf (z.laid.take
        ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length)).map (·.drawn) := by
    unfold roundsOf
    rw [List.map_map]
    rfl
  rw [ed] at hfill
  obtain ⟨g1, g2⟩ := door_of_cols (V := V) (X := X) c Q sentU b1 b2 b3 b4 b5 b6 b7 b8 hb hU _
    (.cons l0 (.cons l1 (.cons l2 (.cons l3 (.cons l4 (.cons l5 (.cons l6 (.cons l7
      (.cons l8 .nil))))))))) L.chain L.stored _ k _ cols s hfold hfill
  exact ⟨s, g1, g2⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.rounds_eight
#print axioms ProofFile.Honest.K12.Light.door_of_cols
#print axioms ProofFile.Honest.K12.Light.door_at_walk
