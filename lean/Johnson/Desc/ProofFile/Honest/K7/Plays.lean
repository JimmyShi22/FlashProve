-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K7/Plays.lean: THE NEXT TOKEN's MEMBER OF THE FIRST CHAIN AT THE
THREADS: WHERE ITS HALF STANDS (a record of named premises on the thread's letters), AND THE FIRST
OF THE MEMBER's DEBTS: IT PLAYS (`PlaysS`, Honest/Thread/PaysS.lean). General in the thread T and in
the letter Said.

  `K7Stands T b l V blk`   THE SEAT: blk is the member number b; its rounds are the kind's one round
      («REPLY»: one element in the clear, no root, nothing opened, nothing drawn); no oracle
      message; the half that the fold finds at its place is `replyHalf l 1 V` (V is not read:
      Honest/K7.lean); the member sends no tree
  `one_draw`       challenges that fit one declared round are one challenge
  `reply_fits`     along every run the row's one message has the shape that the round states,
      whatever rounds are shown and whatever columns are handed (`Seen`)
  `k7_moved`       FROM THE SEAT ALONE, at every stand: where `chainSteps` has returned, the
      challenges fit (`drawsFit`) and nothing stops: `play` returns the one round `replyShown`; the
      state's field `opened` is carried on as it was; the member's own round reads no column
  `k7_playsS`      **IT PLAYS**

`PlaysS` reads of the member its name, place, rounds and oracle messages, not its decision: so
nothing is asked here of what the member is made of (the entry into the head's segment, the next
token's sub-protocol, the frame's «opened»: Honest/K7/Keeps.lean).

By `steps_one_half` (Honest/Law/Thread.lean), `row_silent` (Honest/Small/SaysYesOf.lean),
`play_row_whole` (Honest/Small/PlayRow.lean), `reply_played` (Honest/K7/Played.lean).

Limits. A conditional lemma on our own definitions; none of the library's goals. Nothing shows that
the seat's premises hold at a thread. `k7_moved` runs over every state m, and `k7_playsS` does not
spend `ThrS`: so both hold at every value of the field `opened`: the row's one part reads neither
the rounds shown nor the columns handed (`reply_played`, `reply_fits`: at every `Seen`). This file
proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K7.Played
import Johnson.Desc.ProofFile.Honest.Small.SaysYesOf
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.Kinds.ReplyKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place)
open ProofFile.Honest.Small (playedRow stateRow fitsRow play_row_whole row_silent)

variable {Bk : ProverCoinCounts} {S Cl W₀ Rc Tr X Pb : Type}

/-- **The seat.** A hypothesis's form. Nothing is claimed by the definition. -/
structure K7Stands (T : Thread Bk S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Pb)
    (b l V : Nat) (blk : Block S Cl) : Prop where
  /-- blk is the member -/
  member : T.bs[b]? = some blk
  /-- its rounds are the kind's -/
  rounds : blk.rounds = VerifiableInference.Desc.Kinds.Reply.rounds
  /-- the round has no oracle message -/
  oracles : blk.oracles = [[]]
  /-- the half that the fold finds for the member's place -/
  half : T.hs.find? (fun h => h.place == blk.place) = some (replyHalf l 1 V)
  /-- the member sends no tree -/
  noTree : T.fresh b = []

theorem one_draw {r : Fmt.DeclaredRound} {ds : List Fmt.Drawn} (h : drawsFit [r] ds = true) :
    ∃ d, ds = [d] := by
  match ds, h with
  | [d], _ => exact ⟨d, rfl⟩
  | [], h => cases h
  | _ :: _ :: _, h =>
    simp only [drawsFit, Bool.and_false] at h
    cases h

theorem reply_fits
    (c : RowCoins [(replyPart : Part (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X)])
    (t : State (Local W₀ Rc Inst Tr) X) (seen : Seen) (d : Fmt.Drawn) :
    fitsRow [(replyPart : Part (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X)]
      (VerifiableInference.Desc.Kinds.Reply.rounds.zip [[]]) c t seen [d] = true := rfl

variable {T : Thread Bk S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Pb} {b l V : Nat}
  {blk : Block S Cl}

/-- **The prover's side of the member's step, written out.** -/
theorem k7_moved (K : K7Stands T b l V blk) {k : Coins Bk} {m : Mid (Local W₀ Rc Inst Tr) X}
    {E : Env} {ds : List Fmt.Drawn} {L : List (Step (Local W₀ Rc Inst Tr) X)}
    (hd : drawsFit blk.rounds ds = true)
    (hst : chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none)
    (hl : chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) [blk] T.hs =
      .ok L) :
    ∃ d, ds = [d] ∧ T.Moved blk k m E ds
      ([replyShown blk.name blk.place m.st.input.x d],
        ⟨stateRow (replyHalf (W₀ := W₀) (Rc := Rc) (Tr := Tr) (X := X) l 1 V).parts m.st ds,
          m.loc ++ ds, m.seen ++ roundsOf [replyShown blk.name blk.place m.st.input.x d],
          m.opened⟩) [] := by
  have hs' := row_silent K.half hd hst
  obtain ⟨c, -, rfl⟩ := steps_one_half K.half hl
  obtain ⟨d, rfl⟩ : ∃ d, ds = [d] := one_draw (K.rounds ▸ hd)
  refine ⟨d, rfl, ⟨_, hl, ?_⟩, ?_⟩
  · refine play_row_whole blk.name blk.place _ _ 0 _ c [d] [] m _ hs' ?_
      (reply_played blk.name blk.place c m.st m.shown d)
    rw [K.rounds, K.oracles]
    exact reply_fits c m.st m.shown d
  · rw [K.rounds]
    rfl

/-- **IT PLAYS.** -/
theorem k7_playsS (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop)
    (K : K7Stands T b l V blk) : PlaysS T Said b := by
  intro blk' hblk k s m E ds L _ hd hst hl
  obtain rfl : blk = blk' := Option.some.inj (K.member.symm.trans hblk)
  obtain ⟨d, -, hM⟩ := k7_moved (E := E) K hd hst hl
  refine ⟨_, _, hM, ?_⟩
  rw [K.noTree]
  intro σ hσ
  cases hσ

end ProofFile.Honest

#print axioms ProofFile.Honest.one_draw
#print axioms ProofFile.Honest.reply_fits
#print axioms ProofFile.Honest.k7_moved
#print axioms ProofFile.Honest.k7_playsS
#print axioms ProofFile.Honest.K7Stands
