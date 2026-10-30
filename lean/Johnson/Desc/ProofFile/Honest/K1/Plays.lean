-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Plays.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR THE
HONEST SIDE: AT A MEMBER OF A CHAIN WHOSE SHAPE IS THE PLAN's AND WHOSE HALF IS placeHalf
(Honest/K1/PlaceJob.lean), THE FRAME's PLAY OF THE MEMBER's STEPS AND THE LAYING OF ITS COLUMNS
RETURN (Thread.Moved, Honest/Thread/Pays.lean), where the public test sendFits says yes; and what is
played is written out. One definition with code; statements and proofs. General in the thread.

  k1_reads_none, k1_cols_return   K1's two rounds open no tree, stored or other: nothing is read at
                any list of challenges, and the laying of the columns returns the empty list
  k1_draws_two  what K1's rounds can draw: two challenges, the first of which holds just the seeds
  second_say    the part's second move, beside first_say (Honest/K1/TableShape.lean)
  k1_first_fits, k1_second_fits   the first message, and a message of as many answers as the plan
                counts (P.answers), have the shapes that K1's own block states
  k1_row_silent   the stops of placeHalf's row never stop
  playedK1      THE TERM: the member's two rounds AS PLAYED: A SECOND TEXT of sendPart's two
                messages (Honest/K1/Part.lean): sendPart's own calls at sendPart's own arguments
  lately_hears  behind a challenge the last challenge heard is that one
  played_k1     the tie: under the two public tests the frame's terms for a row (playedRow, fitsRow,
                Honest/Small/PlayRow.lean) return it, at each value of the coins
  k1_moved      THE MEMBER's PLAY AND ITS COLUMNS' LAYING RETURN: at every stand, all tables at
                hand, every list that the member's rounds can draw and all coins at which chainSteps
                lays the member's steps (the book lends): no thread in front and no silence of a
                stop is asked
  k1_moved_term   and what is played is the term, at the coins that the book lends

WHAT IS SENT, NOT WHAT IS SHOWN. playedK1's first record holds the part's tables WHOLE, at all
positions: that is what is SENT as an oracle; a verifier is shown a root and the opened columns.

Limits. The premises on the member (its shape, its half) are met at no chain here. Of "it plays"
(Plays, Honest/Thread/Pays.lean) the first half alone is proved here: that the member's new trees
are the thread's tables is not (under more premises, from the pair with PlayedTo:
Honest/K1/PlaysS.lean). "It plays" is the frame's name for a premise's form: IT IS NO COMPLETENESS,
and it does not say that the prover's messages are accepted. That sendFits holds at a plan, and that
the book lends the part its coins, are premises. playedK1 lays no default of its own; "held (fun _ _
_ => 0)" is sendPart's own text. Nothing on how a coin is made. On hiding nothing is said. Nothing
on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob
import Johnson.Desc.ProofFile.Honest.K1.TableShape
import Johnson.Desc.ProofFile.Honest.Small.SaysYesOf
import Johnson.Desc.ProofFile.Honest.Thread.Pays
import Johnson.Prover.Send.Form

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt col answers)
open ProofFile.Honest.Small (playedRow fitsRow stateRow play_row_whole member_played)
open ProofFile.Honest.SumLaw (playedFrom fitsFrom stateFrom aloneFrom)

variable {S Cl V W W' X Xi Pb : Type} {Bk : ProverCoinCounts}

/-- K1's two rounds open nothing: nothing is read, at every list of challenges. -/
theorem k1_reads_none (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (P : K1.Par) (ds : List Fmt.Drawn) :
    readsOf chain ft stored tree (K1.rounds P) ds = [] := by
  unfold K1.rounds
  cases ds with
  | nil => simp [readsOf]
  | cons a t =>
    cases t with
    | nil => simp [readsOf]
    | cons b u => cases u <;> simp [readsOf]

/-- So the laying of the columns returns the empty list. -/
theorem k1_cols_return (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (P : K1.Par) (ds : List Fmt.Drawn) :
    fillCols (readsOf chain ft stored tree (K1.rounds P) ds) [] = .ok [] := by
  rw [k1_reads_none]
  rfl

/-- What K1's rounds can draw: two challenges, the first of which holds just the seeds. -/
theorem k1_draws_two (P : K1.Par) (ds : List Fmt.Drawn) (h : drawsFit (K1.rounds P) ds = true) :
    ∃ d₀ d₁, ds = [d₀, d₁] ∧ seedsFit P [d₀] = true := by
  unfold K1.rounds at h
  match ds, h with
  | [], h => simp [drawsFit] at h
  | [_], h => simp [drawsFit] at h
  | _ :: _ :: _ :: _, h => simp [drawsFit] at h
  | [d₀, d₁], h =>
    refine ⟨d₀, d₁, rfl, ?_⟩
    simp only [drawsFit, Bool.and_eq_true] at h
    have h0 := h.1
    unfold drawFit at h0
    simp only [Bool.and_eq_true] at h0
    exact h0.1.1.1.1.1.1.1

/-- **The part's second move**, where the job fits its place and the challenge holds the seeds. THE
0 BENEATH THE HELD WORDS: NO COIN: A CONSTANT; never read at the job's own messages (answers_any,
Honest/K1/Law/SendAtBlock.lean). -/
theorem second_say (J : SendJob W' X) (hf : sendFits J.P J.ride = true) :
    ∃ m₁ m₂, (sendPart (V := V) J).moves = [m₁, m₂] ∧
      ∀ c s t, seedsFit J.P (t.lately 1) = true → m₂.say c s t = .ok
        ⟨(answers J.P (stAt J.P J.first) J.first
            (Johnson.Prover.Send.held (fun _ _ _ => 0) J.first J.P (J.rows c.1 s t 1))
            (seedsAt J.P (t.lately 1))).map fun a => .answer (toE a), []⟩ := by
  refine ⟨_, _, rfl, fun c s t hs => ?_⟩
  simp [hf, hs]

/-- The first message has the shape that K1's own block states for its first round. -/
theorem k1_first_fits (P : K1.Par) (Vr : Nat → Rows) :
    (⟨[], treeTables P Vr⟩ : Sending).fits { entry := K1.seedEntry P }
      ((K1.oracles P).headD []) = true := by
  have e : (({ entry := K1.seedEntry P } : Fmt.DeclaredRound).items.filter (· != .root)) = [] := by
    simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, K1.seedEntry]
  unfold Sending.fits
  rw [e, treeTables_oracles]
  simp

/-- A message of as many answers as the plan counts has the shape that K1's own block states for its
second round. -/
theorem k1_second_fits (P : K1.Par) (as : List Fmt.Ext3) (h : as.length = P.answers) :
    (⟨as.map fun a => .answer (toE a), []⟩ : Sending).fits { entry := K1.answerEntry P } [] =
      true := by
  have e : (({ entry := K1.answerEntry P } : Fmt.DeclaredRound).items.filter (· != .root)) =
      List.replicate P.answers .answer := by
    simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, K1.answerEntry]
  unfold Sending.fits
  rw [e, ← h]
  simp [Said.got, itemOf, Function.comp_def]

/-- The stops of placeHalf's row never stop. -/
theorem k1_row_silent (wit : W → PlaceIn Xi) (J : SendJob (PlaceIn Xi) X) (v : Option V)
    (loc ds : List Fmt.Drawn) : rowStopAt v (placeHalf (V := V) wit J).parts loc ds = none := by
  cases v <;> simp [placeHalf, rowStopAt, Part.stopAt, Part.lift, sendPart]

/-- **THE TERM: the member's two rounds as played.** c: the part's own coins. A SECOND TEXT of
sendPart's two messages: sendPart's own calls at sendPart's own arguments. ITS FIRST RECORD HOLDS
THE TABLES WHOLE: what is SENT as an oracle, not what a verifier is shown. THE 0 BENEATH THE HELD
WORDS: NO COIN: A CONSTANT; never read at the job's own messages (answers_any,
Honest/K1/Law/SendAtBlock.lean). seen: what the first move is handed: the rounds shown and the
opened columns (Seen); the second move is handed seen.plus of the first round: the columns as they
were. -/
def playedK1 (name : String) (wit : W → W') (J : SendJob W' X) (c : Cs (dueR J.P J.ride))
    (t : State W X) (seen : Seen) (d₀ d₁ : Fmt.Drawn) : List Played :=
  [⟨name, J.P.place, 0, true, [],
      (treeTables J.P (J.rows c seen (t.narrow wit id) 0)).map some, d₀⟩,
   ⟨name, J.P.place, 0, true,
      ((answers J.P (stAt J.P J.first) J.first
          (Johnson.Prover.Send.held (fun _ _ _ => 0) J.first J.P
            (J.rows c (seen.plus [⟨[], d₀⟩]) ((t.hears d₀).narrow wit id) 1))
          (seedsAt J.P [d₀])).map fun a => Said.got (.answer (toE a))), [], d₁⟩]

/-- The last challenge heard. -/
theorem lately_hears (wit : W → W') (t : State W X) (d : Fmt.Drawn) :
    ((t.hears d).narrow wit id).lately 1 = [d] := by
  show (t.heard ++ [d]).drop ((t.heard ++ [d]).length - 1) = [d]
  rw [List.length_append, List.length_singleton, Nat.add_sub_cancel, List.drop_left]

/-- **THE TIE**: under the two public tests the frame's terms for a row return the term, and every
message fits its round: at each value of the coins. -/
theorem played_k1 (name : String) (wit : W → PlaceIn Xi) (J : SendJob (PlaceIn Xi) X)
    (hf : sendFits J.P J.ride = true) (c : RowCoins (placeHalf (V := V) wit J).parts)
    (t : State W X) (seen : Seen) (d₀ d₁ : Fmt.Drawn)
    (hd : drawsFit (K1.rounds J.P) [d₀, d₁] = true) :
    playedRow name J.P.place (placeHalf (V := V) wit J).parts 0 c t seen [d₀, d₁] =
        some (playedK1 name wit J c.1.1 t seen d₀ d₁) ∧
      fitsRow (placeHalf (V := V) wit J).parts ((K1.rounds J.P).zip (K1.oracles J.P)) c t seen
        [d₀, d₁] = true := by
  have hs : seedsFit J.P [d₀] = true := by
    obtain ⟨a, b, e, h⟩ := k1_draws_two J.P _ hd
    cases e
    exact h
  have hl := lately_hears wit t d₀
  have f1 := k1_first_fits J.P (J.rows c.1.1 seen (t.narrow wit id) 0)
  have f2 := k1_second_fits J.P _ (Johnson.Prover.Send.length_answers J.P (stAt J.P J.first) J.first
    (Johnson.Prover.Send.held (fun _ _ _ => 0) J.first J.P
      (J.rows c.1.1 (seen.plus [⟨[], d₀⟩]) ((t.hears d₀).narrow wit id) 1)) (seedsAt J.P [d₀]))
  have he : (⟨(t.hears d₀).input, (t.hears d₀).heard,
      (State.narrow wit id (t.hears d₀)).own⟩ : State W X) = t.hears d₀ := rfl
  constructor
  · simp [placeHalf, playedRow, playedFrom, Part.lift, Move.lift, sendPart, playedK1, hf, he, hl,
      hs, stateFrom, roundsOf]
  · simp [placeHalf, fitsRow, fitsFrom, Part.lift, Move.lift, sendPart, hf, he, hl, hs, stateFrom,
      aloneFrom, K1.rounds, K1.oracles]
    exact ⟨f1, f2⟩

/-- **THE MEMBER's PLAY AND ITS COLUMNS' LAYING RETURN**: the premise hmv of playsS_by_play
(Honest/Small/PlayedTo.lean), and more: NO THREAD IN FRONT AND NO SILENCE OF A STOP IS ASKED.
General in the thread. -/
theorem k1_moved (T : Thread Bk S Cl V W X Pb) (blk : Block S Cl)
    (wit : W → PlaceIn Xi) (J : SendJob (PlaceIn Xi) X)
    (hsh : blk.place = J.P.place ∧ blk.rounds = K1.rounds J.P ∧ blk.oracles = K1.oracles J.P)
    (hh : (T.hs.find? fun g => g.place == J.P.place) = some (placeHalf wit J))
    (hf : sendFits J.P J.ride = true) :
    ∀ k m E ds l, drawsFit blk.rounds ds = true →
      chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) [blk] T.hs = .ok l →
      ∃ y, T.Moved blk k m E ds y [] := by
  intro k m E ds l hd hl
  obtain ⟨hp, hr, ho⟩ := hsh
  have hf' : (T.hs.find? fun g => g.place == blk.place) = some (placeHalf wit J) := by
    rw [hp]
    exact hh
  have hl₀ := hl
  obtain ⟨c, -, rfl⟩ := steps_one_half hf' hl
  rw [hr] at hd
  obtain ⟨d₀, d₁, rfl, -⟩ := k1_draws_two J.P ds hd
  obtain ⟨h1, h2⟩ := played_k1 (V := V) blk.name wit J hf c m.st m.shown d₀ d₁ hd
  obtain ⟨y, hy⟩ : ∃ y, play (rowSteps blk.name J.P.place (T.φ.sees m.st.input)
      (placeHalf wit J).parts 0 ((K1.rounds J.P).zip (K1.oracles J.P)) c) [d₀, d₁] [] m = .ok y :=
    ⟨_, play_row_whole blk.name J.P.place (T.φ.sees m.st.input) (placeHalf wit J).parts 0
      ((K1.rounds J.P).zip (K1.oracles J.P)) c [d₀, d₁] [] m _ (k1_row_silent wit J _ _ _) h2 h1⟩
  refine ⟨y, ?_⟩
  unfold Thread.Moved
  refine ⟨⟨_, hl₀, ?_⟩, ?_⟩
  · unfold Placed.steps
    rw [hp, hr, ho]
    exact hy
  · rw [hr]
    exact k1_cols_return _ _ _ _ _ _

/-- **And what is played is the term**, at the coins that the book lends. -/
theorem k1_moved_term (T : Thread Bk S Cl V W X Pb) (blk : Block S Cl)
    (wit : W → PlaceIn Xi) (J : SendJob (PlaceIn Xi) X)
    (hsh : blk.place = J.P.place ∧ blk.rounds = K1.rounds J.P ∧ blk.oracles = K1.oracles J.P)
    (hh : (T.hs.find? fun g => g.place == J.P.place) = some (placeHalf wit J))
    (hf : sendFits J.P J.ride = true) :
    ∀ k m E ds y cols, drawsFit blk.rounds ds = true → T.Moved blk k m E ds y cols →
      ∃ c d₀ d₁, lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) J.P.place
          (placeHalf (V := V) wit J).parts 0 = .ok c ∧ ds = [d₀, d₁] ∧ cols = [] ∧
        y.1 = playedK1 blk.name wit J c.1.1 m.st m.shown d₀ d₁ ∧
        y.2.st.input = m.st.input ∧ y.2.st.heard = m.st.heard ++ ds := by
  intro k m E ds y cols hd hM
  obtain ⟨hp, hr, ho⟩ := hsh
  have hf' : (T.hs.find? fun g => g.place == blk.place) = some (placeHalf wit J) := by
    rw [hp]
    exact hh
  unfold Thread.Moved at hM
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM
  obtain ⟨c, hc1, -, hpl, -, hy2⟩ := member_played hf' hl hy
  rw [hr] at hd hc
  obtain ⟨d₀, d₁, rfl, -⟩ := k1_draws_two J.P ds hd
  obtain ⟨h1, -⟩ := played_k1 (V := V) blk.name wit J hf c m.st m.shown d₀ d₁ hd
  rw [hp] at hpl hc1
  rw [k1_cols_return] at hc
  refine ⟨c, d₀, d₁, hc1, rfl, (Except.ok.inj hc).symm, Option.some.inj (hpl.symm.trans h1), ?_, ?_⟩
  · rw [hy2]
    simp [placeHalf, stateRow, stateFrom, Part.lift, sendPart, State.hears]
  · rw [hy2]
    simp [placeHalf, stateRow, stateFrom, Part.lift, sendPart, State.hears]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1_reads_none
#print axioms ProofFile.Honest.K1.k1_cols_return
#print axioms ProofFile.Honest.K1.k1_draws_two
#print axioms ProofFile.Honest.K1.second_say
#print axioms ProofFile.Honest.K1.k1_first_fits
#print axioms ProofFile.Honest.K1.k1_second_fits
#print axioms ProofFile.Honest.K1.k1_row_silent
#print axioms ProofFile.Honest.K1.playedK1
#print axioms ProofFile.Honest.K1.lately_hears
#print axioms ProofFile.Honest.K1.played_k1
#print axioms ProofFile.Honest.K1.k1_moved
#print axioms ProofFile.Honest.K1.k1_moved_term
