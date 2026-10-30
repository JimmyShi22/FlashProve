-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Xch/Coins.lean: the closing of a segment (K10): what the prover's side of the
closing's step shows, with the coins of the prover's part named. It holds three lemmas and no definition.

Words. A thread T (`Thread`, Honest/Thread/Thr.lean) is the structure of parameters of one chain's invariant; T is a
variable throughout. A job J (`CloseJob`, Honest/K10/Job.lean) is the structure of a closing's parameters at a place;
`J.pub.par.k` is its number of rounds "FOLD round". The part is `closePart (foldShellT true J foldWords)`
(Honest/K10/Half.lean, Sim.lean): the honest prover's moves for the closing's 2 + `J.pub.par.k` rounds, in the form
that never refuses. The book Bk (`ProverCoinCounts`, Honest/Frame.lean) is public data: which parts have coins of their own, and
how many; and the entries: blocks of one part's coins that another part is given, to spend or to carry. The run's
coins are k : `Coins Bk`: the coins of one run, typed by the book. The part's coins are a value c of the type
`(closePart …).Coins`: what the frame hands to this part. The lemmas name two things of c: the run that the part
spends, `spentRun J (handSnd c)`, and the runs that it carries, `(handSnd c).2.2`.

Why. `moved_close` (Honest/K10/Thr/Plays.lean) says what the played rounds show "for some value c of the part's
coins". A premise on what the part spends or carries cannot be stated at a c that has no name. Here c is the value of
`closeCoins` (Honest/K10/Fast/Says.lean): what the frame's `lendRow` (Honest/Frame.lean) gives the part at the block's
place, from the book itself, from its table for the thread's chain (`Bk.rowsOf T.chain`) and from the run's coins as
that chain may read them (`k.look T.chain`).

What is proved.
  **`moved_close_at`**
                      Premises. hr, ho: the block's rounds and oracle messages are the first and the second members of
                      `closeRounds J.pub.par`. hh: the first member of T.hs at the block's place has the part as its
                      one part. hd: the challenges ds are such as the block's rounds can draw. hM: the prover's side
                      of the block's step is given (`Thread.Moved`, Honest/Thread/Pays.lean). Conclusion. `closeCoins`
                      returns a value c at the block's place, and at this c the conclusion of `moved_close` holds: ds
                      is d0, d1 and `J.pub.par.k` more; no column is read; the played rounds carry these challenges;
                      played round number i shows the items of `saysAt` at i, taken at `askZero`
                      (Honest/K10/SimSent.lean: the closing's data, made at the runs that c carries and with 0 for
                      each coin of the run that is spent) and at the run that c spends
  `moved_close_of`    the same at a c that the caller hands in together with the equation `closeCoins … = .ok c`
  `moved_at_closing`  `moved_close_at` from the structure `CloseAt T b c Z l p blk J` (Honest/K10/Thr/CloseAt.lean),
                      which gives hr, ho and hh. In that structure the letter c is a chain, so the coins are written
                      cc. The place is written `closePlace J.pub.par`, which names no block

By what. `steps_close_at` (Fast/Says.lean) in the place of `steps_close`; then the proof of `moved_close`, line by
line: `close_draws` and `plays_is` (Honest/K10/SimSent.lean), `close_zip` and `close_reads` (Thr/Plays.lean),
`play_yields` (Honest/Law/Play.lean), `yields_drawn` (Honest/Law/Run.lean).

Limits. hr, ho, hh, hd, hM and `CloseAt` are premises: none is proved here of any thread. That `closeCoins` returns is
drawn from hM, which contains that `chainSteps` (Honest/Frame.lean) returns for the block: where `chainSteps` returns
an error, hM is false and all three lemmas hold vacuously. Which of the run's coins the value c holds is not said:
`lendRow` is not unfolded. J is a variable, and nothing is asked of `J.stAt` or `J.rows`: where `askZero` is `none`,
the items are those of `saysAt` at empty tables, as in `moved_close`. Nothing is said on the block's own step or on
the verifier's state after it. Nothing is shown of a run of the protocol. No property of the protocol is claimed:
nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Thr.Plays
import Johnson.Desc.ProofFile.Honest.K10.Fast.Says

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par entries)

variable {V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **Where the prover's side of the closing's step is given, `closeCoins` returns at the block's place**, and at the
coins c that it returns: there are 2 + `J.pub.par.k` challenges; no column is read; the played rounds carry the
challenges; and played round i shows the items of `saysAt` at i, taken at `askZero` of the state m of the prover's run
before the block. -/
theorem moved_close_at {S' Cl : Type} (T : Thread Bk S' Cl V W X Pb) (J : CloseJob W) (blk : Block S' Cl)
    (hr : blk.rounds = (closeRounds J.pub.par).map (·.1)) (ho : blk.oracles = (closeRounds J.pub.par).map (·.2))
    (hh : ∃ g, (T.hs.find? fun h => h.place == blk.place) = some g ∧
      g.parts = [closePart (foldShellT true J foldWords)])
    (k : Coins Bk) (m : Mid W X) (En : Env) (ds : List Fmt.Drawn) (y : List Played × Mid W X) (cols : List OpenedColumn)
    (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m En ds y cols) :
    ∃ (d0 d1 : Fmt.Drawn) (gs : List Fmt.Drawn)
      (c : (closePart (V := V) (X := X) (foldShellT true J foldWords)).Coins),
      closeCoins (V := V) (X := X) Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place J = .ok c ∧
        ds = d0 :: d1 :: gs ∧ gs.length = J.pub.par.k ∧ cols = [] ∧
        (roundsOf y.1).map (·.drawn) = ds ∧
        (roundsOf y.1).map (·.vals) = (List.range (2 + J.pub.par.k)).map fun i =>
          (saysAt J (askZero J m.st.input m.shown m.st.heard d0 (handSnd c).2.2) (spentRun J (handSnd c)) d1 gs
            i).vals.map Said.got := by
  obtain ⟨⟨l, hl, hp⟩, hc⟩ := hM
  rw [hr] at hd
  obtain ⟨d0, d1, gs, rfl, hk, h1⟩ := close_draws J.pub.par ds hd
  obtain ⟨c, hcc, rfl⟩ := steps_close_at Bk J _ _ _ blk T.hs l (close_zip J.pub.par blk hr ho) hh hl
  obtain ⟨y', hy', e⟩ :=
    plays_is J blk.name ⟨blk.place, 0⟩ (T.φ.sees m.st.input) c m d0 d1 gs hk h1 _ rfl
  have ey : y = y' := Except.ok.inj (hp.symm.trans hy')
  rw [← ey] at e
  rw [hr, close_reads] at hc
  refine ⟨d0, d1, gs, c, hcc, rfl, hk, (Except.ok.inj hc).symm,
    yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hp), ?_⟩
  have e2 := congrArg (List.map Prod.fst) e
  rw [List.map_map, List.map_map] at e2
  unfold roundsOf
  rw [List.map_map]
  exact e2

/-- The same at coins c that the caller hands in together with the equation hc: `closeCoins` returns c at the block's
place. -/
theorem moved_close_of {S' Cl : Type} (T : Thread Bk S' Cl V W X Pb) (J : CloseJob W) (blk : Block S' Cl)
    (hr : blk.rounds = (closeRounds J.pub.par).map (·.1)) (ho : blk.oracles = (closeRounds J.pub.par).map (·.2))
    (hh : ∃ g, (T.hs.find? fun h => h.place == blk.place) = some g ∧
      g.parts = [closePart (foldShellT true J foldWords)])
    (k : Coins Bk) (m : Mid W X) (En : Env) (ds : List Fmt.Drawn) (y : List Played × Mid W X) (cols : List OpenedColumn)
    (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m En ds y cols)
    (c : (closePart (V := V) (X := X) (foldShellT true J foldWords)).Coins)
    (hc : closeCoins (V := V) (X := X) Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place J = .ok c) :
    ∃ (d0 d1 : Fmt.Drawn) (gs : List Fmt.Drawn),
      ds = d0 :: d1 :: gs ∧ gs.length = J.pub.par.k ∧ cols = [] ∧
        (roundsOf y.1).map (·.drawn) = ds ∧
        (roundsOf y.1).map (·.vals) = (List.range (2 + J.pub.par.k)).map fun i =>
          (saysAt J (askZero J m.st.input m.shown m.st.heard d0 (handSnd c).2.2) (spentRun J (handSnd c)) d1 gs
            i).vals.map Said.got := by
  obtain ⟨d0, d1, gs, c', hc', h⟩ := moved_close_at T J blk hr ho hh k m En ds y cols hd hM
  have ec : c' = c := Except.ok.inj (hc'.symm.trans hc)
  subst ec
  exact ⟨d0, d1, gs, h⟩

section
variable {T : Thread Bk S ProofFile.Cl V W X Pb} {b : Nat} {c : Chain S ProofFile.Cl} {Z : ProofFile.Pub} {l : Nat}
  {p : VerifiableInference.Desc.K9.Where} {blk : Block S ProofFile.Cl} {J : CloseJob W}

/-- **`moved_close_at` from the premises on the thread's fields that the structure `CloseAt` holds**, with the closing's
place written by the job's numbers. The part's coins are written cc, because c is the chain here. -/
theorem moved_at_closing (H : CloseAt T b c Z l p blk J) (k : Coins Bk) (m : Mid W X) (En : Env)
    (ds : List Fmt.Drawn) (y : List Played × Mid W X) (cols : List OpenedColumn) (hd : drawsFit blk.rounds ds = true)
    (hM : T.Moved blk k m En ds y cols) :
    ∃ (d0 d1 : Fmt.Drawn) (gs : List Fmt.Drawn)
      (cc : (closePart (V := V) (X := X) (foldShellT true J foldWords)).Coins),
      closeCoins (V := V) (X := X) Bk (Bk.rowsOf T.chain) (k.look T.chain) (closePlace J.pub.par) J = .ok cc ∧
        ds = d0 :: d1 :: gs ∧ gs.length = J.pub.par.k ∧ cols = [] ∧
        (roundsOf y.1).map (·.drawn) = ds ∧
        (roundsOf y.1).map (·.vals) = (List.range (2 + J.pub.par.k)).map fun i =>
          (saysAt J (askZero J m.st.input m.shown m.st.heard d0 (handSnd cc).2.2) (spentRun J (handSnd cc)) d1 gs
            i).vals.map Said.got := by
  obtain ⟨-, -, -, -, -, hp, hr, ho⟩ := H.tied
  have e := moved_close_at T J blk hr ho H.halfAt k m En ds y cols hd hM
  rw [hp] at e
  exact e

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.moved_close_at
#print axioms ProofFile.Honest.K10.moved_close_of
#print axioms ProofFile.Honest.K10.moved_at_closing
