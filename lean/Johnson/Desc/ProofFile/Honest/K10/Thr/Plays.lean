-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Thr/Plays.lean: the closing of a segment (K10): `Plays T b` (Honest/Thread/Pays.lean)
and `PlaysS T Said b` (Honest/Thread/PaysS.lean) are proved at the closing's block, from named hypotheses on the fields
of the thread T. T is a variable throughout. No definition; thirteen theorems.

What `Plays T b` says, of block number b of T's list: from the invariant `Thr T b` before the block, at all coins, at
every list of challenges that the block's rounds can draw and at which none of its stops fires, and where `chainSteps`
(Honest/Frame.lean) returns for the block: the frame's `play` returns, the columns that the rounds read are filled, and
each tree that is new after the block shows what the thread's table shows. `PlaysS` asks the same from `Thr` together
with a second condition Said.

  `close_firsts`, `close_seconds`, `close_zip`   `closeRounds P` (Honest/K10/Sim.lean) is a list of pairs. Its first
                    members are the kind's entries, each as a round that opens no tree; its second members are empty
                    lists of oracle messages. A block whose rounds are the first members (hr) and whose oracle messages
                    are the second (ho) has `closeRounds P` as the two lists zipped
  `reads_entries`, `close_reads`   rounds that are made of an entry alone read no column (`readsOf`, Honest/Frame.lean),
                    at any challenges and any tables; so the closing's rounds read none
  `flat_nils`, `close_noTrees`   the closing's rounds declare no oracle message
  `no_fresh`        at any thread, at a block of its list (hblk) that declares no oracle message (ho): no tree's source
                    is new after it, so the clause on new trees (`Thread.Trees` at `Thread.fresh`) holds vacuously. The
                    proof is the last step of `plays_quiet` (Honest/Thread/QuietLaw.lean)
  `steps_close`     at a block whose rounds and oracle messages, zipped, are `closeRounds J.pub.par` (hz), and at whose
                    place the first prover's side in the list has the one part `closePart (foldShellT true J foldWords)`
                    (hh): where `chainSteps` returns for this one block (hl), its value is that part's 2 + k steps
                    (`Part.steps`) at the block's name, the address (the block's place, part 0) and
                    `closeRounds J.pub.par`, for some value of the part's coins. k is `J.pub.par.k`
  **`moved_close`**   at such a block (hr, ho, hh), at challenges that its rounds can draw (hd), and where the prover's
                    side of the block's step is given (hM: `Thread.Moved`): the challenges are d0, d1 and k more; no
                    column is read; the played rounds carry these challenges (`yields_drawn`, Honest/Law/Run.lean); and
                    played round number i shows the items of `saysAt` at i, taken at `askZero` of the state of the
                    prover's run before the block (`plays_is`, Honest/K10/SimSent.lean). The part's coins c stand behind
                    ∃: `askZero` is at c's carried runs, `saysAt` at c's spent run, and nothing here ties c to the run's
                    coins k
  **`close_plays_of`**   `Plays T b`, at any type of the verifier's state, from four hypotheses on T's fields. hblk:
                    T.bs[b]? = some blk. hr, ho: blk's rounds and oracle messages are the first and the second members
                    of `closeRounds J.pub.par`. hh: the first prover's side of T.hs at blk's place has the one part
                    `closePart (foldShellT true J foldWords)`
  **`close_plays`**, **`close_playsS`**   `Plays T b`, and `PlaysS T Said b` at every Said, from the structure
                    `CloseAt T b c Z l p blk J` (Honest/K10/Thr/CloseAt.lean), from which the four follow: by
                    `CloseAt.blkAt`, `CloseAt.halfAt` and the last two clauses of `Tied` (Honest/K10/SimLot.lean);
                    then `playsS_of`

By what. That `play` returns, and what the played rounds show, is `plays_is`; their challenges are `play_yields`
(Honest/Law/Play.lean) with `yields_drawn`. `play`, `Step.tell` and `Step.hear` are not unfolded here. `steps_close`
unfolds `chainSteps`, `Placed.steps` and `rowSteps`.

Limits. The hypotheses named above, and `CloseAt`, are hypotheses: none is proved here of any thread. J is a variable,
and nothing is asked of `J.stAt` or `J.rows`: the theorems hold as well at a job whose `stAt` always returns an error,
because no move of `foldShellT true` can return one (the head of SimSent.lean); `askZero` is then `none`, and `saysAt`
is taken at empty tables. So `Plays T b` does not distinguish a part that has the closing's data from a part that has
none. Two hypotheses of `Plays` are not used by the proof: the invariant `Thr T b`, and that no stop fires. A third is
used: that `chainSteps` returns. Where the book has no cut for the place, or does not give the part its runs,
`Plays T b` holds vacuously. Nothing is proved of a run of the protocol. Nothing on the block's own step, on what holds
after it, or on the items that its row owes. No property of the protocol is claimed: nothing is said on its soundness,
completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Thr.CloseAt
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par entries)

variable {V W X Pb : Type} {Bk : ProverCoinCounts}

/-! ## The closing's two lists -/

/-- The first members of the closing's declared rounds are the kind's entries, each as a round that opens nothing. -/
theorem close_firsts (P : Par) :
    (entries P).map (fun e => ({ entry := e } : Fmt.DeclaredRound)) = (closeRounds P).map (·.1) := by
  unfold closeRounds
  rw [List.map_map]
  rfl

/-- The second members of the closing's declared rounds are empty lists of oracle messages. -/
theorem close_seconds (P : Par) :
    (entries P).map (fun _ => ([] : List Oracle)) = (closeRounds P).map (·.2) := by
  unfold closeRounds
  rw [List.map_map]
  rfl

/-- A block whose rounds and oracle messages are these two lists has the closing's declared rounds as the two zipped. -/
theorem close_zip {S' Cl : Type} (P : Par) (blk : Block S' Cl) (hr : blk.rounds = (closeRounds P).map (·.1))
    (ho : blk.oracles = (closeRounds P).map (·.2)) : blk.rounds.zip blk.oracles = closeRounds P := by
  rw [hr, ho, List.zip_map']
  exact List.map_id' _

/-! ## No column is read; no tree is new -/

/-- Rounds that are made of an entry alone read no column, at any challenges and any tables. -/
theorem reads_entries (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) : ∀ (es : List Fmt.Entry) (ds : List Fmt.Drawn),
    readsOf chain ft stored tree (es.map fun e => ({ entry := e } : Fmt.DeclaredRound)) ds = []
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | _ :: es, _ :: ds => by
      show ([] : List Read) ++ [] ++
        readsOf chain ft stored tree (es.map fun e => ({ entry := e } : Fmt.DeclaredRound)) ds = []
      rw [reads_entries chain ft stored tree es ds, List.append_nil, List.append_nil]

/-- The closing's rounds read no column. -/
theorem close_reads (P : Par) (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (ds : List Fmt.Drawn) :
    readsOf chain ft stored tree ((closeRounds P).map (·.1)) ds = [] := by
  rw [← close_firsts P]
  exact reads_entries chain ft stored tree (entries P) ds

/-- One empty list for each entry, concatenated, is the empty list. -/
theorem flat_nils : ∀ es : List Fmt.Entry, es.flatMap (fun _ => ([] : List Oracle)) = []
  | [] => rfl
  | _ :: es => by rw [List.flatMap_cons, flat_nils es, List.append_nil]

/-- The closing's rounds declare no oracle message. -/
theorem close_noTrees (P : Par) : ((closeRounds P).map (·.2)).flatMap id = [] := by
  rw [← close_seconds P, flatMap_id_map]
  exact flat_nils (entries P)

/-- After a block that declares no oracle message no tree's source is new: the clause on new trees holds vacuously. -/
theorem no_fresh {S' Cl : Type} (T : Thread Bk S' Cl V W X Pb) {b : Nat} {blk : Block S' Cl}
    (hblk : T.bs[b]? = some blk) (ho : blk.oracles.flatMap id = []) (k : Coins Bk) (m : Mid W X) (E : Env) :
    T.Trees (T.fresh b) k m E := by
  intro σ hσ
  have e : T.hand (b + 1) = T.hand b := by
    unfold Thread.hand
    rw [treesTo_succ hblk, ho, List.length_nil, Nat.add_zero]
  obtain ⟨h1, h2⟩ := List.mem_filter.1 hσ
  rw [e] at h1
  simp [h1] at h2

/-! ## What `chainSteps` returns for the block -/

/-- Where `chainSteps` returns for the closing's block alone, its value is the part's steps, for some value of the
part's coins. -/
theorem steps_close {S' Cl : Type} (J : CloseJob W) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (blk : Block S' Cl) (hs : List (Placed V W X)) (l : List (Step W X))
    (hz : blk.rounds.zip blk.oracles = closeRounds J.pub.par)
    (hh : ∃ g, (hs.find? fun h => h.place == blk.place) = some g ∧
      g.parts = [closePart (foldShellT true J foldWords)])
    (hl : chainSteps Bk rows look v [blk] hs = .ok l) :
    ∃ c : (closePart (V := V) (X := X) (foldShellT true J foldWords)).Coins,
      l = (closePart (foldShellT true J foldWords)).steps blk.name ⟨blk.place, 0⟩ (closeRounds J.pub.par) v c := by
  obtain ⟨⟨gp, gparts⟩, hg, hparts⟩ := hh
  have hparts' : gparts = [closePart (foldShellT true J foldWords)] := hparts
  subst hparts'
  unfold chainSteps at hl
  rw [hg] at hl
  simp only at hl
  split at hl
  · exact nomatch hl
  split at hl
  · exact nomatch hl
  split at hl
  · exact nomatch hl
  split at hl
  · exact nomatch hl
  split at hl
  · exact nomatch hl
  cases hc : lendRow Bk rows look blk.place
      ([closePart (foldShellT true J foldWords)] : List (Part V W X)) 0 with
  | error e => rw [hc] at hl; exact nomatch hl
  | ok c =>
    rw [hc] at hl
    have e : l = (⟨gp, [closePart (foldShellT true J foldWords)]⟩ : Placed V W X).steps blk v c ++ [] :=
      (Except.ok.inj hl).symm
    refine ⟨c.1, ?_⟩
    rw [e, List.append_nil]
    unfold Placed.steps
    rw [hz]
    show (closePart (foldShellT true J foldWords) : Part V W X).steps blk.name ⟨blk.place, 0⟩
      ((closeRounds J.pub.par).take (closePart (V := V) (X := X) (foldShellT true J foldWords)).moves.length) v
      c.1 ++ [] = _
    rw [List.append_nil, moves_len, List.take_length]

/-! ## The prover's side of the block's step -/

/-- **Where the prover's side of the closing's step is given**: there are 2 + k challenges; no column is read; the
played rounds carry the challenges; and played round i shows the items of `saysAt` at i, taken at `askZero` of the state
of the prover's run before the block. -/
theorem moved_close {S' Cl : Type} (T : Thread Bk S' Cl V W X Pb) (J : CloseJob W) (blk : Block S' Cl)
    (hr : blk.rounds = (closeRounds J.pub.par).map (·.1)) (ho : blk.oracles = (closeRounds J.pub.par).map (·.2))
    (hh : ∃ g, (T.hs.find? fun h => h.place == blk.place) = some g ∧
      g.parts = [closePart (foldShellT true J foldWords)])
    (k : Coins Bk) (m : Mid W X) (En : Env) (ds : List Fmt.Drawn) (y : List Played × Mid W X) (cols : List OpenedColumn)
    (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m En ds y cols) :
    ∃ (d0 d1 : Fmt.Drawn) (gs : List Fmt.Drawn)
      (c : (closePart (V := V) (X := X) (foldShellT true J foldWords)).Coins),
      ds = d0 :: d1 :: gs ∧ gs.length = J.pub.par.k ∧ cols = [] ∧
        (roundsOf y.1).map (·.drawn) = ds ∧
        (roundsOf y.1).map (·.vals) = (List.range (2 + J.pub.par.k)).map fun i =>
          (saysAt J (askZero J m.st.input m.shown m.st.heard d0 (handSnd c).2.2) (spentRun J (handSnd c)) d1 gs
            i).vals.map Said.got := by
  obtain ⟨⟨l, hl, hp⟩, hc⟩ := hM
  rw [hr] at hd
  obtain ⟨d0, d1, gs, rfl, hk, h1⟩ := close_draws J.pub.par ds hd
  obtain ⟨c, rfl⟩ := steps_close J _ _ _ blk T.hs l (close_zip J.pub.par blk hr ho) hh hl
  obtain ⟨y', hy', e⟩ :=
    plays_is J blk.name ⟨blk.place, 0⟩ (T.φ.sees m.st.input) c m d0 d1 gs hk h1 _ rfl
  have ey : y = y' := Except.ok.inj (hp.symm.trans hy')
  rw [← ey] at e
  rw [hr, close_reads] at hc
  refine ⟨d0, d1, gs, c, rfl, hk, (Except.ok.inj hc).symm,
    yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hp), ?_⟩
  have e2 := congrArg (List.map Prod.fst) e
  rw [List.map_map, List.map_map] at e2
  unfold roundsOf
  rw [List.map_map]
  exact e2

/-! ## It plays -/

/-- **`Plays` holds at a block that has the closing's rounds and at whose place the first prover's side has the
closing's part alone.** The invariant before the block is not used. -/
theorem close_plays_of {S' Cl : Type} (T : Thread Bk S' Cl V W X Pb) (J : CloseJob W) {b : Nat}
    {blk : Block S' Cl} (hblk : T.bs[b]? = some blk)
    (hr : blk.rounds = (closeRounds J.pub.par).map (·.1)) (ho : blk.oracles = (closeRounds J.pub.par).map (·.2))
    (hh : ∃ g, (T.hs.find? fun h => h.place == blk.place) = some g ∧
      g.parts = [closePart (foldShellT true J foldWords)]) :
    Plays T b := by
  intro blk' hblk' k s m E ds l _ hd _ hl
  rw [hblk] at hblk'
  cases hblk'
  rw [hr] at hd
  obtain ⟨d0, d1, gs, rfl, hk, h1⟩ := close_draws J.pub.par ds hd
  obtain ⟨c, hc⟩ := steps_close J _ _ _ blk T.hs l (close_zip J.pub.par blk hr ho) hh hl
  obtain ⟨y, hy, -⟩ :=
    plays_is J blk.name ⟨blk.place, 0⟩ (T.φ.sees m.st.input) c m d0 d1 gs hk h1 _ rfl
  have hn : blk.oracles.flatMap id = [] := by rw [ho, close_noTrees]
  refine ⟨y, [], ?_, no_fresh T hblk hn k y.2 (E.add y.1)⟩
  unfold Thread.Moved
  refine ⟨⟨l, hl, ?_⟩, ?_⟩
  · rw [hc]
    exact hy
  · rw [hr, close_reads]
    rfl

/-! ## From the structure `CloseAt` -/

section
variable {T : Thread Bk S ProofFile.Cl V W X Pb} {b : Nat} {c : Chain S ProofFile.Cl} {Z : ProofFile.Pub} {l : Nat}
  {p : VerifiableInference.Desc.K9.Where} {blk : Block S ProofFile.Cl} {J : CloseJob W}

/-- **`Plays` holds at the closing's block**, from the hypotheses on the thread's fields that `CloseAt` holds. -/
theorem close_plays (H : CloseAt T b c Z l p blk J) : Plays T b := by
  obtain ⟨-, -, -, -, -, -, hr, ho⟩ := H.tied
  exact close_plays_of T J H.blkAt hr ho H.halfAt

/-- **`PlaysS` holds at the closing's block**, at every second condition Said. -/
theorem close_playsS (H : CloseAt T b c Z l p blk J) (Said : Nat → Coins Bk → Mid W X → Prop) :
    PlaysS T Said b :=
  playsS_of T Said (close_plays H)

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.close_firsts
#print axioms ProofFile.Honest.K10.close_seconds
#print axioms ProofFile.Honest.K10.close_zip
#print axioms ProofFile.Honest.K10.reads_entries
#print axioms ProofFile.Honest.K10.close_reads
#print axioms ProofFile.Honest.K10.flat_nils
#print axioms ProofFile.Honest.K10.close_noTrees
#print axioms ProofFile.Honest.K10.no_fresh
#print axioms ProofFile.Honest.K10.steps_close
#print axioms ProofFile.Honest.K10.moved_close
#print axioms ProofFile.Honest.K10.close_plays_of
#print axioms ProofFile.Honest.K10.close_plays
#print axioms ProofFile.Honest.K10.close_playsS
