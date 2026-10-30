-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/SimPlay.lean: the closing of a segment (K10): four general lemmas: three for
Honest/K10/Sim.lean's (3b), one (`verdict_run`) for its (4'').

  **`ask_run`**     the closing's data read the run at one place alone: at every job: `closeAsk` at a run u is
                   `closeAsk` at any other run, with the field that holds the run laid anew: the same end,
                   the same tables
  `verdict_run`   so which of the three ends is taken (`askVerdict`, Sim.lean) is one at any two runs: the run's half of
                   Sim.lean's (4''), at every job; of the input and the carried runs it says nothing; nor of the law
                   that the job's statement is one, which goes with (4'')
  `play_all`      the frame's `play` forwards, round by round, over a list of rounds none of which stops and each of
                   which says a message of the stated shape: `play` returns, and the played rounds' items in the clear
                   and tables are those that Z names; nothing on where the play stands behind the last round, nor on a
                   played round's name, place, part, challenge or mark `told`. Premises: as many challenges as rounds;
                   no stored run; each round has a move. By the frame's `play_step` (Honest/Law/ToyPlay.lean). General:
                   it names no kind
  `askAt_is`      what the fold's move number n is handed (`closeAskAt`, Honest/K10/Job.lean), at a stand that is
                   written out

Limits. None of the four names a part, a side or a law on coins. `ask_run` is by the text of `closeAsk`: by type no
field of a job is handed the run. No property of the protocol is claimed: nothing is said on its soundness,
completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Sim
import Johnson.Desc.ProofFile.Honest.Law.ToyPlay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (E zeroE)
open VerifiableInference VerifiableInference.Desc

variable {W X : Type}

/-- **The closing's data read the run at one place alone**: at another run the end is the same, and the data are the
same but for the field that holds the run. -/
theorem ask_run (J : CloseJob W) (w : W) (seen : Seen) (front : List Fmt.Drawn) (x : Fmt.Drawn)
    (u u' : Fin (2 * J.pub.par.k + 1) → E) (ca : CsAll (closeCarries J.pub)) :
    closeAsk J w seen front x u ca =
      (closeAsk J w seen front x u' ca).map fun o => o.map fun A =>
        ({ k := J.pub.par.k, h := J.pub.par.h, c := A.c, d := A.d, m := A.m, mu := A.mu,
           keptV := A.keptV, w := u } : FoldAsk) := by
  unfold closeAsk
  simp only [bind, Except.bind, pure, Except.pure]
  repeat' split
  all_goals rfl

/-- **No end reads the run**: which of the three ends the making of the data takes is one at any two runs. -/
theorem verdict_run (J : CloseJob W) (w : W) (seen : Seen) (front : List Fmt.Drawn) (x : Fmt.Drawn)
    (u u' : Fin (2 * J.pub.par.k + 1) → E) (ca : CsAll (closeCarries J.pub)) :
    askVerdict J w seen front x u ca = askVerdict J w seen front x u' ca := by
  unfold askVerdict
  rw [ask_run J w seen front x u u' ca]
  cases closeAsk J w seen front x u' ca with
  | error e => rfl
  | ok o => cases o <;> rfl

/-- **A run of `play`, round by round, forwards**: M: where the play stands in front of round i; Z: what round i says.
Where there are as many challenges as rounds, no stored run, each round has a move, no round stops, round i says Z i, a
message of the stated shape, and M (i + 1) is M i behind round i: `play` returns, and the played rounds' items in the
clear and tables are Z's. -/
theorem play_all : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (M : Nat → Mid W X) (Z : Nat → Sending),
    ss.length = ds.length →
    (∀ i s d, ss[i]? = some s → ds[i]? = some d →
      (∀ f o, s.bad f o = none) ∧ (∀ f o, s.hid f o = none) ∧ ∃ mv, s.move = some mv ∧
        mv.say () (M i).shown (M i).st = .ok (Z i) ∧ (Z i).fits s.decl s.oracles = true ∧
        M (i + 1) = (M i).after mv ((Z i).vals.map Said.got) d) →
    ∃ y, play ss ds [] (M 0) = .ok y ∧
      y.1.map (fun p => (p.vals, p.tables)) =
        (List.range ss.length).map fun i => ((Z i).vals.map Said.got, (Z i).tables.map some)
  | [], [], M, Z, _, _ => ⟨([], M 0), play_nil _, rfl⟩
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | s :: ss, d :: ds, M, Z, h, H => by
      obtain ⟨hb, hh, mv, hmv, hz, hf, hM⟩ := H 0 s d rfl rfl
      obtain ⟨y, hy, e⟩ := play_all ss ds (fun i => M (i + 1)) (fun i => Z (i + 1))
        (by simpa using h) (fun i s' d' h1 h2 => H (i + 1) s' d' (by simpa using h1) (by simpa using h2))
      refine ⟨(playedOf s (Z 0) d :: y.1, y.2), ?_, ?_⟩
      · rw [play_step hb hh hmv hz hf, ← hM]
        show (play ss ds [] (M (0 + 1))).map _ = _
        rw [hy]
        rfl
      · rw [List.map_cons, e, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
        rfl

/-- **What the fold's move number n is handed, at a stand that is written out**: heard: what was heard in front of the
part, "BAT"'s challenge, the fold's own n, each of which drew just one element (hg); shown: what was shown in front, and
n + 1 rounds more. -/
theorem askAt_is (J : CloseJob W) (n : Nat)
    (c : Handed ⟨0, 0⟩ (closeSpends J.pub.par) (closeCarries J.pub)) (s : Seen) (t : State W X)
    (h0 : List Fmt.Drawn) (d0 : Fmt.Drawn) (gs : List Fmt.Drawn) (r0 rs : List Fmt.RoundView)
    (ht : t.heard = h0 ++ d0 :: gs) (hn : gs.length = n) (hs : s.rounds = r0 ++ rs)
    (hr : rs.length = n + 1) (hg : ∀ g ∈ gs, g.elems.length = 1) :
    closeAskAt J n c s t =
      (closeAsk J t.input ⟨r0, s.opened⟩ h0 d0 (spentRun J c) c.2.2).map fun A =>
        A.map fun A => (A, drawnE gs) := by
  have e1 : t.heard.length - (n + 1) = h0.length := by
    rw [ht, List.length_append, List.length_cons, hn]
    omega
  have e2 : t.heard.drop h0.length = d0 :: gs := by rw [ht, List.drop_left]
  have e3 : t.heard.take h0.length = h0 := by rw [ht, List.take_left]
  have e4 : t.lately n = gs := by
    unfold State.lately
    have : t.heard.length - n = (h0 ++ [d0]).length := by
      rw [ht, List.length_append, List.length_append, List.length_cons, List.length_cons, hn,
        List.length_nil]
      omega
    rw [this, ht, show h0 ++ d0 :: gs = (h0 ++ [d0]) ++ gs by simp, List.drop_left]
  have e5 : s.rounds.take (s.rounds.length - (n + 1)) = r0 := by
    have : s.rounds.length - (n + 1) = r0.length := by
      rw [hs, List.length_append, hr]
      omega
    rw [this, hs, List.take_left]
  have e6 : ¬ t.heard.length < n + 1 := by
    rw [ht, List.length_append, List.length_cons, hn]
    omega
  have e7 : (!(gs.all fun g => g.elems.length == 1)) = false := by
    rw [Bool.not_eq_false', List.all_eq_true]
    intro g hgm
    rw [hg g hgm]
    rfl
  unfold closeAskAt closeCut Seen.front
  simp only [e1, e2, e3, e4, e5, List.head?_cons, if_neg e6, e7]
  rfl

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.ask_run
#print axioms ProofFile.Honest.K10.verdict_run
#print axioms ProofFile.Honest.K10.play_all
#print axioms ProofFile.Honest.K10.askAt_is
