-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/PlayReturns.lean: the frame's play returns along a list of rounds
whose moves are a proximity test's, where no round's two stops speak and every message of the test
has the shape that its round states. The companion of `play_test` (PlayLaw.lean in this folder),
which says what a play that has returned has shown. The statement is `play_returns`. It holds at
every job J (`TestJob`, Test.lean in this folder: what a caller supplies for its test), at every
list of rounds and at every number a, the number in the test of the list's first round, under the
six hypotheses below. It is called in HalfReturns.lean, Sim/PlayedFirst.lean (not in the library
yet), Sim/Shows.lean and Sim/ShowsFirst.lean, all in this folder. Two theorems.

In the list: the frame is Johnson/Desc/ProofFile/Honest/Frame.lean. Its play is `play`: it runs a
list l of rounds (`Step`) at a list of challenges ds, one by one, from a state m between two rounds
(`Mid`), and gives an error or a pair: the rounds as played and the state after them. "The play
returns" means that it gives such a pair. A round's two stops are the fields `bad` and `hid` of its
`Step`: each gives, at two lists of challenges, `none` or `some` words, and it speaks where it gives
`some`. `Step.stop` reads both and gives `none` or an error; a round stops where it gives an error.
What a round states are its fields `decl` and `oracles`. A move (`Move`) is the prover's side of one
round. `moveU J K i` (PlayLaw.lean) is the move of the test's round number i, from 0, with the coins
K (`TestCoins`, Test.lean) supplied. `msgAt J w fr K D i` (Parts.lean in this folder) is that
round's message at the input w, the front fr and the challenges D, by the round's number in the
test. A front (`Front`, Johnson/Desc/ProofFile/Honest/Sum.lean) is what the job's functions are
given of the run before the test. `frontBy m a` and `Heard m a D` are defined in PlayLaw.lean.

  `play_returns`: the rounds' moves are the test's from number a on · no stop speaks · the message
    of each round fits what the round states (`Sending.fits`,
    Johnson/Desc/ProofFile/Honest/Frame.lean) · the run has heard the test's first a challenges · as
    many challenges as rounds, D's from a on ⟹ the play returns. In Lean's names: there is a y with
    `play l ds back m = .ok y`
  `stop_none`: a round whose two stops never speak does not stop. In Lean's names: where `s.bad` and
    `s.hid` give `none` at all arguments, `s.stop l n` is `none` at every list l and number n

By what. `play_returns` is proved by induction on the list. At the first round, `say_eq`
(Played.lean in this folder) gives the message of the round's move. With `stop_none` and the third
hypothesis, `Step.tell` (the frame) returns; with `stop_none`, so does `Step.hear` (the frame).
`heard_next` (PlayLaw.lean) gives `Heard` at a + 1, and the same front, for the other rounds.
`stop_none` holds by unfolding `Step.stop`.

Hypotheses of `play_returns`, in the statement's order. For each i below the length of l, the field
`move` of round number i of l is `some (moveU J (Ks (a + i)) (a + i))`. For each round s of l,
`s.bad` and `s.hid` give `none` at all arguments. For each i below the length of l, `Sending.fits`
gives `true` at `msgAt J m.st.input (frontBy m a) (Ks (a + i)) D (a + i)` and the fields `decl` and
`oracles` of round number i of l. `Heard m a D` holds: the last a entries of `m.st.heard` are, in
order, D 0 to D (a - 1), and `m.seen` has at least a entries. ds is as long as l. For each n below
the length of ds, entry number n of ds is D (a + n). J, Ks, D, l, a, ds, `back` and m are free
parameters; `back` is a list of stored rounds, which `play` reads only at a round without a move.

Limits. That the messages fit is a hypothesis. That no stop speaks, that the rounds have these moves
and that `Heard` holds are hypotheses too: none is shown of any list of rounds here. Of the pair
that `play` gives, only that there is one is stated. Ks is a free parameter of type ℕ → `TestCoins`:
no hypothesis compares its values at two rounds. Nothing on the columns, on a decision, on
completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.PlayLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc

variable {W X : Type}

theorem stop_none (s : Step W X) (hb : ∀ f o, s.bad f o = none) (hh : ∀ f o, s.hid f o = none)
    (l : List Fmt.Drawn) (n : ℕ) : s.stop l n = none := by
  unfold Step.stop
  simp only [hb, hh]

/-- **The play returns.** -/
theorem play_returns (J : TestJob W X) (Ks : ℕ → TestCoins) (D : ℕ → Fmt.Drawn) :
    ∀ (l : List (Step W X)) (a : ℕ) (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid W X),
      (∀ i (h : i < l.length), l[i].move = some (moveU J (Ks (a + i)) (a + i))) →
      (∀ s ∈ l, (∀ f o, s.bad f o = none) ∧ ∀ f o, s.hid f o = none) →
      (∀ i (h : i < l.length), (msgAt J m.st.input (frontBy m a) (Ks (a + i)) D (a + i)).fits
        l[i].decl l[i].oracles = true) →
      Heard m a D → ds.length = l.length → (∀ n (h : n < ds.length), ds[n] = D (a + n)) →
      ∃ y, play l ds back m = .ok y
  | [], _, [], _, m, _, _, _, _, _, _ => ⟨([], m), rfl⟩
  | [], _, _ :: _, _, _, _, _, _, _, h, _ => by cases h
  | _ :: _, _, [], _, _, _, _, _, _, h, _ => by cases h
  | s :: ss, a, d :: ds, back, m, hm, hq, hf, H, hl, hd => by
    have hs : s.move = some (moveU J (Ks (a + 0)) (a + 0)) := hm 0 (by simp)
    have hd0 : d = D a := hd 0 (by simp)
    subst hd0
    obtain ⟨qb, qh⟩ := hq s List.mem_cons_self
    have hsay : (moveU J (Ks a) a).say () m.shown m.st =
        .ok (msgAt J m.st.input (frontBy m a) (Ks a) D a) :=
      say_eq J (fun _ : Unit => Ks a) a () m.shown m.st D H.same
    have hfit : (msgAt J m.st.input (frontBy m a) (Ks a) D a).fits s.decl s.oracles = true :=
      hf 0 (by simp)
    have htell : s.tell back.head? m =
        .ok ⟨(msgAt J m.st.input (frontBy m a) (Ks a) D a).vals.map Said.got,
          (msgAt J m.st.input (frontBy m a) (Ks a) D a).tables.map some, true⟩ := by
      unfold Step.tell
      rw [stop_none s qb qh, hs]
      simp only [Nat.add_zero, hsay, hfit, Bool.not_true, Bool.false_eq_true, if_false]
    have hhear : s.hear ⟨(msgAt J m.st.input (frontBy m a) (Ks a) D a).vals.map Said.got,
          (msgAt J m.st.input (frontBy m a) (Ks a) D a).tables.map some, true⟩ (D a) m =
        .ok ⟨{ m.st.hears (D a) with own := m.st.own }, m.loc ++ [D a],
          m.seen ++ [⟨(msgAt J m.st.input (frontBy m a) (Ks a) D a).vals.map Said.got, D a⟩],
          m.opened⟩ := by
      unfold Step.hear
      rw [hs]
      simp only [stop_none s qb qh, ite_self]
      rfl
    obtain ⟨H', hfr⟩ := heard_next H
      ((msgAt J m.st.input (frontBy m a) (Ks a) D a).vals.map Said.got) (m.loc ++ [D a])
    obtain ⟨z, hz⟩ := play_returns J Ks D ss (a + 1) ds back.tail
      (⟨{ m.st.hears (D a) with own := m.st.own }, m.loc ++ [D a], m.seen ++
        [⟨(msgAt J m.st.input (frontBy m a) (Ks a) D a).vals.map Said.got, D a⟩],
        m.opened⟩ : Mid W X)
      (fun i hi => by
        have k := hm (i + 1) (by simpa using hi)
        rw [show a + (i + 1) = a + 1 + i by omega] at k
        simpa using k)
      (fun s' hs' => hq s' (List.mem_cons_of_mem _ hs'))
      (fun i hi => by
        have k := hf (i + 1) (by simpa using hi)
        rw [show a + (i + 1) = a + 1 + i by omega] at k
        rw [hfr]
        show (msgAt J m.st.input (frontBy m a) (Ks (a + 1 + i)) D (a + 1 + i)).fits _ _ = true
        simpa using k)
      H' (Nat.succ.inj hl)
      (fun n hn => by
        have k := hd (n + 1) (by simpa using hn)
        rw [show a + (n + 1) = a + 1 + n by omega] at k
        simpa using k)
    refine ⟨(⟨s.name, s.addr.place, s.addr.part, true,
      (msgAt J m.st.input (frontBy m a) (Ks a) D a).vals.map Said.got,
      (msgAt J m.st.input (frontBy m a) (Ks a) D a).tables.map some, D a⟩ :: z.1, z.2), ?_⟩
    rw [play, htell]
    show (s.hear _ (D a) m).bind _ = _
    rw [hhear]
    show (play ss ds back.tail _).map _ = _
    rw [hz]
    rfl

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.stop_none
#print axioms ProofFile.Honest.K12.play_returns
