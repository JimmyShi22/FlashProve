-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/PlayLaw.lean: what the frame's play makes of a stretch of a
proximity test's moves: the rounds as played are the messages of one term at the whole list of
sampled challenges, round by round; and where the run stands behind them. This is `play_test`. It is
stated at every job J (`TestJob`, Test.lean in this folder: what a caller supplies for its test), at
every list of steps and at every number a, the number in the test of the list's first round, under
the four hypotheses below. `say_eq` (Played.lean in this folder) is on the message of one move;
`play_test` carries it along a list of steps. Definitions and theorems.

In the list: the frame is Johnson/Desc/ProofFile/Honest/Frame.lean. Its play is `play`: it runs a
list of steps (`Step`: one round each, with the round's move where a prover's side is defined) at a
list of challenges ds, one by one, from a state m between two rounds (`Mid`). It returns an error or
a pair y: the rounds as played (`Played`) and the state after them. "Where the run stands" is such a
state; "behind" means after, "in front" before. The fields of m: `st` is the prover's state
(`State`: the input, the challenges heard so far, and `own`, what the parts hand on to each other);
`loc` and `seen` are lists of challenges and of rounds (`Fmt.RoundView`: items and a challenge), to which
`play` appends one entry a round; `opened` holds the columns handed, if any, and `play` leaves it as
it is. A move (`Move`) is the prover's side of one round: `say` computes the message (`Sending`:
items and tables) from the move's coins, `seen` with `opened` (`m.shown`) and `st`, so with the
challenges heard so far; `hand` computes the next `own`. The term is `testAll J w fr K D`
(Test.lean), computed from the job, the prover's input w, a front fr, the coins K (`TestCoins`) and
the challenges D by the round's number in the test, from 0. A front (`Front`,
Johnson/Desc/ProofFile/Honest/Sum.lean) is what the job's functions are given of the run before the
test. The message of round number i is `msgAt J w fr K D i` (Parts.lean in this folder), taken from
the term; `moveAt` (Parts.lean) is that round's move.

  `play_test`: a list of steps whose moves are those of the rounds a, a + 1, ... · `play` returns ·
    the run stands behind the test's first a rounds, which heard D · the challenges are D's next
    ones ⟹ the rounds as played show the messages of the rounds a, a + 1, ... of the term at D, at
    the same front; behind them the input and what is handed on are as they were, and the challenges
    and the rounds shown have come behind those in front. In Lean's names: y.1 has one round for
    each step of l; `shownOf` of its round number i is `shownAt` of the message
    `msgAt J m.st.input (frontBy m a) (Ks (a + i)) D (a + i)` and the challenge D (a + i); y.2 is m
    with ds appended to `st.heard` and to `loc`, and `roundsOf y.1` (the frame) appended to `seen`;
    on the field `opened` of y.2 nothing is said
  `heard_next`: the step of the induction. Where `Heard m a D` holds, take the state that is m with
    D a appended to `st.heard`, one round with the challenge D a and any items appended to `seen`,
    any list as `loc`, and m's own field `opened`: `Heard` holds of it at a + 1 and D, and its
    `frontBy` at a + 1 is `frontBy m a`
  `moveU J K i`: a definition: `moveAt` at round number i with the coins K supplied. Its type of
    coins is `Unit`, as in the field `move` of a `Step`
  `frontBy m a`: a definition: the front that has `m.st.heard` and `m.seen`, each without its last a
    entries, `m.st.own`, and the columns `m.opened` as they are (`m.shown.front a`); a list that has
    fewer than a entries gives the empty list
  `Heard m a D`: a definition, a structure of three propositions: `m.st.heard` has at least a
    entries (`le`); so has `m.seen` (`leS`); the last a entries of `m.st.heard` are, in order, D 0
    to D (a - 1) (`same`)
  `shownOf p`, `shownAt x d`: definitions: of a round as played, the fields `vals`, `tables` and
    `drawn`; of a message x and a challenge d, the items of x converted by `Said.got` (the frame),
    the tables of x, each under `some`, and d

By what. `play_test` is proved by induction on the list. `play_cons_ok`
(Johnson/Desc/ProofFile/Honest/Law/Play.lean) splits a run of `play` that has returned into the
first step's `Step.tell` and `Step.hear` (the frame) and `play` at the other steps. `say_eq`
(Played.lean) gives the message of the first step's move. `heard_next` gives `Heard` and the front
at a + 1; it is proved by unfolding `State.hears` and `State.lately` (the frame).

Hypotheses of `play_test`, in the statement's order. For each i below the length of l, the field
`move` of step number i of l is `some (moveU J (Ks (a + i)) (a + i))`. `play l ds back m` returns y;
`back` is a list of stored rounds, which `play` reads only at a step without a move. `Heard m a D`
holds. For each n below the length of ds, entry number n of ds is D (a + n). J, Ks, D, l, a, ds,
`back` and m are free parameters.

Limits.
- The term stands here at each round's own coins: Ks, the coins that each round's move reads, is a
  letter, by the round's number: "one term" above means one text, one front and one list of
  challenges; one family of coins is PlayedTerm.lean's. In Lean's names: every round's message is
  `msgAt` at the same J, input, front and D; Ks is a free parameter of type ℕ → `TestCoins`, and no
  hypothesis compares its values at two rounds.
- That the two parts' readers agree on what a round reads is not treated here. A part's reader is
  the function that makes a `TestCoins` of what the part is given: `firstRd` (HalfSteps.lean in this
  folder) and `restCoins` (Parts.lean). `played_term` (PlayedTerm.lean in this folder) has a
  hypothesis on the two (`Agree`, CoinsAgree.lean in this folder).
- That `play` returns is a hypothesis: nothing here says that it does.
- That the steps have these moves is a hypothesis, and so is `Heard`. For the steps of the test's
  two parts the first is proved in `half_steps` (HalfSteps.lean), under hypotheses of its own.
- Of a round as played, `play_test` speaks of `vals`, `tables` and `drawn` only: nothing on its
  fields `name`, `place`, `part` and `told`.
- `shownOf` of this file (`ProofFile.Honest.K12.shownOf`) has the short name of the frame's
  `ProofFile.Honest.shownOf` (Johnson/Desc/ProofFile/Honest/Side.lean) and is another function. This one
  holds a round's whole tables; the frame's gives of each table only the columns at given positions.
  So `play_test` is an equation on whole tables, not on what is opened of them.
- Nothing on a decision, on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.Played
import Johnson.Desc.ProofFile.Honest.Law.Play

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc

variable {W X : Type}

/-- The move of the test's round number i (`moveAt`, Parts.lean) with the coins K supplied: a move
whose type of coins is `Unit`, as in the field `move` of a `Step` (the frame). -/
def moveU (J : TestJob W X) (K : TestCoins) (i : ℕ) : Move Unit W X :=
  ⟨fun _ => (moveAt J (fun _ : Unit => K) i).say (), (moveAt J (fun _ : Unit => K) i).hand⟩

/-- The test's front (`Front`), computed from a state m that comes after the test's first a rounds:
`m.st.heard` and `m.seen`, each without its last a entries, `m.st.own`, and the columns `m.opened`
as they are. A list that has fewer than a entries gives the empty list. -/
def frontBy (m : Mid W X) (a : ℕ) : Front X :=
  ⟨m.st.heard.take (m.st.heard.length - a), m.st.own, m.shown.front a⟩

/-- The last a challenges heard are D's first a; as many rounds have been shown. As Lean has it, at
least as many: `le`, `leS`: `m.st.heard` and `m.seen` have at least a entries each, and no field
bounds either length from above. `same`: entry number n of the last a challenges heard
(`State.lately`, the frame) is D n, for each n below a. -/
structure Heard (m : Mid W X) (a : ℕ) (D : ℕ → Fmt.Drawn) : Prop where
  le : a ≤ m.st.heard.length
  leS : a ≤ m.seen.length
  same : ∀ n, n < a → (m.st.lately a).getD n ⟨[], [], [], none⟩ = D n

/-- One round as played, as far as a view and the tables go. These are its fields `vals`, `tables`
and `drawn`. The tables are whole tables, not the columns at asked positions. This is not the
frame's `ProofFile.Honest.shownOf` (Johnson/Desc/ProofFile/Honest/Side.lean), which has the same short
name: that one takes a list of played rounds and lists of positions, and gives of each table only
the columns at these positions. -/
def shownOf (p : Played) : List Fmt.ItemValue × List (Option Table) × Fmt.Drawn :=
  (p.vals, p.tables, p.drawn)

/-- The same of a message and a challenge. The items are converted by `Said.got` (the frame), and
each table is put under `some`. -/
def shownAt (x : Sending) (d : Fmt.Drawn) : List Fmt.ItemValue × List (Option Table) × Fmt.Drawn :=
  (x.vals.map Said.got, x.tables.map some, d)

theorem heard_next {m : Mid W X} {a : ℕ} {D : ℕ → Fmt.Drawn} (H : Heard m a D)
    (vals : List Fmt.ItemValue) (loc : List Fmt.Drawn) :
    Heard (⟨{ m.st.hears (D a) with own := m.st.own }, loc, m.seen ++ [⟨vals, D a⟩],
      m.opened⟩ : Mid W X) (a + 1) D ∧
    frontBy (⟨{ m.st.hears (D a) with own := m.st.own }, loc, m.seen ++ [⟨vals, D a⟩],
      m.opened⟩ : Mid W X) (a + 1) = frontBy m a := by
  have hl := H.le
  have hs := H.leS
  refine ⟨⟨by simp [State.hears]; omega, by simp; omega, fun n hn => ?_⟩, ?_⟩
  · have e : (State.lately ({ m.st.hears (D a) with own := m.st.own } : State W X) (a + 1)) =
        m.st.lately a ++ [D a] := by
      simp only [State.lately, State.hears, List.length_append, List.length_cons, List.length_nil]
      rw [show m.st.heard.length + (0 + 1) - (a + 1) = m.st.heard.length - a by omega,
        List.drop_append_of_le_length (by omega)]
    have hlen : (m.st.lately a).length = a := by
      simp only [State.lately, List.length_drop]
      omega
    rw [e]
    by_cases c : n < a
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact c)]
      exact H.same n c
    · obtain rfl : n = a := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [hlen])]
      simp [hlen]
  · simp only [frontBy, Mid.shown, Seen.front, State.hears, List.length_append, List.length_cons,
      List.length_nil]
    rw [show m.st.heard.length + (0 + 1) - (a + 1) = m.st.heard.length - a by omega,
      show m.seen.length + (0 + 1) - (a + 1) = m.seen.length - a by omega,
      List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]

/-- **Round by round, `shownOf` of what `play` returns is `shownAt` of that round's `msgAt` at D.**
l: steps whose moves are those of the test's rounds a, a + 1 and so on, round number a + i at the
coins Ks (a + i). m: a state after the test's first a rounds (`Heard`). ds: the values of D from the
number a on. The front is `frontBy m a` at every round. The last three equations give the state
after the list. -/
theorem play_test (J : TestJob W X) (Ks : ℕ → TestCoins) (D : ℕ → Fmt.Drawn) :
    ∀ (l : List (Step W X)) (a : ℕ) (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid W X)
      (y : List Played × Mid W X),
      (∀ i (h : i < l.length), l[i].move = some (moveU J (Ks (a + i)) (a + i))) →
      play l ds back m = .ok y → Heard m a D → (∀ n (h : n < ds.length), ds[n] = D (a + n)) →
      y.1.map shownOf = (List.range l.length).map (fun i =>
        shownAt (msgAt J m.st.input (frontBy m a) (Ks (a + i)) D (a + i)) (D (a + i))) ∧
      y.2.st = { m.st with heard := m.st.heard ++ ds } ∧ y.2.seen = m.seen ++ roundsOf y.1 ∧
      y.2.loc = m.loc ++ ds
  | [], a, [], back, m, y, _, h, _, _ => by
    simp only [play] at h
    cases h
    simp [roundsOf]
  | [], _, _ :: _, _, _, _, _, h, _, _ => by simp [play] at h
  | _ :: _, _, [], _, _, _, _, h, _, _ => by simp [play] at h
  | s :: ss, a, d :: ds, back, m, y, hm, h, H, hd => by
    obtain ⟨x, m', z, h1, h2, h3, rfl⟩ := play_cons_ok h
    have hs : s.move = some (moveU J (Ks (a + 0)) (a + 0)) := hm 0 (by simp)
    have hd0 : d = D a := hd 0 (by simp)
    subst hd0
    -- the message of the first step's move
    have hsay : (moveU J (Ks a) a).say () m.shown m.st =
        .ok (msgAt J m.st.input (frontBy m a) (Ks a) D a) :=
      say_eq J (fun _ : Unit => Ks a) a () m.shown m.st D H.same
    have hx : x.vals = (msgAt J m.st.input (frontBy m a) (Ks a) D a).vals.map Said.got ∧
        x.tables = (msgAt J m.st.input (frontBy m a) (Ks a) D a).tables.map some := by
      unfold Step.tell at h1
      split at h1
      · cases h1
      · rw [hs] at h1
        simp only [Nat.add_zero, hsay] at h1
        split at h1
        · cases h1
        · cases h1
          exact ⟨rfl, rfl⟩
    have hm' : m' = ⟨{ m.st.hears (D a) with own := m.st.own }, m.loc ++ [D a],
        m.seen ++ [⟨x.vals, D a⟩], m.opened⟩ := by
      unfold Step.hear at h2
      rw [hs] at h2
      simp only at h2
      split at h2
      · cases h2
      · cases h2
        rfl
    obtain ⟨H', hfr⟩ := heard_next H x.vals (m.loc ++ [D a])
    rw [← hm'] at H' hfr
    obtain ⟨i1, i2, i3, i4⟩ := play_test J Ks D ss (a + 1) ds back.tail m' z
      (fun i hi => by
        have k := hm (i + 1) (by simpa using hi)
        rw [show a + (i + 1) = a + 1 + i by omega] at k
        simpa using k) h3 H'
      (fun n hn => by
        have k := hd (n + 1) (by simpa using hn)
        rw [show a + (n + 1) = a + 1 + n by omega] at k
        simpa using k)
    have hin : m'.st.input = m.st.input := by rw [hm']; rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [List.map_cons, i1, hfr, hin, List.length_cons, List.range_succ_eq_map, List.map_cons,
        List.map_map]
      refine congrArg₂ _ ?_ (List.map_congr_left fun i _ => ?_)
      · simp only [shownOf, shownAt, Nat.add_zero, hx.1, hx.2]
      · simp only [Function.comp, show a + 1 + i = a + (i + 1) by omega, Nat.succ_eq_add_one]
    · rw [i2, hm']
      simp [State.hears]
    · rw [i3, hm']
      simp [roundsOf]
    · rw [i4, hm']
      simp

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.heard_next
#print axioms ProofFile.Honest.K12.play_test
#print axioms ProofFile.Honest.K12.moveU
#print axioms ProofFile.Honest.K12.frontBy
#print axioms ProofFile.Honest.K12.Heard
#print axioms ProofFile.Honest.K12.shownOf
#print axioms ProofFile.Honest.K12.shownAt
