-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/PlayRow.lean: the whole list of rounds that the frame's `play`
(Honest/Frame.lean) returns over the steps of a list of `Part`s (`rowSteps`). The list is written
out as a definition, `playedRow`, and theorems tie it to `play` in both directions: under hypotheses
on this run alone `play` returns it; and where there are as many declared rounds as moves and `play`
has returned, it has returned it. A `Part` (Honest/Frame.lean) is the prover's side of some
consecutive rounds of a sub-protocol: one move for each round, the counts of its coins, and two stop
tests, the fields `bad` and `hid`, each of which returns `none` or an error text. The prover's part
for a sub-protocol (`Placed`) holds a list of `Part`s. "This run" is the coins c, the state m of the
prover's run (`Mid`) and the challenges ds of a statement. General in the list: no kind of
sub-protocol is named.

Honest/SumLaw/PlaysWhole.lean writes out the list for one `Part` (`playedFrom`) and proves that
`play` returns it where `bad` and `hid` return `none` at all challenges (`play_steps_whole`). Here
the same is proved for a list of `Part`s, and the two tests have to return `none` at this run's
challenges only.

  `play_row_whole`: under the hypotheses below, `play` over `rowSteps name a v ps j rs c`, at the
    challenges ds and from the state m, returns l and the state
    `⟨stateRow ps m.st ds, m.loc ++ ds, m.seen ++ roundsOf l, m.opened⟩`: `play` leaves the columns
    handed as they are
  `play_steps_silent`: the same for one `Part`, over `Part.steps`, with `Part.stopAt`, `fitsFrom`,
    `playedFrom` and `stateFrom` for `rowStopAt`, `fitsRow`, `playedRow` and `stateRow`
  `played_of_play`: the converse: where rs has as many declared rounds as the `Part`s have moves and
    `play` over `rowSteps` returns y, `playedRow` returns y.1, `fitsRow` is true, and y.2 is the
    state above with y.1 for l. It has no hypothesis on a stop test or on a message's shape
  `played_of_steps`: the same for one `Part`
  `play_lengths`: where `play` returns, there are as many challenges as steps
  `playedRow name a ps j c t seen ds`: a definition: the rounds as played, one `Part` after the
    other: `playedFrom` at the `Part`'s own challenges, then the rest of the list from the state
    that this `Part` leaves, with its rounds appended to seen (a `Seen`: `Seen.plus`; its columns
    are carried on). It tests no message's shape and asks
    no stop test: it returns a list wherever every move returns a message and there are as many
    challenges as moves
  `stateRow`: a definition: the prover's `State` after the moves of the list
  `fitsRow`: a Bool-valued test: along this run every message has the shape that its round states,
    and there are as many declared rounds and as many challenges as moves
  `play_stepsFrom_silent`, `played_of_stepsFrom`: the two directions for the steps of one `Part`
    from a round number on (`stepsFrom`, Honest/SumLaw/Plays.lean)
  `silent_of_stopAt`: what `Part.stopAt` … = none says of `bad` and `hid`
  `alone_of_played`: where `playedFrom` returns, the rounds of `aloneFrom` are its rounds
  `stop_split`, `tell_at`, `hear_at`: what `Step.stop`, `Step.tell` and `Step.hear` return at one
    step; `tell_inv`, `hear_inv`: the converses for `Step.tell` and `Step.hear`

By what. `play_append`, `play_cons_ok` (Honest/Law/Play.lean): `play` over two lists of steps, and
over a first step and the rest. `exBind_ok`, `exMap_ok` (same file): what an `Except.bind` or
`Except.map` that returns `.ok` is made of. `steps_eq` (Honest/SumLaw/Plays.lean): `Part.steps` is
`stepsFrom` from round 0 on. `steps_length`, `steps_length_fits`, `playedFrom_rounds`
(Honest/SumLaw/PlaysWhole.lean). `or_none` (Honest/Law/Thread.lean). `Part.stopAt` and `rowStopAt`
are definitions of Honest/Side.lean.

Hypotheses of `play_row_whole`. `rowStopAt v ps m.loc ds = none`: in each `Part` that has a move,
`bad` returns `none` at the challenges before the `Part` and every prefix of its own, and so does
`hid` at v where v is not `none`. `fitsRow ps rs c m.st m.shown ds = true`: see `fitsRow` above.
`playedRow name a ps j c m.st m.shown ds = some l`: every move returns a message, and l is the list.

Limits. In `play_steps_silent` and `play_row_whole`, that a move returns a message and that its
message has the stated shape are hypotheses: neither is shown here. Through its import of
PlaysWhole.lean the file depends on three files of Honest/SumLaw/ (PlaysWhole.lean, Plays.lean,
Terms.lean), and through Terms.lean on the masked sumcheck's prover (Honest/Sum.lean) and on
OnBytes/Model/HideLaws.lean. Of all these it uses five definitions, `aloneFrom`, `fitsFrom`,
`stateFrom`, `stepsFrom` and `playedFrom`, which are general and name no sumcheck, and the lemmas on
them that are named above, and nothing else. Nothing on the columns that a sub-protocol's decision
is shown (ColGroups.lean). Nothing on what the messages of the rounds contain or mean. In this file
no `Part` of a protocol is shown to meet the hypotheses of `play_row_whole`. Lemmas on the frame's
own definitions. No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.PlaysWhole
import Johnson.Desc.ProofFile.Honest.Law.Thread

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open VerifiableInference.Desc (Oracle Place)
open ProofFile.Honest.SumLaw (playedFrom stateFrom fitsFrom stepsFrom steps_eq aloneFrom playedFrom_rounds
  steps_length steps_length_fits)

variable {V W X : Type}

/-! ## 1 Definitions for a list of `Part`s -/

/-- The rounds as played over a list of `Part`s, one `Part` after the other. j: the number of the
first `Part`. -/
def playedRow (name : String) (a : Place) : (ps : List (Part V W X)) → Nat → RowCoins ps →
    State W X → Seen → List Fmt.Drawn → Option (List Played)
  | [], _, _, _, _, ds => if ds.isEmpty then some [] else none
  | p :: ps, j, c, t, seen, ds =>
    (playedFrom name ⟨a, j⟩ c.1 p.moves t seen (ds.take p.moves.length)).bind fun l =>
      (playedRow name a ps (j + 1) c.2 (stateFrom p.moves t (ds.take p.moves.length))
        (seen.plus (roundsOf l)) (ds.drop p.moves.length)).map (l ++ ·)

/-- The prover's `State` after the moves of the list. -/
def stateRow : List (Part V W X) → State W X → List Fmt.Drawn → State W X
  | [], t, _ => t
  | p :: ps, t, ds =>
    stateRow ps (stateFrom p.moves t (ds.take p.moves.length)) (ds.drop p.moves.length)

/-- Along this run every message of the list's moves has the shape that its round states, and there
are exactly as many declared rounds and as many challenges as moves. -/
def fitsRow : (ps : List (Part V W X)) → List (Fmt.DeclaredRound × List Oracle) → RowCoins ps →
    State W X → Seen → List Fmt.Drawn → Bool
  | [], rs, _, _, _, ds => rs.isEmpty && ds.isEmpty
  | p :: ps, rs, c, t, seen, ds =>
    fitsFrom c.1 (rs.take p.moves.length) p.moves t seen (ds.take p.moves.length) &&
      fitsRow ps (rs.drop p.moves.length) c.2 (stateFrom p.moves t (ds.take p.moves.length))
        (seen.plus ((aloneFrom c.1 p.moves t seen (ds.take p.moves.length)).getD []))
        (ds.drop p.moves.length)

/-! ## 2 One step -/

/-- `Step.stop` returns `none` at the challenges loc ++ pre, of which pre are the `Part`'s own,
where the step's `bad` and `hid` return `none` at loc and pre. -/
theorem stop_split (s : Step W X) (loc pre : List Fmt.Drawn) (hb : s.bad loc pre = none)
    (hh : s.hid loc pre = none) : s.stop (loc ++ pre) pre.length = none := by
  unfold Step.stop
  have e : (loc ++ pre).length - pre.length = loc.length := by
    rw [List.length_append, Nat.add_sub_cancel]
  simp only [e, List.take_left, List.drop_left, hb, hh]

/-- What `Step.tell` returns where `Step.stop` returns `none` at this state m, the move returns the
message x, and x passes `Sending.fits`. -/
theorem tell_at {s : Step W X} {mv : Move Unit W X} (hm : s.move = some mv) {m : Mid W X}
    (hst : s.stop m.loc s.nth = none) {x : Sending} (hs : mv.say () m.shown m.st = .ok x)
    (hf : x.fits s.decl s.oracles = true) (back : Option Fmt.RoundView) :
    s.tell back m = .ok ⟨x.vals.map Said.got, x.tables.map some, true⟩ := by
  unfold Step.tell
  simp only [hst, hm, hs, hf]
  rfl

/-- The state that `Step.hear` returns at a step with a move where, if the step is the last of its
`Part`, `Step.stop` returns `none` at this state's challenges followed by d. -/
theorem hear_at {s : Step W X} {mv : Move Unit W X} (hm : s.move = some mv) (x : Told)
    (d : Fmt.Drawn) (m : Mid W X)
    (hst : s.last = true → s.stop (m.loc ++ [d]) (s.nth + 1) = none) :
    s.hear x d m = .ok ⟨{ m.st.hears d with own := mv.hand (m.st.hears d) }, m.loc ++ [d],
      m.seen ++ [⟨x.vals, d⟩], m.opened⟩ := by
  unfold Step.hear
  cases hl : s.last with
  | false => simp only [hm, Bool.false_eq_true, if_false]
  | true => simp only [hm, if_true, hst hl]

/-- Where `Step.tell` has returned x at a step with a move, the move has returned a message z that
passes `Sending.fits`, and x is made of z as in `tell_at`. -/
theorem tell_inv {s : Step W X} {mv : Move Unit W X} (hm : s.move = some mv) {m : Mid W X}
    {back : Option Fmt.RoundView} {x : Told} (h : s.tell back m = .ok x) :
    ∃ z : Sending, mv.say () m.shown m.st = .ok z ∧ z.fits s.decl s.oracles = true ∧
      x = ⟨z.vals.map Said.got, z.tables.map some, true⟩ := by
  unfold Step.tell at h
  cases hst : s.stop m.loc s.nth with
  | some e =>
    simp only [hst] at h
    cases h
  | none =>
    cases hs : mv.say () m.shown m.st with
    | error e =>
      simp only [hst, hm, hs] at h
      cases h
    | ok z =>
      cases hf : z.fits s.decl s.oracles with
      | false =>
        simp only [hst, hm, hs, hf, Bool.not_false, if_true] at h
        cases h
      | true =>
        simp only [hst, hm, hs, hf, Bool.not_true, Bool.false_eq_true, if_false] at h
        cases h
        exact ⟨z, rfl, hf, rfl⟩

/-- Where `Step.hear` has returned m' at a step with a move, m' is the state of `hear_at`. -/
theorem hear_inv {s : Step W X} {mv : Move Unit W X} (hm : s.move = some mv) {x : Told}
    {d : Fmt.Drawn} {m m' : Mid W X} (h : s.hear x d m = .ok m') :
    m' = ⟨{ m.st.hears d with own := mv.hand (m.st.hears d) }, m.loc ++ [d],
      m.seen ++ [⟨x.vals, d⟩], m.opened⟩ := by
  unfold Step.hear at h
  simp only [hm] at h
  split at h
  · cases h
  · cases h
    rfl

/-! ## 3 `play` returns the list -/

/-- `play_steps_silent` for the steps of one `Part` from the round number i on (`stepsFrom`). `bad`
and `hid` have to return `none` at this run alone: at loc₀ and each prefix of pre ++ ds whose length
is from i to n. n: i plus the number of the moves mvs. loc₀: the challenges before the `Part`, as
`bad` and `hid` are given them. pre: the `Part`'s own challenges before round i. -/
theorem play_stepsFrom_silent {C : Type} (name : String) (a : Addr)
    (bad hid : List Fmt.Drawn → List Fmt.Drawn → Option String) (n : Nat) (c : C)
    (loc₀ : List Fmt.Drawn) :
    ∀ (rs : List (Fmt.DeclaredRound × List Oracle)) (mvs : List (Move C W X)) (i : Nat)
      (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid W X) (l : List Played)
      (pre : List Fmt.Drawn), m.loc = loc₀ ++ pre → pre.length = i → i + mvs.length = n →
      (n ≠ 0 → ∀ j, i ≤ j → j ≤ n → bad loc₀ ((pre ++ ds).take j) = none ∧
        hid loc₀ ((pre ++ ds).take j) = none) →
      fitsFrom c rs mvs m.st m.shown ds = true → playedFrom name a c mvs m.st m.shown ds = some l →
      play (stepsFrom name a bad hid n c i rs mvs) ds back m =
        .ok (l, ⟨stateFrom mvs m.st ds, m.loc ++ ds, m.seen ++ roundsOf l, m.opened⟩)
  | [], [], _, [], _, m, l, _, _, _, _, _, _, h => by
    have e : l = [] := (Option.some.inj h).symm
    subst e
    show Except.ok ([], m) = _
    simp [stateFrom, roundsOf]
  | r :: rs, mv :: mvs, i, d :: ds, back, m, l, pre, hloc, hpre, hn, hq, hf, h => by
    cases hs : mv.say c m.shown m.st with
    | error e =>
      simp only [playedFrom, hs] at h
      cases h
    | ok x =>
      simp only [fitsFrom, hs, Bool.and_eq_true] at hf
      simp only [playedFrom, hs, Option.map_eq_some_iff] at h
      obtain ⟨l', h', rfl⟩ := h
      rw [List.length_cons] at hn
      have hq' := hq (by omega)
      have hl := play_stepsFrom_silent name a bad hid n c loc₀ rs mvs (i + 1) ds back.tail
        ⟨{ m.st.hears d with own := mv.hand (m.st.hears d) }, m.loc ++ [d],
          m.seen ++ [⟨x.vals.map Said.got, d⟩], m.opened⟩ l' (pre ++ [d])
        (by show m.loc ++ [d] = _; rw [hloc, List.append_assoc])
        (by rw [List.length_append, hpre]; rfl) (by omega)
        (fun _ j h1 h2 => by
          have := hq' j (by omega) h2
          rwa [List.append_assoc, List.singleton_append])
        (by simpa only [Mid.shown, Seen.plus] using hf.2)
        (by simpa only [Mid.shown, Seen.plus] using h')
      have hstep : stepsFrom name a bad hid n c i (r :: rs) (mv :: mvs) =
          ⟨name, a, r.1, r.2, bad, hid, i, i + 1 == n, some ⟨fun _ => mv.say c, mv.hand⟩⟩ ::
            stepsFrom name a bad hid n c (i + 1) rs mvs := rfl
      have q0 := hq' i (Nat.le_refl i) (by omega)
      have t0 : (pre ++ d :: ds).take i = pre := by rw [← hpre]; exact List.take_left
      rw [t0] at q0
      have q1 := hq' (i + 1) (Nat.le_succ i) (by omega)
      have t1 : (pre ++ d :: ds).take (i + 1) = pre ++ [d] := by
        have e : pre ++ d :: ds = (pre ++ [d]) ++ ds := by
          rw [List.append_assoc, List.singleton_append]
        rw [e, show i + 1 = (pre ++ [d]).length by rw [List.length_append, hpre]; rfl]
        exact List.take_left
      rw [t1] at q1
      rw [hstep]
      show ((Step.tell _ back.head? m).bind fun y => _) = _
      rw [tell_at (s := ⟨name, a, r.1, r.2, bad, hid, i, i + 1 == n,
        some ⟨fun _ => mv.say c, mv.hand⟩⟩) rfl
        (by
          show Step.stop _ m.loc i = none
          rw [hloc, ← hpre]
          exact stop_split _ loc₀ pre q0.1 q0.2) hs hf.1]
      show ((Step.hear _ _ d m).bind fun m' => _) = _
      rw [hear_at (s := ⟨name, a, r.1, r.2, bad, hid, i, i + 1 == n,
        some ⟨fun _ => mv.say c, mv.hand⟩⟩) rfl _ d m
        (fun _ => by
          show Step.stop _ (m.loc ++ [d]) (i + 1) = none
          rw [hloc, List.append_assoc,
            show i + 1 = (pre ++ [d]).length by rw [List.length_append, hpre]; rfl]
          exact stop_split _ loc₀ (pre ++ [d]) q1.1 q1.2)]
      show ((play _ ds back.tail _).map fun y => _) = _
      rw [hl]
      show Except.ok _ = Except.ok _
      simp [stateFrom, roundsOf, List.append_assoc]
  | [], [], _, _ :: _, _, _, _, _, _, _, _, _, hf, _ => by simp [fitsFrom] at hf
  | [], _ :: _, _, _, _, _, _, _, _, _, _, _, hf, _ => by simp [fitsFrom] at hf
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, hf, _ => by simp [fitsFrom] at hf
  | _ :: _, _ :: _, _, [], _, _, _, _, _, _, _, _, hf, _ => by simp [fitsFrom] at hf

/-- What `Part.stopAt` … = none says of a `Part` that has a move: `bad`, and `hid` at v, return
`none` at loc and `ds.take j`, for each j up to the number of moves. -/
theorem silent_of_stopAt (p : Part V W X) (v : Option V) (loc ds : List Fmt.Drawn)
    (h : p.stopAt v loc ds = none) (h0 : p.moves.length ≠ 0) :
    ∀ j, j ≤ p.moves.length → p.bad loc (ds.take j) = none ∧
      (v.bind fun u => p.hid u loc (ds.take j)) = none := by
  intro j hj
  unfold Part.stopAt at h
  have hn : (p.moves.length == 0) = false := beq_eq_false_iff_ne.2 h0
  simp only [hn, Bool.false_eq_true, if_false] at h
  have hx := List.findSome?_eq_none_iff.1 h j (List.mem_range.2 (Nat.lt_succ_of_le hj))
  cases hb : p.bad loc (ds.take j) with
  | some e => simp [hb] at hx
  | none =>
    cases hh : (v.bind fun u => p.hid u loc (ds.take j)) with
    | some e => simp [hb, hh] at hx
    | none => exact ⟨rfl, rfl⟩

/-- **One `Part`: `play` returns the list of `playedFrom`**, where `Part.stopAt` returns `none` at
this run, `fitsFrom` is true and `playedFrom` returns. -/
theorem play_steps_silent (p : Part V W X) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins) (ds : List Fmt.Drawn)
    (back : List Fmt.RoundView) (m : Mid W X) (l : List Played) (hst : p.stopAt v m.loc ds = none)
    (hf : fitsFrom c rs p.moves m.st m.shown ds = true)
    (h : playedFrom name a c p.moves m.st m.shown ds = some l) :
    play (p.steps name a rs v c) ds back m =
      .ok (l, ⟨stateFrom p.moves m.st ds, m.loc ++ ds, m.seen ++ roundsOf l, m.opened⟩) := by
  rw [steps_eq]
  refine play_stepsFrom_silent name a p.bad _ p.moves.length c m.loc rs p.moves 0 ds back m l []
    (List.append_nil _).symm rfl (Nat.zero_add _) (fun h0 j _ hj => ?_) hf h
  rw [List.nil_append]
  exact silent_of_stopAt p v m.loc ds hst h0 j hj

/-- Where `playedFrom` returns, the rounds of `aloneFrom` are its rounds. -/
theorem alone_of_played {C : Type} {name : String} {a : Addr} {c : C} {mvs : List (Move C W X)}
    {t : State W X} {seen : Seen} {ds : List Fmt.Drawn} {l : List Played}
    (h : playedFrom name a c mvs t seen ds = some l) :
    (aloneFrom c mvs t seen ds).getD [] = roundsOf l := by
  rw [← playedFrom_rounds name a c mvs t seen ds, h]
  rfl

/-- **A list of `Part`s: `play` returns the list of `playedRow`**, where `rowStopAt` returns `none`
at this run, `fitsRow` is true and `playedRow` returns. -/
theorem play_row_whole (name : String) (a : Place) (v : Option V) :
    ∀ (ps : List (Part V W X)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (c : RowCoins ps) (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid W X)
      (l : List Played), rowStopAt v ps m.loc ds = none →
      fitsRow ps rs c m.st m.shown ds = true → playedRow name a ps j c m.st m.shown ds = some l →
      play (rowSteps name a v ps j rs c) ds back m =
        .ok (l, ⟨stateRow ps m.st ds, m.loc ++ ds, m.seen ++ roundsOf l, m.opened⟩)
  | [], _, _, _, ds, _, m, l, _, hf, h => by
    simp only [fitsRow, Bool.and_eq_true, List.isEmpty_iff] at hf
    obtain ⟨-, rfl⟩ := hf
    have e : l = [] := by
      simp only [playedRow, List.isEmpty_nil, if_true] at h
      exact (Option.some.inj h).symm
    subst e
    show Except.ok ([], m) = _
    simp [stateRow, roundsOf]
  | p :: ps, j, rs, c, ds, back, m, l, hst, hf, h => by
    obtain ⟨s1, s2⟩ := or_none (show (p.stopAt v m.loc (ds.take p.moves.length)).or
      (rowStopAt v ps (m.loc ++ ds.take p.moves.length) (ds.drop p.moves.length)) = none from hst)
    simp only [fitsRow, Bool.and_eq_true] at hf
    obtain ⟨f1, f2⟩ := hf
    simp only [playedRow] at h
    obtain ⟨l₁, h₁, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨l₂, h₂, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [alone_of_played h₁] at f2
    have e1 := play_steps_silent p name ⟨a, j⟩ (rs.take p.moves.length) v c.1
      (ds.take p.moves.length) back m l₁ s1 f1 h₁
    have e2 := play_row_whole name a v ps (j + 1) (rs.drop p.moves.length) c.2
      (ds.drop p.moves.length)
      (back.drop (p.steps name ⟨a, j⟩ (rs.take p.moves.length) v c.1).length)
      ⟨stateFrom p.moves m.st (ds.take p.moves.length), m.loc ++ ds.take p.moves.length,
        m.seen ++ roundsOf l₁, m.opened⟩ l₂ s2 f2 h₂
    show play (p.steps name ⟨a, j⟩ (rs.take p.moves.length) v c.1 ++
      rowSteps name a v ps (j + 1) (rs.drop p.moves.length) c.2) ds back m = _
    conv => lhs; rw [← List.take_append_drop p.moves.length ds]
    rw [play_append _ _ _ _ _ _
      (steps_length_fits p name ⟨a, j⟩ _ v c.1 m.st m.shown _ f1).symm, e1]
    show ((play _ _ _ _).map fun z => _) = _
    rw [e2]
    show Except.ok _ = Except.ok _
    simp only [stateRow, roundsOf, List.map_append, List.append_assoc, List.take_append_drop]

/-! ## 4 What `play` has returned -/

/-- Where `play` has returned, there were as many challenges as steps. -/
theorem play_lengths : ∀ (l : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (m : Mid W X) (y : List Played × Mid W X), play l ds back m = .ok y → ds.length = l.length
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, h => by simp [play] at h
  | _ :: _, [], _, _, _, h => by simp [play] at h
  | s :: l, d :: ds, back, m, y, h => by
    obtain ⟨x, m', z, -, -, h3, -⟩ := play_cons_ok h
    rw [List.length_cons, List.length_cons, play_lengths l ds back.tail m' z h3]

/-- `played_of_steps` for the steps of one `Part` from the round number i on (`stepsFrom`). -/
theorem played_of_stepsFrom {C : Type} (name : String) (a : Addr)
    (bad hid : List Fmt.Drawn → List Fmt.Drawn → Option String) (n : Nat) (c : C) :
    ∀ (rs : List (Fmt.DeclaredRound × List Oracle)) (mvs : List (Move C W X)) (i : Nat)
      (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid W X) (y : List Played × Mid W X),
      rs.length = mvs.length → play (stepsFrom name a bad hid n c i rs mvs) ds back m = .ok y →
      playedFrom name a c mvs m.st m.shown ds = some y.1 ∧
        fitsFrom c rs mvs m.st m.shown ds = true ∧
        y.2 = ⟨stateFrom mvs m.st ds, m.loc ++ ds, m.seen ++ roundsOf y.1, m.opened⟩
  | [], [], _, [], _, m, y, _, h => by
    have e : y = ([], m) := (Except.ok.inj h).symm
    subst e
    refine ⟨rfl, rfl, ?_⟩
    simp [stateFrom, roundsOf]
  | [], [], _, _ :: _, _, _, _, _, h => by simp [stepsFrom, play] at h
  | _ :: _, _ :: _, _, [], _, _, _, _, h => by simp [stepsFrom, play] at h
  | [], _ :: _, _, _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, _, _, hl, _ => by simp at hl
  | r :: rs, mv :: mvs, i, d :: ds, back, m, y, hl, h => by
    have hstep : stepsFrom name a bad hid n c i (r :: rs) (mv :: mvs) =
        ⟨name, a, r.1, r.2, bad, hid, i, i + 1 == n, some ⟨fun _ => mv.say c, mv.hand⟩⟩ ::
          stepsFrom name a bad hid n c (i + 1) rs mvs := rfl
    rw [hstep] at h
    obtain ⟨x, m', z, h1, h2, h3, rfl⟩ := play_cons_ok h
    obtain ⟨sx, hs, hfit, rfl⟩ := tell_inv (s := ⟨name, a, r.1, r.2, bad, hid, i, i + 1 == n,
      some ⟨fun _ => mv.say c, mv.hand⟩⟩) rfl h1
    have hm' := hear_inv (s := ⟨name, a, r.1, r.2, bad, hid, i, i + 1 == n,
      some ⟨fun _ => mv.say c, mv.hand⟩⟩) rfl h2
    subst hm'
    obtain ⟨i1, i2, i3⟩ := played_of_stepsFrom name a bad hid n c rs mvs (i + 1) ds back.tail _ z
      (Nat.succ.inj hl) h3
    have hs' : mv.say c m.shown m.st = .ok sx := hs
    refine ⟨?_, ?_, ?_⟩
    · simp only [playedFrom, hs']
      exact congrArg (Option.map _) i1
    · simp only [fitsFrom, hs', Bool.and_eq_true]
      exact ⟨hfit, i2⟩
    · show z.2 = _
      rw [i3]
      simp [stateFrom, roundsOf, List.append_assoc]

/-- **One `Part`: what `play` has returned is the list of `playedFrom`**; also `fitsFrom` is true,
and the state y.2 is written out. hl: as many declared rounds as moves. No hypothesis on a stop test
or on a message's shape. -/
theorem played_of_steps (p : Part V W X) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins) (ds : List Fmt.Drawn)
    (back : List Fmt.RoundView) (m : Mid W X) (y : List Played × Mid W X)
    (hl : rs.length = p.moves.length) (h : play (p.steps name a rs v c) ds back m = .ok y) :
    playedFrom name a c p.moves m.st m.shown ds = some y.1 ∧
      fitsFrom c rs p.moves m.st m.shown ds = true ∧
      y.2 = ⟨stateFrom p.moves m.st ds, m.loc ++ ds, m.seen ++ roundsOf y.1, m.opened⟩ := by
  rw [steps_eq] at h
  exact played_of_stepsFrom name a p.bad _ p.moves.length c rs p.moves 0 ds back m y hl h

/-- **A list of `Part`s: what `play` has returned is the list of `playedRow`**; also `fitsRow` is
true, and the state y.2 is written out. Its one hypothesis beside `play`'s return: as many declared
rounds as moves. No hypothesis on a stop test or on a message's shape. -/
theorem played_of_play (name : String) (a : Place) (v : Option V) :
    ∀ (ps : List (Part V W X)) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle))
      (c : RowCoins ps) (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid W X)
      (y : List Played × Mid W X), rs.length = (ps.map (·.moves.length)).sum →
      play (rowSteps name a v ps j rs c) ds back m = .ok y →
      playedRow name a ps j c m.st m.shown ds = some y.1 ∧
        fitsRow ps rs c m.st m.shown ds = true ∧
        y.2 = ⟨stateRow ps m.st ds, m.loc ++ ds, m.seen ++ roundsOf y.1, m.opened⟩
  | [], _, rs, _, ds, back, m, y, hl, h => by
    have hr : rs = [] := List.eq_nil_of_length_eq_zero hl
    have hd : ds = [] := List.eq_nil_of_length_eq_zero (play_lengths _ _ _ _ _ h)
    subst hr
    subst hd
    have e : y = ([], m) := (Except.ok.inj h).symm
    subst e
    refine ⟨rfl, rfl, ?_⟩
    simp [stateRow, roundsOf]
  | p :: ps, j, rs, c, ds, back, m, y, hl, h => by
    rw [List.map_cons, List.sum_cons] at hl
    have hr1 : (rs.take p.moves.length).length = p.moves.length := by
      rw [List.length_take]
      omega
    have hr2 : (rs.drop p.moves.length).length = (ps.map (·.moves.length)).sum := by
      rw [List.length_drop]
      omega
    have hs1 : (p.steps name ⟨a, j⟩ (rs.take p.moves.length) v c.1).length = p.moves.length := by
      rw [steps_length, hr1, Nat.min_self]
    have h' : play (p.steps name ⟨a, j⟩ (rs.take p.moves.length) v c.1 ++
      rowSteps name a v ps (j + 1) (rs.drop p.moves.length) c.2) ds back m = .ok y := h
    have hlen := play_lengths _ _ _ _ _ h'
    rw [List.length_append, hs1] at hlen
    have hd1 : (ds.take p.moves.length).length =
        (p.steps name ⟨a, j⟩ (rs.take p.moves.length) v c.1).length := by
      rw [hs1, List.length_take]
      omega
    rw [← List.take_append_drop p.moves.length ds, play_append _ _ _ _ _ _ hd1] at h'
    obtain ⟨y₁, e1, h'⟩ := exBind_ok h'
    obtain ⟨z, e2, rfl⟩ := exMap_ok h'
    obtain ⟨a1, a2, a3⟩ := played_of_steps p name ⟨a, j⟩ _ v c.1 _ back m y₁ hr1 e1
    obtain ⟨b1, b2, b3⟩ := played_of_play name a v ps (j + 1) _ c.2 _ _ y₁.2 z hr2 e2
    rw [a3] at b1 b2 b3
    refine ⟨?_, ?_, ?_⟩
    · simp only [playedRow]
      rw [a1]
      exact congrArg (Option.map (y₁.1 ++ ·)) b1
    · simp only [fitsRow, Bool.and_eq_true]
      rw [alone_of_played a1]
      exact ⟨a2, b2⟩
    · show z.2 = _
      rw [b3]
      simp only [stateRow, roundsOf, List.map_append, List.append_assoc, List.take_append_drop]

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.play_steps_silent
#print axioms ProofFile.Honest.Small.play_row_whole
#print axioms ProofFile.Honest.Small.play_lengths
#print axioms ProofFile.Honest.Small.played_of_steps
#print axioms ProofFile.Honest.Small.played_of_play
#print axioms ProofFile.Honest.Small.playedRow
#print axioms ProofFile.Honest.Small.stateRow
#print axioms ProofFile.Honest.Small.fitsRow
#print axioms ProofFile.Honest.Small.stop_split
#print axioms ProofFile.Honest.Small.tell_at
#print axioms ProofFile.Honest.Small.hear_at
#print axioms ProofFile.Honest.Small.tell_inv
#print axioms ProofFile.Honest.Small.hear_inv
#print axioms ProofFile.Honest.Small.play_stepsFrom_silent
#print axioms ProofFile.Honest.Small.silent_of_stopAt
#print axioms ProofFile.Honest.Small.alone_of_played
#print axioms ProofFile.Honest.Small.played_of_stepsFrom
