-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/Lift.lean: A PART THAT IS ADAPTED TO A WIDER INPUT AND STATE,
HANDED ITS COINS OUT OF MORE, OR JOINED WITH ANOTHER, PLAYED ALONE: what `Part.lift`, `Move.recoin`
and `Part.andThen` (Honest/Frame.lean) make of `alone`, `fitsFrom`, `stateFrom` and `playedFrom`
(Terms.lean, Plays.lean and PlaysWhole.lean of this folder); and moves in a row. General in the
part: no sumcheck is named. Statements with their proofs.

TWO PREMISES ON A LIFT, which the frame asks nowhere. (1) `get (set x y) = y`: what the part lays
back into the wider state is what it reads there next: asked for the rounds, the shapes and the
narrowed state. (2) `set x (get x) = x`: to lay back what was read turns nothing: asked, with moves
that hand on what they were handed, for THE WIDE STATE behind the moves. A lift whose part has no
state of its own (`Unit`; get := fun _ => (), set := fun x _ => x) meets both: `alone_lift_unit`,
`lift_stateFrom_unit`.
Main names:
  `lift_aloneFrom`, `lift_fitsFrom`, `lift_playedFrom`, `lift_stateFrom`: the lifted moves at a
    state do what the moves do at the narrowed state. `stateFrom_input`, `stateFrom_heard`: the
    input stays; the challenges are heard.
  `lift_stateFrom_same`: **the wide state behind lifted moves that hand on what they were handed.**
  `alone_lift`: **a lifted part, played alone, says what the part says at the narrowed state.**
  `aloneFrom_recoin`, `fitsFrom_recoin`, `playedFrom_recoin`, `stateFrom_recoin`: moves that take
    their coins out of more.
  `aloneFrom_append`, `fitsFrom_append`, `playedFrom_append`, `stateFrom_append`: moves in a row.
  `stopBoth_none`, `bad_andThen`, `hid_andThen`: two stops that never stop, joined, never stop.
  `alone_andThen`, `fitsFrom_andThen`, `playedFrom_andThen`, `stateFrom_andThen`: **two parts as
    one.**

Limits. Of stops only that two which never stop, joined, never stop. In a row of moves, and in two
parts as one, the second stretch is handed the columns that the first was handed (`Seen.plus` keeps
`opened`): these laws speak of stretches between which the player opens no column. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.PlaysWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open VerifiableInference.Desc (Oracle)

variable {V V' W W' X Y C C' : Type}

/-! ## A lift -/

/-- The lifted moves, played alone at a state, say what the moves say at the narrowed state. -/
theorem lift_aloneFrom (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hgs : ∀ x y, get (set x y) = y) (c : C) :
    ∀ (mvs : List (Move C W' Y)) (t : State W X) (seen : Seen) (ds : List Fmt.Drawn),
      aloneFrom c (mvs.map (Move.lift wit get set)) t seen ds =
        aloneFrom c mvs (t.narrow wit get) seen ds
  | [], _, _, [] => rfl
  | [], _, _, _ :: _ => rfl
  | _ :: _, _, _, [] => rfl
  | mv :: mvs, t, seen, d :: ds => by
    have hs : (Move.lift wit get set mv).say c seen t = mv.say c seen (t.narrow wit get) := rfl
    rw [List.map_cons]
    cases hx : mv.say c seen (t.narrow wit get) with
    | error e => simp only [aloneFrom, hs, hx]
    | ok x =>
      simp only [aloneFrom, hs, hx]
      rw [lift_aloneFrom wit get set hgs c mvs]
      have e : State.narrow wit get
          ({ t.hears d with own := (Move.lift wit get set mv).hand (t.hears d) } : State W X) =
          { (t.narrow wit get).hears d with own := mv.hand ((t.narrow wit get).hears d) } := by
        show (⟨wit t.input, t.heard ++ [d],
          get (set t.own (mv.hand ((t.hears d).narrow wit get)))⟩ : State W' Y) = _
        rw [hgs]
        rfl
      rw [e]

/-- The test on shapes at the lifted moves is the test at the moves, at the narrowed state. -/
theorem lift_fitsFrom (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hgs : ∀ x y, get (set x y) = y) (c : C) :
    ∀ (rs : List (Fmt.DeclaredRound × List Oracle)) (mvs : List (Move C W' Y)) (t : State W X)
      (seen : Seen) (ds : List Fmt.Drawn),
      fitsFrom c rs (mvs.map (Move.lift wit get set)) t seen ds =
        fitsFrom c rs mvs (t.narrow wit get) seen ds
  | [], [], _, _, [] => rfl
  | [], [], _, _, _ :: _ => rfl
  | [], _ :: _, _, _, _ => rfl
  | _ :: _, [], _, _, _ => rfl
  | _ :: _, _ :: _, _, _, [] => rfl
  | r :: rs, mv :: mvs, t, seen, d :: ds => by
    have hs : (Move.lift wit get set mv).say c seen t = mv.say c seen (t.narrow wit get) := rfl
    rw [List.map_cons]
    cases hx : mv.say c seen (t.narrow wit get) with
    | error e => simp only [fitsFrom, hs, hx]
    | ok x =>
      simp only [fitsFrom, hs, hx]
      rw [lift_fitsFrom wit get set hgs c rs mvs]
      have e : State.narrow wit get
          ({ t.hears d with own := (Move.lift wit get set mv).hand (t.hears d) } : State W X) =
          { (t.narrow wit get).hears d with own := mv.hand ((t.narrow wit get).hears d) } := by
        show (⟨wit t.input, t.heard ++ [d],
          get (set t.own (mv.hand ((t.hears d).narrow wit get)))⟩ : State W' Y) = _
        rw [hgs]
        rfl
      rw [e]

/-- The state behind the lifted moves, narrowed, is the state behind the moves. -/
theorem lift_stateFrom (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hgs : ∀ x y, get (set x y) = y) :
    ∀ (mvs : List (Move C W' Y)) (t : State W X) (ds : List Fmt.Drawn),
      (stateFrom (mvs.map (Move.lift wit get set)) t ds).narrow wit get =
        stateFrom mvs (t.narrow wit get) ds
  | [], _, _ => rfl
  | _ :: _, _, [] => rfl
  | mv :: mvs, t, d :: ds => by
    show (stateFrom (mvs.map (Move.lift wit get set))
      { t.hears d with own := (Move.lift wit get set mv).hand (t.hears d) } ds).narrow wit get = _
    rw [lift_stateFrom wit get set hgs mvs]
    have e : State.narrow wit get
        ({ t.hears d with own := (Move.lift wit get set mv).hand (t.hears d) } : State W X) =
        { (t.narrow wit get).hears d with own := mv.hand ((t.narrow wit get).hears d) } := by
      show (⟨wit t.input, t.heard ++ [d],
        get (set t.own (mv.hand ((t.hears d).narrow wit get)))⟩ : State W' Y) = _
      rw [hgs]
      rfl
    rw [e]
    rfl

/-- The input stays. -/
theorem stateFrom_input : ∀ (mvs : List (Move C W X)) (t : State W X) (ds : List Fmt.Drawn),
    (stateFrom mvs t ds).input = t.input
  | [], _, _ => rfl
  | _ :: _, _, [] => rfl
  | mv :: mvs, t, d :: ds => by
    show (stateFrom mvs { t.hears d with own := mv.hand (t.hears d) } ds).input = _
    rw [stateFrom_input mvs]
    rfl

/-- The challenges are heard. -/
theorem stateFrom_heard : ∀ (mvs : List (Move C W X)) (t : State W X) (ds : List Fmt.Drawn),
    mvs.length = ds.length → (stateFrom mvs t ds).heard = t.heard ++ ds
  | [], _, [], _ => (List.append_nil _).symm
  | mv :: mvs, t, d :: ds, h => by
    show (stateFrom mvs { t.hears d with own := mv.hand (t.hears d) } ds).heard = _
    rw [stateFrom_heard mvs _ ds (by simp only [List.length_cons] at h; omega)]
    show (t.heard ++ [d]) ++ ds = _
    rw [List.append_assoc]
    rfl
  | [], _, _ :: _, h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ :: _, _, [], h => by simp only [List.length_cons, List.length_nil] at h; omega

/-- **A lifted part, played alone, says what the part says at the narrowed state.** -/
theorem alone_lift (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hgs : ∀ x y, get (set x y) = y) (p : Part V' W' Y) (c : p.Coins) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn) :
    alone (p.lift see wit get set) c t seen ds = alone p c (t.narrow wit get) seen ds :=
  lift_aloneFrom wit get set hgs c p.moves t seen ds

/-- The rounds as played of the lifted moves are those of the moves at the narrowed state. -/
theorem lift_playedFrom (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hgs : ∀ x y, get (set x y) = y) (name : String) (a : Addr) (c : C) :
    ∀ (mvs : List (Move C W' Y)) (t : State W X) (seen : Seen) (ds : List Fmt.Drawn),
      playedFrom name a c (mvs.map (Move.lift wit get set)) t seen ds =
        playedFrom name a c mvs (t.narrow wit get) seen ds
  | [], _, _, [] => rfl
  | [], _, _, _ :: _ => rfl
  | _ :: _, _, _, [] => rfl
  | mv :: mvs, t, seen, d :: ds => by
    have hs : (Move.lift wit get set mv).say c seen t = mv.say c seen (t.narrow wit get) := rfl
    rw [List.map_cons]
    cases hx : mv.say c seen (t.narrow wit get) with
    | error e => simp only [playedFrom, hs, hx]
    | ok x =>
      simp only [playedFrom, hs, hx]
      rw [lift_playedFrom wit get set hgs name a c mvs]
      have e : State.narrow wit get
          ({ t.hears d with own := (Move.lift wit get set mv).hand (t.hears d) } : State W X) =
          { (t.narrow wit get).hears d with own := mv.hand ((t.narrow wit get).hears d) } := by
        show (⟨wit t.input, t.heard ++ [d],
          get (set t.own (mv.hand ((t.hears d).narrow wit get)))⟩ : State W' Y) = _
        rw [hgs]
        rfl
      rw [e]

/-- **The wide state behind lifted moves that hand on what they were handed**: it has heard the
challenges; nothing else turns. -/
theorem lift_stateFrom_same (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hsg : ∀ x, set x (get x) = x) :
    ∀ (mvs : List (Move C W' Y)) (t : State W X) (ds : List Fmt.Drawn),
      (∀ mv ∈ mvs, ∀ s, mv.hand s = s.own) → mvs.length = ds.length →
      stateFrom (mvs.map (Move.lift wit get set)) t ds = ⟨t.input, t.heard ++ ds, t.own⟩
  | [], t, [], _, _ => by
    show t = _
    rw [List.append_nil]
  | mv :: mvs, t, d :: ds, hm, hl => by
    have e : ({ t.hears d with own := (Move.lift wit get set mv).hand (t.hears d) } : State W X) =
        t.hears d := by
      show (⟨t.input, t.heard ++ [d], set t.own (mv.hand ((t.hears d).narrow wit get))⟩ :
        State W X) = _
      rw [hm mv List.mem_cons_self]
      show (⟨t.input, t.heard ++ [d], set t.own (get t.own)⟩ : State W X) = _
      rw [hsg]
      rfl
    show stateFrom (mvs.map (Move.lift wit get set))
      { t.hears d with own := (Move.lift wit get set mv).hand (t.hears d) } ds = _
    rw [e, lift_stateFrom_same wit get set hsg mvs _ ds
      (fun x hx => hm x (List.mem_cons_of_mem _ hx))
      (by simp only [List.length_cons] at hl; omega)]
    show (⟨t.input, (t.heard ++ [d]) ++ ds, t.own⟩ : State W X) = _
    rw [List.append_assoc]
    rfl
  | [], _, _ :: _, _, hl => by simp only [List.length_cons, List.length_nil] at hl; omega
  | _ :: _, _, [], _, hl => by simp only [List.length_cons, List.length_nil] at hl; omega

/-- An instance: the lift of a part that has no state of its own meets the first premise. -/
theorem alone_lift_unit (see : V → V') (wit : W → W') (p : Part V' W' Unit) (c : p.Coins)
    (t : State W X) (seen : Seen) (ds : List Fmt.Drawn) :
    alone (p.lift see wit (fun _ : X => ()) (fun x _ => x)) c t seen ds =
      alone p c (t.narrow wit fun _ => ()) seen ds :=
  alone_lift see wit (fun _ => ()) (fun x _ => x) (fun _ _ => rfl) p c t seen ds

/-- An instance: it meets the second premise too. -/
theorem lift_stateFrom_unit (wit : W → W') (mvs : List (Move C W' Unit)) (t : State W X)
    (ds : List Fmt.Drawn) (hl : mvs.length = ds.length) :
    stateFrom (mvs.map (Move.lift wit (fun _ : X => ()) (fun x _ => x))) t ds =
      ⟨t.input, t.heard ++ ds, t.own⟩ :=
  lift_stateFrom_same wit (fun _ => ()) (fun x _ => x) (fun _ => rfl) mvs t ds
    (fun _ _ _ => rfl) hl

/-! ## Coins out of more -/

/-- Moves that take their coins out of more say what the moves say at these coins. -/
theorem aloneFrom_recoin (cut : C → C') (c : C) :
    ∀ (mvs : List (Move C' W X)) (t : State W X) (seen : Seen) (ds : List Fmt.Drawn),
      aloneFrom c (mvs.map (Move.recoin cut)) t seen ds = aloneFrom (cut c) mvs t seen ds
  | [], _, _, [] => rfl
  | [], _, _, _ :: _ => rfl
  | _ :: _, _, _, [] => rfl
  | mv :: mvs, t, seen, d :: ds => by
    have hs : (Move.recoin cut mv).say c seen t = mv.say (cut c) seen t := rfl
    have hh : ∀ s, (Move.recoin cut mv).hand s = mv.hand s := fun _ => rfl
    rw [List.map_cons]
    cases hx : mv.say (cut c) seen t with
    | error e => simp only [aloneFrom, hs, hx]
    | ok x =>
      simp only [aloneFrom, hs, hx, hh]
      rw [aloneFrom_recoin cut c mvs]

/-- The test on shapes at such moves. -/
theorem fitsFrom_recoin (cut : C → C') (c : C) :
    ∀ (rs : List (Fmt.DeclaredRound × List Oracle)) (mvs : List (Move C' W X)) (t : State W X)
      (seen : Seen) (ds : List Fmt.Drawn),
      fitsFrom c rs (mvs.map (Move.recoin cut)) t seen ds = fitsFrom (cut c) rs mvs t seen ds
  | [], [], _, _, [] => rfl
  | [], [], _, _, _ :: _ => rfl
  | [], _ :: _, _, _, _ => rfl
  | _ :: _, [], _, _, _ => rfl
  | _ :: _, _ :: _, _, _, [] => rfl
  | r :: rs, mv :: mvs, t, seen, d :: ds => by
    have hs : (Move.recoin cut mv).say c seen t = mv.say (cut c) seen t := rfl
    have hh : ∀ s, (Move.recoin cut mv).hand s = mv.hand s := fun _ => rfl
    rw [List.map_cons]
    cases hx : mv.say (cut c) seen t with
    | error e => simp only [fitsFrom, hs, hx]
    | ok x =>
      simp only [fitsFrom, hs, hx, hh]
      rw [fitsFrom_recoin cut c rs mvs]

/-- The state behind such moves: no coin is read. -/
theorem stateFrom_recoin (cut : C → C') :
    ∀ (mvs : List (Move C' W X)) (t : State W X) (ds : List Fmt.Drawn),
      stateFrom (mvs.map (Move.recoin cut)) t ds = stateFrom mvs t ds
  | [], _, _ => rfl
  | _ :: _, _, [] => rfl
  | mv :: mvs, t, d :: ds => by
    show stateFrom (mvs.map (Move.recoin cut)) { t.hears d with own := mv.hand (t.hears d) } ds = _
    rw [stateFrom_recoin cut mvs]
    rfl

/-- The rounds as played of such moves. -/
theorem playedFrom_recoin (cut : C → C') (name : String) (a : Addr) (c : C) :
    ∀ (mvs : List (Move C' W X)) (t : State W X) (seen : Seen) (ds : List Fmt.Drawn),
      playedFrom name a c (mvs.map (Move.recoin cut)) t seen ds =
        playedFrom name a (cut c) mvs t seen ds
  | [], _, _, [] => rfl
  | [], _, _, _ :: _ => rfl
  | _ :: _, _, _, [] => rfl
  | mv :: mvs, t, seen, d :: ds => by
    have hs : (Move.recoin cut mv).say c seen t = mv.say (cut c) seen t := rfl
    have hh : ∀ s, (Move.recoin cut mv).hand s = mv.hand s := fun _ => rfl
    rw [List.map_cons]
    cases hx : mv.say (cut c) seen t with
    | error e => simp only [playedFrom, hs, hx]
    | ok x =>
      simp only [playedFrom, hs, hx, hh]
      rw [playedFrom_recoin cut name a c mvs]

/-! ## Moves in a row -/

/-- Moves in a row, played alone: the first stretch; then the second, from the state behind the
first and behind what it has shown. -/
theorem aloneFrom_append (c : C) : ∀ (l₁ l₂ : List (Move C W X)) (t : State W X)
    (seen : Seen) (d₁ d₂ : List Fmt.Drawn), l₁.length = d₁.length →
    aloneFrom c (l₁ ++ l₂) t seen (d₁ ++ d₂) =
      (aloneFrom c l₁ t seen d₁).bind fun o₁ =>
        (aloneFrom c l₂ (stateFrom l₁ t d₁) (seen.plus o₁) d₂).map (o₁ ++ ·)
  | [], l₂, t, seen, [], d₂, _ => by
    show aloneFrom c l₂ t seen d₂ = (aloneFrom c l₂ t (seen.plus []) d₂).map ([] ++ ·)
    rw [Seen.plus_nil]
    simp
  | mv :: l₁, l₂, t, seen, d :: d₁, d₂, h => by
    rw [List.cons_append, List.cons_append]
    cases hx : mv.say c seen t with
    | error e => simp only [aloneFrom, hx, Option.bind_none]
    | ok x =>
      simp only [aloneFrom, hx]
      rw [aloneFrom_append c l₁ l₂ _ _ d₁ d₂ (by simp only [List.length_cons] at h; omega)]
      cases ho : aloneFrom c l₁ { t.hears d with own := mv.hand (t.hears d) }
          (seen.plus [⟨x.vals.map Said.got, d⟩]) d₁ with
      | none => rfl
      | some o₁ =>
        simp only [Option.bind_some, Option.map_some, stateFrom, Seen.plus_plus,
          List.cons_append, List.nil_append, Option.map_map]
        rfl
  | [], _, _, _, _ :: _, _, h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ :: _, _, _, _, [], _, h => by simp only [List.length_cons, List.length_nil] at h; omega

/-- The state behind moves in a row. -/
theorem stateFrom_append : ∀ (l₁ l₂ : List (Move C W X)) (t : State W X)
    (d₁ d₂ : List Fmt.Drawn), l₁.length = d₁.length →
    stateFrom (l₁ ++ l₂) t (d₁ ++ d₂) = stateFrom l₂ (stateFrom l₁ t d₁) d₂
  | [], _, _, [], _, _ => rfl
  | mv :: l₁, l₂, t, d :: d₁, d₂, h => by
    show stateFrom (l₁ ++ l₂) { t.hears d with own := mv.hand (t.hears d) } (d₁ ++ d₂) = _
    rw [stateFrom_append l₁ l₂ _ d₁ d₂ (by simp only [List.length_cons] at h; omega)]
    rfl
  | [], _, _, _ :: _, _, h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ :: _, _, _, [], _, h => by simp only [List.length_cons, List.length_nil] at h; omega

/-- The test on shapes at moves in a row. o₁: what the first stretch shows. -/
theorem fitsFrom_append (c : C) : ∀ (r₁ r₂ : List (Fmt.DeclaredRound × List Oracle))
    (l₁ l₂ : List (Move C W X)) (t : State W X) (seen : Seen) (d₁ d₂ : List Fmt.Drawn)
    (o₁ : List Fmt.RoundView), r₁.length = l₁.length → aloneFrom c l₁ t seen d₁ = some o₁ →
    fitsFrom c (r₁ ++ r₂) (l₁ ++ l₂) t seen (d₁ ++ d₂) =
      (fitsFrom c r₁ l₁ t seen d₁ && fitsFrom c r₂ l₂ (stateFrom l₁ t d₁) (seen.plus o₁) d₂)
  | [], r₂, [], l₂, t, seen, [], d₂, o₁, _, ho => by
    have e : o₁ = [] := (Option.some.inj ho).symm
    rw [e, Seen.plus_nil]
    rfl
  | r :: r₁, r₂, mv :: l₁, l₂, t, seen, d :: d₁, d₂, o₁, hr, ho => by
    rw [List.cons_append, List.cons_append, List.cons_append]
    cases hx : mv.say c seen t with
    | error e =>
      simp only [aloneFrom, hx] at ho
      cases ho
    | ok x =>
      simp only [aloneFrom, hx, Option.map_eq_some_iff] at ho
      obtain ⟨o', ho', rfl⟩ := ho
      simp only [fitsFrom, hx]
      rw [fitsFrom_append c r₁ r₂ l₁ l₂ _ _ d₁ d₂ o'
        (by simp only [List.length_cons] at hr; omega) ho', Bool.and_assoc]
      simp only [stateFrom, Seen.plus_plus, List.cons_append, List.nil_append]
  | [], _, [], _, _, _, _ :: _, _, _, _, ho => by simp [aloneFrom] at ho
  | _ :: _, _, _ :: _, _, _, _, [], _, _, _, ho => by simp [aloneFrom] at ho
  | [], _, _ :: _, _, _, _, _, _, _, hr, _ => by
    simp only [List.length_cons, List.length_nil] at hr
    omega
  | _ :: _, _, [], _, _, _, _, _, _, hr, _ => by
    simp only [List.length_cons, List.length_nil] at hr
    omega

/-- The rounds as played of moves in a row. -/
theorem playedFrom_append (name : String) (a : Addr) (c : C) :
    ∀ (l₁ l₂ : List (Move C W X)) (t : State W X) (seen : Seen) (d₁ d₂ : List Fmt.Drawn),
      l₁.length = d₁.length →
      playedFrom name a c (l₁ ++ l₂) t seen (d₁ ++ d₂) =
        (playedFrom name a c l₁ t seen d₁).bind fun o₁ =>
          (playedFrom name a c l₂ (stateFrom l₁ t d₁) (seen.plus (roundsOf o₁)) d₂).map (o₁ ++ ·)
  | [], l₂, t, seen, [], d₂, _ => by
    show playedFrom name a c l₂ t seen d₂ =
      (playedFrom name a c l₂ t (seen.plus []) d₂).map ([] ++ ·)
    rw [Seen.plus_nil]
    simp
  | mv :: l₁, l₂, t, seen, d :: d₁, d₂, h => by
    rw [List.cons_append, List.cons_append]
    cases hx : mv.say c seen t with
    | error e => simp only [playedFrom, hx, Option.bind_none]
    | ok x =>
      simp only [playedFrom, hx]
      rw [playedFrom_append name a c l₁ l₂ _ _ d₁ d₂
        (by simp only [List.length_cons] at h; omega)]
      cases ho : playedFrom name a c l₁ { t.hears d with own := mv.hand (t.hears d) }
          (seen.plus [⟨x.vals.map Said.got, d⟩]) d₁ with
      | none => rfl
      | some o₁ =>
        simp only [Option.bind_some, Option.map_some, stateFrom, roundsOf, List.map_cons,
          Seen.plus_plus, List.cons_append, List.nil_append, Option.map_map]
        rfl
  | [], _, _, _, _ :: _, _, h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ :: _, _, _, _, [], _, h => by simp only [List.length_cons, List.length_nil] at h; omega

/-! ## Two parts as one -/

/-- Two stops that never stop, joined, never stop. -/
theorem stopBoth_none (n m : Nat) (f g : List Fmt.Drawn → List Fmt.Drawn → Option String)
    (hf : ∀ a b, f a b = none) (hg : ∀ a b, g a b = none) (front own : List Fmt.Drawn) :
    stopBoth n m f g front own = none := by
  unfold stopBoth
  rw [hf, hg, ite_self, ite_self]
  rfl

/-- The first stop of two parts as one never stops, where neither part's does. -/
theorem bad_andThen (p q : Part V W X) (hp : ∀ f o, p.bad f o = none)
    (hq : ∀ f o, q.bad f o = none) (f o : List Fmt.Drawn) : (p.andThen q).bad f o = none :=
  stopBoth_none _ _ _ _ hp hq f o

/-- The like of the second stop. -/
theorem hid_andThen (p q : Part V W X) (hp : ∀ v f o, p.hid v f o = none)
    (hq : ∀ v f o, q.hid v f o = none) (v : V) (f o : List Fmt.Drawn) :
    (p.andThen q).hid v f o = none :=
  stopBoth_none _ _ _ _ (hp v) (hq v) f o

/-- Two stretches of moves, each taking its coins out of more, played alone. -/
theorem aloneFrom_two {C₁ C₂ : Type} (cut₁ : C → C₁) (cut₂ : C → C₂) (c : C)
    (l₁ : List (Move C₁ W X)) (l₂ : List (Move C₂ W X)) (t : State W X) (seen : Seen)
    (d₁ d₂ : List Fmt.Drawn) (h : l₁.length = d₁.length) :
    aloneFrom c (l₁.map (Move.recoin cut₁) ++ l₂.map (Move.recoin cut₂)) t seen (d₁ ++ d₂) =
      (aloneFrom (cut₁ c) l₁ t seen d₁).bind fun o₁ =>
        (aloneFrom (cut₂ c) l₂ (stateFrom l₁ t d₁) (seen.plus o₁) d₂).map (o₁ ++ ·) := by
  rw [aloneFrom_append c _ _ t seen d₁ d₂ (by rw [List.length_map]; exact h), aloneFrom_recoin,
    stateFrom_recoin]
  simp only [aloneFrom_recoin]

/-- The state behind two such stretches. -/
theorem stateFrom_two {C₁ C₂ : Type} (cut₁ : C → C₁) (cut₂ : C → C₂) (l₁ : List (Move C₁ W X))
    (l₂ : List (Move C₂ W X)) (t : State W X) (d₁ d₂ : List Fmt.Drawn)
    (h : l₁.length = d₁.length) :
    stateFrom (l₁.map (Move.recoin cut₁) ++ l₂.map (Move.recoin cut₂)) t (d₁ ++ d₂) =
      stateFrom l₂ (stateFrom l₁ t d₁) d₂ := by
  rw [stateFrom_append _ _ t d₁ d₂ (by rw [List.length_map]; exact h), stateFrom_recoin,
    stateFrom_recoin]

/-- The test on shapes at two such stretches. o₁: what the first shows. -/
theorem fitsFrom_two {C₁ C₂ : Type} (cut₁ : C → C₁) (cut₂ : C → C₂) (c : C)
    (r₁ r₂ : List (Fmt.DeclaredRound × List Oracle)) (l₁ : List (Move C₁ W X))
    (l₂ : List (Move C₂ W X)) (t : State W X) (seen : Seen) (d₁ d₂ : List Fmt.Drawn)
    (o₁ : List Fmt.RoundView) (hr : r₁.length = l₁.length)
    (ho : aloneFrom (cut₁ c) l₁ t seen d₁ = some o₁) :
    fitsFrom c (r₁ ++ r₂) (l₁.map (Move.recoin cut₁) ++ l₂.map (Move.recoin cut₂)) t seen
        (d₁ ++ d₂) =
      (fitsFrom (cut₁ c) r₁ l₁ t seen d₁ &&
        fitsFrom (cut₂ c) r₂ l₂ (stateFrom l₁ t d₁) (seen.plus o₁) d₂) := by
  rw [fitsFrom_append c r₁ r₂ _ _ t seen d₁ d₂ o₁ (by rw [List.length_map]; exact hr)
    (by rw [aloneFrom_recoin]; exact ho), fitsFrom_recoin, fitsFrom_recoin, stateFrom_recoin]

/-- The rounds as played of two such stretches. -/
theorem playedFrom_two {C₁ C₂ : Type} (cut₁ : C → C₁) (cut₂ : C → C₂) (name : String) (a : Addr)
    (c : C) (l₁ : List (Move C₁ W X)) (l₂ : List (Move C₂ W X)) (t : State W X)
    (seen : Seen) (d₁ d₂ : List Fmt.Drawn) (h : l₁.length = d₁.length) :
    playedFrom name a c (l₁.map (Move.recoin cut₁) ++ l₂.map (Move.recoin cut₂)) t seen
        (d₁ ++ d₂) =
      (playedFrom name a (cut₁ c) l₁ t seen d₁).bind fun o₁ =>
        (playedFrom name a (cut₂ c) l₂ (stateFrom l₁ t d₁) (seen.plus (roundsOf o₁)) d₂).map
          (o₁ ++ ·) := by
  rw [playedFrom_append name a c _ _ t seen d₁ d₂ (by rw [List.length_map]; exact h),
    playedFrom_recoin, stateFrom_recoin]
  simp only [playedFrom_recoin]

/-- **Two parts as one, played alone**: the first part at its share of the coins; then the second at
its share, from the state behind the first and behind what it has shown. -/
theorem alone_andThen (p q : Part V W X) (c : (p.andThen q).Coins) (t : State W X)
    (seen : Seen) (d₁ d₂ : List Fmt.Drawn) (h : p.moves.length = d₁.length) :
    alone (p.andThen q) c t seen (d₁ ++ d₂) =
      (alone p (handFst c) t seen d₁).bind fun o₁ =>
        (alone q (handSnd c) (stateFrom p.moves t d₁) (seen.plus o₁) d₂).map (o₁ ++ ·) :=
  aloneFrom_two handFst handSnd c p.moves q.moves t seen d₁ d₂ h

/-- The state behind two parts as one. -/
theorem stateFrom_andThen (p q : Part V W X) (t : State W X) (d₁ d₂ : List Fmt.Drawn)
    (h : p.moves.length = d₁.length) :
    stateFrom (p.andThen q).moves t (d₁ ++ d₂) = stateFrom q.moves (stateFrom p.moves t d₁) d₂ :=
  stateFrom_two handFst handSnd p.moves q.moves t d₁ d₂ h

/-- The test on shapes at two parts as one. o₁: what the first part shows. -/
theorem fitsFrom_andThen (p q : Part V W X) (c : (p.andThen q).Coins)
    (r₁ r₂ : List (Fmt.DeclaredRound × List Oracle)) (t : State W X) (seen : Seen)
    (d₁ d₂ : List Fmt.Drawn) (o₁ : List Fmt.RoundView) (hr : r₁.length = p.moves.length)
    (ho : alone p (handFst c) t seen d₁ = some o₁) :
    fitsFrom c (r₁ ++ r₂) (p.andThen q).moves t seen (d₁ ++ d₂) =
      (fitsFrom (handFst c) r₁ p.moves t seen d₁ &&
        fitsFrom (handSnd c) r₂ q.moves (stateFrom p.moves t d₁) (seen.plus o₁) d₂) :=
  fitsFrom_two handFst handSnd c r₁ r₂ p.moves q.moves t seen d₁ d₂ o₁ hr ho

/-- The rounds as played of two parts as one. -/
theorem playedFrom_andThen (p q : Part V W X) (name : String) (a : Addr)
    (c : (p.andThen q).Coins) (t : State W X) (seen : Seen) (d₁ d₂ : List Fmt.Drawn)
    (h : p.moves.length = d₁.length) :
    playedFrom name a c (p.andThen q).moves t seen (d₁ ++ d₂) =
      (playedFrom name a (handFst c) p.moves t seen d₁).bind fun o₁ =>
        (playedFrom name a (handSnd c) q.moves (stateFrom p.moves t d₁) (seen.plus (roundsOf o₁))
          d₂).map (o₁ ++ ·) :=
  playedFrom_two handFst handSnd name a c p.moves q.moves t seen d₁ d₂ h

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.lift_aloneFrom
#print axioms ProofFile.Honest.SumLaw.lift_fitsFrom
#print axioms ProofFile.Honest.SumLaw.lift_stateFrom
#print axioms ProofFile.Honest.SumLaw.stateFrom_input
#print axioms ProofFile.Honest.SumLaw.stateFrom_heard
#print axioms ProofFile.Honest.SumLaw.alone_lift
#print axioms ProofFile.Honest.SumLaw.aloneFrom_recoin
#print axioms ProofFile.Honest.SumLaw.fitsFrom_recoin
#print axioms ProofFile.Honest.SumLaw.stateFrom_recoin
#print axioms ProofFile.Honest.SumLaw.aloneFrom_append
#print axioms ProofFile.Honest.SumLaw.lift_playedFrom
#print axioms ProofFile.Honest.SumLaw.lift_stateFrom_same
#print axioms ProofFile.Honest.SumLaw.alone_lift_unit
#print axioms ProofFile.Honest.SumLaw.lift_stateFrom_unit
#print axioms ProofFile.Honest.SumLaw.playedFrom_recoin
#print axioms ProofFile.Honest.SumLaw.stateFrom_append
#print axioms ProofFile.Honest.SumLaw.fitsFrom_append
#print axioms ProofFile.Honest.SumLaw.playedFrom_append
#print axioms ProofFile.Honest.SumLaw.stopBoth_none
#print axioms ProofFile.Honest.SumLaw.bad_andThen
#print axioms ProofFile.Honest.SumLaw.hid_andThen
#print axioms ProofFile.Honest.SumLaw.aloneFrom_two
#print axioms ProofFile.Honest.SumLaw.stateFrom_two
#print axioms ProofFile.Honest.SumLaw.fitsFrom_two
#print axioms ProofFile.Honest.SumLaw.playedFrom_two
#print axioms ProofFile.Honest.SumLaw.alone_andThen
#print axioms ProofFile.Honest.SumLaw.stateFrom_andThen
#print axioms ProofFile.Honest.SumLaw.fitsFrom_andThen
#print axioms ProofFile.Honest.SumLaw.playedFrom_andThen
