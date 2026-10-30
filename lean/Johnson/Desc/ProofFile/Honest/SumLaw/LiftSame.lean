-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/LiftSame.lean: THE MASKED SUMCHECK's PART, LIFTED, UNDER ONE
PREMISE ON THE LIFT; AND WHAT A CALLER DOES NEXT. Statements with their proofs.
  1 Moves that hand on what they were handed, lifted (`Move.lift`, Honest/Frame.lean): what they lay
     back into the wider state is what they read there. So ONE premise on the lift serves: `set x
     (get x) = x`. The other premise of Lift.lean of this folder, `get (set x y) = y`, is not asked:
     the two functions by which the frame's lift `seat` (Honest/FrameToy.lean) lifts, WRITTEN OUT
     ANEW HERE (the tie to `seat` is by reading: no statement names it), do not meet it, and meet
     the one that is asked (`seatLens_same`, `seatLens_not`, `plays_lift_seat`).
  2 At `sumPart` (Honest/Sum.lean): the frame's `play` on the steps of the lifted part: OF THE TWO
     PREMISES ON THE LIFT from that one; the three other premises are those of PlaysSum.lean's head
     (two coefficients at least; the declared rounds state the call's scalars; as many challenges as
     moves); and how many moves the lifted part has, as a number of the shape.
  3  WHAT A CALLER DOES NEXT: declared rounds that read no stored table and open no tree read
     nothing (`readsOf`, Honest/Frame.lean), so the frame's `fillCols` returns no column there; for
     a stretch of a sub-protocol's rounds the frame's `readsOf_append` and `fillCols_append`
     (Honest/Law/Cut.lean) join it. And rounds whose list of tables is empty (`tablesOf ps = []`:
     they have no root at all) leave the tables at hand (`Env.add`, Honest/Side.lean) as they were,
     where these hold no own tree from number `sent` on.
Main names:
  `same_state`, `same_narrow`: one round. `same_aloneFrom`, `same_fitsFrom`, `same_playedFrom`: the
    lifted moves at a state do what the moves do at the narrowed state.
  `alone_lift_same`: the same of a part. `plays_lift_same`: **`play` on the steps of the lifted
    part: of the two premises on the lift, from `set x (get x) = x` alone.** `plays_lift_seat`: an
    instance, at the two functions of the frame's `seat`.
  `lift_moves_length`, `lift_moves_count`: the lifted part's moves.
  `readsOf_none`, `fillCols_none`, `add_none`: the third.

Limits. Nothing on stops. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.PlaysSum
import Johnson.Desc.ProofFile.Honest.SumLaw.Counts
import Johnson.Desc.ProofFile.Honest.Side

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open VerifiableInference.Desc (Oracle)

variable {V V' W W' X Y C : Type}

/-! ## 1 Moves that hand on what they were handed, lifted -/

/-- Behind a round of such a move, lifted, the wide state has heard the challenge; nothing else
changes. -/
theorem same_state (wit : W → W') (get : X → Y) (set : X → Y → X) (hsg : ∀ x, set x (get x) = x)
    (mv : Move C W' Y) (hm : ∀ s, mv.hand s = s.own) (t : State W X) (d : Fmt.Drawn) :
    ({ t.hears d with own := (Move.lift wit get set mv).hand (t.hears d) } : State W X) =
      t.hears d := by
  show (⟨t.input, t.heard ++ [d], set t.own (mv.hand ((t.hears d).narrow wit get))⟩ :
    State W X) = _
  rw [hm]
  show (⟨t.input, t.heard ++ [d], set t.own (get t.own)⟩ : State W X) = _
  rw [hsg]
  rfl

/-- Behind a round of such a move the narrow state has heard the challenge; nothing else changes.
-/
theorem same_narrow (mv : Move C W' Y) (hm : ∀ s, mv.hand s = s.own) (t : State W' Y)
    (d : Fmt.Drawn) : ({ t.hears d with own := mv.hand (t.hears d) } : State W' Y) = t.hears d := by
  rw [hm]

/-- Such moves, lifted and played alone, say what the moves say at the narrowed state. -/
theorem same_aloneFrom (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hsg : ∀ x, set x (get x) = x) (c : C) :
    ∀ (mvs : List (Move C W' Y)) (t : State W X) (seen : Seen) (ds : List Fmt.Drawn),
      (∀ mv ∈ mvs, ∀ s, mv.hand s = s.own) →
      aloneFrom c (mvs.map (Move.lift wit get set)) t seen ds =
        aloneFrom c mvs (t.narrow wit get) seen ds
  | [], _, _, [], _ => rfl
  | [], _, _, _ :: _, _ => rfl
  | _ :: _, _, _, [], _ => rfl
  | mv :: mvs, t, seen, d :: ds, hm => by
    have hs : (Move.lift wit get set mv).say c seen t = mv.say c seen (t.narrow wit get) := rfl
    rw [List.map_cons]
    cases hx : mv.say c seen (t.narrow wit get) with
    | error e => simp only [aloneFrom, hs, hx]
    | ok x =>
      simp only [aloneFrom, hs, hx]
      rw [same_state wit get set hsg mv (hm mv List.mem_cons_self),
        same_narrow mv (hm mv List.mem_cons_self),
        same_aloneFrom wit get set hsg c mvs _ _ ds fun y hy => hm y (List.mem_cons_of_mem _ hy)]
      rfl

/-- The test on shapes says of such moves, lifted, what it says of the moves at the narrowed state.
-/
theorem same_fitsFrom (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hsg : ∀ x, set x (get x) = x) (c : C) :
    ∀ (rs : List (Fmt.DeclaredRound × List Oracle)) (mvs : List (Move C W' Y)) (t : State W X)
      (seen : Seen) (ds : List Fmt.Drawn), (∀ mv ∈ mvs, ∀ s, mv.hand s = s.own) →
      fitsFrom c rs (mvs.map (Move.lift wit get set)) t seen ds =
        fitsFrom c rs mvs (t.narrow wit get) seen ds
  | [], [], _, _, [], _ => rfl
  | [], [], _, _, _ :: _, _ => rfl
  | [], _ :: _, _, _, _, _ => rfl
  | _ :: _, [], _, _, _, _ => rfl
  | _ :: _, _ :: _, _, _, [], _ => rfl
  | r :: rs, mv :: mvs, t, seen, d :: ds, hm => by
    have hs : (Move.lift wit get set mv).say c seen t = mv.say c seen (t.narrow wit get) := rfl
    rw [List.map_cons]
    cases hx : mv.say c seen (t.narrow wit get) with
    | error e => simp only [fitsFrom, hs, hx]
    | ok x =>
      simp only [fitsFrom, hs, hx]
      rw [same_state wit get set hsg mv (hm mv List.mem_cons_self),
        same_narrow mv (hm mv List.mem_cons_self),
        same_fitsFrom wit get set hsg c rs mvs _ _ ds
          fun y hy => hm y (List.mem_cons_of_mem _ hy)]
      rfl

/-- The rounds as played of such moves, lifted, are those of the moves at the narrowed state. -/
theorem same_playedFrom (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hsg : ∀ x, set x (get x) = x) (name : String) (a : Addr) (c : C) :
    ∀ (mvs : List (Move C W' Y)) (t : State W X) (seen : Seen) (ds : List Fmt.Drawn),
      (∀ mv ∈ mvs, ∀ s, mv.hand s = s.own) →
      playedFrom name a c (mvs.map (Move.lift wit get set)) t seen ds =
        playedFrom name a c mvs (t.narrow wit get) seen ds
  | [], _, _, [], _ => rfl
  | [], _, _, _ :: _, _ => rfl
  | _ :: _, _, _, [], _ => rfl
  | mv :: mvs, t, seen, d :: ds, hm => by
    have hs : (Move.lift wit get set mv).say c seen t = mv.say c seen (t.narrow wit get) := rfl
    rw [List.map_cons]
    cases hx : mv.say c seen (t.narrow wit get) with
    | error e => simp only [playedFrom, hs, hx]
    | ok x =>
      simp only [playedFrom, hs, hx]
      rw [same_state wit get set hsg mv (hm mv List.mem_cons_self),
        same_narrow mv (hm mv List.mem_cons_self),
        same_playedFrom wit get set hsg name a c mvs _ _ ds
          fun y hy => hm y (List.mem_cons_of_mem _ hy)]
      rfl

/-- A part whose moves hand on what they were handed, lifted and played alone, says what the part
says at the narrowed state. -/
theorem alone_lift_same (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hsg : ∀ x, set x (get x) = x) (p : Part V' W' Y) (hm : ∀ mv ∈ p.moves, ∀ s, mv.hand s = s.own)
    (c : p.Coins) (t : State W X) (seen : Seen) (ds : List Fmt.Drawn) :
    alone (p.lift see wit get set) c t seen ds = alone p c (t.narrow wit get) seen ds :=
  same_aloneFrom wit get set hsg c p.moves t seen ds hm

/-! ## 2 At the masked sumcheck's part -/

/-- **`play` on the steps of the lifted part: of the two premises on the lift, from `set x (get x) =
x` alone** (h2, hr and hl are the three other premises of PlaysSum.lean's head): the rounds are
`sumOut` at the narrowed state, each without a table; the wide state behind has heard the challenges
and nothing else changes; the columns opened stay as they were. -/
theorem plays_lift_same (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hsg : ∀ x, set x (get x) = x) (name endName : String) (J : SumJob W' Y)
    (c : SumCoins name endName J) (h2 : ∀ v ∈ J.shape.vs, 2 ≤ v.d) (nm : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (hr : StatedBy (scalarsOf J.shape) rs)
    (v : Option V) (ds : List Fmt.Drawn) (hl : ds.length = (sumGs name endName J).length)
    (back : List Fmt.RoundView) (m : Mid W X) :
    play (((sumPart (V := V') name endName J).lift see wit get set).steps nm a rs v c) ds back m =
      .ok ((sumOut J c (m.st.narrow wit get) m.shown ds).map (saidPlayed nm a),
        ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
          m.seen ++ sumOut J c (m.st.narrow wit get) m.shown ds, m.opened⟩) := by
  have hf : fitsFrom (C := SumCoins name endName J) c rs
      ((sumPart (V := V') name endName J).moves.map (Move.lift wit get set)) m.st m.shown ds =
      true :=
    (same_fitsFrom wit get set hsg c rs _ m.st m.shown ds (hand_sumPart name endName J)).trans
      (fits_sumPart name endName J c h2 rs hr (m.st.narrow wit get) m.shown ds hl)
  have hp : playedFrom (C := SumCoins name endName J) nm a c
      ((sumPart (V := V') name endName J).moves.map (Move.lift wit get set)) m.st m.shown ds =
      some ((sumOut J c (m.st.narrow wit get) m.shown ds).map (saidPlayed nm a)) :=
    (same_playedFrom wit get set hsg nm a c _ m.st m.shown ds (hand_sumPart name endName J)).trans
      (playedFrom_sumPart name endName J c nm a (m.st.narrow wit get) m.shown ds hl)
  have hst : stateFrom (C := SumCoins name endName J)
      ((sumPart (V := V') name endName J).moves.map (Move.lift wit get set)) m.st ds =
      ⟨m.st.input, m.st.heard ++ ds, m.st.own⟩ :=
    lift_stateFrom_same wit get set hsg _ m.st ds (hand_sumPart name endName J)
      ((moves_length name endName J).trans hl.symm)
  have h := play_steps_whole ((sumPart (V := V') name endName J).lift see wit get set)
    (fun _ _ => rfl) (fun _ _ _ => rfl) nm a rs v c ds back m _ hf hp
  rw [roundsOf_said] at h
  exact h.trans (by rw [← hst]; rfl)

/-- The two functions of the frame's lift `seat` (Honest/FrameToy.lean), written out anew: get x :=
x % 1000, set x y := x / 1000 * 1000 + y: what is read is laid back. A fact on numbers: the tie to
`seat` is by reading. -/
theorem seatLens_same (x : Nat) : x / 1000 * 1000 + x % 1000 = x := Nat.div_add_mod' x 1000

/-- They do not read back all that is laid. -/
theorem seatLens_not : ¬ ∀ x y : Nat, (x / 1000 * 1000 + y) % 1000 = y :=
  fun h => absurd (h 0 1000) (by decide)

/-- An instance: the part at a job whose state is a number, lifted by these two functions; h2, hr
and hl as at `plays_lift_same`. -/
theorem plays_lift_seat (see : V → V') (wit : W → W') (name endName : String) (J : SumJob W' Nat)
    (c : SumCoins name endName J) (h2 : ∀ v ∈ J.shape.vs, 2 ≤ v.d) (nm : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (hr : StatedBy (scalarsOf J.shape) rs)
    (v : Option V) (ds : List Fmt.Drawn) (hl : ds.length = (sumGs name endName J).length)
    (back : List Fmt.RoundView) (m : Mid W Nat) :
    play (((sumPart (V := V') name endName J).lift see wit (fun x => x % 1000)
        fun x y => x / 1000 * 1000 + y).steps nm a rs v c) ds back m =
      .ok ((sumOut J c (m.st.narrow wit fun x => x % 1000) m.shown ds).map (saidPlayed nm a),
        ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
          m.seen ++ sumOut J c (m.st.narrow wit fun x => x % 1000) m.shown ds, m.opened⟩) :=
  plays_lift_same see wit (fun x => x % 1000) (fun x y => x / 1000 * 1000 + y) seatLens_same name
    endName J c h2 nm a rs hr v ds hl back m

/-- The lifted part has the part's number of moves. -/
theorem lift_moves_length (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (name endName : String) (J : SumJob W' Y) :
    ((sumPart (V := V') name endName J).lift see wit get set).moves.length =
      (sumGs name endName J).length := by
  show ((sumPart (V := V') name endName J).moves.map (Move.lift wit get set)).length = _
  rw [List.length_map, moves_length]

/-- The same, as a number of the shape. -/
theorem lift_moves_count (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (name endName : String) (J : SumJob W' Y) :
    ((sumPart (V := V') name endName J).lift see wit get set).moves.length =
      J.shape.vs.length + (match J.shape.ends with
        | none => 1
        | some _ => 3) :=
  (lift_moves_length see wit get set name endName J).trans (sumGs_count name endName J)

/-! ## 3 What a caller does next -/

/-- **Declared rounds that read no stored table and open no tree read nothing.** -/
theorem readsOf_none (chain firstTree : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table)) :
    ∀ (rs : List Fmt.DeclaredRound) (ds : List Fmt.Drawn),
      (∀ r ∈ rs, r.stored = [] ∧ r.opens = []) →
      readsOf chain firstTree stored tree rs ds = []
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | r :: rs, d :: ds, h => by
    obtain ⟨h1, h2⟩ := h r List.mem_cons_self
    unfold readsOf
    rw [h1, h2, readsOf_none chain firstTree stored tree rs ds
      fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

/-- So the frame's `fillCols` returns no column there. -/
theorem fillCols_none (chain firstTree : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table))
    (rs : List Fmt.DeclaredRound) (ds : List Fmt.Drawn) (h : ∀ r ∈ rs, r.stored = [] ∧ r.opens = [])
    (back : List VerifiableInference.Desc.OpenedColumn) :
    fillCols (readsOf chain firstTree stored tree rs ds) back = .ok [] := by
  rw [readsOf_none chain firstTree stored tree rs ds h]
  rfl

/-- **Rounds whose list of tables (`tablesOf`) is empty leave the tables at hand as they were**,
where these hold no own tree from number `sent` on. A round with a root whose table no prover's side
sent has `none` in that list: it is not of these. -/
theorem add_none (En : Env) (ps : List Played) (ht : tablesOf ps = [])
    (hE : ∀ n, En.sent ≤ n → En.tree (.own n) = none) : En.add ps = En := by
  have h1 : (En.add ps).tree = En.tree := by
    funext s
    cases s with
    | own n =>
      show (if n < En.sent then En.tree (.own n) else ((tablesOf ps)[n - En.sent]?).bind id) = _
      by_cases h : n < En.sent
      · rw [if_pos h]
      · rw [if_neg h, ht, hE n (Nat.le_of_not_lt h)]
        rfl
    | taken ch k => rfl
  have h2 : (En.add ps).sent = En.sent := by
    show En.sent + (tablesOf ps).length = En.sent
    rw [ht]
    rfl
  calc En.add ps = ⟨(En.add ps).stored, (En.add ps).tree, (En.add ps).sent⟩ := rfl
    _ = ⟨En.stored, En.tree, En.sent⟩ := by rw [h1, h2]; rfl
    _ = En := rfl

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.same_state
#print axioms ProofFile.Honest.SumLaw.same_narrow
#print axioms ProofFile.Honest.SumLaw.same_aloneFrom
#print axioms ProofFile.Honest.SumLaw.same_fitsFrom
#print axioms ProofFile.Honest.SumLaw.same_playedFrom
#print axioms ProofFile.Honest.SumLaw.alone_lift_same
#print axioms ProofFile.Honest.SumLaw.plays_lift_same
#print axioms ProofFile.Honest.SumLaw.seatLens_same
#print axioms ProofFile.Honest.SumLaw.seatLens_not
#print axioms ProofFile.Honest.SumLaw.plays_lift_seat
#print axioms ProofFile.Honest.SumLaw.lift_moves_length
#print axioms ProofFile.Honest.SumLaw.lift_moves_count
#print axioms ProofFile.Honest.SumLaw.readsOf_none
#print axioms ProofFile.Honest.SumLaw.fillCols_none
#print axioms ProofFile.Honest.SumLaw.add_none
