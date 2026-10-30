-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/Plays.lean: CONDITIONAL: the frame's `play` (Honest/Frame.lean)
on the steps of a part whose moves say scalars and whose stops never stop: THE WHOLE LIST THAT IT
RETURNS; and its cases at the two small parts that many kinds have (`quietPart`, `scalarsPart`,
Honest/ForKinds.lean). General in the parts' letters; no statement names a kind. Statements with
their proofs, and one definition with code.
Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

  `lensBy_length`   as many moves as stated lengths
  `plays_said`   **a part whose moves are `mvOf`'s (Honest/SumLaw/Said.lean)**: `play` returns the
      rounds of `outOf`, each under the step's name, place and part, WITHOUT A TABLE
      (`saidPlayed`, Honest/SumLaw/PlaysSum.lean); the state behind has heard the challenges and
      nothing else turns
  `plays_lift_said`   **the same of such a part, lifted** (`Part.lift`): the rounds are those at the
      narrowed state
  `quietPart_moves`, `outOf_quiet`, `plays_quiet`, `plays_lift_quiet`   rounds in which nothing is
      sent: each round as played holds no item and no table
  `scalarsSaid`, `scalarsPart_moves`, `scalarsSaid_length`, `plays_scalars`, `plays_lift_scalars`
      one round of scalars: each is sent as its value plus its mask entry; no table

The premises, and who is meant to show them. The declared rounds state the part's numbers of
scalars and no oracle message (`StatedBy`, Honest/SumLaw/Fits.lean): the caller, of the verifier's
text. As many challenges as rounds: the caller. On a lift: `set x (get x) = x`: the caller.

Limits. One part: a row is joined by the frame's `play_append` (Honest/Law/Play.lean). Nothing on
the lending of coins or on columns. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.ForKinds
import Johnson.Desc.ProofFile.Honest.SumLaw.LiftSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open OnBytes (E)
open VerifiableInference.Desc (Oracle)
open ProofFile.Honest.SumLaw

variable {V V' W W' X Y : Type}

/-! ## 1 A part whose moves say scalars -/

/-- As many moves as stated lengths. -/
theorem lensBy_length : ∀ (ns : List Nat) (gs : List (Seen → State W X → List E)),
    LensBy ns gs → gs.length = ns.length
  | [], [], _ => rfl
  | _ :: ns, _ :: gs, h => congrArg (· + 1) (lensBy_length ns gs h.2)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- **A part whose moves say scalars and whose stops never stop: the whole list that `play`
returns.** Conditional: on the part's form (hb, hh, hm), on the lists' lengths (hL), on what the
declared rounds state (hr) and on the number of challenges (hl). hL (`LensBy`,
Honest/SumLaw/Fits.lean) ranges over all that a move may be handed as seen (`Seen`), the opened
columns too: it asks the lengths at every value of these, `none` among them. -/
theorem plays_said (p : Part V W X) (hb : ∀ f o, p.bad f o = none)
    (hh : ∀ w f o, p.hid w f o = none)
    (gs : List (p.Coins → Seen → State W X → List E)) (hm : p.moves = gs.map mvOf)
    (ns : List Nat) (c : p.Coins) (hL : LensBy ns (gs.map (· c))) (nm : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (hr : StatedBy ns rs) (v : Option V)
    (ds : List Fmt.Drawn) (hl : ds.length = ns.length) (back : List Fmt.RoundView) (m : Mid W X) :
    play (p.steps nm a rs v c) ds back m =
      .ok ((outOf (gs.map (· c)) m.st m.shown ds).map (saidPlayed nm a),
        ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
          m.seen ++ outOf (gs.map (· c)) m.st m.shown ds, m.opened⟩) := by
  have hlen : gs.length = ds.length := by
    have := lensBy_length ns _ hL
    rw [List.length_map] at this
    rw [this, hl]
  have hf : fitsFrom c rs p.moves m.st m.shown ds = true := by
    rw [hm]
    exact fitsFrom_mvOf c ns rs gs _ _ ds hr hL hl
  have hp : playedFrom nm a c p.moves m.st m.shown ds =
      some ((outOf (gs.map (· c)) m.st m.shown ds).map (saidPlayed nm a)) := by
    rw [hm]
    exact playedFrom_mvOf nm a c gs _ _ ds hlen
  have hst : stateFrom p.moves m.st ds = ⟨m.st.input, m.st.heard ++ ds, m.st.own⟩ := by
    rw [hm]
    exact stateFrom_mvOf gs _ ds hlen
  have h := play_steps_whole p hb hh nm a rs v c ds back m _ hf hp
  rw [roundsOf_said, hst] at h
  exact h

/-- **The same of such a part, lifted**: the rounds are those at the narrowed state; the wide state
behind has heard the challenges and nothing else turns. Conditional: as `plays_said`, hL at every
value of the opened columns too, and on the lift: what is read is laid back (hsg). -/
theorem plays_lift_said (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hsg : ∀ x, set x (get x) = x) (p : Part V' W' Y) (hb : ∀ f o, p.bad f o = none)
    (hh : ∀ w f o, p.hid w f o = none)
    (gs : List (p.Coins → Seen → State W' Y → List E)) (hm : p.moves = gs.map mvOf)
    (ns : List Nat) (c : p.Coins) (hL : LensBy ns (gs.map (· c))) (nm : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (hr : StatedBy ns rs) (v : Option V)
    (ds : List Fmt.Drawn) (hl : ds.length = ns.length) (back : List Fmt.RoundView) (m : Mid W X) :
    play ((p.lift see wit get set).steps nm a rs v c) ds back m =
      .ok ((outOf (gs.map (· c)) (m.st.narrow wit get) m.shown ds).map (saidPlayed nm a),
        ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
          m.seen ++ outOf (gs.map (· c)) (m.st.narrow wit get) m.shown ds, m.opened⟩) := by
  have hlen : gs.length = ds.length := by
    have := lensBy_length ns _ hL
    rw [List.length_map] at this
    rw [this, hl]
  have hand : ∀ mv ∈ p.moves, ∀ s, mv.hand s = s.own := by
    rw [hm]
    intro mv hmv s
    obtain ⟨g, _, rfl⟩ := List.mem_map.1 hmv
    rfl
  have hf : fitsFrom (C := p.Coins) c rs (p.moves.map (Move.lift wit get set)) m.st m.shown ds =
      true :=
    (same_fitsFrom wit get set hsg c rs _ m.st m.shown ds hand).trans (by
      rw [hm]
      exact fitsFrom_mvOf c ns rs gs _ _ ds hr hL hl)
  have hp : playedFrom (C := p.Coins) nm a c (p.moves.map (Move.lift wit get set)) m.st m.shown ds =
      some ((outOf (gs.map (· c)) (m.st.narrow wit get) m.shown ds).map (saidPlayed nm a)) :=
    (same_playedFrom wit get set hsg nm a c _ m.st m.shown ds hand).trans (by
      rw [hm]
      exact playedFrom_mvOf nm a c gs _ _ ds hlen)
  have hst : stateFrom (C := p.Coins) (p.moves.map (Move.lift wit get set)) m.st ds =
      ⟨m.st.input, m.st.heard ++ ds, m.st.own⟩ :=
    lift_stateFrom_same wit get set hsg _ m.st ds hand (by rw [hm, List.length_map, hlen])
  have h := play_steps_whole (p.lift see wit get set) hb (fun w f o => hh (see w) f o) nm a rs v c
    ds back m _ hf hp
  rw [roundsOf_said] at h
  exact h.trans (by rw [← hst]; rfl)

/-! ## 2 Rounds in which nothing is sent -/

/-- The quiet part's moves say no scalar. -/
theorem quietPart_moves (n : Nat) :
    (quietPart n : Part V W X).moves = (List.replicate n fun _ _ _ => []).map mvOf := by
  rw [List.map_replicate]
  rfl

theorem lensBy_quiet : ∀ n : Nat, LensBy (W := W) (X := X) (List.replicate n 0)
    (List.replicate n fun _ _ => [])
  | 0 => trivial
  | n + 1 => ⟨fun _ _ => rfl, lensBy_quiet n⟩

/-- What such moves show: the challenges, each beside no item. -/
theorem outOf_quiet : ∀ (n : Nat) (t : State W X) (seen : Seen) (ds : List Fmt.Drawn),
    ds.length = n →
    outOf (List.replicate n fun _ _ => []) t seen ds = ds.map fun d => (⟨[], d⟩ : Fmt.RoundView)
  | 0, _, _, [], _ => rfl
  | n + 1, t, seen, d :: ds, h =>
    congrArg ((⟨[], d⟩ : Fmt.RoundView) :: ·)
      (outOf_quiet n (t.hears d) (seen.plus [rvSaid [] d]) ds (Nat.succ.inj h))
  | 0, _, _, _ :: _, h => by cases h
  | _ + 1, _, _, [], h => by cases h

/-- **Rounds in which nothing is sent: the whole list that `play` returns.** Conditional: the
declared rounds state no scalar and no oracle message (hr); as many challenges as rounds (hl). -/
theorem plays_quiet (n : Nat) (c : (quietPart n : Part V W X).Coins) (nm : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (hr : StatedBy (List.replicate n 0) rs)
    (v : Option V) (ds : List Fmt.Drawn) (hl : ds.length = n) (back : List Fmt.RoundView) (m : Mid W X) :
    play ((quietPart n : Part V W X).steps nm a rs v c) ds back m =
      .ok (ds.map fun d => saidPlayed nm a ⟨[], d⟩,
        ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
          m.seen ++ ds.map fun d => ⟨[], d⟩, m.opened⟩) := by
  have h := plays_said (quietPart n : Part V W X) (fun _ _ => rfl) (fun _ _ _ => rfl) _
    (quietPart_moves n) (List.replicate n 0) c
    (by rw [List.map_replicate]; exact lensBy_quiet n) nm a rs hr v ds
    (by rw [hl, List.length_replicate]) back m
  rw [List.map_replicate, outOf_quiet n _ _ ds hl, List.map_map] at h
  exact h

/-- **The same of the quiet part, lifted.** Conditional: as `plays_quiet`, and hsg. -/
theorem plays_lift_quiet (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hsg : ∀ x, set x (get x) = x) (n : Nat) (c : (quietPart n : Part V' W' Y).Coins)
    (nm : String) (a : Addr) (rs : List (Fmt.DeclaredRound × List Oracle))
    (hr : StatedBy (List.replicate n 0) rs) (v : Option V) (ds : List Fmt.Drawn)
    (hl : ds.length = n) (back : List Fmt.RoundView) (m : Mid W X) :
    play (((quietPart n : Part V' W' Y).lift see wit get set).steps nm a rs v c) ds back m =
      .ok (ds.map fun d => saidPlayed nm a ⟨[], d⟩,
        ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
          m.seen ++ ds.map fun d => ⟨[], d⟩, m.opened⟩) := by
  have h := plays_lift_said see wit get set hsg (quietPart n : Part V' W' Y) (fun _ _ => rfl)
    (fun _ _ _ => rfl) _ (quietPart_moves n) (List.replicate n 0) c
    (by rw [List.map_replicate]; exact lensBy_quiet n) nm a rs hr v ds
    (by rw [hl, List.length_replicate]) back m
  rw [List.map_replicate, outOf_quiet n _ _ ds hl, List.map_map] at h
  exact h

/-! ## 3 One round of scalars, each under a mask entry -/

/-- What the round says: each value, of the input and of what stands in front, plus its mask entry.
u: the stretch of coins that the part spends. -/
def scalarsSaid (n : Nat) (vals : W → Front X → List E) (u : Cs ⟨0, n⟩) (seen : Seen)
    (t : State W X) : List E :=
  addL (padTo n (vals t.input ⟨t.heard, t.own, seen⟩)) (coinsE u)

/-- The part's one move says that. -/
theorem scalarsPart_moves (name : String) (n : Nat) (vals : W → Front X → List E) :
    (scalarsPart name n vals : Part V W X).moves =
      [fun c seen t => scalarsSaid n vals c.2.1.1 seen t].map mvOf := rfl

/-- It says n scalars. -/
theorem scalarsSaid_length (n : Nat) (vals : W → Front X → List E) (u : Cs ⟨0, n⟩)
    (seen : Seen) (t : State W X) : (scalarsSaid n vals u seen t).length = n := by
  unfold scalarsSaid coinsE
  rw [addL_length, padTo_length, List.length_ofFn, Nat.max_self]

/-- **One round of scalars: the whole list that `play` returns.** Conditional: the declared round
states n scalars and no oracle message (hr). -/
theorem plays_scalars (name : String) (n : Nat) (vals : W → Front X → List E)
    (c : (scalarsPart name n vals : Part V W X).Coins) (nm : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (hr : StatedBy [n] rs) (v : Option V)
    (d : Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid W X) :
    play ((scalarsPart name n vals : Part V W X).steps nm a rs v c) [d] back m =
      .ok ([saidPlayed nm a (rvSaid (scalarsSaid n vals c.2.1.1 m.shown m.st) d)],
        ⟨⟨m.st.input, m.st.heard ++ [d], m.st.own⟩, m.loc ++ [d],
          m.seen ++ [rvSaid (scalarsSaid n vals c.2.1.1 m.shown m.st) d], m.opened⟩) :=
  plays_said (scalarsPart name n vals : Part V W X) (fun _ _ => rfl) (fun _ _ _ => rfl) _
    (scalarsPart_moves name n vals) [n] c
    ⟨fun s t => scalarsSaid_length n vals c.2.1.1 s t, trivial⟩ nm a rs hr v [d] rfl back m

/-- **The same of that part, lifted**: the values are read at the narrowed state. Conditional: as
`plays_scalars`, and hsg. -/
theorem plays_lift_scalars (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hsg : ∀ x, set x (get x) = x) (name : String) (n : Nat) (vals : W' → Front Y → List E)
    (c : (scalarsPart name n vals : Part V' W' Y).Coins) (nm : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (hr : StatedBy [n] rs) (v : Option V)
    (d : Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid W X) :
    play (((scalarsPart name n vals : Part V' W' Y).lift see wit get set).steps nm a rs v c) [d]
        back m =
      .ok ([saidPlayed nm a (rvSaid (scalarsSaid n vals c.2.1.1 m.shown (m.st.narrow wit get)) d)],
        ⟨⟨m.st.input, m.st.heard ++ [d], m.st.own⟩, m.loc ++ [d],
          m.seen ++
              [rvSaid (scalarsSaid n vals c.2.1.1 m.shown (m.st.narrow wit get)) d], m.opened⟩) :=
  plays_lift_said see wit get set hsg (scalarsPart name n vals : Part V' W' Y) (fun _ _ => rfl)
    (fun _ _ _ => rfl) _ (scalarsPart_moves name n vals) [n] c
    ⟨fun s t => scalarsSaid_length n vals c.2.1.1 s t, trivial⟩ nm a rs hr v [d] rfl back m

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.lensBy_length
#print axioms ProofFile.Honest.Small.plays_said
#print axioms ProofFile.Honest.Small.plays_lift_said
#print axioms ProofFile.Honest.Small.quietPart_moves
#print axioms ProofFile.Honest.Small.lensBy_quiet
#print axioms ProofFile.Honest.Small.outOf_quiet
#print axioms ProofFile.Honest.Small.plays_quiet
#print axioms ProofFile.Honest.Small.plays_lift_quiet
#print axioms ProofFile.Honest.Small.scalarsPart_moves
#print axioms ProofFile.Honest.Small.scalarsSaid_length
#print axioms ProofFile.Honest.Small.plays_scalars
#print axioms ProofFile.Honest.Small.plays_lift_scalars
