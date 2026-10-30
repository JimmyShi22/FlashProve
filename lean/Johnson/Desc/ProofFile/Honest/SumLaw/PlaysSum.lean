-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/PlaysSum.lean: THE FRAME's `play` ON THE MASKED SUMCHECK's
PART: THE WHOLE LIST THAT IT RETURNS, AT THE PART ITSELF AND AT THE PART LIFTED, which is the form
in which a kind's row holds it (`Part.lift`, Honest/Frame.lean), under the premises told below.
Definitions with code, and statements with their proofs.
Main names:
  `saidPlayed name a r`: a round as played in which scalars were said: the round's items and
    challenge, under the step's name, place and part; a half made it; NO TABLE.
  `playedFrom_mvOf`: moves that say scalars yield such rounds. `roundsOf_said`, `tablesOf_said`:
    what a view shows of them; THEY HOLD NO TABLE (the frame's `tablesOf` is empty).
  `plays_sumPart_whole`: **`play` on the part's steps returns `sumOut`'s rounds, so laid.**
  `plays_lift_sumPart`: **the same at the lifted part**: the rounds are `sumOut` at the narrowed
    state; the wide state behind has heard the challenges and nothing else turns.
  `plays_unit_sumPart`: an instance: a job without a state of its own, lifted by get := fun _ => (),
    set := fun x _ => x (so a toy file of the frame's, which is not part of this library, lifts a
    part), meets both premises on the lift.

The premises. Every variable of the shape has at least two coefficients (`shape_two`, Fits.lean).
The declared rounds state the call's scalars (`StatedBy`; `statedBy_like`). As many challenges as
moves. On the lift: `get (set x y) = y` and `set x (get x) = x` (Lift.lean); from the second alone:
`plays_lift_same` (LiftSame.lean).

Limits. One part: a row of parts is joined by the frame's `play_append` (Honest/Law/Play.lean), with
`steps_length_fits` (PlaysWhole.lean). Nothing on coins' lending; on columns nothing but that the
field `opened` is left as it was; nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Fits
import Johnson.Desc.ProofFile.Honest.SumLaw.Lift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open OnBytes (E)
open VerifiableInference.Desc (Oracle)
open VerifiableInference.Desc.Part.MaskedSum

variable {V V' W W' X Y : Type}

/-- A round as played in which scalars were said: no table. -/
def saidPlayed (name : String) (a : Addr) (r : Fmt.RoundView) : Played :=
  ⟨name, a.place, a.part, true, r.vals, [], r.drawn⟩

/-- Moves that say scalars yield such rounds. -/
theorem playedFrom_mvOf {C : Type} (name : String) (a : Addr) (c : C) :
    ∀ (gs : List (C → Seen → State W X → List E)) (t : State W X) (seen : Seen)
      (ds : List Fmt.Drawn), gs.length = ds.length →
      playedFrom name a c (gs.map mvOf) t seen ds =
        some ((outOf (gs.map (· c)) t seen ds).map (saidPlayed name a))
  | [], _, _, [], _ => rfl
  | g :: gs, t, seen, d :: ds, h => by
    show (playedFrom name a c (gs.map mvOf) (t.hears d) (seen.plus [rvSaid (g c seen t) d]) ds).map
      (saidPlayed name a (rvSaid (g c seen t) d) :: ·) = _
    rw [playedFrom_mvOf name a c gs _ _ ds (by simp only [List.length_cons] at h; omega)]
    rfl
  | [], _, _, _ :: _, h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ :: _, _, _, [], h => by simp only [List.length_cons, List.length_nil] at h; omega

/-- What a view shows of such rounds. -/
theorem roundsOf_said (name : String) (a : Addr) : ∀ l : List Fmt.RoundView,
    roundsOf (l.map (saidPlayed name a)) = l
  | [] => rfl
  | r :: l => congrArg (r :: ·) (roundsOf_said name a l)

/-- **Such rounds hold no table.** -/
theorem tablesOf_said (name : String) (a : Addr) : ∀ l : List Fmt.RoundView,
    tablesOf (l.map (saidPlayed name a)) = []
  | [] => rfl
  | _ :: l => tablesOf_said name a l

/-- The part's rounds as played. -/
theorem playedFrom_sumPart (name endName : String) (J : SumJob W X) (c : SumCoins name endName J)
    (nm : String) (a : Addr) (t : State W X) (seen : Seen) (ds : List Fmt.Drawn)
    (hl : ds.length = (sumGs name endName J).length) :
    playedFrom (C := SumCoins name endName J) nm a c (sumPart (V := V) name endName J).moves t seen
        ds = some ((sumOut J c t seen ds).map (saidPlayed nm a)) := by
  rw [sumPart_moves, playedFrom_mvOf nm a c _ t seen ds hl.symm,
    outOf_sumGs name endName J c t seen ds hl]

/-- **`play` on the part's steps returns `sumOut`'s rounds, each without a table.** -/
theorem plays_sumPart_whole (name endName : String) (J : SumJob W X)
    (c : SumCoins name endName J) (h2 : ∀ v ∈ J.shape.vs, 2 ≤ v.d) (nm : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (hr : StatedBy (scalarsOf J.shape) rs) (v : Option V)
    (ds : List Fmt.Drawn) (hl : ds.length = (sumGs name endName J).length) (back : List Fmt.RoundView)
    (m : Mid W X) :
    play ((sumPart (V := V) name endName J).steps nm a rs v c) ds back m =
      .ok ((sumOut J c m.st m.shown ds).map (saidPlayed nm a),
        ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
          m.seen ++ sumOut J c m.st m.shown ds, m.opened⟩) := by
  have h := play_steps_whole (sumPart (V := V) name endName J) (bad_sumPart name endName J)
    (hid_sumPart name endName J) nm a rs v c ds back m _
    (fits_sumPart name endName J c h2 rs hr m.st m.shown ds hl)
    (playedFrom_sumPart name endName J c nm a m.st m.shown ds hl)
  rw [state_sumPart name endName J m.st ds hl, roundsOf_said] at h
  exact h

/-- Each move of the part hands on what it was handed. -/
theorem hand_sumPart (name endName : String) (J : SumJob W X) :
    ∀ mv ∈ (sumPart (V := V) name endName J).moves, ∀ s, mv.hand s = s.own := by
  rw [sumPart_moves]
  intro mv hmv s
  obtain ⟨g, _, rfl⟩ := List.mem_map.1 hmv
  rfl

/-- **`play` on the steps of the lifted part**: the rounds are `sumOut` at the narrowed state, each
without a table; the wide state behind has heard the challenges and nothing else turns. -/
theorem plays_lift_sumPart (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hgs : ∀ x y, get (set x y) = y) (hsg : ∀ x, set x (get x) = x) (name endName : String)
    (J : SumJob W' Y) (c : SumCoins name endName J) (h2 : ∀ v ∈ J.shape.vs, 2 ≤ v.d) (nm : String)
    (a : Addr) (rs : List (Fmt.DeclaredRound × List Oracle)) (hr : StatedBy (scalarsOf J.shape) rs)
    (v : Option V) (ds : List Fmt.Drawn) (hl : ds.length = (sumGs name endName J).length)
    (back : List Fmt.RoundView) (m : Mid W X) :
    play (((sumPart (V := V') name endName J).lift see wit get set).steps nm a rs v c) ds back m =
      .ok ((sumOut J c (m.st.narrow wit get) m.shown ds).map (saidPlayed nm a),
        ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
          m.seen ++ sumOut J c (m.st.narrow wit get) m.shown ds, m.opened⟩) := by
  have hf : fitsFrom (C := SumCoins name endName J) c rs
      ((sumPart (V := V') name endName J).moves.map (Move.lift wit get set)) m.st m.shown ds =
      true :=
    (lift_fitsFrom wit get set hgs c rs _ m.st m.shown ds).trans
      (fits_sumPart name endName J c h2 rs hr (m.st.narrow wit get) m.shown ds hl)
  have hp : playedFrom (C := SumCoins name endName J) nm a c
      ((sumPart (V := V') name endName J).moves.map (Move.lift wit get set)) m.st m.shown ds =
      some ((sumOut J c (m.st.narrow wit get) m.shown ds).map (saidPlayed nm a)) :=
    (lift_playedFrom wit get set hgs nm a c _ m.st m.shown ds).trans
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

/-- An instance: a job without a state of its own, lifted by get := fun _ => (), set := fun x _ =>
x. -/
theorem plays_unit_sumPart (see : V → V') (wit : W → W') (name endName : String)
    (J : SumJob W' Unit) (c : SumCoins name endName J) (h2 : ∀ v ∈ J.shape.vs, 2 ≤ v.d)
    (nm : String) (a : Addr) (rs : List (Fmt.DeclaredRound × List Oracle))
    (hr : StatedBy (scalarsOf J.shape) rs) (v : Option V) (ds : List Fmt.Drawn)
    (hl : ds.length = (sumGs name endName J).length) (back : List Fmt.RoundView) (m : Mid W X) :
    play (((sumPart (V := V') name endName J).lift see wit (fun _ : X => ())
        (fun x _ => x)).steps nm a rs v c) ds back m =
      .ok ((sumOut J c (m.st.narrow wit fun _ => ()) m.shown ds).map (saidPlayed nm a),
        ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
          m.seen ++ sumOut J c (m.st.narrow wit fun _ => ()) m.shown ds, m.opened⟩) :=
  plays_lift_sumPart see wit (fun _ => ()) (fun x _ => x) (fun _ _ => rfl) (fun _ => rfl) name
    endName J c h2 nm a rs hr v ds hl back m

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.playedFrom_mvOf
#print axioms ProofFile.Honest.SumLaw.roundsOf_said
#print axioms ProofFile.Honest.SumLaw.tablesOf_said
#print axioms ProofFile.Honest.SumLaw.playedFrom_sumPart
#print axioms ProofFile.Honest.SumLaw.plays_sumPart_whole
#print axioms ProofFile.Honest.SumLaw.hand_sumPart
#print axioms ProofFile.Honest.SumLaw.plays_lift_sumPart
#print axioms ProofFile.Honest.SumLaw.plays_unit_sumPart
#print axioms ProofFile.Honest.SumLaw.saidPlayed
