-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Keep/LiftLens.lean: a row of parts that pass something on,
seated in a chain's letters by `Part.lift` at any get and set: played alone it shows what the row
shows at the narrowed state. The counterparts of the row's lemmas of Honest/K3/Law/PlayLift.lean,
which are typed at parts that pass nothing on. Conditional on laws of get and set, named at each
theorem.
General in the parts: no sub-protocol is named. One definition that the statements need, and
theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: get reads the row's own state in what the chain's parts
pass on, set lays it there. The three laws: hgs: get (set x y) = y. hss: set (set x y) y' =
set x y'. hsg: set x (get x) = x.

What is defined.
  `unliftG`: a seated row's coins as the row's: part by part the two types are the same.

What is shown.
  `endFrom_lift_narrow`, `endRow_lift_narrow` (hgs): the state behind the seated moves, narrowed, is
    the state behind the moves.
  `endFrom_lift_own`, `endRow_lift_own` (hgs, hss, hsg): behind the seated moves the chain's state
    is the one in front with the row's own state laid in it.
  `aloneRow_liftG` (hgs): **the seated row, played alone, shows what the row shows at the narrowed
    state.**
  `noStops_liftG`, `rowFits_liftG`: no part of the seated row stops, and its messages have the
    stated shapes, where that holds of the row. No law of get and set is needed.
  `lift_moves_length`, `lift_moves_sum`: a seated part has as many moves; so has the seated row,
    part by part.

Hypotheses that remain. The laws of get and set (`hgs`, `hss`, `hsg`): for whoever seats the row to
show. `h`: (in `noStops_liftG`) the row has no stops. `rowFits_liftG` has a hypothesis without a
name, in front of an arrow: `RowFits` of the row at the narrowed coins.

Imported: Honest/SumLaw/Lift.lean.

Users. Honest/K3/Law/Keep/SameRounds.lean.

Limits. Nothing on what the rounds are worth.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Lift
import Johnson.Desc.ProofFile.Honest.K3.Law.PlayLift
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Oracle)
open ProofFile.Honest.SumLaw (alone aloneFrom)

variable {V V' W W' X Y C : Type}

/-! ## 1 The state behind seated moves -/

/-- The state behind the seated moves, narrowed, is the state behind the moves. Conditional on hgs.
-/
theorem endFrom_lift_narrow (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hgs : ∀ x y, get (set x y) = y) (ms : List (Move C W' Y)) (t : State W X)
    (ds : List Fmt.Drawn) :
    (endFrom (ms.map (Move.lift wit get set)) t ds).narrow wit get =
      endFrom ms (t.narrow wit get) ds := by
  rw [endFrom_eq_stateFrom, endFrom_eq_stateFrom]
  exact SumLaw.lift_stateFrom wit get set hgs ms t ds

/-- Behind the seated moves the chain's state is the one in front with the row's own state laid in
it. Conditional on hgs, hss and hsg. -/
theorem endFrom_lift_own (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hgs : ∀ x y, get (set x y) = y) (hss : ∀ x y y', set (set x y) y' = set x y')
    (hsg : ∀ x, set x (get x) = x) :
    ∀ (ms : List (Move C W' Y)) (t : State W X) (ds : List Fmt.Drawn),
      (endFrom (ms.map (Move.lift wit get set)) t ds).own =
        set t.own (endFrom ms (t.narrow wit get) ds).own
  | [], t, _ => (hsg t.own).symm
  | _ :: _, t, [] => (hsg t.own).symm
  | mv :: ms, t, d :: ds => by
    show (endFrom (ms.map (Move.lift wit get set))
        ⟨t.input, t.heard ++ [d], set t.own (mv.hand ((t.hears d).narrow wit get))⟩ ds).own =
      set t.own (endFrom ms
        ⟨wit t.input, t.heard ++ [d], mv.hand ((t.hears d).narrow wit get)⟩ ds).own
    rw [endFrom_lift_own wit get set hgs hss hsg ms _ ds, hss]
    show set t.own (endFrom ms ⟨wit t.input, t.heard ++ [d],
      get (set t.own (mv.hand ((t.hears d).narrow wit get)))⟩ ds).own = _
    rw [hgs]

/-! ## 2 A row -/

/-- A seated row's coins as the row's. -/
def unliftG (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X) :
    (ps : List (Part V' W' Y)) → RowCoins (ps.map (Part.lift see wit get set)) → RowCoins ps
  | [], _ => ()
  | p :: ps, c =>
    let c' : p.Coins × RowCoins (ps.map (Part.lift see wit get set)) := c
    (c'.1, unliftG see wit get set ps c'.2)

theorem lift_moves_length (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (p : Part V' W' Y) : (p.lift see wit get set).moves.length = p.moves.length := by
  simp [Part.lift]

/-- The seated row has as many moves, part by part. -/
theorem lift_moves_sum (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (ps : List (Part V' W' Y)) :
    ((ps.map (Part.lift see wit get set)).map (·.moves.length)) = ps.map (·.moves.length) := by
  rw [List.map_map]
  exact List.map_congr_left fun p _ => lift_moves_length see wit get set p

/-- The state behind the seated row, narrowed, is the state behind the row. Conditional on hgs. -/
theorem endRow_lift_narrow (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hgs : ∀ x y, get (set x y) = y) :
    ∀ (ps : List (Part V' W' Y)) (t : State W X) (ds : List Fmt.Drawn),
      (endRow (ps.map (Part.lift see wit get set)) t ds).narrow wit get =
        endRow ps (t.narrow wit get) ds
  | [], _, _ => rfl
  | p :: ps, t, ds => by
    show (endRow (ps.map (Part.lift see wit get set))
        (endFrom (p.moves.map (Move.lift wit get set)) t
          (ds.take (p.lift see wit get set).moves.length))
        (ds.drop (p.lift see wit get set).moves.length)).narrow wit get =
      endRow ps (endFrom p.moves (t.narrow wit get) (ds.take p.moves.length))
        (ds.drop p.moves.length)
    rw [lift_moves_length, endRow_lift_narrow see wit get set hgs ps,
      endFrom_lift_narrow wit get set hgs]

/-- Behind the seated row the chain's state is the one in front with the row's own state laid in it.
Conditional on hgs, hss and hsg. -/
theorem endRow_lift_own (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hgs : ∀ x y, get (set x y) = y) (hss : ∀ x y y', set (set x y) y' = set x y')
    (hsg : ∀ x, set x (get x) = x) :
    ∀ (ps : List (Part V' W' Y)) (t : State W X) (ds : List Fmt.Drawn),
      (endRow (ps.map (Part.lift see wit get set)) t ds).own =
        set t.own (endRow ps (t.narrow wit get) ds).own
  | [], t, _ => (hsg t.own).symm
  | p :: ps, t, ds => by
    show (endRow (ps.map (Part.lift see wit get set))
        (endFrom (p.moves.map (Move.lift wit get set)) t
          (ds.take (p.lift see wit get set).moves.length))
        (ds.drop (p.lift see wit get set).moves.length)).own =
      set t.own (endRow ps (endFrom p.moves (t.narrow wit get) (ds.take p.moves.length))
        (ds.drop p.moves.length)).own
    rw [lift_moves_length, endRow_lift_own see wit get set hgs hss hsg ps,
      endFrom_lift_narrow wit get set hgs, endFrom_lift_own wit get set hgs hss hsg, hss]

/-- **The seated row, played alone, shows what the row shows at the narrowed state.** Conditional on
hgs. -/
theorem aloneRow_liftG (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hgs : ∀ x y, get (set x y) = y) :
    ∀ (ps : List (Part V' W' Y)) (c : RowCoins (ps.map (Part.lift see wit get set)))
      (t : State W X) (seen : Seen) (ds : List Fmt.Drawn),
      aloneRow (ps.map (Part.lift see wit get set)) c t seen ds =
        aloneRow ps (unliftG see wit get set ps c) (t.narrow wit get) seen ds
  | [], _, _, _, [] => rfl
  | [], _, _, _, _ :: _ => rfl
  | p :: ps, c, t, seen, ds => by
    let c' : p.Coins × RowCoins (ps.map (Part.lift see wit get set)) := c
    show (alone (p.lift see wit get set) c'.1 t seen
        (ds.take (p.lift see wit get set).moves.length)).bind (fun y =>
          (aloneRow (ps.map (Part.lift see wit get set)) c'.2
            (endFrom (p.moves.map (Move.lift wit get set)) t
              (ds.take (p.lift see wit get set).moves.length)) (seen.plus y)
            (ds.drop (p.lift see wit get set).moves.length)).map (y ++ ·)) =
      (alone p c'.1 (t.narrow wit get) seen (ds.take p.moves.length)).bind fun y =>
        (aloneRow ps (unliftG see wit get set ps c'.2)
          (endFrom p.moves (t.narrow wit get) (ds.take p.moves.length)) (seen.plus y)
          (ds.drop p.moves.length)).map (y ++ ·)
    rw [lift_moves_length, alone_lift see wit get set hgs p c'.1]
    refine congrArg _ (funext fun y => ?_)
    rw [aloneRow_liftG see wit get set hgs ps c'.2, endFrom_lift_narrow wit get set hgs]

theorem noStops_liftG (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (ps : List (Part V' W' Y)) (h : NoStops ps) :
    NoStops (ps.map (Part.lift see wit get set)) := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
  exact ⟨(h p hp).1, fun v f o => (h p hp).2 (see v) f o⟩

theorem rowFits_liftG (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X) :
    ∀ (ps : List (Part V' W' Y)) (rs : List (Fmt.DeclaredRound × List Oracle))
      (c : RowCoins (ps.map (Part.lift see wit get set))),
      RowFits ps rs (unliftG see wit get set ps c) →
      RowFits (ps.map (Part.lift see wit get set)) rs c
  | [], _, _, h => h
  | p :: ps, rs, c, h => by
    let c' : p.Coins × RowCoins (ps.map (Part.lift see wit get set)) := c
    have h' : p.moves.length ≤ rs.length ∧
      (∀ r ∈ (rs.take p.moves.length).zip p.moves, ∀ (sn : Seen) (u : State W' Y) (y : Sending),
        r.2.say c'.1 sn u = .ok y → y.fits r.1.1 r.1.2 = true) ∧
      RowFits ps (rs.drop p.moves.length) (unliftG see wit get set ps c'.2) := h
    show (p.lift see wit get set).moves.length ≤ rs.length ∧
      (∀ r ∈ (rs.take (p.lift see wit get set).moves.length).zip (p.lift see wit get set).moves,
        ∀ (sn : Seen) (u : State W X) (y : Sending), r.2.say c'.1 sn u = .ok y →
          y.fits r.1.1 r.1.2 = true) ∧
      RowFits (ps.map (Part.lift see wit get set))
        (rs.drop (p.lift see wit get set).moves.length) c'.2
    rw [lift_moves_length]
    refine ⟨h'.1, fun r hr sn u y hy => ?_, rowFits_liftG see wit get set ps _ c'.2 h'.2.2⟩
    have hr' : r ∈ (rs.take p.moves.length).zip (p.moves.map (Move.lift wit get set)) := hr
    rw [List.zip_map_right] at hr'
    obtain ⟨r₀, hr₀, he⟩ := List.mem_map.1 hr'
    subst he
    exact h'.2.1 r₀ hr₀ sn (u.narrow wit get) y hy

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.endFrom_lift_narrow
#print axioms ProofFile.Honest.K3.Law.endFrom_lift_own
#print axioms ProofFile.Honest.K3.Law.lift_moves_length
#print axioms ProofFile.Honest.K3.Law.lift_moves_sum
#print axioms ProofFile.Honest.K3.Law.endRow_lift_narrow
#print axioms ProofFile.Honest.K3.Law.endRow_lift_own
#print axioms ProofFile.Honest.K3.Law.aloneRow_liftG
#print axioms ProofFile.Honest.K3.Law.noStops_liftG
#print axioms ProofFile.Honest.K3.Law.rowFits_liftG
