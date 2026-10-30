-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/PlayLift.lean: a part that is seated by `Part.lift`
(Honest/Frame.lean), played alone; for every part. Theorems on the frame's functions, with two
definitions. No sub-protocol is named here.

Terms. Honest/K3/GLOSSARY.md ("part, stretch", "play", "row"). The narrowed state is `State.narrow`
(Frame.lean); "get" and "set" are two of the arguments of `Part.lift`.

What is shown.
  `aloneFrom_lift`, `alone_lift`: lifted moves, played alone, yield what the moves yield at the
    narrowed state, where "get" reads back what "set" writes.
  `endFrom_lift_keep`: where "set" writes nothing: behind lifted moves the state has heard the
    challenges, and nothing else of it has changed.
  `unlift`: a lifted row's coins as the row's: part by part the same (`Part.lift` keeps the counts).
  `aloneRow_lift`: the same for a row, where the parts hand nothing on.
  `noStops_lift`, `rowFits_lift`: a lifted row stops as little, and its messages have the same
    shapes.
  `endRow_lift_keep`: the state behind a lifted row.

Hypotheses that remain. `hgs`: (in `aloneFrom_lift`, `alone_lift`) "get" reads back what "set"
writes. `h`: (in `noStops_lift`) the row has no stops. Without a name, in front of arrows: in
`endFrom_lift_keep` and `endRow_lift_keep`: as many challenges as moves; in `rowFits_lift`:
`RowFits` of the row itself.

Imported. Honest/Frame.lean lies beneath this file.

Users. This file is imported by Honest/K3/Law/RowSeated.lean.

Limits. The row's lemmas are stated at parts that hand nothing on (their own state is Unit) and at a
"set" that writes nothing. Nothing
is said on what the rounds are worth.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.SumFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Oracle)
open ProofFile.Honest.SumLaw (alone aloneFrom)

variable {V V' W W' X Y C : Type}

theorem aloneFrom_lift (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hgs : ∀ x y, get (set x y) = y) (c : C) :
    ∀ (ms : List (Move C W' Y)) (t : State W X) (seen : Seen) (ds : List Fmt.Drawn),
      aloneFrom c (ms.map (Move.lift wit get set)) t seen ds =
        aloneFrom c ms (t.narrow wit get) seen ds
  | [], _, _, [] => by simp [aloneFrom]
  | [], _, _, _ :: _ => by simp [aloneFrom]
  | _ :: _, _, _, [] => by simp [aloneFrom]
  | mv :: ms, t, seen, d :: ds => by
    rw [List.map_cons]
    have e : (Move.lift wit get set mv).say c seen t = mv.say c seen (t.narrow wit get) := rfl
    unfold aloneFrom
    rw [e]
    cases mv.say c seen (t.narrow wit get) with
    | error e => rfl
    | ok x =>
      show (aloneFrom c (ms.map (Move.lift wit get set)) _ _ ds).map _ =
        (aloneFrom c ms _ _ ds).map _
      rw [aloneFrom_lift wit get set hgs c ms]
      simp only [Move.lift, State.narrow, State.hears, hgs]

/-- **A lifted part, played alone, yields what the part yields at the narrowed state**, where "get"
reads back what "set" writes. -/
theorem alone_lift (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hgs : ∀ x y, get (set x y) = y) (p : Part V' W' Y) (c : p.Coins) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn) :
    alone (p.lift see wit get set) c t seen ds = alone p c (t.narrow wit get) seen ds :=
  aloneFrom_lift wit get set hgs c p.moves t seen ds

/-- Where "set" writes nothing, and there are as many challenges as moves: behind lifted moves the
state has heard the challenges. -/
theorem endFrom_lift_keep (wit : W → W') (get : X → Y) :
    ∀ (ms : List (Move C W' Y)) (t : State W X) (ds : List Fmt.Drawn), ds.length = ms.length →
      endFrom (ms.map (Move.lift wit get fun x _ => x)) t ds = { t with heard := t.heard ++ ds }
  | [], t, [], _ => by simp [endFrom]
  | [], _, _ :: _, h => by simp at h
  | _ :: _, _, [], h => by simp at h
  | mv :: ms, t, d :: ds, h => by
    rw [List.map_cons]
    unfold endFrom
    rw [endFrom_lift_keep wit get ms _ ds (by simpa using h)]
    simp [State.hears, Move.lift, List.append_assoc]

/-! ## A row -/

/-- The seat of a row whose parts hand nothing on. -/
abbrev liftU (see : V → V') (wit : W → W') (p : Part V' W' Unit) : Part V W X :=
  p.lift see wit (fun _ => ()) fun x _ => x

/-- A lifted row's coins as the row's. -/
def unlift (see : V → V') (wit : W → W') :
    (ps : List (Part V' W' Unit)) → RowCoins (ps.map (liftU (X := X) see wit)) → RowCoins ps
  | [], _ => ()
  | p :: ps, c =>
    let c' : p.Coins × RowCoins (ps.map (liftU (X := X) see wit)) := c
    (c'.1, unlift see wit ps c'.2)

theorem aloneRow_lift (see : V → V') (wit : W → W') :
    ∀ (ps : List (Part V' W' Unit)) (c : RowCoins (ps.map (liftU (X := X) see wit)))
      (t : State W X) (seen : Seen) (ds : List Fmt.Drawn),
      aloneRow (ps.map (liftU (X := X) see wit)) c t seen ds =
        aloneRow ps (unlift see wit ps c) (t.narrow wit fun _ => ()) seen ds
  | [], _, _, _, [] => rfl
  | [], _, _, _, _ :: _ => rfl
  | p :: ps, c, t, seen, ds => by
    let c' : p.Coins × RowCoins (ps.map (liftU (X := X) see wit)) := c
    have hm : (liftU (X := X) see wit p).moves.length = p.moves.length := by
      simp [Part.lift]
    show (alone (liftU (X := X) see wit p) c'.1 t seen
        (ds.take (liftU (X := X) see wit p).moves.length)).bind (fun y =>
          (aloneRow (ps.map (liftU (X := X) see wit)) c'.2
            (endFrom (liftU (X := X) see wit p).moves t
              (ds.take (liftU (X := X) see wit p).moves.length)) (seen.plus y)
            (ds.drop (liftU (X := X) see wit p).moves.length)).map (y ++ ·)) =
      (alone p c'.1 (t.narrow wit fun _ => ()) seen (ds.take p.moves.length)).bind fun y =>
        (aloneRow ps (unlift see wit ps c'.2)
          (endFrom p.moves (t.narrow wit fun _ => ()) (ds.take p.moves.length)) (seen.plus y)
          (ds.drop p.moves.length)).map (y ++ ·)
    rw [hm, alone_lift see wit (fun _ => ()) (fun x _ => x) (fun _ _ => rfl) p c'.1]
    cases hal : alone p c'.1 (t.narrow wit fun _ => ()) seen (ds.take p.moves.length) with
    | none => rfl
    | some y =>
      have hlen := (aloneFrom_length c'.1 _ _ seen _ y hal).1
      show (aloneRow (ps.map (liftU (X := X) see wit)) c'.2
          (endFrom (p.moves.map (Move.lift wit (fun _ => ()) fun x _ => x)) t
            (ds.take p.moves.length)) (seen.plus y) (ds.drop p.moves.length)).map (y ++ ·) =
        (aloneRow ps (unlift see wit ps c'.2)
          (endFrom p.moves (t.narrow wit fun _ => ()) (ds.take p.moves.length)) (seen.plus y)
          (ds.drop p.moves.length)).map (y ++ ·)
      rw [endFrom_lift_keep wit (fun _ => ()) p.moves t _ hlen, endFrom_unit p.moves _ _ hlen,
        aloneRow_lift see wit ps c'.2]
      rfl

theorem noStops_lift (see : V → V') (wit : W → W') (ps : List (Part V' W' Unit))
    (h : NoStops ps) : NoStops (ps.map (liftU (X := X) see wit)) := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
  exact ⟨(h p hp).1, fun v f o => (h p hp).2 (see v) f o⟩

theorem rowFits_lift (see : V → V') (wit : W → W') :
    ∀ (ps : List (Part V' W' Unit)) (rs : List (Fmt.DeclaredRound × List Oracle))
      (c : RowCoins (ps.map (liftU (X := X) see wit))), RowFits ps rs (unlift see wit ps c) →
      RowFits (ps.map (liftU (X := X) see wit)) rs c
  | [], _, _, h => h
  | p :: ps, rs, c, h => by
    let c' : p.Coins × RowCoins (ps.map (liftU (X := X) see wit)) := c
    have h' : p.moves.length ≤ rs.length ∧
      (∀ r ∈ (rs.take p.moves.length).zip p.moves, ∀ (sn : Seen) (u : State W' Unit) (y : Sending),
        r.2.say c'.1 sn u = .ok y → y.fits r.1.1 r.1.2 = true) ∧
      RowFits ps (rs.drop p.moves.length) (unlift see wit ps c'.2) := h
    have hm : (liftU (X := X) see wit p).moves.length = p.moves.length := by
      simp [Part.lift]
    show (liftU (X := X) see wit p).moves.length ≤ rs.length ∧
      (∀ r ∈ (rs.take (liftU (X := X) see wit p).moves.length).zip
          (liftU (X := X) see wit p).moves,
        ∀ (sn : Seen) (u : State W X) (y : Sending), r.2.say c'.1 sn u = .ok y →
          y.fits r.1.1 r.1.2 = true) ∧
      RowFits (ps.map (liftU (X := X) see wit))
        (rs.drop (liftU (X := X) see wit p).moves.length) c'.2
    rw [hm]
    refine ⟨h'.1, fun r hr sn u y hy => ?_, rowFits_lift see wit ps _ c'.2 h'.2.2⟩
    have hr' : r ∈ (rs.take p.moves.length).zip
        (p.moves.map (Move.lift wit (fun _ => ()) fun x _ => x)) := hr
    rw [List.zip_map_right] at hr'
    obtain ⟨r₀, hr₀, he⟩ := List.mem_map.1 hr'
    subst he
    exact h'.2.1 r₀ hr₀ sn (u.narrow wit fun _ => ()) y hy

theorem endRow_lift_keep (see : V → V') (wit : W → W') :
    ∀ (ps : List (Part V' W' Unit)) (t : State W X) (ds : List Fmt.Drawn),
      ds.length = (ps.map (·.moves.length)).sum →
      endRow (ps.map (liftU (X := X) see wit)) t ds = { t with heard := t.heard ++ ds }
  | [], t, [], _ => by simp [endRow]
  | [], _, _ :: _, h => by simp at h
  | p :: ps, t, ds, h => by
    simp only [List.map_cons, List.sum_cons] at h
    show endRow (ps.map (liftU (X := X) see wit))
      (endFrom (p.moves.map (Move.lift wit (fun _ => ()) fun x _ => x)) t
        (ds.take (p.moves.map (Move.lift wit (fun _ => ()) fun x _ => x)).length))
      (ds.drop (p.moves.map (Move.lift wit (fun _ => ()) fun x _ => x)).length) = _
    rw [List.length_map, endFrom_lift_keep wit (fun _ => ()) p.moves t _
      (by rw [List.length_take]; omega),
      endRow_lift_keep see wit ps _ _ (by rw [List.length_drop]; omega)]
    simp [List.append_assoc]

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.aloneFrom_lift
#print axioms ProofFile.Honest.K3.Law.alone_lift
#print axioms ProofFile.Honest.K3.Law.endFrom_lift_keep
#print axioms ProofFile.Honest.K3.Law.aloneRow_lift
#print axioms ProofFile.Honest.K3.Law.noStops_lift
#print axioms ProofFile.Honest.K3.Law.rowFits_lift
#print axioms ProofFile.Honest.K3.Law.endRow_lift_keep
