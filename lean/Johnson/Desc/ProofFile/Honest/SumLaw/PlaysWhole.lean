-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/PlaysWhole.lean: THE FRAME's `play` ON ONE PART's ROUNDS: THE
WHOLE LIST THAT IT RETURNS, for any part whose two stops never stop, where the part's moves all
answer and each message has the shape that its round states. Plays.lean of this folder says which
rounds `play` shows; here the list of rounds as played is written out, each with its name, place,
part and TABLES: what a caller reads next (the columns, the tables at hand) is made of these.
General in the part: for any part whose two stops never stop. Definitions with code, and statements
with their proofs.
Main names:
  `playedFrom name a c mvs t seen ds`: the rounds as played, along the run of `aloneFrom`
    (Terms.lean): for each move what it says, laid as the frame's `play` lays it. Nothing if a move
    answers with an error or the challenges are not as many as the moves.
  `playedFrom_rounds`: its rounds, as a view shows them, are those of `aloneFrom`.
  `play_stepsFrom_whole`, `play_steps_whole`: **the law: `play` returns that list.**
  `steps_length`: how many steps a part lays. `fits_lengths`: where the test on shapes passes, there
    are as many declared rounds, and as many challenges, as moves. `steps_length_fits`: so the part
    lays as many steps as there are challenges (the premise of the frame's `play_append`).

Limits. That a part's moves answer or fit: premises. A part with a stop that can stop is not
reached. The premises are asked at `m.shown`; the field `opened` is left as it was. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Plays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open VerifiableInference.Desc (Oracle)

variable {V W X : Type}

/-- The rounds as played, along the run of `aloneFrom`. -/
def playedFrom {C : Type} (name : String) (a : Addr) (c : C) : List (Move C W X) → State W X →
    Seen → List Fmt.Drawn → Option (List Played)
  | [], _, _, [] => some []
  | mv :: mvs, t, seen, d :: ds =>
    match mv.say c seen t with
    | .ok x =>
      (playedFrom name a c mvs { t.hears d with own := mv.hand (t.hears d) }
        (seen.plus [⟨x.vals.map Said.got, d⟩]) ds).map
        (⟨name, a.place, a.part, true, x.vals.map Said.got, x.tables.map some, d⟩ :: ·)
    | .error _ => none
  | _, _, _, _ => none

/-- Its rounds, as a view shows them, are those of `aloneFrom`. -/
theorem playedFrom_rounds {C : Type} (name : String) (a : Addr) (c : C) :
    ∀ (mvs : List (Move C W X)) (t : State W X) (seen : Seen) (ds : List Fmt.Drawn),
      (playedFrom name a c mvs t seen ds).map roundsOf = aloneFrom c mvs t seen ds
  | [], _, _, [] => rfl
  | [], _, _, _ :: _ => rfl
  | _ :: _, _, _, [] => rfl
  | mv :: mvs, t, seen, d :: ds => by
    cases hx : mv.say c seen t with
    | error e => simp only [playedFrom, aloneFrom, hx, Option.map_none]
    | ok x =>
      simp only [playedFrom, aloneFrom, hx]
      rw [← playedFrom_rounds name a c mvs, Option.map_map, Option.map_map]
      rfl

/-- **The law, from a round's number on.** -/
theorem play_stepsFrom_whole {C : Type} (name : String) (a : Addr)
    (bad hid : List Fmt.Drawn → List Fmt.Drawn → Option String) (hb : ∀ f o, bad f o = none)
    (hh : ∀ f o, hid f o = none) (n : Nat) (c : C) :
    ∀ (rs : List (Fmt.DeclaredRound × List Oracle)) (mvs : List (Move C W X)) (i : Nat)
      (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid W X) (l : List Played),
      fitsFrom c rs mvs m.st m.shown ds = true → playedFrom name a c mvs m.st m.shown ds = some l →
      play (stepsFrom name a bad hid n c i rs mvs) ds back m =
        .ok (l, ⟨stateFrom mvs m.st ds, m.loc ++ ds, m.seen ++ roundsOf l, m.opened⟩)
  | [], [], _, [], _, m, l, _, h => by
    have e : l = [] := (Option.some.inj h).symm
    subst e
    show Except.ok ([], m) = _
    simp [stateFrom, roundsOf]
  | r :: rs, mv :: mvs, i, d :: ds, back, m, l, hf, h => by
    cases hs : mv.say c m.shown m.st with
    | error e =>
      simp only [playedFrom, hs] at h
      cases h
    | ok x =>
      simp only [fitsFrom, hs, Bool.and_eq_true] at hf
      simp only [playedFrom, hs, Option.map_eq_some_iff] at h
      obtain ⟨l', h', rfl⟩ := h
      have hl := play_stepsFrom_whole name a bad hid hb hh n c rs mvs (i + 1) ds back.tail
        ⟨{ m.st.hears d with own := mv.hand (m.st.hears d) }, m.loc ++ [d],
          m.seen ++ [(⟨x.vals.map Said.got, d⟩ : Fmt.RoundView)], m.opened⟩ l' hf.2 h'
      have hstep : stepsFrom name a bad hid n c i (r :: rs) (mv :: mvs) =
          ⟨name, a, r.1, r.2, bad, hid, i, i + 1 == n, some ⟨fun _ => mv.say c, mv.hand⟩⟩ ::
            stepsFrom name a bad hid n c (i + 1) rs mvs := rfl
      rw [hstep]
      show ((Step.tell _ back.head? m).bind fun y => _) = _
      rw [tell_ok (s := ⟨name, a, r.1, r.2, bad, hid, i, i + 1 == n,
        some ⟨fun _ => mv.say c, mv.hand⟩⟩) hb hh rfl hs hf.1]
      show ((Step.hear _ _ d m).bind fun m' => _) = _
      rw [hear_ok (s := ⟨name, a, r.1, r.2, bad, hid, i, i + 1 == n,
        some ⟨fun _ => mv.say c, mv.hand⟩⟩) hb hh rfl]
      show ((play _ ds back.tail _).map fun y => _) = _
      rw [hl]
      show Except.ok _ = Except.ok _
      simp [stateFrom, roundsOf, List.append_assoc]
  | [], [], _, _ :: _, _, _, _, hf, _ => by simp [fitsFrom] at hf
  | [], _ :: _, _, _, _, _, _, hf, _ => by simp [fitsFrom] at hf
  | _ :: _, [], _, _, _, _, _, hf, _ => by simp [fitsFrom] at hf
  | _ :: _, _ :: _, _, [], _, _, _, hf, _ => by simp [fitsFrom] at hf

/-- **The law**: `play` on one part's steps returns the rounds of `playedFrom`. -/
theorem play_steps_whole (p : Part V W X) (hb : ∀ f o, p.bad f o = none)
    (hh : ∀ w f o, p.hid w f o = none) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins) (ds : List Fmt.Drawn)
    (back : List Fmt.RoundView) (m : Mid W X) (l : List Played)
    (hf : fitsFrom c rs p.moves m.st m.shown ds = true)
    (h : playedFrom name a c p.moves m.st m.shown ds = some l) :
    play (p.steps name a rs v c) ds back m =
      .ok (l, ⟨stateFrom p.moves m.st ds, m.loc ++ ds, m.seen ++ roundsOf l, m.opened⟩) := by
  rw [steps_eq]
  refine play_stepsFrom_whole name a p.bad _ hb (fun f o => ?_) p.moves.length c rs p.moves 0 ds
    back m l hf h
  cases v with
  | none => rfl
  | some w => exact hh w f o

/-- How many steps a part lays: one for each declared round that has a move. -/
theorem steps_length (p : Part V W X) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins) :
    (p.steps name a rs v c).length = min rs.length p.moves.length := by
  unfold Part.steps
  rw [List.length_map, List.length_zipIdx, List.length_zip]

/-- Where the test on shapes passes, there are as many declared rounds, and as many challenges, as
moves. -/
theorem fits_lengths {C : Type} (c : C) : ∀ (rs : List (Fmt.DeclaredRound × List Oracle))
    (mvs : List (Move C W X)) (t : State W X) (seen : Seen) (ds : List Fmt.Drawn),
    fitsFrom c rs mvs t seen ds = true → rs.length = mvs.length ∧ ds.length = mvs.length
  | [], [], _, _, [], _ => ⟨rfl, rfl⟩
  | r :: rs, mv :: mvs, t, seen, d :: ds, h => by
    cases hs : mv.say c seen t with
    | error e => simp [fitsFrom, hs] at h
    | ok x =>
      simp only [fitsFrom, hs, Bool.and_eq_true] at h
      obtain ⟨a, b⟩ := fits_lengths c rs mvs _ _ ds h.2
      exact ⟨by rw [List.length_cons, List.length_cons, a],
        by rw [List.length_cons, List.length_cons, b]⟩
  | [], [], _, _, _ :: _, h => by simp [fitsFrom] at h
  | [], _ :: _, _, _, _, h => by simp [fitsFrom] at h
  | _ :: _, [], _, _, _, h => by simp [fitsFrom] at h
  | _ :: _, _ :: _, _, _, [], h => by simp [fitsFrom] at h

/-- Where the test on shapes passes, the part lays as many steps as there are challenges: what the
frame's `play_append` (Honest/Law/Play.lean) asks of the first of two stretches. -/
theorem steps_length_fits (p : Part V W X) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn) (h : fitsFrom c rs p.moves t seen ds = true) :
    (p.steps name a rs v c).length = ds.length := by
  obtain ⟨h1, h2⟩ := fits_lengths c rs p.moves t seen ds h
  rw [steps_length, h1, h2, Nat.min_self]

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.playedFrom_rounds
#print axioms ProofFile.Honest.SumLaw.play_stepsFrom_whole
#print axioms ProofFile.Honest.SumLaw.play_steps_whole
#print axioms ProofFile.Honest.SumLaw.steps_length
#print axioms ProofFile.Honest.SumLaw.fits_lengths
#print axioms ProofFile.Honest.SumLaw.steps_length_fits
#print axioms ProofFile.Honest.SumLaw.playedFrom
