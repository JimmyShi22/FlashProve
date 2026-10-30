-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/Plays.lean: THE FRAME's `play` ON ONE PART's ROUNDS: for any
part whose two stops never stop: where the part's moves, played alone (`alone`, Terms.lean of this
folder), all answer, and each message has the shape that its round states, `play` goes through on
the part's steps, shows the same rounds, and leaves the run where the moves leave it; the premises
are asked at `m.shown`, and the field `opened` is left as it was. Definitions with code, and
statements with their proofs. No sumcheck is named: the law is general in the part.
Main names:
  `fitsFrom`: along the run of `aloneFrom`: every message has the stated shape. A test with code.
  `stateFrom`: the state behind the moves.
  `stop_none`, `tell_ok`, `hear_ok`: one round of the frame, where no stop stops.
  `stepsFrom`, `steps_eq`: a part's steps from a round's number on.
  `play_stepsFrom`, `play_steps`: **the law.**

What is not claimed. That a part's moves answer or fit: premises. OF THE LIST THAT `play` RETURNS
ONLY ITS ROUNDS ARE SAID HERE, not its tables, names or places: the whole list is in PlaysWhole.lean
of this folder. Nothing on a row of several parts (`play_append`, Honest/Law/Play.lean, joins them).
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Terms
import Johnson.Desc.ProofFile.Honest.Law.Play

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open VerifiableInference.Desc (Oracle)

variable {V W X : Type}

/-- Along the run of `aloneFrom`: every message has the shape that its round states. -/
def fitsFrom {C : Type} (c : C) : List (Fmt.DeclaredRound × List Oracle) → List (Move C W X) →
    State W X → Seen → List Fmt.Drawn → Bool
  | [], [], _, _, [] => true
  | r :: rs, mv :: mvs, t, seen, d :: ds =>
    match mv.say c seen t with
    | .ok x =>
      x.fits r.1 r.2 && fitsFrom c rs mvs { t.hears d with own := mv.hand (t.hears d) }
        (seen.plus [⟨x.vals.map Said.got, d⟩]) ds
    | .error _ => false
  | _, _, _, _, _ => false

/-- The state behind the moves. -/
def stateFrom {C : Type} : List (Move C W X) → State W X → List Fmt.Drawn → State W X
  | mv :: mvs, t, d :: ds => stateFrom mvs { t.hears d with own := mv.hand (t.hears d) } ds
  | _, t, _ => t

/-- Where neither stop ever stops, a step's test of the stops passes. -/
theorem stop_none {s : Step W X} (hb : ∀ f o, s.bad f o = none) (hh : ∀ f o, s.hid f o = none)
    (l : List Fmt.Drawn) (n : Nat) : s.stop l n = none := by
  unfold Step.stop
  simp only [hb, hh]

/-- A round's message, where no stop stops, the move answers and the message fits. -/
theorem tell_ok {s : Step W X} (hb : ∀ f o, s.bad f o = none) (hh : ∀ f o, s.hid f o = none)
    {mv : Move Unit W X} (hm : s.move = some mv) {m : Mid W X} {x : Sending}
    (hs : mv.say () m.shown m.st = .ok x) (hf : x.fits s.decl s.oracles = true)
    (back : Option Fmt.RoundView) :
    s.tell back m = .ok ⟨x.vals.map Said.got, x.tables.map some, true⟩ := by
  unfold Step.tell
  simp only [stop_none hb hh, hm, hs, hf]
  rfl

/-- Behind a round's challenge, where no stop stops. -/
theorem hear_ok {s : Step W X} (hb : ∀ f o, s.bad f o = none) (hh : ∀ f o, s.hid f o = none)
    {mv : Move Unit W X} (hm : s.move = some mv) (x : Told) (d : Fmt.Drawn) (m : Mid W X) :
    s.hear x d m = .ok ⟨{ m.st.hears d with own := mv.hand (m.st.hears d) }, m.loc ++ [d],
      m.seen ++ [⟨x.vals, d⟩], m.opened⟩ := by
  unfold Step.hear
  simp only [hm, stop_none hb hh, ite_self]

/-- A part's steps, from the round number i on. n: the part's number of moves. -/
def stepsFrom {C : Type} (name : String) (a : Addr)
    (bad hid : List Fmt.Drawn → List Fmt.Drawn → Option String) (n : Nat) (c : C) (i : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (mvs : List (Move C W X)) : List (Step W X) :=
  ((rs.zip mvs).zipIdx i).map fun r =>
    ⟨name, a, r.1.1.1, r.1.1.2, bad, hid, r.2, r.2 + 1 == n,
      some ⟨fun _ => r.1.2.say c, r.1.2.hand⟩⟩

/-- A part's steps are these, from 0 on. -/
theorem steps_eq (p : Part V W X) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins) :
    p.steps name a rs v c =
      stepsFrom name a p.bad (fun f o => v.bind fun w => p.hid w f o) p.moves.length c 0 rs
        p.moves :=
  rfl

/-- **The law, from a round's number on.** -/
theorem play_stepsFrom {C : Type} (name : String) (a : Addr)
    (bad hid : List Fmt.Drawn → List Fmt.Drawn → Option String) (hb : ∀ f o, bad f o = none)
    (hh : ∀ f o, hid f o = none) (n : Nat) (c : C) :
    ∀ (rs : List (Fmt.DeclaredRound × List Oracle)) (mvs : List (Move C W X)) (i : Nat)
      (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid W X) (out : List Fmt.RoundView),
      fitsFrom c rs mvs m.st m.shown ds = true → aloneFrom c mvs m.st m.shown ds = some out →
      ∃ l, play (stepsFrom name a bad hid n c i rs mvs) ds back m =
          .ok (l, ⟨stateFrom mvs m.st ds, m.loc ++ ds, m.seen ++ out, m.opened⟩) ∧ roundsOf l = out
  | [], [], i, [], back, m, out, _, h => by
    have e : out = [] := (Option.some.inj h).symm
    subst e
    refine ⟨[], ?_, rfl⟩
    show Except.ok ([], m) = _
    simp [stateFrom]
  | r :: rs, mv :: mvs, i, d :: ds, back, m, out, hf, h => by
    cases hs : mv.say c m.shown m.st with
    | error e =>
      simp only [aloneFrom, hs] at h
      cases h
    | ok x =>
      simp only [fitsFrom, hs, Bool.and_eq_true] at hf
      simp only [aloneFrom, hs, Option.map_eq_some_iff] at h
      obtain ⟨out', h', rfl⟩ := h
      obtain ⟨l, hl, hr⟩ := play_stepsFrom name a bad hid hb hh n c rs mvs (i + 1) ds back.tail
        ⟨{ m.st.hears d with own := mv.hand (m.st.hears d) }, m.loc ++ [d],
          m.seen ++ [(⟨x.vals.map Said.got, d⟩ : Fmt.RoundView)], m.opened⟩ out' hf.2 h'
      have hstep : stepsFrom name a bad hid n c i (r :: rs) (mv :: mvs) =
          ⟨name, a, r.1, r.2, bad, hid, i, i + 1 == n, some ⟨fun _ => mv.say c, mv.hand⟩⟩ ::
            stepsFrom name a bad hid n c (i + 1) rs mvs := rfl
      refine ⟨⟨name, a.place, a.part, true, x.vals.map Said.got, x.tables.map some, d⟩ :: l, ?_, ?_⟩
      · rw [hstep]
        show ((Step.tell _ back.head? m).bind fun y => _) = _
        rw [tell_ok (s := ⟨name, a, r.1, r.2, bad, hid, i, i + 1 == n,
          some ⟨fun _ => mv.say c, mv.hand⟩⟩) hb hh rfl hs hf.1]
        show ((Step.hear _ _ d m).bind fun m' => _) = _
        rw [hear_ok (s := ⟨name, a, r.1, r.2, bad, hid, i, i + 1 == n,
          some ⟨fun _ => mv.say c, mv.hand⟩⟩) hb hh rfl]
        show ((play _ ds back.tail _).map fun y => _) = _
        rw [hl]
        show Except.ok _ = Except.ok _
        simp [stateFrom, List.append_assoc]
      · show _ :: roundsOf l = _
        rw [hr]
  | [], [], _, _ :: _, _, _, _, hf, _ => by simp [fitsFrom] at hf
  | [], _ :: _, _, _, _, _, _, hf, _ => by simp [fitsFrom] at hf
  | _ :: _, [], _, _, _, _, _, hf, _ => by simp [fitsFrom] at hf
  | _ :: _, _ :: _, _, [], _, _, _, hf, _ => by simp [fitsFrom] at hf

/-- **The law**: `play` on one part's steps. -/
theorem play_steps (p : Part V W X) (hb : ∀ f o, p.bad f o = none)
    (hh : ∀ w f o, p.hid w f o = none) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins) (ds : List Fmt.Drawn)
    (back : List Fmt.RoundView) (m : Mid W X) (out : List Fmt.RoundView)
    (hf : fitsFrom c rs p.moves m.st m.shown ds = true)
    (h : alone p c m.st m.shown ds = some out) :
    ∃ l, play (p.steps name a rs v c) ds back m =
        .ok (l, ⟨stateFrom p.moves m.st ds, m.loc ++ ds, m.seen ++ out, m.opened⟩) ∧
            roundsOf l = out := by
  rw [steps_eq]
  refine play_stepsFrom name a p.bad _ hb (fun f o => ?_) p.moves.length c rs p.moves 0 ds back m
    out hf h
  cases v with
  | none => rfl
  | some w => exact hh w f o

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.stop_none
#print axioms ProofFile.Honest.SumLaw.tell_ok
#print axioms ProofFile.Honest.SumLaw.hear_ok
#print axioms ProofFile.Honest.SumLaw.steps_eq
#print axioms ProofFile.Honest.SumLaw.play_stepsFrom
#print axioms ProofFile.Honest.SumLaw.play_steps
#print axioms ProofFile.Honest.SumLaw.fitsFrom
#print axioms ProofFile.Honest.SumLaw.stateFrom
#print axioms ProofFile.Honest.SumLaw.stepsFrom
