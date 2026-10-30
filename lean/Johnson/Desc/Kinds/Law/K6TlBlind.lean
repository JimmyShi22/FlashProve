-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6TlBlind.lean: THE READERS OF THE OUTPUT HEAD's FOUR RUNS OF CLAIMS
("norm", "join", "policy", "logits") ARE BLIND TO THE DRAW OF THE APPROXIMATE RANGE PROOF's FIRST
HALF: the draw (Johnson/Desc/First/K8/TieRides.lean: Drawn) turns two fields of the open segment's
tail, which no reader of the output head's sub-protocol reads. For the row on that kind's text
(TlBlind, RunBlind: Johnson/Desc/First/K8/BlindPub.lean, BlindReaders.lean). Statements and proofs.

  alike_of_drawn   a draw in the head's link: the two states are Alike (Law/RunsFixed.lean), both
                   ways.
  head_of_letters, letters_drawn, letters_drawn_opt   the letters are read at the one state just
                   where they are read at the other, and they are the same.
  own_runBlind     RunBlind of the kind's own three runs (k6_run_spec · k6_same · k6_run_answers).
  putFork_drawn, join_runBlind   RunBlind of "join".
  withTables_drawn the tables that the reads' quiet step makes are blind to a draw; the two states
                   with them laid are a draw apart.
  k6Silent_blind, k6Silent_blind_found   so the filling of "silent" (Law/K6SilentCode.lean) is blind
                   where the run's reader is.
  readerOf_blind_found   readerOf_blind from a narrower premise: of the run that the reader
                   finds alone.
  runBlind_of_iff  two functions that accept together with one answer.
  k6_reader_blind, k6_forms_blind   MAIN: under K6States and K6Back (Law/K6Silent.lean,
                   Law/K6SilentRides.lean: which runs stand at the link's sub-protocol number b
                   under the four names, in whatever dress): TlBlind of the reader, and of the
                   link's readers' forms at the head's segment: both arms (the run's reader;
                   "silent").
  readersAt_blind_head   readersAt_blind at m = mH: there too the row asks RunBlind of the
                   stated runs alone.

WHAT IT IS NOT. FOUR OF THE HEAD's SEVEN LINES: "objects", "guests", "planes" are the lookup's
runs: for these readersAt_blind_head leaves RunBlind of the stated runs as its premise. K6States
and K6Back ARE PREMISES (paid at the seat, in scope, under Johnson/P4SR/: not called
here). Nothing on soundness.
LETTERS. e, e' in withTables_drawn stand under "there is": tied by withTables' two answers.

-/
import Mathlib
import Johnson.Desc.First.K8.BlindReaders
import Johnson.Desc.Kinds.Law.ReaderRides
import Johnson.Desc.Kinds.Law.K6SilentCode
import Johnson.Desc.Kinds.Law.HeadRunsCarry
import Johnson.Desc.Kinds.HeadCaller
import Johnson.Desc.Kinds.Law.K6SilentRides
import Johnson.Desc.Kinds.Law.HeardAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (Drawn TlBlind RunBlind drawn_ind blind_fork blind_lookHeard
  readerOf_blind readersOfLink_blind)
open VerifiableInference.Desc.K9 (readerOf RunOf readersAt statesOfLink holesAt phAt)
open OnBytes.PscRun (Later)

/-- **A draw in the head's link: the two states are alike, both ways.** -/
theorem alike_of_drawn {s t : S} (h : Drawn s t) :
    ((∃ o, s.here = .head o) ∨ ∃ o, t.here = .head o) → Alike s t ∧ Alike t s := by
  refine drawn_ind (motive := fun s t =>
    ((∃ o, s.here = .head o) ∨ ∃ o, t.here = .head o) → Alike s t ∧ Alike t s) ?_ ?_ ?_ h
  · rintro s a mm f hs (⟨o, ho⟩ | ⟨o, ho⟩)
    · rw [hs] at ho
      cases ho
    · cases ho
  · rintro s a mm f hs (⟨o, ho⟩ | ⟨o, ho⟩)
    · rw [hs] at ho
      cases ho
    · cases ho
  · rintro s a mm f hs _ _
    exact ⟨⟨a, _, hs, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Later.refl _, rfl⟩,
      ⟨_, a, rfl, hs, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Later.refl _, rfl⟩⟩

section At
variable (h : Model.Head.Shape) (iU3 : Nat)

/-- Where the letters are read the head's link is entered. -/
theorem head_of_letters (p : Par) {s : S} {v : Given × Behind × Places}
    (e : lettersAt p (seatAt h iU3) s = .ok v) : ∃ o, s.here = .head o := by
  unfold lettersAt at e
  cases hg : given p (seatAt h iU3) s with
  | error m => rw [hg] at e; cases e
  | ok g =>
    rw [hg] at e
    cases hH : (seatAt h iU3).heard s with
    | none => rw [hH] at e; cases e
    | some H =>
      have e' : (match s.here with
        | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
          allOf o.F x (some (keptOf q x.wpl.sL))
        | _ => none) = some H := hH
      cases hh : s.here with
      | head o => exact ⟨o, rfl⟩
      | _ => rw [hh] at e'; cases e'

/-- **The letters are blind to a draw.** -/
theorem letters_drawn (p : Par) {s t : S} (hd : Drawn s t) (v : Given × Behind × Places) :
    lettersAt p (seatAt h iU3) t = .ok v ↔ lettersAt p (seatAt h iU3) s = .ok v :=
  ⟨fun e => letters_alike h iU3 p (alike_of_drawn hd (Or.inr (head_of_letters h iU3 p e))).2 v e,
    fun e => letters_alike h iU3 p (alike_of_drawn hd (Or.inl (head_of_letters h iU3 p e))).1 v e⟩

theorem letters_drawn_opt (p : Par) {s t : S} (hd : Drawn s t) :
    (lettersAt p (seatAt h iU3) t).toOption = (lettersAt p (seatAt h iU3) s).toOption := by
  cases hs : lettersAt p (seatAt h iU3) s with
  | ok v => rw [(letters_drawn h iU3 p hd v).2 hs]
  | error m =>
    cases ht : lettersAt p (seatAt h iU3) t with
    | ok v => rw [(letters_drawn h iU3 p hd v).1 ht] at hs; cases hs
    | error m' => rfl

/-- One way, at one of the three own runs. -/
theorem own_run_drawn (l piece : Nat) (p : Par) {name : String}
    {run : Nat → S → Except String (List Claim × S)}
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run) (n : Nat)
    {s t : S}
    (hl : ∀ v, lettersAt p (seatAt h iU3) s = .ok v → lettersAt p (seatAt h iU3) t = .ok v)
    {y : List Claim × S} (e : run n s = .ok y) : y.2 = s ∧ run n t = .ok (y.1, t) := by
  obtain ⟨c, s1⟩ := y
  obtain ⟨g, b, x, fs, h1, h2, rfl⟩ :=
    k6_run_spec asClaim (seatAt h iU3) l piece p name run n s s1 c hrun e
  exact ⟨k6_same h iU3 l piece p (name, run) (lookup_mem _ _ _ hrun) n s _ e,
    k6_run_answers h iU3 l piece p name run hrun n t g b x fs (hl _ h1) h2⟩

/-- **THE HEAD's THREE OWN RUNS: THE CLAIMS AND THE LEDGER BEHIND ARE BLIND TO A DRAW.** -/
theorem own_runBlind (l piece : Nat) (p : Par) {name : String}
    {run : Nat → S → Except String (List Claim × S)}
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run) (n : Nat) :
    RunBlind (run n) := by
  intro s t hd
  cases hs : run n s with
  | ok y =>
    obtain ⟨e1, e2⟩ := own_run_drawn h iU3 l piece p hrun n
      (fun v => (letters_drawn h iU3 p hd v).2) hs
    rw [e2]
    show some (y.1, t.fork?) = some (y.1, y.2.fork?)
    rw [e1, blind_fork s t hd]
  | error m =>
    cases ht : run n t with
    | ok y =>
      obtain ⟨_, e2⟩ := own_run_drawn h iU3 l piece p hrun n
        (fun v => (letters_drawn h iU3 p hd v).1) ht
      rw [e2] at hs
      cases hs
    | error m' => rfl

/-- The ledger behind a marking is blind to a draw. -/
theorem putFork_drawn {s t : S} (hd : Drawn s t) (G : Fork) :
    (t.putFork G).fork? = (s.putFork G).fork? := by
  refine drawn_ind (motive := fun s t => (t.putFork G).fork? = (s.putFork G).fork?) ?_ ?_ ?_ hd
  · intro s a mm f hs
    simp [S.putFork, S.fork?, hs]
  · intro s a mm f hs
    simp [S.putFork, S.fork?, hs]
  · intro s a mm f hs ho
    simp [S.putFork, S.fork?, hs, ho]

/-- **"join": THE CLAIM AND THE LEDGER BEHIND ARE BLIND TO A DRAW.** -/
theorem join_runBlind (p : Par) (n : Nat) :
    RunBlind (K3.joinRun (K3.seatCalls asClaim) (callerKeys p (seatAt h iU3)) n) := by
  intro s t hd
  have e1 : (K3.seatCalls asClaim).fork t = (K3.seatCalls asClaim).fork s := blind_fork s t hd
  have e2 : (K3.seatCalls asClaim).heard t = (K3.seatCalls asClaim).heard s :=
    blind_lookHeard s t hd
  have e3 : callerKeys p (seatAt h iU3) t = callerKeys p (seatAt h iU3) s := by
    unfold callerKeys
    simp only [letters_drawn_opt h iU3 p hd]
  unfold K3.joinRun
  simp only [bind, Except.bind, e1, e2, e3]
  cases named "K3 join: no sub-proof is open" ((K3.seatCalls asClaim).fork s) with
  | error m => rfl
  | ok F =>
    dsimp only
    cases named "K3 join: nothing was heard" ((K3.seatCalls asClaim).heard s) with
    | error m => rfl
    | ok g =>
      dsimp only
      cases need "K3 join: it is made once" (K3.unpaid F g.owedJoin) with
      | error m => rfl
      | ok _ =>
        dsimp only
        cases named "K3 join: the caller's keys" (callerKeys p (seatAt h iU3) s) with
        | error m => rfl
        | ok KF =>
          dsimp only
          cases named "K3 join: one form and one weight a call" (First.Look.joinF g KF F []) with
          | error m => rfl
          | ok x =>
            show some ([asClaim x.1], (t.putFork x.2.1).fork?) =
              some ([asClaim x.1], (s.putFork x.2.1).fork?)
            rw [putFork_drawn hd]

end At

/-- **The tables that the quiet step makes are blind to a draw; the two states with them laid are a
draw apart.** -/
theorem withTables_drawn (P : K8.ReadsQuiet.PH) {s t : S} (hd : Drawn s t) :
    (withTables P s = none ∧ withTables P t = none) ∨
      ∃ e e', withTables P s = some e ∧ withTables P t = some e' ∧ Drawn e e' := by
  refine drawn_ind (motive := fun s t => (withTables P s = none ∧ withTables P t = none) ∨
      ∃ e e', withTables P s = some e ∧ withTables P t = some e' ∧ Drawn e e') ?_ ?_ ?_ hd
  · intro s a mm f hs
    exact Or.inl ⟨by simp [withTables, hs], by simp [withTables]⟩
  · intro s a mm f hs
    exact Or.inl ⟨by simp [withTables, hs], by simp [withTables]⟩
  · intro s a mm f hs ho
    have et : tablesAt P
        { s with here := .head { a with tl := { a.tl with cfF := mm, cfFirst := f } } } =
          tablesAt P s := by
      unfold tablesAt
      rw [hs]
      rfl
    cases hT : tablesAt P s with
    | none =>
      refine Or.inl ⟨?_, ?_⟩
      · unfold withTables
        rw [hs]
        simp only [hT, Option.map_none]
      · unfold withTables
        simp only [et, hT, Option.map_none]
    | some tt =>
      refine Or.inr ⟨{ s with here := .head { a with t := some tt } },
        { s with here :=
            .head { a with tl := { a.tl with cfF := mm, cfFirst := f }, t := some tt } },
        ?_, ?_, ⟨a.tl, mm, f, ?_, ?_⟩⟩
      · unfold withTables
        rw [hs]
        simp only [hT, Option.map_some]
      · unfold withTables
        simp only [et, hT, Option.map_some]
      · simp [S.tl?, ho]
      · simp [S.putTl, ho]

/-- **THE FILLING OF "silent" IS BLIND TO A DRAW**, where the runs of that name that are stated
are. -/
theorem k6Silent_blind (P : K8.ReadsQuiet.PH) (states : Nat → List (RunOf S)) (b : Nat)
    (name : String) (hR : ∀ r ∈ states b, (r.1 == name) = true → RunBlind (r.2 0)) :
    TlBlind (k6Silent P states b name) := fun s t hd => by
  unfold k6Silent
  rcases withTables_drawn P hd with ⟨e1, e2⟩ | ⟨e, e', e1, e2, hd'⟩
  · rw [e1, e2]
  · rw [e1, e2]
    exact readerOf_blind states b name hR e e' hd'

/-- The reader of a run is blind where THE RUN THAT IT FINDS is. (readerOf_blind asks it of
every run of that name; its proof spends the found one alone: typed again with the narrower
premise.) -/
theorem readerOf_blind_found (states : Nat → List (RunOf S)) (b : Nat) (name : String)
    (hR : ∀ r, (states b).find? (fun r => r.1 == name) = some r → RunBlind (r.2 0)) :
    TlBlind (readerOf states b name) := by
  cases hf : (states b).find? (fun r => r.1 == name) with
  | none =>
    intro s t _
    unfold readerOf
    rw [hf]
    rfl
  | some r =>
    have e : readerOf states b name = readerOf (fun _ => [r]) b name := by
      have hn : (r.1 == name) = true := List.find?_some (p := fun r : RunOf S => r.1 == name) hf
      funext s
      unfold readerOf
      rw [hf]
      simp [List.find?, hn]
    rw [e]
    refine readerOf_blind (fun _ => [r]) b name fun r' hr' _ => ?_
    obtain rfl := List.mem_singleton.1 hr'
    exact hR _ hf

/-- The same for the filling of "silent". -/
theorem k6Silent_blind_found (P : K8.ReadsQuiet.PH) (states : Nat → List (RunOf S)) (b : Nat)
    (name : String) (hR : TlBlind (readerOf states b name)) :
    TlBlind (k6Silent P states b name) := fun s t hd => by
  unfold k6Silent
  rcases withTables_drawn P hd with ⟨e1, e2⟩ | ⟨e, e', e1, e2, hd'⟩
  · rw [e1, e2]
  · rw [e1, e2]
    exact hR e e' hd'

/-- Two functions that accept together, with one answer: where the one commutes with the draw, so
does the other. -/
theorem runBlind_of_iff {f f' : S → Except String (List Claim × S)}
    (h1 : ∀ t y, f t = .ok y → f' t = .ok y) (h2 : ∀ t y, f' t = .ok y → f t = .ok y)
    (hB : RunBlind f') : RunBlind f := by
  have e : ∀ t, (f t).toOption = (f' t).toOption := fun t => by
    cases hf : f t with
    | ok y => rw [h1 t y hf]
    | error m =>
      cases hf' : f' t with
      | ok y => rw [h2 t y hf'] at hf; cases hf
      | error m' => rfl
  intro s t hd
  rw [e s, e t]
  exact hB s t hd

section Stated
variable {h : Model.Head.Shape} {iU3 : Nat} {p : Par} {l piece : Nat}
  {states : Nat → List (RunOf S)} {b : Nat}

/-- **THE READER OF EACH OF THE HEAD's FOUR RUNS, AS THEY ARE STATED (in whatever dress K6States and
K6Back admit), IS BLIND TO A DRAW.** -/
theorem k6_reader_blind (KS : K6States h iU3 p l piece states b)
    (KB : K6Back h iU3 p l piece states b) (name : String) (hn : K6Name name) :
    TlBlind (readerOf states b name) := by
  refine readerOf_blind_found states b name fun r hr => ?_
  have own : name = "norm" ∨ name = "policy" ∨ name = "logits" → RunBlind (r.2 0) := fun h3 => by
    obtain ⟨run, run', hf, hrun, hans⟩ := KS.own name h3
    obtain rfl : (name, run) = r := Option.some.inj (hf.symm.trans hr)
    exact runBlind_of_iff (hans 0) (fun t y hy => KB.own name run run' hf hrun 0 t y hy (by
      rw [k6_same h iU3 l piece p (name, run') (lookup_mem _ _ _ hrun) 0 t y hy]))
      (own_runBlind h iU3 l piece p hrun 0)
  rcases hn with h1 | h1 | h1 | rfl
  · exact own (Or.inl h1)
  · exact own (Or.inr (Or.inl h1))
  · exact own (Or.inr (Or.inr h1))
  · obtain ⟨run, hf, hans⟩ := KS.join
    obtain rfl : ("join", run) = r := Option.some.inj (hf.symm.trans hr)
    exact runBlind_of_iff (hans 0) (fun t y hy => KB.join run hf 0 t y hy (by
      obtain ⟨F, g, _, _, e⟩ := k6_join _ 0 t y hy
      rw [e, out_putFork])) (join_runBlind h iU3 p 0)

/-- **THE HEAD's FOUR LINES OF THE ROW**: at a link whose stated runs are the head's four. -/
theorem k6_forms_blind {lk : VerifiableInference.Desc.Link S Claim}
    (KS : K6States h iU3 p l piece (statesOfLink lk) b)
    (KB : K6Back h iU3 p l piece (statesOfLink lk) b) (X : OnBytes.Model.Verify.Public) (mH : Nat)
    (name : String) (hn : K6Name name) :
    TlBlind ((VerifiableInference.Desc.K9.readersOfLink (holesAt X mH mH lk) lk).forms b name) :=
  fun s t hd => by
  have hne : (name == "K8.equations") = false := by
    rcases hn with rfl | rfl | rfl | rfl <;> decide
  have e1 := k6_reader_blind KS KB name hn
  have e2 : TlBlind ((holesAt X mH mH lk).silent b name) := by
    unfold holesAt
    rw [beq_self_eq_true, if_pos rfl]
    exact k6Silent_blind_found _ _ b name e1
  show (if (name == "K8.equations") = true then (holesAt X mH mH lk).small t
    else match readerOf (statesOfLink lk) b name t with
      | some R => some R
      | Option.none => (holesAt X mH mH lk).silent b name t) =
    (if (name == "K8.equations") = true then (holesAt X mH mH lk).small s
    else match readerOf (statesOfLink lk) b name s with
      | some R => some R
      | Option.none => (holesAt X mH mH lk).silent b name s)
  rw [hne, e1 s t hd, e2 s t hd]
  rfl

end Stated

/-- **SO AT THE OUTPUT HEAD's SEGMENT TOO THE ROW ASKS RunBlind OF THE STATED RUNS ALONE.** -/
theorem readersAt_blind_head (lk : Nat → Option (VerifiableInference.Desc.Link S Claim))
    (X : OnBytes.Model.Verify.Public) (mH : Nat) (b : Nat) (name : String)
    (hn : (name == "K8.equations") = false)
    (hR : ∀ l, lk mH = some l → ∀ r ∈ statesOfLink l b, (r.1 == name) = true → RunBlind (r.2 0)) :
    TlBlind ((readersAt lk X mH mH).forms b name) := by
  cases hl : lk mH with
  | none =>
    rw [VerifiableInference.Desc.K9.readersAt_none lk X mH mH hl]
    exact fun _ _ _ => rfl
  | some l =>
    rw [VerifiableInference.Desc.K9.readersAt_some lk X mH mH l hl]
    refine readersOfLink_blind _ l b name hn (hR l hl) ?_
    unfold holesAt
    rw [beq_self_eq_true, if_pos rfl]
    exact k6Silent_blind _ _ b name (hR l hl)

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.own_runBlind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.join_runBlind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.readersAt_blind_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_forms_blind
