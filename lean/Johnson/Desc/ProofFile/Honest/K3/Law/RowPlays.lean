-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/RowPlays.lean: the proofs of the statements `RowPlays` and
`CourseSays` (Honest/K3/Law/Statements.lean). `RowPlays`: the frame's player on a lookup's row of
parts, at the planner's entries, goes through and yields the rounds of a course: the stages, each
played alone; and every row's coins are some course's. Theorems, with definitions.

Terms. Honest/K3/GLOSSARY.md ("book, coins", "course", "play", "row", "stage").

What is shown, by the file's sections.
  1. `readCs`, `fillCs`, `readRuns`, `fillRuns`, `rowRead`, `courseCoins`: a row's coins read as
     plain functions of numbers, and laid into the type in which a course holds a stage's coins,
     without a cast.
  2. `stage_vars`, `stage_ends_ne`, `runsOf_counts`: what the proof reads of the stages' calls.
  3. `CoinsAt`, `CoinsRow`, `stage_eq`, `aloneRow_run`: where part by part the coins are the
     course's, the row's parts, played alone one behind the other, are the course's run.
  4. `row_noStops`, `part_sends`, `aloneRow_some`, `row_fits`: no part of the row stops; every move
     answers; every message has the shape of the planner's entry.
  5. `coinsRow_of_read`, `spent_of_coins`, `coinsAre`: the coins.
  6. `RowPlaysFull`, `rowPlaysFull`, `rowPlays`: the statement in full (for all stored rounds to
     fall back on; with all that the player leaves; with what each played round bears), and
     `RowPlays` as the case of it with nothing to fall back on.
  7. `stage_some`, `run_some`, `courseSays`: the statement `CourseSays`: all stages of a course
     answer.
Definitions that stand in no line above: `Rd`, `runsOf`, `rowOf`, `stageCounts`, `cutOf`.

Hypotheses that remain. `rowPlaysFull`, `rowPlays` and `courseSays` have those inside their
statements (Statements.lean; `RowPlaysFull` here). In the steps: `h`, `hk`: the stage has the call
k, or none; `h`: (in `stage_eq`) `CoinsAt`; `hc`: (in `coinsAre`) `CoinsRow`; `hR`: (in
`coinsRow_of_read`) the course's coins are `courseCoins` at a function g (that g is read off the
row's is the first of its two hypotheses without a name); `h`: (in `stage_some`) as many challenges
as the stage has rounds; (in `coinsE_fill`, `runs_of_csAllE`) two counts, or two lists of coins, are
equal. Eleven steps have hypotheses without a name: `csAllE_fill`, `stage_ends_ne`, `aloneRow_run`,
`fits_of_sends` (two), `row_fits`, `aloneRow_some`, `endRow_unit`, `coinsRow_of_read` (two),
`spent_of_coins` (two), `drawsFit_length`, `run_some`.

How the proof goes. It rests on Honest/K3/Law/PlayPart.lean (for every part),
Honest/K3/Law/SumFits.lean (plain facts on the masked sumcheck's part), Honest/K3/RowLaw.lean and
Honest/K3/RowAt.lean (the stages' entries are the verifier's; no stage stands twice), and, through
PlayPart.lean, on Honest/Law/Play.lean.

Users. This file is imported by Honest/K3/Law/RowSeated.lean, Honest/K3/Law/SpentFlat.lean
[not in this library] and Honest/K3/Law/Keep/RowKeepLaw.lean.

Limits. It says that rounds come and whose they are; nothing on what they are worth. The row is the
one at the jobs' own input type (`lookRow`): the row seated by `Part.lift` (`proverSideOfLookupInChainAtOneOwner`) is not
spoken of.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Statements
import Johnson.Desc.ProofFile.Honest.K3.Law.SumFits
import Johnson.Desc.ProofFile.Honest.K3.RowAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE)
open VerifiableInference.Desc (Oracle)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call)
open VerifiableInference.Desc.K3 (entriesV entriesFit)
open ProofFile.Honest.SumLaw (alone aloneFrom SumCoins firstRun endRun)

variable {V W : Type}

/-- The two functions by which the row reads the run's points. -/
abbrev Rd : Reads := ⟨ptsOf, pointsAt⟩

/-! ## 1 Coins as plain functions of numbers -/

/-- The coin number i of the extension field; 0 beyond the count. -/
def readCs {d : Due} (c : Cs d) (i : Nat) : Cb.Gl.E := if h : i < d.e then c.e ⟨i, h⟩ else 0

/-- Coins at a count, of a function of numbers; the base field's are 0, whatever the count says of
that field: they are not read off g. The stretches that a lookup's parts state (`runsOf`) have no
coin of the base field. -/
def fillCs (d : Due) (g : Nat → Cb.Gl.E) : Cs d := ⟨fun _ => 0, fun i => g i.1⟩

theorem coinsE_fill {d d' : Due} (c : Cs d) (h : d'.e = d.e) :
    coinsE (fillCs d' (readCs c)) = coinsE c := by
  unfold coinsE
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    have hi : i < d.e := by simpa using h2
    simp [fillCs, readCs, hi]

/-- Stretch number j, coin number i; 0 beyond the list of stretches, and (`readCs`) beyond a
stretch's count. -/
def readRuns : (l : List (String × Due)) → CsAll l → Nat → Nat → Cb.Gl.E
  | [], _, _, _ => 0
  | _ :: _, c, 0, i => readCs c.1 i
  | _ :: l, c, j + 1, i => readRuns l c.2 j i

def fillRuns : (l : List (String × Due)) → (Nat → Nat → Cb.Gl.E) → CsAll l
  | [], _ => ()
  | d :: l, g => (fillCs d.2 (g 0), fillRuns l fun j => g (j + 1))

theorem csAllE_fill : ∀ (l l' : List (String × Due)) (c : CsAll l),
    l'.map (·.2.e) = l.map (·.2.e) → csAllE l' (fillRuns l' (readRuns l c)) = csAllE l c
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | d :: l, d' :: l', c, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    show coinsE (fillCs d'.2 (readCs c.1)) :: csAllE l' (fillRuns l' (readRuns l c.2)) =
      coinsE c.1 :: csAllE l c.2
    rw [coinsE_fill c.1 h.1, csAllE_fill l l' c.2 h.2]

/-- Part number j of a row, stretch, coin: of what the part spends; 0 beyond the row's parts, and
where `readRuns` is 0. -/
def rowRead {X : Type} : (ps : List (Part V W X)) → RowCoins ps → Nat → Nat → Nat → Cb.Gl.E
  | [], _, _ => fun _ _ => 0
  | p :: _, c, 0 => readRuns p.spends c.1.2.1
  | _ :: ps, c, j + 1 => rowRead ps c.2 j

/-- **A course's coins, of a function of numbers**: the stage's own number in the row, stretch,
coin. -/
def courseCoins (a : At) (g : Nat → Nat → Nat → Cb.Gl.E) (s : Stage) : StageCoins a s :=
  show Handed _ _ _ from (Cs.empty, fillRuns _ (g (indexOf a.face s)), ())

/-! ## 2 What is read of the stages' calls -/

theorem stage_vars (f : LFace) (s : Stage) (k : Call) (h : s.call f = some k) :
    ∀ v ∈ k.vs, v.d ≠ 1 := by
  cases s with
  | tie n =>
    cases n with
    | zero =>
      simp only [Stage.call, Option.some.injEq] at h; subst h; intro v hv
      simp [VerifiableInference.Desc.K3.noVar] at hv
    | succ n =>
      simp only [Stage.call, Option.some.injEq] at h; subst h; intro v hv
      simp [VerifiableInference.Desc.K3.noVar] at hv
  | split i =>
    simp only [Stage.call, Option.some.injEq] at h; subst h; intro v hv
    simp [VerifiableInference.Desc.K3.noVar] at hv
  | key i m =>
    simp only [Stage.call, Option.some.injEq] at h; subst h; intro v hv
    simp only [levelCall, VerifiableInference.Desc.First.ProdV.levelVars, List.mem_map] at hv
    obtain ⟨_, _, rfl⟩ := hv
    simp [Var.d]
  | tab l =>
    simp only [Stage.call, Option.some.injEq] at h; subst h; intro v hv
    simp only [levelCall, VerifiableInference.Desc.First.ProdV.levelVars, List.mem_map] at hv
    obtain ⟨_, _, rfl⟩ := hv
    simp [Var.d]
  | leaves =>
    simp only [Stage.call, Option.some.injEq] at h; subst h; intro v hv
    simp only [VerifiableInference.Desc.K3.leafVars, List.mem_map] at hv
    obtain ⟨j, _, rfl⟩ := hv
    simp only [Var.d]; split <;> decide
  | bits =>
    simp only [Stage.call, Option.some.injEq] at h; subst h; intro v hv
    simp only [VerifiableInference.Desc.K3.bitsCall, List.mem_map] at hv
    obtain ⟨j, _, rfl⟩ := hv
    simp [Var.d]
  | shift => simp [Stage.call] at h
  | alpha => simp [Stage.call] at h
  | join => simp [Stage.call] at h
  | keyLine i m => simp [Stage.call] at h
  | tabLine l => simp [Stage.call] at h
  | zero => simp [Stage.call] at h

/-- A stage's call has no ends, or ends with an end value at least. -/
theorem stage_ends_ne (f : LFace) (s : Stage) (k : Call) (h : s.call f = some k) :
    ∀ e, k.ends = some e → e.n ≠ 0 := by
  cases s with
  | tie n =>
    cases n with
    | zero =>
      simp only [Stage.call, Option.some.injEq] at h; subst h; intro e he
      simp only [VerifiableInference.Desc.K3.noVar, Option.some.injEq] at he; subst he; decide
    | succ n =>
      simp only [Stage.call, Option.some.injEq] at h; subst h; intro e he
      simp only [VerifiableInference.Desc.K3.noVar, Option.some.injEq] at he; subst he; decide
  | split i =>
    simp only [Stage.call, Option.some.injEq] at h; subst h; intro e he
    simp only [VerifiableInference.Desc.K3.noVar, Option.some.injEq] at he; subst he; decide
  | key i m =>
    simp only [Stage.call, Option.some.injEq] at h; subst h; intro e he
    simp only [levelCall, Option.some.injEq] at he; subst he; decide
  | tab l =>
    simp only [Stage.call, Option.some.injEq] at h; subst h; intro e he
    simp only [levelCall, Option.some.injEq] at he; subst he; decide
  | leaves =>
    simp only [Stage.call, Option.some.injEq] at h; subst h; intro e he
    simp at he
  | bits =>
    simp only [Stage.call, Option.some.injEq] at h; subst h; intro e he
    simp only [VerifiableInference.Desc.K3.bitsCall, Option.some.injEq] at he; subst he; decide
  | shift => simp [Stage.call] at h
  | alpha => simp [Stage.call] at h
  | join => simp [Stage.call] at h
  | keyLine i m => simp [Stage.call] at h
  | tabLine l => simp [Stage.call] at h
  | zero => simp [Stage.call] at h

theorem partOf_some (J : LookJobs W) (a : At) (s : Stage) (i : Nat) (k : Call)
    (h : s.call a.face = some k) :
    partOf (V := V) Rd J a s i =
      sumPart (sumName a.place i) (endName a.place i) (jobOf Rd J a s k) := by
  simp only [partOf, h]

theorem partOf_none (J : LookJobs W) (a : At) (s : Stage) (i : Nat) (h : s.call a.face = none) :
    partOf (V := V) Rd J a s i = quiet := by
  simp only [partOf, h]

theorem shapeAt_some (a : At) (s : Stage) (k : Call) (h : s.call a.face = some k) :
    shapeAt a s = k := by
  simp [shapeAt, h]

/-- The names and counts of the two stretches of a call. -/
abbrev runsOf (n e : String) (k : Call) : List (String × Due) :=
  (n, ⟨0, ownRun k⟩) :: endRuns e k.ends

theorem runsOf_counts (n e n' e' : String) (k : Call) :
    (runsOf n e k).map (·.2.e) = (runsOf n' e' k).map (·.2.e) := by
  obtain ⟨lead, vs, ends⟩ := k
  cases ends <;> rfl

/-- The two stretches as lists. -/
theorem csAllE_runs (n e : String) (k : Call) (c : CsAll (runsOf n e k)) :
    csAllE _ c = coinsE c.1 :: (if k.ends.isNone then [] else [endCoins e k.ends c.2]) := by
  revert c
  obtain ⟨lead, vs, ends⟩ := k
  cases ends <;> intro c <;> rfl

theorem runs_of_csAllE (n e n' e' : String) (k : Call) (c : CsAll (runsOf n e k))
    (c' : CsAll (runsOf n' e' k)) (h : csAllE _ c = csAllE _ c') :
    coinsE c.1 = coinsE c'.1 ∧ endCoins e k.ends c.2 = endCoins e' k.ends c'.2 := by
  revert h
  revert c c'
  obtain ⟨lead, vs, ends⟩ := k
  cases ends with
  | none =>
    intro c c' h
    have h' : [coinsE c.1] = [coinsE c'.1] := h
    exact ⟨by simpa using h', rfl⟩
  | some x =>
    intro c c' h
    have h' : [coinsE c.1, coinsE c.2.1] = [coinsE c'.1, coinsE c'.2.1] := h
    simp only [List.cons.injEq, and_true] at h'
    exact h'

/-! ## 3 The row's parts, played alone, are the course's run -/

variable (R : Course W)

/-- The row over a list of stages, each with its number. -/
abbrev rowOf (V : Type) (l : List (Stage × Nat)) : List (Part V W Unit) :=
  l.map fun x => partOf Rd R.J R.a x.1 x.2

/-- At a stage with a call: what the part spends is what the course has for the stage, stretch by
stretch. -/
def CoinsAt (x : Stage × Nat) (c₀ : (partOf (V := V) Rd R.J R.a x.1 x.2).Coins) : Prop :=
  (x.1.call R.a.face).isSome = true → csAllE _ c₀.2.1 = csAllE _ (R.c x.1).2.1

def CoinsRow : (l : List (Stage × Nat)) → RowCoins (rowOf R V l) → Prop
  | [], _ => True
  | x :: l, c =>
    let c' : (partOf (V := V) Rd R.J R.a x.1 x.2).Coins × RowCoins (rowOf R V l) := c
    CoinsAt R x c'.1 ∧ CoinsRow l c'.2

theorem alone_quiet (c : (quiet : Part V W Unit).Coins) (t : State W Unit) (seen : Seen)
    (ds : List Fmt.Drawn) :
    alone quiet c t seen ds = (match ds with
      | [d] => some [⟨[], d⟩]
      | _ => none) := by
  cases ds with
  | nil => simp [alone, aloneFrom, quiet]
  | cons d ds => cases ds <;> simp [alone, aloneFrom, quiet]

/-- **A part of the row, played alone, is the course's stage.** -/
theorem stage_eq (x : Stage × Nat) (c₀ : (partOf (V := V) Rd R.J R.a x.1 x.2).Coins)
    (h : CoinsAt R x c₀) (t : State W Unit) (seen : Seen) (ds : List Fmt.Drawn) :
    alone (partOf (V := V) Rd R.J R.a x.1 x.2) c₀ t seen ds = R.stage x.1 t seen ds := by
  cases hk : x.1.call R.a.face with
  | none =>
    have key : ∀ (p : Part V W Unit) (_ : p = quiet) (c : p.Coins), alone p c t seen ds =
        (match ds with
          | [d] => some [⟨[], d⟩]
          | _ => none) := by
      intro p hp c
      subst hp
      exact alone_quiet c t seen ds
    rw [key _ (partOf_none R.J R.a x.1 x.2 hk) c₀]
    simp only [Course.stage, hk]
    rcases ds with _ | ⟨d, _ | ⟨d', ds⟩⟩ <;> rfl
  | some k =>
    have hs := shapeAt_some R.a x.1 k hk
    have key : ∀ (p : Part V W Unit)
        (hp : p = sumPart (sumName R.a.place x.2) (endName R.a.place x.2) (jobOf Rd R.J R.a x.1 k))
        (c : p.Coins) (k' : Call) (_ : k' = k)
        (c' : Handed ⟨0, 0⟩ (runsOf (sumName R.a.place (indexOf R.a.face x.1))
          (endName R.a.place (indexOf R.a.face x.1)) k') []),
        csAllE p.spends c.2.1 = csAllE _ c'.2.1 →
        alone p c t seen ds = alone (sumPart (V := Unit) (sumName R.a.place (indexOf R.a.face x.1))
          (endName R.a.place (indexOf R.a.face x.1)) (jobOf Rd R.J R.a x.1 k')) c' t seen ds := by
      intro p hp c k' hk' c' hc
      subst hp
      subst hk'
      obtain ⟨h1, h2⟩ := runs_of_csAllE _ _ _ _ k' c.2.1 c'.2.1 hc
      exact aloneFrom_congr c c' _ _ (by
        have := sumPart_coins (V := V) _ _ _ _ (jobOf Rd R.J R.a x.1 k') c c' h1 h2
        exact this) t seen ds
    have := key _ (partOf_some R.J R.a x.1 x.2 k hk) c₀ (shapeAt R.a x.1) hs (R.c x.1)
      (h (by simp [hk]))
    rw [this]
    simp only [Course.stage, hk]

/-- **The row's parts, played alone one behind the other, are the course's run.** -/
theorem aloneRow_run : ∀ (l : List (Stage × Nat)) (c : RowCoins (rowOf R V l)) (t : State W Unit)
    (seen : Seen) (ds : List Fmt.Drawn), CoinsRow R l c →
    aloneRow (rowOf R V l) c t seen ds = R.run (l.map (·.1)) t seen ds
  | [], _, _, _, [], _ => rfl
  | [], _, _, _, _ :: _, _ => rfl
  | x :: l, c, t, seen, ds, h => by
    let c' : (partOf (V := V) Rd R.J R.a x.1 x.2).Coins × RowCoins (rowOf R V l) := c
    have h' : CoinsAt R x c'.1 ∧ CoinsRow R l c'.2 := h
    have hm : (partOf (V := V) Rd R.J R.a x.1 x.2).moves.length = x.1.rounds R.a.face :=
      partOf_moves _ _ _ _ _
    show (alone (partOf (V := V) Rd R.J R.a x.1 x.2) c'.1 t seen
        (ds.take (partOf (V := V) Rd R.J R.a x.1 x.2).moves.length)).bind (fun y =>
          (aloneRow (rowOf R V l) c'.2 (endFrom (partOf (V := V) Rd R.J R.a x.1 x.2).moves t
            (ds.take (partOf (V := V) Rd R.J R.a x.1 x.2).moves.length)) (seen.plus y)
            (ds.drop (partOf (V := V) Rd R.J R.a x.1 x.2).moves.length)).map (y ++ ·)) =
      (R.stage x.1 t seen (ds.take (x.1.rounds R.a.face))).bind fun y =>
        (R.run (l.map (·.1)) { t with heard := t.heard ++ ds.take (x.1.rounds R.a.face) }
          (seen.plus y) (ds.drop (x.1.rounds R.a.face))).map (y ++ ·)
    rw [hm, stage_eq R x c'.1 h'.1]
    cases hst : R.stage x.1 t seen (ds.take (x.1.rounds R.a.face)) with
    | none => rfl
    | some y =>
      have hal : alone (partOf (V := V) Rd R.J R.a x.1 x.2) c'.1 t seen
          (ds.take (x.1.rounds R.a.face)) = some y := by
        rw [stage_eq R x c'.1 h'.1]; exact hst
      have hlen := (aloneFrom_length c'.1 _ t seen _ y hal).1
      show (aloneRow (rowOf R V l) c'.2 (endFrom (partOf (V := V) Rd R.J R.a x.1 x.2).moves t
            (ds.take (x.1.rounds R.a.face))) (seen.plus y) (ds.drop (x.1.rounds R.a.face))).map
            (y ++ ·) = _
      rw [endFrom_unit _ t _ hlen, aloneRow_run l c'.2 _ _ _ h'.2]
      rfl

/-! ## 4 No stop; every move answers; every message has its entry's shape -/

theorem part_noStops (x : Stage × Nat) :
    (∀ f o, (partOf (V := V) Rd R.J R.a x.1 x.2).bad f o = none) ∧
      ∀ v f o, (partOf (V := V) Rd R.J R.a x.1 x.2).hid v f o = none := by
  cases hk : x.1.call R.a.face with
  | none => rw [partOf_none R.J R.a x.1 x.2 hk]; exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  | some k => rw [partOf_some R.J R.a x.1 x.2 k hk]; exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem row_noStops (l : List (Stage × Nat)) : NoStops (rowOf R V l) := by
  intro p hp
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 hp
  exact part_noStops R x

/-- How many scalars each round of a stage sends. -/
def stageCounts (f : LFace) (s : Stage) : List Nat :=
  match s.call f with
  | some k => scalarsOf k
  | none => [0]

theorem part_sends (x : Stage × Nat) :
    AllTwo Sends (stageCounts R.a.face x.1) (partOf (V := V) Rd R.J R.a x.1 x.2).moves := by
  cases hk : x.1.call R.a.face with
  | none =>
    rw [partOf_none R.J R.a x.1 x.2 hk]
    simp only [stageCounts, hk]
    exact ⟨fun _ _ _ => ⟨[], rfl, rfl⟩, trivial⟩
  | some k =>
    rw [partOf_some R.J R.a x.1 x.2 k hk]
    simp only [stageCounts, hk]
    exact sumPart_sends _ _ (jobOf Rd R.J R.a x.1 k) (stage_vars R.a.face x.1 k hk)

/-- What the cut of a message reads of an entry. -/
def cutOf (e : Fmt.Entry) : Nat × Nat × Nat := (e.msg, e.answers, e.roots)

theorem entries_cut (f : LFace) (s : Stage) :
    (Stage.entries f s).map cutOf = (stageCounts f s).map fun n => (24 * n, 0, 0) := by
  unfold Stage.entries stageCounts
  cases s.call f with
  | none => rfl
  | some k =>
    obtain ⟨lead, vs, ends⟩ := k
    cases ends <;>
      simp [VerifiableInference.Desc.Part.MaskedSum.entries,
        VerifiableInference.Desc.Part.MaskedSum.entry, scalarsOf, cutOf, Function.comp_def]

theorem fits_of_sends {C : Type} : ∀ (ns : List Nat) (ms : List (Move C W Unit))
    (es : List Fmt.Entry), AllTwo Sends ns ms → es.map cutOf = ns.map (fun n => (24 * n, 0, 0)) →
    AllTwo (fun (r : Fmt.DeclaredRound × List Oracle) (mv : Move C W Unit) =>
      ∀ (c : C) (sn : Seen) (u : State W Unit) (y : Sending), mv.say c sn u = .ok y →
        y.fits r.1 r.2 = true) (es.map fun e => (declOf e, ([] : List Oracle))) ms
  | [], [], [], _, _ => trivial
  | [], [], _ :: _, _, h => by simp at h
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim
  | _ :: _, _ :: _, [], _, h => by simp at h
  | n :: ns, mv :: ms, e :: es, h, he => by
    simp only [List.map_cons, List.cons.injEq, cutOf, Prod.mk.injEq] at he
    refine ⟨fun c sn u y hy => ?_, fits_of_sends ns ms es h.2 he.2⟩
    obtain ⟨l, hl, hn⟩ := h.1 c sn u
    rw [hl] at hy
    obtain rfl := Except.ok.inj hy
    exact fits_sayE l e (by rw [hn]; exact he.1.1) he.1.2.1 he.1.2.2

theorem row_fits : ∀ (l : List (Stage × Nat)) (es : List Fmt.Entry) (c : RowCoins (rowOf R V l)),
    es.map cutOf = (l.flatMap fun x => Stage.entries R.a.face x.1).map cutOf →
    RowFits (rowOf R V l) (es.map fun e => (declOf e, ([] : List Oracle))) c
  | [], es, _, h => by
    have : es = [] := by simpa using h
    subst this
    rfl
  | x :: l, es, c, h => by
    let c' : (partOf (V := V) Rd R.J R.a x.1 x.2).Coins × RowCoins (rowOf R V l) := c
    have hm : (partOf (V := V) Rd R.J R.a x.1 x.2).moves.length = x.1.rounds R.a.face :=
      partOf_moves _ _ _ _ _
    have hn : ((Stage.entries R.a.face x.1).map cutOf).length = x.1.rounds R.a.face := by
      rw [List.length_map, entries_length]
    rw [List.flatMap_cons, List.map_append] at h
    have h1 : (es.take (x.1.rounds R.a.face)).map cutOf =
        (Stage.entries R.a.face x.1).map cutOf := by
      rw [List.map_take, h, ← hn, List.take_left']
      rfl
    have h2 : (es.drop (x.1.rounds R.a.face)).map cutOf =
        (l.flatMap fun x => Stage.entries R.a.face x.1).map cutOf := by
      rw [List.map_drop, h, ← hn, List.drop_left']
      rfl
    have hlen : x.1.rounds R.a.face ≤ es.length := by
      have := congrArg List.length h
      simp only [List.length_map, List.length_append] at this hn
      omega
    show (partOf (V := V) Rd R.J R.a x.1 x.2).moves.length ≤
        (es.map fun e => (declOf e, ([] : List Oracle))).length ∧
      (∀ r ∈ ((es.map fun e => (declOf e, ([] : List Oracle))).take
          (partOf (V := V) Rd R.J R.a x.1 x.2).moves.length).zip
          (partOf (V := V) Rd R.J R.a x.1 x.2).moves,
        ∀ (sn : Seen) (u : State W Unit) (y : Sending), r.2.say c'.1 sn u = .ok y →
          y.fits r.1.1 r.1.2 = true) ∧
      RowFits (rowOf R V l) ((es.map fun e => (declOf e, ([] : List Oracle))).drop
        (partOf (V := V) Rd R.J R.a x.1 x.2).moves.length) c'.2
    rw [hm, ← List.map_take, ← List.map_drop]
    refine ⟨by simpa using hlen, fun r hr sn u y hy => ?_, row_fits l _ c'.2 h2⟩
    exact allTwo_zip (fits_of_sends _ _ _ (part_sends R x) (h1.trans (entries_cut _ _))) r hr
      c'.1 sn u y hy

theorem aloneRow_some : ∀ (l : List (Stage × Nat)) (c : RowCoins (rowOf R V l)) (t : State W Unit)
    (seen : Seen) (ds : List Fmt.Drawn),
    ds.length = (l.map fun x => x.1.rounds R.a.face).sum →
    ∃ y, aloneRow (rowOf R V l) c t seen ds = some y
  | [], _, _, _, [], _ => ⟨[], rfl⟩
  | [], _, _, _, _ :: _, h => by simp at h
  | x :: l, c, t, seen, ds, h => by
    let c' : (partOf (V := V) Rd R.J R.a x.1 x.2).Coins × RowCoins (rowOf R V l) := c
    have hm : (partOf (V := V) Rd R.J R.a x.1 x.2).moves.length = x.1.rounds R.a.face :=
      partOf_moves _ _ _ _ _
    simp only [List.map_cons, List.sum_cons] at h
    obtain ⟨y₁, hy₁⟩ := aloneFrom_some c'.1 (partOf (V := V) Rd R.J R.a x.1 x.2).moves t seen
      (ds.take (partOf (V := V) Rd R.J R.a x.1 x.2).moves.length)
      (fun mv hmv sn u => by
        obtain ⟨l', hl', _⟩ := allTwo_right (Q := fun mv => ∀ c sn u, ∃ l' : List E,
          mv.say c sn u = .ok (sayE l') ∧ True) (fun n b hb c sn u => by
            obtain ⟨l', h1, _⟩ := hb c sn u
            exact ⟨l', h1, trivial⟩) (part_sends R x) mv hmv c'.1 sn u
        exact ⟨_, hl'⟩)
      (by rw [List.length_take, hm]; omega)
    obtain ⟨y₂, hy₂⟩ := aloneRow_some l c'.2
      (endFrom (partOf (V := V) Rd R.J R.a x.1 x.2).moves t
        (ds.take (partOf (V := V) Rd R.J R.a x.1 x.2).moves.length)) (seen.plus y₁)
      (ds.drop (partOf (V := V) Rd R.J R.a x.1 x.2).moves.length)
      (by rw [List.length_drop, hm]; omega)
    refine ⟨y₁ ++ y₂, ?_⟩
    show (alone (partOf (V := V) Rd R.J R.a x.1 x.2) c'.1 t seen
        (ds.take (partOf (V := V) Rd R.J R.a x.1 x.2).moves.length)).bind (fun y =>
          (aloneRow (rowOf R V l) c'.2 (endFrom (partOf (V := V) Rd R.J R.a x.1 x.2).moves t
            (ds.take (partOf (V := V) Rd R.J R.a x.1 x.2).moves.length)) (seen.plus y)
            (ds.drop (partOf (V := V) Rd R.J R.a x.1 x.2).moves.length)).map (y ++ ·)) = _
    have hy₁' : alone (partOf (V := V) Rd R.J R.a x.1 x.2) c'.1 t seen
        (ds.take (partOf (V := V) Rd R.J R.a x.1 x.2).moves.length) = some y₁ := hy₁
    rw [hy₁']
    show (aloneRow (rowOf R V l) c'.2 _ (seen.plus y₁) _).map (y₁ ++ ·) = _
    rw [hy₂]
    rfl

theorem endRow_unit : ∀ (l : List (Stage × Nat)) (t : State W Unit) (ds : List Fmt.Drawn),
    ds.length = (l.map fun x => x.1.rounds R.a.face).sum →
    endRow (rowOf R V l) t ds = { t with heard := t.heard ++ ds }
  | [], t, [], _ => by simp [endRow]
  | [], _, _ :: _, h => by simp at h
  | x :: l, t, ds, h => by
    have hm : (partOf (V := V) Rd R.J R.a x.1 x.2).moves.length = x.1.rounds R.a.face :=
      partOf_moves _ _ _ _ _
    simp only [List.map_cons, List.sum_cons] at h
    show endRow (rowOf R V l) (endFrom (partOf (V := V) Rd R.J R.a x.1 x.2).moves t
      (ds.take (partOf (V := V) Rd R.J R.a x.1 x.2).moves.length))
      (ds.drop (partOf (V := V) Rd R.J R.a x.1 x.2).moves.length) = _
    rw [endFrom_unit _ t _ (by rw [List.length_take]; omega),
      endRow_unit l _ _ (by rw [List.length_drop, hm]; omega)]
    simp [List.append_assoc]

/-! ## 5 The coins -/

/-- Where the course's coins are a row's, read by number: part by part they agree. -/
theorem coinsRow_of_read (g : Nat → Nat → Nat → Cb.Gl.E) (hR : ∀ s, R.c s = courseCoins R.a g s) :
    ∀ (ss : List Stage) (off : Nat) (c : RowCoins (rowOf R V (ss.zipIdx off))),
    (∀ j, j < ss.length → g (off + j) = rowRead _ c j) →
    (∀ j (h : j < ss.length), indexOf R.a.face ss[j] = off + j) →
    CoinsRow R (ss.zipIdx off) c
  | [], _, _, _, _ => trivial
  | s :: ss, off, c, hg, hi => by
    let c' : (partOf (V := V) Rd R.J R.a s off).Coins ×
      RowCoins (rowOf R V (ss.zipIdx (off + 1))) := c
    show CoinsAt R (s, off) c'.1 ∧ CoinsRow R (ss.zipIdx (off + 1)) c'.2
    refine ⟨fun hsome => ?_, coinsRow_of_read g hR ss (off + 1) c'.2 (fun j hj => ?_)
      (fun j hj => ?_)⟩
    · obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hsome
      have hk' : s.call R.a.face = some k := hk
      have h0 : g (indexOf R.a.face s) = readRuns _ c'.1.2.1 := by
        have e := hi 0 (by simp)
        simp only [List.getElem_cons_zero, Nat.add_zero] at e
        rw [e]
        exact hg 0 (by simp)
      show csAllE _ c'.1.2.1 = csAllE _ (R.c s).2.1
      rw [hR]
      show csAllE _ c'.1.2.1 = csAllE _ (fillRuns (runsOf (sumName R.a.place (indexOf R.a.face s))
        (endName R.a.place (indexOf R.a.face s)) (shapeAt R.a s)) (g (indexOf R.a.face s)))
      rw [h0]
      refine (csAllE_fill _ _ _ ?_).symm
      rw [shapeAt_some R.a s k hk', partOf_some R.J R.a s off k hk']
      exact runsOf_counts _ _ _ _ k
    · rw [show off + 1 + j = off + (j + 1) by omega]
      exact hg (j + 1) (by simpa using hj)
    · have e := hi (j + 1) (by simpa using hj)
      simp only [List.getElem_cons_succ] at e
      omega

theorem spent_of_coins : ∀ (l : List (Stage × Nat)) (c : RowCoins (rowOf R V l)), CoinsRow R l c →
    ∀ j (h : j < l.length), (l[j].1.call R.a.face).isSome = true →
      (rowSpent (rowOf R V l) c).getD j [] = csAllE _ (R.c l[j].1).2.1
  | [], _, _, _, h, _ => by simp at h
  | x :: l, c, hc, 0, _, hs => by
    let c' : (partOf (V := V) Rd R.J R.a x.1 x.2).Coins × RowCoins (rowOf R V l) := c
    have h' : CoinsAt R x c'.1 ∧ CoinsRow R l c'.2 := hc
    show (csAllE _ c'.1.2.1 :: rowSpent (rowOf R V l) c'.2).getD 0 [] = _
    exact h'.1 hs
  | x :: l, c, hc, j + 1, h, hs => by
    let c' : (partOf (V := V) Rd R.J R.a x.1 x.2).Coins × RowCoins (rowOf R V l) := c
    have h' : CoinsAt R x c'.1 ∧ CoinsRow R l c'.2 := hc
    show (csAllE _ c'.1.2.1 :: rowSpent (rowOf R V l) c'.2).getD (j + 1) [] = _
    rw [List.getD_cons_succ]
    exact spent_of_coins l c'.2 h'.2 j (by simpa using h) hs

theorem tail_zero_iff (a : At) (s : Stage) (k : Call) (hk : s.call a.face = some k) :
    (shapeAt a s).ends.isNone = true ↔ s.tail a.face = 0 := by
  rw [shapeAt_some a s k hk]
  unfold Stage.tail
  rw [hk]
  cases he : k.ends with
  | none => simp [he]
  | some e =>
    have := stage_ends_ne a.face s k hk e he
    simp [he, this]

/-- **The row's coins are the course's**, in the statement's own form. -/
theorem coinsAre (c : RowCoins (lookRow (V := V) Rd R.J R.a))
    (hc : CoinsRow R ((stages R.a.face).zipIdx) c) : CoinsAre R c := by
  intro s hs hsome
  have hj : indexOf R.a.face s < (stages R.a.face).length := List.idxOf_lt_length_iff.2 hs
  have hj' : indexOf R.a.face s < ((stages R.a.face).zipIdx).length := by simpa using hj
  have hget : ((stages R.a.face).zipIdx)[indexOf R.a.face s]'hj' = (s, indexOf R.a.face s) := by
    simp [List.getElem_zipIdx, indexOf]
  have key : ∀ (x : Stage × Nat), x = (s, indexOf R.a.face s) →
      (x.1.call R.a.face).isSome = true ∧
      ((rowSpent (rowOf R V ((stages R.a.face).zipIdx)) c).getD (indexOf R.a.face s) [] =
        csAllE _ (R.c x.1).2.1 →
      (rowSpent (rowOf R V ((stages R.a.face).zipIdx)) c).getD (indexOf R.a.face s) [] =
        csAllE _ (R.c s).2.1) := by
    intro x hx
    subst hx
    exact ⟨hsome, id⟩
  have hk0 := key _ hget
  have hsp := hk0.2 (spent_of_coins R _ c hc (indexOf R.a.face s) hj' hk0.1)
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hsome
  have hcond := tail_zero_iff R.a s k hk
  refine hsp.trans ?_
  have hruns := csAllE_runs (sumName R.a.place (indexOf R.a.face s))
    (endName R.a.place (indexOf R.a.face s)) (shapeAt R.a s) (R.c s).2.1
  refine hruns.trans ?_
  by_cases h0 : s.tail R.a.face = 0
  · rw [if_pos (hcond.2 h0), if_pos h0]
    rfl
  · rw [if_neg (fun h => h0 (hcond.1 h)), if_neg h0]
    rfl

/-! ## 6 The statement -/

theorem drawsFit_length : ∀ (A : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    drawsFit A Rs = true → Rs.length = A.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [drawsFit] at h
  | _ :: _, [], h => by simp [drawsFit] at h
  | _ :: A, _ :: Rs, h => by
    simp only [drawsFit, Bool.and_eq_true] at h
    simp [drawsFit_length A Rs h.2]

/-- **The statement `RowPlays` (Honest/K3/Law/Statements.lean), in full**: for all stored rounds to
fall back on (no round of the row falls back on one); with all that the player leaves behind the
row: the state, the challenges that stops may read, the rounds shown, the columns opened as they
stood in front; and with what each played round bears: the lookup's place, that a half made it, no
table. A lemma's statement, none of the library's goals. -/
def RowPlaysFull : Prop :=
  ∀ (V W : Type) (R : Course W) (name : String) (v : Option V) (es : List Fmt.Entry)
    (loc : List Fmt.Drawn) (c : RowCoins (lookRow (V := V) ⟨ptsOf, pointsAt⟩ R.J R.a)),
    ∃ c' : (s : Stage) → StageCoins R.a s, CoinsAre { R with c := c' } c ∧
      (Fit R → entriesFit R.f es = true → ∀ back : List Fmt.RoundView,
        ∃ y x, play (rowSteps name R.a.place v (lookRow ⟨ptsOf, pointsAt⟩ R.J R.a) 0
              (es.map fun e => (declOf e, ([] : List Oracle))) c) R.ds back
              ⟨R.t, loc, R.seen.rounds, R.seen.opened⟩ = .ok y ∧
          ({ R with c := c' } : Course W).rounds = some x ∧ roundsOf y.1 = x ∧
          y.2 = ⟨{ R.t with heard := R.t.heard ++ R.ds }, loc ++ R.ds, R.seen.rounds ++ x,
            R.seen.opened⟩ ∧
          ∀ q ∈ y.1, q.place = R.a.place ∧ q.told = true ∧ q.tables = [])

/-- **The proof of `RowPlaysFull`.** -/
theorem rowPlaysFull : RowPlaysFull := by
  intro V W R name v es loc c
  let g := rowRead _ c
  let R' : Course W := { R with c := courseCoins R.a g }
  have hc : CoinsRow R' ((stages R.a.face).zipIdx) c :=
    coinsRow_of_read R' g (fun _ => rfl) (stages R.a.face) 0 c
      (fun j _ => by rw [Nat.zero_add]; rfl)
      (fun j hj => by simpa using indexOf_getElem R.a.face j hj)
  refine ⟨courseCoins R.a g, coinsAre R' c hc, fun hfit hes back => ?_⟩
  have h2 := two_le_planes_of_ok _ hfit.ok
  have hlen : R.ds.length = (((stages R.a.face).zipIdx).map fun x => x.1.rounds R.a.face).sum := by
    rw [drawsFit_length _ _ hfit.draws, List.length_map,
      map_zipIdx_fst (fun s => Stage.rounds R.a.face s), rounds_stages _ h2]
  obtain ⟨x, hx⟩ := aloneRow_some R' ((stages R.a.face).zipIdx) c R.t R.seen R.ds hlen
  have hcut : es.map cutOf =
      (((stages R.a.face).zipIdx).flatMap fun x => Stage.entries R.a.face x.1).map cutOf := by
    rw [flatMap_zipIdx_fst (Stage.entries R.a.face), entries_stages _ h2]
    have e : (es.map fun e => { e with work := 0 }) = entriesV R.a.face := eq_of_beq hes
    rw [← e, List.map_map]
    rfl
  obtain ⟨y, hy, hy1, hy2⟩ := play_row name R.a.place v _ 0 _ c R.ds back R.t loc R.seen x
    (row_noStops R' _) (row_fits R' _ es c hcut) hx
  refine ⟨y, x, hy, ?_, hy1, ?_, played_row name R.a.place v _ 0 _ c R.ds back _ y hy
    (fun r hr => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.1 hr
      rfl)⟩
  · show R'.run (stages R.a.face) R.t R.seen R.ds = some x
    rw [← hx, aloneRow_run R' _ c _ _ _ hc, map_zipIdx_fst (fun s => s), List.map_id']
  · have he : endRow (lookRow (V := V) Rd R.J R.a) R.t R.ds =
        { R.t with heard := R.t.heard ++ R.ds } := endRow_unit R' _ _ _ hlen
    rw [hy2, he]

/-- **The proof of `RowPlays`**: the case of `RowPlaysFull` with nothing to fall back on. -/
theorem rowPlays : RowPlays := by
  intro V W R name v es loc c
  obtain ⟨c', h1, h2⟩ := rowPlaysFull V W R name v es loc c
  refine ⟨c', h1, fun hf he => ?_⟩
  obtain ⟨y, x, a, b, d, e, _⟩ := h2 hf he []
  exact ⟨y, x, a, b, d, by rw [e]⟩

/-! ## 7 All stages of a course answer -/

theorem stage_some (s : Stage) (t : State W Unit) (seen : Seen) (ds : List Fmt.Drawn)
    (h : ds.length = s.rounds R.a.face) :
    ∃ y, R.stage s t seen ds = some y ∧ y.length = s.rounds R.a.face := by
  cases hk : s.call R.a.face with
  | none =>
    have h1 : s.rounds R.a.face = 1 := by simp [Stage.rounds, hk]
    rw [h1] at h ⊢
    obtain ⟨d, rfl⟩ := List.length_eq_one_iff.1 h
    exact ⟨[⟨[], d⟩], by simp only [Course.stage, hk], rfl⟩
  | some k =>
    have hs := shapeAt_some R.a s k hk
    have hm : (sumPart (V := Unit) (sumName R.a.place (indexOf R.a.face s))
        (endName R.a.place (indexOf R.a.face s)) (R.job s)).moves.length = s.rounds R.a.face := by
      rw [sumPart_moves]
      show VerifiableInference.Desc.K3.roundsOf (shapeAt R.a s) = _
      rw [hs]
      simp [Stage.rounds, hk]
    have hv : ∀ v ∈ (R.job s).shape.vs, v.d ≠ 1 := by
      show ∀ v ∈ (shapeAt R.a s).vs, v.d ≠ 1
      rw [hs]
      exact stage_vars R.a.face s k hk
    obtain ⟨y, hy⟩ := aloneFrom_some (R.c s) (sumPart (V := Unit)
      (sumName R.a.place (indexOf R.a.face s)) (endName R.a.place (indexOf R.a.face s))
      (R.job s)).moves t seen ds
      (fun mv hmv sn u => by
        obtain ⟨l', hl', _⟩ := allTwo_right (Q := fun mv => ∀ c sn u, ∃ l' : List E,
          mv.say c sn u = .ok (sayE l') ∧ True) (fun n b hb c sn u => by
            obtain ⟨l', h1, _⟩ := hb c sn u
            exact ⟨l', h1, trivial⟩) (sumPart_sends (V := Unit) _ _ (R.job s) hv) mv hmv (R.c s)
          sn u
        exact ⟨_, hl'⟩)
      (h.trans hm.symm)
    refine ⟨y, ?_, ?_⟩
    · simp only [Course.stage, hk]
      exact hy
    · exact (aloneFrom_length _ _ _ _ _ y hy).2.trans hm

theorem run_some : ∀ (l : List Stage) (t : State W Unit) (seen : Seen)
    (ds : List Fmt.Drawn), ds.length = (l.map (Stage.rounds R.a.face)).sum →
    ∃ x, R.run l t seen ds = some x ∧ x.length = (l.map (Stage.rounds R.a.face)).sum
  | [], _, _, [], _ => ⟨[], rfl, rfl⟩
  | [], _, _, _ :: _, h => by simp at h
  | s :: l, t, seen, ds, h => by
    simp only [List.map_cons, List.sum_cons] at h ⊢
    obtain ⟨y, hy, hyl⟩ := stage_some R s t seen (ds.take (s.rounds R.a.face))
      (by rw [List.length_take]; omega)
    obtain ⟨x, hx, hxl⟩ := run_some l { t with heard := t.heard ++ ds.take (s.rounds R.a.face) }
      (seen.plus y) (ds.drop (s.rounds R.a.face)) (by rw [List.length_drop]; omega)
    refine ⟨y ++ x, ?_, by rw [List.length_append, hyl, hxl]⟩
    show (R.stage s t seen (ds.take (s.rounds R.a.face))).bind (fun y =>
      (R.run l { t with heard := t.heard ++ ds.take (s.rounds R.a.face) } (seen.plus y)
        (ds.drop (s.rounds R.a.face))).map (y ++ ·)) = _
    rw [hy]
    show (R.run l _ (seen.plus y) _).map (y ++ ·) = _
    rw [hx]
    rfl

/-- **The proof of `CourseSays`.** -/
theorem courseSays : CourseSays := by
  intro W R hfit
  have h2 := two_le_planes_of_ok _ hfit.ok
  have hlen : R.ds.length = ((stages R.a.face).map (Stage.rounds R.a.face)).sum := by
    rw [drawsFit_length _ _ hfit.draws, List.length_map, rounds_stages _ h2]
  obtain ⟨x, hx, hxl⟩ := run_some R (stages R.a.face) R.t R.seen R.ds hlen
  exact ⟨x, hx, by rw [hxl, rounds_stages _ h2]⟩

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.courseSays
#print axioms ProofFile.Honest.K3.Law.stage_eq
#print axioms ProofFile.Honest.K3.Law.aloneRow_run
#print axioms ProofFile.Honest.K3.Law.row_fits
#print axioms ProofFile.Honest.K3.Law.coinsAre
#print axioms ProofFile.Honest.K3.Law.rowPlaysFull
#print axioms ProofFile.Honest.K3.Law.rowPlays
#print axioms ProofFile.Honest.K3.Law.coinsE_fill
#print axioms ProofFile.Honest.K3.Law.csAllE_fill
#print axioms ProofFile.Honest.K3.Law.stage_vars
#print axioms ProofFile.Honest.K3.Law.stage_ends_ne
#print axioms ProofFile.Honest.K3.Law.partOf_some
#print axioms ProofFile.Honest.K3.Law.partOf_none
#print axioms ProofFile.Honest.K3.Law.shapeAt_some
#print axioms ProofFile.Honest.K3.Law.runsOf_counts
#print axioms ProofFile.Honest.K3.Law.csAllE_runs
#print axioms ProofFile.Honest.K3.Law.runs_of_csAllE
#print axioms ProofFile.Honest.K3.Law.alone_quiet
#print axioms ProofFile.Honest.K3.Law.part_noStops
#print axioms ProofFile.Honest.K3.Law.row_noStops
#print axioms ProofFile.Honest.K3.Law.part_sends
#print axioms ProofFile.Honest.K3.Law.entries_cut
#print axioms ProofFile.Honest.K3.Law.fits_of_sends
#print axioms ProofFile.Honest.K3.Law.aloneRow_some
#print axioms ProofFile.Honest.K3.Law.endRow_unit
#print axioms ProofFile.Honest.K3.Law.coinsRow_of_read
#print axioms ProofFile.Honest.K3.Law.spent_of_coins
#print axioms ProofFile.Honest.K3.Law.tail_zero_iff
#print axioms ProofFile.Honest.K3.Law.drawsFit_length
#print axioms ProofFile.Honest.K3.Law.stage_some
#print axioms ProofFile.Honest.K3.Law.run_some
