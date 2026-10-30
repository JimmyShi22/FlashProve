-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/SaidRow.lean: A ROW OF PARTS WHOSE MOVES SAY SCALARS AND WHOSE
STOPS NEVER STOP, each lifted to a wider input: what the frame's `play` returns on the row's Steps:
the whole list; and that list part by part. Definitions with code, and statements with their proofs.

What it is not. Nothing is said of the VALUES that are said: `sayOut` names them. `Sayer.Ok` is a
premise's form: this file shows it of no part. GENERAL in the parts only as far as they see nothing
and hand on nothing (`Part Unit W' Unit`), each lifted by a reader of the input alone; general in
the place, the step's name and that reader: no letter of any sub-protocol stands in it. Nothing is
claimed on soundness, completeness or hiding.

  1  `Sayer`, `Sayer.Ok`, `sayParts`, `sayOut`   a part at a small input with what its moves say and
     how many scalars each says; what is asked of it; the parts, lifted; the rounds as played
  2  `sayRow_plays`, `sayOut_tables`   **the row's Steps play: the whole list**,
     CONDITIONAL on `Sayer.Ok` of each part, on what the declared rounds state and on the number of
     challenges; no round holds a table
  3  `sayFront`, `sayCoin`, `sayPieces`, `sayOut_rounds`, `sayPieces_at`, `sayCoin_fst`   **the
     list, part by part**: the rounds of part number i as a term of its share of the coins, of the
     state that has heard the challenges in front of it, of what has been shown in front of it, and
     of its share of the challenges
  4  `outOf_length`, `outOf_drawn`, `outOf_one`, `sayFront_succ`, `sayFront_le`, `sayShare_length`,
     `Sayer.Ok.alone`, `sayParts_moves`   counts; and: played alone, such a part says these rounds

What is called. One step of the row is `plays_lift_said` (Honest/Small/Plays.lean); the row's Steps
are cut by `rowSteps_cons`, the declared rounds by `statedBy_split`, and counted by
`statedBy_length` (Honest/Small/Stated.lean); the frame's `play_append`, `tablesOf_append`; of the
masked sumcheck's law `steps_length`, `roundsOf_said`, `tablesOf_said`, `aloneFrom_mvOf`. `sayOut`,
`sayRow_plays` with its proof and `sayOut_tables` follow the like on the attention segment's own row
(Honest/K5/Law/Plays.lean, which is not in the library: `rowOut`, `rowOf_plays`, `rowOut_tables`)
line for line, with that row's parts turned into letters. Typed here: `Sayer` and `Sayer.Ok`, and
the cut into pieces (3, 4).
-/
import Johnson.Desc.ProofFile.Honest.Small.Stated
import Johnson.Desc.ProofFile.Honest.Small.Plays
import Johnson.Desc.ProofFile.Honest.Law.Cut
import Johnson.Desc.ProofFile.Honest.Law.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open OnBytes (E)
open VerifiableInference.Desc (Place Oracle)
open ProofFile.Honest.SumLaw

variable {V W W' X : Type}

/-- A part at a small input, with what its moves say and how many scalars each says. -/
structure Sayer (W' : Type) where
  part : Part Unit W' Unit
  gs : List (part.Coins → Seen → State W' Unit → List E)
  ns : List Nat

/-- The part's stops never stop; its moves say just `gs` and hand on what they were handed; there
are as many as `ns` has members, and the lists have the lengths `ns`. -/
structure Sayer.Ok (s : Sayer W') : Prop where
  bad : ∀ f o, s.part.bad f o = none
  hid : ∀ w f o, s.part.hid w f o = none
  moves : s.part.moves = s.gs.map mvOf
  count : s.gs.length = s.ns.length
  lens : ∀ c, LensBy s.ns (s.gs.map (· c))

/-- The parts, each lifted to the wider input and state. -/
def sayParts (wit : W → W') (l : List (Sayer W')) : List (Part V W X) :=
  l.map fun s => s.part.lift (fun _ => ()) wit (fun _ => ()) fun x _ => x

/-- **The rounds of the row as played**, part by part: what the part's moves say at its coins, from
the state and from what has been shown in front of it (`Seen`: the rounds, and the opened columns
where any are handed), at its share of the challenges; each round under the step's name, the place
and the part's number, without a table. From part to part the rounds grow and the columns stay
(`Seen.plus`). -/
def sayOut (nm : String) (a : Place) (wit : W → W') : (l : List (Sayer W')) → (j : Nat) →
    RowCoins (sayParts (V := V) (X := X) wit l) → State W X → Seen → List Fmt.Drawn →
    List Played
  | [], _, _, _, _, _ => []
  | s :: l, j, c, t, seen, ds =>
    let c' : s.part.Coins × RowCoins (sayParts (V := V) (X := X) wit l) := c
    (outOf (s.gs.map (· c'.1)) (t.narrow wit fun _ => ()) seen
        (ds.take s.ns.length)).map (saidPlayed nm ⟨a, j⟩) ++
      sayOut nm a wit l (j + 1) c'.2 ⟨t.input, t.heard ++ ds.take s.ns.length, t.own⟩
        (seen.plus
            (outOf (s.gs.map (· c'.1)) (t.narrow wit fun _ => ()) seen (ds.take s.ns.length)))
        (ds.drop s.ns.length)

/-- **THE ROW's STEPS PLAY: THE WHOLE LIST.** Conditional: each part is as `Sayer.Ok` says; the
declared rounds state the parts' scalars and no oracle message; there are as many challenges as
rounds. -/
theorem sayRow_plays (nm : String) (a : Place) (wit : W → W') (v : Option V) :
    ∀ (l : List (Sayer W')) (j : Nat) (c : RowCoins (sayParts (V := V) (X := X) wit l))
      (rs : List (Fmt.DeclaredRound × List Oracle)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
      (m : Mid W X), (∀ s ∈ l, s.Ok) → StatedBy (l.flatMap (·.ns)) rs →
      ds.length = (l.flatMap (·.ns)).length →
      play (rowSteps nm a v (sayParts wit l) j rs c) ds back m =
        .ok (sayOut nm a wit l j c m.st m.shown ds,
          ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
            m.seen ++ roundsOf (sayOut nm a wit l j c m.st m.shown ds), m.opened⟩)
  | [], _, _, _, [], _, m, _, _, _ => by
    show Except.ok ([], m) = Except.ok ([], (⟨⟨m.st.input, m.st.heard ++ [], m.st.own⟩,
      m.loc ++ [], m.seen ++ [], m.opened⟩ : Mid W X))
    rw [List.append_nil, List.append_nil, List.append_nil]
  | [], _, _, _, _ :: _, _, _, _, _, hl => by cases hl
  | s :: l, j, c, rs, ds, back, m, h2, hr, hl => by
    rw [List.flatMap_cons] at hr hl
    obtain ⟨hr1, hr2⟩ := statedBy_split _ _ rs hr
    rw [List.length_append] at hl
    have hk : s.Ok := h2 s List.mem_cons_self
    have hmv : (s.part.lift (V := V) (X := X) (fun _ => ()) wit (fun _ => ())
        fun x _ => x).moves.length = s.ns.length := by
      show (s.part.moves.map _).length = _
      rw [List.length_map, hk.moves, List.length_map, hk.count]
    have ht : (ds.take s.ns.length).length = s.ns.length := by
      rw [List.length_take]
      omega
    have hd : (ds.drop s.ns.length).length = (l.flatMap (·.ns)).length := by
      rw [List.length_drop]
      omega
    have h1 := plays_lift_said (V := V) (X := X) (fun _ => ()) wit (fun _ => ()) (fun x _ => x)
      (fun _ => rfl) s.part hk.bad hk.hid s.gs hk.moves s.ns c.1 (hk.lens c.1) nm ⟨a, j⟩
      (rs.take s.ns.length) hr1 v (ds.take s.ns.length) ht back m
    have hs : ((s.part.lift (V := V) (X := X) (fun _ => ()) wit (fun _ => ())
        fun x _ => x).steps nm ⟨a, j⟩ (rs.take s.ns.length) v c.1).length = s.ns.length := by
      rw [steps_length, statedBy_length _ _ hr1, hmv, Nat.min_self]
    have e := rowSteps_cons nm a v (s.part.lift (V := V) (X := X) (fun _ => ()) wit (fun _ => ())
      fun x _ => x) (sayParts wit l) j rs c
    rw [hmv] at e
    have h3 := fun bk => sayRow_plays nm a wit v l (j + 1) c.2 (rs.drop s.ns.length)
      (ds.drop s.ns.length) bk
      ⟨⟨m.st.input, m.st.heard ++ ds.take s.ns.length, m.st.own⟩, m.loc ++ ds.take s.ns.length,
        m.seen ++ outOf (s.gs.map (· c.1)) (m.st.narrow wit fun _ => ()) m.shown
          (ds.take s.ns.length), m.opened⟩
      (fun x hx => h2 x (List.mem_cons_of_mem _ hx)) hr2 hd
    have er : ∀ (O : List Fmt.RoundView) (R : List Played),
        roundsOf (O.map (saidPlayed nm ⟨a, j⟩) ++ R) = O ++ roundsOf R := by
      intro O R
      show (O.map (saidPlayed nm ⟨a, j⟩) ++ R).map _ = _
      rw [List.map_append]
      exact congrArg (· ++ roundsOf R) (roundsOf_said nm ⟨a, j⟩ O)
    refine (congrArg (fun L => play L ds back m) e).trans ?_
    have ed : play ((s.part.lift (V := V) (X := X) (fun _ => ()) wit (fun _ => ())
          fun x _ => x).steps nm ⟨a, j⟩ (rs.take s.ns.length) v c.1 ++
        rowSteps nm a v (sayParts wit l) (j + 1) (rs.drop s.ns.length) c.2)
        (ds.take s.ns.length ++ ds.drop s.ns.length) back m = _ :=
      play_append _ _ _ _ back m (ht.trans hs.symm)
    rw [List.take_append_drop] at ed
    refine ed.trans ?_
    rw [h1]
    show ((play _ _ _ _).map fun z => _) = _
    rw [h3]
    show Except.ok _ = Except.ok _
    refine congrArg Except.ok ?_
    show (_, _) = (_ ++ _, (⟨_, _, m.seen ++ roundsOf (_ ++ _), m.opened⟩ : Mid W X))
    rw [er]
    simp only [List.append_assoc, List.take_append_drop]
    rfl

/-- **No round of the row holds a table.** No premise. -/
theorem sayOut_tables (nm : String) (a : Place) (wit : W → W') :
    ∀ (l : List (Sayer W')) (j : Nat) (c : RowCoins (sayParts (V := V) (X := X) wit l))
      (t : State W X) (seen : Seen) (ds : List Fmt.Drawn),
      tablesOf (sayOut nm a wit l j c t seen ds) = []
  | [], _, _, _, _, _ => rfl
  | s :: l, j, c, t, seen, ds => by
    show tablesOf (_ ++ _) = []
    rw [tablesOf_append, tablesOf_said, sayOut_tables nm a wit l (j + 1)]
    rfl

/-! ## The list, part by part -/

/-- How many rounds stand in front of part number i. -/
def sayFront (l : List (Sayer W')) (i : Nat) : Nat := ((l.take i).flatMap (·.ns)).length

/-- Part number i, with its share of the row's coins. -/
def sayCoin (wit : W → W') : (l : List (Sayer W')) →
    RowCoins (sayParts (V := V) (X := X) wit l) → Nat → Option ((s : Sayer W') × s.part.Coins)
  | [], _, _ => none
  | s :: l, c, 0 =>
    let c' : s.part.Coins × RowCoins (sayParts (V := V) (X := X) wit l) := c
    some ⟨s, c'.1⟩
  | s :: l, c, i + 1 =>
    let c' : s.part.Coins × RowCoins (sayParts (V := V) (X := X) wit l) := c
    sayCoin wit l c'.2 i

/-- The rounds as a view shows them, part by part: `sayOut`'s recursion without the names. -/
def sayPieces (wit : W → W') : (l : List (Sayer W')) →
    RowCoins (sayParts (V := V) (X := X) wit l) → State W X → Seen → List Fmt.Drawn →
    List (List Fmt.RoundView)
  | [], _, _, _, _ => []
  | s :: l, c, t, seen, ds =>
    let c' : s.part.Coins × RowCoins (sayParts (V := V) (X := X) wit l) := c
    outOf (s.gs.map (· c'.1)) (t.narrow wit fun _ => ()) seen (ds.take s.ns.length) ::
      sayPieces wit l c'.2 ⟨t.input, t.heard ++ ds.take s.ns.length, t.own⟩
        (seen.plus
            (outOf (s.gs.map (· c'.1)) (t.narrow wit fun _ => ()) seen (ds.take s.ns.length)))
        (ds.drop s.ns.length)

/-- The rounds of the row as played are these pieces, one behind the other. No premise. -/
theorem sayOut_rounds (nm : String) (a : Place) (wit : W → W') :
    ∀ (l : List (Sayer W')) (j : Nat) (c : RowCoins (sayParts (V := V) (X := X) wit l))
      (t : State W X) (seen : Seen) (ds : List Fmt.Drawn),
      roundsOf (sayOut nm a wit l j c t seen ds) = (sayPieces wit l c t seen ds).flatten
  | [], _, _, _, _, _ => rfl
  | s :: l, j, c, t, seen, ds => by
    show (_ ++ _ : List Played).map _ = _ ++ _
    rw [List.map_append]
    exact congrArg₂ (· ++ ·) (roundsOf_said nm ⟨a, j⟩ _) (sayOut_rounds nm a wit l (j + 1) _ _ _ _)

/-- **THE ROUNDS OF PART NUMBER i**: what its moves say at its share of the coins, from the state
that has heard the challenges of the rounds in front of it, at what was shown in front of the row,
with the pieces in front of the part laid behind its rounds (`Seen.plus`: the opened columns are
those in front of the row), at its share of the challenges. CONDITIONAL on
`sayCoin wit l c i = some x`, which names x and fails from the list's length on. -/
theorem sayPieces_at (wit : W → W') :
    ∀ (l : List (Sayer W')) (c : RowCoins (sayParts (V := V) (X := X) wit l)) (t : State W X)
      (seen : Seen) (ds : List Fmt.Drawn) (i : Nat) (x : (s : Sayer W') × s.part.Coins),
      sayCoin wit l c i = some x →
      (sayPieces wit l c t seen ds)[i]? = some (outOf (x.1.gs.map (· x.2))
        ((⟨t.input, t.heard ++ ds.take (sayFront l i), t.own⟩ : State W X).narrow wit fun _ => ())
        (seen.plus (((sayPieces wit l c t seen ds).take i).flatten))
        ((ds.drop (sayFront l i)).take x.1.ns.length))
  | [], _, _, _, _, _, _, h => by cases h
  | s :: l, c, t, seen, ds, 0, x, h => by
    obtain rfl : (⟨s, c.1⟩ : (s : Sayer W') × s.part.Coins) = x := Option.some.inj h
    show some _ = some _
    simp [sayFront, Seen.plus_nil]
  | s :: l, c, t, seen, ds, i + 1, x, h => by
    have ih := sayPieces_at wit l c.2 ⟨t.input, t.heard ++ ds.take s.ns.length, t.own⟩
      (seen.plus (outOf (s.gs.map (· c.1)) (t.narrow wit fun _ => ()) seen (ds.take s.ns.length)))
      (ds.drop s.ns.length) i x h
    have hf : sayFront (s :: l) (i + 1) = s.ns.length + sayFront l i := by
      show ((s :: l.take i).flatMap (·.ns)).length = _
      rw [List.flatMap_cons, List.length_append]
      rfl
    show (sayPieces wit l c.2 _ _ _)[i]? = _
    rw [ih, hf, List.take_add, List.append_assoc, ← List.drop_drop]
    show some _ = some _
    simp [Seen.plus_plus]
    rfl

/-- The part that `sayCoin` names is the list's member number i. CONDITIONAL on
`sayCoin wit l c i = some x`, which fails from the list's length on. -/
theorem sayCoin_fst (wit : W → W') :
    ∀ (l : List (Sayer W')) (c : RowCoins (sayParts (V := V) (X := X) wit l)) (i : Nat)
      (x : (s : Sayer W') × s.part.Coins), sayCoin wit l c i = some x → l[i]? = some x.1
  | [], _, _, _, h => by cases h
  | s :: l, c, 0, x, h => by
    obtain rfl : (⟨s, c.1⟩ : (s : Sayer W') × s.part.Coins) = x := Option.some.inj h
    rfl
  | s :: l, c, i + 1, x, h => by
    show l[i]? = _
    exact sayCoin_fst wit l c.2 i x h

/-- As many rounds as challenges, where there are as many moves. -/
theorem outOf_length : ∀ (gs : List (Seen → State W X → List E)) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn), gs.length = ds.length →
    (outOf gs t seen ds).length = ds.length
  | [], _, _, [], _ => rfl
  | _ :: gs, _, _, _ :: ds, h => congrArg (· + 1) (outOf_length gs _ _ ds (Nat.succ.inj h))
  | [], _, _, _ :: _, h => by cases h
  | _ :: _, _, _, [], h => by cases h

/-- The rounds bear the challenges, in order, where there are as many moves. -/
theorem outOf_drawn : ∀ (gs : List (Seen → State W X → List E)) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn), gs.length = ds.length →
    (outOf gs t seen ds).map (·.drawn) = ds
  | [], _, _, [], _ => rfl
  | _ :: gs, _, _, d :: ds, h => congrArg (d :: ·) (outOf_drawn gs _ _ ds (Nat.succ.inj h))
  | [], _, _, _ :: _, h => by cases h
  | _ :: _, _, _, [], h => by cases h

/-- One move at one challenge: one round. -/
theorem outOf_one (g : Seen → State W X → List E) (t : State W X) (seen : Seen)
    (d : Fmt.Drawn) : outOf [g] t seen [d] = [rvSaid (g seen t) d] := rfl

/-- Behind part number i stand its rounds more. -/
theorem sayFront_succ (l : List (Sayer W')) (i : Nat) (s : Sayer W') (h : l[i]? = some s) :
    sayFront l (i + 1) = sayFront l i + s.ns.length := by
  unfold sayFront
  rw [List.take_add_one, h, List.flatMap_append, List.length_append]
  simp

/-- No more rounds stand in front of a part than the row has. -/
theorem sayFront_le (l : List (Sayer W')) (i : Nat) :
    sayFront l i ≤ (l.flatMap (·.ns)).length := by
  have e : (l.flatMap (·.ns)).length =
      ((l.take i).flatMap (·.ns)).length + ((l.drop i).flatMap (·.ns)).length := by
    rw [← List.length_append, ← List.flatMap_append, List.take_append_drop]
  unfold sayFront
  omega

/-- A part's share of the challenges has the part's number of rounds. Conditional: there are as many
challenges as the row has rounds. -/
theorem sayShare_length (l : List (Sayer W')) (i : Nat) (s : Sayer W') (h : l[i]? = some s)
    (ds : List Fmt.Drawn) (hl : ds.length = (l.flatMap (·.ns)).length) :
    ((ds.drop (sayFront l i)).take s.ns.length).length = s.ns.length := by
  have h1 := sayFront_succ l i s h
  have h2 := sayFront_le l (i + 1)
  rw [List.length_take, List.length_drop]
  omega

/-- **Played alone, such a part says these rounds.** Conditional: the part is as `Sayer.Ok` says;
there are as many challenges as it has rounds. -/
theorem Sayer.Ok.alone {s : Sayer W'} (h : s.Ok) (c : s.part.Coins) (t : State W' Unit)
    (seen : Seen) (ds : List Fmt.Drawn) (hl : ds.length = s.ns.length) :
    SumLaw.alone s.part c t seen ds = some (outOf (s.gs.map (· c)) t seen ds) := by
  show aloneFrom c s.part.moves t seen ds = _
  rw [h.moves]
  exact aloneFrom_mvOf c s.gs t seen ds (h.count.trans hl.symm)

/-- The row's numbers of moves, part by part. Conditional: each part is as `Sayer.Ok` says. -/
theorem sayParts_moves (wit : W → W') : ∀ (l : List (Sayer W')), (∀ s ∈ l, s.Ok) →
    (sayParts (V := V) (X := X) wit l).map (·.moves.length) = l.map (·.ns.length)
  | [], _ => rfl
  | s :: l, h => by
    show (s.part.moves.map _).length ::
      (sayParts (V := V) (X := X) wit l).map (·.moves.length) = _
    rw [List.length_map, (h s List.mem_cons_self).moves, List.length_map,
      (h s List.mem_cons_self).count,
      sayParts_moves wit l fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.sayRow_plays
#print axioms ProofFile.Honest.Small.sayOut_tables
#print axioms ProofFile.Honest.Small.sayOut_rounds
#print axioms ProofFile.Honest.Small.sayPieces_at
#print axioms ProofFile.Honest.Small.sayCoin_fst
#print axioms ProofFile.Honest.Small.outOf_length
#print axioms ProofFile.Honest.Small.outOf_drawn
#print axioms ProofFile.Honest.Small.outOf_one
#print axioms ProofFile.Honest.Small.sayFront_succ
#print axioms ProofFile.Honest.Small.sayFront_le
#print axioms ProofFile.Honest.Small.sayShare_length
#print axioms ProofFile.Honest.Small.Sayer.Ok.alone
#print axioms ProofFile.Honest.Small.sayParts_moves
#print axioms ProofFile.Honest.Small.Sayer
#print axioms ProofFile.Honest.Small.Sayer.Ok
#print axioms ProofFile.Honest.Small.sayParts
#print axioms ProofFile.Honest.Small.sayOut
#print axioms ProofFile.Honest.Small.sayFront
#print axioms ProofFile.Honest.Small.sayCoin
#print axioms ProofFile.Honest.Small.sayPieces
