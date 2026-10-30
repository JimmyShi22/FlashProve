-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Plays.lean: CONDITIONAL: the honest side of an attention
segment's own rounds (`k5Half`, Honest/K5/Row.lean) PLAYS at the member of a chain's `Thread` at
which it stands: the debt `Plays` of Honest/Thread/Pays.lean; with the whole list of rounds that the
frame's `play` returns; and these rounds fit the verifier's entries as its hearing reads them.
Definitions with code, and statements with their proofs. EVERY STATEMENT ON A MEMBER IS CONDITIONAL:
on `K5Seated` (Honest/K5/Law/Seated.lean).

  1  `partAt`, `rowOf_eq`, `saysAt`, `partAt_moves`, `saysAt_lens`, `partAt_bad`, `partAt_hid`   a
     part of the row (`rowOf`, Honest/K5/RowOf.lean) by its shape and number: its moves say scalars,
     as many as the shape counts, and its stops never stop
  2  `rowParts`, `rowOut`, `rowOf_plays`, `rowOut_tables`   **the row's steps play: the whole
     list**, general in the list of shapes, in the jobs, in the place, in the step's name and in
     the lift's reader of the input; no round holds a table
  3  `says_sum`, `says_quiet`, `says_scalars`   what a part's rounds are, sort by sort: a masked
     sumcheck's are `sumOut` (Honest/SumLaw/Out.lean)
  4  `k5Half_parts`, `k5Out`, `half_counts`, `k5_played`, `k5_cols`, `k5_fresh`, `k5_env`   at the
     member: what its Steps are and what `play` returns on them; it reads no column; no new tree is
     at hand behind it; the tables at hand stay as they are
     `partAt_count`, `rowParts_moves`, `half_cut`, `bookFits`, `k5_steps_return`   **`chainSteps`
     returns at the member**, under a test with code on the book and where `lendRow` lends
  5  `k5_plays`   **IT PLAYS**
  6  `scalars_of_items`, `fits_of_roundsFit`, `fits_of_played`   **the played rounds, without the
     sealed digest, fit the verifier's entries** (`Fits`, Johnson/Desc/Part/MaskedSumShape.lean)
  7  `digest_of_fit`, `noDigest_of_none`, `k5_bare`   **at this member, taking the sealed digest out
     of the played rounds changes nothing**: no challenge of theirs has one

Six names above or in the proofs stand for the laws of the same spelling in Honest/Small/Stated.lean
(one line `export`) and are no declarations here: `rowSteps_cons`, `half_counts`,
`scalars_of_items`, `fits_of_roundsFit`, `digest_of_fit`, `noDigest_of_none`.

What is spent. Of the sentence `Thr` in front nothing is read for `k5_plays`: these parts have no
stop, send no table and read no column, so they play from every stand. The lending of the coins is
a premise of `Plays` itself (`chainSteps … = .ok l`).

Limits. Nothing is said of the VALUES that are sent: `rowOut` names them, and no statement here
holds them against the verifier's claims. `K5Seated` is shown here of no description.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Seated
import Johnson.Desc.ProofFile.Honest.K5.Law.Shapes
import Johnson.Desc.ProofFile.Honest.K5.Law.Small
import Johnson.Desc.ProofFile.Honest.Small.Stated
import Johnson.Desc.ProofFile.Honest.Thread.Pays
import Johnson.Desc.ProofFile.Honest.Law.Cut
import Johnson.Desc.ProofFile.Honest.Law.Thread
import Johnson.Desc.ProofFile.Honest.Law.Run
import Johnson.Desc.Part.MaskedSumShape
import Johnson.Desc.First.Att.K05Seam

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E)
open VerifiableInference.Desc (Block Place Oracle OpenedColumn roundsFit noDigest itemOf)
open VerifiableInference.Desc.Part.MaskedSum (Call Fits scalars)
open VerifiableInference.Desc.First.Att.P (Par rounds)
open H2K5.Honest (PartShape shapes Chal)
open ProofFile.Honest.SumLaw

export ProofFile.Honest.Small (rowSteps_cons half_counts scalars_of_items fits_of_roundsFit digest_of_fit
  noDigest_of_none)

/-! ## 1 A part of the row -/

section Row
variable {V W W' X : Type}

/-- The part of the row at a shape and its number: the text of `rowOf`. -/
def partAt (a : Place) (chalOf : List Fmt.Drawn → Chal) (J : Jobs W') (s : PartShape × Nat) :
    Part Unit W' Unit :=
  match s.1 with
  | .sum k =>
    sumPart (nameOf a s.2 "sum") (nameOf a s.2 "ends")
      (jobOf k (fun w fr => J.alone s.2 w (chalOf fr.heard)) fun w fr =>
        J.sum s.2 w (chalOf fr.heard))
  | .one 0 => quietPart
  | .one n => scalarsPart (nameOf a s.2 "scalars") n fun w fr => J.alone s.2 w (chalOf fr.heard)

/-- The row is made of these. -/
theorem rowOf_eq (a : Place) (x : OnBytes.Params.AttentionRounds)
    (chalOf : List Fmt.Drawn → Chal) (J : Jobs W') :
    rowOf a x chalOf J = (shapes x).zipIdx.map (partAt a chalOf J) := rfl

/-- What the moves of that part say. -/
def saysAt (a : Place) (chalOf : List Fmt.Drawn → Chal) (J : Jobs W') :
    (s : PartShape × Nat) →
      List ((partAt a chalOf J s).Coins → Seen → State W' Unit → List E)
  | (.sum k, i) =>
    sumGs (nameOf a i "sum") (nameOf a i "ends")
      (jobOf k (fun w fr => J.alone i w (chalOf fr.heard)) fun w fr => J.sum i w (chalOf fr.heard))
  | (.one 0, _) => [fun _ _ _ => []]
  | (.one (n + 1), i) =>
    [fun (c : Handed ⟨0, 0⟩ [(nameOf a i "scalars", ⟨0, n + 1⟩)] []) seen t =>
      scalarsSaid (n + 1) (fun w fr => J.alone i w (chalOf fr.heard)) c.2.1.1 seen t]

/-- The part's moves say just that, and hand on what they were handed. -/
theorem partAt_moves (a : Place) (chalOf : List Fmt.Drawn → Chal) (J : Jobs W') :
    ∀ s : PartShape × Nat, (partAt a chalOf J s).moves = (saysAt a chalOf J s).map mvOf
  | (.sum _, _) => sumPart_moves _ _ _
  | (.one 0, _) => rfl
  | (.one (_ + 1), _) => rfl

/-- The lists have the shape's lengths. Conditional: every variable of a sumcheck has at least two
coefficients. -/
theorem saysAt_lens (a : Place) (chalOf : List Fmt.Drawn → Chal) (J : Jobs W') :
    ∀ (s : PartShape × Nat) (c : (partAt a chalOf J s).Coins),
      (∀ k, s.1 = .sum k → ∀ v ∈ k.vs, 2 ≤ v.d) →
      LensBy (sentOf s.1) ((saysAt a chalOf J s).map (· c))
  | (.sum k, _), c, h => lensBy_sumGs _ _ _ c (h k rfl)
  | (.one 0, _), _, _ => ⟨fun _ _ => rfl, trivial⟩
  | (.one (_ + 1), _), c, _ => ⟨fun s t => scalarsSaid_length _ _ c.2.1.1 s t, trivial⟩

/-- The part's first stop never stops. -/
theorem partAt_bad (a : Place) (chalOf : List Fmt.Drawn → Chal) (J : Jobs W') :
    ∀ (s : PartShape × Nat) (f o : List Fmt.Drawn), (partAt a chalOf J s).bad f o = none
  | (.sum _, _), _, _ => rfl
  | (.one 0, _), _, _ => rfl
  | (.one (_ + 1), _), _, _ => rfl

/-- The part's second stop never stops. -/
theorem partAt_hid (a : Place) (chalOf : List Fmt.Drawn → Chal) (J : Jobs W') :
    ∀ (s : PartShape × Nat) (w : Unit) (f o : List Fmt.Drawn),
      (partAt a chalOf J s).hid w f o = none
  | (.sum _, _), _, _, _ => rfl
  | (.one 0, _), _, _, _ => rfl
  | (.one (_ + 1), _), _, _, _ => rfl

/-! ## 2 The row -/

/-- The parts from the number j on, each lifted to the wider input and state. -/
def rowParts (a : Place) (chalOf : List Fmt.Drawn → Chal) (J : Jobs W') (wit : W → W')
    (sh : List PartShape) (j : Nat) : List (Part V W X) :=
  ((sh.zipIdx j).map (partAt a chalOf J)).map fun p =>
    p.lift (fun _ => ()) wit (fun _ => ()) fun x _ => x

/-- **The rounds of the row as played**, part by part: what the part's moves say at its coins, from
the state and the rounds shown in front of it, at its share of the challenges; each round under the
step's name, the place and the part's number, without a table. -/
def rowOut (nm : String) (a : Place) (chalOf : List Fmt.Drawn → Chal) (J : Jobs W')
    (wit : W → W') : (sh : List PartShape) → (j : Nat) →
      RowCoins (rowParts (V := V) (X := X) a chalOf J wit sh j) → State W X → Seen →
      List Fmt.Drawn → List Played
  | [], _, _, _, _, _ => []
  | s :: sh, j, c, t, seen, ds =>
    let c' : (partAt a chalOf J (s, j)).Coins ×
      RowCoins (rowParts (V := V) (X := X) a chalOf J wit sh (j + 1)) := c
    (outOf ((saysAt a chalOf J (s, j)).map (· c'.1)) (t.narrow wit fun _ => ()) seen
        (ds.take (sentOf s).length)).map (saidPlayed nm ⟨a, j⟩) ++
      rowOut nm a chalOf J wit sh (j + 1) c'.2
        ⟨t.input, t.heard ++ ds.take (sentOf s).length, t.own⟩
        (seen.plus (outOf ((saysAt a chalOf J (s, j)).map (· c'.1)) (t.narrow wit fun _ => ()) seen
          (ds.take (sentOf s).length)))
        (ds.drop (sentOf s).length)

/-- **THE ROW's STEPS PLAY: THE WHOLE LIST.** Conditional: every variable of every sumcheck has at
least two coefficients; the declared rounds state the parts' scalars and no oracle message; there
are as many challenges as rounds. At the kind's own shapes the first two have no premise left
(`shapes_two`, `rounds_stated`, Honest/K5/Law/Shapes.lean). -/
theorem rowOf_plays (nm : String) (a : Place) (chalOf : List Fmt.Drawn → Chal) (J : Jobs W')
    (wit : W → W') (v : Option V) : ∀ (sh : List PartShape) (j : Nat)
      (c : RowCoins (rowParts (V := V) (X := X) a chalOf J wit sh j))
      (rs : List (Fmt.DeclaredRound × List Oracle)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
      (m : Mid W X), (∀ k, PartShape.sum k ∈ sh → ∀ v ∈ k.vs, 2 ≤ v.d) →
      StatedBy (sh.flatMap sentOf) rs → ds.length = (sh.flatMap sentOf).length →
      play (rowSteps nm a v (rowParts a chalOf J wit sh j) j rs c) ds back m =
        .ok (rowOut nm a chalOf J wit sh j c m.st m.shown ds,
          ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
            m.seen ++ roundsOf (rowOut nm a chalOf J wit sh j c m.st m.shown ds), m.opened⟩)
  | [], _, _, _, [], _, m, _, _, _ => by
    show Except.ok ([], m) = Except.ok ([], (⟨⟨m.st.input, m.st.heard ++ [], m.st.own⟩,
      m.loc ++ [], m.seen ++ [], m.opened⟩ : Mid W X))
    rw [List.append_nil, List.append_nil, List.append_nil]
  | [], _, _, _, _ :: _, _, _, _, _, hl => by cases hl
  | s :: sh, j, c, rs, ds, back, m, h2, hr, hl => by
    rw [List.flatMap_cons] at hr hl
    obtain ⟨hr1, hr2⟩ := statedBy_split _ _ rs hr
    rw [List.length_append] at hl
    have hmv : ((partAt a chalOf J (s, j)).lift (V := V) (X := X) (fun _ => ()) wit (fun _ => ())
        fun x _ => x).moves.length = (sentOf s).length := by
      show ((partAt a chalOf J (s, j)).moves.map _).length = _
      rw [List.length_map, partAt_moves, List.length_map]
      have := lensBy_length _ _ (saysAt_lens a chalOf J (s, j) c.1
        fun k hk => h2 k (by rw [← hk]; exact List.mem_cons_self))
      rwa [List.length_map] at this
    have ht : (ds.take (sentOf s).length).length = (sentOf s).length := by
      rw [List.length_take]
      omega
    have hd : (ds.drop (sentOf s).length).length = (sh.flatMap sentOf).length := by
      rw [List.length_drop]
      omega
    have h1 := plays_lift_said (V := V) (X := X) (fun _ => ()) wit (fun _ => ()) (fun x _ => x)
      (fun _ => rfl) (partAt a chalOf J (s, j)) (partAt_bad a chalOf J _) (partAt_hid a chalOf J _)
      (saysAt a chalOf J (s, j)) (partAt_moves a chalOf J _) (sentOf s) c.1
      (saysAt_lens a chalOf J (s, j) c.1 fun k hk => h2 k (by rw [← hk]; exact List.mem_cons_self))
      nm ⟨a, j⟩ (rs.take (sentOf s).length) hr1 v (ds.take (sentOf s).length) ht back m
    have hs : (((partAt a chalOf J (s, j)).lift (V := V) (X := X) (fun _ => ()) wit (fun _ => ())
        fun x _ => x).steps nm ⟨a, j⟩ (rs.take (sentOf s).length) v c.1).length =
        (sentOf s).length := by
      rw [steps_length, statedBy_length _ _ hr1, hmv, Nat.min_self]
    have e := rowSteps_cons nm a v ((partAt a chalOf J (s, j)).lift (V := V) (X := X)
      (fun _ => ()) wit (fun _ => ()) fun x _ => x) (rowParts a chalOf J wit sh (j + 1)) j rs c
    rw [hmv] at e
    have h3 := fun bk => rowOf_plays nm a chalOf J wit v sh (j + 1) c.2
      (rs.drop (sentOf s).length) (ds.drop (sentOf s).length) bk
      ⟨⟨m.st.input, m.st.heard ++ ds.take (sentOf s).length, m.st.own⟩,
        m.loc ++ ds.take (sentOf s).length,
        m.seen ++ outOf ((saysAt a chalOf J (s, j)).map (· c.1)) (m.st.narrow wit fun _ => ())
          m.shown (ds.take (sentOf s).length), m.opened⟩
      (fun k hk => h2 k (List.mem_cons_of_mem _ hk)) hr2 hd
    have er : ∀ (O : List Fmt.RoundView) (R : List Played),
        roundsOf (O.map (saidPlayed nm ⟨a, j⟩) ++ R) = O ++ roundsOf R := by
      intro O R
      show (O.map (saidPlayed nm ⟨a, j⟩) ++ R).map _ = _
      rw [List.map_append]
      exact congrArg (· ++ roundsOf R) (roundsOf_said nm ⟨a, j⟩ O)
    refine (congrArg (fun L => play L ds back m) e).trans ?_
    have ed : play (((partAt a chalOf J (s, j)).lift (V := V) (X := X) (fun _ => ()) wit
          (fun _ => ()) fun x _ => x).steps nm ⟨a, j⟩ (rs.take (sentOf s).length) v c.1 ++
        rowSteps nm a v (rowParts a chalOf J wit sh (j + 1)) (j + 1) (rs.drop (sentOf s).length)
          c.2) (ds.take (sentOf s).length ++ ds.drop (sentOf s).length) back m = _ :=
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
theorem rowOut_tables (nm : String) (a : Place) (chalOf : List Fmt.Drawn → Chal) (J : Jobs W')
    (wit : W → W') : ∀ (sh : List PartShape) (j : Nat)
      (c : RowCoins (rowParts (V := V) (X := X) a chalOf J wit sh j)) (t : State W X)
      (seen : Seen) (ds : List Fmt.Drawn),
      tablesOf (rowOut nm a chalOf J wit sh j c t seen ds) = []
  | [], _, _, _, _, _ => rfl
  | s :: sh, j, c, t, seen, ds => by
    show tablesOf (_ ++ _) = []
    rw [tablesOf_append, tablesOf_said, rowOut_tables nm a chalOf J wit sh (j + 1)]
    rfl

/-! ## 3 What a part's rounds are, sort by sort -/

/-- A masked sumcheck's rounds are `sumOut`'s. Conditional: as many challenges as rounds. -/
theorem says_sum (a : Place) (chalOf : List Fmt.Drawn → Chal) (J : Jobs W') (k : Call) (i : Nat)
    (c : (partAt a chalOf J (.sum k, i)).Coins) (t : State W' Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (hl : ds.length = (sentOf (.sum k)).length) :
    outOf ((saysAt a chalOf J (.sum k, i)).map (· c)) t seen ds =
      sumOut (name := nameOf a i "sum") (endName := nameOf a i "ends")
        (jobOf k (fun w fr => J.alone i w (chalOf fr.heard)) fun w fr =>
          J.sum i w (chalOf fr.heard)) c t seen ds :=
  outOf_sumGs _ _ _ c t seen ds (hl.trans (scalarsOf_length (nameOf a i "sum") (nameOf a i "ends")
    (jobOf k (fun w fr => J.alone i w (chalOf fr.heard)) fun w fr =>
      J.sum i w (chalOf fr.heard))))

/-- A round by itself in which nothing is sent. -/
theorem says_quiet (a : Place) (chalOf : List Fmt.Drawn → Chal) (J : Jobs W') (i : Nat)
    (c : (partAt a chalOf J (.one 0, i)).Coins) (t : State W' Unit) (seen : Seen)
    (d : Fmt.Drawn) :
    outOf ((saysAt a chalOf J (.one 0, i)).map (· c)) t seen [d] = [⟨[], d⟩] := rfl

/-- A round by itself in which scalars are sent: each as its value plus its mask entry. -/
theorem says_scalars (a : Place) (chalOf : List Fmt.Drawn → Chal) (J : Jobs W') (n i : Nat)
    (c : (partAt a chalOf J (.one (n + 1), i)).Coins) (t : State W' Unit) (seen : Seen)
    (d : Fmt.Drawn) :
    outOf ((saysAt a chalOf J (.one (n + 1), i)).map (· c)) t seen [d] =
      [rvSaid (scalarsSaid (n + 1) (fun w fr => J.alone i w (chalOf fr.heard)) c.2.1.1 seen t) d] :=
  rfl

end Row

/-! ## 4 At the member -/

section Member
variable {Bk : ProverCoinCounts} {S Cl W₀ Rc Xi Tr X Pb : Type}

/-- The half's parts are the row's, lifted. -/
theorem k5Half_parts (cells : Tr → Cells) (Z : Seat5) :
    (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts =
      rowParts Z.place (chalOf Z) (jobs Z.P)
        (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace)) (shapes Z.P.x) 0 := rfl

/-- **The kind's rounds as played, at a place's public data.** nm: the member's name. -/
def k5Out (nm : String) (cells : Tr → Cells) (Z : Seat5)
    (c : RowCoins (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts)
    (t : State (Local W₀ Rc Xi Tr) X) (seen : Seen) (ds : List Fmt.Drawn) : List Played :=
  rowOut nm Z.place (chalOf Z) (jobs Z.P)
    (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace)) (shapes Z.P.x) 0 c t seen ds

variable (T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block S Cl}

/-- **What the member's Steps are, and what `play` returns on them: the whole list.** Conditional:
on `K5Seated`; the challenges are such as the member's rounds can draw; `chainSteps` has returned,
that is: the book has lent the row its coins. c: these coins, part by part, as `lendRow` lends them:
what a later law on the mask entries under the scalars will speak of. -/
theorem k5_played (Hs : K5Seated T b cells Z p blk) {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {v : Option (Local W₀ Rc Xi Tr)}
    {l : List (Step (Local W₀ Rc Xi Tr) X)} {ds : List Fmt.Drawn}
    (hd : drawsFit blk.rounds ds = true) (hl : chainSteps Bk rows look v [blk] T.hs = .ok l)
    (m : Mid (Local W₀ Rc Xi Tr) X) :
    ∃ c, lendRow Bk rows look blk.place (k5Half cells Z).parts 0 = .ok c ∧
      l = (k5Half cells Z).steps blk v c ∧
      play l ds [] m = .ok (k5Out blk.name cells Z c m.st m.shown ds,
        ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
          m.seen ++ roundsOf (k5Out blk.name cells Z c m.st m.shown ds), m.opened⟩) := by
  obtain ⟨c, hc, rfl⟩ := steps_one_half Hs.half hl
  refine ⟨c, hc, rfl, ?_⟩
  have hlen : ds.length = ((shapes Z.P.x).flatMap sentOf).length := by
    rw [drawsFit_length _ _ hd, Hs.rounds, rounds_length, Hs.own]
  have hst : StatedBy ((shapes Z.P.x).flatMap sentOf) (blk.rounds.zip blk.oracles) := by
    rw [Hs.rounds, Hs.oracles, ← Hs.own]
    exact rounds_stated p
  show play (rowSteps blk.name blk.place v _ 0 (blk.rounds.zip blk.oracles) c) ds [] m = _
  rw [Hs.place]
  exact rowOf_plays blk.name Z.place (chalOf Z) (jobs Z.P) _ v (shapes Z.P.x) 0 c _ ds [] m
    (shapes_two _) hst hlen

/-- A part of the row has as many moves as its shape has rounds in which it sends. -/
theorem partAt_count {W' : Type} (a : Place) (chalOf : List Fmt.Drawn → Chal) (J : Jobs W') :
    ∀ s : PartShape × Nat, (partAt a chalOf J s).moves.length = (sentOf s.1).length
  | (.sum _, _) => by
    rw [partAt_moves, List.length_map]
    exact (scalarsOf_length _ _ _).symm
  | (.one 0, _) => rfl
  | (.one (_ + 1), _) => rfl

/-- The row's numbers of moves, part by part. -/
theorem rowParts_moves {V W W' X : Type} (a : Place) (chalOf : List Fmt.Drawn → Chal) (J : Jobs W')
    (wit : W → W') : ∀ (sh : List PartShape) (j : Nat),
      (rowParts (V := V) (X := X) a chalOf J wit sh j).map (·.moves.length) =
        sh.map fun s => (sentOf s).length
  | [], _ => rfl
  | s :: sh, j => by
    show ((partAt a chalOf J (s, j)).moves.map _).length ::
      (rowParts (V := V) (X := X) a chalOf J wit sh (j + 1)).map (·.moves.length) = _
    rw [List.length_map, partAt_count, rowParts_moves a chalOf J wit sh (j + 1)]
    rfl

/-- The half is cut as `cut` says (Johnson/Desc/K5/Honest/Faces.lean). No premise. -/
theorem half_cut (cells : Tr → Cells) (Z : Seat5) :
    (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts.map (·.moves.length) =
      H2K5.Honest.cut Z.P.x := by
  rw [k5Half_parts, rowParts_moves]
  exact List.map_congr_left fun s hs => sentOf_length Z.P.x s hs

/-- **A TEST WITH CODE ON THE BOOK**, at a place's public data: the three of `chainSteps`' tests
that read the book and the row's cut alone: the book's cut for the place is the row's; the book's
table for the chain has no row, and the book no entry, for a part beyond the row's. -/
def bookFits (Bk : ProverCoinCounts) (rows : List (Addr × Due)) (Z : Seat5) : Bool :=
  Bk.cuts.lookup Z.place == some (H2K5.Honest.cut Z.P.x) &&
    !rows.any (fun r => r.1.place == Z.place && decide ((shapes Z.P.x).length ≤ r.1.part)) &&
    !Bk.ahead.any fun e =>
      e.spender.place == Z.place && decide ((shapes Z.P.x).length ≤ e.spender.part)

/-- **`chainSteps` RETURNS AT THE MEMBER**: the equation that the debts of Honest/Thread/Pays.lean
which speak of the member's Steps have as a premise. CONDITIONAL: on `K5Seated`; the book passes
`bookFits`, a test with code on public data; and `lendRow` lends the row its coins. Who is meant to
show the last two: whoever makes the book. No law that `lendRow` returns under a test with code is
known to this file. -/
theorem k5_steps_return (Hs : K5Seated T b cells Z p blk) {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} (v : Option (Local W₀ Rc Xi Tr))
    (hB : bookFits Bk rows Z = true) {c : RowCoins (k5Half cells Z).parts}
    (hc : lendRow Bk rows look Z.place (k5Half cells Z).parts 0 = .ok c) :
    chainSteps Bk rows look v [blk] T.hs = .ok ((k5Half cells Z).steps blk v c) := by
  simp only [bookFits, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hB
  obtain ⟨⟨b1, b2⟩, b3⟩ := hB
  have hn : (k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).parts.length =
      (shapes Z.P.x).length := by
    have := congrArg List.length (half_cut (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z)
    rw [List.length_map] at this
    rw [this]
    exact List.length_map _
  have e1 : (blk.oracles.length != blk.rounds.length) = false := by
    rw [Hs.oracles, Hs.rounds, List.length_map]
    exact bne_self_eq_false _
  have e2 : ((k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z).rounds !=
      blk.rounds.length) = false := by
    unfold Placed.rounds
    rw [foldl_moves, Nat.zero_add, half_cut, Hs.rounds, ← Hs.own, cut_sum]
    exact bne_self_eq_false _
  have e3 : (Bk.cuts.lookup blk.place != some ((k5Half (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X)
      cells Z).parts.map (·.moves.length))) = false := by
    rw [Hs.place, half_cut, b1]
    exact bne_self_eq_false _
  rw [← Hs.place] at b2 b3 hc
  simp only [chainSteps, Hs.half, e1, e2, e3, hn, b2, b3, hc, Bool.false_eq_true, if_false]
  simp [Except.mapError, Except.bind, Except.map]

/-- **The member reads no column.** Conditional: on `K5Seated`. -/
theorem k5_cols (Hs : K5Seated T b cells Z p blk) (chain ft : Nat)
    (stored : Nat → Nat → Option (List UInt64)) (tree : Fmt.TreeSource → Option (Place × Table))
    (ds : List Fmt.Drawn) :
    fillCols (readsOf chain ft stored tree blk.rounds ds) [] = .ok [] := by
  rw [Hs.rounds]
  exact fillCols_none chain ft stored tree _ ds (rounds_read_nothing p) []

/-- **No tree is at hand behind the member that is not at hand in front of it.** Conditional: on
`K5Seated`. -/
theorem k5_fresh (Hs : K5Seated T b cells Z p blk) : T.fresh b = [] := by
  have ho : blk.oracles.flatMap id = [] := by
    rw [Hs.oracles, List.flatMap_eq_nil_iff]
    intro x hx
    obtain ⟨_, _, rfl⟩ := List.mem_map.1 hx
    rfl
  have ht : treesTo T.bs (b + 1) = treesTo T.bs b := by
    unfold treesTo
    rw [List.take_add_one, Hs.member, List.flatMap_append, List.length_append]
    show _ + ([blk].flatMap fun x => x.oracles.flatMap id).length = _
    rw [List.flatMap_cons, ho]
    rfl
  unfold Thread.fresh Thread.hand
  rw [ht, List.filter_eq_nil_iff]
  intro σ hσ
  simp [hσ]

/-- **The tables at hand stay as they are, and no column is laid.** Conditional: on `K5Seated`; no
tree is at hand above those sent (a clause of `Thr` in front: `Thread.Made`). -/
theorem k5_env (Hs : K5Seated T b cells Z p blk) {k : Coins Bk} {m : Mid (Local W₀ Rc Xi Tr) X}
    {E : Env} {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    {cols : List OpenedColumn} (hd : drawsFit blk.rounds ds = true)
    (hE : ∀ n, E.sent ≤ n → E.tree (.own n) = none) (hM : T.Moved blk k m E ds y cols) :
    E.add y.1 = E ∧ cols = [] := by
  obtain ⟨⟨l, hl, hp⟩, hc⟩ := hM
  obtain ⟨c, -, -, hq⟩ := k5_played T Hs hd hl m
  rw [hp] at hq
  have hy := congrArg (·.1) (Except.ok.inj hq)
  rw [k5_cols T Hs] at hc
  refine ⟨add_none E y.1 ?_ hE, (Except.ok.inj hc).symm⟩
  rw [show y.1 = _ from hy]
  exact rowOut_tables _ _ _ _ _ _ _ _ _ _ _

/-! ## 5 It plays -/

/-- **IT PLAYS**: the debt `Plays` (Honest/Thread/Pays.lean) at the member at which the kind's half
stands. CONDITIONAL: on `K5Seated`, which is shown here of no description. Of `Thr` in front
and of "nothing stops" the proof reads nothing. `Plays` takes `Thr` alone, which does not read the
field `opened` of the state of the prover's run (`thr_took`, Honest/Thread/ThrField.lean: the two
sides are one term): so it is asked, and shown here, at every value of that field, `none` too. -/
theorem k5_plays (Hs : K5Seated T b cells Z p blk) : Plays T b := by
  intro blk' hb k s m E ds l _ hd _ hl
  obtain rfl : blk = blk' := Option.some.inj (Hs.member.symm.trans hb)
  obtain ⟨c, -, -, hp⟩ := k5_played T Hs hd hl m
  refine ⟨_, [], ⟨⟨l, hl, hp⟩, k5_cols T Hs _ _ _ _ _⟩, ?_⟩
  rw [k5_fresh T Hs]
  intro σ hσ
  cases hσ

/-! ## 6 The played rounds fit the verifier's entries -/

/-- **THE PLAYED ROUNDS, WITHOUT THE SEALED DIGEST, FIT THE VERIFIER's ENTRIES.** CONDITIONAL: on
`K5Seated`; the challenges are such as the member's rounds can draw; the prover's side of the step
has gone through (`Thread.Moved`). -/
theorem fits_of_played (Hs : K5Seated T b cells Z p blk) {k : Coins Bk}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols) :
    Fits ((rounds p).map (·.entry)) ((roundsOf y.1).map noDigest) := by
  obtain ⟨⟨l, hl, hp⟩, hc⟩ := hM
  obtain ⟨ho, hr⟩ := half_counts Hs.half hl
  obtain ⟨c, -, rfl⟩ := steps_one_half Hs.half hl
  have h := (fits_played hr ho hp hd hc).1.1
  rw [Hs.rounds] at h
  exact fits_of_roundsFit _ _ h (rounds_plain p)

/-! ## 7 The rounds bear no sealed digest -/

/-- **AT THIS MEMBER, TAKING THE SEALED DIGEST OUT OF THE PLAYED ROUNDS CHANGES NOTHING.** The
general step hands a sub-protocol's decision its rounds with the sealed digest taken out
(`noDigest`). None of this member's rounds is a sealing round, so no challenge that they can draw
has a sealed digest. So the verifier's hearing is handed the very list of which
Honest/K5/Law/Stretch.lean says "played alone, the part says these rounds". CONDITIONAL: on
`K5Seated`; the challenges are such as the member's rounds can draw; `play` has returned at these
challenges, on whatever list of Steps. -/
theorem k5_bare (Hs : K5Seated T b cells Z p blk) {l : List (Step (Local W₀ Rc Xi Tr) X)}
    {ds : List Fmt.Drawn} (hd : drawsFit blk.rounds ds = true) {m : Mid (Local W₀ Rc Xi Tr) X}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} (hp : play l ds [] m = .ok y) :
    (roundsOf y.1).map noDigest = roundsOf y.1 := by
  have hdr : (roundsOf y.1).map (·.drawn) = ds := yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hp)
  have hn := digest_of_fit _ _ hd (by
    rw [Hs.rounds]
    intro z hz hs
    rcases (VerifiableInference.Desc.First.Att.P.rounds_cut p z hz).kind with h | h | h <;>
      · rw [hs] at h
        cases h)
  refine noDigest_of_none _ fun r hr => hn _ ?_
  rw [← hdr]
  exact List.mem_map.2 ⟨r, hr, rfl⟩

end Member

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.rowOf_eq
#print axioms ProofFile.Honest.K5.partAt_moves
#print axioms ProofFile.Honest.K5.saysAt_lens
#print axioms ProofFile.Honest.K5.partAt_bad
#print axioms ProofFile.Honest.K5.partAt_hid
#print axioms ProofFile.Honest.K5.rowOf_plays
#print axioms ProofFile.Honest.K5.rowOut_tables
#print axioms ProofFile.Honest.K5.says_sum
#print axioms ProofFile.Honest.K5.says_quiet
#print axioms ProofFile.Honest.K5.says_scalars
#print axioms ProofFile.Honest.K5.k5Half_parts
#print axioms ProofFile.Honest.K5.k5_played
#print axioms ProofFile.Honest.K5.partAt_count
#print axioms ProofFile.Honest.K5.rowParts_moves
#print axioms ProofFile.Honest.K5.half_cut
#print axioms ProofFile.Honest.K5.k5_steps_return
#print axioms ProofFile.Honest.K5.k5_cols
#print axioms ProofFile.Honest.K5.k5_fresh
#print axioms ProofFile.Honest.K5.k5_env
#print axioms ProofFile.Honest.K5.k5_plays
#print axioms ProofFile.Honest.K5.fits_of_played
#print axioms ProofFile.Honest.K5.k5_bare
