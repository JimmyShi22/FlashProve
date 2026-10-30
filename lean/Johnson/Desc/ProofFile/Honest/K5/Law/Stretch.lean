-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Stretch.lean: CONDITIONAL: the rounds that the honest side of
an attention segment's own rounds plays (`rowOut`, `k5Out`, Honest/K5/Law/Plays.lean), CUT PART BY
PART: the stretch of a part is what that part says when it is played alone (`alone`,
Honest/SumLaw/Terms.lean), at the coins that the book lends it. Statements with their proofs, and
one definition with code.

  `frontOfPart`   how many rounds stand in front of a part
  `alone_partAt`, `outOf_length`   a part of the row, played alone
  `rowOut_cut`   **the law in a row of parts**, general in the list of shapes, the jobs, the place,
      the step's name and the lift's reader of the input
  `frontOfPart_shapes`, `k5_cut`   **the law at the member**: in the numbers of
      Johnson/Desc/K5/Honest/Faces.lean (`firstOf`, `PartShape.rounds`)
  `entries_length`, `entriesAre_at`, `k5_drawsOk`   a sumcheck's entries are its stretch of the
      row's; **its share of the challenges has the call's numbers of elements**

What it is for. The laws on the masked sumcheck's honest part (Honest/SumLaw/Statement.lean) speak
of the part played alone, at a state, rounds shown and challenges of its own. This file hands them
these at each part of the kind's row, with the coins as `lendPart` lends them.

Every statement on a row or a member is CONDITIONAL: see each docstring. `K5Seated` is shown here
of no description.
Limits. The rounds are those that a view shows, with the sealed digest as drawn: the verifier's
decision is shown them without; at this member the two are one list (`k5_bare`,
Honest/K5/Law/Plays.lean). Nothing is said of the values.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Plays
import Johnson.Desc.K5.Honest.Law.Calls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E)
open VerifiableInference.Desc (Block Place Oracle OpenedColumn)
open VerifiableInference.Desc.Part.MaskedSum (Call)
open VerifiableInference.Desc.First.Att.P (Par rounds)
open H2K5.Honest (PartShape shapes Chal)
open ProofFile.Honest.SumLaw

/-! ## 1 In a row of parts -/

section Row
variable {V W W' X : Type}

/-- How many rounds stand in front of the part number q of a list of shapes. -/
def frontOfPart (sh : List PartShape) (q : Nat) : Nat := ((sh.take q).flatMap sentOf).length

/-- A part of the row, played alone, says what `saysAt` lists. Conditional: as many challenges as
the shape has rounds; every variable of a sumcheck has at least two coefficients. -/
theorem alone_partAt (a : Place) (chalOf : List Fmt.Drawn → Chal) (J : Jobs W')
    (s : PartShape × Nat) (c : (partAt a chalOf J s).Coins)
    (h2 : ∀ k, s.1 = .sum k → ∀ v ∈ k.vs, 2 ≤ v.d) (t : State W' Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (hl : ds.length = (sentOf s.1).length) :
    alone (partAt a chalOf J s) c t seen ds =
      some (outOf ((saysAt a chalOf J s).map (· c)) t seen ds) := by
  have hlen : (saysAt a chalOf J s).length = ds.length := by
    have := lensBy_length _ _ (saysAt_lens a chalOf J s c h2)
    rw [List.length_map] at this
    rw [this, hl]
  unfold alone
  rw [partAt_moves]
  exact aloneFrom_mvOf c _ t seen ds hlen

/-- Such rounds are as many as the challenges, where these are as many as the moves. -/
theorem outOf_length : ∀ (gs : List (Seen → State W X → List E)) (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn), gs.length = ds.length →
    (outOf gs t seen ds).length = ds.length
  | [], _, _, [], _ => rfl
  | g :: gs, t, seen, d :: ds, h =>
    congrArg (· + 1) (outOf_length gs (t.hears d) (seen.plus [rvSaid (g seen t) d]) ds
      (Nat.succ.inj h))
  | [], _, _, _ :: _, h => by cases h
  | _ :: _, _, _, [], h => by cases h

/-- **A PART's STRETCH OF THE ROW's ROUNDS IS WHAT THE PART SAYS WHEN IT IS PLAYED ALONE**: at the
coins that the book lends that part; from the narrowed state that has heard the challenges of the
parts in front; behind the rounds that these have shown; at the part's own share of the challenges.
Conditional: the row's coins are those that `lendRow` lends; every variable of every sumcheck has at
least two coefficients; there are as many challenges as rounds. -/
theorem rowOut_cut {Bk : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    (nm : String) (a : Place) (chalOf : List Fmt.Drawn → Chal) (J : Jobs W') (wit : W → W') :
    ∀ (sh : List PartShape) (j : Nat)
      (c : RowCoins (rowParts (V := V) (X := X) a chalOf J wit sh j)) (t : State W X)
      (seen : Seen) (ds : List Fmt.Drawn),
      lendRow Bk rows look a (rowParts (V := V) (X := X) a chalOf J wit sh j) j = .ok c →
      (∀ k, PartShape.sum k ∈ sh → ∀ v ∈ k.vs, 2 ≤ v.d) →
      ds.length = (sh.flatMap sentOf).length →
      ∀ (q : Nat) (si : PartShape × Nat), (sh.zipIdx j)[q]? = some si →
      ∃ cq : (partAt a chalOf J si).Coins,
        lendPart Bk rows look ⟨a, si.2⟩ ((partAt a chalOf J si).lift (V := V) (X := X)
          (fun _ => ()) wit (fun _ => ()) fun x _ => x) = .ok cq ∧
        alone (partAt a chalOf J si) cq
            ⟨wit t.input, t.heard ++ ds.take (frontOfPart sh q), ()⟩
            (seen.plus
                ((roundsOf (rowOut nm a chalOf J wit sh j c t seen ds)).take (frontOfPart sh q)))
            ((ds.drop (frontOfPart sh q)).take (sentOf si.1).length) =
          some (((roundsOf (rowOut nm a chalOf J wit sh j c t seen ds)).drop
            (frontOfPart sh q)).take (sentOf si.1).length)
  | [], _, _, _, _, _, _, _, _, _, _, h => by cases h
  | s :: sh, j, c, t, seen, ds, hc, h2, hl, q, si, hq => by
    rw [List.flatMap_cons, List.length_append] at hl
    have ht : (ds.take (sentOf s).length).length = (sentOf s).length := by
      rw [List.length_take]
      omega
    have hs2 : ∀ k, (s, j).1 = PartShape.sum k → ∀ v ∈ k.vs, 2 ≤ v.d :=
      fun k hk => h2 k (by rw [← hk]; exact List.mem_cons_self)
    have hgl : ((saysAt a chalOf J (s, j)).map (· c.1)).length =
        (ds.take (sentOf s).length).length := by
      rw [lensBy_length _ _ (saysAt_lens a chalOf J (s, j) c.1 hs2), ht]
    have hol := outOf_length _ (t.narrow wit fun _ => ()) seen (ds.take (sentOf s).length) hgl
    rw [ht] at hol
    have eR : roundsOf (rowOut nm a chalOf J wit (s :: sh) j c t seen ds) =
        outOf ((saysAt a chalOf J (s, j)).map (· c.1)) (t.narrow wit fun _ => ()) seen
            (ds.take (sentOf s).length) ++
          roundsOf (rowOut nm a chalOf J wit sh (j + 1) c.2
            ⟨t.input, t.heard ++ ds.take (sentOf s).length, t.own⟩
            (seen.plus
                (outOf ((saysAt a chalOf J (s, j)).map (· c.1)) (t.narrow wit fun _ => ()) seen
              (ds.take (sentOf s).length))) (ds.drop (sentOf s).length)) := by
      show (_ ++ _ : List Played).map _ = _
      rw [List.map_append]
      exact congrArg (· ++ _) (roundsOf_said nm ⟨a, j⟩ _)
    obtain ⟨c1, hc1, hc⟩ := exBind_ok hc
    obtain ⟨c2, hc2, hcc⟩ := exMap_ok hc
    have e1 : c.1 = c1 := (congrArg (·.1) hcc).symm
    have e2 : c.2 = c2 := (congrArg (·.2) hcc).symm
    cases q with
    | zero =>
      obtain rfl : (s, j) = si := Option.some.inj hq
      refine ⟨c.1, ?_, ?_⟩
      · rw [e1]
        cases hp : lendPart Bk rows look ⟨a, j⟩ ((partAt a chalOf J (s, j)).lift (V := V) (X := X)
            (fun _ => ()) wit (fun _ => ()) fun x _ => x) with
        | error e =>
          rw [hp] at hc1
          cases hc1
        | ok c' =>
          rw [hp] at hc1
          cases hc1
          rfl
      · show alone _ _ ⟨wit t.input, t.heard ++ ds.take 0, ()⟩ (seen.plus (List.take 0 _))
          ((ds.drop 0).take _) = some ((List.drop 0 _).take _)
        rw [List.take_zero, List.take_zero, List.append_nil, Seen.plus_nil, List.drop_zero,
          List.drop_zero, eR, List.take_left' hol]
        exact alone_partAt a chalOf J (s, j) c.1 hs2 _ seen _ ht
    | succ q =>
      have hd : (ds.drop (sentOf s).length).length = (sh.flatMap sentOf).length := by
        rw [List.length_drop]
        omega
      obtain ⟨cq, h1, h3⟩ := rowOut_cut nm a chalOf J wit sh (j + 1) c.2
        ⟨t.input, t.heard ++ ds.take (sentOf s).length, t.own⟩
        (seen.plus (outOf ((saysAt a chalOf J (s, j)).map (· c.1)) (t.narrow wit fun _ => ()) seen
          (ds.take (sentOf s).length))) (ds.drop (sentOf s).length) (by rw [e2]; exact hc2)
        (fun k hk => h2 k (List.mem_cons_of_mem _ hk)) hd q si hq
      refine ⟨cq, h1, ?_⟩
      have eF : frontOfPart (s :: sh) (q + 1) = (sentOf s).length + frontOfPart sh q := by
        unfold frontOfPart
        rw [List.take_succ_cons, List.flatMap_cons, List.length_append]
      rw [eF, eR, List.take_add, List.take_add, List.take_left' hol, List.drop_left' hol,
        ← List.drop_drop, ← List.drop_drop, List.drop_left' hol, ← List.append_assoc,
        ← Seen.plus_plus]
      exact h3

/-- A call has as many entries as rounds in which it sends. -/
theorem entries_length (k : Call) :
    (VerifiableInference.Desc.Part.MaskedSum.entries k).length = (scalarsOf k).length := by
  have h := congrArg List.length (entries_nums k)
  rwa [List.length_map, List.length_map] at h

/-- **The entries of a part that is a masked sumcheck are its stretch of the row's entries.**
Conditional: the entries are the parts' entries in a row (`EntriesAre`,
Honest/K5/Law/Shapes.lean). -/
theorem entriesAre_at : ∀ (L : List PartShape) (es : List Fmt.Entry), EntriesAre L es →
    ∀ (q : Nat) (k : Call), L[q]? = some (.sum k) →
    (es.drop (frontOfPart L q)).take (sentOf (.sum k)).length =
      VerifiableInference.Desc.Part.MaskedSum.entries k
  | [], _, _, _, _, h => by cases h
  | .sum k' :: L, _, ⟨es', rfl, _⟩, 0, k, h => by
    obtain rfl : k' = k := by
      have := Option.some.inj h
      cases this
      rfl
    show ((_ ++ es').drop 0).take _ = _
    rw [List.drop_zero]
    exact List.take_left' (entries_length k')
  | .sum k' :: L, _, ⟨es', rfl, h'⟩, q + 1, k, h => by
    have eF : frontOfPart (.sum k' :: L) (q + 1) = (sentOf (.sum k')).length + frontOfPart L q := by
      unfold frontOfPart
      rw [List.take_succ_cons, List.flatMap_cons, List.length_append]
    rw [eF, ← List.drop_drop, List.drop_left' (show _ = (sentOf (.sum k')).length from
      entries_length k')]
    exact entriesAre_at L es' h' q k h
  | .one _ :: L, _, _, 0, k, h => by cases h
  | .one n :: L, _, ⟨e, es', rfl, _, h'⟩, q + 1, k, h => by
    have eF : frontOfPart (.one n :: L) (q + 1) = 1 + frontOfPart L q := by
      unfold frontOfPart
      rw [List.take_succ_cons, List.flatMap_cons, List.length_append]
      rfl
    rw [eF, ← List.drop_drop]
    exact entriesAre_at L es' h' q k h

end Row

/-! ## 2 At the member -/

section Member
variable {Bk : ProverCoinCounts} {S Cl W₀ Rc Xi Tr X Pb : Type}

private theorem zipIdx_get {α : Type} : ∀ (l : List α) (j q : Nat) (s : α), l[q]? = some s →
    (l.zipIdx j)[q]? = some (s, j + q)
  | [], _, _, _, h => by cases h
  | _ :: _, _, 0, _, h => by
    cases h
    rfl
  | _ :: l, j, q + 1, s, h => by
    show (l.zipIdx (j + 1))[q]? = _
    rw [zipIdx_get l (j + 1) q s h, Nat.add_right_comm, Nat.add_assoc]

/-- In the kind's row the rounds in front of a part are those that `firstOf` counts. -/
theorem frontOfPart_shapes (x : OnBytes.Params.AttentionRounds) (q : Nat) :
    frontOfPart (shapes x) q = H2K5.Honest.firstOf x q := by
  unfold frontOfPart
  rw [H2K5.Honest.firstOf_eq, List.length_flatMap]
  exact congrArg List.sum (List.map_congr_left fun s hs =>
    sentOf_length x s (List.mem_of_mem_take hs))

variable (T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block S Cl}

/-- **AT THE MEMBER: THE STRETCH OF PART q OF THE PLAYED ROUNDS IS WHAT THAT PART SAYS WHEN IT IS
PLAYED ALONE**: at the coins that the book lends the part at the address (the place, q); from the
small input, at the challenges heard up to the part's first round (`firstOf`); behind the rounds
shown up to there. At a part that is a masked sumcheck `partAt` is `sumPart` at the part's job, by
its text: so this is the premise "played alone, the part says these rounds" of the laws on the
masked sumcheck's part (Honest/SumLaw/Statement.lean). CONDITIONAL: on `K5Seated`; the challenges
are such as the member's rounds can draw; `chainSteps` and `play` have returned. That the part's
share of the challenges has the call's numbers of elements is `k5_drawsOk` below. -/
theorem k5_cut (Hs : K5Seated T b cells Z p blk) {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {v : Option (Local W₀ Rc Xi Tr)}
    {l : List (Step (Local W₀ Rc Xi Tr) X)} {ds : List Fmt.Drawn}
    (hd : drawsFit blk.rounds ds = true) (hl : chainSteps Bk rows look v [blk] T.hs = .ok l)
    {m : Mid (Local W₀ Rc Xi Tr) X} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
    (hp : play l ds [] m = .ok y) (q : Nat) (s : PartShape)
    (hq : (shapes Z.P.x)[q]? = some s) :
    ∃ cq : (partAt Z.place (chalOf Z) (jobs Z.P) (s, q)).Coins,
      lendPart Bk rows look ⟨Z.place, q⟩
        ((partAt Z.place (chalOf Z) (jobs Z.P) (s, q)).lift (V := Local W₀ Rc Xi Tr) (X := X)
          (fun _ => ()) (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace))
          (fun _ => ()) fun x _ => x) = .ok cq ∧
      alone (partAt Z.place (chalOf Z) (jobs Z.P) (s, q)) cq
          ⟨inOf Z.P.S Z.link (cells m.st.input.trace),
            m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x q), ()⟩
          (m.shown.plus ((roundsOf y.1).take (H2K5.Honest.firstOf Z.P.x q)))
          ((ds.drop (H2K5.Honest.firstOf Z.P.x q)).take s.rounds) =
        some (((roundsOf y.1).drop (H2K5.Honest.firstOf Z.P.x q)).take s.rounds) := by
  obtain ⟨c, hc, -, hq'⟩ := k5_played T Hs hd hl m
  rw [hp] at hq'
  have hy : y.1 = k5Out blk.name cells Z c m.st m.shown ds := congrArg (·.1) (Except.ok.inj hq')
  have hlen : ds.length = ((shapes Z.P.x).flatMap sentOf).length := by
    rw [drawsFit_length _ _ hd, Hs.rounds, rounds_length, Hs.own]
  rw [Hs.place] at hc
  have hz := zipIdx_get (shapes Z.P.x) 0 q s hq
  rw [Nat.zero_add] at hz
  have h := rowOut_cut blk.name Z.place (chalOf Z) (jobs Z.P)
    (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace)) (shapes Z.P.x) 0 c m.st m.shown
    ds hc (shapes_two _) hlen q (s, q) hz
  rw [frontOfPart_shapes, sentOf_length Z.P.x s (List.mem_of_getElem? hq)] at h
  rw [hy]
  exact h

/-- **AT THE MEMBER: THE SHARE OF THE CHALLENGES OF A PART THAT IS A MASKED SUMCHECK HAS THE CALL's
NUMBERS OF ELEMENTS** (`drawsOk`, Honest/SumLaw/Terms.lean): a premise of the laws on the masked
sumcheck's part. CONDITIONAL: on `K5Seated`; the challenges are such as the member's rounds can
draw. -/
theorem k5_drawsOk (Hs : K5Seated T b cells Z p blk) {ds : List Fmt.Drawn}
    (hd : drawsFit blk.rounds ds = true) (q : Nat) (k : Call)
    (hq : (shapes Z.P.x)[q]? = some (.sum k)) :
    drawsOk k ((ds.drop (H2K5.Honest.firstOf Z.P.x q)).take (k.vs.length + 3)) = true := by
  have h1 := elems_of_fit _ _ hd
  rw [Hs.rounds] at h1
  have h2 : (rounds p).map (·.entry.drawE) =
      (VerifiableInference.Desc.First.Att.P.entriesOf 0
        (VerifiableInference.Desc.First.Att.P.script p.own)).map (·.drawE) := by
    unfold rounds
    rw [List.map_map]
    refine List.map_congr_left fun e _ => ?_
    show (if e.drawE == 0 then e else { e with work := p.work }).drawE = _
    split <;> rfl
  have h3 : (sentOf (.sum k)).length = k.vs.length + 3 :=
    sentOf_length Z.P.x _ (List.mem_of_getElem? hq)
  unfold drawsOk
  rw [beq_iff_eq, List.map_take, List.map_drop, h1, h2, ← List.map_drop, ← List.map_take, Hs.own,
    ← frontOfPart_shapes, ← h3, entriesAre_at _ _ (shapes_are_script Z.P.x) q k hq]

end Member

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.alone_partAt
#print axioms ProofFile.Honest.K5.outOf_length
#print axioms ProofFile.Honest.K5.rowOut_cut
#print axioms ProofFile.Honest.K5.frontOfPart_shapes
#print axioms ProofFile.Honest.K5.k5_cut
#print axioms ProofFile.Honest.K5.entries_length
#print axioms ProofFile.Honest.K5.entriesAre_at
#print axioms ProofFile.Honest.K5.k5_drawsOk
#print axioms ProofFile.Honest.K5.zipIdx_get
