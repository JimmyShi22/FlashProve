-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/RowKit.lean: CONDITIONAL on returns of the frame's `chainSteps`
and `play`. A KIT: general in the row, in the part and in the round.

What is here. From a run of the frame's `play` over one sub-protocol's row of parts to what a given
round of it shows. Four definitions, and nineteen statements with their proofs.

  1  `rowAt?`, `rowAt_some`, `movesTo`, `coinsIn`, `spentTo`   part number i of a row with what it
     is handed of coins; how many rounds, and how many coins of spent runs, lie in front of it
  2  `runsE_length`, `runsE_first`, `spentOf_at`, `spentOf_length`   a part's spent runs lie in the
     row's list of spent coins (`spentOf`, Law/Script.lean) from number `spentTo` on; its first run
     comes first
  3  `zipIdx_map_at`, `steps_length`, `rowSteps_at`, `chainSteps_one`, `movesTo_lt`, `row_lt`   the
     Step of a part's move number r; the Steps of a chain of one sub-protocol at whose place a half
     stands; the sub-protocol has a round for every move of the half
  4  `play_at`, `tell_said`   round number n as played is what its Step tells where the run stands
     in front of it: the input is the run's, the challenges heard and the rounds shown are those in
     front with the first n of this run's, the field `opened` is as in front of the run; its
     challenge is number n of the list
  5  `row_said`   **`rowSteps_at`, `chainSteps_one`, `play_at` and `tell_said` as one**: what round
     `movesTo` + r of the row shows is the message of move number r of part number i at that part's
     coins
  6  `headD_getD`, `leading_sayE`, `paired_sent`, `paired_drawn`, `paired_noDigest`   words: scalars
     that a part says, as the verifier's tape holds them: each with its three words reduced below
     the prime (`SumLaw.canon`, Honest/SumLaw/Reads.lean, of other writers); the tape does not see
     the sealed digest, without which a step shows the rounds to its decision

Not shown here. ONE WAY, FROM A RETURN of `chainSteps` and of `play`: that they return is not shown.
Nothing on what a move's message means. Nothing on what the parts hand on to each other (the state's
field `own`): of the state in front of a round the input and the challenges heard are said, and no
more. Of the run's stand in front of a round (`Mid`) `play_at` says these two, the rounds shown and
the field `opened`: not the challenges that the stops may read (the field `loc`). `play` IS TAKEN
WITH NO STORED RUN TO FALL BACK ON (its third argument is []), as a thread's move takes it. Of a
Step `rowSteps_at` says the move alone: not its stops, its round's entry or its number; of what is
told `tell_said` says the items in the clear alone. COINS OF THE EXTENSION FIELD ALONE: `runsE`,
`coinsIn` and `spentTo` pass over a run's coins of the base field. Nothing on what a verifier does
with a tape. Nothing on the law of any coin. NOTHING ON WHAT THE FIELD `opened` HOLDS: `play_at`
says that the rounds leave it as it was, and no more; every statement here that has a letter of type
`Mid` is at every value of that field. Nothing on soundness, on completeness or on any other
property.

Kin. `chainSteps_one` CALLS `K3.Law.AtThr.chainSteps_one` (Honest/K3/Law/Thread/OneBlock.lean, of
other writers): the same four facts in another order. Honest/K13/DebtsKit.lean has two of the four
under the same short name; Honest/K12/StepsReturn.lean the way back, from the tests to the return.
`steps_length` IS, TO THE LETTER, `SumLaw.steps_length` (Honest/SumLaw/PlaysWhole.lean, of other
writers), typed again here: the proof is one line here, two there; that file is not imported.
`headD_getD` is an instance of a lemma of that name that the library has twice
(Johnson/Desc/First/Look/KeyLaw/Mid/LevSimB.lean, OnBytes/Tie/Pv/KeyLookup/LevSimB.lean), general in
the type and in the element that an empty list hands back; a third stands at ℕ and 0
(OnBytes/Tie/Pv/KeyLookup/AdmAtPlan.lean); none is imported: by a walk over import lines the lighter
would add some 47 modules for a proof of one line. `runsE_length` and `spentOf_length`:
Honest/K5/Law/Coins.lean, of other writers, has the like two lengths over its own folder's texts of
`runsE` and `spentOf`, ending in THE SAME NUMBERS under names of its own: `runsNo ds` is, unfolded,
the sum that stands here (so `coinsIn p` is `runsNo p.spends`); `spentNo ps` is that sum over the
whole row, as `spentTo ps ps.length` is: not shown here. `spentOf_at` HAS A NEAR KIN IN THAT FILE,
`spent_at`: the same equation over that folder's texts, with `spentNo (ps.take q)` where
`spentTo ps i` stands here (unfolded, the same sum). There the part's coins are what `lendPart`
lends it, where `lendRow` has lent the row's; here they are what `rowAt?` hands of any coins of the
row. Neither is shown from the other; that file is not imported. `zipIdx_map_at`: the library has
two lemmas of that name on one list (Johnson/Road/FormsKeysDictA.lean,
OnBytes/Tie/Pv/Lookup/Ends/FoPlaneMatPubG.lean); this one speaks of a zip of two, counted from a
number on. `tell_said` HAS A STRONGER KIN IN `Small.tell_inv` (Honest/Small/PlayRow.lean, of other
writers): the same two hypotheses; that one says besides that the message fits, and what is told
whole. AS THAT FILE LAY WITH THE WRITER IT WRITES WHAT THE MOVE IS HANDED AS ⟨m.seen⟩, A `Seen` OF
ONE FIELD, WHERE `m.shown` STANDS HERE; so does `tell_move`, and `played_of_play` writes a `Mid` of
three fields (both below). THESE THREE WERE HELD IN THAT FORM ALONE. `tell_inv` is not called: by a
walk over import lines its file would lay three modules more beneath this one (itself,
Honest/Law/Thread.lean, Honest/SumLaw/PlaysWhole.lean), and its form over the field `opened` was not
at hand. `tell_yields` (Honest/Law/Play.lean) has the like without the move's return. `play_at`,
`rowSteps_at` and `row_said` have near kin in Honest/K12/Sim/RoundInFront.lean, of other writers:
`played_round` (the stand in front as the play of the first rounds; not the round's challenge),
`step_move` and `tell_move` (one part, where here a row). `played_of_play`
(Honest/Small/PlayRow.lean) writes a row's whole played list out; Honest/Small/SaidRow.lean, of
other writers, goes the other way for parts that say scalars: that such a row plays, and its list
part by part. Of the files named since `tell_said` Honest/Law/Play.lean alone lies beneath this one;
none of these statements is called. THE CLAUSE ON `opened` IN `play_at`: two files of the frame's
writers that are no part of the library yet have, as they lay with the writer, `hear_opened`
(Honest/WalkOpened.lean: hearing a challenge leaves the field: the step that `play_at` proves within
its own proof) and `play_opened` (Honest/Gap.lean: so does a whole run of `play`); neither file is
imported. `leading_sayE` HAS A NEAR KIN IN `SumLaw.scalars_rvSaid`, in the file that defines
`canon`, which is imported: the same scalars as another reader takes them off the round (`scalars`,
Johnson/Desc/Part/MaskedSum4.lean: `none` where an item is no element of the extension field, where
`leading` stops); it is not called. `paired_drawn` has a kin in `paired_sampled`
(Johnson/Desc/K13/Honest/MergeLayers.lean): what all the rounds of such a tape sampled, as one list,
where here round number n; `sampledRV_noDigest` (SampledRV.lean of that folder) says of that list
what `paired_noDigest` says of the tape. Neither of these two files is imported. That the reading
does not see the difference between an element and its `canon` is `SumLaw.canon_gl`, in the file
that defines it. Sought: by statement, to the letter and up to the bound letters, and by short name,
among the theorems of the library and of files that are no part of it yet, as they lay with the
writer; each short name that stands elsewhere read at its line beside ours. The search by statement
does not see a statement that has a binder in front of the colon where ours has it behind, or the
other way round. `play_at`, `tell_said` AND `row_said` WERE SOUGHT SO IN THEIR FORM OVER A `Seen` OF
ONE FIELD; IN THE FORM THAT STANDS HERE BY SHORT NAME ALONE: no other file that lay with the writer
declares one of the three. UNDER Honest/ MORE THAN TWO HUNDRED FILES OF THE LIBRARY WRITE
`rowSteps`, `Step.tell` OR `play` IN THEIR CODE (more than fifty write `rowSteps`): of these the
statements named above and SaidRow.lean's head were read, the others not: so the kin told here are
kin among others. Not sought by the writer: twins of the four definitions in other letters (two are
told above).
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Script
import Johnson.Desc.ProofFile.Honest.Law.Along
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Johnson.Desc.ProofFile.Honest.Law.Steps
import OnBytes.Desc.First.P1.Heard
import OnBytes.Desc.First.P1.TapeCut
import Johnson.Desc.ProofFile.Honest.SumLaw.Reads
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.OneBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open OnBytes.K.Kc (paired leading)
open OnBytes.Desc.First.P1 (sentOf drawnOf)
open VerifiableInference.Desc (Block Place Oracle)
open ProofFile.Honest.SumLaw (canon)

variable {S Cl V W X : Type}

/-! ## 1 A part of a row -/

/-- **Part number i of a row, with what it is handed of coins.** -/
def rowAt? : (ps : List (Part V W X)) → RowCoins ps → Nat → Option ((p : Part V W X) × p.Coins)
  | [], _, _ => none
  | p :: ps, c, 0 =>
    let c' : p.Coins × RowCoins ps := c
    some ⟨p, c'.1⟩
  | p :: ps, c, i + 1 =>
    let c' : p.Coins × RowCoins ps := c
    rowAt? ps c'.2 i

/-- Where the row has a part number i, it is handed something. -/
theorem rowAt_some : ∀ (ps : List (Part V W X)) (c : RowCoins ps) (i : Nat) (p : Part V W X),
    ps[i]? = some p → ∃ cp, rowAt? ps c i = some ⟨p, cp⟩
  | [], _, _, _, h => by simp at h
  | q :: ps, c, 0, p, h => by
    have e : q = p := by simpa using h
    subst e
    exact ⟨_, rfl⟩
  | q :: ps, c, i + 1, p, h =>
    rowAt_some ps (show q.Coins × RowCoins ps from c).2 i p (by simpa using h)

/-- How many rounds the parts in front of part number i have. -/
def movesTo (ps : List (Part V W X)) (i : Nat) : Nat := ((ps.take i).map (·.moves.length)).sum

/-- How many coins of the extension field the runs hold that a part spends. -/
def coinsIn (p : Part V W X) : Nat := (p.spends.map (·.2.e)).sum

/-- How many such coins the parts in front of part number i spend. -/
def spentTo (ps : List (Part V W X)) (i : Nat) : Nat := ((ps.take i).map coinsIn).sum

/-! ## 2 Its stretch of the row's spent coins -/

/-- A list of runs holds as many coins of the extension field as the runs' counts of these say. -/
theorem runsE_length : ∀ (ds : List (String × Due)) (c : CsAll ds),
    (runsE ds c).length = (ds.map (·.2.e)).sum
  | [], _ => rfl
  | d :: ds, c => by
    have e : runsE (d :: ds) c = coinsE (show Cs d.2 × CsAll ds from c).1 ++
        runsE ds (show Cs d.2 × CsAll ds from c).2 := rfl
    rw [e, List.length_append, runsE_length ds, List.map_cons, List.sum_cons]
    congr 1
    simp [coinsE]

/-- The first run's coins come first. -/
theorem runsE_first (d : String × Due) (ds : List (String × Due)) (c : Cs d.2 × CsAll ds) (j : Nat)
    (hj : j < d.2.e) : (runsE (d :: ds) c).getD j zeroE = (coinsE c.1).getD j zeroE := by
  have e : runsE (d :: ds) c = coinsE c.1 ++ runsE ds c.2 := rfl
  rw [e, List.getD_append _ _ _ _ (by simp [coinsE]; exact hj)]

/-- **A part's spent runs lie in the row's list from number `spentTo` on.** -/
theorem spentOf_at : ∀ (ps : List (Part V W X)) (c : RowCoins ps) (i : Nat) (p : Part V W X)
    (cp : p.Coins), rowAt? ps c i = some ⟨p, cp⟩ → ∀ (j : Nat), j < coinsIn p →
    (spentOf ps c).getD (spentTo ps i + j) zeroE = (runsE p.spends cp.2.1).getD j zeroE
  | [], _, _, _, _, h, _, _ => by simp [rowAt?] at h
  | q :: ps, c, 0, p, cp, h, j, hj => by
    have h' : (⟨q, (show q.Coins × RowCoins ps from c).1⟩ : (p : Part V W X) × p.Coins) =
        ⟨p, cp⟩ := Option.some.inj h
    cases h'
    have e : spentOf (q :: ps) c = runsE q.spends (show q.Coins × RowCoins ps from c).1.2.1 ++
        spentOf ps (show q.Coins × RowCoins ps from c).2 := rfl
    have z : spentTo (q :: ps) 0 = 0 := rfl
    rw [e, z, Nat.zero_add, List.getD_append _ _ _ _ (by rw [runsE_length]; exact hj)]
  | q :: ps, c, i + 1, p, cp, h, j, hj => by
    have ih := spentOf_at ps (show q.Coins × RowCoins ps from c).2 i p cp h j hj
    have e : spentOf (q :: ps) c = runsE q.spends (show q.Coins × RowCoins ps from c).1.2.1 ++
        spentOf ps (show q.Coins × RowCoins ps from c).2 := rfl
    have z : spentTo (q :: ps) (i + 1) = coinsIn q + spentTo ps i := by
      simp [spentTo, List.take_succ_cons]
    have l : (runsE q.spends (show q.Coins × RowCoins ps from c).1.2.1).length = coinsIn q :=
      runsE_length _ _
    have a : coinsIn q + spentTo ps i + j - coinsIn q = spentTo ps i + j := by omega
    rw [e, z, List.getD_append_right _ _ _ _ (by rw [l]; omega), l, a]
    exact ih

/-- The row's list holds as many coins as all its parts spend. -/
theorem spentOf_length : ∀ (ps : List (Part V W X)) (c : RowCoins ps),
    (spentOf ps c).length = spentTo ps ps.length
  | [], _ => rfl
  | q :: ps, c => by
    have e : spentOf (q :: ps) c = runsE q.spends (show q.Coins × RowCoins ps from c).1.2.1 ++
        spentOf ps (show q.Coins × RowCoins ps from c).2 := rfl
    have z : spentTo (q :: ps) (q :: ps).length = coinsIn q + spentTo ps ps.length := by
      simp [spentTo, List.take_succ_cons]
    rw [e, List.length_append, runsE_length, spentOf_length ps, z]
    rfl

/-! ## 3 Its Steps -/

/-- Pairs with their numbers, mapped: member number r. -/
theorem zipIdx_map_at {α β γ : Type} (f : (α × β) × Nat → γ) : ∀ (rs : List α) (mvs : List β)
    (i r : Nat) (x : α) (mv : β), rs[r]? = some x → mvs[r]? = some mv →
    (((rs.zip mvs).zipIdx i).map f)[r]? = some (f ((x, mv), i + r))
  | [], _, _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, h => by simp at h
  | a :: rs, b :: mvs, i, 0, x, mv, h1, h2 => by
    have e1 : a = x := by simpa using h1
    have e2 : b = mv := by simpa using h2
    subst e1 e2
    rfl
  | a :: rs, b :: mvs, i, r + 1, x, mv, h1, h2 => by
    have ih := zipIdx_map_at f rs mvs (i + 1) r x mv (by simpa using h1) (by simpa using h2)
    have e : i + 1 + r = i + (r + 1) := by omega
    rw [e] at ih
    exact ih

/-- A part has as many Steps as the fewer of its moves and the rounds handed to it. -/
theorem steps_length (p : Part V W X) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins) :
    (p.steps name a rs v c).length = min rs.length p.moves.length := by
  simp [Part.steps]

/-- **The Step of move number r of part number i**, where the sub-protocol has a round for it. -/
theorem rowSteps_at (name : String) (a : Place) (v : Option V) : ∀ (ps : List (Part V W X))
    (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle)) (c : RowCoins ps) (i : Nat)
    (p : Part V W X) (cp : p.Coins), rowAt? ps c i = some ⟨p, cp⟩ → ∀ (r : Nat)
    (mv : Move (Handed p.takes p.spends p.carries) W X), p.moves[r]? = some mv →
    movesTo ps i + r < rs.length →
    ∃ s, (rowSteps name a v ps j rs c)[movesTo ps i + r]? = some s ∧
      s.move = some ⟨fun _ => mv.say cp, mv.hand⟩
  | [], _, _, _, _, _, _, h, _, _, _, _ => by simp [rowAt?] at h
  | q :: ps, j, rs, c, 0, p, cp, h, r, mv, hm, hr => by
    have h' : (⟨q, (show q.Coins × RowCoins ps from c).1⟩ : (p : Part V W X) × p.Coins) =
        ⟨p, cp⟩ := Option.some.inj h
    cases h'
    have z : movesTo (q :: ps) 0 = 0 := rfl
    rw [z, Nat.zero_add] at hr ⊢
    have hr2 : r < q.moves.length := (List.getElem?_eq_some_iff.1 hm).1
    have hx : (rs.take q.moves.length)[r]? =
        some ((rs.take q.moves.length)[r]'(by rw [List.length_take]; omega)) :=
      List.getElem?_eq_getElem _
    show ∃ s, (q.steps name ⟨a, j⟩ (rs.take q.moves.length) v
        (show q.Coins × RowCoins ps from c).1 ++
      rowSteps name a v ps (j + 1) (rs.drop q.moves.length)
        (show q.Coins × RowCoins ps from c).2)[r]? = some s ∧ _
    rw [List.getElem?_append_left (by rw [steps_length, List.length_take]; omega)]
    exact ⟨_, zipIdx_map_at _ _ _ 0 r _ mv hx hm, rfl⟩
  | q :: ps, j, rs, c, i + 1, p, cp, h, r, mv, hm, hr => by
    have z : movesTo (q :: ps) (i + 1) = q.moves.length + movesTo ps i := by
      simp [movesTo, List.take_succ_cons]
    rw [z] at hr ⊢
    obtain ⟨s, h1, h2⟩ := rowSteps_at name a v ps (j + 1) (rs.drop q.moves.length)
      (show q.Coins × RowCoins ps from c).2 i p cp h r mv hm (by rw [List.length_drop]; omega)
    refine ⟨s, ?_, h2⟩
    show (q.steps name ⟨a, j⟩ (rs.take q.moves.length) v (show q.Coins × RowCoins ps from c).1 ++
      rowSteps name a v ps (j + 1) (rs.drop q.moves.length)
        (show q.Coins × RowCoins ps from c).2)[q.moves.length + movesTo ps i + r]? = some s
    have e : q.moves.length + movesTo ps i + r -
        min (min q.moves.length rs.length) q.moves.length = movesTo ps i + r := by omega
    rw [List.getElem?_append_right (by rw [steps_length, List.length_take]; omega), steps_length,
      List.length_take, e]
    exact h1

/-- **The Steps of a chain of one sub-protocol at whose place a half stands.** -/
theorem chainSteps_one {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {blk : Block S Cl} {hs : List (Placed V W X)} {h : Placed V W X}
    {l : List (Step W X)} (hl : chainSteps B rows look v [blk] hs = .ok l)
    (hh : hs.find? (fun h => h.place == blk.place) = some h) :
    ∃ c, lendRow B rows look blk.place h.parts 0 = .ok c ∧ l = h.steps blk v c ∧
      blk.oracles.length = blk.rounds.length ∧ h.rounds = blk.rounds.length := by
  obtain ⟨a, b, c, hc, e⟩ := K3.Law.AtThr.chainSteps_one B rows look v blk hs h hh l hl
  exact ⟨c, hc, e, a, b⟩

/-- A move of a part of the row has a number below the number of all the row's moves. -/
theorem movesTo_lt : ∀ (ps : List (Part V W X)) (i : Nat) (p : Part V W X) (r : Nat),
    ps[i]? = some p → r < p.moves.length → movesTo ps i + r < movesTo ps ps.length
  | [], _, _, _, h, _ => by simp at h
  | q :: ps, 0, p, r, h, hr => by
    have e : q = p := by simpa using h
    subst e
    simp only [movesTo, List.take_zero, List.map_nil, List.sum_nil, List.length_cons,
      List.take_succ_cons, List.map_cons, List.sum_cons]
    omega
  | q :: ps, i + 1, p, r, h, hr => by
    have ih := movesTo_lt ps i p r (by simpa using h) hr
    simp only [movesTo, List.length_cons, List.take_succ_cons, List.map_cons, List.sum_cons]
      at ih ⊢
    omega

/-- **The sub-protocol has a round for every move of the half.** -/
theorem row_lt {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {blk : Block S Cl} {hs : List (Placed V W X)} {h : Placed V W X}
    {l : List (Step W X)} (hl : chainSteps B rows look v [blk] hs = .ok l)
    (hh : hs.find? (fun h => h.place == blk.place) = some h) (i : Nat) (p : Part V W X) (r : Nat)
    (hp : h.parts[i]? = some p) (hr : r < p.moves.length) :
    movesTo h.parts i + r < blk.rounds.length := by
  obtain ⟨_, _, _, _, hrd⟩ := chainSteps_one hl hh
  have e : h.rounds = movesTo h.parts h.parts.length := by
    unfold Placed.rounds movesTo
    rw [foldl_moves, Nat.zero_add, List.take_length]
  rw [← hrd, e]
  exact movesTo_lt h.parts i p r hp hr

/-! ## 4 A round as played -/

/-- **Round number n as played is what its Step tells where the run stands in front of it.** -/
theorem play_at : ∀ (l : List (Step W X)) (ds : List Fmt.Drawn) (m : Mid W X)
    (y : List Played × Mid W X), play l ds [] m = .ok y → ∀ (n : Nat) (s : Step W X),
    l[n]? = some s →
    ∃ (mn : Mid W X) (x : Told), mn.st.input = m.st.input ∧
      mn.st.heard = m.st.heard ++ ds.take n ∧ mn.seen = m.seen ++ roundsOf (y.1.take n) ∧
      mn.opened = m.opened ∧
      s.tell none mn = .ok x ∧ ((roundsOf y.1)[n]?).map (·.vals) = some x.vals ∧
      ((roundsOf y.1)[n]?).map (·.drawn) = ds[n]?
  | [], _, _, _, _, _, _, hs => by simp at hs
  | _ :: _, [], _, _, h, _, _, _ => by simp [play] at h
  | s0 :: ss, d :: ds, m, y, h, 0, s, hs => by
    obtain ⟨x, m', z, hx, -, -, rfl⟩ := play_cons_ok h
    have e : s0 = s := by simpa using hs
    subst e
    exact ⟨m, x, rfl, by simp, by simp [roundsOf], rfl, hx, by simp [roundsOf], by simp [roundsOf]⟩
  | s0 :: ss, d :: ds, m, y, h, n + 1, s, hs => by
    obtain ⟨x, m', z, -, hm, hz, rfl⟩ := play_cons_ok h
    obtain ⟨mn, x', e1, e2, e3, eo, e4, e5, e6⟩ := play_at ss ds m' z hz n s (by simpa using hs)
    obtain ⟨i1, -, i3⟩ := hear_mid hm
    have i2 := hear_heard hm
    have io : m'.opened = m.opened := by
      unfold Step.hear at hm
      cases hv : s0.move with
      | none =>
        simp only [hv] at hm
        cases hm
        rfl
      | some mv =>
        simp only [hv] at hm
        split at hm
        · cases hm
        · cases hm
          rfl
    refine ⟨mn, x', e1.trans i1, ?_, ?_, eo.trans io, e4, ?_, ?_⟩
    · rw [e2, i2]
      simp
    · rw [e3, i3]
      simp [roundsOf]
    · simpa [roundsOf] using e5
    · simpa [roundsOf] using e6

/-- What a Step with a move tells is the move's message. -/
theorem tell_said {s : Step W X} {b : Option Fmt.RoundView} {m : Mid W X} {x : Told}
    {mv : Move Unit W X} (h : s.tell b m = .ok x) (hm : s.move = some mv) :
    ∃ z, mv.say () m.shown m.st = .ok z ∧ x.vals = z.vals.map Said.got := by
  cases hst : s.stop m.loc s.nth with
  | some e => simp [Step.tell, hst] at h
  | none =>
    cases hz : mv.say () m.shown m.st with
    | error e => simp [Step.tell, hst, hm, hz] at h
    | ok z =>
      cases hf : z.fits s.decl s.oracles with
      | false => simp [Step.tell, hst, hm, hz, hf] at h
      | true =>
        simp [Step.tell, hst, hm, hz, hf] at h
        subst h
        exact ⟨z, rfl, rfl⟩

/-! ## 5 The four as one -/

/-- **What a round of a played row shows is its move's message at its part's coins.** The round's
number in the row is `movesTo` + r. st: the prover's state in front of that round. The move is
handed what `m` shows with the rounds of this run in front of that round laid behind: the field
`opened` as `m` has it. `hr` follows from the other hypotheses (`row_lt`, once `hp` is read as
`h.parts[i]? = some p`, which is not shown here): it is asked, so that the proof need not go that
way. -/
theorem row_said {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {blk : Block S Cl} {hs : List (Placed V W X)} {h : Placed V W X}
    {l : List (Step W X)} (hl : chainSteps B rows look v [blk] hs = .ok l)
    (hh : hs.find? (fun h => h.place == blk.place) = some h) {c : RowCoins h.parts}
    (hc : lendRow B rows look blk.place h.parts 0 = .ok c) {ds : List Fmt.Drawn} {m : Mid W X}
    {y : List Played × Mid W X} (hy : play l ds [] m = .ok y) (i : Nat) (p : Part V W X)
    (cp : p.Coins) (hp : rowAt? h.parts c i = some ⟨p, cp⟩) (r : Nat)
    (mv : Move (Handed p.takes p.spends p.carries) W X) (hm : p.moves[r]? = some mv)
    (hr : movesTo h.parts i + r < blk.rounds.length) :
    ∃ (st : State W X) (z : Sending), st.input = m.st.input ∧
      st.heard = m.st.heard ++ ds.take (movesTo h.parts i + r) ∧
      mv.say cp (m.shown.plus (roundsOf (y.1.take (movesTo h.parts i + r)))) st = .ok z ∧
      ((roundsOf y.1)[movesTo h.parts i + r]?).map (·.vals) = some (z.vals.map Said.got) ∧
      ((roundsOf y.1)[movesTo h.parts i + r]?).map (·.drawn) = ds[movesTo h.parts i + r]? := by
  obtain ⟨c', hc', rfl, ho, _⟩ := chainSteps_one hl hh
  obtain rfl : c' = c := Except.ok.inj (hc'.symm.trans hc)
  obtain ⟨s, hs, hmv⟩ := rowSteps_at blk.name blk.place v h.parts 0 (blk.rounds.zip blk.oracles) c'
    i p cp hp r mv hm (by rw [List.length_zip, ho, Nat.min_self]; exact hr)
  obtain ⟨mn, x, e1, e2, e3, eo, e4, e5, e6⟩ := play_at _ ds m y hy _ s hs
  obtain ⟨z, hz, hv⟩ := tell_said e4 hmv
  have es : mn.shown = m.shown.plus (roundsOf (y.1.take (movesTo h.parts i + r))) := by
    show (⟨mn.seen, mn.opened⟩ : Seen) =
      ⟨m.seen ++ roundsOf (y.1.take (movesTo h.parts i + r)), m.opened⟩
    rw [e3, eo]
  exact ⟨mn.st, z, e1, e2, by rw [← es]; exact hz, by rw [e5, hv], e6⟩

/-! ## 6 Words -/

/-- A list's first member, by its number. -/
theorem headD_getD (l : List E) : l.headD zeroE = l.getD 0 zeroE := by
  cases l <;> rfl

/-- Scalars that a part says, as the verifier's tape takes them off the round. -/
theorem leading_sayE : ∀ l : List E, leading ((sayE l).vals.map Said.got) = l.map canon
  | [] => rfl
  | x :: l => congrArg (canon x :: ·) (leading_sayE l)

/-- What round number n of a tape made of a view's rounds sent. -/
theorem paired_sent : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry) (n : Nat),
    sentOf ((paired rs es).drop n) = ((rs[n]?).map fun r => leading r.vals).getD []
  | [], _, n => by simp [paired, sentOf]
  | _ :: _, [], 0 => rfl
  | _ :: _, _ :: _, 0 => rfl
  | _ :: rs, [], n + 1 => paired_sent rs [] n
  | _ :: rs, _ :: es, n + 1 => paired_sent rs es n

/-- What round number n of such a tape sampled. -/
theorem paired_drawn : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry) (n : Nat),
    drawnOf ((paired rs es).drop n) =
      ((rs[n]?).map fun r => r.drawn.elems.map E.ofTriple).getD []
  | [], _, n => by simp [paired, drawnOf]
  | _ :: _, [], 0 => rfl
  | _ :: _, _ :: _, 0 => rfl
  | _ :: rs, [], n + 1 => paired_drawn rs [] n
  | _ :: rs, _ :: es, n + 1 => paired_drawn rs es n

/-- The tape does not see the sealed digest. -/
theorem paired_noDigest : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry),
    paired (rs.map VerifiableInference.Desc.noDigest) es = paired rs es
  | [], _ => rfl
  | r :: rs, [] => congrArg (OnBytes.K.Kc.flatOf r none :: ·) (paired_noDigest rs [])
  | r :: rs, e :: es => congrArg (OnBytes.K.Kc.flatOf r (some e) :: ·) (paired_noDigest rs es)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.rowAt?
#print axioms ProofFile.Honest.K4.rowAt_some
#print axioms ProofFile.Honest.K4.movesTo
#print axioms ProofFile.Honest.K4.coinsIn
#print axioms ProofFile.Honest.K4.spentTo
#print axioms ProofFile.Honest.K4.runsE_length
#print axioms ProofFile.Honest.K4.runsE_first
#print axioms ProofFile.Honest.K4.spentOf_at
#print axioms ProofFile.Honest.K4.spentOf_length
#print axioms ProofFile.Honest.K4.zipIdx_map_at
#print axioms ProofFile.Honest.K4.steps_length
#print axioms ProofFile.Honest.K4.rowSteps_at
#print axioms ProofFile.Honest.K4.chainSteps_one
#print axioms ProofFile.Honest.K4.movesTo_lt
#print axioms ProofFile.Honest.K4.row_lt
#print axioms ProofFile.Honest.K4.play_at
#print axioms ProofFile.Honest.K4.tell_said
#print axioms ProofFile.Honest.K4.row_said
#print axioms ProofFile.Honest.K4.headD_getD
#print axioms ProofFile.Honest.K4.leading_sayE
#print axioms ProofFile.Honest.K4.paired_sent
#print axioms ProofFile.Honest.K4.paired_drawn
#print axioms ProofFile.Honest.K4.paired_noDigest
