-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/RowIs.lean: the row of an attention segment's own rounds (kind
K5) beside its simulators (k5Pairs, Honest/K5/Side.lean), MEMBER BY MEMBER: which part, which
simulator and which declared rounds each member of a side has (Side.members, Honest/Side.lean); and
the side's test on row and sub-protocol. Definitions, and statements with their proofs. No coin, no
distribution, no run occurs.

  K5Block        what is asked of the member of the description at the place: four of K5Seated's
                 fields (Honest/K5/Law/Seated.lean); no thread
  block_kind     the kind's own sub-protocol at the seat's numbers meets it
  partOf5, simOf5, stretchOf   part number j by its shape, lifted; the simulator beside it; the
                 rounds from the part's first round on
  row_is         the row is made of these
  membersOf_mem  a member of any row, by its number: general in the row
  member_at      **a member of K5's side is the literal (j, stretchOf, partOf5, simOf5)**
  rounds_drawn, entries_of_part, firstOf_sent   the verifier's declared rounds, part by part
  stretch_like   what a part's rounds state and draw: the call's entries' numbers, up to the work
                 bits; at a round by itself: its n scalars
  shapes_ok      the verifier's test on a call's shape, off one test with code on public numbers
  sum_stage, shapes_plan   that test says yes wherever the verifier's own test on the plan does
  k5_fits        **Side.fits**

CONDITIONAL: member_at: the side's row is K5's · stretch_like: K5Block · k5_fits: both ·
shapes_ok | shapes_plan: the test named says yes · entries_of_part: its two premises ·
K5Seated.block: K5Seated. The other statements (on lists, the cut, the declared rounds and the row's
text) have no premise.

Limits. Lists and numbers alone. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Side
import Johnson.Desc.ProofFile.Honest.K5.Law.Plays
import Johnson.Desc.ProofFile.Honest.K5.Law.GoodForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E)
open VerifiableInference.Desc (Block Place Oracle)
open VerifiableInference.Desc.Part.MaskedSum (Call entries shapeOk)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (entriesOf script)
open H2K5.Honest (shapes cut PartShape K5In)
open ProofFile.Honest.SumLaw (StatedBy)

/-! ## 1 Lists -/

theorem foldl_add_sum : ∀ (l : List Nat) (a : Nat), l.foldl (· + ·) a = a + l.sum
  | [], a => (Nat.add_zero a).symm
  | x :: l, a => by
    rw [List.foldl_cons, foldl_add_sum l (a + x), List.sum_cons, Nat.add_assoc]

/-- A part's first round, as a sum. -/
theorem firstOf_sum (x : OnBytes.Params.AttentionRounds) (j : Nat) :
    H2K5.Honest.firstOf x j = ((cut x).take j).sum := by
  unfold H2K5.Honest.firstOf
  rw [foldl_add_sum, Nat.zero_add]

/-- **A member of a row, by its number**: general in the row. -/
theorem membersOf_mem {V W X Pb : Type} : ∀ (row : List (Part V W X × Sim Pb)) (j0 : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (u : Member V W X Pb), u ∈ membersOf row j0 rs →
    ∃ t y, row[t]? = some y ∧ u = ⟨j0 + t,
      (rs.drop ((row.map (·.1.moves.length)).take t).sum).take y.1.moves.length, y.1, y.2⟩
  | [], _, _, _, h => by cases h
  | x :: l, j0, rs, u, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨0, x, rfl, rfl⟩
    · obtain ⟨t, y, hy, rfl⟩ := membersOf_mem l (j0 + 1) (rs.drop x.1.moves.length) u h
      refine ⟨t + 1, y, hy, ?_⟩
      rw [List.drop_drop, List.map_cons, List.take_succ_cons, List.sum_cons,
        show j0 + 1 + t = j0 + (t + 1) by omega]

/-! ## 2 The row -/

variable {W₀ Rc Xi Tr X Pb S Cl : Type}

/-- **What is asked of the member at the place.** It is a definition: a premise's form. The
verifier's test on the plan is no field: the one statement that wants something of it (k5_good,
Honest/K5/Law/Good.lean) asks the weaker test of shapes_ok, which shapes_plan draws from it. -/
structure K5Block (blk : Block S Cl) (Z : Seat5) (p : P.Par) : Prop where
  /-- it stands at the place of the public data -/
  place : blk.place = Z.place
  /-- its rounds are the verifier's, at the numbers p -/
  rounds : blk.rounds = P.rounds p
  /-- no round has an oracle message -/
  oracles : blk.oracles = (P.rounds p).map fun _ => []
  /-- the numbers of these rounds are the public data's -/
  own : p.own = Z.P.x

/-- **It can be met**: the kind's own sub-protocol (attentionKind, Johnson/Desc/First/Att/K5AttentionKind.lean), at the
seat's segment and numbers, at every seat of the verifier's, list of claims, number of work bits and
list of messages in front. A description's member may be that sub-protocol wrapped: of a wrapped one
nothing is said here. -/
theorem block_kind (seat : P.Seat S)
    (claims : List (String × (Nat → S → Except String (List Cl × S)))) (Z : Seat5) (work : Nat)
    (before : List (Nat × Nat)) :
    K5Block (P.attentionKind seat claims ⟨Z.link, 3, work, Z.P.x, before⟩) Z
      ⟨Z.link, 3, work, Z.P.x, before⟩ :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- K5Seated holds these four. -/
theorem K5Seated.block {Bk : ProverCoinCounts}
    {T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
    {cells : Tr → Cells} {Z : Seat5} {p : P.Par} {blk : Block S Cl}
    (H : K5Seated T b cells Z p blk) : K5Block blk Z p :=
  ⟨H.place, H.rounds, H.oracles, H.own⟩

/-- Part number j of the row, by its shape: the row's own text (partAt, Honest/K5/Law/Plays.lean),
lifted as the kind's half lifts it. -/
def partOf5 (cells : Tr → Cells) (Z : Seat5) (j : Nat) (s : PartShape) :
    Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  (K5.partAt Z.place (chalOf Z) (jobs Z.P) (s, j)).lift (fun _ => ())
    (fun t => inOf Z.P.S Z.link (cells t.trace)) (fun _ => ()) fun x _ => x

/-- The simulator beside it. -/
def simOf5 (Z : Seat5) (j : Nat) (s : PartShape) : Sim Pb :=
  match s with
  | .sum k => sumSim ⟨Z.place, j⟩ k
  | .one 0 => quietSim ⟨Z.place, j⟩
  | .one n => scalarsSim ⟨Z.place, j⟩ n

/-- The rounds of part number j: from the part's first round on, as many as the part has. -/
def stretchOf (blk : Block S Cl) (Z : Seat5) (j : Nat) : List (Fmt.DeclaredRound × List Oracle) :=
  ((blk.rounds.zip blk.oracles).drop (H2K5.Honest.firstOf Z.P.x j)).take ((cut Z.P.x).getD j 0)

/-- **The row is made of these.** No premise. -/
theorem row_is (cells : Tr → Cells) (Z : Seat5) :
    (k5Pairs cells Z : List (Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X × Sim Pb)) =
      (shapes Z.P.x).zipIdx.map fun s => (partOf5 cells Z s.2 s.1, simOf5 Z s.2 s.1) := by
  unfold k5Pairs
  rw [k5Half_parts]
  unfold rowParts simsOf
  rw [List.map_map, List.zip_map']
  rfl

/-- The row's numbers of moves are the cut. No premise. -/
theorem row_cut (cells : Tr → Cells) (Z : Seat5) :
    (k5Pairs cells Z : List (Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X × Sim Pb)).map
      (·.1.moves.length) = cut Z.P.x := by
  rw [← half_cut (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells Z]
  unfold k5Pairs
  have e : ∀ l : List (Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X × Sim Pb),
      l.map (·.1.moves.length) = (l.map Prod.fst).map (·.moves.length) := fun l => by
    rw [List.map_map]
    rfl
  rw [e, List.map_fst_zip]
  rw [k5Half_parts]
  unfold rowParts simsOf
  simp only [List.length_map, List.length_zipIdx, Nat.le_refl]

variable {σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {cells : Tr → Cells}
  {Z : Seat5} {p : P.Par}

/-- **A member of K5's side, written out.** CONDITIONAL: the side's row is K5's. -/
theorem member_at (hr : σ.row = k5Pairs cells Z)
    {u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} (hu : u ∈ σ.members) :
    ∃ j s, (shapes Z.P.x)[j]? = some s ∧
      u = ⟨j, stretchOf σ.block Z j, partOf5 cells Z j s, simOf5 Z j s⟩ := by
  unfold Side.members at hu
  obtain ⟨t, y, hy, rfl⟩ := membersOf_mem _ _ _ _ hu
  have hc := row_cut (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) (Pb := Pb) cells Z
  rw [hr] at hy ⊢
  have hlen : (cut Z.P.x)[t]? = some y.1.moves.length := by
    rw [← hc, List.getElem?_map, hy]
    rfl
  rw [row_is, List.getElem?_map, List.getElem?_zipIdx] at hy
  cases hs : (shapes Z.P.x)[t]? with
  | none =>
    rw [hs] at hy
    cases hy
  | some s =>
    rw [hs] at hy
    obtain rfl := Option.some.inj hy
    refine ⟨t, s, hs, ?_⟩
    unfold stretchOf
    rw [hc, firstOf_sum, List.getD_eq_getElem?_getD, hlen, Nat.zero_add]
    rfl

/-! ## 3 What a part's rounds state and draw -/

/-- The entries of the part number j that is a masked sumcheck are the call's own. -/
theorem entries_of_part : ∀ (L : List PartShape) (es : List Fmt.Entry), EntriesAre L es →
    ∀ (j : Nat) (k : Call), L[j]? = some (.sum k) →
      (es.drop ((L.take j).flatMap sentOf).length).take (entries k).length = entries k
  | [], _, _, _, _, h => by cases h
  | .sum k' :: l, es, ⟨es', e, h'⟩, 0, k, h => by
    obtain rfl : k' = k := by
      have h1 := Option.some.inj h
      cases h1
      rfl
    subst e
    exact List.take_left' rfl
  | .one n :: l, es, _, 0, k, h => by
    have h1 := Option.some.inj h
    cases h1
  | .sum k' :: l, es, ⟨es', e, h'⟩, j + 1, k, h => by
    subst e
    have ih := entries_of_part l es' h' j k h
    have hl : (entries k').length = (sentOf (.sum k')).length := by
      have := congrArg List.length (SumLaw.entries_nums k')
      rw [List.length_map, List.length_map] at this
      exact this
    rw [List.take_succ_cons, List.flatMap_cons, List.length_append, ← hl, ← List.drop_drop,
      List.drop_left' rfl]
    exact ih
  | .one n :: l, es, ⟨e0, es', e, _, h'⟩, j + 1, k, h => by
    subst e
    have ih := entries_of_part l es' h' j k h
    rw [List.take_succ_cons, List.flatMap_cons, List.length_append]
    show ((e0 :: es').drop (1 + _)).take _ = _
    rw [Nat.add_comm, List.drop_succ_cons]
    exact ih

/-- What the frame's test on challenges reads of the verifier's declared rounds: the work bits are
no part of it. -/
theorem rounds_drawn (p : P.Par) :
    ((P.rounds p).zip ((P.rounds p).map fun _ => ([] : List Oracle))).map (fun r =>
        (r.1.entry.name, r.1.entry.drawE, r.1.entry.drawNZ, r.1.entry.poss, r.1.entry.trits)) =
      (entriesOf 0 (script p.own)).map fun e => (e.name, e.drawE, e.drawNZ, e.poss, e.trits) := by
  unfold P.rounds
  induction entriesOf 0 (script p.own) with
  | nil => rfl
  | cons e es ih =>
    rw [List.map_cons, List.map_cons, List.zip_cons_cons, List.map_cons, List.map_cons, ih]
    congr 1
    show ((if e.drawE == 0 then e else { e with work := p.work }).name,
      (if e.drawE == 0 then e else { e with work := p.work }).drawE,
      (if e.drawE == 0 then e else { e with work := p.work }).drawNZ,
      (if e.drawE == 0 then e else { e with work := p.work }).poss,
      (if e.drawE == 0 then e else { e with work := p.work }).trits) = _
    split <;> rfl

/-- As many rounds in front of part number j as the parts in front send in. -/
theorem firstOf_sent (x : OnBytes.Params.AttentionRounds) (j : Nat) :
    H2K5.Honest.firstOf x j = (((shapes x).take j).flatMap sentOf).length := by
  rw [firstOf_sum]
  unfold cut
  rw [← List.map_take, List.length_flatMap]
  refine congrArg List.sum (List.map_congr_left fun s hs => ?_)
  exact (sentOf_length x s (List.mem_of_mem_take hs)).symm

/-- **What a part's rounds state and draw.** CONDITIONAL on K5Block. -/
theorem stretch_like (hB : K5Block σ.block Z p) {j : Nat} {s : PartShape}
    (hq : (shapes Z.P.x)[j]? = some s) :
    match s with
    | .sum k => StatedBy (scalarsOf k) (stretchOf σ.block Z j) ∧
        DrawnLike (entries k) (stretchOf σ.block Z j)
    | .one n => StatedBy [n] (stretchOf σ.block Z j) := by
  have hmem : s ∈ shapes Z.P.x := List.mem_of_getElem? hq
  have hcut : (cut Z.P.x).getD j 0 = (sentOf s).length := by
    unfold cut
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hq]
    exact (sentOf_length Z.P.x s hmem).symm
  have hsplit : shapes Z.P.x = (shapes Z.P.x).take j ++ s :: (shapes Z.P.x).drop (j + 1) := by
    have hj : j < (shapes Z.P.x).length := (List.getElem?_eq_some_iff.1 hq).1
    have e : (shapes Z.P.x)[j] = s := (List.getElem?_eq_some_iff.1 hq).2
    rw [← e, List.cons_getElem_drop_succ, List.take_append_drop]
  have hst : StatedBy (sentOf s) (stretchOf σ.block Z j) := by
    have h0 := rounds_stated p
    rw [hB.own, hsplit, List.flatMap_append, List.flatMap_cons] at h0
    have h1 := (statedBy_split _ _ _ h0).2
    have h2 := (statedBy_split _ _ _ h1).1
    unfold stretchOf
    rw [hB.rounds, hB.oracles, firstOf_sent, hcut]
    exact h2
  cases s with
  | one n => exact hst
  | sum k =>
    refine ⟨hst, ?_⟩
    have hE := entries_of_part _ _ (shapes_are_script Z.P.x) j k hq
    have hl : (entries k).length = (sentOf (.sum k)).length := by
      have := congrArg List.length (SumLaw.entries_nums k)
      rw [List.length_map, List.length_map] at this
      exact this
    unfold DrawnLike stretchOf
    rw [hB.rounds, hB.oracles, List.map_take, List.map_drop, rounds_drawn, hB.own, hcut, ← hl,
      firstOf_sent, ← List.map_drop, ← List.map_take, hE]

/-- The verifier's test on a call's shape, off one test with code on the public numbers. -/
theorem shapes_ok {x : OnBytes.Params.AttentionRounds} (hx : ((shapes x).all fun s =>
      match s with
      | .sum k => shapeOk k
      | .one _ => true) = true) {j : Nat} {k : Call}
    (hq : (shapes x)[j]? = some (.sum k)) : shapeOk k = true :=
  List.all_eq_true.1 hx _ (List.mem_of_getElem? hq)

/-- A sumcheck among the parts has the variables and the ends of a sumcheck among the stages. -/
theorem sum_stage : ∀ (st : List P.Stage) (lead : Nat) (k : Call),
    PartShape.sum k ∈ H2K5.Honest.shapesOf lead st →
      ∃ e, k.ends = some e ∧ P.Stage.sum k.vs e ∈ st
  | [], _, _, h => by cases h
  | .scalars n :: l, lead, k, h =>
    (sum_stage l (lead + n) k h).imp fun _ h => ⟨h.1, List.mem_cons_of_mem _ h.2⟩
  | .sum vs e :: l, lead, k, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h
      exact ⟨e, rfl, List.mem_cons_self⟩
    · exact (sum_stage l 0 k h).imp fun _ h => ⟨h.1, List.mem_cons_of_mem _ h.2⟩
  | .batch _ :: l, lead, k, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h
    · exact (sum_stage l 0 k h).imp fun _ h => ⟨h.1, List.mem_cons_of_mem _ h.2⟩
  | .point _ :: l, lead, k, h => by
    rcases List.mem_cons.1 h with h | h
    · cases h
    · exact (sum_stage l 0 k h).imp fun _ h => ⟨h.1, List.mem_cons_of_mem _ h.2⟩

/-- **That test says yes wherever the verifier's own test on the plan does** (planOk,
Johnson/Desc/First/Att/K5AttentionKind.lean): the test on a shape reads no lead. -/
theorem shapes_plan {p : P.Par} (h : P.planOk p = true) : ((shapes p.own).all fun s =>
      match s with
      | .sum k => shapeOk k
      | .one _ => true) = true := by
  unfold P.planOk at h
  rw [Bool.and_eq_true] at h
  have h2 := List.all_eq_true.1 h.2
  refine List.all_eq_true.2 fun s hs => ?_
  match s, hs with
  | .one _, _ => rfl
  | .sum k, hs =>
    obtain ⟨e, he, hm⟩ := sum_stage _ 0 k hs
    have h3 : shapeOk ⟨0, k.vs, some e⟩ = true := h2 _ hm
    show shapeOk k = true
    unfold shapeOk at h3 ⊢
    rw [he]
    exact h3

/-! ## 4 The side's test -/

/-- **Row and sub-protocol fit.** CONDITIONAL on K5Block; the side's row is K5's. -/
theorem k5_fits (hB : K5Block σ.block Z p) (hr : σ.row = k5Pairs cells Z) : σ.fits = true := by
  unfold Side.fits
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hr, row_is, List.all_eq_true]
    intro y hy
    obtain ⟨t, ht⟩ := List.mem_iff_getElem?.1 hy
    rw [List.getElem?_zipIdx, List.getElem?_map, List.getElem?_zipIdx] at ht
    cases hs : (shapes Z.P.x)[t]? with
    | none =>
      rw [hs] at ht
      cases ht
    | some s =>
      rw [hs] at ht
      obtain rfl := Option.some.inj ht
      rw [hB.place]
      match s with
      | .sum _ => exact beq_self_eq_true _
      | .one 0 => exact beq_self_eq_true _
      | .one (_ + 1) => exact beq_self_eq_true _
  · have h1 : σ.half.rounds = (cut Z.P.x).sum := by
      unfold Placed.rounds Side.half
      rw [foldl_moves, Nat.zero_add, List.map_map, hr]
      exact congrArg List.sum (row_cut cells Z)
    rw [h1, hB.rounds, ← hB.own, cut_sum]
    exact beq_self_eq_true _
  · rw [hB.oracles, hB.rounds, List.length_map]
    exact beq_self_eq_true _

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.foldl_add_sum
#print axioms ProofFile.Honest.K5.firstOf_sum
#print axioms ProofFile.Honest.K5.membersOf_mem
#print axioms ProofFile.Honest.K5.block_kind
#print axioms ProofFile.Honest.K5.K5Seated.block
#print axioms ProofFile.Honest.K5.row_is
#print axioms ProofFile.Honest.K5.row_cut
#print axioms ProofFile.Honest.K5.member_at
#print axioms ProofFile.Honest.K5.entries_of_part
#print axioms ProofFile.Honest.K5.rounds_drawn
#print axioms ProofFile.Honest.K5.firstOf_sent
#print axioms ProofFile.Honest.K5.stretch_like
#print axioms ProofFile.Honest.K5.shapes_ok
#print axioms ProofFile.Honest.K5.sum_stage
#print axioms ProofFile.Honest.K5.shapes_plan
#print axioms ProofFile.Honest.K5.k5_fits
