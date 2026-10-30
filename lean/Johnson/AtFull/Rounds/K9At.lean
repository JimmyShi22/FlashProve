-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/K9At.lean: KIND K9's LOT's ROW FOR THE ROUNDS AT THE FULL SIZE, IF THREE
THINGS THAT THE LOT READS OF THE PUBLIC PART ARE THE WRITTEN ONES: EACH BLOCK OF THE LOT
(ProofFile.k9Ninth, Johnson/Desc/ProofFile/Lot/K9.lean) DECLARES NO ROUND, OR THE WRITTEN LIST THAT THE
TABLE listAt (Johnson/AtFull/Rounds/ListAt.lean) HAS AT THE NAME OF THE BLOCK's PLACE; AND SO DOES
THE BATCHING, AT EVERY GATHERER, AT A PLACE ON CHAIN 1. The laws: Johnson/AtFull/Rounds/K9.lean.
Here: the written terms, ten closed facts by Lean's kernel, two of them bent twins, and the rows.

  nameCut a   the name of the FIRST row that the written cut of the first chain has at the place a;
      "" where it has none. The table's list at "" is empty: so a member with rounds that meets its
      list has a row in the cut. That the cut has one row a place is not said here.
  k9RdW, k9BatchW   the lot's blocks' places and rounds, and the batchings', at the written places
      (spotsWritten), the written first chain's entries (esW) and the written shape's groups
      (groupsW): the first row's three written values (Johnson/AtFull/Desc/Lots/K9RowWritten.lean).
  k9_rounds_closed, k9_batch_closed   BY LEAN's KERNEL: each member declares no round, or the
      table's list at the written cut's name of its place; each batching the latter.
  k9_counts, k9_batch_count   BY LEAN's KERNEL: 75 blocks, 25 of them with rounds, 238 rounds in
      all; 25 batchings.
  k9_rounds_bent   A BENT TWIN: with one row variable more in every group there are still 25
      closings with rounds, and none meets its list.
  k9_batch_bent   A BENT TWIN: with one row more in every entry of the stretches there are still 25
      batchings, and none meets its list.
  k9_batch_other_chain   at the first batching's link and piece ON CHAIN 2 the written term
      k9BatchRdE xsW (the lot's batching's rounds under hs · he, by k9_batch_pr) gives one round
      too, while the written cut has no row there and the table's list at "" is empty.
  k9_blocks_written   hs · he · hg ⊢ the lot's blocks' places and rounds are k9RdW.
  **k9_row_by**   THE ROW: hs · he · hg · hN ⊢ for every block b of the lot: b.rounds = [] or
      b.rounds = listAt (name b.place).
  **k9_batch_by**   THE BATCHING's ROW: hs · he · hN ⊢ for every place a ON CHAIN 1 at which the lot
      supplies a maker mk, and EVERY gatherer g: (mk g).rounds = listAt (name a).
Both rows are general in name, a function from places to names: whoever joins the lots' rows lays
the written name at a place there.
  spots_chain, k9_names_closed, k9_batch_names   BY LEAN's KERNEL: every written spot stands on
      chain 1; each of the 25 members with rounds (of the 25 batchings) HAS a written spot at its
      place, and a written spot there bears the written cut's name of that place.
  **k9_row_spots, k9_batch_spots**   THE TWO ROWS AT THE WRITTEN SPOTS, WITHOUT hN AND WITHOUT A
      WORD ON THE CHAIN: for every written spot p with p.place = b.place: b.rounds = [] or
      b.rounds = listAt p.name; for every written spot p at whose place the lot supplies a maker
      mk, and every gatherer g: (mk g).rounds = listAt p.name.

THE PREMISES. hs: the places off the table of steps are the written ones. he: the first chain's
declared rounds' entries are the written ones. hg: the first state's groups are the written shape's.
hN: at the places of k9RdW's members with rounds (of k9BatchW's members) name gives the written
cut's name. NONE IS SHOWN HERE AT ANY PUBLIC FILES. hs, he, hg are the first row's. WHO IS TO GIVE
THEM, AS FAR AS IS KNOWN HERE: hs: another file's spots_written behind "Z.cuts is the written table
of steps" · he: Johnson/AtFull/Rounds/EntriesW.lean's entries_at, from the premise on the plans
· hg: nobody known here. THE LOT READS rows AND work OFF THE
PLAN's ROUNDS Z.D: so he is a premise on the plan's side beneath this lot's share of "what the
blocks declare".

Limits. The full size alone. WITHOUT a.chain = 1 THE BATCHING's ROW WOULD FAIL AT name := nameCut:
the lot's batch does not read a place's chain: shown on the written terms (k9_batch_other_chain);
the step to a Z that meets hs and he is not taken here. The closed facts hold this library's own
routines at written values against written values.

Raised limit: maxRecDepth 1000000. Nothing on soundness.

-/
import Johnson.AtFull.Rounds.K9
import Johnson.AtFull.Desc.Lots.K9RowWritten
import Johnson.AtFull.Rounds.ListAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Rounds
open VerifiableInference.Desc
open VerifiableInference.PlanWritten (cutFirstFull)
open ProofFile
open Johnson.AtFull.Desc (spotsWritten)
open Johnson.AtFull.Desc.Lots

/-- The name that the written cut of the first chain has at a place. -/
def nameCut (a : Place) : String := ((cutFirstFull.find? fun r => r.2.1 == a).map (·.1)).getD ""

/-- The lot's blocks' places and rounds at the written values. -/
def k9RdW : List PR := (k9WsE xsW).flatMap (k9RdAtE groupsW xsW)

/-- The batchings' places on chain 1 and rounds at the written values. -/
def k9BatchW : List PR := k9BatchAllE xsW

/-- **Each block declares no round, or the table's list at its place's written name.** -/
theorem k9_rounds_closed :
    k9RdW.all (fun q => q.2.isEmpty || decide (q.2 = listAt (nameCut q.1))) = true := by
  decide +kernel

/-- 75 blocks, 25 of them with rounds, 238 rounds in all. -/
theorem k9_counts : k9RdW.length = 75 ∧ (k9RdW.filter fun q => !q.2.isEmpty).length = 25 ∧
    (k9RdW.flatMap (·.2)).length = 238 := by decide +kernel

/-- **Each batching declares the table's list at its place's written name.** -/
theorem k9_batch_closed :
    k9BatchW.all (fun q => decide (q.2 = listAt (nameCut q.1))) = true := by decide +kernel

/-- 25 batchings. -/
theorem k9_batch_count : k9BatchW.length = 25 := by decide +kernel

/-- The blocks' places and rounds with one row variable more in every group. -/
def k9RdBent : List PR :=
  (k9WsE xsW).flatMap (k9RdAtE (groupsW.map fun g => { g with k := g.k + 1 }) xsW)

/-- A BENT TWIN: with one row variable more in every group there are still 25 closings with rounds,
and none meets its list. -/
theorem k9_rounds_bent :
    (k9RdBent.filter fun q => !q.2.isEmpty).length = 25 ∧
      k9RdBent.all (fun q => q.2.isEmpty || !decide (q.2 = listAt (nameCut q.1))) = true := by
  decide +kernel

/-- The batchings with one row more in every entry of the stretches. -/
def k9BatchBent : List PR :=
  k9BatchAllE (xsW.map fun x => (x.1, x.2.1.map fun e => { e with rows := e.rows + 1 }, x.2.2))

/-- A BENT TWIN: with one row more in every entry of the stretches there are still 25 batchings, and
none meets its list. -/
theorem k9_batch_bent :
    k9BatchBent.length = 25 ∧
      k9BatchBent.all (fun q => !decide (q.2 = listAt (nameCut q.1))) = true := by decide +kernel

/-- On another chain: at the first segment's batching's link and piece on chain 2 the written term
k9BatchRdE xsW gives one round too, the written cut has no row, and the table's list at "" is
empty. -/
theorem k9_batch_other_chain :
    (k9BatchRdE xsW ⟨2, some 0, 8, .K9⟩).map (·.length) = some 1 ∧
      nameCut ⟨2, some 0, 8, .K9⟩ = "" ∧ listAt "" = [] := by decide +kernel

/-- The lot's blocks' places and rounds are the written term. -/
theorem k9_blocks_written (Z : Pub) (G : Ground) (hs : spotsOf Z.cuts = some spotsWritten)
    (he : Z.D.1.map (·.entry) = esW) (hg : Z.s₀.check.frame.groups = groupsW) :
    ((k9Ninth Z).blocks G).map prOf = k9RdW := by
  rw [k9_blocks_at Z G hs he hg, walk_eq]
  rfl

/-- A block of the lot: its place and rounds are a member of the written term. -/
theorem k9_mem (Z : Pub) (G : Ground) (hs : spotsOf Z.cuts = some spotsWritten)
    (he : Z.D.1.map (·.entry) = esW) (hg : Z.s₀.check.frame.groups = groupsW)
    {b : Block First.S ProofFile.Cl} (hb : b ∈ (k9Ninth Z).blocks G) : prOf b ∈ k9RdW := by
  rw [← k9_blocks_written Z G hs he hg]
  exact List.mem_map_of_mem hb

/-- **THE ROW: each block of K9's lot declares no round, or the table's list at its place's
name.** -/
theorem k9_row_by (Z : Pub) (G : Ground) (name : Place → String)
    (hs : spotsOf Z.cuts = some spotsWritten) (he : Z.D.1.map (·.entry) = esW)
    (hg : Z.s₀.check.frame.groups = groupsW)
    (hN : ∀ q ∈ k9RdW, q.2 ≠ [] → name q.1 = nameCut q.1) :
    ∀ b ∈ (k9Ninth Z).blocks G, b.rounds = [] ∨ b.rounds = listAt (name b.place) := by
  intro b hb
  have hm : prOf b ∈ k9RdW := k9_mem Z G hs he hg hb
  by_cases h0 : b.rounds = []
  · exact Or.inl h0
  · have h := List.all_eq_true.1 k9_rounds_closed _ hm
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · exact absurd (List.isEmpty_iff.1 h) h0
    · have hn : name b.place = nameCut b.place := hN _ hm h0
      refine Or.inr ?_
      rw [hn]
      exact of_decide_eq_true h

/-- A batching that the lot supplies at a place on chain 1: the place and the rounds, at every
gatherer, are a member of the written term. -/
theorem k9_batch_in (Z : Pub) (G : Ground) (hs : spotsOf Z.cuts = some spotsWritten)
    (he : Z.D.1.map (·.entry) = esW) {a : Place} {mk : Gatherer → Block First.S ProofFile.Cl}
    (hc : a.chain = 1) (h : (k9Ninth Z).batch G a = some mk) (g : Gatherer) :
    (a, (mk g).rounds) ∈ k9BatchW := by
  have e := k9_batch_pr Z G a g
  rw [h, k9_stretches_at Z hs he, walk_eq] at e
  exact k9_batch_mem xsW a _ e.symm hc

/-- **THE BATCHING's ROW: at a place on chain 1, at every gatherer.** -/
theorem k9_batch_by (Z : Pub) (G : Ground) (name : Place → String)
    (hs : spotsOf Z.cuts = some spotsWritten) (he : Z.D.1.map (·.entry) = esW)
    (hN : ∀ q ∈ k9BatchW, name q.1 = nameCut q.1) :
    ∀ a mk, a.chain = 1 → (k9Ninth Z).batch G a = some mk →
      ∀ g, (mk g).rounds = listAt (name a) := by
  intro a mk hc h g
  have hm := k9_batch_in Z G hs he hc h g
  rw [hN _ hm]
  exact of_decide_eq_true (List.all_eq_true.1 k9_batch_closed _ hm)

/-! ### at the written spots -/

/-- Every written spot stands on chain 1. -/
theorem spots_chain : spotsWritten.all (fun p => decide (p.place.chain = 1)) = true := by
  decide +kernel

/-- The test: a written spot at the place a bears the written cut's name of a. -/
def spotNamed (a : Place) : Bool :=
  spotsWritten.all fun p => !decide (p.place = a) || decide (p.name = nameCut a)

/-- A written spot stands at the place a. -/
def spotAt (a : Place) : Bool := spotsWritten.any fun p => decide (p.place = a)

/-- Each of the 25 members with rounds has a written spot at its place, and a written spot there
bears the written cut's name. -/
theorem k9_names_closed :
    (k9RdW.filter fun q => !q.2.isEmpty && spotAt q.1).length = 25 ∧
      k9RdW.all (fun q => q.2.isEmpty || spotNamed q.1) = true := by decide +kernel

/-- The like of the 25 batchings. -/
theorem k9_batch_names :
    (k9BatchW.filter fun q => spotAt q.1).length = 25 ∧
      k9BatchW.all (fun q => spotNamed q.1) = true := by decide +kernel

/-- From a yes of spotNamed: the spot's name. -/
theorem name_of_spot {a : Place} (h : spotNamed a = true) {p : Spot} (hp : p ∈ spotsWritten)
    (e : p.place = a) : p.name = nameCut a := by
  have c := List.all_eq_true.1 h p hp
  rw [Bool.or_eq_true] at c
  rcases c with c | c
  · rw [Bool.not_eq_true', decide_eq_false_iff_not] at c
    exact absurd e c
  · exact of_decide_eq_true c

/-- **THE ROW AT THE WRITTEN SPOTS.** -/
theorem k9_row_spots (Z : Pub) (G : Ground) (hs : spotsOf Z.cuts = some spotsWritten)
    (he : Z.D.1.map (·.entry) = esW) (hg : Z.s₀.check.frame.groups = groupsW) :
    ∀ b ∈ (k9Ninth Z).blocks G, ∀ p ∈ spotsWritten, p.place = b.place →
      b.rounds = [] ∨ b.rounds = listAt p.name := by
  intro b hb p hp e
  by_cases h0 : b.rounds = []
  · exact Or.inl h0
  · have hm : prOf b ∈ k9RdW := k9_mem Z G hs he hg hb
    have c := List.all_eq_true.1 k9_names_closed.2 _ hm
    rw [Bool.or_eq_true] at c
    rcases c with c | c
    · exact absurd (List.isEmpty_iff.1 c) h0
    · rw [name_of_spot c hp e]
      exact k9_row_by Z G nameCut hs he hg (fun _ _ _ => rfl) b hb

/-- **THE BATCHING's ROW AT THE WRITTEN SPOTS, at every gatherer.** -/
theorem k9_batch_spots (Z : Pub) (G : Ground) (hs : spotsOf Z.cuts = some spotsWritten)
    (he : Z.D.1.map (·.entry) = esW) :
    ∀ p ∈ spotsWritten, ∀ mk, (k9Ninth Z).batch G p.place = some mk →
      ∀ g, (mk g).rounds = listAt p.name := by
  intro p hp mk h g
  have hc : p.place.chain = 1 := of_decide_eq_true (List.all_eq_true.1 spots_chain p hp)
  have hm := k9_batch_in Z G hs he hc h g
  rw [name_of_spot (List.all_eq_true.1 k9_batch_names.2 _ hm) hp rfl]
  exact of_decide_eq_true (List.all_eq_true.1 k9_batch_closed _ hm)

end Johnson.AtFull.Rounds

#print axioms Johnson.AtFull.Rounds.k9_rounds_closed
#print axioms Johnson.AtFull.Rounds.k9_counts
#print axioms Johnson.AtFull.Rounds.k9_batch_closed
#print axioms Johnson.AtFull.Rounds.k9_batch_count
#print axioms Johnson.AtFull.Rounds.k9_rounds_bent
#print axioms Johnson.AtFull.Rounds.k9_batch_bent
#print axioms Johnson.AtFull.Rounds.k9_batch_other_chain
#print axioms Johnson.AtFull.Rounds.k9_blocks_written
#print axioms Johnson.AtFull.Rounds.k9_mem
#print axioms Johnson.AtFull.Rounds.k9_row_by
#print axioms Johnson.AtFull.Rounds.k9_batch_in
#print axioms Johnson.AtFull.Rounds.k9_batch_by
#print axioms Johnson.AtFull.Rounds.spots_chain
#print axioms Johnson.AtFull.Rounds.k9_names_closed
#print axioms Johnson.AtFull.Rounds.k9_batch_names
#print axioms Johnson.AtFull.Rounds.name_of_spot
#print axioms Johnson.AtFull.Rounds.k9_row_spots
#print axioms Johnson.AtFull.Rounds.k9_batch_spots
