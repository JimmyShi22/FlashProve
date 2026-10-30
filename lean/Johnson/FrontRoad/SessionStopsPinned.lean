-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/SessionStopsPinned.lean: glue. If a chain's rows are pinned (RowsPinned) and the
chain's data fit its members' rounds, then PartsHeld holds at every premise Q on the input that
gives CellsSmallAt (partsHeld_of_pinned). And the sum of the stated shares is at most the sum of
windowShare over the pinned places (sharesSum_of_pinned). cells is free; the values that par names
are free: tied to nothing here.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

Words. A chain's members are its sub-protocols (Block, Johnson/Desc/Block.lean; not the member of
Johnson/FrontRoad/Spec.lean). A half is the prover's share of one sub-protocol at its place: a list
of parts (Placed, Part, Johnson/Desc/ProofFile/Honest/Frame.lean). A part's stretch is the data of
its own rounds. A part has two abort tests. Its public abort test (Part.bad) reads challenges alone.
Its private abort test (Part.hid; that file calls the two a stop of the first and of the second
sort) may also read the input with its trace. A part's stated share (Part.hidShare) is a number that
the part writes down for its private abort test. The planner: Johnson/FrontRoad/RangeCheckBits.lean.
The smallness test: the kind K8 of sub-protocol (Johnson/Desc/First/K8/Hear.lean). A place with
parameters, or pinned place: the place of a member of the chain at which par names parameters.

What this file has (namespace OnBytes.FrontRoad).
  RowsPinned   a premise's form, called the pin below and in the files that import this one. At each
      member b of the chain: where par names parameters P at b's place, a half stands at that place,
      the public test smallFits P passes, b has the one round round P.1 of the smallness test, and
      the first half there has the one part quietStop (smallStop cells P) (windowShare P.1); where
      par names none, b's place is not of the kind K8 (Place.kind, Johnson/Desc/Block.lean), and, if
      a half stands at b's place, no part of the first half there has a private abort test that
      fires at any argument, and each part's stated share has the value 0. So at every member of the
      kind K8 par names parameters, a half stands, and it has that one part. The library finds the
      members of the smallness test by that kind (drawIxs, Johnson/Desc/First/K8/PlanDoor.lean).
      rowsPinned_names: at a member of the kind K8 par names parameters. rowsPinned_at: what the pin
      says of the first half that stands at a member's place. rowsPinned_stands: at a member with
      parameters a half stands. smallFits is used by no proof here: it is the condition under which
      the half smallHalf cells P has just that part (small_parts,
      Johnson/Desc/ProofFile/Honest/K8/QuietForm.lean).
  CellsSmallAt   a premise's form, on the input with its trace. At each member at whose place par
      names parameters P, the cells that the reader cells yields of the trace pass cellsSmall
      (Johnson/Desc/K8/Honest/Window.lean): each is at most 128 in absolute value. It reads the
      hidden input.
  partsHeld_of_pinned   to PartsHeld (Johnson/FrontRoad/SessionStopsOfParts.lean). At a pinned place
      the part's stretch of the data is one round's, with the entry and the kind of the test's own
      declared round (stretch_one, Johnson/Desc/ProofFile/Honest/Law/CoverFitAt.lean; kind_rng,
      Johnson/Desc/First/K8/Law.lean); then small_stopDebt
      (Johnson/Desc/ProofFile/Honest/K8/WindowDebt.lean). That the part has one move is by
      quietStop's definition (Johnson/Desc/ProofFile/Honest/K9/QuietMember.lean).
  partsHeld_of_silent   its case without parameters: no premise on the data, any Q.
  sharesSum_of_pinned, sharesSum_of_silent   on sharesSum
      (Johnson/FrontRoad/SessionStopsOfHeld.lean). Only "at most" is stated; under the pin the two
      sides are equal (by inspection, not proved). rowGates_p and memberSum_of_pinned are helpers.

How it fits. PartsHeld and the two sums are the premises on the parts in sessionStops_at_files
(Johnson/FrontRoad/SessionStopsAtFiles.lean). With shares_le_planner
(Johnson/FrontRoad/SharesLePlanner.lean) the sum is at most the planner's bound where the planner's
test passes. The measure in partsHeld_of_pinned is StopDebt's
(Johnson/Desc/ProofFile/Honest/Law/SharesParts.lean): the written verifier message of the part's own
one round, uniform; the input, its trace, all challenges in front and the place are bound by "for
all". Glue; not one of the release's goal statements.

Limits.
  That any prover's rows are pinned is not proved here. That the first alternative of RowsPinned can
      be met is pinned_at_smallHalf (Johnson/FrontRoad/SessionStopsPinnedTests.lean).
  That the cells of the trace of an input that meets Q pass cellsSmall is a premise. It reads the
      hidden input, and nothing here proves it.
  cells is free. At a reader that yields zeros alone CellsSmallAt holds at every input and the
      private abort test never fires. Nothing here ties cells to what the other kinds' parts send.
  The values that par names are free. The pin holds P.1 against the member by one number alone, the
      number of entries that the round draws (columns · tau): not the numbers of a matrix's rows,
      not how the columns are cut into matrices, not tau by itself. At a par that states fewer rows
      than the description, the test, the premise and the shares all shrink. P.2, each matrix's
      owner, name and first column, is held against nothing but its length (smallFits). At a wrong
      name the test and the premise read other cells than the matrix's, whatever the reader yields
      there.
  A half is looked up by place, the first that stands there, as the definition of where a chain's
      halves abort looks it up (chainStopAt, Johnson/Desc/ProofFile/Honest/Rule.lean). A second half
      at one place, and a half at no member's place, are read by nothing here; ready
      (Johnson/Desc/ProofFile/Honest/Frame.lean) refuses both. Rows without a half at a member's
      place with parameters are not pinned (no_half_not_pinned,
      Johnson/FrontRoad/SessionStopsPinnedTests.lean). The test lacking
      (Johnson/Desc/ProofFile/Honest/Frame.lean) does not see such rows: it lists only members with
      a round that sends something (Entry.msg, Fmt/Plan.lean), and the round of the smallness test
      sends nothing. A par that names none at the place of a member of the kind K8 is shut out too
      (unnamed_not_pinned, in that file). At a member of another kind at whose place par names none
      the pin does not ask that a half stands.
  At par := fun _ => none, at a chain without a member of the kind K8 and at rows whose parts have
      private abort tests that never fire and state the value 0, everything here holds with the sum
      0.
  An earlier part's or member's public abort shuts out a later private one, and within one part the
      public test is asked first; at rows that always abort publicly all premises can hold (by
      inspection, not proved).
  Nothing is said on hiding, completeness or soundness.
-/
import Johnson.FrontRoad.SessionStopsOfParts
import Johnson.Desc.ProofFile.Honest.K8.WindowDebt
import Johnson.Desc.ProofFile.Honest.Law.CoverFitAt
import Johnson.Desc.First.K8.Law

set_option autoImplicit false

namespace OnBytes.FrontRoad
open OnBytes.Maker (RDT)
open _root_.Run (ckP)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First.K8 (Par round rd kind_rng)
open VerifiableInference.Desc.First.K8.Honest (cellsSmall)
open ProofFile.Honest (Placed Local Face Why Cells KindFits StopDebt stretch_one chainGates memberGates
  rowGates)
open ProofFile.Honest.K8 (smallStop smallFits windowShare askOfInput small_stopDebt)
open ProofFile.Honest.K9 (quietStop)
open scoped ENNReal

variable {S Cl W₀ Rc Xi Tr X : Type}
  (par : Place → Option (Par × List (ℕ × String × ℕ))) (cells : Tr → Cells)

/-- **A premise's form: the rows are pinned.** hs: a chain's halves; bs: its members. At each member
b of bs: where par names parameters P at b's place, a half of hs stands at that place, the public
test smallFits P passes, b has the one round round P.1, and the first half there has the one part
quietStop (smallStop cells P) (windowShare P.1); where par names none, b's place is not of the kind
K8, and, if a half stands at b's place, no part of the first half there has a private abort test
that fires at any argument, and each part's stated share has the value 0. At par := fun _ => none
the pin also says that the chain has no member of the kind K8. cells is free; the values that par
names are free. -/
def RowsPinned (hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X))
    (bs : List (Block S Cl)) : Prop :=
  ∀ b ∈ bs,
    match par b.place with
    | some P => ∃ g, (hs.find? fun g => g.place == b.place) = some g ∧ smallFits P = true ∧
        b.rounds = [round P.1] ∧ g.parts = [quietStop (smallStop cells P) (windowShare P.1)]
    | none => b.place.kind ≠ KindName.K8 ∧
        ∀ g, (hs.find? fun g => g.place == b.place) = some g →
          ∀ p ∈ g.parts, (∀ u l o, p.hid u l o = none) ∧ p.hidShare.val = 0

/-- What the pin says of the first half that stands at a member's place. -/
theorem rowsPinned_at {hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)}
    {bs : List (Block S Cl)} (hp : RowsPinned par cells hs bs) (b : Block S Cl) (hb : b ∈ bs)
    (g : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)
    (hg : (hs.find? fun g => g.place == b.place) = some g) :
    match par b.place with
    | some P => smallFits P = true ∧ b.rounds = [round P.1] ∧
        g.parts = [quietStop (smallStop cells P) (windowShare P.1)]
    | none => ∀ p ∈ g.parts, (∀ u l o, p.hid u l o = none) ∧ p.hidShare.val = 0 := by
  have h := hp b hb
  cases hpar : par b.place with
  | none =>
    rw [hpar] at h
    exact h.2 g hg
  | some P =>
    rw [hpar] at h
    obtain ⟨g', hg', h'⟩ := h
    rw [hg] at hg'
    cases hg'
    exact h'

/-- At a member of the kind K8, par names parameters. -/
theorem rowsPinned_names {hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)}
    {bs : List (Block S Cl)} (hp : RowsPinned par cells hs bs) (b : Block S Cl) (hb : b ∈ bs)
    (hk : b.place.kind = KindName.K8) : ∃ P, par b.place = some P := by
  have h := hp b hb
  cases hpar : par b.place with
  | none =>
    rw [hpar] at h
    exact absurd hk h.1
  | some P => exact ⟨P, rfl⟩

/-- At a member at whose place par names parameters, a half stands. -/
theorem rowsPinned_stands {hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)}
    {bs : List (Block S Cl)} (hp : RowsPinned par cells hs bs) (b : Block S Cl) (hb : b ∈ bs)
    (P : Par × List (ℕ × String × ℕ)) (hpar : par b.place = some P) :
    ∃ g, (hs.find? fun g => g.place == b.place) = some g := by
  have h := hp b hb
  rw [hpar] at h
  obtain ⟨g, hg, -⟩ := h
  exact ⟨g, hg⟩

/-- **A premise's form, on the input with its trace**: at each member at whose place par names
parameters, the cells that the reader cells yields of the trace pass cellsSmall: each is at most 128
in absolute value. It reads the hidden input. -/
def CellsSmallAt (bs : List (Block S Cl)) (v : Local W₀ Rc Xi Tr) : Prop :=
  ∀ b ∈ bs, ∀ P, par b.place = some P → cellsSmall P.1 (askOfInput cells P.2 v).cell = true

/-- **From the pin, and data that fit the members' rounds, to PartsHeld**, at every Q that gives
CellsSmallAt. The measure is StopDebt's: the written verifier message of the part's own one round.
-/
theorem partsHeld_of_pinned {hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)}
    {bs : List (Block S Cl)} {ds : List RDT} (hp : RowsPinned par cells hs bs)
    (hk : List.Forall₂ KindFits ds (bs.flatMap (·.rounds))) (Q : Local W₀ Rc Xi Tr → Prop)
    (hQ : ∀ v, Q v → CellsSmallAt par cells bs v) : PartsHeld Q Face.own.sees hs bs ds := by
  intro v hv A b B e g hg A' p B' e'
  have hb : b ∈ bs := by
    rw [e]
    exact List.mem_append_right _ (List.mem_cons_self)
  have h := rowsPinned_at par cells hp b hb g hg
  cases hpar : par b.place with
  | none =>
    rw [hpar] at h
    refine Or.inl (h p ?_).1
    rw [e']
    exact List.mem_append_right _ (List.mem_cons_self)
  | some P =>
    rw [hpar] at h
    obtain ⟨-, hr, hparts⟩ := h
    rw [hparts] at e'
    have hA : A' = [] := by
      cases A' with
      | nil => rfl
      | cons a A'' =>
        have hl := congrArg List.length e'
        simp at hl
    subst hA
    have hpq : p = quietStop (smallStop cells P) (windowShare P.1) := by
      have := List.cons.inj (e'.symm : p :: B' = _)
      exact this.1
    subst hpq
    subst e
    obtain ⟨d, hd, he, hkd⟩ := stretch_one ds A B b hk (round P.1) hr
    have hkind : d.kind = .entries := by
      have := (kind_rng P.1).symm.trans hkd
      exact (Option.some.inj this).symm
    refine Or.inr ?_
    rw [hd]
    exact small_stopDebt cells P d he hkind v (hQ v hv b hb P hpar)

/-- The case without parameters: no premise on the data, any Q. -/
theorem partsHeld_of_silent {hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)}
    {bs : List (Block S Cl)} {ds : List RDT} (hp : RowsPinned (fun _ => none) cells hs bs)
    (Q : Local W₀ Rc Xi Tr → Prop) : PartsHeld Q Face.own.sees hs bs ds := by
  intro v _ A b B e g hg A' p B' e'
  have hb : b ∈ bs := by
    rw [e]
    exact List.mem_append_right _ (List.mem_cons_self)
  refine Or.inl ((rowsPinned_at (fun _ => none) cells hp b hb g hg) p ?_).1
  rw [e']
  exact List.mem_append_right _ (List.mem_cons_self)

/-- The numbers at a row's gates are the parts' values. -/
theorem rowGates_p {V W Y : Type} (sp : Option Why → Bool) (v : Option V)
    (val : ProofFile.Honest.Part V W Y → ℝ≥0∞) :
    ∀ (ps : List (ProofFile.Honest.Part V W Y)) (ds : List RDT),
    (rowGates sp v val ps ds).map (·.p) = ps.map val
  | [], _ => rfl
  | p :: ps, ds => by
    unfold rowGates
    rw [List.map_cons, List.map_cons, rowGates_p sp v val ps]

/-- One member: the sum of the numbers at its gates is at most the pinned place's stated share, and
0 at a place without parameters. -/
theorem memberSum_of_pinned {hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)}
    {bs : List (Block S Cl)} (hp : RowsPinned par cells hs bs) (b : Block S Cl) (hb : b ∈ bs)
    (ds : List RDT) :
    ((memberGates (· == some Why.hid) (none : Option (Local W₀ Rc Xi Tr)) (·.hidShare.val) hs b
      ds).map (·.p)).sum ≤ (((par b.place).toList).map fun P => (windowShare P.1).val).sum := by
  unfold memberGates
  cases hg : hs.find? fun g => g.place == b.place with
  | none =>
    show (([⟨ds, fun _ _ => false, 0⟩] : List ProofFile.Honest.Gate).map (·.p)).sum ≤ _
    simp
  | some g =>
    show ((rowGates _ _ _ g.parts ds).map (·.p)).sum ≤ _
    rw [rowGates_p]
    have h := rowsPinned_at par cells hp b hb g hg
    cases hpar : par b.place with
    | none =>
      rw [hpar] at h
      refine le_of_eq_of_le (List.sum_eq_zero fun x hx => ?_) (zero_le _)
      obtain ⟨p, hpm, rfl⟩ := List.mem_map.1 hx
      exact (h p hpm).2
    | some P =>
      rw [hpar] at h
      rw [h.2.2]
      exact le_of_eq rfl

/-- **The sum of the shares that a pinned chain's parts state is at most the sum of windowShare over
the places with parameters.** Arithmetic on written shares; no event. -/
theorem sharesSum_of_pinned {hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)} :
    ∀ {bs : List (Block S Cl)} (_ : RowsPinned par cells hs bs) (ds : List RDT),
    sharesSum hs bs ds ≤
      ((bs.filterMap fun b => par b.place).map fun P => (windowShare P.1).val).sum
  | [], _, _ => le_of_eq rfl
  | b :: bs, hp, ds => by
    have ih := sharesSum_of_pinned (bs := bs)
      (fun b' hb' => hp b' (List.mem_cons_of_mem _ hb')) (ds.drop b.rounds.length)
    have hm := memberSum_of_pinned par cells hp b (List.mem_cons_self) (ds.take b.rounds.length)
    have e : sharesSum hs (b :: bs) ds =
        ((memberGates (· == some Why.hid) (none : Option (Local W₀ Rc Xi Tr)) (·.hidShare.val) hs b
          (ds.take b.rounds.length)).map (·.p)).sum +
          sharesSum hs bs (ds.drop b.rounds.length) := by
      unfold sharesSum
      show ((memberGates _ _ _ hs b (ds.take b.rounds.length) ++
        chainGates _ _ _ hs bs (ds.drop b.rounds.length)).map (·.p)).sum = _
      rw [List.map_append, List.sum_append]
    rw [e]
    refine (add_le_add hm ih).trans (le_of_eq ?_)
    cases hpar : par b.place with
    | none => simp [List.filterMap_cons, hpar]
    | some P => simp [List.filterMap_cons, hpar]

/-- The case without parameters: the sum is 0. -/
theorem sharesSum_of_silent {hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)}
    {bs : List (Block S Cl)} (hp : RowsPinned (fun _ => none) cells hs bs) (ds : List RDT) :
    sharesSum hs bs ds ≤ 0 := by
  have h := sharesSum_of_pinned (fun _ => none) cells hp ds
  simpa using h

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.RowsPinned
#print axioms OnBytes.FrontRoad.rowsPinned_at
#print axioms OnBytes.FrontRoad.rowsPinned_names
#print axioms OnBytes.FrontRoad.rowsPinned_stands
#print axioms OnBytes.FrontRoad.CellsSmallAt
#print axioms OnBytes.FrontRoad.partsHeld_of_pinned
#print axioms OnBytes.FrontRoad.partsHeld_of_silent
#print axioms OnBytes.FrontRoad.rowGates_p
#print axioms OnBytes.FrontRoad.memberSum_of_pinned
#print axioms OnBytes.FrontRoad.sharesSum_of_pinned
#print axioms OnBytes.FrontRoad.sharesSum_of_silent
