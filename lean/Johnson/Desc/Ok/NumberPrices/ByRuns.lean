-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/NumberPrices/ByRuns.lean: the public test on a chain's finished plan
(`Desc.chainOk`, `Desc.chainAll`, Johnson/Desc/MadeOk.lean) at a plan whose rounds are written as
records and runs: a yes at the records, taken as a plan of their own, is a yes at the whole plan.

A plan of the full size has some ten thousand rounds and few distinct ones, and Lean's kernel is to
evaluate the test on a written plan. Every clause of the test is "all rounds ...", but one:
`Planned.oneDistance` (OnBytes/Params/Planner.lean) is "all pairs of rounds ...", in the list's
order. Its relation holds of a choice with itself and does not mind the order, so it too is settled
on the records.

All that is here are tools. They hold of all settings, records and runs; they name no file and no
description of the protocol. No row is to be laid on any of them.

Definitions.
  `agree g h`: the relation of `oneChoice`: the same two codes, so the same rule and integer.
  `chainRuns recs runs`: the runs whose record has not the name "RECORD".
  `Lit`: a written priced plan: a setting, the distinct priced rounds, the runs. `Lit.plan`: the
    plan.
  `litOk w k recsW runsW L`: the test on a written priced plan, against a written list of rounds:
    `Desc.chainAll w` at the records; and one walk along both lists of runs finds the same entry at
    every place (`sameBy`, Johnson/G/Runs.lean; k bounds its steps). A record under the name
    "RECORD", which is no round of the chain, is passed over in the walk (`chainRuns`).
  `sameRound a b`: the seven fields of two priced rounds are the same. `rideB k P L`: the plan P has
    L's setting, and one walk finds L's rounds in P's, field by field. `rideAt k x L`: the like at
    what a routine of the planner answers.
Statements and proofs.
  `unrunR_eq`: the library's `unrunR` is `unrunG`.
  `agree_iff`, `agree_refl`, `agree_symm`; `agree_of_one`, `one_of_agree`, `oneChoice_of_mem`.
  `chainOk_of_mem`: a yes at rounds rs is a yes at every list of members of rs.
  `chainOk_of_runs`, `chainAll_of_runs`: so at records and runs.
  `chainRounds_of_runs`: the plan's rounds of the chain (`chainRounds`), along the runs.
  `litOk_parts`, `litOk_chainOk`: a yes of `litOk` gives `Desc.chainAll w L.plan` = true, and that
    the written list's entries are those of the plan's rounds of the chain, one by one.
  `entries_of_lit`, `filter_of_lit`: the entries of the plan's plan (`Planned.plan`), and a filter
    on them, along the runs.
  `sameRound_eq`, `ride_eq`, `rideAt_eq`: a yes of `rideB` gives P = L.plan; a yes of `rideAt`, that
    the routine returns L.plan.

What of OnBytes/Model/ is used: nothing.

The definitions `Lit`, `Lit.plan`, `sameRound` and `rideB` have moved, unturned, into
Johnson/G/RunsDefs.lean, a file of definitions alone, which this file imports through
Johnson/G/Runs.lean.

Limits. A yes at the records is asked here, and shown at no records. The converse is not claimed: a
record that no run names can make the test at the records say no where the plan would pass. An
error's number in a record is held against nothing but the bound (`roundHolds`): that it bounds a
count is a premise wherever it is spent. In a written plan the fields `why`, `group`, `rests`,
`scope` and `wordFault` are the written record's own words, held against nothing; the tests read
three of them (`workPlaced` reads `why`, `oneDistance` reads `group`, `wordsFit` reads `wordFault`).
`rideB` and `rideAt` are evaluated nowhere in this file.
-/
import Johnson.Desc.MadeOk
import Johnson.G.DryKeyLit
import Johnson.G.Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number.ByRuns
open OnBytes.Params OnBytes.Flat.Held VerifiableInference
open Johnson.G (unrunR)
open Johnson.G.Runs

/-- The library's list of a list of runs of written rounds is `unrunG`. -/
theorem unrunR_eq (recs : List (Fmt.Round × List Fmt.Stored)) (runs : List (Nat × Nat)) :
    unrunR recs runs = unrunG recs runs := rfl

/-! ## All pairs -/

/-- The relation of `oneChoice`. -/
def agree (g h : PricedChoice) : Bool :=
  !(h.main == g.main && h.mask == g.mask) || (h.rule == g.rule && h.m == g.m)

theorem agree_iff (g h : PricedChoice) : agree g h = true ↔
    (h.main = g.main → h.mask = g.mask → h.rule = g.rule ∧ h.m = g.m) := by
  unfold agree
  by_cases a : h.main = g.main <;> by_cases b : h.mask = g.mask <;> simp [a, b]

theorem agree_refl (g : PricedChoice) : agree g g = true :=
  (agree_iff g g).2 fun _ _ => ⟨rfl, rfl⟩

theorem agree_symm {g h : PricedChoice} (H : agree g h = true) : agree h g = true :=
  (agree_iff h g).2 fun a b =>
    ⟨((agree_iff g h).1 H a.symm b.symm).1.symm, ((agree_iff g h).1 H a.symm b.symm).2.symm⟩

theorem oneChoice_cons (g : PricedChoice) (gs : List PricedChoice) :
    oneChoice (g :: gs) = ((gs.all fun h => agree g h) && oneChoice gs) := rfl

theorem agree_of_one {l : List PricedChoice} (H : oneChoice l = true) :
    ∀ g ∈ l, ∀ h ∈ l, agree g h = true := by
  induction l with
  | nil =>
    intro g hg
    simp at hg
  | cons a as ih =>
    rw [oneChoice_cons] at H
    have c := Bool.and_eq_true_iff.1 H
    intro g hg h hh
    rcases List.mem_cons.1 hg with eg | hg
    · rcases List.mem_cons.1 hh with eh | hh
      · rw [eg, eh]
        exact agree_refl a
      · rw [eg]
        exact List.all_eq_true.1 c.1 h hh
    · rcases List.mem_cons.1 hh with eh | hh
      · rw [eh]
        exact agree_symm (List.all_eq_true.1 c.1 g hg)
      · exact ih c.2 g hg h hh

theorem one_of_agree {l : List PricedChoice} (H : ∀ g ∈ l, ∀ h ∈ l, agree g h = true) :
    oneChoice l = true := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [oneChoice_cons]
    refine Bool.and_eq_true_iff.2 ⟨List.all_eq_true.2 fun h hh => ?_, ih fun g hg h hh => ?_⟩
    · exact H a (List.mem_cons.2 (Or.inl rfl)) h (List.mem_cons_of_mem _ hh)
    · exact H g (List.mem_cons_of_mem _ hg) h (List.mem_cons_of_mem _ hh)

/-- The test on all pairs, at a list of members. -/
theorem oneChoice_of_mem {l l' : List PricedChoice} (hs : ∀ g ∈ l', g ∈ l)
    (H : oneChoice l = true) : oneChoice l' = true :=
  one_of_agree fun g hg h hh => agree_of_one H g (hs g hg) h (hs h hh)

/-! ## The test on a chain's plan -/

/-- **A yes at rounds rs is a yes at every list of members of rs.** -/
theorem chainOk_of_mem {w : ℕ} {s : Setting} {rs rs' : List PlanRound} (hs : ∀ r ∈ rs', r ∈ rs)
    (h : Desc.chainOk w ⟨s, rs⟩ = true) : Desc.chainOk w ⟨s, rs'⟩ = true := by
  have c1 := Bool.and_eq_true_iff.1 h
  have c2 := Bool.and_eq_true_iff.1 c1.1
  have c3 := Bool.and_eq_true_iff.1 c2.1
  have d1 := Bool.and_eq_true_iff.1 c3.1
  have d2 := Bool.and_eq_true_iff.1 d1.1
  have e1 := Bool.and_eq_true_iff.1 c3.2
  have g1 : rs'.all (roundHolds s (capped s)) = true := all_of_mem hs d2.1
  have g2 : rs'.all (fun r => !r.wordFault) = true := all_of_mem hs d2.2
  have g3 : oneChoice (rs'.filterMap (·.group)) = true := by
    refine oneChoice_of_mem (fun g hg => ?_) d1.2
    obtain ⟨r, hr, e⟩ := List.mem_filterMap.1 hg
    exact List.mem_filterMap.2 ⟨r, hs r hr, e⟩
  have g4 : rs'.all (sideR s.target) = true := all_of_mem hs e1.2
  have g5 : rs'.all (fun r => decide (r.entry.work ≤ w)) = true := all_of_mem hs c1.2
  exact Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2
    ⟨Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨g1, g2⟩, g3⟩,
      Bool.and_eq_true_iff.2 ⟨e1.1, g4⟩⟩, c2.2⟩, g5⟩

/-- **A yes at the records is a yes at the plan that is written as records and runs.** -/
theorem chainOk_of_runs {w : ℕ} {s : Setting} {recs : List PlanRound} (runs : List (Nat × Nat))
    (h : Desc.chainOk w ⟨s, recs⟩ = true) : Desc.chainOk w ⟨s, unrunG recs runs⟩ = true :=
  chainOk_of_mem (fun _ hr => mem_unrunG hr) h

/-- The like with the tests on the rounds that draw matrix entries and on where work is counted. -/
theorem chainAll_of_runs {w : ℕ} {s : Setting} {recs : List PlanRound} (runs : List (Nat × Nat))
    (h : Desc.chainAll w ⟨s, recs⟩ = true) : Desc.chainAll w ⟨s, unrunG recs runs⟩ = true := by
  have c := (Desc.chainAll_iff w _).1 h
  have g1 : (unrunG recs runs).all (fun r => Number.smallE r.entry) = true :=
    all_of_recs runs c.2.1
  have g2 : (unrunG recs runs).all
      (fun r => r.entry.work == 0 || (r.why == .query && r.entry.poss != 0)) = true :=
    all_of_recs runs c.2.2
  exact (Desc.chainAll_iff w _).2 ⟨chainOk_of_runs runs c.1, g1, g2⟩

/-- The runs of the rounds of the chain: those whose record has not the name "RECORD". -/
def chainRuns (recs : List PlanRound) (runs : List (Nat × Nat)) : List (Nat × PlanRound) :=
  (valRuns recs runs).filter fun x => x.2.entry.name != Fmt.recordName

/-- The plan's rounds of the chain, along the runs. -/
theorem chainRounds_of_runs (s : Setting) (recs : List PlanRound) (runs : List (Nat × Nat)) :
    chainRounds ⟨s, unrunG recs runs⟩ = expand (chainRuns recs runs) :=
  filter_unrunG (fun r : PlanRound => r.entry.name != Fmt.recordName) recs runs

/-! ## A written priced plan -/

/-- **The test on a written priced plan**, against a written list of rounds. w: the most bits of
work of a round. k: a bound on the steps of the walk. -/
def litOk (w k : ℕ) (recsW : List (Fmt.Round × List Fmt.Stored)) (runsW : List (Nat × Nat))
    (L : Lit) : Bool :=
  Desc.chainAll w ⟨L.set, L.recs⟩ &&
    sameBy (fun x r => decide (x.1.entry = r.entry)) k (valRuns recsW runsW)
      (chainRuns L.recs L.runs)

/-- **What its yes gives.** -/
theorem litOk_parts {w k : ℕ} {recsW : List (Fmt.Round × List Fmt.Stored)}
    {runsW : List (Nat × Nat)} {L : Lit} (h : litOk w k recsW runsW L = true) :
    Desc.chainAll w L.plan = true ∧
      (unrunR recsW runsW).map (·.1.entry) = (chainRounds L.plan).map (·.entry) := by
  have c := Bool.and_eq_true_iff.1 h
  refine ⟨chainAll_of_runs L.runs c.1, ?_⟩
  have e : chainRounds L.plan = expand (chainRuns L.recs L.runs) :=
    chainRounds_of_runs L.set L.recs L.runs
  rw [e, unrunR_eq, unrunG_eq]
  exact map_eq_of_walk (fun x : Fmt.Round × List Fmt.Stored => x.1.entry)
    (fun r : PlanRound => r.entry) k c.2

/-- Of its yes: the test on the prices alone. -/
theorem litOk_chainOk {w k : ℕ} {recsW : List (Fmt.Round × List Fmt.Stored)}
    {runsW : List (Nat × Nat)} {L : Lit} (h : litOk w k recsW runsW L = true) :
    Desc.chainOk w L.plan = true :=
  ((Desc.chainAll_iff w _).1 (litOk_parts h).1).1

/-- The entries of a written priced plan's plan are the records' entries, by the same runs. -/
theorem entries_of_lit (L : Lit) :
    L.plan.plan.entries = unrunG (L.recs.map (·.entry)) L.runs :=
  map_unrunG (fun r : PlanRound => r.entry) L.recs L.runs

/-- A filter on them is a filter on the runs. -/
theorem filter_of_lit (L : Lit) (q : Fmt.Entry → Bool) :
    L.plan.plan.entries.filter q =
      expand ((valRuns (L.recs.map (·.entry)) L.runs).filter fun x => q x.2) := by
  rw [entries_of_lit, filter_unrunG]

/-! ## Whence the numbers came: a test for a run -/

theorem sameRound_eq {a b : PlanRound} (h : sameRound a b = true) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := a
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := b
  simp only [sameRound, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7
  rfl

/-- **A yes: P is the written plan.** -/
theorem ride_eq {k : ℕ} {P : Planned} {L : Lit} (h : rideB k P L = true) : P = L.plan := by
  have c := Bool.and_eq_true_iff.1 h
  have e1 : P.set = L.set := of_decide_eq_true c.1
  have f := (sameBy_sound sameRound k _ _ c.2).imp fun _ _ H => sameRound_eq H
  rw [expand_ones, ← unrunG_eq] at f
  have e2 : P.rounds = unrunG L.recs L.runs := eq_of_forall2 f
  obtain ⟨s, rs⟩ := P
  show (⟨s, rs⟩ : Planned) = ⟨L.set, unrunG L.recs L.runs⟩
  have e1' : s = L.set := e1
  have e2' : rs = unrunG L.recs L.runs := e2
  rw [e1', e2']

/-- What a routine of the planner answers is the written plan: `rideB` at the answer. It says no
where the routine refuses. -/
def rideAt (k : ℕ) (x : Except String Planned) (L : Lit) : Bool :=
  match x with
  | .ok P => rideB k P L
  | .error _ => false

/-- **A yes: the routine returns the written plan.** -/
theorem rideAt_eq {k : ℕ} {x : Except String Planned} {L : Lit} (h : rideAt k x L = true) :
    x = .ok L.plan := by
  cases x with
  | error e => simp [rideAt] at h
  | ok P =>
    have h' : rideB k P L = true := h
    exact congrArg Except.ok (ride_eq h')

end VerifiableInference.Number.ByRuns

#print axioms VerifiableInference.Number.ByRuns.unrunR_eq
#print axioms VerifiableInference.Number.ByRuns.agree_iff
#print axioms VerifiableInference.Number.ByRuns.agree_refl
#print axioms VerifiableInference.Number.ByRuns.agree_symm
#print axioms VerifiableInference.Number.ByRuns.oneChoice_cons
#print axioms VerifiableInference.Number.ByRuns.agree_of_one
#print axioms VerifiableInference.Number.ByRuns.one_of_agree
#print axioms VerifiableInference.Number.ByRuns.oneChoice_of_mem
#print axioms VerifiableInference.Number.ByRuns.chainOk_of_mem
#print axioms VerifiableInference.Number.ByRuns.chainOk_of_runs
#print axioms VerifiableInference.Number.ByRuns.chainAll_of_runs
#print axioms VerifiableInference.Number.ByRuns.chainRounds_of_runs
#print axioms VerifiableInference.Number.ByRuns.litOk_parts
#print axioms VerifiableInference.Number.ByRuns.litOk_chainOk
#print axioms VerifiableInference.Number.ByRuns.entries_of_lit
#print axioms VerifiableInference.Number.ByRuns.filter_of_lit
#print axioms VerifiableInference.Number.ByRuns.sameRound_eq
#print axioms VerifiableInference.Number.ByRuns.ride_eq
#print axioms VerifiableInference.Number.ByRuns.rideAt_eq
