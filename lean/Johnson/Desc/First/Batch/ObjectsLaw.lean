-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/ObjectsLaw.lean: THEOREMS ON Johnson/Desc/First/Batch/Objects.lean: WHAT
TIES A STEP OF ADDING TO "THE CLAIMS" OF WHICH THE KIND's LEMMA SPEAKS. No Mathlib. No axiom beyond
Lean's own is meant.

A step of adding calls the kinds' named runs in a row, gathers their claims, and adds them to the
ledger behind the last run ("made first, then added"). The program `verify-on-bytes` makes a claim
and adds it at once. BETWEEN THE TWO STANDS A THIRD FORM, TYPED HERE ("made and added"): each run's
claims are added before the next run is called. (3) ties the step's form to that third form. WHAT
TIES THE THIRD FORM TO THE ROUTINES OF `verify-on-bytes`, which add claim by claim inside a run, is
each kind's "my run is worth the routine": not here. The laws:
  (1) `gather_eq`: gather is `gatherFrom` over the runs, each guarded by its windows and with its
      name in front of a refusal: the list is the runs' lists in a row; each run is handed the
      number gathered in front of it; the state is handed from run to run; the first refusal is
      the whole's.
  (1b) `gather_rel`: what every run keeps between the state in front and the state behind (a
      reflexive, transitive relation), the gathering keeps.
  (2) `addsStep_decide`: the step's decision is: the counts · K9.adds over gather · what is read
      behind. `adds_decide`: K9.adds' decision, written out.
  (3) `made_first_iff`: FOR RUNS THAT ARE BLIND TO THE ADDING, "made first, then added" ends in a
      state v JUST IF "made and added" ends in v.
  (3c) `steps_iff`: FOR RUNS THAT ARE BLIND TO THE ADDING: two steps of adding in a row end where
      one step over all their runs ends.
  (3b) `guarded_blind`: a run that is Blind stays so when it is guarded, if no adding turns the
      windows.
  (4) `addsOf`: for a lens that keeps two laws (LensOk), the adding by Claim.lean's addAll (the
      yardstick that the laws speak of) is a way of adding. THE JOINT OF (2) AND (3), K9.adds' own
      decision against madeThenAdded at `addsOf X`, stands in
      Johnson/Desc/First/Batch/ObjectsLawAdd.lean: K9.adds adds by the kind's own addList. Proved in
      the kind's own law file: a yes of addList is a yes of addAll, to the same ledger, at all
      arguments; the converse where there is a mark; with no mark they part.
`Blind A f` IS THE CONDITION, AS A PROPERTY OF ONE RUN f AND A WAY OF ADDING A:
  moves: where claims cs can be added in front of the run, the run called BEHIND that adding, handed
         k, does what the run called IN FRONT of it does when handed k + the number of cs: the same
         claims or the same refusal; and cs can be added behind it, to the same end. (So the run
         reads neither the sums, nor the rows' weights, nor the marks of the weights handed out; and
         if it reads the count, it reads it as the count plus the number that it is handed.)
  keeps: whether a list of claims can be added is not turned by the run.
WHAT IS NOT Blind, BY ITS MAKE: K9's own count in the step "objects" ("K9.digits-rows"): it reads
the number HANDED alone, which is the step's own count; and whatever a step asks in front of its
runs or reads off the ledger behind its adding. These live in the step's form alone.
WHAT IS NOT HERE. That any real run (K3's, K4's, K5's, K6's, K8's, K11's) is Blind: A PREMISE, run
by run: held so far by runs on two stored proofs alone (the ledger whole, by value). The refusals'
NAMES of the two forms are not compared: where both refuse they may refuse under different names (an
adding that fails is seen at once in one form and behind the last run in the other). Nothing on
soundness: these are equalities of two programs.
`seen_parts`: A CONTROL ON THE STATEMENT: at a toy state a run that reads the sum is not Blind, and
the two forms part: so the premise cannot be dropped.
Limits: equalities of two programs' answers; in (3) and (3c) the ends are compared, not the
refusals' names. That a real run is Blind is a premise here. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.Objects

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9

variable {T Cl : Type}

/-- A run without its name. -/
abbrev Fn (T : Type) : Type := Nat → T → Except String (List Claim × T)

/-! ## (1) the gathering -/

/-- The runs' claims in a row, n claims being gathered in front. -/
def gatherFrom : List (Fn T) → Nat → T → Except String (List Claim × T)
  | [], _, t => .ok ([], t)
  | f :: fs, n, t =>
    match f n t with
    | .error e => .error e
    | .ok y =>
      match gatherFrom fs (n + y.1.length) y.2 with
      | .error e => .error e
      | .ok z => .ok (y.1 ++ z.1, z.2)

/-- A named run as gather calls it: its claims held against the windows; its name in front of a
refusal. -/
def guarded (ws : T → List Window) (cut : List (Nat × String)) (r : RunOf T) : Fn T := fun n t =>
  match (r.2 n t).bind fun y =>
      (windowsOk (ws t) ((cut.find? fun o => o.2 == r.1).getD (0, r.1)) y.1).map fun _ => y with
  | .ok y => .ok y
  | .error e => .error (r.1 ++ ": " ++ e)

/-- gather's step, by the guarded run. -/
def stepG (ws : T → List Window) (cut : List (Nat × String)) (x : List Claim × T) (r : RunOf T) :
    Except String (List Claim × T) :=
  match guarded ws cut r x.1.length x.2 with
  | .ok y => .ok (x.1 ++ y.1, y.2)
  | .error e => .error e

theorem stepG_eq (ws : T → List Window) (cut : List (Nat × String)) (x : List Claim × T)
    (r : RunOf T) :
    (match (r.2 x.1.length x.2).bind fun y =>
        (windowsOk (ws x.2) ((cut.find? fun o => o.2 == r.1).getD (0, r.1)) y.1).map fun _ => y with
      | .ok y => (.ok (x.1 ++ y.1, y.2) : Except String (List Claim × T))
      | .error e => .error (r.1 ++ ": " ++ e)) = stepG ws cut x r := by
  unfold stepG guarded
  cases ((r.2 x.1.length x.2).bind fun y =>
    (windowsOk (ws x.2) ((cut.find? fun o => o.2 == r.1).getD (0, r.1)) y.1).map fun _ => y) <;> rfl

theorem gather_step (ws : T → List Window) (cut : List (Nat × String)) (runs : List (RunOf T))
    (t : T) : gather ws cut runs t = runs.foldlM (stepG ws cut) ([], t) := by
  unfold gather
  exact congrArg (fun f => List.foldlM f (([], t) : List Claim × T) runs)
    (funext fun x => funext fun r => stepG_eq ws cut x r)

/-- gather's fold, from any list gathered so far. -/
theorem gather_fold (ws : T → List Window) (cut : List (Nat × String)) (runs : List (RunOf T)) :
    ∀ (acc : List Claim) (t : T),
      runs.foldlM (stepG ws cut) (acc, t) =
      match gatherFrom (runs.map (guarded ws cut)) acc.length t with
      | .ok z => .ok (acc ++ z.1, z.2)
      | .error e => .error e := by
  induction runs with
  | nil => intro acc t; simp [gatherFrom, pure, Except.pure]
  | cons r l ih =>
    intro acc t
    simp only [List.foldlM_cons, List.map_cons, gatherFrom, stepG]
    cases guarded ws cut r acc.length t with
    | error e => rfl
    | ok y =>
      simp only [bind, Except.bind]
      rw [ih (acc ++ y.1) y.2, List.length_append]
      cases gatherFrom (l.map (guarded ws cut)) (acc.length + y.1.length) y.2 with
      | error e => rfl
      | ok z => simp [List.append_assoc]

/-- **(1)** -/
theorem gather_eq (ws : T → List Window) (cut : List (Nat × String)) (runs : List (RunOf T))
    (t : T) : gather ws cut runs t = gatherFrom (runs.map (guarded ws cut)) 0 t := by
  rw [gather_step, gather_fold ws cut runs [] t]
  simp only [List.length_nil]
  cases gatherFrom (runs.map (guarded ws cut)) 0 t with
  | error e => rfl
  | ok z => simp

/-- Where a guarded run returns, the run itself has returned the same. -/
theorem guarded_ok (ws : T → List Window) (cut : List (Nat × String)) (r : RunOf T) (n : Nat)
    (t : T) (y : List Claim × T) (h : guarded ws cut r n t = .ok y) : r.2 n t = .ok y := by
  unfold guarded at h
  cases hr : r.2 n t with
  | error e => simp [hr, Except.bind] at h
  | ok w =>
    simp only [hr, Except.bind] at h
    cases hw : windowsOk (ws t) ((cut.find? fun o => o.2 == r.1).getD (0, r.1)) w.1 with
    | error e => simp [hw, Except.map] at h
    | ok _ =>
      simp only [hw, Except.map] at h
      injection h with h'
      rw [h']

/-- **(1b) WHAT EVERY RUN KEEPS, THE GATHERING KEEPS.** R: a relation between the state in front and
the state behind (for one: the ledger's core is the same; a filled slot keeps what was shown
and its factor; what was heard stays heard): reflexive, transitive, and kept by each run. -/
theorem gatherFrom_rel (R : T → T → Prop) (hrefl : ∀ t, R t t)
    (htrans : ∀ a b c, R a b → R b c → R a c) : ∀ (fs : List (Fn T)),
    (∀ f ∈ fs, ∀ (n : Nat) (t : T) (y : List Claim × T), f n t = .ok y → R t y.2) →
    ∀ (n : Nat) (t : T) (z : List Claim × T), gatherFrom fs n t = .ok z → R t z.2 := by
  intro fs
  induction fs with
  | nil =>
    intro _ n t z h
    simp [gatherFrom] at h
    subst h
    exact hrefl t
  | cons f l ih =>
    intro hb n t z h
    simp only [gatherFrom] at h
    cases hf : f n t with
    | error e => simp [hf] at h
    | ok y =>
      simp only [hf] at h
      cases hg : gatherFrom l (n + y.1.length) y.2 with
      | error e => simp [hg] at h
      | ok w =>
        simp only [hg] at h
        have hz : z = (y.1 ++ w.1, w.2) := by
          injection h with h'
          exact h'.symm
        subst hz
        exact htrans _ _ _ (hb f (List.mem_cons_self ..) n t y hf)
          (ih (fun g hgm => hb g (List.mem_cons_of_mem f hgm)) (n + y.1.length) y.2 w hg)

/-- (1b) at gather itself. -/
theorem gather_rel (R : T → T → Prop) (hrefl : ∀ t, R t t)
    (htrans : ∀ a b c, R a b → R b c → R a c) (ws : T → List Window) (cut : List (Nat × String))
    (runs : List (RunOf T))
    (hk : ∀ r ∈ runs, ∀ (n : Nat) (t : T) (y : List Claim × T), r.2 n t = .ok y → R t y.2)
    (t : T) (z : List Claim × T) (h : gather ws cut runs t = .ok z) : R t z.2 := by
  rw [gather_eq] at h
  refine gatherFrom_rel R hrefl htrans _ ?_ 0 t z h
  intro f hf n t' y hy
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hf
  exact hk r hr n t' y (guarded_ok ws cut r n t' y hy)

/-! ## (2) the step's decision -/

/-- K9.adds' decision, written out. -/
theorem adds_decide (X : Lens T) (p : Where) (piece : Nat) (what : String)
    (claims : T → Except String (List Claim × T)) (t : T) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (adds (Cl := Cl) X p piece what claims).decide t rs gs =
      (do
        let s₀ ← X.part t
        need "K9.draw-has-run" s₀.L.handed
        let x ← claims t
        let s ← X.part x.2
        let F ← addList s.F x.1
        pure (X.set x.2 { s with F := F })) := rfl

/-- **(2)** -/
theorem addsStep_decide (X : Lens T) (p : Where) (what : String)
    (counts : List (String × (T → Bool))) (ws : T → List Window) (cut : List (Nat × String))
    (runs : List (RunOf T)) (behind : T → Except String T) (t : T) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (addsStep (Cl := Cl) X p what counts ws cut runs behind).decide t rs gs =
      (do
        countsHold counts t
        let t₁ ← (adds (Cl := Cl) X p p.piece what (gather ws cut runs)).decide t rs gs
        behind t₁) := rfl

/-! ## (3) made first, then added = made and added -/

/-- A way of adding claims to a state. -/
structure Adds (T : Type) where
  add : T → List Claim → Option T
  /-- adding a row of two lists is adding the one and then the other -/
  app : ∀ t a b, add t (a ++ b) = (add t a).bind fun u => add u b
  /-- behind an adding, adding nothing turns nothing -/
  idle : ∀ t cs u, add t cs = some u → add u [] = some u

/-- **A run that is blind to the adding.** -/
structure Blind (A : Adds T) (f : Fn T) : Prop where
  moves : ∀ (k : Nat) (t t' : T) (cs : List Claim), A.add t cs = some t' →
    match f (k + cs.length) t with
    | .ok y => ∃ u', f k t' = .ok (y.1, u') ∧ A.add y.2 cs = some u'
    | .error e => f k t' = .error e
  keeps : ∀ (n : Nat) (t : T) (y : List Claim × T) (cs : List Claim), f n t = .ok y →
    (A.add y.2 cs).isSome = (A.add t cs).isSome

/-- A form between the step's and that of `verify-on-bytes`: each run's claims are added before the
next run is called; a run is handed 0: all that was gathered in front of it stands in the ledger. -/
def madeAndAdded (A : Adds T) : List (Fn T) → T → Except String T
  | [], t => .ok t
  | f :: fs, t =>
    match f 0 t with
    | .error e => .error e
    | .ok y =>
      match A.add y.2 y.1 with
      | none => .error "K9.claim-added"
      | some u => madeAndAdded A fs u

/-- The step's form: all runs first; then all claims. -/
def madeThenAdded (A : Adds T) (fs : List (Fn T)) (t : T) : Except String T :=
  match gatherFrom fs 0 t with
  | .error e => .error e
  | .ok z =>
    match A.add z.2 z.1 with
    | none => .error "K9.claim-added"
    | some u => .ok u

/-- Whether a list can be added is not turned by a row of blind runs. -/
theorem gatherFrom_keeps (A : Adds T) : ∀ (fs : List (Fn T)), (∀ f ∈ fs, Blind A f) →
    ∀ (n : Nat) (t : T) (z : List Claim × T) (cs : List Claim), gatherFrom fs n t = .ok z →
      (A.add z.2 cs).isSome = (A.add t cs).isSome := by
  intro fs
  induction fs with
  | nil =>
    intro _ n t z cs h
    simp [gatherFrom] at h
    subst h
    rfl
  | cons f l ih =>
    intro hb n t z cs h
    simp only [gatherFrom] at h
    cases hf : f n t with
    | error e => simp [hf] at h
    | ok y =>
      simp only [hf] at h
      cases hg : gatherFrom l (n + y.1.length) y.2 with
      | error e => simp [hg] at h
      | ok w =>
        simp only [hg] at h
        have hz : z = (y.1 ++ w.1, w.2) := by
          injection h with h'
          exact h'.symm
        subst hz
        have h1 := ih (fun g hgm => hb g (List.mem_cons_of_mem f hgm)) (n + y.1.length) y.2 w cs hg
        have h2 := (hb f (List.mem_cons_self ..)).keeps n t y cs hf
        simpa using h1.trans h2

/-- The law with claims cs gathered and not yet added: t: the state without them; t': with them. -/
theorem made_first_from (A : Adds T) : ∀ (fs : List (Fn T)), (∀ f ∈ fs, Blind A f) →
    ∀ (t t' : T) (cs : List Claim), A.add t cs = some t' → ∀ (v : T),
      (∃ z, gatherFrom fs cs.length t = .ok z ∧ A.add z.2 (cs ++ z.1) = some v) ↔
        madeAndAdded A fs t' = .ok v := by
  intro fs
  induction fs with
  | nil =>
    intro _ t t' cs hadd v
    constructor
    · rintro ⟨z, hz, hv⟩
      simp [gatherFrom] at hz
      subst hz
      simp [hadd] at hv
      simp [madeAndAdded, hv]
    · intro h
      simp [madeAndAdded] at h
      subst h
      exact ⟨([], t), rfl, by simpa using hadd⟩
  | cons f l ih =>
    intro hb t t' cs hadd v
    have hf := (hb f (List.mem_cons_self ..)).moves 0 t t' cs hadd
    have hl : ∀ g ∈ l, Blind A g := fun g hg => hb g (List.mem_cons_of_mem f hg)
    rw [Nat.zero_add] at hf
    cases hy : f cs.length t with
    | error e =>
      simp only [hy] at hf
      constructor
      · rintro ⟨z, hz, _⟩
        simp [gatherFrom, hy] at hz
      · intro h
        simp [madeAndAdded, hf] at h
    | ok y =>
      simp only [hy] at hf
      obtain ⟨u', hf0, hu'⟩ := hf
      have happ : A.add y.2 (cs ++ y.1) = A.add u' y.1 := by
        rw [A.app, hu']
        rfl
      cases hw : A.add u' y.1 with
      | none =>
        constructor
        · rintro ⟨z, hz, hv⟩
          simp only [gatherFrom, hy] at hz
          cases hg : gatherFrom l (cs.length + y.1.length) y.2 with
          | error e => simp [hg] at hz
          | ok w =>
            simp only [hg] at hz
            have hzz : z = (y.1 ++ w.1, w.2) := by
              injection hz with h'
              exact h'.symm
            subst hzz
            have hk := gatherFrom_keeps A l hl _ _ _ (cs ++ y.1) hg
            rw [happ, hw] at hk
            have : A.add w.2 (cs ++ (y.1 ++ w.1)) = none := by
              rw [← List.append_assoc, A.app]
              cases hq : A.add w.2 (cs ++ y.1) with
              | none => rfl
              | some q => simp [hq] at hk
            simp [this] at hv
        · intro h
          simp [madeAndAdded, hf0, hw] at h
      | some w₀ =>
        have hadd' : A.add y.2 (cs ++ y.1) = some w₀ := by rw [happ, hw]
        have key := ih hl y.2 w₀ (cs ++ y.1) hadd' v
        rw [List.length_append] at key
        constructor
        · rintro ⟨z, hz, hv⟩
          simp only [gatherFrom, hy] at hz
          cases hg : gatherFrom l (cs.length + y.1.length) y.2 with
          | error e => simp [hg] at hz
          | ok w =>
            simp only [hg] at hz
            have hzz : z = (y.1 ++ w.1, w.2) := by
              injection hz with h'
              exact h'.symm
            subst hzz
            have := key.mp ⟨w, hg, by simpa [List.append_assoc] using hv⟩
            simpa [madeAndAdded, hf0, hw] using this
        · intro h
          have h' : madeAndAdded A l w₀ = .ok v := by simpa [madeAndAdded, hf0, hw] using h
          obtain ⟨w, hg, hv⟩ := key.mpr h'
          exact ⟨(y.1 ++ w.1, w.2), by simp [gatherFrom, hy, hg],
            by simpa [List.append_assoc] using hv⟩

/-- **(3)** At a state at which the empty list can be added (a segment is open): t₀: the state
behind that idle adding. The two forms are compared FROM t AND FROM t₀: at the real lens t₀ is t
with its own part laid back: the same, but that "no row is owed" is written in one way: the lens
cannot tell the two apart (Johnson/Desc/First/Batch/ObjectsLawAtS.lean: owedOf_idem). -/
theorem made_first_iff (A : Adds T) (fs : List (Fn T)) (hb : ∀ f ∈ fs, Blind A f) (t t₀ : T)
    (h0 : A.add t [] = some t₀) (v : T) :
    madeThenAdded A fs t = .ok v ↔ madeAndAdded A fs t₀ = .ok v := by
  rw [← made_first_from A fs hb t t₀ [] h0 v]
  unfold madeThenAdded
  simp only [List.length_nil, List.nil_append]
  cases hg : gatherFrom fs 0 t with
  | error e => simp
  | ok z =>
    cases ha : A.add z.2 z.1 with
    | none => simp [ha]
    | some u => simp [ha]

/-! ## (3c) steps in a row = one step over all the runs -/

theorem madeAndAdded_append (A : Adds T) : ∀ (a b : List (Fn T)) (t : T),
    madeAndAdded A (a ++ b) t = (madeAndAdded A a t).bind (madeAndAdded A b) := by
  intro a
  induction a with
  | nil => intro b t; rfl
  | cons f l ih =>
    intro b t
    simp only [List.cons_append, madeAndAdded]
    cases f 0 t with
    | error e => rfl
    | ok y =>
      dsimp only
      cases A.add y.2 y.1 with
      | none => rfl
      | some u => exact ih b u

/-- Behind "made and added", from a state at which adding nothing turns nothing, adding nothing
turns nothing. -/
theorem madeAndAdded_idle (A : Adds T) : ∀ (a : List (Fn T)) (t u : T), A.add t [] = some t →
    madeAndAdded A a t = .ok u → A.add u [] = some u := by
  intro a
  induction a with
  | nil =>
    intro t u h0 h
    simp [madeAndAdded] at h
    rw [← h]
    exact h0
  | cons f l ih =>
    intro t u _ h
    simp only [madeAndAdded] at h
    cases hf : f 0 t with
    | error e => simp [hf] at h
    | ok y =>
      simp only [hf] at h
      cases ha : A.add y.2 y.1 with
      | none => simp [ha] at h
      | some w =>
        simp only [ha] at h
        exact ih w u (A.idle _ _ _ ha) h

/-- **(3c) TWO STEPS OF ADDING IN A ROW END WHERE ONE STEP OVER ALL THEIR RUNS ENDS**, for runs that
are Blind: so the seat by steps and a batching that gathers a whole segment at once end alike, AS
FAR AS THE STEPS ARE RUNS AND ADDINGS ALONE. (What a step reads off the ledger BEHIND its adding,
as the smallness test's own coefficients, is no Blind run: it must stay between the addings.) -/
theorem steps_iff (A : Adds T) (a b : List (Fn T)) (ha : ∀ f ∈ a, Blind A f)
    (hb : ∀ f ∈ b, Blind A f) (t t₀ : T) (h0 : A.add t [] = some t₀) (v : T) :
    (∃ u, madeThenAdded A a t = .ok u ∧ madeThenAdded A b u = .ok v) ↔
      madeThenAdded A (a ++ b) t = .ok v := by
  have hab : ∀ f ∈ a ++ b, Blind A f := by
    intro f hf
    cases List.mem_append.mp hf with
    | inl h => exact ha f h
    | inr h => exact hb f h
  have h00 : A.add t₀ [] = some t₀ := A.idle _ _ _ h0
  rw [made_first_iff A (a ++ b) hab t t₀ h0 v, madeAndAdded_append]
  constructor
  · rintro ⟨u, hu, hv⟩
    have hu' := (made_first_iff A a ha t t₀ h0 u).mp hu
    have hidle := madeAndAdded_idle A a t₀ u h00 hu'
    have hv' := (made_first_iff A b hb u u hidle v).mp hv
    simp [hu', Except.bind, hv']
  · intro h
    cases hu' : madeAndAdded A a t₀ with
    | error e => simp [hu', Except.bind] at h
    | ok u =>
      simp only [hu', Except.bind] at h
      have hidle := madeAndAdded_idle A a t₀ u h00 hu'
      exact ⟨u, (made_first_iff A a ha t t₀ h0 u).mpr hu',
        (made_first_iff A b hb u u hidle v).mpr h⟩

/-! ## (3b) the guarded run -/

/-- **(3b)** -/
theorem guarded_blind (A : Adds T) (ws : T → List Window) (cut : List (Nat × String))
    (r : RunOf T) (hr : Blind A r.2)
    (hw : ∀ (t t' : T) (cs : List Claim), A.add t cs = some t' → ws t' = ws t) :
    Blind A (guarded ws cut r) where
  moves := by
    intro k t t' cs hadd
    have h := hr.moves k t t' cs hadd
    unfold guarded
    rw [hw t t' cs hadd]
    cases hy : r.2 (k + cs.length) t with
    | error e =>
      simp only [hy] at h
      simp [h, Except.bind]
    | ok y =>
      simp only [hy] at h
      obtain ⟨u', h1, h2⟩ := h
      simp only [h1, Except.bind]
      cases windowsOk (ws t) ((cut.find? fun o => o.2 == r.1).getD (0, r.1)) y.1 with
      | error e => simp [Except.map]
      | ok _ => exact ⟨u', by simp [Except.map], h2⟩
  keeps := by
    intro n t y cs h
    exact hr.keeps n t y cs (guarded_ok ws cut r n t y h)

/-! ## (4) the joint: K9.adds is "made first, then added" -/

/-- The lens's two laws, AS FAR AS THE ADDING WANTS THEM: of a part that differs from the state's
own in its ledger alone, and there by an adding. (The real lens reads some of the part's fields off
the state and writes them nowhere: the laws do not hold of an arbitrary part.) -/
structure LensOk (X : Lens T) : Prop where
  getSet : ∀ (t : T) (s : Part) (cs : List Claim) (G : OnBytes.Model.Fork), X.get? t = some s →
    addAll s.F cs = some G → X.get? (X.set t { s with F := G }) = some { s with F := G }
  setSet : ∀ (t : T) (s : Part) (G H : OnBytes.Model.Fork), X.get? t = some s →
    X.set (X.set t { s with F := G }) { s with F := H } = X.set t { s with F := H }

/-- The real adding: the ledger inside the part inside the state. -/
def addAt (X : Lens T) (t : T) (cs : List Claim) : Option T :=
  (X.get? t).bind fun s => (addAll s.F cs).map fun F => X.set t { s with F := F }

theorem addAll_append (F : OnBytes.Model.Fork) (a b : List Claim) :
    addAll F (a ++ b) = (addAll F a).bind fun G => addAll G b := by
  unfold addAll
  rw [List.foldlM_append]
  rfl

/-- The real adding is a way of adding. -/
def addsOf (X : Lens T) (h : LensOk X) : Adds T where
  add := addAt X
  app := by
    intro t a b
    unfold addAt
    cases hs : X.get? t with
    | none => rfl
    | some s =>
      simp only [Option.bind]
      rw [addAll_append]
      cases ha : addAll s.F a with
      | none => rfl
      | some G =>
        simp only [Option.bind, Option.map]
        rw [h.getSet t s a G hs ha]
        simp only [Option.bind]
        cases addAll G b with
        | none => rfl
        | some H => simp [Option.map, h.setSet t s G H hs]
  idle := by
    intro t cs u hu
    unfold addAt at hu ⊢
    cases hs : X.get? t with
    | none => simp [hs] at hu
    | some s =>
      simp only [hs, Option.bind] at hu
      cases ha : addAll s.F cs with
      | none => simp [ha] at hu
      | some G =>
        simp only [ha, Option.map] at hu
        injection hu with hu'
        rw [← hu', h.getSet t s cs G hs ha]
        simp [addAll, pure, h.setSet t s G G hs]

/-! ## a control on the statement -/

/-- A toy: the state is the number of claims added. -/
def toyAdds : Adds Nat where
  add := fun t cs => some (t + cs.length)
  idle := by intro t cs u _; simp
  app := by intro t a b; simp [Nat.add_assoc]

/-- Lays one claim; reads nothing. -/
def toyBlind : Fn Nat := fun _ t => .ok ([{}], t)

/-- Lays one claim, IF NOTHING HAS BEEN ADDED YET: it reads what an adding writes. -/
def toySees : Fn Nat := fun _ t => if t == 0 then .ok ([{}], t) else .error "seen"

/-- **With a run that sees the adding the two forms part.** -/
theorem seen_parts :
    madeThenAdded toyAdds [toyBlind, toySees] 0 = .ok 2 ∧
      madeAndAdded toyAdds [toyBlind, toySees] 0 = .error "seen" := ⟨rfl, rfl⟩

/-- And that run is not Blind. -/
theorem toySees_not_blind : ¬ Blind toyAdds toySees := by
  intro h
  have := h.moves 0 0 1 [{}] rfl
  simp [toySees] at this

/-- The toy's blind run is Blind: the premise can be met. -/
theorem toyBlind_blind : Blind toyAdds toyBlind where
  moves := by
    intro k t t' cs h
    simp [toyBlind, toyAdds] at h ⊢
    exact h
  keeps := by
    intro n t y cs h
    simp [toyAdds]

end VerifiableInference.Desc.K9
