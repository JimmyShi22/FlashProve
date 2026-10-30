-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/K8Sits.lean: THE SMALLNESS TEST's THREE RUNS, AS ITS BLOCK STATES THEM, ARE THE TEXTS OF WHICH
THE LAWS SPEAK. The kind's block is K8.whole p (Johnson/Desc/First/K8/Whole.lean). It states one run of claims,
"K8.equations", and two runs behind the batching, "K8.lsTail" and "K8.tests". The laws of this folder speak of the plain
functions equations (Equations.lean) and testsP (SelfRows.lean) on a record, a list of tables and a ledger. Here: what the
block states under each name says yes at a carried record just where the plain function says yes at the record's own
parts, and hands on just what that function returns.

Statements and proofs.
Main names:
  partOf s: the parts of the carried record that the three runs read (k8PartP.get?): the smallness test's record, the list
    of tables, the ledger; nothing outside a link.
  sits_names: the block states just these three names, in this order.
  sits_equations, sits_lsTail, sits_tests: for each name: the run that the block states under it, as an equivalence.
  **K08SitsClaims** (a closed Prop), **k08_sits_claims**: the four together, at every place's numbers p.
Limits. That a description's seat lays K8.whole at its places, and that the step which gathers claims calls a block's run
by its name, is not said here: these are laws on the driver, general in the kind. Of the block's first half (planOk,
rounds, oracles, before, decide) nothing is said. The number that equations is handed is the ledger's own count plus the
number that the run is handed.

-/
import Johnson.Desc.First.K8.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims

/-- The parts of the carried record that the three runs read. -/
def partOf (s : S) : Option K8Part := k8PartP.get? s

/-- The block states just these names. -/
theorem sits_names (p : K8.ParW) :
    (K8.whole p).claims.map (·.1) = ["K8.equations"] ∧
      (K8.whole p).after.map (·.1) = ["K8.lsTail", "K8.tests"] := ⟨rfl, rfl⟩

/-- A run at the part, as a run at the record: taken apart. -/
theorem atRecord_ok {α : Type} (f : K8Part → Except String (α × K8Part)) (s s' : S) (a : α) :
    K8.atRecord f s = .ok (a, s') ↔
      ∃ q q', partOf s = some q ∧ f q = .ok (a, q') ∧ s' = k8PartP.set s q' := by
  unfold K8.atRecord partOf
  cases hq : k8PartP.get? s with
  | none => simp
  | some q =>
    show (f q).map (fun x => (x.1, k8PartP.set s x.2)) = .ok (a, s') ↔ _
    constructor
    · intro h
      cases hf : f q with
      | error e => rw [hf] at h; cases h
      | ok x =>
        rw [hf] at h
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Except.ok.inj h)
        exact ⟨q, x.2, rfl, by rw [← h1]; exact hf, h2.symm⟩
    · rintro ⟨q1, q', h1, h2, rfl⟩
      obtain rfl := Option.some.inj h1
      rw [h2]
      rfl

/-- **"K8.equations"**: the run that the block states under that name says yes at the number front and the record s just
where equations says yes at the ledger's count + front and the record's own parts; its claims are that list; the record
behind it has the returned record and ledger laid. -/
theorem sits_equations (p : K8.ParW) (run : Nat → S → Except String (List Claim × S))
    (h : ("K8.equations", run) ∈ (K8.whole p).claims) (front : Nat) (s s' : S) (cls : List Claim) :
    run front s = .ok (cls, s') ↔
      ∃ q tl' F1, partOf s = some q ∧
        equations (q.F.nClaim + front) q.tl q.funs q.F = .ok (tl', F1, cls) ∧
        s' = k8PartP.set s { q with tl := tl', F := F1 } := by
  have e : run = fun front => K8.atRecord ((k8Claims.head (by simp [k8Claims])).2 front) := by
    have h' : ("K8.equations", run) ∈
        [("K8.equations", fun front => K8.atRecord ((k8Claims.head (by simp [k8Claims])).2 front))] := h
    simpa using h'
  subst e
  rw [atRecord_ok]
  constructor
  · rintro ⟨q, q', hq, hf, rfl⟩
    change (equations (q.F.nClaim + front) q.tl q.funs q.F).map _ = _ at hf
    cases he : equations (q.F.nClaim + front) q.tl q.funs q.F with
    | error e => rw [he] at hf; cases hf
    | ok x =>
      obtain ⟨tl', F1, c⟩ := x
      rw [he] at hf
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hf)
      exact ⟨q, tl', F1, hq, he, rfl⟩
  · rintro ⟨q, tl', F1, hq, he, rfl⟩
    refine ⟨q, _, hq, ?_, rfl⟩
    change (equations (q.F.nClaim + front) q.tl q.funs q.F).map _ = _
    rw [he]
    rfl

/-- A run behind the batching at the part, as the block lays it at the record: taken apart. -/
theorem afterRecord_ok (f : K8Part → Except String K8Part) (s s' : S) :
    (K8.atRecord (fun q => (f q).map fun q' => ((), q')) s).map (·.2) = .ok s' ↔
      ∃ q q', partOf s = some q ∧ f q = .ok q' ∧ s' = k8PartP.set s q' := by
  constructor
  · intro h
    cases hr : K8.atRecord (fun q => (f q).map fun q' => ((), q')) s with
    | error e => rw [hr] at h; cases h
    | ok x =>
      obtain ⟨u, s1⟩ := x
      rw [hr] at h
      obtain rfl : s1 = s' := Except.ok.inj h
      obtain ⟨q, q', hq, hf, rfl⟩ := (atRecord_ok _ s s1 u).1 hr
      cases hfq : f q with
      | error e => rw [hfq] at hf; cases hf
      | ok q1 =>
        rw [hfq] at hf
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj hf)
        exact ⟨q, q1, hq, hfq, rfl⟩
  · rintro ⟨q, q', hq, hf, rfl⟩
    have : K8.atRecord (fun q => (f q).map fun q' => ((), q')) s = .ok ((), k8PartP.set s q') :=
      (atRecord_ok _ s _ ()).2 ⟨q, q', hq, by rw [hf]; rfl, rfl⟩
    rw [this]
    rfl

/-- **"K8.lsTail"**: it refuses nowhere inside a link, and lays the coefficients on the test's own slots, as the ledger has
them, into the record's field lsTail. -/
theorem sits_lsTail (p : K8.ParW) (run : S → Except String S)
    (h : ("K8.lsTail", run) ∈ (K8.whole p).after) (s s' : S) :
    run s = .ok s' ↔
      ∃ q, partOf s = some q ∧
        s' = k8PartP.set s { q with tl := { q.tl with lsTail := q.F.LS.extract q.tl.slotA q.tl.slotB } } := by
  have h' : ("K8.lsTail", run) ∈
      [(k8LsTail.1, fun s => (K8.atRecord (fun q => (k8LsTail.2 q).map fun q' => ((), q')) s).map (·.2)),
       ((k8Tests p.nU).1,
        fun s => (K8.atRecord (fun q => ((k8Tests p.nU).2 q).map fun q' => ((), q')) s).map (·.2))] := h
  have e : run = fun s => (K8.atRecord (fun q => (k8LsTail.2 q).map fun q' => ((), q')) s).map (·.2) := by
    simpa [k8LsTail, k8Tests] using h'
  subst e
  rw [afterRecord_ok]
  constructor
  · rintro ⟨q, q', hq, hf, rfl⟩
    obtain rfl := Except.ok.inj hf
    exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, _, hq, rfl, rfl⟩

/-- **"K8.tests"**: it says yes just where testsP says yes at the place's lengths of the vectors and the record's own parts,
and lays the returned ledger. -/
theorem sits_tests (p : K8.ParW) (run : S → Except String S)
    (h : ("K8.tests", run) ∈ (K8.whole p).after) (s s' : S) :
    run s = .ok s' ↔
      ∃ q Fc, partOf s = some q ∧ testsP p.nU q.tl q.F = .ok Fc ∧ s' = k8PartP.set s { q with F := Fc } := by
  have h' : ("K8.tests", run) ∈
      [(k8LsTail.1, fun s => (K8.atRecord (fun q => (k8LsTail.2 q).map fun q' => ((), q')) s).map (·.2)),
       ((k8Tests p.nU).1,
        fun s => (K8.atRecord (fun q => ((k8Tests p.nU).2 q).map fun q' => ((), q')) s).map (·.2))] := h
  have e : run =
      fun s => (K8.atRecord (fun q => ((k8Tests p.nU).2 q).map fun q' => ((), q')) s).map (·.2) := by
    simpa [k8LsTail, k8Tests] using h'
  subst e
  rw [afterRecord_ok]
  constructor
  · rintro ⟨q, q', hq, hf, rfl⟩
    change (testsP p.nU q.tl q.F).map _ = _ at hf
    cases ht : testsP p.nU q.tl q.F with
    | error e => rw [ht] at hf; cases hf
    | ok Fc =>
      rw [ht] at hf
      obtain rfl := Except.ok.inj hf
      exact ⟨q, Fc, hq, ht, rfl⟩
  · rintro ⟨q, Fc, hq, ht, rfl⟩
    refine ⟨q, _, hq, ?_, rfl⟩
    change (testsP p.nU q.tl q.F).map _ = _
    rw [ht]
    rfl

/-- **The claims half of "the smallness test's block sits".** -/
def K08SitsClaims : Prop :=
  ∀ p : K8.ParW,
    ((K8.whole p).claims.map (·.1) = ["K8.equations"] ∧
      (K8.whole p).after.map (·.1) = ["K8.lsTail", "K8.tests"]) ∧
    (∀ run, ("K8.equations", run) ∈ (K8.whole p).claims → ∀ front s s' cls,
      run front s = .ok (cls, s') ↔
        ∃ q tl' F1, partOf s = some q ∧
          equations (q.F.nClaim + front) q.tl q.funs q.F = .ok (tl', F1, cls) ∧
          s' = k8PartP.set s { q with tl := tl', F := F1 }) ∧
    (∀ run, ("K8.lsTail", run) ∈ (K8.whole p).after → ∀ s s',
      run s = .ok s' ↔
        ∃ q, partOf s = some q ∧
          s' = k8PartP.set s
            { q with tl := { q.tl with lsTail := q.F.LS.extract q.tl.slotA q.tl.slotB } }) ∧
    (∀ run, ("K8.tests", run) ∈ (K8.whole p).after → ∀ s s',
      run s = .ok s' ↔
        ∃ q Fc, partOf s = some q ∧ testsP p.nU q.tl q.F = .ok Fc ∧
          s' = k8PartP.set s { q with F := Fc })

theorem k08_sits_claims : K08SitsClaims := fun p =>
  ⟨sits_names p, fun run h front s s' cls => sits_equations p run h front s s' cls,
    fun run h s s' => sits_lsTail p run h s s', fun run h s s' => sits_tests p run h s s'⟩

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.k08_sits_claims
