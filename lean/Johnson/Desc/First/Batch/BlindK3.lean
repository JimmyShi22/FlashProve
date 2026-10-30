-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/BlindK3.lean: THE FIRST REAL RUNS THAT ARE SHOWN BLIND TO THE ADDING
(Johnson/Desc/First/Batch/ObjectsLaw.lean: Blind), at the first chain's state S and the real adding
(addsOf atS atS_ok): the lookup's run "objects", at the lookup on the calls and at the lookup on the
digits. No Mathlib.
  `addAll_paid`: marking a debt as paid and adding claims commute: the adding neither reads nor
      writes the ledger's list of debts.
  `objectsCalls` | `objectsDigits`: the run's text, written out; `objectsCalls_is` |
      `objectsDigits_is`: it is the run "objects" that K3's block states at that seat (by rfl).
  `objectsCalls_blind` | `objectsDigits_blind`.
Limits: the run "objects" at the two seats alone. A law on two programs' commuting. Nothing on
soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.ObjectsLawAtS
import Johnson.Desc.First.Look.K3Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

/-! ## marking a debt and adding commute -/

theorem kapTake_paid (F : Fork) (i c : Nat) :
    (F.paid i).kapTake c = (F.kapTake c).map fun x => (x.1, x.2.paid i) := by
  cases h1 : F.doorShutF <;> cases h2 : F.kapMapF.isEmpty <;> cases h3 : F.thetaDrawnF <;>
    cases h4 : (decide (c < F.planClaimsF) && F.kapMapF.size == F.planClaimsF &&
      !F.kapMapF.getD c true) <;>
    (simp [Fork.kapTake, Fork.kapAt, Fork.paid, h1, h2, h3, h4] <;> rfl)

theorem kap_paid (F : Fork) (i : Nat) :
    (F.paid i).kap = F.kap.map fun x => (x.1, x.2.paid i) := by
  unfold Fork.kap
  rw [show (F.paid i).nClaim = F.nClaim from rfl, kapTake_paid]
  cases F.kapTake F.nClaim <;> rfl

theorem push_paid (F : Fork) (i : Nat) (w : E) (a : Aff) :
    (F.paid i).push w a = (F.push w a).map (·.paid i) := by
  cases h1 : F.doorShutF <;> cases h2 : a.ents.foldlM (Fork.pushEnt w) F.trees <;>
    cases h3 : a.slots.foldlM (Fork.pushSlot w F.ns) F.LS <;>
    (simp [Fork.push, Fork.paid, h1, h2, h3] <;> rfl)

theorem pushRuns_paid (F : Fork) (i : Nat) (k : E) (runs : Array Run2) :
    (F.paid i).pushRuns k runs = (F.pushRuns k runs).map (·.paid i) := by
  cases h : runs.foldlM (pushRun k) F.trees <;>
    (simp [Fork.pushRuns, Fork.paid, h] <;> rfl)

/-- The weight of a claim, as addClaim reckons it. -/
def weightOf (F : Fork) (x : E × Fork) (cl : Claim) : Option E :=
  match cl.eqFirst with
  | none => some x.1
  | some first =>
    if F.nClaim < F.planClaimsF then some (powE F.theta (F.planClaimsF + first)) else none

/-- The claim added under a weight. -/
def addWith (k : Option E) (G : Fork) (cl : Claim) : Option Fork :=
  k.bind fun k => (G.push k cl.form).bind (·.pushRuns k cl.runs)

theorem addClaim_eq (F : Fork) (cl : Claim) :
    addClaim F cl = F.kap.bind fun x => addWith (weightOf F x cl) x.2 cl := rfl

theorem addWith_paid (k : Option E) (G : Fork) (cl : Claim) (i : Nat) :
    addWith k (G.paid i) cl = (addWith k G cl).map (·.paid i) := by
  cases k with
  | none => rfl
  | some k =>
    simp only [addWith, Option.bind]
    rw [push_paid]
    cases G.push k cl.form with
    | none => rfl
    | some P => exact pushRuns_paid P i k cl.runs

theorem addClaim_paid (F : Fork) (cl : Claim) (i : Nat) :
    addClaim (F.paid i) cl = (addClaim F cl).map (·.paid i) := by
  rw [addClaim_eq, addClaim_eq, kap_paid]
  cases F.kap with
  | none => rfl
  | some x => exact addWith_paid (weightOf F x cl) x.2 cl i

theorem addAll_paid (i : Nat) : ∀ (cs : List Claim) (F : Fork),
    addAll (F.paid i) cs = (addAll F cs).map (·.paid i) := by
  intro cs
  induction cs with
  | nil => intro F; rfl
  | cons c l ih =>
    intro F
    unfold addAll
    rw [List.foldlM_cons, List.foldlM_cons, addClaim_paid]
    cases addClaim F c with
    | none => rfl
    | some G => exact ih G

/-! ## what the lens and the state do with a ledger laid anew -/

/-- The lens's ledger is the state's. -/
theorem get_fork (t : S) (p : Part) (h : atS.get? t = some p) : t.fork? = some p.F := by
  cases hh : t.here with
  | between => simp [atS, S.link?, hh] at h
  | fin a => simp [atS, S.link?, hh] at h
  | mem a => simp [atS, S.link?, hh] at h
  | lay a =>
    simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh] at h
    subst h
    simp [S.fork?, hh]
  | att a =>
    simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh] at h
    subst h
    simp [S.fork?, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [atS, S.link?, hh, ho] at h
    | true =>
      cases hsl : a.slot with
      | none => simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh, ho, hsl] at h
      | some n =>
        simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh, ho, hsl] at h
        subst h
        simp [S.fork?, hh, ho]

/-- A ledger with the same next free slot, laid by putFork: the lens reads the part with it. -/
theorem get_putFork (t : S) (p : Part) (F₁ : Fork) (h : atS.get? t = some p)
    (hn : F₁.next = p.F.next) : atS.get? (t.putFork F₁) = some { p with F := F₁ } := by
  cases hh : t.here with
  | between => simp [atS, S.link?, hh] at h
  | fin a => simp [atS, S.link?, hh] at h
  | mem a => simp [atS, S.link?, hh] at h
  | lay a =>
    simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh] at h
    subst h
    simp [atS, S.link?, S.fork?, S.tl?, usedOf, S.putFork, hh, owedOf]
  | att a =>
    simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh] at h
    subst h
    simp at hn
    simp [atS, S.link?, S.fork?, S.tl?, usedOf, S.putFork, hh, owedOf, hn]
  | head a =>
    cases ho : a.opened with
    | false => simp [atS, S.link?, hh, ho] at h
    | true =>
      cases hsl : a.slot with
      | none => simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh, ho, hsl] at h
      | some n =>
        simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh, ho, hsl] at h
        subst h
        simp [atS, S.link?, S.fork?, S.tl?, usedOf, S.putFork, hh, ho, hsl, owedOf]

/-- Where the lens answers nothing, it answers nothing behind putFork. -/
theorem get_none_putFork (t : S) (F₁ : Fork) (h : atS.get? t = none) :
    atS.get? (t.putFork F₁) = none := by
  cases hh : t.here with
  | between => simp [atS, S.link?, S.putFork, hh]
  | fin a => simp [atS, S.link?, S.putFork, hh]
  | mem a => simp [atS, S.link?, S.putFork, hh]
  | lay a => simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh] at h
  | att a => simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh] at h
  | head a =>
    cases ho : a.opened with
    | false => simp [atS, S.link?, S.putFork, hh, ho]
    | true =>
      cases hsl : a.slot with
      | none => simp [atS, S.link?, S.fork?, S.tl?, usedOf, S.putFork, hh, ho, hsl]
      | some n => simp [atS, S.link?, S.fork?, S.tl?, usedOf, hh, ho, hsl] at h

/-- Laying a ledger by putFork and laying the part by the lens, either way round. -/
theorem set_putFork (t : S) (p : Part) (F₁ G H : Fork) :
    atS.set (t.putFork F₁) { p with F := H } = (atS.set t { p with F := G }).putFork H := by
  cases hh : t.here with
  | between => simp [atS, S.putLink, S.putFork, hh]
  | fin a => simp [atS, S.putLink, S.putFork, hh]
  | mem a => simp [atS, S.putLink, S.putFork, hh]
  | lay a => simp [atS, S.putLink, S.putFork, hh]
  | att a => simp [atS, S.putLink, S.putFork, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [atS, S.putLink, S.putFork, hh, ho]
    | true => simp [atS, S.putLink, S.putFork, hh, ho]

/-- The lens's laying turns neither what the lookup on the calls left nor the smallness test's
record. -/
theorem set_heard (t : S) (q : Part) :
    (atS.set t q).lookHeard? = t.lookHeard? ∧ (atS.set t q).tl? = t.tl? := by
  cases hh : t.here with
  | between => simp [atS, S.putLink, S.putFork, S.lookHeard?, S.tl?, hh]
  | fin a => simp [atS, S.putLink, S.putFork, S.lookHeard?, S.tl?, hh]
  | mem a => simp [atS, S.putLink, S.putFork, S.lookHeard?, S.tl?, hh]
  | lay a => simp [atS, S.putLink, S.putFork, S.lookHeard?, S.tl?, hh]
  | att a => simp [atS, S.putLink, S.putFork, S.lookHeard?, S.tl?, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [atS, S.putLink, S.putFork, S.lookHeard?, S.tl?, hh, ho]
    | true => simp [atS, S.putLink, S.putFork, S.lookHeard?, S.tl?, hh, ho]

/-! ## the run -/

/-- The lookup's run "objects", general in where what was heard is read. -/
def objectsBy (heard : S → Option Forest.Heard) : Fn S := fun _ s => do
  let F ← named "K3 objects: no sub-proof is open" s.fork?
  let g ← named "K3 objects: nothing was heard" (heard s)
  pure (g.rows.toList.map (fun a => ({ form := a } : Claim)), s.putFork (F.paid g.owedObjects))

/-- **A run of that form is Blind**, if the lens's laying does not turn what it reads as heard. -/
theorem objectsBy_blind (heard : S → Option Forest.Heard)
    (hh : ∀ (t : S) (q : Part), heard (atS.set t q) = heard t) :
    Blind (addsOf atS atS_ok) (objectsBy heard) where
  moves := by
    intro k t t' cs hadd
    obtain ⟨p, hp, h1⟩ := bind_some (show (atS.get? t).bind _ = some t' from hadd)
    obtain ⟨G, hG, ht'⟩ := map_some h1
    have hf := get_fork t p hp
    have hp' := atS_ok.getSet t p cs G hp hG
    have hf' := get_fork _ _ hp'
    subst ht'
    cases hg : heard t with
    | none => simp [objectsBy, hf, hf', hh, hg, named, bind, Except.bind]
    | some g =>
      simp only [objectsBy, hf, hf', hh, hg, named, bind, Except.bind, pure, Except.pure]
      refine ⟨_, rfl, ?_⟩
      show addAt atS (t.putFork (p.F.paid g.owedObjects)) cs = _
      unfold addAt
      rw [get_putFork t p (p.F.paid g.owedObjects) hp rfl]
      simp only [Option.bind]
      rw [addAll_paid, hG]
      simp only [Option.map]
      rw [set_putFork t p (p.F.paid g.owedObjects) G (G.paid g.owedObjects)]
  keeps := by
    intro n t y cs hy
    show (addAt atS y.2 cs).isSome = (addAt atS t cs).isSome
    unfold addAt
    cases hp : atS.get? t with
    | none =>
      cases hf : t.fork? with
      | none => simp [objectsBy, hf, named, bind, Except.bind] at hy
      | some F =>
        cases hg : heard t with
        | none => simp [objectsBy, hf, hg, named, bind, Except.bind] at hy
        | some g =>
          simp [objectsBy, hf, hg, named, bind, Except.bind, pure, Except.pure] at hy
          subst hy
          rw [get_none_putFork t _ hp]
          rfl
    | some p =>
      have hf := get_fork t p hp
      cases hg : heard t with
      | none => simp [objectsBy, hf, hg, named, bind, Except.bind] at hy
      | some g =>
        simp [objectsBy, hf, hg, named, bind, Except.bind, pure, Except.pure] at hy
        subst hy
        rw [get_putFork t p (p.F.paid g.owedObjects) hp rfl]
        simp only [Option.bind]
        rw [addAll_paid]
        cases addAll p.F cs <;> rfl

/-- At the lookup on the calls. -/
def objectsCalls : Fn S := objectsBy S.lookHeard?

/-- At the lookup on the smallness test's digits. -/
def objectsDigits : Fn S := objectsBy fun s => s.tl?.bind (·.heard)

/-- It is the run "objects" that K3's block states at the calls' seat. -/
theorem objectsCalls_is (piece : Nat) (laid : Array Nat) (before : List (Nat × Nat))
    (p : First.Look.P) (guests : List (First.Look.Guest S Claim)) :
    (K3.block (K3.seatCalls fun a => ({ form := a } : Claim)) piece laid before p
      guests).claims.lookup "objects" = some objectsCalls := rfl

/-- It is the run "objects" that K3's block states at the digits' seat. -/
theorem objectsDigits_is (piece : Nat) (laid : Array Nat) (before : List (Nat × Nat))
    (p : First.Look.P) (guests : List (First.Look.Guest S Claim)) :
    (K3.block (K3.seatDigits fun a => ({ form := a } : Claim)) piece laid before p
      guests).claims.lookup "objects" = some objectsDigits := rfl

/-- **K3's "objects" at the calls is Blind to the real adding.** -/
theorem objectsCalls_blind : Blind (addsOf atS atS_ok) objectsCalls :=
  objectsBy_blind _ fun t q => (set_heard t q).1

/-- **K3's "objects" at the digits is Blind to the real adding.** -/
theorem objectsDigits_blind : Blind (addsOf atS atS_ok) objectsDigits :=
  objectsBy_blind _ fun t q => by rw [(set_heard t q).2]

end VerifiableInference.Desc.K9
