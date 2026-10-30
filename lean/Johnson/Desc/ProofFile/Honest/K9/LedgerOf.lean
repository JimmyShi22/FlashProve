-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/LedgerOf.lean: K9's OWN SHARE OF THE LAWS ON THE RUNS (`RunsLaw`,
Honest/K9/FallGoodOf.lean): what the draw itself leaves. Statements and proofs ON THE VERIFIER's TEXT; no
prover is in this file, and no goal is stated.

  `get_set`, `set_fork`   K9's lens: behind `atS.set` at a state at which the lens answers, it answers again, and
                   shows the ledger and the book-keeping that were laid; the state's open ledger is that one
  `get_put`        the like behind a writing of the ledger alone (`S.putFork`)
  `all_zero`       an array that passes "all are the word 0" yields the word 0 at every index
  `DrawLeaves`, `draw_facts`   **a yes of the draw at x**: behind it the ledger holds x; it has one coefficient
                   for each slot; every coefficient is the word 0; no claim is counted; the plan's number
                   of claims is the one in front, and not 0; chi is marked as drawn; there is one mark for
                   each number of the plan, none set; the draw is marked as run; the arrays are those in
                   front with their weights laid out. From K9's own text at the draw. NO TEST AT THE DRAW
                   ASKS WHETHER THE EQUATION IS OPEN: that flag is what it was in front
  `drawnPart`, `draw_is`   THE WHOLE STATE BEHIND A YES OF THE DRAW, written out: the state in front with K9's part laid
                   anew: outside K9's part nothing turns; of K9's part chi stands in the ledger's one field theta
  `LedgerCore a a'`   what of the open ledger a run of claims must leave (its docstring lists it)
  `GatherKeeps g`  THE PREMISE ON THE GATHERER: what its runs do to the state leaves the ledger's core
  `KeysSame p g s` THE OTHER PREMISE: at any two challenges at which draw and gatherer return, the claims'
                   keys and the merge's slot are the same
  `runsLaw_of`     **these two give `RunsLaw`**: the clause `ledger` whole, and of `same` the two numbers

WHAT IS NOT CLAIMED. That a real segment's gatherer meets either premise: both are owed by the kinds whose
runs it calls. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.FallGoodOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (atS Where mergeOf drawAlone drawnClean drawn ledgerEmpty chiOf need)

/-- Behind `atS.set` the lens answers again, with the ledger and the book-keeping that were laid. -/
theorem get_set (s : S) (a q : VerifiableInference.Desc.K9.Part) (ha : atS.get? s = some a) :
    ∃ a₁, atS.get? (atS.set s q) = some a₁ ∧ a₁.F = q.F ∧ a₁.L = q.L := by
  cases hh : s.here with
  | between => simp [atS, S.link?, hh] at ha
  | fin x => simp [atS, S.link?, hh] at ha
  | mem x => simp [atS, S.link?, hh] at ha
  | lay x => simp [atS, S.putLink, S.putFork, S.link?, S.fork?, S.tl?,
      VerifiableInference.Desc.K9.usedOf, hh]
  | att x => simp [atS, S.putLink, S.putFork, S.link?, S.fork?, S.tl?,
      VerifiableInference.Desc.K9.usedOf, hh]
  | head x =>
    by_cases ho : x.opened = true
    · cases hsl : x.slot with
      | none => simp [atS, S.link?, S.fork?, S.tl?, VerifiableInference.Desc.K9.usedOf, hh, ho, hsl] at ha
      | some u => simp [atS, S.putLink, S.putFork, S.link?, S.fork?, S.tl?,
          VerifiableInference.Desc.K9.usedOf, hh, ho, hsl]
    · simp [atS, S.link?, hh, ho] at ha

/-- Behind `atS.set` the state's open ledger is the one that was laid. -/
theorem set_fork (s : S) (a q : VerifiableInference.Desc.K9.Part) (ha : atS.get? s = some a) :
    (atS.set s q).fork? = some q.F := by
  cases hh : s.here with
  | between => simp [atS, S.link?, hh] at ha
  | fin x => simp [atS, S.link?, hh] at ha
  | mem x => simp [atS, S.link?, hh] at ha
  | lay x => simp [atS, S.putLink, S.putFork, S.fork?, hh]
  | att x => simp [atS, S.putLink, S.putFork, S.fork?, hh]
  | head x =>
    by_cases ho : x.opened = true
    · simp [atS, S.putLink, S.putFork, S.fork?, hh, ho]
    · simp [atS, S.link?, hh, ho] at ha

/-- Behind a writing of the ledger the lens answers again, with the ledger that was written; and the ledger
in front is the one that the lens showed. -/
theorem get_put (s : S) (a : VerifiableInference.Desc.K9.Part) (ha : atS.get? s = some a) (G : Fork) :
    ∃ a₁, atS.get? (s.putFork G) = some a₁ ∧ a₁.F = G ∧ s.fork? = some a.F := by
  cases hh : s.here with
  | between => simp [atS, S.link?, hh] at ha
  | fin x => simp [atS, S.link?, hh] at ha
  | mem x => simp [atS, S.link?, hh] at ha
  | lay x =>
    simp only [atS, S.link?, S.fork?, S.tl?, VerifiableInference.Desc.K9.usedOf, hh,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at ha
    subst ha
    simp [atS, S.putFork, S.link?, S.fork?, S.tl?, VerifiableInference.Desc.K9.usedOf, hh]
  | att x =>
    simp only [atS, S.link?, S.fork?, S.tl?, VerifiableInference.Desc.K9.usedOf, hh,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at ha
    subst ha
    simp [atS, S.putFork, S.link?, S.fork?, S.tl?, VerifiableInference.Desc.K9.usedOf, hh]
  | head x =>
    by_cases ho : x.opened = true
    · cases hsl : x.slot with
      | none => simp [atS, S.link?, S.fork?, S.tl?, VerifiableInference.Desc.K9.usedOf, hh, ho, hsl] at ha
      | some u =>
        simp only [atS, S.link?, S.fork?, S.tl?, VerifiableInference.Desc.K9.usedOf, hh, ho, hsl,
          if_true, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at ha
        subst ha
        simp [atS, S.putFork, S.link?, S.fork?, S.tl?, VerifiableInference.Desc.K9.usedOf, hh, ho, hsl]
    · simp [atS, S.link?, hh, ho] at ha

theorem all_zero (A : Array E) (h : A.all isZeroE = true) (j : Nat) : A.getD j zeroE = zeroE := by
  by_cases hj : j < A.size
  · have h1 := (Array.all_eq_true.1 h) j hj
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
    exact isZeroE_eq h1
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    rfl

theorem need_ok {n : String} {b : Bool} {u : Unit} (h : need n b = .ok u) : b = true := by
  cases b with
  | true => rfl
  | false => exact nomatch h

/-- **What a yes of the draw at x leaves**: a: K9's part in front; a₁: behind. -/
structure DrawLeaves (a a₁ : VerifiableInference.Desc.K9.Part) (x : E) : Prop where
  chi : a₁.F.theta = x
  sized : a₁.F.LS.size = a₁.F.ns
  empty : ∀ j, a₁.F.LS.getD j zeroE = zeroE
  count : a₁.F.nClaim = 0
  plan : a₁.F.planClaimsF = a.F.planClaimsF
  planned : a.F.planClaimsF ≠ 0
  drawn : a₁.F.thetaDrawnF = true
  marks : a₁.F.kapMapF = Array.replicate a.F.planClaimsF false
  /-- NO TEST AT THE DRAW ASKS WHETHER THE EQUATION IS OPEN: the flag is what it was in front -/
  door : a₁.F.doorShutF = a.F.doorShutF
  ns : a₁.F.ns = a.F.ns
  trees : a₁.F.trees = (t2FillL a.F a.L.list).trees
  handed : a₁.L.handed = true

theorem draw_facts (p : Where) (s t₁ : S) (x : E) (a : VerifiableInference.Desc.K9.Part)
    (ha : atS.get? s = some a)
    (h : (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁) :
    ∃ a₁, atS.get? t₁ = some a₁ ∧ DrawLeaves a a₁ x := by
  obtain ⟨s₀, hs₀, h⟩ := bind_ok (x := atS.part s) h
  have e0 : s₀ = a := by
    unfold VerifiableInference.Desc.K9.Lens.part VerifiableInference.Desc.K9.there at hs₀
    rw [ha] at hs₀
    exact (Except.ok.inj hs₀).symm
  subst e0
  obtain ⟨chi, hchi, h⟩ := bind_ok (x := chiOf ⟨[], drawnOne x⟩) h
  have ex : chi = x := (Except.ok.inj hchi).symm
  subst ex
  obtain ⟨o, ho, h⟩ := bind_ok (x := drawnClean p.rows chi s₀.owed s₀.used s₀.L s₀.F) h
  obtain ⟨o', hd, ho⟩ := bind_ok (x := drawn p.rows chi s₀.owed s₀.used s₀.L s₀.F) ho
  obtain ⟨_, n1, ho⟩ := bind_ok (x := need "K9.ledger-empty" (ledgerEmpty s₀.F)) ho
  obtain ⟨_, n2, ho⟩ := bind_ok (x := need "K9.no-claim-yet" (s₀.F.nClaim == 0)) ho
  obtain ⟨_, n3, ho⟩ := bind_ok (x := need "K9.a-coefficient-a-slot" (s₀.F.LS.size == s₀.F.ns)) ho
  have eo : o' = o := Except.ok.inj ho
  subst eo
  obtain ⟨_, _, hd⟩ := bind_ok (x := need "K9.nothing-owed" s₀.owed.isNone) hd
  obtain ⟨_, _, hd⟩ := bind_ok (x := need "K9.slots-used" (s₀.L.list.planned && s₀.used == s₀.F.ns)) hd
  obtain ⟨_, _, hd⟩ := bind_ok (x := need "K9.link-ready"
    (s₀.L.list.link && !s₀.L.handed && s₀.L.moments == s₀.L.check.momentsOf s₀.L.link)) hd
  obtain ⟨_, _, hd⟩ := bind_ok (x := need "K9.drawn-once" !s₀.F.thetaDrawnF) hd
  obtain ⟨_, n5, hd⟩ := bind_ok (x := need "K9.claims-planned" (s₀.F.planClaimsF != 0)) hd
  have eF : o'.F = { t2FillL s₀.F s₀.L.list with
      theta := chi, thetaDrawnF := true,
      kapMapF := Array.replicate s₀.F.planClaimsF false } := by
    rw [← Except.ok.inj hd]
  have eL : o'.L.handed = true := by rw [← Except.ok.inj hd]
  obtain ⟨a₁, h1, h2, h3⟩ := get_set s s₀ { s₀ with owed := o'.owed, L := o'.L, F := o'.F } ha
  have et : t₁ = atS.set s { s₀ with owed := o'.owed, L := o'.L, F := o'.F } :=
    (Except.ok.inj h).symm
  have hE := need_ok n1
  unfold ledgerEmpty at hE
  rw [Bool.and_eq_true, Bool.and_eq_true] at hE
  have h2' : a₁.F = { t2FillL s₀.F s₀.L.list with
      theta := chi, thetaDrawnF := true,
      kapMapF := Array.replicate s₀.F.planClaimsF false } := h2.trans eF
  refine ⟨a₁, by rw [et]; exact h1, ?_⟩
  exact
    { chi := by rw [h2']
      sized := by rw [h2']; exact beq_iff_eq.1 (need_ok n3)
      empty := fun j => by rw [h2']; exact all_zero _ hE.1.2 j
      count := by rw [h2']; exact beq_iff_eq.1 (need_ok n2)
      plan := by rw [h2']; rfl
      planned := by simpa using need_ok n5
      drawn := by rw [h2']
      marks := by rw [h2']
      door := by rw [h2']; rfl
      ns := by rw [h2']; rfl
      trees := by rw [h2']
      handed := by rw [h3]; exact eL }

/-- K9's part behind the draw of x, written out. a: K9's part in front. -/
def drawnPart (p : Where) (a : VerifiableInference.Desc.K9.Part) (x : E) : VerifiableInference.Desc.K9.Part :=
  { a with
    owed := some p.rows
    L := { a.L with list := { a.L.list with used := a.used }, handed := true }
    F := { t2FillL a.F a.L.list with
      theta := x, thetaDrawnF := true, kapMapF := Array.replicate a.F.planClaimsF false } }

/-- **THE WHOLE STATE BEHIND A YES OF THE DRAW**: the state in front with K9's part laid anew: OUTSIDE K9's PART
NOTHING TURNS, AND OF K9's PART chi STANDS IN ONE FIELD ALONE. -/
theorem draw_is (p : Where) (s t₁ : S) (x : E) (a : VerifiableInference.Desc.K9.Part)
    (ha : atS.get? s = some a)
    (h : (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁) :
    t₁ = atS.set s (drawnPart p a x) := by
  obtain ⟨s₀, hs₀, h⟩ := bind_ok (x := atS.part s) h
  have e0 : s₀ = a := by
    unfold VerifiableInference.Desc.K9.Lens.part VerifiableInference.Desc.K9.there at hs₀
    rw [ha] at hs₀
    exact (Except.ok.inj hs₀).symm
  subst e0
  obtain ⟨chi, hchi, h⟩ := bind_ok (x := chiOf ⟨[], drawnOne x⟩) h
  have ex : chi = x := (Except.ok.inj hchi).symm
  subst ex
  obtain ⟨o, ho, h⟩ := bind_ok (x := drawnClean p.rows chi s₀.owed s₀.used s₀.L s₀.F) h
  obtain ⟨o', hd, ho⟩ := bind_ok (x := drawn p.rows chi s₀.owed s₀.used s₀.L s₀.F) ho
  obtain ⟨_, _, ho⟩ := bind_ok (x := need "K9.ledger-empty" (ledgerEmpty s₀.F)) ho
  obtain ⟨_, _, ho⟩ := bind_ok (x := need "K9.no-claim-yet" (s₀.F.nClaim == 0)) ho
  obtain ⟨_, _, ho⟩ := bind_ok (x := need "K9.a-coefficient-a-slot" (s₀.F.LS.size == s₀.F.ns)) ho
  have eo : o' = o := Except.ok.inj ho
  subst eo
  obtain ⟨_, _, hd⟩ := bind_ok (x := need "K9.nothing-owed" s₀.owed.isNone) hd
  obtain ⟨_, _, hd⟩ := bind_ok (x := need "K9.slots-used" (s₀.L.list.planned && s₀.used == s₀.F.ns)) hd
  obtain ⟨_, _, hd⟩ := bind_ok (x := need "K9.link-ready"
    (s₀.L.list.link && !s₀.L.handed && s₀.L.moments == s₀.L.check.momentsOf s₀.L.link)) hd
  obtain ⟨_, _, hd⟩ := bind_ok (x := need "K9.drawn-once" !s₀.F.thetaDrawnF) hd
  obtain ⟨_, _, hd⟩ := bind_ok (x := need "K9.claims-planned" (s₀.F.planClaimsF != 0)) hd
  rw [← Except.ok.inj h, ← Except.ok.inj hd]
  rfl

/-- What of the open ledger a run of claims must leave: chi, the slots' coefficients, the number of slots, the
plan's number of claims, the number of claims added, the two flags, the marks, and the arrays' frame (all of
the arrays but the weights' values). -/
structure LedgerCore (a a' : VerifiableInference.Desc.K9.Part) : Prop where
  theta : a'.F.theta = a.F.theta
  LS : a'.F.LS = a.F.LS
  ns : a'.F.ns = a.F.ns
  plan : a'.F.planClaimsF = a.F.planClaimsF
  count : a'.F.nClaim = a.F.nClaim
  door : a'.F.doorShutF = a.F.doorShutF
  drawn : a'.F.thetaDrawnF = a.F.thetaDrawnF
  marks : a'.F.kapMapF = a.F.kapMapF
  frame : treesFrame a'.F.trees = treesFrame a.F.trees

theorem LedgerCore.refl (a : VerifiableInference.Desc.K9.Part) : LedgerCore a a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem LedgerCore.trans {a b c : VerifiableInference.Desc.K9.Part} (h1 : LedgerCore a b)
    (h2 : LedgerCore b c) : LedgerCore a c :=
  ⟨h2.theta.trans h1.theta, h2.LS.trans h1.LS, h2.ns.trans h1.ns, h2.plan.trans h1.plan,
    h2.count.trans h1.count, h2.door.trans h1.door, h2.drawn.trans h1.drawn,
    h2.marks.trans h1.marks, h2.frame.trans h1.frame⟩

/-- **The premise on the gatherer.** -/
def GatherKeeps (g : S → Except String (List Claim × S)) : Prop :=
  ∀ t cls e a a', g t = .ok (cls, e) → atS.get? t = some a → atS.get? e = some a' → LedgerCore a a'

/-- **The other premise.** -/
def KeysSame (p : Where) (g : S → Except String (List Claim × S)) (s : S) : Prop :=
  ∀ x x' y y', gathered p g s x = some y → gathered p g s x' = some y' →
    y.2.2.map slotKey = y'.2.2.map slotKey ∧ mergeOf y.1 = mergeOf y'.1

/-- What `gathered` yields, taken apart. -/
theorem gathered_split (p : Where) (g : S → Except String (List Claim × S)) (s : S) (x : E)
    (y : S × VerifiableInference.Desc.K9.Part × List Claim) (h : gathered p g s x = some y) :
    ∃ t₁, (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁ ∧
      g t₁ = .ok (y.2.2, y.1) ∧ atS.get? y.1 = some y.2.1 := by
  unfold gathered at h
  split at h
  · rename_i t₁ ht
    split at h
    · rename_i z hz
      cases hq : atS.get? z.2 with
      | none => rw [hq] at h; exact nomatch h
      | some b =>
        rw [hq] at h
        have e1 := Option.some.inj h
        subst e1
        exact ⟨t₁, ht, hz, hq⟩
    · exact nomatch h
  · exact nomatch h

/-- **The two premises give `RunsLaw`.** -/
theorem runsLaw_of (p : Where) (g : S → Except String (List Claim × S)) (s : S)
    (hk : GatherKeeps g) (hs : KeysSame p g s) : RunsLaw p g s := by
  -- the facts at one challenge
  have one : ∀ x y, gathered p g s x = some y →
      ∃ a, atS.get? s = some a ∧ y.2.1.F.theta = x ∧ y.2.1.F.LS.size = y.2.1.F.ns ∧
        (∀ j, y.2.1.F.LS.getD j zeroE = zeroE) ∧ y.2.1.F.nClaim = 0 ∧
        y.2.1.F.planClaimsF = a.F.planClaimsF := by
    intro x y hy
    obtain ⟨t₁, hd, hg, he⟩ := gathered_split p g s x y hy
    have hsome : ∃ a, atS.get? s = some a := by
      obtain ⟨s₀, hs₀, _⟩ := bind_ok (x := atS.part s) hd
      unfold VerifiableInference.Desc.K9.Lens.part VerifiableInference.Desc.K9.there at hs₀
      cases hq : atS.get? s with
      | none => rw [hq] at hs₀; exact nomatch hs₀
      | some a => exact ⟨a, rfl⟩
    obtain ⟨a, ha⟩ := hsome
    obtain ⟨a₁, h1, f⟩ := draw_facts p s t₁ x a ha hd
    have k := hk t₁ y.2.2 y.1 a₁ y.2.1 hg h1 he
    exact ⟨a, ha, by rw [k.theta, f.chi], by rw [k.LS, k.ns, f.sized],
      fun j => by rw [k.LS]; exact f.empty j, by rw [k.count, f.count], by rw [k.plan, f.plan]⟩
  refine ⟨fun x y hy => ?_, fun x x' y y' hy hy' => ?_⟩
  · obtain ⟨_, _, f1, f2, f3, _, _⟩ := one x y hy
    exact ⟨f1, f2, f3⟩
  · obtain ⟨a, ha, _, _, _, f4, f5⟩ := one x y hy
    obtain ⟨a', ha', _, _, _, f4', f5'⟩ := one x' y' hy'
    have ea : a = a' := Option.some.inj (ha.symm.trans ha')
    obtain ⟨k, m⟩ := hs x x' y y' hy hy'
    exact ⟨k, by rw [f5, f5', ea], by rw [f4, f4'], m⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.get_set
#print axioms ProofFile.Honest.K9.set_fork
#print axioms ProofFile.Honest.K9.get_put
#print axioms ProofFile.Honest.K9.all_zero
#print axioms ProofFile.Honest.K9.draw_is
#print axioms ProofFile.Honest.K9.draw_facts
#print axioms ProofFile.Honest.K9.gathered_split
#print axioms ProofFile.Honest.K9.runsLaw_of
#print axioms ProofFile.Honest.K9.need_ok
#print axioms ProofFile.Honest.K9.DrawLeaves
#print axioms ProofFile.Honest.K9.drawnPart
#print axioms ProofFile.Honest.K9.LedgerCore
#print axioms ProofFile.Honest.K9.LedgerCore.refl
#print axioms ProofFile.Honest.K9.LedgerCore.trans
#print axioms ProofFile.Honest.K9.GatherKeeps
#print axioms ProofFile.Honest.K9.KeysSame
