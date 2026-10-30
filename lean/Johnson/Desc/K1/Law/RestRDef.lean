-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/RestRDef.lean: THE TERMS OF Johnson/Desc/K1/Law/RestDef.lean A THIRD TIME, AT THE
CUT BETWEEN ITS OWN AND RestQDef.lean's: what a later commitment of kind K1 does not write, WITHOUT
THE APPROXIMATE RANGE PROOF's PART OF THE STATE (the field tl) BUT WITH THE READS' TABLES (the field
t). Definitions, and the laws that are general in the run: RestQDef.lean's, lemma for lemma.

Why. Five runs of the output head's segment read the tables, so they are no members at RestQDef.lean's
cut. The reads' quiet step of that segment lays tl anew as well: so RestDef.lean's cut does not reach
across it. None of the five reads tl.
THREE FILES OF ONE FORM: a form general in "what is taken off" would hold all three. Not done here.
Main names (namespace VerifiableInference.Desc.K1.R): blankHere, blank, restOf, RestAlike (.symm,
.trans, .fork, .lookHeard, .putFork, .out), alike_of, Respects, ReadsRest (.alike),
readsRest_lookHeard, respects_read, respects_readRest, respects_guarded, readerOf_imp,
readerOf_alike, PairStays, readersOfLink_alike.
What is not claimed. That any sub-protocol's accept leaves the rest. Respects of any kind's run.
Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.RestDef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1.R
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S Here)
open VerifiableInference.Desc.K9 (Read Readers RunOf readerOf lateOf ownRow LinkHoles statesOfLink
  readersOfLink)

/-! ## The rest, without the approximate range proof's part -/

/-- The open segment's state without the approximate range proof's part. -/
def blankHere : Here → Here
  | .lay a => .lay { a with tl := {} }
  | .att a => .att { a with tl := {} }
  | .head a => .head { a with tl := {} }
  | h => h

def blank (s : S) : S := { s with here := blankHere s.here }

/-- **The chain's state without all that a later commitment writes and without that part.** -/
def restOf (s : S) : S := blank (K1.restOf s)

/-- Two states part in nothing but that. -/
def RestAlike (s s' : S) : Prop := restOf s = restOf s'

theorem RestAlike.symm {s s' : S} (h : RestAlike s s') : RestAlike s' s := Eq.symm h

theorem RestAlike.trans {s t u : S} (h : RestAlike s t) (k : RestAlike t u) : RestAlike s u :=
  Eq.trans h k

/-- Alike at the narrower cut is alike here. -/
theorem alike_of {s s' : S} (h : K1.RestAlike s s') : RestAlike s s' := congrArg blank h

/-! ## What reads the rest alone -/

theorem fork_rest (s : S) : (restOf s).fork? = s.fork?.map forkRest := by
  cases hh : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [restOf, blank, blankHere, K1.restOf, hereRest, S.fork?, hh, ho]
  | _ => simp [restOf, blank, blankHere, K1.restOf, hereRest, S.fork?, hh]

theorem lookHeard_rest (s : S) : (restOf s).lookHeard? = s.lookHeard? := by
  cases hh : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [restOf, blank, blankHere, K1.restOf, hereRest, S.lookHeard?, hh, ho]
  | _ => simp [restOf, blank, blankHere, K1.restOf, hereRest, S.lookHeard?, hh]

theorem RestAlike.fork {s s' : S} (h : RestAlike s s') {F : Fork} (hF : s.fork? = some F) :
    ∃ F', s'.fork? = some F' ∧ forkRest F' = forkRest F := by
  have e : s.fork?.map forkRest = s'.fork?.map forkRest := by
    rw [← fork_rest, ← fork_rest, h]
  rw [hF, Option.map_some] at e
  obtain ⟨F', h1, h2⟩ := Option.map_eq_some_iff.1 e.symm
  exact ⟨F', h1, h2⟩

theorem RestAlike.lookHeard {s s' : S} (h : RestAlike s s') : s.lookHeard? = s'.lookHeard? := by
  rw [← lookHeard_rest s, ← lookHeard_rest s', h]

/-- Ledgers that part in the marks alone, laid into such states. -/
theorem RestAlike.putFork {s s' : S} (h : RestAlike s s') {G G' : Fork}
    (hG : forkRest G = forkRest G') :
    RestAlike (s.putFork G) (s'.putFork G') := by
  have key : ∀ (t : S) (X : Fork), restOf (t.putFork X) = (restOf t).putFork (forkRest X) := by
    intro t X
    cases hh : t.here with
    | head a => by_cases ho : a.opened = true <;> simp [restOf, blank, blankHere, K1.restOf, hereRest, S.putFork, hh, ho]
    | _ => simp [restOf, blank, blankHere, K1.restOf, hereRest, S.putFork, hh]
  unfold RestAlike
  rw [key, key, h, hG]

/-- **A RUN READS THE REST ALONE**: handed no claim in front, at two states that part in nothing
but what a later moment's sending writes, it lays the same claims and leaves two such states. -/
def Respects (ρ : Nat → S → Except String (List Claim × S)) : Prop :=
  ∀ s s', RestAlike s s' → ∀ cl t, ρ 0 s = .ok (cl, t) →
    ∃ t', ρ 0 s' = .ok (cl, t') ∧ RestAlike t t'

theorem readerOf_imp (states : Nat → List (RunOf S)) (b : Nat) (name : String)
    (hr : ∀ r, (states b).find? (fun r => r.1 == name) = some r → Respects r.2) {s s' : S}
    (hA : RestAlike s s') (X : Read) (h : readerOf states b name s = some X) :
    readerOf states b name s' = some X := by
  unfold readerOf at h ⊢
  obtain ⟨r, hr1, h⟩ := Option.bind_eq_some_iff.1 h
  rw [hr1, Option.bind_some]
  split at h
  · rename_i z F e1 e2
    obtain ⟨G, hG, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨t', f1, f2⟩ := hr r hr1 s s' hA z.1 z.2 e1
    obtain ⟨F', g1, g2⟩ := hA.fork e2
    obtain ⟨G', k1, k2⟩ := f2.fork hG
    rw [f1, g1]
    show (t'.fork?).bind _ = some X
    rw [k1, Option.bind_some, lateOf_rest g2 k2]
    simp only [ownRow_rest g2]
    exact h
  · cases h

/-- **THE GENERAL LAW**: the reader that is the run itself answers alike at two such states. -/
theorem readerOf_alike (states : Nat → List (RunOf S)) (b : Nat) (name : String)
    (hr : ∀ r, (states b).find? (fun r => r.1 == name) = some r → Respects r.2) {s s' : S}
    (hA : RestAlike s s') : readerOf states b name s' = readerOf states b name s := by
  cases h : readerOf states b name s with
  | some X => exact readerOf_imp states b name hr hA X h
  | none =>
    cases h' : readerOf states b name s' with
    | none => rfl
    | some X =>
      rw [readerOf_imp states b name hr hA.symm X h'] at h
      cases h

/-- What is asked of a link's readers at a pair (block, name): of the hole "small" at the smallness
test's equations; else of the run of that name and of the hole "silent". -/
def PairStays (H : LinkHoles) (l : Link S Claim) (p : Nat × String) : Prop :=
  if p.2 == "K8.equations" then ∀ s s', RestAlike s s' → H.small s' = H.small s
  else (∀ r, (statesOfLink l p.1).find? (fun r => r.1 == p.2) = some r → Respects r.2) ∧
    ∀ s s', RestAlike s s' → H.silent p.1 p.2 s' = H.silent p.1 p.2 s

theorem readersOfLink_alike (H : LinkHoles) (l : Link S Claim) (p : Nat × String)
    (hp : PairStays H l p) {s s' : S} (hA : RestAlike s s') :
    (readersOfLink H l).forms p.1 p.2 s' = (readersOfLink H l).forms p.1 p.2 s := by
  unfold PairStays at hp
  show (if p.2 == "K8.equations" then H.small s' else
      match readerOf (statesOfLink l) p.1 p.2 s' with
      | some R => some R
      | Option.none => H.silent p.1 p.2 s') =
    (if p.2 == "K8.equations" then H.small s else
      match readerOf (statesOfLink l) p.1 p.2 s with
      | some R => some R
      | Option.none => H.silent p.1 p.2 s)
  by_cases hn : (p.2 == "K8.equations") = true
  · rw [if_pos hn] at hp ⊢
    rw [if_pos hn]
    exact hp s s' hA
  · rw [if_neg hn] at hp ⊢
    rw [if_neg hn, readerOf_alike _ _ _ hp.1 hA, hp.2 s s' hA]

/-! ## A function of the chain's state that reads the rest alone -/

/-- f does not turn when all that a later moment's sending writes is taken off the state. -/
def ReadsRest {α : Type} (f : S → α) : Prop := ∀ s, f (restOf s) = f s

theorem ReadsRest.alike {α : Type} {f : S → α} (h : ReadsRest f) {s s' : S} (hA : RestAlike s s') :
    f s' = f s := by
  rw [← h s', ← h s, hA]

theorem readsRest_lookHeard : ReadsRest S.lookHeard? := lookHeard_rest

/-! ## A run that reads the state, lays claims and leaves the state -/

theorem respects_read (read : S → Except String (List Claim))
    (h : ∀ s s', RestAlike s s' → read s' = read s) :
    Respects fun _ s => (read s).map fun l => (l, s) := by
  intro s s' hA cl t e
  obtain ⟨l, hl, e'⟩ := okOfMap _ _ _ e
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
  refine ⟨s', ?_, hA⟩
  show (read s').map _ = _
  rw [h s s' hA, hl]
  rfl

theorem respects_readRest (read : S → Except String (List Claim)) (h : ReadsRest read) :
    Respects fun _ s => (read s).map fun l => (l, s) :=
  respects_read read fun _ _ hA => h.alike hA

/-! ## The seat's guard around a run -/

theorem RestAlike.out {s s' : S} (h : RestAlike s s') : s.out = s'.out := by
  have := congrArg S.out h
  exact this

/-- The guard that a seat lays around a block's runs (Block.guarded, Johnson/Desc/SeatGuard.lean):
where its test answers alike at such states. -/
theorem respects_guarded (same : S → S → Bool)
    (hs : ∀ s s' t t', RestAlike s s' → RestAlike t t' → same s' t' = same s t)
    (ρ : Nat → S → Except String (List Claim × S)) (h : Respects ρ) :
    Respects fun n t => (ρ n t).bind fun y => (seatSame same t y.2).map fun _ => y := by
  intro s s' hA cl t e
  obtain ⟨y, hy, e⟩ := okOfBind _ _ _ e
  obtain ⟨u, hu, rfl⟩ := okOfMap _ _ _ e
  obtain ⟨t', f1, f2⟩ := h s s' hA cl t hy
  refine ⟨t', ?_, f2⟩
  show ((ρ 0 s').bind fun y => (seatSame same s' y.2).map fun _ => y) = _
  rw [f1]
  show (seatSame same s' t').map _ = _
  unfold seatSame at hu ⊢
  rw [hs s s' t t' hA f2]
  split at hu
  · rename_i hb
    rw [if_pos hb]
    rfl
  · cases hu

end VerifiableInference.Desc.K1.R

#print axioms VerifiableInference.Desc.K1.R.alike_of
#print axioms VerifiableInference.Desc.K1.R.fork_rest
#print axioms VerifiableInference.Desc.K1.R.lookHeard_rest
#print axioms VerifiableInference.Desc.K1.R.RestAlike.fork
#print axioms VerifiableInference.Desc.K1.R.RestAlike.lookHeard
#print axioms VerifiableInference.Desc.K1.R.RestAlike.putFork
#print axioms VerifiableInference.Desc.K1.R.readerOf_imp
#print axioms VerifiableInference.Desc.K1.R.readerOf_alike
#print axioms VerifiableInference.Desc.K1.R.readersOfLink_alike
#print axioms VerifiableInference.Desc.K1.R.ReadsRest.alike
#print axioms VerifiableInference.Desc.K1.R.respects_read
#print axioms VerifiableInference.Desc.K1.R.respects_readRest
#print axioms VerifiableInference.Desc.K1.R.RestAlike.out
#print axioms VerifiableInference.Desc.K1.R.respects_guarded
