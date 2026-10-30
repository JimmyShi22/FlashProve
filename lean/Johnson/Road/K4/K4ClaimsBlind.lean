-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4ClaimsBlind.lean: K4's TWO RUNS OF CLAIMS ("front", "back") COMMUTE WITH THE ONE
WRITING OF THE APPROXIMATE RANGE PROOF's DRAW, AND LEAVE WHAT GOES ON TO THE LATER CHAINS.
Statements and proofs: unfolding, by the three forms of a draw's accept (`drawn_ind`,
Johnson/Desc/First/K8/BlindPub.lean).

  `runS`: a run of K4's own term at the verifier's state, written out. `k4Core`: what a reader of
    the run sees of its return: the forms and the ledger behind: a function of K4's own part and the
    ledger in front ALONE.
  `seen_runOf`: the run's return, as it is seen, is `k4Core`. `runS_blind`: so the run is
    `RunBlindC` (Johnson/Desc/First/Batch/Law/BlindRunsK3.lean). `runS_leaves`: and its return's
    field out is the state's.
  **`k4_claimsBlind`**: `ClaimsBlind (blockAtC p)`. **`k4_leaves`**: every run that `blockAtC p`
  states leaves the field out. NO PREMISE.

WHY. K4's runs read K4's own part of the state and the open segment's ledger; the draw writes two
fields of that proof's parameters.

Limits. Nothing on the decision. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED.
Nothing on soundness.
-/
import Johnson.Desc.First.K4.AtC
import Johnson.Desc.First.K4.RunsAtS
import Johnson.Desc.First.Batch.Law.BlindRunsK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Desc.First.K4 (Par part? setPart seatOwn runOf blockAtC claimOf formsFront
  formsFrontNoRows formsBack)
open VerifiableInference.Desc (Claim named)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.K8 (Drawn drawn_ind RunBlind RunBlindC ClaimsBlind runBlind_map)

/-- A run of K4's own term at the verifier's state, written out. -/
def runS (nm : String) (f : Own → Fork → Option (Array Aff × Fork)) (s : S) :
    Except String (List Aff × S) :=
  (named "the part is not there" (part? s)).bind fun q =>
    (runOf seatOwn nm f q).map fun y => (y.1, setPart s y.2)

/-- What a reader sees of the run's return. -/
def k4Core (f : Own → Fork → Option (Array Aff × Fork)) (ow : Option Own) (F : Fork) :
    Option (List Aff × Option Fork) :=
  ow.bind fun o => (f o F).map fun x => (x.1.toList, some x.2)

theorem runOf_eq (nm : String) (f : Own → Fork → Option (Array Aff × Fork))
    (q : OnBytes.Desc.First.K4.Part) :
    runOf seatOwn nm f q =
      (named "K4.what-was-heard-is-not-there" q.1.own).bind fun o =>
        (named nm (f o q.1.F)).bind fun x => .ok (x.1.toList, ({ q.1 with F := x.2 }, q.2)) := rfl

theorem seen_runOf (nm : String) (f : Own → Fork → Option (Array Aff × Fork)) (u : S) (a : LayOwn)
    (r : Option ℕ × Array ℕ) :
    (((runOf seatOwn nm f (a, r)).map fun y => (y.1, setPart u y.2)).toOption.map fun z =>
      (z.1, z.2.fork?)) = k4Core f a.own a.F := by
  rw [runOf_eq]
  unfold k4Core
  cases a.own with
  | none => rfl
  | some o =>
    show ((((named nm (f o a.F)).bind fun x => _).map _).toOption.map _ :
      Option (List Aff × Option Fork)) = (f o a.F).map _
    cases f o a.F <;> rfl

/-- **A run of K4's commutes with the draw's one writing.** -/
theorem runS_blind (nm : String) (f : Own → Fork → Option (Array Aff × Fork)) :
    RunBlindC (runS nm f) := fun s t hd => by
  refine drawn_ind (motive := fun s t =>
    ((runS nm f t).toOption.map fun z => (z.1, z.2.fork?)) =
      (runS nm f s).toOption.map fun z => (z.1, z.2.fork?)) ?_ ?_ ?_ hd
  · intro s a mm ff e
    have e1 : part? s = some (a, if s.noneWaits then none else s.rowsOwed, s.tokv) := by
      unfold part?
      rw [e]
    unfold runS
    rw [e1]
    exact (seen_runOf nm f _ _ _).trans (seen_runOf nm f s a _).symm
  · intro s a mm ff e
    have e1 : part? s = none := by
      unfold part?
      rw [e]
    unfold runS
    rw [e1]
    rfl
  · intro s a mm ff e _
    have e1 : part? s = none := by
      unfold part?
      rw [e]
    unfold runS
    rw [e1]
    rfl

/-- **A run of K4's leaves what goes on to the later chains.** -/
theorem runS_leaves (nm : String) (f : Own → Fork → Option (Array Aff × Fork)) (s : S)
    (z : List Aff × S) (h : runS nm f s = .ok z) : z.2.out = s.out := by
  unfold runS at h
  cases hp : part? s with
  | none =>
    rw [hp] at h
    exact nomatch h
  | some q =>
    rw [hp] at h
    have h' : ((runOf seatOwn nm f q).map fun y => (y.1, setPart s y.2)) = .ok z := h
    cases hr : runOf seatOwn nm f q with
    | error x =>
      rw [hr] at h'
      exact nomatch h'
    | ok y =>
      rw [hr] at h'
      obtain rfl : (y.1, setPart s y.2) = z := Except.ok.inj h'
      rfl

/-- The two runs that K4's sub-protocol states, at the one type of a claim. -/
theorem claims_eq (p : Par) : (blockAtC p).claims =
    [("front", fun _ s => (runS "K4.claims-front"
        ((if p.k3Runs then formsFrontNoRows else formsFront) p.P p.g) s).map fun y =>
          (y.1.map claimOf, y.2)),
     ("back", fun _ s => (runS "K4.claims-back" formsBack s).map fun y =>
        (y.1.map claimOf, y.2))] := rfl

/-- **All runs that K4's sub-protocol states commute with the draw.** -/
theorem k4_claimsBlind (p : Par) : ClaimsBlind (blockAtC p) := by
  intro c hc n
  rw [claims_eq] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact runBlind_map claimOf _ (runS_blind _ _)
  · exact runBlind_map claimOf _ (runS_blind _ _)

/-- **All runs that K4's sub-protocol states leave what goes on to the later chains.** -/
theorem k4_leaves (p : Par) :
    ∀ c ∈ (blockAtC p).claims, ∀ n s z, c.2 n s = .ok z → z.2.out = s.out := by
  intro c hc n s z h
  rw [claims_eq] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  have key : ∀ (nm : String) (f : Own → Fork → Option (Array Aff × Fork)),
      ((runS nm f s).map fun y => (y.1.map claimOf, y.2)) = .ok z → z.2.out = s.out := by
    intro nm f h'
    cases hr : runS nm f s with
    | error x =>
      rw [hr] at h'
      exact nomatch h'
    | ok y =>
      rw [hr] at h'
      obtain rfl : (y.1.map claimOf, y.2) = z := Except.ok.inj h'
      exact runS_leaves nm f s y hr
  rcases hc with rfl | rfl
  · exact key _ _ h
  · exact key _ _ h

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.runS_blind
#print axioms OnBytes.Road.K4.k4_claimsBlind
#print axioms OnBytes.Road.K4.k4_leaves
