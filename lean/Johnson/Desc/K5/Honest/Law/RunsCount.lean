-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/RunsCount.lean: CONDITIONAL: HOW MANY CLAIMS THE RUNS "first" AND
"second" OF AN ATTENTION SEGMENT's OWN ROUNDS MAKE: where both lists of forms are there, their
lengths together are JUST the closed number `attOwnB` (Johnson/Desc/First/Link/K9LensAsk.lean),
which repeats the planner's own count of these claims; and where one of the two is not there, they
are not. On the verifier's own runs; no prover in it. IT IMPORTS FILES OF THE LIBRARY ALONE. Five
definitions, and statements with their proofs.

Why. The test behind the batching's adding asks that the claims of a segment's runs number just the
plan's number. Of these two runs the library has "at most", as a premise
(Johnson/Desc/First/Link/Law/K9LensAskLaw.lean); that, where the verifier's dry run on the plan says
yes, there are two numbers which the lengths are at every input that agrees with the blank one in
what is public (`lens_of_dry`, Johnson/Desc/First/Att/Claims/LenSame.lean), and so at every input
made of a hearing with the place's lengths (`lens_heard`, SameHeard.lean beside it); and that the
lengths are at most those at a blank structure, under two premises on what is fixed
(Johnson/Desc/First/Link/Law/AttLensBlank.lean). None of these names a number.

How. The forms are counted off the runs' text (Johnson/Desc/First/Att/RunsP.lean). `LaysForms n r`
says of a routine r: wherever it returns it has appended just n forms. The lemmas on the ways of
putting routines together, and one lemma for each routine of the text, follow
Johnson/Desc/First/Att/Claims/LenSame.lean lemma for lemma, with a number where that file has a
second routine. The four routines on the division, the value product, the maximum and the index lay
numbers of the place alone. The two on the lookup's units lay sums over the units that the points
hold. These sums are evaluated at a place of the usual four calls, from what the points' maker lays
there (`planes_are`, `points_are`, `points_counts`, `calls_are`, `pieces_size`, `npOf_unit`,
`inAt_parts` of the library). Neither a blank structure nor an evaluation is used.

Main names:
  `LaysForms`, `StepLays`   the two predicates (definitions), and their lemmas `LaysForms.of_eq` to
      `StepLays.after`
  `g_uEnt` to `g_lessPieces`   the readers lay no form
  `formsKR`, `formsUnit`, `formsKFD`   definitions: the sums over the units. In `formsUnit` the 0
      where the unit's plane claim is not in the list is a filler: the run refuses there
  `g_linPlanes` to `g_claim8`   the routines of claims
  `first_count_gen`, `second_count`   **the two runs at every input, from their return alone**
  `counts_place3`   the planner's three counts at the four calls (kin: the library's
      `counts_place`, Johnson/Desc/First/Att/K05Record.lean, which has the first of the three)
  `place_lists`, `formsKR_place`, `formsKFD_place`, `first_count`, `attOwnB_place`   at the four
      calls
  `firstAt_count`, `secondAt_count`, `bothAt_count`   **the runs at what was heard and a ledger**
  `lenBoth_eq`   **the two lengths as the tables of lengths read them off the fixed part**
  `place_of_plan`   the four calls at every return of the planner at the usual call list
  `lenFirst_eq`, `lenSecond_eq`, `lenBoth_eq_iff`   **the equation holds just where both lists of
      forms are there**

Premises of `lenBoth_eq`. Pl: `PlaceIs` (Johnson/Desc/First/Att/Claims/Place.lean): the shape's
calls are the usual four. hc: the runs' parameters have the shape's geometry; at `parCOf A` and
`A.S` it is `rfl`. e1, e2: both lists of forms are there at q.
Who pays them. Pl: `place_of_plan`, by the library's `place_of_hid`
(Johnson/Desc/First/Att/Claims/PlaceOf.lean): a return of the planner at the usual call list, which
a test with code decides (`usualB`, Johnson/Road/Lane5AttLaid.lean). Not called here: from the
planner's return under the kind's one test on the plan (`planOkAll`):
Johnson/Desc/K5/Honest/Law/PublicAtPlan.lean; so under the library's head on the public input: the
field place of `law_at_head` (Johnson/Desc/K5/Honest/Law/PublicAtHead.lean). A part of that test
(`planOkLaw`, Johnson/Desc/First/Att/Claims/PlanLaw.lean) says no at the four small plans of the
tests, where `usualB` says yes. e1, e2, not called here: a return of the run at a state that goes on
from q gives them: the field forms of `still_first` and `still_second`
(Johnson/Desc/First/Att/Claims/K5Still.lean).

Limits. WHERE ONE OF THE TWO LISTS OF FORMS IS NOT THERE THE EQUATION FAILS (`lenBoth_eq_iff`): a
run that refuses has no list, and its number is 0. So at a state of which no more is known than
that it is reached, the equation is not to be had from this file. THE USUAL CALL LIST IS NO TEST OF
THE VERIFIER: it takes other call lists, and groups with two shifts; there `PlaceIs` fails,
`first_count_gen` still holds, and its two sums are evaluated by nobody. The run "keys" states no
claim; the one claim of "join" and the three of "planes" are the lookup's and are not counted here.
`attOwnB` is a second text of the planner's count: this file ties the runs to `attOwnB`, not to the
plan's number of claims. The head of Johnson/Desc/First/Link/Law/AttLensBlank.lean says that no
closed number is known for either length: `second_count` and `first_count` are such numbers.
Tests: Johnson/Desc/K5/Honest/Law/RunsCountToy.lean, at the blank of four small plans. It meets the
premises of `first_count` and `second_count`. THOSE OF `firstAt_count` TO `lenBoth_eq_iff` IT DOES
NOT MEET: see its Limits.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.Claims.PlaceOf
import Johnson.Desc.First.Att.Claims.LenSame
import Johnson.Desc.First.Att.Claims.K5Still
import Johnson.Desc.First.Att.Claims.HeardPlain
import Johnson.Desc.First.Att.K05Record
import Johnson.Desc.First.Att.SeatC
import Johnson.Desc.First.Link.K9LensAsk

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest.Count
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P
    (W1 RemP ScoreP DivP MaxP Pts SumP TablesP ScoreT Geo Ten CallG Keys UnitG
  Heard Left ParC geoOf callOf keysOf tabOf)
open VerifiableInference.Desc.First.Att.P.Runs (W In JoinsP)
open VerifiableInference.Desc.K9L (Pub9)
open VerifiableInference.Desc.StillRun (lenStill)
open VerifiableInference.Desc.K9Asks (attOwnB)
open K5Law (bind_none bind_some PlaceIs inAt firstAt secondAt fsFirst fsSecond)

variable {α β σ : Type}

/-! ### Counting the forms that a routine appends -/

/-- Wherever the routine returns it has appended just n forms. -/
def LaysForms (n : ℕ) (r : W α) : Prop :=
  ∀ (K : ℕ) (acc : Array Aff) (x : α × Array Aff), r K acc = some x → x.2.size = acc.size + n

/-- The same of a loop's step, which also says that the loop goes on. -/
def StepLays (n : ℕ) (r : W (ForInStep PUnit)) : Prop :=
  ∀ (K : ℕ) (acc : Array Aff) (x : ForInStep PUnit × Array Aff), r K acc = some x →
    x.1 = ForInStep.yield PUnit.unit ∧ x.2.size = acc.size + n

/-- The number may be written in another way. -/
theorem LaysForms.of_eq {m n : ℕ} {r : W α} (h : LaysForms m r) (e : m = n) : LaysForms n r := e ▸ h

/-- The number may be written in another way. -/
theorem StepLays.of_eq {m n : ℕ} {r : W (ForInStep PUnit)} (h : StepLays m r) (e : m = n) :
    StepLays n r := e ▸ h

/-- A value by itself lays no form. -/
theorem LaysForms.pure (a : α) : LaysForms 0 (Pure.pure a : W α) := fun _ acc x h => by
  have h' : some (a, acc) = some x := h
  rw [← Option.some.inj h']
  rfl

/-- A refusal returns nowhere, so every number is right of it. -/
theorem LaysForms.fail (n : ℕ) : LaysForms n (failure : W α) := fun _ _ x h => by
  have h' : (none : Option (α × Array Aff)) = some x := h
  cases h'

/-- One routine after another: the numbers add. -/
theorem LaysForms.bind {m n : ℕ} {r : W α} {k : α → W β} (h1 : LaysForms m r)
    (h2 : ∀ a, LaysForms n (k a)) :
    LaysForms (m + n) (r >>= k) := by
  intro K acc x h
  cases hr : r K acc with
  | none => rw [bind_none hr] at h; cases h
  | some y =>
    rw [bind_some hr] at h
    have a1 := h1 K acc y hr
    have a2 := h2 y.1 K y.2 x h
    omega

/-- The same after a routine that lays no form. -/
theorem LaysForms.bind0 {n : ℕ} {r : W α} {k : α → W β} (h1 : LaysForms 0 r)
    (h2 : ∀ a, LaysForms n (k a)) :
    LaysForms n (r >>= k) := (LaysForms.bind h1 h2).of_eq (Nat.zero_add n)

/-- A routine, then a step: the numbers add. -/
theorem StepLays.bind {m n : ℕ} {r : W α} {k : α → W (ForInStep PUnit)} (h1 : LaysForms m r)
    (h2 : ∀ a, StepLays n (k a)) : StepLays (m + n) (r >>= k) := by
  intro K acc x h
  cases hr : r K acc with
  | none => rw [bind_none hr] at h; cases h
  | some y =>
    rw [bind_some hr] at h
    have a1 := h1 K acc y hr
    obtain ⟨a2, a3⟩ := h2 y.1 K y.2 x h
    exact ⟨a2, by omega⟩

/-- The same after a routine that lays no form. -/
theorem StepLays.bind0 {n : ℕ} {r : W α} {k : α → W (ForInStep PUnit)} (h1 : LaysForms 0 r)
    (h2 : ∀ a, StepLays n (k a)) : StepLays n (r >>= k) :=
        (StepLays.bind h1 h2).of_eq (Nat.zero_add n)

/-- The bare step that goes on lays no form. -/
theorem StepLays.yield : StepLays 0
    (Pure.pure (ForInStep.yield PUnit.unit) : W (ForInStep PUnit)) :=
  fun _ acc x h => by
    have h' : some (ForInStep.yield PUnit.unit, acc) = some x := h
    rw [← Option.some.inj h']
    exact ⟨rfl, rfl⟩

/-- One test decides both the number and the routine. -/
theorem LaysForms.iteB {b : Bool} {m : ℕ} {x y : W α} (hx : LaysForms m x) (hy : LaysForms 0 y) :
    LaysForms (if b then m else 0) (if b then x else y) := by
  cases b with
  | false => exact hy
  | true => exact hx

/-- Reading the number of columns lays no form. -/
theorem LaysForms.read : LaysForms 0 (read : W ℕ) := fun K acc x h => by
  have h' : some (K, acc) = some x := h
  rw [← Option.some.inj h']
  rfl

/-- Appending a form lays one. -/
theorem LaysForms.lin (f : Aff) : LaysForms 1 (W.lin f) := fun _ acc x h => by
  have h' : some (PUnit.unit, acc.push f) = some x := h
  rw [← Option.some.inj h']
  exact Array.size_push _

/-- A test lays no form. -/
theorem LaysForms.mustAs (n : String) (b : Bool) : LaysForms 0 (P.Runs.mustAs n b) := by
  unfold P.Runs.mustAs
  split
  · exact LaysForms.pure _
  · exact LaysForms.fail 0

/-- A named refusal is a refusal. -/
theorem LaysForms.refuse (n : ℕ) (s : String) : LaysForms n (P.Runs.refuse s : W α)
    := LaysForms.fail n

/-- Taking a value that must be there lays no form. -/
theorem LaysForms.need (x : Option α) : LaysForms 0 (W.need x) := by
  cases x
  · exact LaysForms.fail 0
  · exact LaysForms.pure _

/-- What follows a value that must be there may lay a number of forms that depends on it. -/
theorem LaysForms.needBind {x : Option α} {k : α → W β} {n : α → ℕ}
    (h : ∀ a, LaysForms (n a) (k a)) :
    LaysForms ((x.map n).getD 0) (W.need x >>= k) := by
  intro K acc y hy
  cases x with
  | none =>
    rw [bind_none (r := W.need (none : Option α)) rfl] at hy
    cases hy
  | some a =>
    rw [bind_some (r := W.need (some a)) (x := (a, acc)) rfl] at hy
    exact h a K acc y hy

/-- A fold whose steps lay no form lays none. -/
theorem LaysForms.foldlM0 {f : σ → α → W σ} (hf : ∀ s a, LaysForms 0 (f s a)) :
    ∀ (xs : List α) (s : σ), LaysForms 0 (xs.foldlM f s)
  | [], s => by
    simp only [List.foldlM_nil]
    exact LaysForms.pure s
  | a :: xs, s => by
    simp only [List.foldlM_cons]
    exact LaysForms.bind0 (hf s a) fun s' => LaysForms.foldlM0 hf xs s'

/-- A fold: the steps' numbers add up. -/
theorem LaysForms.foldlM {f : σ → α → W σ} {w : α → ℕ} (hf : ∀ s a, LaysForms (w a) (f s a)) :
    ∀ (xs : List α) (s : σ), LaysForms (xs.map w).sum (xs.foldlM f s)
  | [], s => by
    simp only [List.foldlM_nil, List.map_nil, List.sum_nil]
    exact LaysForms.pure s
  | a :: xs, s => by
    simp only [List.foldlM_cons, List.map_cons, List.sum_cons]
    exact LaysForms.bind (hf s a) fun s' => LaysForms.foldlM hf xs s'

/-- A loop over a list, with one number for each member. -/
theorem LaysForms.forM {f : α → W PUnit} {n : ℕ} (hf : ∀ a, LaysForms n (f a)) :
    ∀ xs : List α, LaysForms (xs.length * n) (xs.forM f)
  | [] => (LaysForms.pure PUnit.unit).of_eq (by simp)
  | a :: xs => (LaysForms.bind (hf a) fun _ => LaysForms.forM hf xs).of_eq (by
      rw [List.length_cons, Nat.succ_mul]; omega)

/-- The same of a `for` loop whose steps all go on. -/
theorem LaysForms.forIn {f : α → PUnit → W (ForInStep PUnit)} {n : ℕ}
    (hf : ∀ a, StepLays n (f a PUnit.unit)) :
    ∀ xs : List α, LaysForms (xs.length * n) (forIn xs PUnit.unit f)
  | [] => by
    rw [List.forIn_nil]
    exact (LaysForms.pure PUnit.unit).of_eq (by simp)
  | x :: xs => by
    rw [List.forIn_cons]
    intro K acc y h
    cases hr : f x PUnit.unit K acc with
    | none => rw [bind_none hr] at h; cases h
    | some z =>
      rw [bind_some hr] at h
      obtain ⟨e, s⟩ := hf x K acc z hr
      rw [e] at h
      have t := LaysForms.forIn hf xs K z.2 y h
      rw [List.length_cons, Nat.succ_mul]
      omega

/-- A step that ends in one form. -/
theorem StepLays.linYield (f : Aff) :
    StepLays 1 (W.lin f >>= fun _ => (Pure.pure (ForInStep.yield PUnit.unit) : W _)) :=
  StepLays.bind (LaysForms.lin f) fun _ => StepLays.yield

/-- A step that is a routine and nothing more. -/
theorem StepLays.after {n : ℕ} {r : W α} (h : LaysForms n r) :
    StepLays n (r >>= fun _ => (Pure.pure (ForInStep.yield PUnit.unit) : W _)) :=
  StepLays.bind h fun _ => StepLays.yield

/-! ### The readers lay no form -/

theorem g_uEnt (t x : ℕ) : LaysForms 0 (P.Runs.uEnt t x) := by
  unfold P.Runs.uEnt
  exact LaysForms.bind0 LaysForms.read fun _ => LaysForms.bind0 (LaysForms.mustAs _ _) fun _
      => LaysForms.pure _

variable (i : In)

/-- `u3at` lays no form. -/
theorem g_u3at (t n : ℕ) : LaysForms 0 (P.Runs.u3at i t n) := by
  unfold P.Runs.u3at
  exact LaysForms.bind0 (LaysForms.mustAs _ _) fun _ => g_uEnt _ _

/-- `weighted` lays no form. -/
theorem g_weighted (n : ℕ) (w : Array E) (f : ℕ → W Aff) (hf : ∀ k, LaysForms 0 (f k)) :
    LaysForms 0 (P.Runs.weighted n w f) := by
  unfold P.Runs.weighted
  exact LaysForms.foldlM0 (fun _ k => LaysForms.bind0 (hf k) fun _ => LaysForms.pure _) _ _

/-- `plane` lays no form. -/
theorem g_plane (t x lam a : ℕ) (z : Array E) (isD : Bool) : LaysForms 0
    (P.Runs.plane i t x lam a z isD) := by
  unfold P.Runs.plane
  dsimp only
  exact g_weighted _ _ _ fun _ => g_u3at i _ _

/-- `shV` lays no form. -/
theorem g_shV (t off nl J lam j : ℕ) : LaysForms 0 (P.Runs.shV i t off nl J lam j) := by
  unfold P.Runs.shV
  exact g_weighted _ _ _ fun _ => g_u3at i _ _

/-- `overG` lays no form. -/
theorem g_overG (zg : Array E) (f : ℕ → W Aff) (hf : ∀ k, LaysForms 0 (f k)) :
    LaysForms 0 (P.Runs.overG i zg f) := by
  unfold P.Runs.overG
  exact g_weighted _ _ _ hf

/-- `readDenominator` lays no form. -/
theorem g_readDenominator (t : ℕ) (zg : Array E) (lam a : ℕ) :
    LaysForms 0 (P.Runs.readDenominator i t zg lam a) := by
  unfold P.Runs.readDenominator
  exact g_overG i _ _ fun _ => g_shV i _ _ _ _ _ _

/-- `readMaximum` lays no form. -/
theorem g_readMaximum (t : ℕ) (zg : Array E) (lam a : ℕ) : LaysForms 0
    (P.Runs.readMaximum i t zg lam a) := by
  unfold P.Runs.readMaximum
  exact g_overG i _ _ fun _ => g_shV i _ _ _ _ _ _

/-- `readIndexBit` lays no form. -/
theorem g_readIndexBit (t : ℕ) (zg : Array E) (lam a k : ℕ) :
    LaysForms 0 (P.Runs.readIndexBit i t zg lam a k) := by
  unfold P.Runs.readIndexBit
  exact g_overG i _ _ fun _ => g_shV i _ _ _ _ _ _

/-- `xl` lays no form. -/
theorem g_xl (t : ℕ) (X : Ten) (lam hd : ℕ) (zc : Array E) : LaysForms 0
    (P.Runs.xl i t X lam hd zc) := by
  unfold P.Runs.xl
  dsimp only
  cases P.cutLast (zc.extract 0 i.g.ldh) i.g.ls with
  | none => exact LaysForms.refuse 0 _
  | some cut =>
    dsimp only
    cases P.headFeat X hd i.g.dh with
    | none => exact LaysForms.refuse 0 _
    | some j0 =>
      dsimp only
      exact g_weighted _ _ _ fun _ => g_weighted _ _ _ fun _ => g_u3at i _ _

/-- `readHead` lays no form. -/
theorem g_readHead (t : ℕ) (X : Ten) (zg zc : Array E) (lam a : ℕ) :
    LaysForms 0 (P.Runs.readHead i t X zg zc lam a) := by
  unfold P.Runs.readHead
  exact g_overG i _ _ fun _ => g_xl i _ _ _ _ _

/-- `readGroup` lays no form. -/
theorem g_readGroup (t : ℕ) (X : Ten) (zg zc : Array E) (lam : ℕ) :
    LaysForms 0 (P.Runs.readGroup i t X zg zc lam) := by
  unfold P.Runs.readGroup
  exact g_overG i _ _ fun _ => g_xl i _ _ _ _ _

/-- `lessPieces` lays no form. -/
theorem g_lessPieces (s : Aff) (pw : Array W1) (f : W1 → W Aff) (hf : ∀ w, LaysForms 0 (f w)) :
    LaysForms 0 (P.Runs.lessPieces s pw f) := by
  unfold P.Runs.lessPieces
  rw [← Array.foldlM_toList]
  exact LaysForms.foldlM0 (fun _ w => LaysForms.bind0 (hf w) fun _ => LaysForms.pure _) _ _

/-! ### The six routines of claims -/

theorem g_linPlanes (pc : RemP) : LaysForms pc.np (P.Runs.linPlanes i pc) := by
  unfold P.Runs.linPlanes
  exact (LaysForms.forM (n := 1) (fun x => LaysForms.bind0
    (g_lessPieces _ _ _ fun w => g_plane i _ _ _ _ _ _) fun _ => LaysForms.lin _) _).of_eq (by
      rw [List.length_range, Nat.mul_one])

/-- A remainder-table call: the plane values of its units. -/
theorem g_callKR (q : ℕ) :
    LaysForms (i.p.planes.toList.map fun pc => if pc.call == q then pc.np else 0).sum
        (P.Runs.callKR i q) := by
  unfold P.Runs.callKR
  rw [← Array.foldlM_toList]
  exact LaysForms.foldlM (fun _ pc => LaysForms.iteB
    ((LaysForms.bind (g_linPlanes i pc) fun _ => LaysForms.pure _).of_eq (Nat.add_zero _))
        (LaysForms.pure _)) _ _

/-- The forms of the routine on the remainder-table units: each such call's units' plane values. -/
def formsKR : ℕ := (i.g.calls.toList.zipIdx.map fun x => if x.1.tab == .kr then
  (i.p.planes.toList.map fun pc => if pc.call == x.2 then pc.np else 0).sum else 0).sum

/-- The routine on the remainder-table units. -/
theorem g_claim3 (j : JoinsP) : LaysForms (formsKR i) (P.Runs.claim3 i j) := by
  unfold P.Runs.claim3 formsKR
  exact LaysForms.foldlM (fun _ (x : CallG × ℕ) => LaysForms.iteB
    ((LaysForms.bind (g_callKR i x.2) fun _ => LaysForms.pure _).of_eq (Nat.add_zero _))
        (LaysForms.pure _)) _ _

/-- Two forms for a piece's two end values. -/
theorem g_endValues (k : ScoreP) (tb : ScoreT) (rc : Array E) (b : ℕ) (w : W1) :
    LaysForms 2 (P.Runs.endValues i k tb rc b w) := by
  unfold P.Runs.endValues
  exact LaysForms.bind0 (g_readHead i _ _ _ _ _ _) fun _ => LaysForms.bind
      (LaysForms.lin _) fun _ =>
    LaysForms.bind0 (g_readGroup i _ _ _ _ _) fun _ => LaysForms.lin _

/-- The forms of one softmax-table unit: its plane values, the maximum, the sumcheck's row, two to a
piece. The 0 where the unit's plane claim is not in the list is a filler: the run refuses there. -/
def formsUnit (k : ScoreP) : ℕ :=
  ((i.p.planes[k.claim]?).map fun pc => pc.np + (2 + k.pw.size * 2)).getD 0

/-- One softmax-table unit. -/
theorem g_unitKFD (n : ℕ) (k : ScoreP) : LaysForms (formsUnit i k) (P.Runs.unitKFD i n k) := by
  unfold P.Runs.unitKFD formsUnit
  dsimp only
  refine LaysForms.bind0 (LaysForms.need _) fun tb => LaysForms.needBind fun pc => ?_
  refine LaysForms.bind (g_linPlanes i pc) fun _ => ?_
  refine LaysForms.bind0 (g_lessPieces _ _ _ fun w => g_readMaximum i _ _ _ _) fun _ => ?_
  refine (LaysForms.bind (LaysForms.lin _) fun _ => LaysForms.bind (LaysForms.lin _) fun _ =>
    LaysForms.forM (n := 2) (fun x => g_endValues i _ _ _ _ _) _).of_eq ?_
  rw [List.length_zipIdx, Array.length_toList]
  omega

/-- A softmax-table call: its units. -/
theorem g_callKFD (q : ℕ) (c : CallG) :
    LaysForms (i.p.scores.toList.zipIdx.map fun y => if y.1.call == q then formsUnit
        i y.1 else 0).sum
      (P.Runs.callKFD i q c) := by
  unfold P.Runs.callKFD
  exact LaysForms.foldlM (fun _ (y : ScoreP × ℕ) => LaysForms.iteB
    ((LaysForms.bind (g_unitKFD i y.2 y.1) fun _ => LaysForms.pure _).of_eq (Nat.add_zero _))
        (LaysForms.pure _)) _ _

/-- The forms of the routine on the softmax-table units. -/
def formsKFD : ℕ := (i.g.calls.toList.zipIdx.map fun x => if x.1.tab == .kfd then
  (i.p.scores.toList.zipIdx.map fun y => if y.1.call == x.2 then formsUnit i y.1 else
      0).sum else 0).sum

/-- The routine on the softmax-table units. -/
theorem g_claim4 (j : JoinsP) : LaysForms (formsKFD i) (P.Runs.claim4 i j) := by
  unfold P.Runs.claim4 formsKFD
  exact LaysForms.foldlM (fun _ (x : CallG × ℕ) => LaysForms.iteB
    ((LaysForms.bind (g_callKFD i x.2 x.1) fun _ => LaysForms.pure _).of_eq (Nat.add_zero _))
        (LaysForms.pure _)) _ _

/-- Two forms for a pair's two end values in the division's sumcheck. -/
theorem g_endValuesE (b : ℕ) (w : W1) : LaysForms 2 (P.Runs.endValuesE i b w) := by
  unfold P.Runs.endValuesE
  dsimp only
  exact LaysForms.bind0 (g_readDenominator i _ _ _ _) fun _ => LaysForms.bind
      (LaysForms.lin _) fun _ =>
    LaysForms.bind0 (g_readHead i _ _ _ _ _ _) fun _ => LaysForms.lin _

/-- The routine on the division. -/
theorem g_claim5 (j : JoinsP) : LaysForms (6 + i.g.lt + 2 * i.g.NP) (P.Runs.claim5 i j) := by
  unfold P.Runs.claim5
  dsimp only
  refine LaysForms.bind0 (g_lessPieces _ _ _ fun w => g_readDenominator i _ _ _ _) fun _ => ?_
  refine LaysForms.bind0 (g_lessPieces _ _ _ fun w => g_readHead i _ _ _ _ _ _) fun _ => ?_
  refine LaysForms.bind0 (g_lessPieces _ _ _ fun w => g_readHead i _ _ _ _ _ _) fun _ => ?_
  refine LaysForms.bind0 (g_lessPieces _ _ _ fun w => g_readHead i _ _ _ _ _ _) fun _ => ?_
  refine LaysForms.bind0 (g_lessPieces _ _ _ fun w => g_readHead i _ _ _ _ _ _) fun _ => ?_
  refine (LaysForms.bind (LaysForms.lin _) fun _ => LaysForms.bind (LaysForms.lin _) fun _ =>
    LaysForms.bind (LaysForms.lin _) fun _ =>
    LaysForms.bind (LaysForms.forIn (n := 1) (fun k => StepLays.bind0
      (g_lessPieces _ _ _ fun w => g_readIndexBit i _ _ _ _ _) fun _ =>
          StepLays.linYield _) _) fun _ =>
    LaysForms.bind (LaysForms.lin _) fun _ => LaysForms.bind (LaysForms.lin _) fun _ =>
    LaysForms.bind (LaysForms.lin _) fun _ =>
    LaysForms.bind (LaysForms.forIn (n := 2)
        (fun b => StepLays.after (g_endValuesE i b _)) _) fun _ =>
    LaysForms.pure _).of_eq ?_
  rw [List.length_range, List.length_range]
  omega

/-- One value product: its sumcheck's row, and two forms to a pair. -/
theorem g_valueProduct (sc : SumP) (tS : ℕ) (pt : Array E) (isD : Bool) (tV : ℕ) :
    LaysForms (1 + 2 * i.g.NP) (P.Runs.valueProduct i sc tS pt isD tV) := by
  unfold P.Runs.valueProduct
  refine (LaysForms.bind (LaysForms.lin _) fun _ => LaysForms.bind
      (LaysForms.forIn (n := 2) (fun b => ?_) _)
    fun _ => LaysForms.pure _).of_eq ?_
  · dsimp only
    exact StepLays.bind0 (g_plane i _ _ _ _ _ _) fun _ => StepLays.bind0
        (g_plane i _ _ _ _ _ _) fun _ =>
      StepLays.bind (LaysForms.lin _) fun _ => StepLays.bind0 (g_readGroup i _ _ _ _ _) fun _ =>
          StepLays.linYield _
  · rw [List.length_range]
    omega

/-- The routine on the value product. -/
theorem g_claim6 : LaysForms (3 + 4 * i.g.NP) (P.Runs.claim6 i) := by
  unfold P.Runs.claim6
  dsimp only
  exact (LaysForms.bind (LaysForms.lin _) fun _ => LaysForms.bind
      (g_valueProduct i _ _ _ _ _) fun _ =>
    g_valueProduct i _ _ _ _ _).of_eq (by omega)

/-- The routine on the maximum. -/
theorem g_claim7 : LaysForms (2 + 2 * i.g.NP + i.g.Lam + i.g.NP * i.g.lt) (P.Runs.claim7 i) := by
  unfold P.Runs.claim7
  dsimp only
  refine (LaysForms.bind (LaysForms.forIn (n := 1) (fun b =>
      StepLays.bind0 (g_readMaximum i _ _ _ _) fun _ => StepLays.linYield _) _) fun _ =>
    LaysForms.bind (LaysForms.lin _) fun _ =>
    LaysForms.bind (LaysForms.forIn (n := 1) (fun b =>
      StepLays.bind0 (g_readHead i _ _ _ _ _ _) fun _ => StepLays.linYield _) _) fun _ =>
    LaysForms.bind (LaysForms.lin _) fun _ =>
    LaysForms.bind (LaysForms.forIn (n := 1) (fun lam =>
      StepLays.bind0 (g_readGroup i _ _ _ _ _) fun _ => StepLays.linYield _) _) fun _ =>
    LaysForms.bind (LaysForms.forIn (n := i.g.lt) (fun b => ?_) _) fun _ =>
        LaysForms.pure _).of_eq ?_
  · refine (StepLays.bind (LaysForms.forIn (n := 1) (fun k =>
      StepLays.bind0 (g_readIndexBit i _ _ _ _ _) fun _ => StepLays.linYield _) _) fun _ =>
      StepLays.bind0 (LaysForms.pure _) fun _ => StepLays.yield).of_eq ?_
    rw [List.length_range]
    omega
  · rw [List.length_range, List.length_range]
    omega

/-- The routine on the index's cells. -/
theorem g_claim8 : LaysForms (1 + 2 * i.g.NP) (P.Runs.claim8 i) := by
  unfold P.Runs.claim8
  dsimp only
  refine (LaysForms.bind (LaysForms.lin _) fun _ => LaysForms.bind
      (LaysForms.forIn (n := 2) (fun b => ?_) _)
    fun _ => LaysForms.pure _).of_eq ?_
  · exact StepLays.bind (LaysForms.lin _) fun _ => StepLays.bind0
      (LaysForms.foldlM0 (fun _ k => LaysForms.bind0 (g_readIndexBit i _ _ _ _ _) fun _ =>
          LaysForms.pure _) _ _)
      fun _ => StepLays.linYield _
  · rw [List.length_range]
    omega

/-! ### The two runs, at every input -/

variable {i}

/-- A routine that is run from no form returns a list of just its number of forms. -/
theorem gather_count {n : ℕ} {r : W α} (h : LaysForms n r) {K : ℕ} {x : α × List Aff}
    (h1 : P.Runs.gather K r = some x) : x.2.length = n := by
  unfold P.Runs.gather at h1
  have e : (r.run K).run #[] = r K #[] := rfl
  rw [e] at h1
  cases a1 : r K #[] with
  | none => rw [a1] at h1; cases h1
  | some y =>
    rw [a1] at h1
    rw [← Option.some.inj h1]
    show y.2.toList.length = n
    rw [Array.length_toList, h K #[] y a1]
    exact Nat.zero_add n

/-- **The run "first", wherever it returns.** -/
theorem first_count_gen {K : ℕ} {l : List Aff} {j : JoinsP}
    (h : P.Runs.firstRun i K = some (l, j)) :
    l.length = formsKR i + formsKFD i + (6 + i.g.lt + 2 * i.g.NP) := by
  unfold P.Runs.firstRun at h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
  obtain ⟨x, g1, rfl, -⟩ := h
  exact gather_count ((LaysForms.bind (g_claim3 i _) fun _ => LaysForms.bind (g_claim4 i _) fun _ =>
    g_claim5 i _).of_eq (by omega)) g1

/-- **The run "second", wherever it returns.** -/
theorem second_count {K : ℕ} {l : List Aff} (h : P.Runs.secondRun i K = some l) :
    l.length = (3 + 4 * i.g.NP) + (2 + 2 * i.g.NP + i.g.Lam + i.g.NP * i.g.lt) +
        (1 + 2 * i.g.NP) := by
  unfold P.Runs.secondRun at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨x, g1, rfl⟩ := h
  exact gather_count ((LaysForms.bind (g_claim6 i) fun _ => LaysForms.bind (g_claim7 i) fun _ =>
    g_claim8 i).of_eq (by omega)) g1

/-! ### At a place of the four calls -/

variable {S : Attention.Shape} {c0 c1 c2 c3 : Attention.ACall}

/-- The planner's three counts over the place's four calls. -/
theorem counts_place3 (Pl : PlaceIs S c0 c1 c2 c3) :
    (Attention.Counts.of S).nKRp = 2 ∧ (Attention.Counts.of S).nKFp = 2 ∧
      (Attention.Counts.of S).sumNp = c1.npOf .fm + c1.npOf .fd := by
  unfold Attention.Counts.of
  rw [← Array.foldl_toList, Pl.calls]
  simp [Attention.Counts.call, Attention.Counts.plane, Attention.Counts.scores,
    Attention.ACall.holds, Pl.k0, Pl.k1, Pl.k2, Pl.k3, Pl.g0, Pl.g1]

/-- What the points hold at such a place, as far as the count reads it: four plane claims, two
units. -/
theorem place_lists (Pl : PlaceIs S c0 c1 c2 c3) (hg : i.g = geoOf S)
    {zk : Array (Array E)} {hh : Heard}
    {L : Left} (hP : P.pointsOf i.g zk hh L = some i.p) :
    ∃ (a1 a2 : ℕ) (k1 k2 : ScoreP),
      i.p.planes.toList = [K5Law.remAt i.g zk (0, callOf c0, .rm) a1, K5Law.remAt i.g zk
          (0, callOf c0, .rd) a2,
        K5Law.remOfUnit zk (i.g.unitAt 1 (callOf c1) .fm) k1.s0,
        K5Law.remOfUnit zk (i.g.unitAt 1 (callOf c1) .fd) k2.s0] ∧
      i.p.scores.toList = [k1, k2] ∧ k1.call = 1 ∧ k2.call = 1 ∧ k1.claim = 2 ∧ k2.claim = 3 ∧
      k1.pw.size = c1.npOf .fm ∧ k2.pw.size = c1.npOf .fd := by
  have PA := K5Law.points_are hP
  have Pn := K5Law.planes_are hP
  obtain ⟨-, nP, nS⟩ := K5Law.points_counts hP
  have hkr : i.g.units .kr [.rm, .rd] = [(0, callOf c0, .rm), (0, callOf c0, .rd)] := by
    rw [hg]; exact K5Law.place_kr Pl
  have hgs : i.g.scores = [i.g.unitAt 1 (callOf c1) .fm, i.g.unitAt 1 (callOf c1) .fd] := by
    rw [hg]; exact K5Law.place_scores Pl
  have nR : hh.remainders.size = 2 := by rw [← Pn.nR, hkr]; rfl
  have nH : hh.scores.size = 2 := by rw [← PA.nH, hgs]; rfl
  have ea1 : hh.remainders[0]? = some hh.remainders[0] := Array.getElem?_eq_getElem (by omega)
  have ea2 : hh.remainders[1]? = some hh.remainders[1] := Array.getElem?_eq_getElem (by omega)
  have eo1 : hh.scores[0]? = some hh.scores[0] := Array.getElem?_eq_getElem (by omega)
  have eo2 : hh.scores[1]? = some hh.scores[1] := Array.getElem?_eq_getElem (by omega)
  have p1 := Pn.rem 0 _ _ (by rw [hkr]; rfl) ea1
  have p2 := Pn.rem 1 _ _ (by rw [hkr]; rfl) ea2
  obtain ⟨k1, s1, q1, d1, z1, -, w1, -⟩ := Pn.unit 0 _ _ (by rw [hgs]; rfl) eo1
  obtain ⟨k2, s2, q2, d2, z2, -, w2, -⟩ := Pn.unit 1 _ _ (by rw [hgs]; rfl) eo2
  rw [← z1, q1, nR] at d1
  rw [← z2, q2, nR] at d2
  have lp : i.p.planes.toList = [K5Law.remAt i.g zk (0, callOf c0, .rm) hh.remainders[0],
      K5Law.remAt i.g zk (0, callOf c0, .rd) hh.remainders[1],
      K5Law.remOfUnit zk (i.g.unitAt 1 (callOf c1) .fm) k1.s0,
      K5Law.remOfUnit zk (i.g.unitAt 1 (callOf c1) .fd) k2.s0] :=
    K5Law.list_four (by rw [Array.length_toList, nP, nR, nH])
        (by rw [Array.getElem?_toList]; exact p1)
      (by rw [Array.getElem?_toList]; exact p2) (by rw [Array.getElem?_toList]; exact d1)
      (by rw [Array.getElem?_toList]; exact d2)
  have ls : i.p.scores.toList = [k1, k2] :=
    K5Law.list_two (by rw [Array.length_toList, nS, nH]) (by rw [Array.getElem?_toList]; exact s1)
      (by rw [Array.getElem?_toList]; exact s2)
  have cc := K5Law.calls_are PA
  rw [ls, hgs] at cc
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at cc
  refine ⟨_, _, k1, k2, lp, ls, cc.1, cc.2, by rw [q1, nR], by rw [q2, nR], ?_, ?_⟩
  · rw [w1, P.pieces_size, P.npOf_unit i.g 1 c1 .fm]
    rfl
  · rw [w2, P.pieces_size, P.npOf_unit i.g 1 c1 .fd]
    rfl

/-- The first call's kind of table. -/
theorem place_tab0 (Pl : PlaceIs S c0 c1 c2 c3) : (callOf c0).tab = .kr := by
  show tabOf c0.kind = _
  rw [Pl.k0]; rfl
/-- The second call's kind of table. -/
theorem place_tab1 (Pl : PlaceIs S c0 c1 c2 c3) : (callOf c1).tab = .kfd := by
  show tabOf c1.kind = _
  rw [Pl.k1]; rfl
/-- The third call's kind of table. -/
theorem place_tab2 (Pl : PlaceIs S c0 c1 c2 c3) : (callOf c2).tab = .r16 := by
  show tabOf c2.kind = _
  rw [Pl.k2]; rfl
/-- The fourth call's kind of table. -/
theorem place_tab3 (Pl : PlaceIs S c0 c1 c2 c3) : (callOf c3).tab = .wh := by
  show tabOf c3.kind = _
  rw [Pl.k3]; rfl

/-- The remainder-table units lay six forms. -/
theorem formsKR_place (Pl : PlaceIs S c0 c1 c2 c3) (hg : i.g = geoOf S)
    {zk : Array (Array E)} {hh : Heard}
    {L : Left} (hP : P.pointsOf i.g zk hh L = some i.p) : formsKR i = 6 := by
  obtain ⟨a1, a2, k1, k2, lp, -⟩ := place_lists Pl hg hP
  have hz : i.g.calls.toList.zipIdx =
      [(callOf c0, 0), (callOf c1, 1), (callOf c2, 2), (callOf c3, 3)] := by
    rw [hg]; exact K5Law.place_zip Pl
  unfold formsKR
  rw [lp, hz]
  simp [place_tab0 Pl, place_tab1 Pl, place_tab2 Pl, place_tab3 Pl, K5Law.remAt,
      K5Law.remOfUnit, P.Geo.unitAt]

/-- The softmax-table units lay seven forms each, and two to a piece. -/
theorem formsKFD_place (Pl : PlaceIs S c0 c1 c2 c3) (hg : i.g = geoOf S)
    {zk : Array (Array E)} {hh : Heard}
    {L : Left} (hP : P.pointsOf i.g zk hh L = some i.p) :
    formsKFD i = (5 + (2 + c1.npOf .fm * 2)) + (5 + (2 + c1.npOf .fd * 2)) := by
  obtain ⟨a1, a2, k1, k2, lp, ls, hc1, hc2, hq1, hq2, hw1, hw2⟩ := place_lists Pl hg hP
  have hz : i.g.calls.toList.zipIdx =
      [(callOf c0, 0), (callOf c1, 1), (callOf c2, 2), (callOf c3, 3)] := by
    rw [hg]; exact K5Law.place_zip Pl
  have u1 : formsUnit i k1 = 5 + (2 + c1.npOf .fm * 2) := by
    unfold formsUnit
    rw [hq1, ← Array.getElem?_toList, lp, hw1]
    rfl
  have u2 : formsUnit i k2 = 5 + (2 + c1.npOf .fd * 2) := by
    unfold formsUnit
    rw [hq2, ← Array.getElem?_toList, lp, hw2]
    rfl
  have hy : [k1, k2].zipIdx = [(k1, 0), (k2, 1)] := rfl
  unfold formsKFD
  rw [ls, hz, hy]
  simp [place_tab0 Pl, place_tab1 Pl, place_tab2 Pl, place_tab3 Pl, hc1, hc2, u1, u2]

/-- **The run "first" at such a place.** -/
theorem first_count (Pl : PlaceIs S c0 c1 c2 c3) (hg : i.g = geoOf S)
    {zk : Array (Array E)} {hh : Heard}
    {L : Left} (hP : P.pointsOf i.g zk hh L = some i.p) {K : ℕ} {l : List Aff} {j : JoinsP}
    (h : P.Runs.firstRun i K = some (l, j)) :
    l.length = 6 + ((5 + (2 + c1.npOf .fm * 2)) + (5 + (2 + c1.npOf .fd * 2))) +
        (6 + S.cf.lt + 2 * S.NP) := by
  rw [first_count_gen h, formsKR_place Pl hg hP, formsKFD_place Pl hg hP, hg]
  rfl

/-- The closed number at such a place. -/
theorem attOwnB_place (Pl : PlaceIs S c0 c1 c2 c3) :
    attOwnB S = 3 * 2 + (6 * 2 + 2 * (c1.npOf .fm + c1.npOf .fd)) + (5 + S.cf.lt + 2 * S.NP)
        + (1 + 4 * S.NP) +
      (4 * S.NP + S.Lam + S.NP * S.cf.lt) + (2 + 5 + 1) := by
  obtain ⟨k1, k2, k3⟩ := counts_place3 Pl
  unfold attOwnB
  dsimp only
  rw [k1, k2, k3]

/-- **The run "first" at what was heard and a ledger.** -/
theorem firstAt_count (Pl : PlaceIs S c0 c1 c2 c3) {c : ParC} (hc : c.geo = geoOf S)
    {g : Forest.Heard}
    {h : Heard} {U : Fork} {l : List Aff} (e : firstAt c g h U = some l) :
    l.length = 6 + ((5 + (2 + c1.npOf .fm * 2)) + (5 + (2 + c1.npOf .fd * 2))) +
        (6 + S.cf.lt + 2 * S.NP) := by
  unfold firstAt at e
  obtain ⟨x, hx, r⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 r
  obtain ⟨eg, -, -, ⟨Lf, -, hq⟩, -⟩ := K5Law.inAt_parts hx
  exact first_count Pl (eg.trans hc) (by rw [eg]; exact hq) (l := y.1) (j := y.2) hy

/-- **The run "second" at what was heard and a ledger.** -/
theorem secondAt_count {c : ParC} (hc : c.geo = geoOf S) {g : Forest.Heard} {h : Heard} {U : Fork}
    {l : List Aff} (e : secondAt c g h U = some l) :
    l.length = (3 + 4 * S.NP) + (2 + 2 * S.NP + S.Lam + S.NP * S.cf.lt) + (1 + 2 * S.NP) := by
  unfold secondAt at e
  obtain ⟨x, hx, r⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨eg, -⟩ := K5Law.inAt_parts hx
  rw [second_count r, eg, hc]
  rfl

/-- **The two runs together, at what was heard and a ledger**: where both return, their forms number
just the closed number. -/
theorem bothAt_count (Pl : PlaceIs S c0 c1 c2 c3) {c : ParC} (hc : c.geo = geoOf S)
    {g : Forest.Heard} {h : Heard}
    {U : Fork} {l₁ l₂ : List Aff} (e1 : firstAt c g h U = some l₁)
        (e2 : secondAt c g h U = some l₂) :
    l₁.length + l₂.length = attOwnB S := by
  rw [firstAt_count Pl hc e1, secondAt_count hc e2, attOwnB_place Pl]
  omega

/-- **THE TWO LENGTHS AS THE TABLES OF LENGTHS READ THEM OFF THE FIXED PART**: where both lists of
forms are there, the two numbers together are just the closed number. -/
theorem lenBoth_eq (Pl : PlaceIs S c0 c1 c2 c3) {c : ParC} (hc : c.geo = geoOf S)
    (rd : α → Option (Forest.Heard × Heard)) (q : α × Option Pub9) {l₁ l₂ : List Aff}
    (e1 : fsFirst rd c q = some l₁) (e2 : fsSecond rd c q = some l₂) :
    lenStill (fsFirst rd c) q + lenStill (fsSecond rd c) q = attOwnB S := by
  have a1 : lenStill (fsFirst rd c) q = l₁.length := by unfold lenStill; rw [e1]; rfl
  have a2 : lenStill (fsSecond rd c) q = l₂.length := by unfold lenStill; rw [e2]; rfl
  unfold fsFirst at e1
  unfold fsSecond at e2
  obtain ⟨gh, hg, e1⟩ := Option.bind_eq_some_iff.1 e1
  obtain ⟨v, hv, e1⟩ := Option.bind_eq_some_iff.1 e1
  obtain ⟨gh', hg', e2⟩ := Option.bind_eq_some_iff.1 e2
  obtain ⟨v', hv', e2⟩ := Option.bind_eq_some_iff.1 e2
  obtain rfl : gh = gh' := Option.some.inj (hg.symm.trans hg')
  obtain rfl : v = v' := Option.some.inj (hv.symm.trans hv')
  rw [a1, a2]
  exact bothAt_count Pl hc e1 e2

/-- **The four calls at every return of the planner at the usual call list**, which a test with code
decides. -/
theorem place_of_plan {settings : Model.Settings} {inp : Attention.In} {cf : Attention.Cfg}
    {A : Attention.Plan} (h : Attention.plan settings inp cf = Except.ok A)
    (hu : OnBytes.Road.L5.usualB cf = true) :
    PlaceIs A.S (OnBytes.Road.L5.callAt A.S 0) (OnBytes.Road.L5.callAt A.S 1)
      (OnBytes.Road.L5.callAt A.S 2) (OnBytes.Road.L5.callAt A.S 3) :=
  K5Law.place_of_hid (OnBytes.Road.L5.plan_shape h).1 (OnBytes.Road.L5.usual_of_test hu)

/-! ### The premises that the forms are there carry weight -/

/-- Where a list of forms is not there its length is 0. -/
theorem len_none {fs : α × Option Pub9 → Option (List Aff)} {q : α × Option Pub9}
    (e : fs q = none) :
    lenStill fs q = 0 := by
  unfold lenStill
  rw [e]
  rfl

/-- Where a list of forms is there its length is the list's. -/
theorem len_some {fs : α × Option Pub9 → Option (List Aff)} {q : α × Option Pub9} {l : List Aff}
    (e : fs q = some l) : lenStill fs q = l.length := by
  unfold lenStill
  rw [e]
  rfl

/-- The length of "first" as the tables of lengths read it off the fixed part. -/
theorem lenFirst_eq (Pl : PlaceIs S c0 c1 c2 c3) {c : ParC} (hc : c.geo = geoOf S)
    (rd : α → Option (Forest.Heard × Heard)) (q : α × Option Pub9) {l : List Aff}
    (e : fsFirst rd c q = some l) :
    lenStill (fsFirst rd c) q =
      6 + ((5 + (2 + c1.npOf .fm * 2)) + (5 + (2 + c1.npOf .fd * 2))) +
          (6 + S.cf.lt + 2 * S.NP) := by
  rw [len_some e]
  unfold fsFirst at e
  obtain ⟨gh, -, e⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨v, -, e⟩ := Option.bind_eq_some_iff.1 e
  exact firstAt_count Pl hc e

/-- The length of "second" as the tables of lengths read it off the fixed part. -/
theorem lenSecond_eq {c : ParC} (hc : c.geo = geoOf S) (rd : α → Option (Forest.Heard × Heard))
    (q : α × Option Pub9) {l : List Aff} (e : fsSecond rd c q = some l) :
    lenStill (fsSecond rd c) q =
      (3 + 4 * S.NP) + (2 + 2 * S.NP + S.Lam + S.NP * S.cf.lt) + (1 + 2 * S.NP) := by
  rw [len_some e]
  unfold fsSecond at e
  obtain ⟨gh, -, e⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨v, -, e⟩ := Option.bind_eq_some_iff.1 e
  exact secondAt_count hc e

/-- **THE EQUATION HOLDS JUST WHERE BOTH LISTS OF FORMS ARE THERE**: where one of the two is not,
the two lengths together are not the closed number. -/
theorem lenBoth_eq_iff (Pl : PlaceIs S c0 c1 c2 c3) {c : ParC} (hc : c.geo = geoOf S)
    (rd : α → Option (Forest.Heard × Heard)) (q : α × Option Pub9) :
    lenStill (fsFirst rd c) q + lenStill (fsSecond rd c) q = attOwnB S ↔
      (fsFirst rd c q).isSome = true ∧ (fsSecond rd c q).isSome = true := by
  have hA := attOwnB_place Pl
  cases e1 : fsFirst rd c q with
  | none =>
    have z1 := len_none e1
    cases e2 : fsSecond rd c q with
    | none =>
      have z2 := len_none e2
      constructor
      · intro hs; omega
      · intro hs; cases hs.1
    | some l₂ =>
      have z2 := lenSecond_eq hc rd q e2
      constructor
      · intro hs; omega
      · intro hs; cases hs.1
  | some l₁ =>
    have z1 := lenFirst_eq Pl hc rd q e1
    cases e2 : fsSecond rd c q with
    | none =>
      have z2 := len_none e2
      constructor
      · intro hs; omega
      · intro hs; cases hs.2
    | some l₂ => exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => lenBoth_eq Pl hc rd q e1 e2⟩

end H2K5.Honest.Count

#print axioms H2K5.Honest.Count.LaysForms.of_eq
#print axioms H2K5.Honest.Count.StepLays.of_eq
#print axioms H2K5.Honest.Count.LaysForms.pure
#print axioms H2K5.Honest.Count.LaysForms.fail
#print axioms H2K5.Honest.Count.LaysForms.bind
#print axioms H2K5.Honest.Count.LaysForms.bind0
#print axioms H2K5.Honest.Count.StepLays.bind
#print axioms H2K5.Honest.Count.StepLays.bind0
#print axioms H2K5.Honest.Count.StepLays.yield
#print axioms H2K5.Honest.Count.LaysForms.iteB
#print axioms H2K5.Honest.Count.LaysForms.read
#print axioms H2K5.Honest.Count.LaysForms.lin
#print axioms H2K5.Honest.Count.LaysForms.mustAs
#print axioms H2K5.Honest.Count.LaysForms.refuse
#print axioms H2K5.Honest.Count.LaysForms.need
#print axioms H2K5.Honest.Count.LaysForms.needBind
#print axioms H2K5.Honest.Count.LaysForms.foldlM0
#print axioms H2K5.Honest.Count.LaysForms.foldlM
#print axioms H2K5.Honest.Count.LaysForms.forM
#print axioms H2K5.Honest.Count.LaysForms.forIn
#print axioms H2K5.Honest.Count.StepLays.linYield
#print axioms H2K5.Honest.Count.StepLays.after
#print axioms H2K5.Honest.Count.g_uEnt
#print axioms H2K5.Honest.Count.g_u3at
#print axioms H2K5.Honest.Count.g_weighted
#print axioms H2K5.Honest.Count.g_plane
#print axioms H2K5.Honest.Count.g_shV
#print axioms H2K5.Honest.Count.g_overG
#print axioms H2K5.Honest.Count.g_readDenominator
#print axioms H2K5.Honest.Count.g_readMaximum
#print axioms H2K5.Honest.Count.g_readIndexBit
#print axioms H2K5.Honest.Count.g_xl
#print axioms H2K5.Honest.Count.g_readHead
#print axioms H2K5.Honest.Count.g_readGroup
#print axioms H2K5.Honest.Count.g_lessPieces
#print axioms H2K5.Honest.Count.g_linPlanes
#print axioms H2K5.Honest.Count.g_callKR
#print axioms H2K5.Honest.Count.g_claim3
#print axioms H2K5.Honest.Count.g_endValues
#print axioms H2K5.Honest.Count.g_unitKFD
#print axioms H2K5.Honest.Count.g_callKFD
#print axioms H2K5.Honest.Count.g_claim4
#print axioms H2K5.Honest.Count.g_endValuesE
#print axioms H2K5.Honest.Count.g_claim5
#print axioms H2K5.Honest.Count.g_valueProduct
#print axioms H2K5.Honest.Count.g_claim6
#print axioms H2K5.Honest.Count.g_claim7
#print axioms H2K5.Honest.Count.g_claim8
#print axioms H2K5.Honest.Count.gather_count
#print axioms H2K5.Honest.Count.first_count_gen
#print axioms H2K5.Honest.Count.second_count
#print axioms H2K5.Honest.Count.counts_place3
#print axioms H2K5.Honest.Count.place_lists
#print axioms H2K5.Honest.Count.place_tab0
#print axioms H2K5.Honest.Count.place_tab1
#print axioms H2K5.Honest.Count.place_tab2
#print axioms H2K5.Honest.Count.place_tab3
#print axioms H2K5.Honest.Count.formsKR_place
#print axioms H2K5.Honest.Count.formsKFD_place
#print axioms H2K5.Honest.Count.first_count
#print axioms H2K5.Honest.Count.attOwnB_place
#print axioms H2K5.Honest.Count.firstAt_count
#print axioms H2K5.Honest.Count.secondAt_count
#print axioms H2K5.Honest.Count.bothAt_count
#print axioms H2K5.Honest.Count.lenBoth_eq
#print axioms H2K5.Honest.Count.place_of_plan
#print axioms H2K5.Honest.Count.len_none
#print axioms H2K5.Honest.Count.len_some
#print axioms H2K5.Honest.Count.lenFirst_eq
#print axioms H2K5.Honest.Count.lenSecond_eq
#print axioms H2K5.Honest.Count.lenBoth_eq_iff
