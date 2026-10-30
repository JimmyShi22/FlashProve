--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/More/OwnAtState.lean: THE PUBLIC TEST OF THE ITEM formsInT m 3 "own" (the forms of
K4's two runs of claims name only what is there) ACCEPTS AT THE VERIFIER's STATE BEHIND AN ACCEPT OF
K4's SUB-PROTOCOL, FROM TESTS WITH CODE AT THE STATE IN FRONT, ONE LINE ON WHAT THE LOOKUP HEARD,
AND TESTS ON THE PUBLIC PARAMETERS: NO MEANING, NO PROMISE, NO PIECE. One statement with its proof:
the calls of Riders/AsksAtMeans.lean, Rec/InTFour.lean and Riders/OwnAtMeans.lean, at the tests
themselves.

  `OwnFront`: what is asked of the state in front: FOURTEEN LINES: ten tests: of ledger m ·
  freeAbove m · look m · "K4.lookLeft" m · "frame.liveIs" · linkFresh m · "K12.seatsCarried" ·
  "K12.msgShapes" · "frame.sentIs" m · "ledger.treesAre" m; the statement's codes; the two counts;
    and ONE LINE ON WHAT THE LOOKUP HEARD: it has the public parameters' shape.
  **`own_at`**: `KeptAtS par s s'` · `OwnFront` at s · frontB · maskSeatP · readsArrayP · the two
  runs are K4's own term's, state by state ⟹ both runs' tests accept at s'.

Limits. Every premise stands; OF THE FOURTEEN LINES FIVE ("frame.liveIs" · "K12.seatsCarried" ·
"K12.msgShapes" · the codes · the heard shape) ARE NOT AMONG THE COMPOSED MEANING's OWN PUBLIC TESTS
IN FRONT OF K4: they are facts on reached states, owed by their authors. K04_law, the law of K4's
sub-protocol itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.More.RecAtState
import Johnson.Road.K4.Rec.InTFour
import Johnson.Road.K4.Riders.AsksOfFront
import Johnson.Road.K4.InT.FormsInTOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.More

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Total (frontB)
open OnBytes.Road.K4.InT (StatesAt formsInT_own inT_ofLink)
open OnBytes.Road.K4.Rec (RecPlan recIs_at_state four_of_kept readsArrayP)
open OnBytes.Road.K4.Riders (keptAsks_of_front padNames_of_left)
open VerifiableInference.Desc (Claim Link K9.LinkHoles K9.statesOfLink K9.readersOfLink K9.formsInT)
open VerifiableInference.Desc.First (S ledgerB freeAboveB)
open VerifiableInference.Desc.First.FillBare (lookLeftB)
open VerifiableInference.Desc.First.FillK4 (lookLayB look_agrees)
open VerifiableInference.Desc.First.FillSent (sentIsB treesAreB)
open VerifiableInference.Desc.First.RecordPlan (maskSeatP)
open VerifiableInference.Desc.K12.Door (atFirstSeats atFirstShapes)

/-- **What is asked of the state in front of K4's sub-protocol.** -/
structure OwnFront (par : Par) (R : RecPlan) (n m ns : ℕ) (s : S) : Prop where
  ledger : ledgerB s = true
  free : freeAboveB ns s = true
  look : lookLayB s = true
  lookLeft : lookLeftB s = true
  live : (decide (s.live.frame.shape = R.shape) && decide (s.live.rows.layout = R.layout)) = true
  fresh : ((s.tl?.bind (·.heard)).isNone && s.link?.any fun L => L.arrayOf == R.arrs m) = true
  seats : atFirstSeats R.L s = true
  shapes : atFirstShapes R.M s = true
  sent : sentIsB R.d m s = true
  trees : treesAreB R.d m s = true
  codes : s.st.codes = R.cs
  places : s.book.place.size = n
  msgs : s.st.oracles.size = n
  heard : ∀ al fo', s.here = .lay al → al.fo = some fo' → fo'.shape = par.P.y.fo

/-- **The two runs' tests behind an accept.** -/
theorem own_at {par : Par} {s s' : S} (K : KeptAtS par s s') {R : RecPlan} {n m ns : ℕ}
    (F : OwnFront par R n m ns s) {own : List (ℕ × ℕ)}
    (hB : frontB (!par.k3Runs) par.P par.hp par.g par.P.y.fo = true)
    (hM : (maskSeatP R.shape R.d own R.L.places n m).isSome = true)
    (hR : readsArrayP par.hp R.shape R.layout (R.arrs m) m (R.d.trees m) = true)
    {Hh : K9.LinkHoles} {l : Link S Claim}
    (st : ∀ u : S, StatesAt (K9.statesOfLink l) 2 par "front" u ∧
      StatesAt (K9.statesOfLink l) 2 par "back" u) :
    ([(2, "front"), (2, "back")].all fun p =>
      K9.formsInT (K9.readersOfLink Hh l) own p.1 p.2 s') = true := by
  have K0 := K
  obtain ⟨a, _, _, _, ha, _⟩ := K0
  obtain ⟨A₀, hA₀, _, _⟩ := OnBytes.Desc.First.K4.InT.segAt_lay ha
  have r := recIs_at_state (R := R) (n := n) (m := m) hA₀ F.live F.fresh F.seats F.shapes
    F.sent F.trees F.codes F.places F.msgs
  obtain ⟨g1, g2, g3, g4⟩ := four_of_kept K (Rec.sized_of_ledgerB F.ledger) hA₀ r own hM hR
  have hag : ∀ al, s.here = .lay al → al.fo = al.lookHeard := fun al hal => look_agrees F.look hal
  obtain ⟨o₀, A⟩ := keptAsks_of_front K F.ledger F.free F.lookLeft hag F.heard hB
  obtain ⟨h1, h2⟩ := formsInT_own own par s s' par.P o₀ (K9.statesOfLink l) K A
    ⟨fun al fo' hal hfo' => padNames_of_left F.lookLeft hal (hag al hal) hfo', g1, g2, g3, g4⟩
    (st _).1 (st _).2
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨inT_ofLink Hh l _ 2 "front" _ (by decide) h1, inT_ofLink Hh l _ 2 "back" _ (by decide) h2⟩

end OnBytes.Road.K4.More

#print axioms OnBytes.Road.K4.More.own_at
