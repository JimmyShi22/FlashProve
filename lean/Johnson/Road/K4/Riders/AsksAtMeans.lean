-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/AsksAtMeans.lean: THE PREMISE asks OF `hOwn_of_means` AND `k4Row_of_means`
(at an accept of K4's sub-protocol inside the promise in front: the premises of the law
`formsInT_own`: `KeptAsks` · `InTAsks` · `StatesAt` at K4's two runs), AT A MEANING WITH `K4Means`:
OUT OF THE PROMISE IN FRONT, ONE TEST ON THE PUBLIC PARAMETERS, AND THREE NAMED PREMISES. One
statement with its proof: the promise's tests drawn out, then calls.

  **`asks_of_means`**: `K4Means` · `K4Front` at the layout's own shape (hh3) · the public
    parameters' number of slots (hns) · `frontB` at the sub-protocol's own letters (ONE TEST ON THE
    PUBLIC PARAMETERS) · left : inside the promise in front, unmarked: `lookLeftB` (the name
      "K4.lookLeft": to become an equation of `K4Means` and an item of the promise when its layer
    lies in the composed filling) · four : at a Yes: the four fields hK · mask · oneRow · reads of
      `InTAsks` at the state behind ("the verifier's state reads as the public
    parameters say") · st : the seat's tie at K4's two runs (InT/SeatTie.lean has it at every state,
      at a sub-protocol behind the driver's guard)
    ⟹ asks.
  OUT OF THE PROMISE, BY THE EQUATIONS: the ledger has its sizes (ledger m) · it is free from its
  next slot on (freeAbove m) · the segment's two readers of what the lookup has heard agree (look m)
    ·
  what was heard has the layout's shape (the item left m's sentence).

Limits. left, four and st are premises. frontB has run at one small set of public parameters (true;
its negative tests rang): no theorem. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED.
Nothing on soundness.
-/
import Johnson.Road.K4.Riders.AsksOfFront
import Johnson.Road.K4.Riders.OwnAtMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open Iop OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par seatS seatS_look)
open OnBytes.Desc.First.K4.Total (KeptAsks frontB)
open OnBytes.Road.K4.InT (InTAsks StatesAt oneRowB readsThereB)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit Claim Link K9.statesOfLink K9.segAt? K9.maskSeat)
open VerifiableInference.Desc.First (S ModelPart Meaning)
open VerifiableInference.Desc.First.FillBare (lookLeftB)
open VerifiableInference.Desc.Sound (Frame Piece onQ MsgT)

variable {Xi P Tok Cl : Type} {rows cols nR kC : ℕ} {X : Verify.Public} {Fr : Frame}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X} {Z : P}
  {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}
  {q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT)} {par : Par}

/-- **The premises of `formsInT_own` at an accept inside the promise in front.** -/
theorem asks_of_means (E : K4Means Mg D) (H : AtK4 links ps k m pl) {h3 : Forest.Shape}
    {lm first : ℕ} {Q3 : Fork → Prop} (Kf : K4Front Mg Z links ps m h3 lm first Q3)
    (hh3 : h3 = par.P.y.fo) {ns : ℕ} (hns : D.nsOf m = some ns)
    (hB : frontB (!par.k3Runs) par.P par.hp par.g par.P.y.fo = true) {l : Link S Claim}
    (left : ∀ a : S × Fr.E.Str, onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      lookLeftB a.1 = true)
    (four : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' →
      (∀ o', (behindOf seatS q a τ o G').1.own? = some o' → par.hp.nU.getD 2 0 ≤ o'.v.K3) ∧
      (∀ A, K9.segAt? (behindOf seatS q a τ o G').1 = some A →
        (K9.maskSeat (D.N.sent m 0) A).isSome = true) ∧
      (∀ G o', (behindOf seatS q a τ o G').1.fork? = some G →
        (behindOf seatS q a τ o G').1.own? = some o' → oneRowB G o'.v.iU3 = true) ∧
      ∀ A o', K9.segAt? (behindOf seatS q a τ o G').1 = some A →
        (behindOf seatS q a τ o G').1.own? = some o' →
        readsThereB A o'.v.iU3 (par.hp.nU.getD 2 0) = true)
    (st : ∀ s : S, StatesAt (K9.statesOfLink l) 2 par "front" s ∧
      StatesAt (K9.statesOfLink l) 2 par "back" s) :
    ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∃ (P₀ : Layer.Pub) (o₀ : Own),
        KeptAsks par a.1 (behindOf seatS q a τ o G').1 P₀ o₀ ∧
        InTAsks (D.N.sent m 0) par a.1 (behindOf seatS q a τ o G').1 ∧
        StatesAt (K9.statesOfLink l) 2 par "front" (behindOf seatS q a τ o G').1 ∧
        StatesAt (K9.statesOfLink l) 2 par "back" (behindOf seatS q a τ o G').1 := by
  intro a τ fo o G' ha hu y
  have f := k4_pub_front D.N Mg Z H Kf.fit ha hu
  have f1 := f (.ledger m) (by simp)
  have f2 := f (.freeAbove m) (by simp)
  have f3 := f (.look m) (by simp)
  rw [E.ledger] at f1
  rw [E.freeAbove, hns] at f2
  have hag : ∀ al, a.1.here = .lay al → al.fo = al.lookHeard := fun al hal => Kf.look a.1 al f3 hal
  have hsh : ∀ al fo', a.1.here = .lay al → al.fo = some fo' → fo'.shape = par.P.y.fo := by
    intro al fo' hal hfo'
    obtain ⟨_, _, g, _, _, _, L, hg, _⟩ := k4_left_front D.N Mg Z H Kf ha hu
    have e : seatS.look a.1 = some fo' := by
      rw [seatS_look hal]
      exact hfo'
    obtain rfl : g = fo' := Option.some.inj (hg.symm.trans e)
    rw [L.shape, hh3]
  have hl := left a ha hu
  obtain ⟨o₀, A⟩ := keptAsks_of_front (kept_of_yes y) f1 (by simpa using f2) hl hag hsh hB
  obtain ⟨g1, g2, g3, g4⟩ := four a τ fo o G' ha hu y
  exact ⟨par.P, o₀, A,
    ⟨fun al fo' hal hfo' => padNames_of_left hl hal (hag al hal) hfo', g1, g2, g3, g4⟩,
    (st _).1, (st _).2⟩

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.asks_of_means
