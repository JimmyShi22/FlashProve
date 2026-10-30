-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/SpecCoins.lean: the finite type of the link prover's random values, an
addition on it, and five statements on its embedding into the coin variables. Definitions and
statements.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

No proof here: coinsAdd, coinsInj and coinsCancel are proved in CoinsAdd.lean, coinsIn and
coinsOnto in CoinsPlaces.lean.

The type and the map are those of Johnson/Prover/Link/LinkCoin.lean (LinkK, coinsOf). An element is
a family of finite functions, each of a type fixed by the sizes of the message that holds it.
coinsOf embeds it in the prover's algorithm's coin variables, with 0 outside the sizes. The step
from the coin variables down to that type (UpToShiftOn.comap, Johnson/LinkSim/UpToOn.lean) asks four
things of the map: it is one to one, additive and into the places, and every family of coin
variables in the places is in its image.

What this file states. All five hold for all parameters, but coinsOnto, which asks that the plan
have a stage.
  Spec.coinsAdd      coinsOf of a sum is addC of the two (Johnson/LinkSim/AtText/Defs.lean).
  Spec.coinsInj      coinsOf is one to one.
  Spec.coinsCancel   the sum can be cancelled on the right.
  Spec.coinsIn       coinsOf at the plan's own stages is in the places (InPlaces,
                     Johnson/LinkSim/AtText/Places.lean).
  Spec.coinsOnto     where the plan has a stage, every family of coin variables in the places is
                     coinsOf of an element. (At a plan without a stage the type has one element,
                     which is embedded as zeros, while InPlaces leaves the pads, the front's tails
                     and the stages' variables free: there the statement would be false.)
  addFirst, addSw, addRide, addWord, addBody, addLink   the sum, field by field, along the stages.

How it fits. CoinsDown.lean uses coinsInj, coinsAdd, coinsIn and coinsOnto to carry Spec.linkShiftIn
down to this finite type (UpToShiftOn.comap). The proof of homeExact
(Johnson/LinkSim/AtHome/Home.lean) uses coinsCancel.

Notes. No premise on sizes is asked but that one (a stage, in coinsOnto).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkCoin
import Johnson.LinkSim.AtText.Places

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (P15 p12Of)
open H2K.Pub (sgOf)
open Johnson.Prover.Link

/-- The sum of two values of this part of the coins, entry by entry. -/
def addFirst {S : Sz} {s₀ : Sg} (k k' : FirstK GE S s₀) : FirstK GE S s₀ :=
  ⟨fun a i q => k.tail a i q + k'.tail a i q, fun a => k.pad a + k'.pad a,
    fun x => k.W x + k'.W x, fun q => k.wTail q + k'.wTail q⟩

/-- The sum of two values of this part of the coins, entry by entry. -/
def addSw {s s' : Sg} (k k' : SwK GE s s') : SwK GE s s' :=
  ⟨fun b q => k.mainTail b q + k'.mainTail b q, fun i => k.free i + k'.free i,
    fun b q => k.maskTail b q + k'.maskTail b q⟩

/-- The sum of two values of this part of the coins, entry by entry. -/
def addRide {s : Sg} (k k' : RideK GE s) : RideK GE s :=
  ⟨fun x => k.W x + k'.W x, fun b q => k.tail b q + k'.tail b q⟩

/-- The sum of two values of this part of the coins, entry by entry. -/
def addWord {s : Sg} (k k' : WordK GE s) : WordK GE s :=
  ⟨fun q => k.mainTail q + k'.mainTail q, fun i => k.main i + k'.main i,
    fun i => k.mask i + k'.mask i, fun q => k.maskTail q + k'.maskTail q⟩

/-- The sum along the stages. -/
def addBody : (cur : Fmt.M1.Stage) → (rest : List Fmt.M1.Stage) → BodyK GE cur rest →
    BodyK GE cur rest → BodyK GE cur rest
  | _, [], _, _ => ()
  | _, [_], k, k' => (addSw k.1 k'.1, addWord k.2 k'.2)
  | _, next :: n₂ :: rest, k, k' =>
    (addSw k.1 k'.1, addRide k.2.1 k'.2.1, addBody next (n₂ :: rest) k.2.2 k'.2.2)

/-- **The sum of two elements of LinkK.** -/
def addLink (S : Sz) : (l : List Fmt.M1.Stage) → LinkK GE S l → LinkK GE S l → LinkK GE S l
  | [], _, _ => ()
  | first :: rest, k, k' => (addFirst k.1 k'.1, addBody first rest k.2 k'.2)

/-- Statement only; proved as coinsAdd in CoinsAdd.lean. coinsOf of a sum is addC of the two. -/
def Spec.coinsAdd : Prop :=
  ∀ (S : Sz) (l : List Fmt.M1.Stage) (k k' : LinkK GE S l),
    coinsOf S l (addLink S l k k') = addC (coinsOf S l k) (coinsOf S l k')

/-- Statement only; proved as coinsInj in CoinsAdd.lean. coinsOf is one to one. -/
def Spec.coinsInj : Prop :=
  ∀ (S : Sz) (l : List Fmt.M1.Stage), Function.Injective (coinsOf S l)

/-- Statement only; proved as coinsCancel in CoinsAdd.lean. The sum cancels on the right. -/
def Spec.coinsCancel : Prop :=
  ∀ (S : Sz) (l : List Fmt.M1.Stage) (k k' d : LinkK GE S l),
    addLink S l k d = addLink S l k' d → k = k'

/-- Statement only; proved as coinsIn in CoinsPlaces.lean. coinsOf is in the places. -/
def Spec.coinsIn : Prop :=
  ∀ (P : P15) (S : Sz) (k : LinkK GE S (p12Of P).nums.stages),
    InPlaces P S (coinsOf S (p12Of P).nums.stages k)

/-- Statement only; proved as coinsOnto in CoinsPlaces.lean. Where the plan has a stage, every
family of coin variables in the places is coinsOf of an element. -/
def Spec.coinsOnto : Prop :=
  ∀ (P : P15) (S : Sz) (C : LCoins), (p12Of P).nums.stages ≠ [] → InPlaces P S C →
    ∃ k : LinkK GE S (p12Of P).nums.stages, coinsOf S (p12Of P).nums.stages k = C

end OnBytes.LinkSim.AtText
