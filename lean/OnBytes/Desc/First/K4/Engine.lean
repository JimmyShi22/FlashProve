-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/K4/Engine.lean: what the text of the layers' own rounds asks of the parts beneath
it.

The kind K4 (OnBytes/Desc/First/K4/Hear.lean, Claims.lean) is written once, over a record of
eighteen operations. They belong to four parts that several kinds share:
  the strict reading of a round: `point`, `batch`;
  the ledger of the sub-proof's slots and claims: `fork`, `change`, `shown`, `claimsIn`, `lin`;
  the masked sumcheck: `pscBegin`, `roundIn`, `pscEnds`, `pscRow`, `levelIn`, `tscIn`;
  the merge of the claims on the weights: `wsForkEnd`;
and four ways to refuse: `get`, `must`, `mustAs`, `check`.
OnBytes/Desc/First/K4/Plain.lean fills the record with plain functions on data.

Limits. Definitions alone.
-/
import OnBytes.Model.Layer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest

/-- The operations of a sub-proof's engine that the text below calls. -/
structure Eng (m : Type → Type) where
  /-- unwraps a value whose presence hangs on public numbers alone; refuses if it is not there -/
  get : {α : Type} → Option α → m α
  /-- a public condition -/
  must : Bool → m Unit
  /-- a public condition, with the name of its refusal -/
  mustAs : String → Bool → m Unit
  /-- a condition on values, with the name of its refusal -/
  check : String → Bool → m Unit
  /-- the sub-proof's state -/
  fork : m Fork
  /-- changes the sub-proof's state by a step that may refuse -/
  change : (Fork → Option Fork) → m Unit
  /-- the value that was shown under a slot -/
  shown : Nat → m E
  /-- adds a claim -/
  lin : Aff → m Unit
  /-- a round in which a point is drawn -/
  point : RoundName → Nat → m (Array E)
  /-- receives hidden values under the next slots; returns the first slot -/
  claimsIn : Nat → m Nat
  /-- a round that batches rows; returns the powers of the drawn element -/
  batch : Nat → m (Array E)
  /-- the masked sumcheck's routines -/
  levelIn : Nat → Array E → Aff → List Nat → m Level
  tscIn : Array E → Nat → Nat → Nat → m Tsc
  pscBegin : Aff → m Psc
  roundIn : RoundForm → Psc → E → Nat → m (E × Psc)
  pscEnds : Psc → Nat → Nat → m (Nat × Psc)
  pscRow : Psc → E → Aff → m (Aff × Psc)
  /-- the merge of the weight claims: its tests on the claims' number and sizes, its messages, and
  what is left of each claim -/
  wsForkEnd : WsLay → Array WsClaim → Array Nat → m WsForkOut

variable {m : Type → Type} [Monad m] (En : Eng m)

/-- A sumcheck's claim with nothing kept. -/
def sumcheckClaim (p : Psc) (S0 : E) : m (Aff × Psc) := En.pscRow p S0 {}

/-- The values that were shown under the n slots from first on. -/
def shownRun (first n : Nat) : m (Array E) :=
  (Array.range n).mapM fun i => En.shown (first + i)

/-- After roundsIn and stackRounds (OnBytes/Model/Look.lean:83-88, :102-104). -/
def plainRounds (st : Stack) : m Stack := do
  let (r, p) ← (List.replicate st.lam (zeroE, 0)).foldlM
    (fun (s : Array E × Psc) (z : E × Nat) => do
      let (r, q) ← En.roundIn .sum2 s.2 z.1 z.2
      pure (s.1.push r, q))
    (#[], st.p)
  pure { st with rs := r.reverse, p := p }

end OnBytes.Desc.First.K4
