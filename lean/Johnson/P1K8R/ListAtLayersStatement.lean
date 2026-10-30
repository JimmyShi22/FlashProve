-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ListAtLayersStatement.lean: AT A STATE REACHED IN FRONT OF THE BATCHING OF A
FEED-FORWARD LAYERS' SEGMENT (member 28 g + 9 of the first chain's flat list) THE SMALLNESS TEST's
LIST OF TABLES IS THE LIST THAT THE STATE HOLDS AS RETURNED BY THE SEGMENT's OWN ROUNDS, WEIGHTS
TOO; its matrices and their number are the plan's. In the goals' scope, at an opening's letters. A
STATEMENT ALONE: one definition of a proposition; no definition of another kind. NOTHING IS PROVED
IN THIS FILE, and it is none of the library's goals: a lemma's statement.

WHAT IT IS NOT. CONDITIONAL ON "REACHED": nothing says that any state is reached. Nothing on what
the list holds. The layers' segments alone. The plain family of reached states, from any first
state. At the format's second hash function alone (OnBytes.secondHashFunction). The full size alone.

NEAR. `quiet_funs`, `quiet_front` (Johnson/Meaning/QuietFront.lean),
Johnson/Road/K4/ClosedTurns.lean: the equation behind one step's yes. `funs_from_reads`,
`funsSkel_at_batch` (Johnson/Desc/First/Link/Law/FunsAtBatch.lean): of the reading `S.funs?`, which
at a layers' link reads what the own rounds returned, not the smallness test's list.

Limits. Equations at a state, under "reached". Nothing on any property.
-/
import Johnson.IMR.SeatOpen
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- **The statement of the title.** Not proved here; a lemma's statement, none of the library's
goals. -/
def ListAtLayers : Prop :=
  ∀ (P : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (lay : ByteArray) (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub)
    (Bs : ProofFile.PureBase) (base : List (Block S ProofFile.Cl)) (c : Chain S ProofFile.Cl) (A : ProofFile.SharedSeat)
    (B : ProofFile.SecondSeat), VerifierAndGoals.InScope P = true → VerifierAndGoals.readFiles P = .ok pp →
    IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B →
    ∀ (Q : Type) (start : Q → S) (g : Nat), g < 12 → ∀ (z : Q) (s' : S),
      Reach 0 c.blocksInOrder start (28 * g + 9) (z, s') →
      ∃ hp tl o, Bs.G₀.W.G[g]? = some hp ∧ s'.tl? = some tl ∧ s'.own? = some o ∧
        tl.funs = o.funs ∧ tl.mats = hp.tl.mats ∧ tl.NM = hp.tl.NM

end P1K8

#print axioms P1K8.ListAtLayers
