-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/Frame.lean: the relation of the top theorems' interface at the full size, in
the plain statements of Johnson/Meaning/Says.lean.

The theorems on the compiled verifier name one relation between a decoded matrix M of field elements
and a request x (the field Rno of the configuration): at the full size, at a table pp of scales and
policy, it is "M is in range, and RelLAt pp M x" (relationsAndEncodingOfClaims, OnBytes/Flat/FilesAt.lean; claimsReqAt and
RelLAt, Johnson/Top/H/TargetAtPolicy.lean). RelLAt speaks of a trace of cells and of conditions
modulo the protocol's prime.

Main definitions and theorems:
  frameRel pp M x: that relation, written out. frameRel_is: it is the configuration's field Rno, by
    unfolding, at every decoder D, numbers N and coding E.
  relLAt_iff_says: at what the goals' reader returns, RelLAt pp M x holds exactly if M holds an
    index at which some stream meets Says.
  frameRel_iff_says: so does frameRel (a matrix that holds an index is in range).
What is not claimed. Nothing on a protocol. The full size alone.
-/
import Johnson.Goal.Meaning.TieR
import Johnson.Top.H.TargetAtPolicy
import OnBytes.Flat.FilesAt

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model
open VerifiableInference.OnPublicFiles.Flat (Holds InRange RelLAt GE Req)

variable {rows cols : ℕ}

/-- The relation of the interface at the full size, written out. -/
def frameRel (pp : ScalesAndPolicy) (M : Fin rows → Fin cols → GE) (x : Instance ppref) : Prop :=
  InRange M ∧ RelLAt pp M x

/-- It is the configuration's field Rno. -/
theorem frameRel_is (D : OnBytes.Slice.DecR) (N : OnBytes.Flat.MatrixNums) (pp : ScalesAndPolicy)
    (E : OnBytes.Flat.Coding (OnBytes.Flat.claimsReqAt D N pp))
    (M : (OnBytes.Flat.claimsReqAt D N pp).Mat) (x : Req) (c : Unit) :
    (OnBytes.Slice.DecR.configurationOfStoredTable (OnBytes.Flat.claimsReqAt D N pp)
      (OnBytes.Flat.relationsAndEncodingOfClaims _ E)).Rno M x c ↔ frameRel pp M x.val :=
  Iff.rfl

/-- **The claim of a request on a matrix, in plain statements.** -/
theorem relLAt_iff_says {pp : ScalesAndPolicy} (hs : (Cm.Scales.of pp).Lawful) (hpol : Policy.PolCond pp.pol)
    (M : Fin rows → Fin cols → GE) (x : Instance ppref) :
    RelLAt pp M x ↔ ∃ i : Cm.Idx, Holds M i ∧ ∃ S, Says pp i.index.val x S := by
  have L := Policy.ledger_relation_at_protocol_prime (Cm.Scales.of pp) hs pp.pol hpol
  constructor
  · rintro ⟨i, hi, T, hT⟩
    exact ⟨i, hi, (tieSays pp i x).2 ((L i x).1 T hT)⟩
  · rintro ⟨i, hi, hS⟩
    exact ⟨i, hi, _, Policy.ledger_sub _ _ _ _ _ ((L i x).2 ((tieSays pp i x).1 hS))⟩

/-- **The interface's relation, in plain statements.** -/
theorem frameRel_iff_says {pp : ScalesAndPolicy} (hs : (Cm.Scales.of pp).Lawful)
    (hpol : Policy.PolCond pp.pol) (M : Fin rows → Fin cols → GE) (x : Instance ppref) :
    frameRel pp M x ↔ ∃ i : Cm.Idx, Holds M i ∧ ∃ S, Says pp i.index.val x S :=
  ⟨fun h => (relLAt_iff_says hs hpol M x).1 h.2,
    fun h => ⟨⟨h.choose, h.choose_spec.1⟩, (relLAt_iff_says hs hpol M x).2 h⟩⟩

end Meaning

#print axioms Meaning.frameRel_is
#print axioms Meaning.frameRel_iff_says
