-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/JoinAtBatch.lean: OkHead's CLAUSE join (OkOne.lean): the slots that the
form left for the join names are filled in the state's ledger: A PROJECTION OF THE LOOKUPS' PROMISE
AT THE CALLS' SEAT (K3LeftOn, Johnson/Top/H/K3LeftStatement.lean). The sister of hb_of_leftOn
(HbAtHead.lean).
  leftOn_cEndFilled   K3Left's field cEndFilled, carried along Fo.Later's field keep; general in the
                      two readers
  **join_of_leftOn**  the clause join, to the letter, at the fixed part of a state of which the
                      promise holds; general in φ and kap
PREMISE. LC : K3LeftOn S.fork? S.lookHeard? … s: at 347 the table's promise gives it
(leftOn_at_front, KxOfTable.lean). Nothing else.
Limits. That the promise can be met is not shown. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.HbAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.OnPublicFiles (K3LeftOn)

/-- **The slots that the form left for the join names are filled in the state's ledger**: a
projection of the lookups' promise on the state: K3Left's field cEndFilled, carried along
"later". -/
theorem leftOn_cEndFilled {T : Type} {fork : T → Option Fork} {heard : T → Option Forest.Heard}
    {h : Forest.Shape} {lm first : ℕ} {Qf : Fork → Prop} {s : T}
    (L : K3LeftOn fork heard h lm first Qf s) :
    ∀ g G, heard s = some g → fork s = some G → CEndFilled g G := by
  obtain ⟨_, F', G0, g0, _, _, _, K, hg, hG, hL, _⟩ := L
  intro g G e eG x hx
  obtain rfl : g0 = g := Option.some.inj (hg.symm.trans e)
  obtain rfl : G0 = G := Option.some.inj (hG.symm.trans eG)
  exact (hL.keep x.1 (K.cEndFilled x hx).2).1

/-- **OkHead's CLAUSE join**, at the fixed part of a state of which the lookups' promise at the
calls' seat holds. -/
theorem join_of_leftOn {α : Type} (φ : S → α) (kap : α → Option Seen)
    (hkap : ∀ e, kap (φ e) = seenOf e) {hC : Forest.Shape} {lmC jC : ℕ} {QC : Fork → Prop} {s : S}
    (LC : K3LeftOn S.fork? S.lookHeard? hC lmC jC QC s) :
    ∀ z u g, kap (fixed9 φ s).1 = some z → (fixed9 φ s).2 = some u → z.lookHeard = some g →
      CEndFilled g u.F := by
  intro z u g hz hu hg
  have hz' : seenOf s = some z := (hkap s).symm.trans hz
  have hu' : (atS.get? s).map pubOf = some u := hu
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hu'
  have hF := K9.get_fork s b hb
  exact leftOn_cEndFilled LC g _ ((seen_look hz' hF).symm.trans hg) hF

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.leftOn_cEndFilled
#print axioms VerifiableInference.Desc.LinkJoin.join_of_leftOn
