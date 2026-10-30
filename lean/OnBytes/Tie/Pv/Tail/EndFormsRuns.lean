-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndFormsRuns.lean: what objectsF adds, as a list of forms
(`objectsF_forms_from`, OnBytes/Tie/Pv/Tail/EndFormsFrom.lean), at one run of the check of an
attention sub-proof and of a layer group's sub-proof, with that theorem's premises on the state and
on the record paid from the run.

Theorems with their proofs. The run is given taken apart, as the records `AttRan`
(OnBytes/Tie/Pv/Keeps/KeepsChainA2.lean) and `LayRan` (OnBytes/Tie/Pv/Keeps/LayerRan.lean) have it.
`objectsF_forms_from` asks four things: the run of objectsF; that the record's shapes fit its
matrices; that the state has one coefficient for each slot; and `RawRows`. The first is a field of
the record of the run. The second and third are in OnBytes/Tie/Pv/Tail/EndInvRuns.lean. The fourth
comes from `ReadsRaw` (OnBytes/Tie/Pv/Tail/EndAttAll.lean, EndLayRows.lean).

Main names:
  `attRan_rawRows`: `RawRows` at the states of `AttRan`, at the batching element of the state that
    objectsF takes.
  `attRan_forms`, `layRan_forms`: the conclusion of `objectsF_forms_from`, with the plan's own
    number of claims.

Limits: the run must begin at the plan's state. `ReadsRaw` at the cells of m
(OnBytes/Tie/Pv/Tail/EndRaw.lean) is a premise. The lay Y is a free letter. Of what the lookup's
claims add to the total nothing is said. Nothing at the head. The plan is taken as the value that
the planning routine returns. The plan with which the verifier runs differs from it: at attention
the routine attentionOwners fills one record of the list plFor in the plan's record (the number of
the sub-proof that owns the matrix, and the array's place: borderMeans); at the head the weights are
taken off all virtual rows of the state.


-/
import OnBytes.Tie.Pv.Tail.EndAttAll
import OnBytes.Tie.Pv.Tail.EndFormsFrom
import OnBytes.Tie.Pv.Tail.EndInvRuns
import OnBytes.Tie.Pv.Tail.EndLayRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port OnBytes.L5 OnBytes.L5.LayerRan
  OnBytes.L5.LayerCut OnBytes.Road.Rows

variable {K : Type} [Field K] {J : Type} [Fintype J] (Y : Lay J) (ρ : Reading K) (W : World K)

section
variable {P : Attention.Plan} {L L' : LinkCtx} {F' : Fork} {c c' : Ctx} {tl0 : HTailF2}
  {f : Attention.First} {t : Attention.Tables} {tl1 tlA tl : HTailF2} {laid : Nat}
  {L1 L2 L3 L4 : LinkCtx} {F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 : Fork}
  {c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 : Ctx}

/-- `RawRows` at the record's own states, at the batching element of the state that objectsF takes.
-/
theorem attRan_rawRows (s0 : Attention.Seam) (nU3 hb hbLine : Nat)
    (hplan : s0.plan nU3 hb hbLine = .ok P.seam)
    (X : AttRan P L P.seam.Fp c L' F' c' tl0 f t tl1 tlA tl laid L1 L2 L3 L4 F1 F2 F3 F4 F5 F6 F7
      F8 F9 F10 F11 F12 F13 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14)
    (A : Nat → Nat → Nat → K) (hW : ReadsRaw ρ tl t.funs F11 W A) :
    RawRows W tlA F8 t.funs (ρ.val F7.theta) A := by
  have h := rawRows_attention_runs ρ s0 P nU3 hb hbLine _ f [P.iU3] t.funs P.ns P.nLin _
    P.nMsg P.seam.nU tl0 tl1 tlA tl L L1 L2 L3 L4 F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12
    c c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 W A hplan X.start X.hear X.root X.closed
    X.transcript X.setPlan X.batch X.claims X.objects X.noFree X.selfTest X.coefficients X.v12
    X.tile hW
  rw [(objectsF_keeps tlA tl t.funs F7 F8 c8 c9 X.objects (attRan_state X).1).2.2] at h
  exact h

/-- What objectsF adds at attention, as a list of forms. -/
theorem attRan_forms (s0 : Attention.Seam) (nU3 hb hbLine : Nat)
    (hplan : s0.plan nU3 hb hbLine = .ok P.seam)
    (X : AttRan P L P.seam.Fp c L' F' c' tl0 f t tl1 tlA tl laid L1 L2 L3 L4 F1 F2 F3 F4 F5 F6 F7
      F8 F9 F10 F11 F12 F13 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14)
    (m : J → K) (hW : ReadsRaw ρ tl t.funs F11 W fun t r c => Y.cellAt m t r c) :
    ((rowsForm Y ρ tlA t.funs P.nLin).map Prod.fst).Nodup ∧
    (∀ p ∈ rowsForm Y ρ tlA t.funs P.nLin,
      P.nLin ≤ p.1 ∧ p.1 ≤ P.nLin + topOf tlA t.funs - 1) ∧
    ∃ g Fa ca tla Fb cb tlb Fc cc,
      tlA.heard = some g ∧ Forest.objects g F7 c8 = .ok (((), Fa), ca) ∧
      tlA.linJoin9 Fa ca = .ok ((tla, Fb), cb) ∧ tla.linBits9 Fb cb = .ok ((tlb, Fc), cc) ∧
      c9 = cc ∧ Kept Fc F8 ∧
      F8.nClaim = Fc.nClaim + tlA.NM + (readsList tlA t.funs).length ∧
      F8.total ρ W = Fc.total ρ W +
        (batchAt (ρ.val F7.theta) (rowsForm Y ρ tlA t.funs P.nLin)).gap m := by
  have h := objectsF_forms_from Y ρ W tlA tl t.funs F7 F8 c8 c9 X.objects
    (attRan_fits s0 nU3 hb hbLine hplan X) (attRan_state X).1 m
    (attRan_rawRows ρ W s0 nU3 hb hbLine hplan X _ hW)
  rw [(attRan_state X).2.1] at h
  exact h

end

section
variable {P : Layer.Pub} {hp : Layer.HPlan2} {g : Nat} {L L' : LinkCtx} {F' : Fork} {c c' : Ctx}
  {iU3 : Nat} {fo : Forest.Heard} {o : Layer.Own} {F0 F1 F2 F3 : Fork} {L3 : LinkCtx}
  {c1 c2 c3 : Ctx} {tl1 tlA tl : HTailF2} {laid : Nat} {L4 L6 : LinkCtx}
  {F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 : Fork}
  {F21 F22 F23 F24 F25 F26 F27 F28 F29 F30 F31 F32 F33 F34 : Fork}
  {c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 : Ctx}
  {c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 : Ctx}

/-- What objectsF adds at a layer group, as a list of forms. -/
theorem layRan_forms (O : Option Layer.HPlan2) (hplan : Layer.planG P g O = .ok hp)
    (X : LayRan P hp g L hp.Fp c L' F' c' iU3 fo o F0 F1 F2 F3 L3 c1 c2 c3 tl1 tlA tl laid L4 L6
      F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 F19 F20 F21 F22 F23 F24 F25 F26 F27
      F28 F29 F30 F31 F32 F33 F34 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20
      c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34)
    (m : J → K) (hW : ReadsRaw ρ tl o.funs F33 W fun t r c => Y.cellAt m t r c) :
    ((rowsForm Y ρ tlA o.funs hp.nLin).map Prod.fst).Nodup ∧
    (∀ p ∈ rowsForm Y ρ tlA o.funs hp.nLin,
      hp.nLin ≤ p.1 ∧ p.1 ≤ hp.nLin + topOf tlA o.funs - 1) ∧
    ∃ g Fa ca tla Fb cb tlb Fc cc,
      tlA.heard = some g ∧ Forest.objects g F22 c22 = .ok (((), Fa), ca) ∧
      tlA.linJoin9 Fa ca = .ok ((tla, Fb), cb) ∧ tla.linBits9 Fb cb = .ok ((tlb, Fc), cc) ∧
      c23 = cc ∧ Kept Fc F23 ∧
      F23.nClaim = Fc.nClaim + tlA.NM + (readsList tlA o.funs).length ∧
      F23.total ρ W = Fc.total ρ W +
        (batchAt (ρ.val F22.theta) (rowsForm Y ρ tlA o.funs hp.nLin)).gap m := by
  have hV := layRan_rawRows ρ O hplan X W _ hW
  rw [(objectsF_keeps tlA tl o.funs F22 F23 c22 c23 X.objectsF (layRan_state X).1).2.2] at hV
  have h := objectsF_forms_from Y ρ W tlA tl o.funs F22 F23 c22 c23 X.objectsF
    (layRan_fits O hplan X) (layRan_state X).1 m hV
  rw [(layRan_state X).2.1] at h
  exact h

end

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.attRan_rawRows
#print axioms OnBytes.Tie.Pv.Tail.attRan_forms
#print axioms OnBytes.Tie.Pv.Tail.layRan_forms
