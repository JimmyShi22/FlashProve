-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K10/Honest/LeavesAt.lean: which record the closing of a segment returns.

What is proved. `close_leaves`: from `CloseBase P s D` (the facts in front of the block that name none of its
challenges) and rounds of the kind's shape, the batching returns a row at the element that "BAT" drew, and the block's
decision returns this record: nothing owed; the frame with the single rows
`foldOutAt (D.S1 s) (D.F s) row D.m (rE :: rR)`, no mask, the link's number moved on, the next call "first"; the
statement `spent (D.S1 s) D.m` (`spent` is Johnson/Prover/Link/FormFold.lean's, as in `yes_leaves`). One theorem, on the
verifier's own text; no move of a prover is named.

Why. `close_plays` (Johnson/Desc/K10/Honest/Leaves.lean) says that the decision returns a record and that this record's
single rows are true, but not which rows they are. A law that has to name a stage or a fresh table that depends on the
rows' code, layout or fresh mask must name them before that record is at hand. `closeBase_holds` (Holds.lean) speaks of
`foldOutAt (D.S1 s) (D.F s) row D.m (rE :: rR)`; this file shows that the decision lays exactly these rows.

Proof. By `close_yes_all` (Base.lean) and `yes_leaves` (Leaves.lean); the five equations between the data that
`yes_leaves` gives and the data of `CloseBase` are those in the proof of `close_plays`.

Limits. `CloseBase` is an assumption: that it holds at a state of a run is not shown here. The theorem is on the block's
decision at the kind's own record, not on the block's step, which asks two tests in front of the decision (Step.lean),
nor on the block as the first chain runs it (AtS.lean). Nothing is said of words, of a fresh table or of what the rounds
show. Nothing is said on soundness, completeness or hiding of the protocol.
-/
import Johnson.Desc.K10.Honest.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.Values
open OnBytes OnBytes.Means OnBytes.Slice Johnson.Prover.Link H2K.ClaimSays Cb
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par Rec kind onSt)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase CloseFront CloseData ShapedAll)

/-- **The record that the decision returns**, written with the data of `CloseBase`. -/
theorem close_leaves {Cl : Type} {P : Par} {s : Rec} {D : BaseData} (H : CloseBase P s D)
    (rB rE : Fmt.RoundView) (rR : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hl : (rB :: rE :: rR).length = 2 + P.k) (hsh : ShapedAll (rB :: rE :: rR)) :
    ∃ row, Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩
        (drawnOf rB) = some row ∧
      ((kind (Cl := Cl)) P).decide s (rB :: rE :: rR) gs = .ok ⟨none, { s.frame with
          rows := foldOutAt (D.S1 s) (D.F s) row D.m (rE :: rR), mask := none
          link := s.frame.link + 1, next := .first }, spent (D.S1 s) D.m⟩ := by
  obtain ⟨s', hy⟩ := ProofFile.Honest.K10.YesFree.close_yes_all (Cl := Cl) H (rB :: rE :: rR) gs hl hsh
  obtain ⟨t, D', ht, H', rfl⟩ := yes_leaves hy
  have hx : drawnOf rB = E.ofTriple t := by
    unfold drawnOf
    rw [ht]
    rfl
  have eG : D'.G = D.Gq := Option.some.inj (H'.group.symm.trans H.group)
  have em : D'.m = D.m := Option.some.inj (H'.mask.symm.trans H.mask)
  have eb : (D'.input, D'.d) = (⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩,
      { onSt s.st with st := D.S1 s }) := by
    have h1 := H'.layout
    unfold Ground.beginRunP at h1
    have hb : Ground.ok (Ground.beginRunL (onSt s.st).st s.frame.group) = true := H.beginRun
    have ht' : (onSt s.st).st.groups[s.frame.group]? = some D.G := H.there
    rw [if_pos hb, ht'] at h1
    exact (Option.some.inj h1).symm
  obtain ⟨ei, ed⟩ := Prod.mk.inj eb
  have eF : D'.F s = D.F s := by
    show ioppFoldShape _ D'.input.layout = ioppFoldShape _ (Own.layoutOf s.st D.G)
    rw [ei, eG]
  refine ⟨D'.row, ?_, ?_⟩
  · have h2 := H'.combine
    rw [ei, ed, ← hx] at h2
    exact h2
  · have e1 : D'.d.st = D.S1 s := congrArg (·.st) ed
    rw [hy, e1, eF, em]

end ProofFile.Honest.K10.Values

#print axioms ProofFile.Honest.K10.Values.close_leaves
