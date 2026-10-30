-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoFixedUAtt.lean.
The attention sub-proof's own claims are fixed before the state and read the array of reads alone.

What is asked of the records: of a sumcheck's record (Sc3, Scd): that its row's form rowU is InU; of
a score: that of its sumcheck; of the records Divide and Attain: that of their sumchecks; of the
record Heard: that of the lookup's record g (OnBytes/Tie/Pv/Lookup/Ends/FoFixedULook.lean), of its
scores, of d and of x; of the record Joins: that of its key forms.
States Fo.FixedU h.iU3 (OnBytes/Tie/Pv/Lookup/Ends/FoFixedU.lean, with its limits) of Attention.u3at
and, for a record h that is good, of claim3, claim4, claim5 (for a good record of key forms),
claim6, claim7, claim8, and of Attention.claims as a whole (fixedU_claims). That routine adds the
lookup's rows, the join and the three claims on the planes too, so the one list covers them.
Limits: which the members of the list are, how many, and in which order is not said here. The list
of fixedU_claims stands under an ∃ of its own: no statement ties it to the lists of claims_added
(OnBytes/Tie/Pv/Lookup/Ends/FoAddsAttAll.lean).

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a record which a run of Attention.hear returns is good: no file of this
library shows it.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoFixedULook
import OnBytes.Model.Attention

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention

instance goodSc3 : HasGood Sc3 := ⟨fun t s => InU t s.rowU⟩
instance goodScd : HasGood Scd := ⟨fun t s => InU t s.rowU⟩
instance goodScore : HasGood Score := ⟨fun t k => good t k.sc⟩
instance goodDivide : HasGood Divide := ⟨fun t d => good t d.scE ∧ good t d.vpm ∧ good t d.vpd⟩
instance goodAttain : HasGood Attain := ⟨fun t x => good t x.scF ∧ good t x.scd ∧ good t x.scH⟩
instance goodHeardA : HasGood Attention.Heard :=
  ⟨fun t h => good t h.g ∧ good t h.scores ∧ good t h.d ∧ good t h.x⟩
instance goodJoins : HasGood Joins := ⟨fun t j => good t j.kf⟩

section
variable {t0 : ℕ}

instance (s : Sc3) [h : Good t0 s] : Good t0 s.rowU := ⟨h.out⟩
instance (s : Scd) [h : Good t0 s] : Good t0 s.rowU := ⟨h.out⟩
instance (k : Score) [h : Good t0 k] : Good t0 k.sc := ⟨h.out⟩
instance (d : Divide) [h : Good t0 d] : Good t0 d.scE := ⟨h.out.1⟩
instance (d : Divide) [h : Good t0 d] : Good t0 d.vpm := ⟨h.out.2.1⟩
instance (d : Divide) [h : Good t0 d] : Good t0 d.vpd := ⟨h.out.2.2⟩
instance (x : Attain) [h : Good t0 x] : Good t0 x.scF := ⟨h.out.1⟩
instance (x : Attain) [h : Good t0 x] : Good t0 x.scd := ⟨h.out.2.1⟩
instance (x : Attain) [h : Good t0 x] : Good t0 x.scH := ⟨h.out.2.2⟩
instance (h : Attention.Heard) [g : Good t0 h] : Good t0 h.g := ⟨g.out.1⟩
instance (h : Attention.Heard) [g : Good t0 h] : Good t0 h.scores := ⟨g.out.2.1⟩
instance (h : Attention.Heard) [g : Good t0 h] : Good t0 h.d := ⟨g.out.2.2.1⟩
instance (h : Attention.Heard) [g : Good t0 h] : Good t0 h.x := ⟨g.out.2.2.2⟩
instance (j : Joins) [g : Good t0 j] : Good t0 j.kf := ⟨g.out⟩
instance (kf : Array Aff) (n : Array ℕ) [g : Good t0 kf] : Good t0 (Joins.mk kf n) := ⟨g.out⟩
instance (j : Joins) (q : ℕ) (v : Aff) [Good t0 j] [Good t0 v] : Good t0 (j.set q v) :=
  ⟨(inferInstance : Good t0 (j.kf.setIfInBounds q v)).out⟩
instance (n : ℕ) : Good t0 (Joins.empty n) :=
  ⟨(inferInstance : Good t0 (Array.replicate n (Aff.ofConst zeroE))).out⟩

end

theorem fixedU_u3at (h : Attention.Heard) (t i : ℕ) : FixedU h.iU3 (u3at h t i) := by fixedu

macro_rules | `(tactic| fixedu_rule) => `(tactic| with_reducible exact fixedU_u3at _ _ _)

section
variable {t0 : ℕ}

instance good_remForm (d : Divide) : Good t0 (remForm d) := by fixedu
instance good_indexForm (d : Divide) (lt : ℕ) : Good t0 (indexForm d lt) := by fixedu
instance good_keyWL (d : Divide) : Good t0 (keyWL d) := by fixedu
instance good_keyIX (S : Shape) (d : Divide) : Good t0 (keyIX S d) := by fixedu
instance good_keyWH (d : Divide) : Good t0 (keyWH d) := by fixedu
instance good_joinR16 (S : Shape) (d : Divide) (j : Joins) [Good t0 j] :
    Good t0 (joinR16 S d j) := by fixedu

end

theorem fixedU_claim3 (h : Attention.Heard) [Good h.iU3 h] (j : Joins) [Good h.iU3 j] :
    FixedU h.iU3 (claim3 h j) := by fixedu
theorem fixedU_claim4 (h : Attention.Heard) [Good h.iU3 h] (j : Joins) [Good h.iU3 j] :
    FixedU h.iU3 (claim4 h j) := by fixedu
theorem fixedU_claim5 (h : Attention.Heard) [Good h.iU3 h] (j : Joins) [Good h.iU3 j] :
    FixedU h.iU3 (claim5 h j) := by fixedu
theorem fixedU_claim6 (h : Attention.Heard) [Good h.iU3 h] : FixedU h.iU3 (claim6 h) := by fixedu
theorem fixedU_claim7 (h : Attention.Heard) [Good h.iU3 h] : FixedU h.iU3 (claim7 h) := by fixedu
theorem fixedU_claim8 (h : Attention.Heard) [Good h.iU3 h] : FixedU h.iU3 (claim8 h) := by fixedu
theorem fixedU_allJoined (t0 : ℕ) (j : Joins) : FixedU t0 (allJoined j) := by fixedu
theorem fixedU_paddingLaidA (t0 : ℕ) (S : Shape) (g : Forest.Heard) :
    FixedU t0 (Attention.paddingLaid S g) := by fixedu

macro_rules | `(tactic| fixedu_rule) => `(tactic| with_reducible first
  | exact fixedU_claim3 _ _ | exact fixedU_claim4 _ _ | exact fixedU_claim5 _ _
  | exact fixedU_claim6 _ | exact fixedU_claim7 _ | exact fixedU_claim8 _
  | exact fixedU_allJoined _ _ | exact fixedU_paddingLaidA _ _ _
  | exact fixedU_objects _ | exact fixedU_join _ _
  | refine fixedU_planeLins _ _ _ _ ?_ ?_)

/-- **All claims of the attention sub-proof.** -/
theorem fixedU_claims (P : Plan) (h : Attention.Heard) [Good h.iU3 h] :
    FixedU h.iU3 (Attention.claims P h) := by fixedu

end Fo
