-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/U3Fit/ValsSorts.lean

Theorems; no definition. "valsAt" (Johnson/HonestTrace/U3Rows.lean) at a layers' and at an attention
segment is that sort's maker: the sisters of "valsAt_head"
(Johnson/HonestTrace/U3Fit/ValsGeneral.lean). So whoever shows that "layersVals" or "attVals"
returns at a group has shown that "valsAt" returns at the group's segment. Public data alone. A
SegVals is carried whole; its field vec, a function that awaits the trace's cells, is applied
nowhere here.

Main theorems:
* "valsAt_layers", "valsAt_att" (no head): from the return of "spotsOf", the segment's built data,
  its sort (0 or 1), and that the built data's group is the segment's.
* "valsAt_layers_at_head", "valsAt_att_at_head": under the head, at g below 12 and at every cov:
  "valsAt Zp G cov (2 * g) = layersVals Zp G spotsWritten (2 * g) g" and "valsAt Zp G cov (2 * g +
  1) = attVals Zp G spotsWritten (2 * g + 1) g".
* "returns_of_makers": under the head, where the two makers return at each group, "valsAt" returns
  at each segment below 24, at every cov.

Limits. The head (the terms: Johnson/HonestTrace/U3Fit/SeatsAtHead.lean) is a premise: the full size
and the format's second hash function alone. No closed fact and no raised option in this file.
Not claimed: that a maker returns: the premise of "returns_of_makers" on "attVals" is shown by no
file of this folder. No property of a release, of a verifier or of a prover is claimed.
-/
import Johnson.HonestTrace.U3Fit.SeatsAtHead
import Johnson.HonestTrace.U3Fit.MatsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace.U3.Fit

open OnBytes OnBytes.Model
open ProofFile (Pub Ground Spot spotsOf)
open ProofFile.Honest.K3 (linkG linkA stepOf)
open Johnson.AtFull.Desc (spotsWritten)
open P5J (AtMgA TS)

/-- **GENERAL: at a segment whose built data is of the sort 0, "valsAt" is the layers' maker.** -/
theorem valsAt_layers {Z : Pub} {G : Ground} {sps : List Spot} {seg : Nat} {Y : Stages.LinkH}
    (hs : spotsOf Z.cuts = some sps) (hb : G.built[seg]? = some Y) (hk : Y.kind = 0)
    (hl : linkG G.W Y.g = seg) (cov : Head.Covered) :
    valsAt Z G cov seg = layersVals Z G sps seg Y.g := by
  unfold valsAt
  rw [hs, hb]
  simp only [have_, bind, Except.bind, ask, hk, hl]
  rw [beq_self_eq_true seg]
  rfl

/-- **GENERAL: at a segment whose built data is of the sort 1, "valsAt" is attention's maker.** -/
theorem valsAt_att {Z : Pub} {G : Ground} {sps : List Spot} {seg : Nat} {Y : Stages.LinkH}
    (hs : spotsOf Z.cuts = some sps) (hb : G.built[seg]? = some Y) (hk : Y.kind = 1)
    (hl : linkA G.W Y.g = seg) (cov : Head.Covered) :
    valsAt Z G cov seg = attVals Z G sps seg Y.g := by
  unfold valsAt
  rw [hs, hb]
  simp only [have_, bind, Except.bind, ask, hk, hl]
  rw [beq_self_eq_true seg]
  rfl

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **UNDER THE HEAD, at the segment of group g of layers.** -/
theorem valsAt_layers_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {g : Nat} (hg : g < 12)
    (cov : Head.Covered) :
    valsAt Zp G cov (2 * g) = layersVals Zp G spotsWritten (2 * g) g := by
  obtain ⟨l, l', e, k, q, -, -, -, -, -⟩ := (IM.ground_named h.scope h.reads h.laid.pub hG).1 g hg
  have s := valsAt_layers (spots_at_head h) e k (by
    unfold linkG
    rw [step_at_head h hG, q]) cov
  rw [q] at s
  exact s

/-- **UNDER THE HEAD, at the attention segment of group g.** -/
theorem valsAt_att_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {g : Nat} (hg : g < 12)
    (cov : Head.Covered) :
    valsAt Zp G cov (2 * g + 1) = attVals Zp G spotsWritten (2 * g + 1) g := by
  obtain ⟨l, l', -, -, -, -, e, k, q, -⟩ := (IM.ground_named h.scope h.reads h.laid.pub hG).1 g hg
  have s := valsAt_att (spots_at_head h) e k (by
    unfold linkA
    rw [step_at_head h hG, q]) cov
  rw [q] at s
  exact s

/-- **UNDER THE HEAD: where the two makers return at each group, "valsAt" returns at each segment below
24, at every cov.** -/
theorem returns_of_makers (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hL : ∀ g < 12, ∃ V, layersVals Zp G spotsWritten (2 * g) g = .ok V)
    (hA : ∀ g < 12, ∃ V, attVals Zp G spotsWritten (2 * g + 1) g = .ok V) :
    ∀ cov, ∀ l < 24, ∃ V, valsAt Zp G cov l = .ok V := by
  intro cov l hl
  by_cases e : l % 2 = 0
  · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g := ⟨l / 2, by omega⟩
    rw [valsAt_layers_at_head h hG (by omega) cov]
    exact hL g (by omega)
  · obtain ⟨g, rfl⟩ : ∃ g, l = 2 * g + 1 := ⟨l / 2, by omega⟩
    rw [valsAt_att_at_head h hG (by omega) cov]
    exact hA g (by omega)

end OnBytes.HonestTrace.U3.Fit

-- Lean's own words on each theorem of this file: its statement, and the axioms that it rests on: each line
-- «depends on axioms» should name no more than propext, Classical.choice and Quot.sound.
#check @OnBytes.HonestTrace.U3.Fit.valsAt_layers
#check @OnBytes.HonestTrace.U3.Fit.valsAt_att
#check @OnBytes.HonestTrace.U3.Fit.valsAt_layers_at_head
#check @OnBytes.HonestTrace.U3.Fit.valsAt_att_at_head
#check @OnBytes.HonestTrace.U3.Fit.returns_of_makers
#print axioms OnBytes.HonestTrace.U3.Fit.valsAt_layers
#print axioms OnBytes.HonestTrace.U3.Fit.valsAt_att
#print axioms OnBytes.HonestTrace.U3.Fit.valsAt_layers_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.valsAt_att_at_head
#print axioms OnBytes.HonestTrace.U3.Fit.returns_of_makers
