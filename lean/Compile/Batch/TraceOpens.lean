-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/TraceOpens.lean: the honest committer's trace contains an opening of every leaf of the
encoded index, under every family of oracle functions and for all coins.
`TraceOpens W i cm tr`: some string y decodes to the index i, and every symbol of y opens its leaf
under the root cm by entries of tr. It names no oracle function and no hash event. It is monotone in
the trace (`TraceOpens.mono`).
`TraceOpens.dec` (needs W.OKG): outside the hash event on tr, the extractor's string under cm
decodes to i. `traceOpens_of_first`, `traceOpens_C` (need L.Wired and W.OKG): every outcome of a
typed committer that first builds the tree under the root in its key, and so of the committer `C`
(Compile/Batch/Star.lean), has the property. That is a fact on the trace, not that an extractor is
correct.
Not stated: anything about another committer.
-/
import Compile.Batch.ExtractionSeed

set_option autoImplicit false

noncomputable section

namespace Compile.Batch
open Iop Rom Prob Merkle Compile.Extr Compile.Batch.Cmpl Compile.Batch.Extr

namespace Extr

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {f : Fam (spec lam K L)}
  {tr : Trace (spec lam K L)}

/-- Every leaf of a tree whose queries are in the trace opens under the root within the trace. No
hash event is excluded. -/
theorem opensIn_of_tree {sMT : ℕ} {vs : List Bits} {t : TreeH lam} {d : ℕ}
    {leaf : ℕ → Body L × Bool} (hok : TreeOK f sMT vs t d leaf) (hin : TreeIn f tr vs t d leaf)
    {j : ℕ} (hj : j < 2 ^ d) :
    (pairM lam K L).OpensIn tr (posOf d j) ⟨(leaf j).1, saltVal vs (t.salts.getD j none)⟩
      t.root := by
  have hcl := climbsIn_pathOf (pairM lam K L) (nodeFB f) d _ j hin.2 (by simp) hj
  rw [← hok.2.2.2] at hcl
  have hget : (((List.range (2 ^ d)).map fun j =>
      leafFB f ⟨(leaf j).1, saltVal vs (t.salts.getD j none)⟩).getD j default)
      = leafFB f ⟨(leaf j).1, saltVal vs (t.salts.getD j none)⟩ := by
    simp [List.getD_eq_getElem?_getD, hj]
  rw [hget] at hcl
  exact opensIn_of_climbsIn (pairM lam K L) (leaf_recorded_iff.2 (hin.1 j hj)) d _ _
    (by rw [hok.2.2.2]; exact length_pathOf_levelsF _ _ _ _) hcl

end Extr

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- The trace holds an opening, under the root cm, of every leaf of a string that decodes to i. -/
def TraceOpens (W : QueryLayout lam L) (i : I) (cm : Dig lam) (tr : Tc W) : Prop :=
  ∃ y : Fin L.wordLength → L.Symbol, L.decodeIndex y = some i ∧ ∀ q : Fin L.wordLength, ∃ s,
    (pairM lam W.K L).OpensIn tr (posOf W.depth q.val) ⟨some (.inl (y q)), s⟩ cm

/-- The property passes to every trace that contains the entries of tr. -/
theorem TraceOpens.mono {W : QueryLayout lam L} {i : I} {cm : Dig lam} {tr tr' : Tc W} (hs : tr ⊆ tr')
    (h : TraceOpens W i cm tr) : TraceOpens W i cm tr' := by
  obtain ⟨y, hy, ho⟩ := h
  refine ⟨y, hy, fun q => ?_⟩
  obtain ⟨s, h1⟩ := ho q
  exact ⟨s, Merkle.OraclePair.OpensIn.mono _ hs h1⟩

/-- Outside the hash event on the trace, the string that the extractor reads under cm decodes
to i. -/
theorem TraceOpens.dec {W : QueryLayout lam L} {i : I} {cm : Dig lam} {tr : Tc W} (hW : W.OKG)
    (hEM : ¬ EM tr) (h : TraceOpens W i cm tr) : L.decodeIndex (extEnc W tr cm) = some i := by
  obtain ⟨y, hy, ho⟩ := h
  rw [extEnc_eqG (y := y) hW fun q => ?_, hy]
  obtain ⟨s, h1⟩ := ho q
  exact ⟨s, (pairM lam W.K L).preimage_of_opensIn hEM h1⟩

/-- Any committer that first builds the tree under the root in its key: every outcome, under every
family of oracle functions, has the property. -/
theorem traceOpens_of_first (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (hwd : L.Wired)
    (hW : W.OKG) (i : I)
    {β γ : Type} (X0 : TypedOracleComputation lam W.K L β) (nd : β → Node lam L × List Bits)
    (Rest : β → TypedOracleComputation lam W.K L γ) (cmOf : γ → Dig lam)
    (h1 : ∀ (f : Fam (spec lam W.K L)) (a : β × Tc W), a ∈ Outs f X0.withTrace →
      nd a.1 ∈ OutsIn f a.2 (erase (nodeP' W WP p i) []))
    (h2 : ∀ (f : Fam (spec lam W.K L)) (a : β), ∀ b ∈ Outs f (Rest a),
      cmOf b = (nd a).1.tree.root)
    (f : Fam (spec lam W.K L)) (o : γ × Tc W) (ho : o ∈ Outs f (X0.bind Rest).withTrace) :
    TraceOpens W i (cmOf o.1) o.2 := by
  rw [withTrace_bind] at ho
  obtain ⟨a, ha, hb'⟩ := mem_outs_bind.1 ho
  obtain ⟨b, hb, hob⟩ := mem_outs_bind.1 hb'
  obtain rfl := mem_outs_pure.1 hob
  obtain ⟨hok, hin⟩ := triI_nodeP' WP p i [] (nd a.1) (h1 f a ha)
  have hcm : cmOf b.1 = (nd a.1).1.tree.root :=
    h2 f a.1 b.1 (outs_of_outsIn (outsIn_of_withTrace hb))
  refine ⟨L.encodeIndex i (nd a.1).1.r, hwd.dec_enc _ _, fun q => ?_⟩
  have h3 := opensIn_of_tree hok hin (j := q.val) (lt_of_lt_of_le q.isLt hW.fits)
  rw [Cmpl.encLeaf_val] at h3
  show ∃ s, (pairM lam W.K L).OpensIn (a.2 ++ b.2) (posOf W.depth q.val) _ (cmOf b.1)
  rw [hcm]
  exact ⟨_, Merkle.OraclePair.OpensIn.mono _ (List.subset_append_left _ _) h3⟩

/-- Every outcome of the typed committer `C`, under every family of oracle functions, has the
property under the root in its key. -/
theorem traceOpens_C (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (hwd : L.Wired) (hW : W.OKG) (i
          : I)
    (f : Fam (spec lam W.K L)) :
    ∀ o ∈ Outs f (C W WP p i).withTrace, TraceOpens W i o.1.1.cm o.2 := by
  intro o ho
  rw [Extr.C_eq] at ho
  exact traceOpens_of_first W WP p hwd hW i (erase (nodeP' W WP p i) []) id
    (fun x => (eraseR (Extr.restC W WP p i x.1) x.2).bind fun o =>
      OComp.pure (o.1.1, (o.1.2, o.2)))
    (fun o => o.1.cm) (fun _ _ ha => outsIn_of_withTrace ha)
    (fun f a b hb => by
      obtain ⟨z, hz, hbz⟩ := mem_outs_bind.1 hb
      rw [mem_outs_pure.1 hbz]
      exact Extr.tri_restC W WP p (realF f) i a.1 a.2 z (outs_realQ hz)) f o ho

end Compile.Batch
