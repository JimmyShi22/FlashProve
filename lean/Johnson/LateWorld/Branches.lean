-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/Branches.lean: THE SESSION LEMMA AT THE LETTERS OF THE KEY's TEST AND OF A LINK:
the proofs of Spec.testBranch and Spec.linkBranch (Johnson/LateWorld/SpecBranches.lean). Theorems
with their proofs.

Lemmas of one step of a proof. This file states no goal of the release.

Each is the session lemma (session, Johnson/LateWorld/Session.lean) at its letters. It follows the
pattern of sess_branch (Johnson/LateWorld/Steps.lean). What is fed: the laws of the wire of the
external strings; that the positions read do not hang on nonces; that "stop" decides the honest
side's abort set; that the run values stand in the plain parts; and that the honest side's trees
over the external strings are the reduction's with the bodies put in (TabAgree): the same levels and
salts by the text of realTree, and at an external position the leaf that the committer lays holds
that position's symbol.

Main names (namespace OnBytes.LateWorld).
  dec_iff'     from "decide p = true", at whatever instance, to p and back.
  testBranch, linkBranch   THE THEOREMS.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateWorld.SpecBranches
import Johnson.LateWorld.Session

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.LateWorld
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.WrapLaws
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

theorem dec_iff' {p : Prop} {d : Decidable p} : @decide p d = true ↔ p := @decide_eq_true_iff p d

/-- **The key's test.** -/
theorem testBranch : Spec.testBranch := by
  intro I X lam L Bd aT aL W S cA r₀ a ok Gs δ i hP hi e t r sd co hco T
  have hext : a.Hs.T.ext (i, r, sd) = L.encodeIndex i r := hP.ext.T i r sd
  have hTab : TabAgree (batTC L aT) (wTC W) W.embE (a.Hs.T.ext (i, r, sd))
      (fun _ => realTree W a.b₀ (L.encodeIndex i r) t.tree) (fun _ => t.tree) := by
    rw [hext]
    refine ⟨fun _ => rfl, fun _ _ => rfl, fun p => ?_⟩
    show (committerLeafInput W a.b₀ (L.encodeIndex i r) (fun j => (t.tree.inp j).salt) (W.T.ext.leaf p)).body = _
    rw [(hP.wires.base.extT p).2]
    exact dif_pos p.isLt
  have h := session Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none) []
    (cmsTA cA t.tree.root (L.recOf i r sd).2) (L.recOf i r sd)
    (fun _ => realTree W a.b₀ (L.encodeIndex i r) t.tree) (fun _ => t.tree) a.side.capT W.embE
    a.Hs.T (i, r, sd) (a.side.st.stopT i r sd)
    (blank a.b₀ W.depthReqT) (fun κ => a.side.dressT (a.side.rvT κ) co) (coVT a co)
    hP.wires.T.ext (hP.freeT (L.recOf i r sd)) (fun _ => dec_iff')
    (fun κ ρ hρ => congrArg (fun v => a.side.dressT v co) (hP.runVals.T i r sd κ ρ hi hρ))
    (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ => (List.length_replicate ..).trans hco.symm) hTab T
  rw [hext] at h
  exact h.symm

/-- **A link.** -/
theorem linkBranch : Spec.linkBranch := by
  intro I X lam L Bd aT aL W S cA r₀ a ok Gs δ i hP hi e t₁ t₂ u₁ u₂ co hco T
  have hext : a.Hs.Lk.ext (i, u₁, u₂) = (L.encodeIndex i u₁.1, L.encodeIndex i u₂.1) :=
    hP.ext.Lk i u₁.1 u₁.2 u₂.1 u₂.2
  have hTab : TabAgree (batLC L aL) (wLC W) W.embE (a.Hs.Lk.ext (i, u₁, u₂))
      (fun k => if k = 0 then realTree W a.b₀ (L.encodeIndex i u₁.1) t₁.tree
        else realTree W a.b₀ (L.encodeIndex i u₂.1) t₂.tree)
      (fun k => if k = 0 then t₁.tree else t₂.tree) := by
    rw [hext]
    refine ⟨fun k => ?_, fun k j => ?_, fun p => ?_⟩
    · by_cases hk : k = 0
      · simp only [if_pos hk]
        rfl
      · simp only [if_neg hk]
        rfl
    · by_cases hk : k = 0
      · simp only [if_pos hk]
        rfl
      · simp only [if_neg hk]
        rfl
    · cases p with
      | inl p =>
        show ((if W.Lk.ext.which (.inl p) = 0 then realTree W a.b₀ (L.encodeIndex i u₁.1) t₁.tree
          else realTree W a.b₀ (L.encodeIndex i u₂.1) t₂.tree).inp (W.Lk.ext.leaf (.inl p))).body = _
        rw [(hP.wires.base.extL.1 p).1, (hP.wires.base.extL.1 p).2, if_pos rfl]
        exact dif_pos p.isLt
      | inr p =>
        show ((if W.Lk.ext.which (.inr p) = 0 then realTree W a.b₀ (L.encodeIndex i u₁.1) t₁.tree
          else realTree W a.b₀ (L.encodeIndex i u₂.1) t₂.tree).inp (W.Lk.ext.leaf (.inr p))).body = _
        rw [(hP.wires.base.extL.2 p).1, (hP.wires.base.extL.2 p).2, if_neg (by decide)]
        exact dif_pos p.isLt
  have h := session Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none) []
    (cmsLA cA t₁.tree.root t₂.tree.root (L.recOf i u₁.1 u₁.2).2 (L.recOf i u₂.1 u₂.2).2)
    (L.recOf i u₁.1 u₁.2, L.recOf i u₂.1 u₂.2)
    (fun k => if k = 0 then realTree W a.b₀ (L.encodeIndex i u₁.1) t₁.tree
      else realTree W a.b₀ (L.encodeIndex i u₂.1) t₂.tree)
    (fun k => if k = 0 then t₁.tree else t₂.tree) a.side.capL W.embE
    a.Hs.Lk (i, u₁, u₂) (a.side.st.stopL i u₁ u₂)
    (blank a.b₀ W.depthReqL) (fun κ => a.side.dressL (a.side.rvL κ) co) (coVL a co)
    hP.wires.Lk.ext (hP.freeL (L.recOf i u₁.1 u₁.2, L.recOf i u₂.1 u₂.2)) (fun _ => dec_iff')
    (fun κ ρ hρ => congrArg (fun v => a.side.dressL v co) (hP.runVals.Lk i u₁ u₂ κ ρ hi hρ))
    (fun _ => ⟨rfl, rfl, rfl⟩) (fun _ => (List.length_replicate ..).trans hco.symm) hTab T
  rw [hext] at h
  exact h.symm

end OnBytes.LateWorld

#print axioms OnBytes.LateWorld.testBranch
#print axioms OnBytes.LateWorld.linkBranch
