-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/StrictLinkRdLaws.lean: the lists of read leaves that rdOfR (StrictLinkRd.lean) makes of a
set R of positions are the lists that the listed strict verifier's equation asks for (LeavesOK,
OnBytes/TypedOracleCompiler/Compile/Batch/ListedForests.lean): tree by tree, the leaves whose positions are read, rising.
General in the skeleton. Premises: the four laws on how a wire numbers positions (PlaceOKS,
OnBytes/TypedOracleCompiler/Run/LaxPlaces.lean), and that isRead is membership in R.
Two theorems: leavesT_places (one component of one round, over placesAt_eq) · leavesOK_rdOfR.
Nothing on soundness. EVERY PROOF IS A TRY until Lean has spoken.
(Where this and lean/THEOREM.md differ, the page holds.)

-/
import Johnson.RunOne.StrictLinkRd
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedForests

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Thin
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.Thin

/-- One component of one round: from tree number k on, the lists are the right ones. -/
theorem leavesT_places {lam K : ℕ} {r : RS} {a : RAnn r.up} (w : WireRB lam K r.up a) (b : Bool)
    (posAt : ℕ → ℕ → Option r.Pos)
    (hat : ∀ k j p, posAt k j = some p → a.own p = b ∧ w.tree p = k ∧ w.place p = j)
    (hback : ∀ p, a.own p = b → posAt (w.tree p) (w.place p) = some p)
    (R : Finset r.Pos) (isRead : r.Pos → Bool) (hR : ∀ p, isRead p = true ↔ p ∈ R) :
    ∀ (ds : List ℕ) (k : ℕ),
      LeavesT (r := r.up) posAt isRead k ds ((ds.zipIdx k).map fun d => placesAt w b R d.2 d.1)
  | [], _ => trivial
  | d :: ds, k => by
      classical
      refine ⟨?_, leavesT_places w b posAt hat hback R isRead hR ds (k + 1)⟩
      show placesAt w b R k d = _
      rw [placesAt_eq w b posAt hat hback R k d]
      refine List.filter_congr fun j _ => ?_
      unfold keepP readAt
      cases posAt k j with
      | none => rfl
      | some p =>
        show decide (p ∈ R) = isRead p
        cases h : isRead p with
        | true => exact decide_eq_true ((hR p).1 h)
        | false =>
          refine decide_eq_false fun hm => ?_
          rw [(hR p).2 hm] at h
          cases h

/-- **The lists of rdOfR are the right ones**, at every skeleton whose wire numbers its positions lawfully. -/
theorem leavesOK_rdOfR {lam K : ℕ} :
    ∀ (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A), PlaceOKS S A W →
      ∀ (R : Finset (OPos (up S))) (isRead : OPos (up S) → Bool),
        (∀ p, isRead p = true ↔ p ∈ R) → LeavesOK (up S) A W isRead (rdOfR S A W R)
  | [], _, _, _, _, _, _ => trivial
  | r :: S, (_, A), (w, W), hW, R, isRead, hR =>
      ⟨leavesT_places w false w.posAt0 hW.1.at0 hW.1.back0
          (headR (α := r.Pos) (β := OPos (up S)) R) (fun p => isRead (.inl p))
          (fun p => (hR (.inl p)).trans (mem_headR R p).symm) w.depth0 0,
        leavesT_places w true w.posAtJ hW.1.atJ hW.1.backJ
          (headR (α := r.Pos) (β := OPos (up S)) R) (fun p => isRead (.inl p))
          (fun p => (hR (.inl p)).trans (mem_headR R p).symm) w.depthJ 0,
        leavesOK_rdOfR S A W hW.2 (tailR (α := r.Pos) (β := OPos (up S)) R)
          (fun p => isRead (.inr p)) (fun p => (hR (.inr p)).trans (mem_tailR R p).symm)⟩

end TypedOracleCompiler.Run.Thin

#print axioms TypedOracleCompiler.Run.Thin.leavesOK_rdOfR
