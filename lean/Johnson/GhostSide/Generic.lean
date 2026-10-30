-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/GhostSide/Generic.lean: proofs of the statements of Johnson/GhostSide/Defs.lean, and the
rules by which "routed" is shown of a sequence. This file states no goal of the release. A DEVICE OF
A PROOF: the names fbw t k, the exchange of queries and "routed" stand in no statement on the
scheme.

The proofs follow Compile/Batch/Ghost.lean and the first lemma of Compile/Batch/GhostRouted.lean
closely: these have the like for the compiler's first form.

  ghostPerm, realQ_via, routedErase   the three statements.
  Routed.bind, RoutedT.bind           a routed program followed by routed programs is routed.
  plainOf_via      a routed token program as an ordinary oracle algorithm (plainOf,
                   Johnson/TokenSide/Erased.lean) is what erase makes of it, translated by ghost W.
Limits: those of Compile/Batch/SpecGhost.lean. Nothing is said here on any program.
Terms: lean/GLOSSARY.md.

-/
import Johnson.GhostSide.Defs
import Johnson.TokenSide.Erased
import Compile.Batch.Ghost

set_option autoImplicit false

noncomputable section

namespace OnBytes.GhostSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch OnBytes.TokenSide Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} (W : QueryLayout lam L)

theorem ghost_fb_zero {t : Tag} {q : FbIn lam L t} (h : cls W t q = 0) :
    ghost W (.fb t) q = ⟨.fb t, q, id⟩ := by
  show (match cls W t q with
      | 0 =>
        (⟨.fb t, q, id⟩ : Σ o' : OracleName, domOf lam L o' × (rngOf lam W.K o' → rngOf lam W.K (.fb t)))
      | k + 1 => ⟨.fbw t k, q, id⟩) = _
  rw [h]
  rfl

theorem ghost_fb_succ {t : Tag} {q : FbIn lam L t} {k : ℕ} (h : cls W t q = k + 1) :
    ghost W (.fb t) q = ⟨.fbw t k, q, id⟩ := by
  show (match cls W t q with
      | 0 =>
        (⟨.fb t, q, id⟩ : Σ o' : OracleName, domOf lam L o' × (rngOf lam W.K o' → rngOf lam W.K (.fb t)))
      | k + 1 => ⟨.fbw t k, q, id⟩) = _
  rw [h]
  rfl

theorem ghost_fbw_pos {t : Tag} {q : FbIn lam L t} {k : ℕ} (h : cls W t q = k + 1) :
    ghost W (.fbw t k) q = ⟨.fb t, q, id⟩ := if_pos h

theorem ghost_fbw_neg {t : Tag} {q : FbIn lam L t} {k : ℕ} (h : cls W t q ≠ k + 1) :
    ghost W (.fbw t k) q = ⟨.fbw t k, q, id⟩ := if_neg h

theorem ghost_inv : QMap.Inv (ghost W) (ghost W) := by
  intro o q
  cases o with
  | fb t =>
      rcases h : cls W t q with _ | k
      · exact QMap.inv_at (ghost_fb_zero W h) (ghost_fb_zero W h) (fun _ => rfl) fun _ => rfl
      · exact QMap.inv_at (ghost_fb_succ W h) (ghost_fbw_pos W h) (fun _ => rfl) fun _ => rfl
  | fbw t k =>
      by_cases h : cls W t q = k + 1
      · exact QMap.inv_at (ghost_fbw_pos W h) (ghost_fb_succ W h) (fun _ => rfl) fun _ => rfl
      · exact QMap.inv_at (ghost_fbw_neg W h) (ghost_fbw_neg W h) (fun _ => rfl) fun _ => rfl
  | leaf => exact ⟨id, rfl, fun _ => rfl, fun _ => rfl⟩
  | node => exact ⟨id, rfl, fun _ => rfl, fun _ => rfl⟩
  | rleaf => exact ⟨id, rfl, fun _ => rfl, fun _ => rfl⟩
  | rnode => exact ⟨id, rfl, fun _ => rfl, fun _ => rfl⟩
  | g t => exact ⟨id, rfl, fun _ => rfl, fun _ => rfl⟩
  | ann => exact ⟨id, rfl, fun _ => rfl, fun _ => rfl⟩
  | other => exact ⟨id, rfl, fun _ => rfl, fun _ => rfl⟩

theorem ghostPerm : Spec.ghostPerm := fun _ _ _ _ W => ⟨ghost_inv W, ghost_inv W⟩

theorem realQ_via : Spec.realQ_via := by
  intro I X lam L W α c
  induction c with
  | pure a => intro _; rfl
  | sample n k ih => intro h; exact congrArg (OComp.sample n) (funext fun r => ih r (h r))
  | query o q k ih =>
      intro h
      cases o with
      | fb t =>
        exact (congrArg (OComp.query (S := typedOracleFamily lam W.K L) (.fb t) q)
            (funext fun r => ih r (h.2 r))).trans
          (OComp.via_query_of (ghost_fb_zero W h.1) k).symm
      | fbw t j =>
        exact (congrArg (OComp.query (S := typedOracleFamily lam W.K L) (.fb t) q)
            (funext fun r => ih r (h.2 r))).trans
          (OComp.via_query_of (ghost_fbw_pos W h.1) k).symm
      | leaf =>
        exact congrArg (OComp.query (S := typedOracleFamily lam W.K L) .leaf q) (funext fun r => ih r (h r))
      | node =>
        exact congrArg (OComp.query (S := typedOracleFamily lam W.K L) .node q) (funext fun r => ih r (h r))
      | rleaf =>
        exact congrArg (OComp.query (S := typedOracleFamily lam W.K L) .rleaf q) (funext fun r => ih r (h r))
      | rnode =>
        exact congrArg (OComp.query (S := typedOracleFamily lam W.K L) .rnode q) (funext fun r => ih r (h r))
      | g t =>
        exact congrArg (OComp.query (S := typedOracleFamily lam W.K L) (.g t) q) (funext fun r => ih r (h r))
      | ann =>
        exact congrArg (OComp.query (S := typedOracleFamily lam W.K L) .ann q) (funext fun r => ih r (h r))
      | other =>
        exact congrArg (OComp.query (S := typedOracleFamily lam W.K L) .other q) (funext fun r => ih r (h r))

variable {W}

/-- a routed algorithm followed by routed algorithms is routed -/
theorem Routed.bind {α β : Type} :
    ∀ {c : TypedOracleComputation lam W.K L α} {g : α → TypedOracleComputation lam W.K L β},
      Routed W c → (∀ a, Routed W (g a)) → Routed W (c.bind g)
  | .pure a, _, _, hg => hg a
  | .sample _ k, _, h, hg => fun r => Routed.bind (c := k r) (h r) hg
  | .query (.fb _) _ k, _, h, hg => ⟨h.1, fun r => Routed.bind (c := k r) (h.2 r) hg⟩
  | .query (.fbw _ _) _ k, _, h, hg => ⟨h.1, fun r => Routed.bind (c := k r) (h.2 r) hg⟩
  | .query .leaf _ k, _, h, hg => fun r => Routed.bind (c := k r) (h r) hg
  | .query .node _ k, _, h, hg => fun r => Routed.bind (c := k r) (h r) hg
  | .query .rleaf _ k, _, h, hg => fun r => Routed.bind (c := k r) (h r) hg
  | .query .rnode _ k, _, h, hg => fun r => Routed.bind (c := k r) (h r) hg
  | .query (.g _) _ k, _, h, hg => fun r => Routed.bind (c := k r) (h r) hg
  | .query .ann _ k, _, h, hg => fun r => Routed.bind (c := k r) (h r) hg
  | .query .other _ k, _, h, hg => fun r => Routed.bind (c := k r) (h r) hg

theorem routedErase : Spec.routedErase := by
  intro I X lam L W α c
  induction c with
  | pure a => intro _ _; trivial
  | sample n k ih => intro vs h r; exact ih r vs (h r)
  | plain o q k ih =>
      intro vs h
      cases o with
      | fb t => exact ⟨h.1, fun r => ih r vs (h.2 r)⟩
      | fbw t j => exact ⟨h.1, fun r => ih r vs (h.2 r)⟩
      | leaf => exact fun r => ih r vs (h r)
      | node => exact fun r => ih r vs (h r)
      | rleaf => exact fun r => ih r vs (h r)
      | rnode => exact fun r => ih r vs (h r)
      | g t => exact fun r => ih r vs (h r)
      | ann => exact fun r => ih r vs (h r)
      | other => exact fun r => ih r vs (h r)
  | fresh ℓ k ih => intro vs h r; exact ih _ _ (h _)
  | marked o t us pt inj k ih =>
      intro vs h
      cases o with
      | fb t' => exact ⟨h.1 _ _, fun r => ih _ _ _ (h.2 _ _)⟩
      | fbw t' j => exact ⟨h.1 _ _, fun r => ih _ _ _ (h.2 _ _)⟩
      | leaf => exact fun r => ih _ _ _ (h _ _)
      | node => exact fun r => ih _ _ _ (h _ _)
      | rleaf => exact fun r => ih _ _ _ (h _ _)
      | rnode => exact fun r => ih _ _ _ (h _ _)
      | g t' => exact fun r => ih _ _ _ (h _ _)
      | ann => exact fun r => ih _ _ _ (h _ _)
      | other => exact fun r => ih _ _ _ (h _ _)
  | reveal ts k ih => intro vs h; exact ih _ vs (h _)

/-- a routed program followed by routed programs is routed -/
theorem RoutedT.bind {α β : Type} {c : StT lam W.K L α} {g : α → StT lam W.K L β}
    (h : RoutedT W c) (hg : ∀ a, RoutedT W (g a)) : RoutedT W (c.bind g) := by
  induction c with
  | pure a => exact hg a
  | sample n k ih => exact fun r => ih r (h r)
  | plain o q k ih =>
      cases o with
      | fb t => exact ⟨h.1, fun r => ih r (h.2 r)⟩
      | fbw t j => exact ⟨h.1, fun r => ih r (h.2 r)⟩
      | leaf => exact fun r => ih r (h r)
      | node => exact fun r => ih r (h r)
      | rleaf => exact fun r => ih r (h r)
      | rnode => exact fun r => ih r (h r)
      | g t => exact fun r => ih r (h r)
      | ann => exact fun r => ih r (h r)
      | other => exact fun r => ih r (h r)
  | fresh ℓ k ih => exact fun u => ih u (h u)
  | marked o t us pt inj k ih =>
      cases o with
      | fb t' => exact ⟨h.1, fun v u => ih v u (h.2 v u)⟩
      | fbw t' j => exact ⟨h.1, fun v u => ih v u (h.2 v u)⟩
      | leaf => exact fun v u => ih v u (h v u)
      | node => exact fun v u => ih v u (h v u)
      | rleaf => exact fun v u => ih v u (h v u)
      | rnode => exact fun v u => ih v u (h v u)
      | g t' => exact fun v u => ih v u (h v u)
      | ann => exact fun v u => ih v u (h v u)
      | other => exact fun v u => ih v u (h v u)
  | reveal ts k ih => exact fun vs => ih vs (h vs)

/-- A routed token program as an ordinary oracle algorithm: what erase makes of it, translated by
the exchange of queries. -/
theorem plainOf_via {α : Type} {c : StT lam W.K L α} (h : RoutedT W c) (vs : List Bits) :
    plainOf c vs = (erase c vs).via (ghost W) :=
  realQ_via I X lam L W _ _ (routedErase I X lam L W α c vs h)

end OnBytes.GhostSide

#print axioms OnBytes.GhostSide.ghostPerm
#print axioms OnBytes.GhostSide.realQ_via
#print axioms OnBytes.GhostSide.routedErase
#print axioms OnBytes.GhostSide.plainOf_via
