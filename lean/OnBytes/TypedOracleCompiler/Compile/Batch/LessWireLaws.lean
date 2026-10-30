-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/LessWireLaws.lean: the verifier over the lesser wire records
(LessWire.lean) is the verifier along the lists (ListedVerifier.lean), at what is left of the full
records. Equations.

Main statement. verifyBSX_eq: for every list of full wire records sh, and all other arguments,
verifyBSX .. (lessS _ _ sh) .. = verifyBSL .. sh .., as trees of queries. There is no premise: none
on the argument string, none on the lists own, listed, mkRd, mkRdE. Each step says the same of one
function: chainBX_eq, mkTrX_eq, strictSBX_eq, forestsBX_eq, then strictBBX_eq, forestsOfX_eq,
afterFX_eq, afterBOX_eq. lessS_app: what is left of two lists of records laid behind each other.

Limits. That verifyBSL is verifyOneProtocol has premises of its own (ListedVerifierLaws.lean, verifyBSL_eq):
they are not touched here. Nothing on time or memory. Nothing on soundness.
The program does not import this file.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.LessWire
import OnBytes.TypedOracleCompiler.Joined.Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

theorem chainBX_eq (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits)
    (rtreq : Dig lam) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
      (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam)
      (rts : List (Dig lam)) (pls : Plains s),
      chainBX t cms x salt rtreq s A (lessS s A W) embP i ph rts pls =
        recomputeChain t cms x salt rtreq s A W embP i ph rts pls
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls) => by
      have ih := chainBX_eq t cms x salt rtreq s A W
      simp only [chainBX, recomputeChain, lessS, lessR, ih]
      all_goals rfl

theorem mkTrX_eq :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (rts : RootsOfChain lam s) (pls : Plains s)
      (ρ : Rho s) (f : (p : OPos s) → Option (Opening lam (OSym s p))),
      mkTrX s A (lessS s A W) rts pls ρ f = mkTr s A W rts pls ρ f
  | [], _, _, _, _, _, _ => rfl
  | _ :: s, (_, A), (_, W), (_, rts), (_, pls), (_, ρ), f =>
      Prod.ext rfl (Prod.ext rfl (mkTrX_eq s A W rts pls ρ fun p => f (.inr p)))

theorem strictSBX_eq (sMT : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (rts : RootsOfChain lam s)
      (f : (p : OPos s) → Option (Opening lam (OSym s p))) (own rd : Leaves),
      strictSBX sMT s (lessS s A W) rts f own rd = strictSBL sMT s A W rts f own rd
  | [], _, _, _, _, _, _ => rfl
  | _ :: s, (_, A), (w, W), (rt, rts), f, own, rd =>
      congrArg (fun b =>
        strictTreesL sMT w.posAt0 w.depth0 (rt.1.getD []) (fun p => f (.inl p))
          (rd.headD ([], [])).1 (own.headD ([], [])).1 &&
        strictTreesL sMT w.posAtJ w.depthJ (rt.2.getD []) (fun p => f (.inl p))
          (rd.headD ([], [])).2 (own.headD ([], [])).2 && b)
        (strictSBX_eq sMT s A W rts (fun p => f (.inr p)) own.tail rd.tail)

theorem forestsBX_eq :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (emb : (p : OPos s) → OSym s p → Body L)
      (rts : RootsOfChain lam s) (f : (p : OPos s) → Option (Opening lam (OSym s p))) (rd : Leaves),
      forestsBX s (lessS s A W) emb rts f rd = forestsBL s A W emb rts f rd
  | [], _, _, _, _, _, _ => rfl
  | _ :: s, (_, A), (w, W), emb, (rt, rts), f, rd => by
      have ih := forestsBX_eq s A W (fun p => emb (.inr p)) rts (fun p => f (.inr p)) rd.tail
      simp only [forestsBX, forestsBL, lessS, lessR, ih]
      all_goals rfl

/-- What is left of two lists of records laid behind each other. -/
theorem lessS_app :
    ∀ {s u : Shape} {A : RoundSplits s} {B : RoundSplits u} (W : RoundsQueryLayout lam K s A) (V : RoundsQueryLayout lam K u B),
      lessS (s ++ u) (RoundSplits.app A B) (TypedOracleCompiler.Joined.WireSB.app W V) =
        WireSL.app (lessS s A W) (lessS u B V)
  | [], _, _, _, _, _ => rfl
  | _ :: _, _, (_, _), _, (w, W), V => congrArg (Prod.mk (lessR w)) (lessS_app W V)

section
variable {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (sh : RoundsQueryLayout lam K Q.loc.shape Q.ann)
  (wl : WireELess E) (sMT sFS depthReq : ℕ) (x : Y) (π : OneProtocolProof lam Q) (own : Leaves)
  (listed : List E.Pos) (rd : Leaves) (rdE : List E.Pos) (ρ : Rho Q.loc.shape)
  (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam)

theorem strictBBX_eq :
    strictBBX sMT sFS Q (lessS _ _ sh) wl depthReq π own listed rd rdE rts ph =
      strictBBL sMT sFS Q sh wl depthReq π own listed rd rdE rts ph := by
  unfold strictBBX strictBBL
  rw [strictSBX_eq]

variable (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
  (cms : List (Dig lam))

theorem forestsOfX_eq :
    forestsOfX Q (lessS _ _ sh) wl embS embE cms π rd rdE rts =
      forestsOfL Q sh wl embS embE cms π rd rdE rts := by
  unfold forestsOfX forestsOfL
  rw [forestsBX_eq]
  all_goals rfl

theorem afterFX_eq (Fs : List (Forest lam L)) (s : List (Dig lam)) :
    afterFX (K := K) Q (lessS _ _ sh) wl depthReq x π ρ rts ph Fs s =
      afterFL Q sh wl depthReq x π ρ rts ph Fs s := by
  unfold afterFX afterFL
  rw [mkTrX_eq]

theorem afterBOX_eq (nOpen maxDepth : ℕ) :
    afterBOX Q (lessS _ _ sh) wl nOpen maxDepth embS embE depthReq cms x π rd rdE ρ rts ph =
      afterBOL Q sh wl nOpen maxDepth embS embE depthReq cms x π rd rdE ρ rts ph := by
  unfold afterBOX afterBOL
  rw [forestsOfX_eq]
  cases forestsOfL Q sh wl embS embE cms π rd rdE rts with
  | none => rfl
  | some Fs =>
    simp only [afterFX_eq]

/-- **The verifier over the lesser records is the verifier along the lists**, as a tree of queries.
No premise. -/
theorem verifyBSX_eq (t : Tag) (nOpen maxDepth : ℕ)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (mkRd : Y → Rho Q.loc.shape → Plains Q.loc.shape → Leaves)
    (mkRdE : Y → Rho Q.loc.shape → List E.Pos) :
    verifyBSX sMT sFS t Q (lessS _ _ sh) wl nOpen maxDepth embS embP xin embE depthReq cms x π own
        listed mkRd mkRdE =
      verifyBSL sMT sFS t Q sh wl nOpen maxDepth embS embP xin embE depthReq cms x π own listed
        mkRd mkRdE := by
  unfold verifyBSX verifyBSL
  rw [chainBX_eq]
  refine congrArg _ (funext fun r => ?_)
  rcases r with _ | ⟨ρ, rts, ph⟩
  · rfl
  · show (if strictBBX sMT sFS Q (lessS _ _ sh) wl depthReq π own listed
          (mkRd x ρ (effPlains Q.loc.shape Q.ann rts π.plains)) (mkRdE x ρ) rts ph = true then
        afterBOX Q (lessS _ _ sh) wl nOpen maxDepth embS embE depthReq cms x π
          (mkRd x ρ (effPlains Q.loc.shape Q.ann rts π.plains)) (mkRdE x ρ) ρ rts ph
      else pure false) = _
    rw [strictBBX_eq, afterBOX_eq]

end

end TypedOracleCompiler.Compile.Batch
