-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/VerifyDetProofs.lean: the proofs of the statements of Run/VerifyDet.lean.

`vd_verify`: the run of the compiled verifier of one slot as a plain function (statement and
hypotheses: Run/VerifyDet.lean).
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.VerifyDet

set_option autoImplicit false

namespace Run
open Iop Rom Compile Compile.Batch

section
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (g : Fam (Batch.spec lam K L))

theorem det_bind' {S : OSpec} {α β : Type} (g : Fam S) (c : OComp S α) (k : α → OComp S β) :
    (c >>= k).det g = (k (c.det g)).det g :=
  OComp.det_bind g c k
theorem det_pure' {S : OSpec} {α : Type} (g : Fam S) (a : α) : (pure a : OComp S α).det g = a := rfl
theorem det_askV (o : Batch.OracleName) (q : domOf lam L o) : (askTypedOracle (L := L) (K := K) o q).det g = g o q :=
  rfl

theorem chainB_det (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits) (rtreq : Dig lam) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
        (i : ℕ) (ph : Phase lam) (rts : List (Dig lam)) (pls : Plains s),
      (recomputeChain t cms x salt rtreq s A W embP i ph rts pls).det g =
        chainF g t cms x salt rtreq s A W embP i ph rts pls
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls) => by
      simp only [recomputeChain, chainF]
      generalize actOf cms (x.map L.early) salt a.kind ph = act
      cases act with
      | none => rfl
      | some ac =>
        cases ac with
        | one h own next =>
          cases own with
          | true =>
            dsimp only
            generalize takeRt w.hasJ rts = tr
            cases tr with
            | none => rfl
            | some p =>
              simp only [det_bind', det_pure', det_askV, chainB_det t cms x salt rtreq s A W]
          | false =>
            dsimp only
            generalize takeRt w.has0 rts = tr
            cases tr with
            | none => rfl
            | some p =>
              simp only [det_bind', det_pure', det_askV, chainB_det t cms x salt rtreq s A W]
        | join ρ =>
          dsimp only
          generalize takeRt w.hasJ rts = tr
          cases tr with
          | none => rfl
          | some p =>
            dsimp only
            generalize takeRt w.has0 p.2 = tr2
            cases tr2 with
            | none => rfl
            | some p2 =>
              simp only [det_bind', det_pure', det_askV, chainB_det t cms x salt rtreq s A W]

/-! ### The walks up the Merkle trees -/

theorem leavesV_det :
    ∀ cs : List (ℕ × Check lam L),
      (leavesV (K := K) cs).det g = cs.map fun e => (g Batch.OracleName.leaf e.2.inp : Dig lam)
  | [] => rfl
  | e :: es => by
    simp only [leavesV, det_bind', det_pure', det_askV, leavesV_det es, List.map_cons]
    rfl

theorem runForest_det (F : Forest lam L) (s : List (Dig lam)) :
    (runForest (K := K) F s).det g = runForestF g F s := by
  simp only [runForest, det_bind', det_pure', leavesV_det]
  exact congrArg
    (fun out => ((Octopus.upN F.depth F.idx).zip out).all fun m => decide (m.2 = F.treeRoot m.1))
    (Evaluates.octC (Seed.evalO g) (qN := hashTreeNode (L := L) (K := K)) (hN := nodeF g)
      (fun _ _ => rfl) F.depth F.idx _ s)

theorem runForests_det :
    ∀ (Fs : List (Forest lam L)) (s : List (Dig lam)),
      (runForests (K := K) Fs s).det g = runForestsF g Fs s
  | [], _ => rfl
  | F :: Fs, s => by
    simp only [runForests, runForestsF, det_bind', det_pure', runForest_det, runForests_det Fs]

/-! ### The request tree -/

theorem reqCheck_det (depthReq : ℕ) (rtreq : Dig lam) (slot : ℕ)
    (path : List (Dig lam)) (c : Dig lam) :
    (reqCheck (L := L) (K := K) depthReq rtreq slot path c).det g =
      reqCheckF g depthReq rtreq slot path c := by
  unfold reqCheck reqCheckF
  split
  · simp only [det_bind', det_pure', det_askV]
    exact congrArg (fun r => decide (r = rtreq))
      (Evaluates.climbM (Seed.evalO g) (qN := rnodeV (L := L) (K := K)) (hN := rnodeF g)
        (fun _ _ => rfl) path slot _)
  · rfl

variable {Y : Type} {E : ExtSpec}

theorem reqPart_det {Q : BatchInteractiveOracleProof Y E} (depthReq : ℕ) (π : OneProtocolProof lam Q) (ph : Phase lam) :
    (reqPart (L := L) (K := K) depthReq π ph).det g = reqPartF g depthReq π ph := by
  unfold reqPart reqPartF
  cases ph.slotVal with
  | none => rfl
  | some c => exact reqCheck_det g depthReq _ _ _ c

/-! ### The verifier -/

theorem afterBO_det (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    (checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph).det g =
      afterBOF g Q wq embS embE depthReq cms x π ρ rts ph := by
  unfold checkPrunedOpenings afterBOF
  cases forestsOf Q wq embS embE cms x π ρ rts with
  | none => rfl
  | some Fs =>
    dsimp only
    split
    · unfold afterF
      rw [OComp.det_bind, OComp.det_bind, runForests_det, reqPart_det]
      rfl
    · rfl

theorem verifyBS_det (sMT sFS : ℕ) (t : Tag) (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) :
    (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π).det g =
      verifyF g sMT sFS t Q wq embS embP xin embE depthReq cms x π := by
  unfold verifyOneProtocol verifyF recomputeChainOfProof
  rw [OComp.det_bind, chainB_det]
  cases chainF g t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann wq.sh embP 0
      .first π.roots π.plains with
  | none => rfl
  | some r =>
    dsimp only
    split
    · exact afterBO_det g Q wq embS embE depthReq cms x π _ _ _
    · rfl


end

theorem vd_chain : Spec.vd_chain := fun _ _ _ _ _ g t cms x salt rtreq =>
  chainB_det g t cms x salt rtreq

theorem vd_forests : Spec.vd_forests := fun _ _ _ _ _ g => ⟨runForest_det g, runForests_det g⟩

theorem vd_req : Spec.vd_req := fun _ _ _ _ _ g => reqCheck_det g

theorem vd_after : Spec.vd_after := fun _ _ _ _ _ g _ _ => afterBO_det g

theorem vd_verify : Spec.vd_verify := fun _ _ _ _ _ g _ _ => verifyBS_det g

end Run
