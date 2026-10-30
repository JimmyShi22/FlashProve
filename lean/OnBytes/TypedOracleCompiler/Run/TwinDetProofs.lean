-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/TwinDetProofs.lean.
Run/TwinDetProofs.lean: the proofs of the statements of Run/TwinDet.lean. The steps are those of
Run/VerifyDetProofs.lean, on the twin's texts; the walks' and the request tree's lemmas of that file
serve as they are; the last statement by Run/TwinTie.lean (verifyT_eq).

Terms: lean/GLOSSARY.md.

-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library: a test by Lean's evaluator, which
   leaves no declaration. So nothing that is checked of declarations is checked of such a run. No
   clause of a soundness theorem of this library speaks of a run. -/
import Run.TwinDetProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinDefs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.VerifyDet
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinTiePureProofs
-- TWO: reached in the library through files that are not said again
import OnBytes.TypedOracleCompiler.Run.TwinTiePure
import OnBytes.TypedOracleCompiler.Run.TwinDet
import OnBytes.TypedOracleCompiler.Run.TwinTie
import OnBytes.TypedOracleCompiler.Run.VerifyDetProofs

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Twin
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.Twin

section
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily lam K L))

theorem chainT_det (early : X → X) (late : Option ℕ) (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (salt : Bits) (rtreq : Dig lam) :
    ∀ (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A)
        (embP : PlainPart (up S) A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam)
        (rts : List (Dig lam)) (pls : Plains (up S)),
      (chainT early late t cms x salt rtreq S A W embP i ph rts pls).det g =
        chainTF g early late t cms x salt rtreq S A W embP i ph rts pls
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: S, (a, A), (w, W), embP, i, ph, rts, (pl, pls) => by
      simp only [chainT, chainTF]
      generalize actOf cms (x.map early) salt a.kind ph = act
      cases act with
      | none => rfl
      | some ac =>
        cases ac with
        | one h own next =>
          cases own with
          | true =>
            dsimp only
            generalize takeRt w.depthJ.length rts = tr
            cases tr with
            | none => rfl
            | some p =>
              simp only [det_bind', det_pure', det_askV,
                chainT_det early late t cms x salt rtreq S A W]
          | false =>
            dsimp only
            generalize takeRt w.depth0.length rts = tr
            cases tr with
            | none => rfl
            | some p =>
              simp only [det_bind', det_pure', det_askV,
                chainT_det early late t cms x salt rtreq S A W]
        | join ρ =>
          dsimp only
          generalize takeRt w.depthJ.length rts = tr
          cases tr with
          | none => rfl
          | some p =>
            dsimp only
            generalize takeRt w.depth0.length p.2 = tr2
            cases tr2 with
            | none => rfl
            | some p2 =>
              simp only [det_bind', det_pure', det_askV,
                chainT_det early late t cms x salt rtreq S A W]

variable {Y : Type} {E : ExtSpec}

theorem afterBOT_det (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) (ρ : Rho (up P.S))
    (rts : RootsOfChain lam (up P.S)) (ph : Phase lam) :
    (afterBOT P wq embS embE depthReq cms x π ρ rts ph).det g =
      afterBOTF g P wq embS embE depthReq cms x π ρ rts ph := by
  unfold afterBOT afterBOTF
  cases forestsOfT P wq embS embE cms x π ρ rts with
  | none => rfl
  | some Fs =>
    dsimp only
    split
    · unfold afterFT
      rw [OComp.det_bind, OComp.det_bind, runForests_det, reqPart_det]
      rfl
    · rfl

theorem verifyT_det (early : X → X) (late : Option ℕ) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
    (wq : ProtocolQueryLayout lam K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) :
    (verifyT early late sMT sFS t P wq embS embP xin embE depthReq cms x π).det g =
      verifyTF g early late sMT sFS t P wq embS embP xin embE depthReq cms x π := by
  unfold verifyT verifyTF chainQT
  rw [OComp.det_bind, chainT_det]
  cases chainTF g early late t cms (xin x) π.salt π.rtreq P.S P.ann wq.sh embP 0
      .first π.roots π.plains with
  | none => rfl
  | some r =>
    dsimp only
    split
    · exact afterBOT_det g P wq embS embE depthReq cms x π _ _ _
    · rfl

/-- so: the library's verifier at the skeleton's protocol, run under g, is verifyTF -/
theorem verifyBS_det_twin (sMT sFS : ℕ) (t : Tag) (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam P.up) :
    (verifyOneProtocol sMT sFS t P.up wq embS embP xin embE depthReq cms x π).det g =
      verifyTF g L.early L.late sMT sFS t P wq embS embP xin embE depthReq cms x π := by
  rw [← verifyT_eq, verifyT_det]

end

theorem twd_chain : Spec.twd_chain := fun _ _ _ _ _ g early late t cms x salt rtreq =>
  chainT_det g early late t cms x salt rtreq

theorem twd_after : Spec.twd_after := fun _ _ _ _ _ g _ _ => afterBOT_det g

theorem twd_twin : Spec.twd_twin := fun _ _ _ _ _ g _ _ => verifyT_det g

theorem twd_verify : Spec.twd_verify := fun _ _ _ _ _ g _ _ => verifyBS_det_twin g

end TypedOracleCompiler.Run.Twin
