-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/TwinDetProofs.lean: the proofs of the statements of Run/TwinDet.lean. Many statements of this
library are written twice: a definition in the namespace `Spec` states a proposition, and a theorem
of the same name outside that namespace proves it (lean/GLOSSARY.md).

`twd_twin`, `twd_verify`: the runs of `verifyT` and of the compiled verifier as the plain function
`verifyTF` (statements and hypotheses: Run/TwinDet.lean).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.TwinDet
import Run.TwinTie
import Run.VerifyDetProofs

set_option autoImplicit false

namespace Run.Twin
open Iop Rom Compile Compile.Batch

section
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (g : Fam (Batch.spec lam K L))

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
            generalize takeRt w.hasJ rts = tr
            cases tr with
            | none => rfl
            | some p =>
              simp only [det_bind', det_pure', det_askV,
                chainT_det early late t cms x salt rtreq S A W]
          | false =>
            dsimp only
            generalize takeRt w.has0 rts = tr
            cases tr with
            | none => rfl
            | some p =>
              simp only [det_bind', det_pure', det_askV,
                chainT_det early late t cms x salt rtreq S A W]
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

/-- So the compiled verifier at the skeleton's protocol, run under g, is `verifyTF g` at `L.early`,
`L.late`. -/
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

end Run.Twin
