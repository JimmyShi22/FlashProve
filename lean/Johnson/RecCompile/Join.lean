-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RecCompile/Join.lean: THE HOLOGRAPHIC IOP WITH RECORDS OF Hiop/RecMain.lean,
PASSED AND COMPILED: index binding of the verifier VC (Cms.lean), WORK COUNTED, from the library's
own hypotheses on a configuration and its sub-protocols (C.Props, S.Hyp P) and its own measure with
work on the five lists (P.BelowG g κ).
join_conf is generic in the configuration. Nothing is said of an honest prover; no configuration
with a record phase that is not empty is shown to meet the hypotheses here.

-/
import Johnson.RecCompile.Wire
import Cond.ObjBitsProof
import Hiop.RecMainProof
import Hiop.RecSoundProof

set_option autoImplicit false

noncomputable section

namespace Hiop
open Iop
namespace SubsR
variable {C : ConfigurationWithOutOfDomainSample} {S : SubsR C}

/-- the three lists of proof-of-work bits on the shapes of the object with records -/
def Bits.TR (g : S.Bits) : GBits S.lhr.offline.shape :=
  (GBits.app g.wf g.linOff : GBits (S.wf.shape ++ S.linOff.shape))
def Bits.LR (g : S.Bits) : GBits S.lhr.link.shape := g.link
def Bits.BR (g : S.Bits) : GBits S.lhr.onlineBatch.loc.shape :=
  (GBits.app g.req g.linOn : GBits (S.req.shape ++ S.linOn.ior.shape))

/-- The object with records, its verifier messages made by the samplers σ, with the proof-of-work
bits g. -/
def lhrW (S : SubsR C) (Nn : Type) [Inhabited Nn] (σT : Samplers S.lhr.offline.shape)
    (σL : Samplers S.lhr.link.shape) (σB : Samplers S.lhr.onlineBatch.loc.shape) (g : S.Bits) :
    HolographicProtocol C.I C.X :=
  (S.lhr.pull σT σL σB).grind Nn (g.TR.pull σT) (g.LR.pull σL) (g.BR.pull σB)

end SubsR
end Hiop

namespace Compile.Batch.Cms
open Iop Rom Prob Hiop
open scoped ENNReal

/-- Index binding of VC at the passed object of a configuration with records, at κs · κ: κ bounds
every round's error of the five lists, its work counted; κs is the samplers' bias. -/
theorem join_conf {ISK : Type} {lam : ℕ} (Nn : Type) [Inhabited Nn] (C : ConfigurationWithOutOfDomainSample) (S : SubsR C)
    (P : S.Nums) (b eR : ℕ) (hC : C.Props b eR) (hS : S.Hyp P)
    (σT : Samplers S.lhr.offline.shape) (σL : Samplers S.lhr.link.shape)
    (σB : Samplers S.lhr.onlineBatch.loc.shape) (κs KT KL KB : ℝ≥0∞) (gdT : σT.Good κs KT)
    (gdL : σL.Good κs KL) (gdB : σB.Good κs KB) (g : S.Bits) (κ : ℝ≥0∞) (hG : P.BelowG g κ)
    (W : QueryLayout lam (S.lhrW Nn σT σL σB g).carrierC) (Sd : OutOfDomainSampleQueryLayout lam W.K (S.lhrW Nn σT σL σB g))
    (p : Params) (hLaw : Sd.Law (κs * κ)) (hW : OKC W Sd)
    (A : ZKCP.Gen.Arg (spec lam W.K (S.lhrW Nn σT σL σB g).carrierC) C.I C.X Unit
      (FullKey lam (S.lhrW Nn σT σL σB g)) ISK (RequestProof lam (S.lhrW Nn σT σL σB g)))
    (hA : A.V = VC W Sd p) :
    ZKCP.Gen.HasIndexBindingWith
      (relPair (fun i x => ∃ w, C.Ryes i x w) (fun i x => ∃ w, C.Rno i x w)
        fun i x ⟨w, hw⟩ => ⟨w, hC.sub i x w hw⟩)
      A (extractorC0 W) (epsC W (κs * κ)) :=
  have hH := rec_honest C S P b eR 0 hC hS.honest
  cms_binding_work Nn S.lhr σT σL σB _ _ _ W Sd p C.Ryes C.Rno S.wit eR _ _ _ (κs * κ) _
    (rec_soundAt C S P b eR hC hS) gdT.fib gdL.fib gdB.fib hLaw
    (Err.BelowG.pull gdT
      ((belowG_app _ _ g.wf g.linOff P.wf.err P.linOff.err κ).2 ⟨hG.wf, hG.linOff⟩))
    (Err.BelowG.pull gdL hG.link)
    (Err.BelowG.pull gdB ((belowG_app _ _ g.req g.linOn P.req.err P.linOn.err κ).2 ⟨hG.req, hG.linOn⟩))
    rfl hH.localT hH.localL hH.localB hH.cohB hW A hA

end Compile.Batch.Cms

#print axioms Compile.Batch.Cms.join_conf
