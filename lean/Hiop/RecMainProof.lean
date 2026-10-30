-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/RecMainProof.lean: this file proves the composition theorems of the holographic interactive
oracle proof (Hiop/RecMain.lean), but for index binding.

(Index binding: Hiop/RecSoundProof.lean.)

The honest half (`rec_honest`) uses no item on knowledge soundness. What it uses of `S.HypH P`
(Hiop/RecBuild.lean, Hiop/RecSubs.lean) and of `ConfigurationWithOutOfDomainSample.Props`, field by field of `PropsH`:
  `wired`: `ConfigurationWithOutOfDomainSample.Props`: `free_enc`, `dcd_enc`, `held_hold`.
  `reads`: preambles: `noReads`, `srcIdx`, `srcAux`; IOPP: `idxReads`, at N instances `idxShared`;
    link: `cntPar`, `cntCh`; `ConfigurationWithOutOfDomainSample.Props.hides`.
  `hidden`: offline: `exact` of both parts, composed (with `isLocal`, `acc` of the preamble);
    `bud0`, `tied`, `fitOff`, `noTie`, `noHid`, `prHid`. link: `exact`, `bud0`, `tied`, `noHid`.
    session: `isLocal`, `acc`, `exact`, `copy`, `srcIdx`, `srcAux`, `noReads`, `noTie`, `fitOn`,
    `bud0`, `tied`, `prHid`, `hands`, and `ConfigurationWithOutOfDomainSample.Props.admits`.
  `complete`: `acc` of `wf`, `linOff`, `link`, `req`, `linOn`; `prBad`, `prHid`, `noHid`; for a
    session also `hands` and `ConfigurationWithOutOfDomainSample.Props.admits`.
  local, coherent, point: of the parameter lists.
An input of an honest side is valid if its record is that of an honest record phase (for a session,
`validB`, also: x has a witness in Ryes); then the statement with the prover encoded index `pidx` is
in the exact relation (`in_rwf`, `in_req`; `in_rreq`, under `C.Props b eR`).

Limits: what the head of Hiop/RecMain.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
/- Limits: no theorem of this library states `S.Hyp P` of a concrete object, or that the hypotheses
   of `rec_main`, `rec_offline`, `rec_online` or `rec_honest` can be met together.



-/
import Hiop.RecSoundProof
import Hiop.RecInterfaceProofs
import Hiop.ProofKit
import Iop.BatchOne
import Ior.OnlineHon
import Ior.SeqProofs
import Ior.ExactSeq
import Blocks.Basic
import Blocks.Batch.Kit

set_option autoImplicit false

namespace Hiop
open Iop Prob
open scoped ENNReal

variable {C : ConfigurationWithOutOfDomainSample} {S : SubsR C} {P : S.Nums}

theorem ConfigurationWithOutOfDomainSample.enc_pidx (C : ConfigurationWithOutOfDomainSample) (i : C.I) (r : C.Pad × C.Rnd) (s : C.Seed) :
    C.Enc (s, C.smp s (C.hold i r.1)) (C.enc (C.hold i r.1) r.2) (C.pidx i r s) := ⟨rfl, rfl, rfl⟩

/-- the index decoder on an honest word with an honest record -/
theorem ConfigurationWithOutOfDomainSample.Props.D_enc {b eR : ℕ} (hC : C.Props b eR) (i : C.I)
    (r : C.Pad × C.Rnd) (s : C.Seed) :
    C.D (C.enc (C.hold i r.1) r.2) (s, C.smp s (C.hold i r.1)) = some i := by
  unfold ConfigurationWithOutOfDomainSample.D
  rw [if_neg (hC.free_enc _ _ _), hC.dcd_enc]
  exact hC.held_hold i r.1

theorem in_rwf (w : C.I × (C.Pad × C.Rnd) × C.Seed) (rec : C.Rec) (h : S.lhr.validT w rec) :
    C.Rwf rec (C.enc (C.hold w.1 w.2.1.1) w.2.1.2) (C.pidx w.1 w.2.1 w.2.2) := by
  subst h
  exact ⟨C.enc_pidx _ _ _, w.1, w.2.1.1, rfl⟩

theorem in_req (w : C.I × ((C.Pad × C.Rnd) × C.Seed) × ((C.Pad × C.Rnd) × C.Seed))
    (rr : C.Rec × C.Rec) (h : S.lhr.validL w rr) :
    C.Req rr (C.enc (C.hold w.1 w.2.1.1.1) w.2.1.1.2, C.enc (C.hold w.1 w.2.2.1.1) w.2.2.1.2)
      (C.pidx w.1 w.2.1.1 w.2.1.2, C.pidx w.1 w.2.2.1 w.2.2.2) := by
  subst h
  exact ⟨C.enc_pidx _ _ _, C.enc_pidx _ _ _, w.1, w.2.1.1.1, w.2.2.1.1, rfl, rfl⟩

theorem in_rreq {b eR : ℕ} (hC : C.Props b eR) (w : C.I × (C.Pad × C.Rnd) × C.Seed)
    (a : C.X × C.Rec) (h : S.lhr.validB (fun i x => ∃ c, C.Ryes i x c) w a) :
    C.Rreq a (C.enc (C.hold w.1 w.2.1.1) w.2.1.2) (C.pidx w.1 w.2.1 w.2.2, C.trace w.1 a.1) := by
  obtain ⟨x, rec⟩ := a
  obtain ⟨h1, c, hc⟩ := h
  have h1 : rec = S.lhr.recOf w.1 w.2.1 w.2.2 := h1
  subst h1
  exact ⟨C.enc_pidx _ _ _, w.1, w.2.1.1, rfl, hC.admits _ _ c hc⟩

theorem rec_offline_acc (hS : S.HypH P) : S.hOffline.Acc C.Rwf IOR.triv :=
  Iop.acc_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hS.wf.acc hS.linOff.acc

theorem rec_offline_exact (hS : S.HypH P) :
    S.hOffline.Exact C.Rwf (IOR.budSeq S.wf S.linOff P.wf.bud P.linOff.bud) :=
  Iop.exact_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hS.wf.isLocal hS.wf.acc
    hS.wf.exact hS.linOff.exact

theorem rec_offline : Spec.rec_offline := fun C S P hS =>
  ⟨rec_offline_know C S P hS.know, rec_offline_acc hS.honest, rec_offline_exact hS.honest⟩

theorem rec_online_exact {b eR : ℕ} (hC : C.Props b eR) (hS : S.HypH P) :
    S.session.ExactT S.lhr.honestOnlineBatchProver S.N (S.lhr.validB fun i x => ∃ c, C.Ryes i x c)
      (budOnline S.req S.linOn P.req.bud P.linOn.bud) :=
  Iop.exact_online (C.X × C.Rec) (S.on.Xl × C.Rec) (C.I × (C.Pad × C.Rnd) × C.Seed)
    (C.PIdx × C.Cells) C.PIdx S.on.WAux C.E0 S.on.Ej S.req S.linOn S.hReq S.hLinOn
    (fun w => C.enc (C.hold w.1 w.2.1.1) w.2.1.2) (fun w => C.pidx w.1 w.2.1 w.2.2)
    (fun w a => (C.pidx w.1 w.2.1 w.2.2, C.trace w.1 a.1))
    (S.lhr.validB fun i x => ∃ c, C.Ryes i x c) C.Rreq S.on.Rlin P.req.bud S.N P.linOn.bud
    hS.req.isLocal hS.req.acc hS.req.exact hS.linOn.exact (fun w a hv => in_rreq hC w a hv)
    (fun w a c ρ hv hρ => hS.req.hands a _ _ c ρ (in_rreq hC w a hv) hρ) hS.req.copy hS.req.srcIdx
    hS.req.srcAux hS.req.noReads hS.req.noTie

theorem rec_online : Spec.rec_online := fun C S P _ _ hC hS =>
  ⟨rec_online_know C S P hS.know hS.honest.req.passes hS.honest.req.copy,
    rec_online_exact hC hS.honest⟩

theorem rec_honest : Spec.rec_honest := by
  intro C S P b eR εs hC hS
  refine ⟨?wired, ?reads, ?hidden, ?complete, ?localT, ?localL, ?localB, ?cohB,
    ?pointT, ?pointL, ?pointB⟩
  case wired =>
    exact ⟨fun i r s => hC.D_enc i r s, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  case reads =>
    refine ⟨fun _ ρ => ?_, fun _ ρ => hS.link.cntPar ρ, fun _ ρ => hS.link.cntCh ρ, ?_, hC.hides⟩
    · exact le_trans
        (IOR.card_extReads_seq_copy
          S.wf S.linOff hS.wf.noReads (fun ρ p => (hS.wf.srcIdx ρ p).1) hS.wf.srcAux ρ)
        (hS.linOff.idxReads _)
    · exact BatchInteractiveOracleProof.readsAtMost_of_extShared _
        (extShared_online S.req S.linOn hS.req.noReads (fun ρ p => (hS.req.srcIdx ρ p).1)
          hS.req.srcAux hS.linOn.idxShared)
        (fun _ ρ =>
          le_trans (IOR.card_extReads_seq_copy
              S.req S.linOn.ior hS.req.noReads (fun ρ p => (hS.req.srcIdx ρ p).1) hS.req.srcAux ρ)
            (hS.linOn.idxReads _)) S.N
  case hidden =>
    refine ⟨?_, ?_, ?_⟩
    · exact Iop.hvzk_toProto C.Rec (C.I × (C.Pad × C.Rnd) × C.Seed) C.PIdx C.E0 S.offline
        S.hOffline (fun w => C.enc (C.hold w.1 w.2.1.1) w.2.1.2)
        (fun w _ => C.pidx w.1 w.2.1 w.2.2) S.lhr.validT C.Rwf
        (IOR.budSeq S.wf S.linOff P.wf.bud P.linOff.bud) P.wf.pHid (rec_offline_exact hS)
        (fun ρ =>
          IOR.budSeq_empty S.wf S.linOff P.wf.bud P.linOff.bud ρ (hS.linOff.bud0 _)
            (tied_union _ hS.linOff.tied _) (hS.fitOff _ _))
        (IOR.tied_seq_of_noTie S.wf S.linOff hS.wf.noTie (tied_union _ hS.linOff.tied))
        (fun w x hv => in_rwf w x hv) (fun w x hv =>
          le_trans
            (le_of_eq (IOR.Honest.prRho_hid_seq_of_noHid S.hWf S.hLinOff hS.linOff.noHid _ _))
            (hS.wf.prHid _ _ _ (in_rwf w x hv)))
    · exact Iop.hvzk_toProto (C.Rec × C.Rec)
        (C.I × ((C.Pad × C.Rnd) × C.Seed) × ((C.Pad × C.Rnd) × C.Seed)) (C.PIdx × C.PIdx)
        (twoExternalStrings C.n C.Sg) S.link S.hLink
        (fun w => (C.enc (C.hold w.1 w.2.1.1.1) w.2.1.1.2, C.enc (C.hold w.1 w.2.2.1.1) w.2.2.1.2))
        (fun w _ => (C.pidx w.1 w.2.1.1 w.2.1.2, C.pidx w.1 w.2.2.1 w.2.2.2))
        S.lhr.validL C.Req P.link.bud 0 hS.link.exact hS.link.bud0
        (tied_union _ hS.link.tied) (fun w x hv => in_req w x hv)
        (fun w x _ => by rw [hS.link.noHid]; exact le_of_eq (pr_empty _))
    · exact Iop.hvzk_online (C.X × C.Rec) (S.on.Xl × C.Rec) (C.I × (C.Pad × C.Rnd) × C.Seed)
        (C.PIdx × C.Cells) C.PIdx S.on.WAux C.E0 S.on.Ej S.req S.linOn S.hReq S.hLinOn
        (fun w => C.enc (C.hold w.1 w.2.1.1) w.2.1.2) (fun w => C.pidx w.1 w.2.1 w.2.2)
        (fun w a => (C.pidx w.1 w.2.1 w.2.2, C.trace w.1 a.1))
        (S.lhr.validB fun i x => ∃ c, C.Ryes i x c) C.Rreq S.on.Rlin P.req.bud S.N P.linOn.bud
        P.req.pHid hS.req.isLocal hS.req.acc hS.req.exact hS.linOn.exact
        (fun w a hv => in_rreq hC w a hv)
        (fun w a c ρ hv hρ => hS.req.hands a _ _ c ρ (in_rreq hC w a hv) hρ) hS.req.copy
        hS.req.srcIdx hS.req.srcAux hS.req.noReads hS.req.noTie hS.fitOn hS.linOn.bud0 hS.linOn.tied
        (fun w a hv => hS.req.prHid _ _ _ (in_rreq hC w a hv))
  case complete =>
    refine ⟨?_, ?_, ?_, fun w x hv => ?_, fun w x _ => ?_, fun w a hv => ?_⟩
    · exact Iop.acc_toProto C.Rec (C.I × (C.Pad × C.Rnd) × C.Seed) C.PIdx C.E0 S.offline S.hOffline
        _ _ S.lhr.validT C.Rwf (rec_offline_acc hS) (fun w x hv => in_rwf w x hv)
    · exact Iop.acc_toProto (C.Rec × C.Rec)
        (C.I × ((C.Pad × C.Rnd) × C.Seed) × ((C.Pad × C.Rnd) × C.Seed))
        (C.PIdx × C.PIdx) (twoExternalStrings C.n C.Sg) S.link S.hLink _ _ S.lhr.validL C.Req
        hS.link.acc (fun w x hv => in_req w x hv)
    · exact Iop.acc_online (C.X × C.Rec) (S.on.Xl × C.Rec) (C.I × (C.Pad × C.Rnd) × C.Seed)
        (C.PIdx × C.Cells) C.PIdx S.on.WAux C.E0 S.on.Ej S.req S.linOn S.hReq S.hLinOn
        (fun w => C.enc (C.hold w.1 w.2.1.1) w.2.1.2) (fun w => C.pidx w.1 w.2.1 w.2.2)
        (fun w a => (C.pidx w.1 w.2.1 w.2.2, C.trace w.1 a.1))
        (S.lhr.validB fun i x => ∃ c, C.Ryes i x c) C.Rreq S.on.Rlin hS.req.acc hS.linOn.acc
        (fun w a hv => in_rreq hC w a hv)
        (fun w a c ρ hv hρ => hS.req.hands a _ _ c ρ (in_rreq hC w a hv) hρ)
    · exact le_trans (IOR.Honest.prRho_withheld_seq_le S.hWf S.hLinOff hS.linOff.noHid _ _)
        (add_le_add (add_le_add hS.wf.prBad (hS.wf.prHid _ _ _ (in_rwf w x hv))) hS.linOff.prBad)
    · show prRho
          (S.hLink.Bad ∪ S.hLink.Hid (C.pidx w.1 w.2.1.1 w.2.1.2, C.pidx w.1 w.2.2.1 w.2.2.2) x) ≤
        P.link.pBad
      rw [hS.link.noHid, Set.union_empty]
      exact hS.link.prBad
    · exact le_trans (prRho_withheld_online_le S.req S.linOn S.hReq S.hLinOn _ _ _ w a)
        (add_le_add (add_le_add hS.req.prBad (hS.req.prHid _ _ _ (in_rreq hC w a hv)))
          hS.linOn.prBad)
  case localT =>
    exact Iop.isLocal_toProto _ _ _
      (Iop.isLocal_seq _ _ _ _ _ _ _ _ hS.wf.isLocal hS.linOff.isLocal)
  case localL => exact Iop.isLocal_toProto _ _ _ hS.link.isLocal
  case localB =>
    exact Iop.isLocal_toProto _ _ _
      (Iop.isLocal_seq _ _ _ _ _ _ _ _ hS.req.isLocal hS.linOn.isLocal)
  case cohB =>
    exact RoundSplits.app_coherent
      (RoundSplits.const_coherent (f := RAnn.allLocal) (fun r => RAnn.ofSlot_coherent .lo r) _)
      hS.linOn.coherent
  case pointT => exact hS.wf.point.elim fun p => hS.linOff.point.elim fun q => ⟨Blocks.pointApp p q⟩
  case pointL => exact hS.link.point
  case pointB => exact hS.req.point.elim fun p => hS.linOn.point.elim fun q => ⟨Blocks.pointApp p q⟩

theorem rec_main : Spec.rec_main := fun C S P b eR εs hC hS hP hR =>
  { sub := fun i x ⟨w, hw⟩ => ⟨w, hC.sub i x w hw⟩
    sound := (Iop.soundR_iff_at _ _ _ S.lhr C.Rno S.wit εs).2
      ⟨eR, _, _, _, rec_soundAt C S P b eR hC hS, hR, Err.Below.app hP.wf hP.linOff,
        hP.link, Err.Below.app hP.req hP.linOn⟩
    honest := rec_honest C S P b eR εs hC hS.honest }

end Hiop
