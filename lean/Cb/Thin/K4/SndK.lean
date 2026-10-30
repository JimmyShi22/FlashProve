-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Thin/K4/SndK.lean.
WHY: the library's record LdLinP.Snd.OK (Cb/Ld/LdLin.lean:429-450) has 21 fields; nine are on the
three senders; every statement of the batch's «know» road takes it whole. HERE: D4 Snd.OKK: THE
TWELVE OTHERS, in its words (laws, fair, list, ev of W, U, O: of codes, seeds, lists);
T7 linkWK: linkW's conclusion to the letter from fair, list, ev of W: ITS PROOF CALLS THE LIBRARY's
ROOT ldSendFam_into (Cb/Ld/LdSendFam.lean:338) where linkW (Cb/Ld/LdLinBProofs.lean:221-222) reads a
bundle at .good.know; T8 linkUK, T9 linkOK: linkU's, linkO's terms again;
T10 ldLinCB_coreK: ldLinCB_core's term with three names turned; T11 ldLinC_plK: every link of the
core has Link.PL.
NEARLY ALL OF IT IS COPY WITH A NAME TURNED: the library's statements take S.OK whole: no call can
be thinner than its callee. If the library's linkW called the root, Snd.OK's nine would fall out of
the «know» road with no twin at all.
NOT CALLED: ldLinC_allT, ldLinCB_core, ldSendFam_piece. S : P.Snd is data that holds the three
senders: no property of them is asked.

-/
import Cb.Thin.K4.PLOf
import Cb.Ld.LdLinChainB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- D4: twelve of `Snd.OK`'s twenty-one fields: what the «know» road, locality and the points read.
-/
structure LdLinP.Snd.OKK {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Fintype κ]
    [Fintype J] [Fintype Y] {P : LdLinP E ι κ J Y} (S : P.Snd) : Prop where
  lawsW : ∀ a, (P.NW.om a).C.Laws
  fairW : P.SdW.Fair
  listW : ∀ a, (P.NW.om a).ListLE (S.LW a)
  evW   : ∀ a, (P.NW.om a).Evades
  lawsU : ∀ a, (P.NU.om a).C.Laws
  fairU : P.SdU.Fair
  listU : ∀ a, (P.NU.om a).ListLE (S.LU a)
  evU   : ∀ a, (P.NU.om a).Evades
  lawsO : ∀ a, (P.NO.om a).C.Laws
  fairO : P.SdO.Fair
  listO : ∀ a, (P.NO.om a).ListLE (S.LO a)
  evO   : ∀ a, (P.NO.om a).Evades

section
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y] (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (N : ℕ)

omit [Fintype E] [Nonempty ι] in
/-- T7: the sending of W in every slot: a call of the root. -/
theorem LdLinP.linkWK (S : P.Snd) (hF : P.SdW.Fair) (hL : ∀ a, (P.NW.om a).ListLE (S.LW a))
    (hE : ∀ a, (P.NW.om a).Evades) :
    ldk_LinkB P.sW (RoundSplits.allLocal _) N P.k0 P.k1 (P.jA on0).cf.relR (P.j1 on0).cf.relR
      (fun _ _ w => P.backW (P.NW.msgs w.1) w.2)
      (ldSendFamNums P.NW P.SdW P.X0 P.E0 Unit S.LW S.tW).err :=
  ⟨ldk_knowB_adm _
      (knowB_local _ _ _ _ _ _ P.sW RAnn.allLocal (fun _ => rfl) N _ _ _ _ _
        ((knowInto_iff _ _ _ _ _ _ _ _ _ _ _).1
          (ldSendFam_into E P.NW P.SdW Unit P.X0 P.WA P.W0 P.E0 (P.jA on0) P.backW S.LW hF hL hE))),
    fun _ ha τ =>
      ldk_sameKey_bind (fun j aj => P.sW.red.out aj (τ.slot j)) id
        (fun _ _ _ h => by obtain rfl := Option.some.inj h; rfl) ha⟩

omit [Fintype E] [Nonempty ι] in
/-- T8: the sending of G_u by the shared part. -/
theorem LdLinP.linkUK (S : P.Snd) (hF : P.SdU.Fair) (hL : ∀ a, (P.NU.om a).ListLE (S.LU a))
    (hE : ∀ a, (P.NU.om a).Evades) :
    ldk_LinkB P.sU (shAnn _) N P.k2 P.k3 (P.j2 on0).cf.relR (P.j3 on0).cf.relR
      (fun _ _ w => P.backU (P.NU.msgs w.1) w.2)
      (ldSendFamNums P.NU P.SdU P.X2 P.E1 Unit S.LU S.tU).err :=
  ⟨ldk_knowB_adm _
      (ldLinB_send_shared P.NU P.SdU P.X2 P.W2 P.W1 P.E1 (P.j2 on0)
        P.backU S.LU S.tU N hF hL hE),
    fun _ ha τ =>
      ldk_sameKey_bind (fun j aj => P.sU.red.out aj (τ.slot j))
        (fun k => (k, ((fun a => (P.SdU.sd a τ.2.1, τ.2.2.1.1.2 a)), τ.1.1.1)))
        (fun _ _ _ h => by obtain rfl := Option.some.inj h; rfl) ha⟩

omit [Fintype E] [Fintype ι] [Nonempty ι] in
/-- T9: the sending of Ω by the shared part. -/
theorem LdLinP.linkOK (S : P.Snd) (hF : P.SdO.Fair) (hL : ∀ a, (P.NO.om a).ListLE (S.LO a))
    (hE : ∀ a, (P.NO.om a).Evades) :
    ldk_LinkB P.sO (shAnn _) N P.k4 P.k5 P.j4.cf.relR P.j5.cf.relR
      (fun _ _ w => P.backO (P.NO.msgs w.1) w.2)
      (ldSendFamNums P.NO P.SdO P.X4 P.E4 Unit S.LO S.tO).err :=
  ⟨ldk_knowB_adm _
      (ldLinB_send_shared P.NO P.SdO P.X4 P.W4 P.W3 P.E4 P.j4 P.backO S.LO S.tO N
        hF hL hE),
    fun _ ha τ =>
      ldk_sameKey_bind (fun j aj => P.sO.red.out aj (τ.slot j))
        (fun k => (k, ((fun a => (P.SdO.sd a τ.2.1, τ.2.2.1.1.2 a)), τ.1.1.1)))
        (fun _ _ _ h => by obtain rfl := Option.some.inj h; rfl) ha⟩

/-- T10: the core has `KB`, from the twelve. -/
theorem ldLinCB_coreK (εf : ℕ) (S : P.Snd) (hF : P.FoldErr on0 εf)
    (hpy : Function.Injective P.D.py) (hS : S.OKK) :
    (P.chainA on0 S εf N).KB N (P.key0 on0) P.key6 := by
  unfold LdLinP.chainA
  simp only [ChainA.kb_snoc, ChainA.kb_one]
  exact ⟨⟨_, P.k5⟩,
    ⟨⟨_, P.k4⟩,
      ⟨⟨_, P.k3⟩,
        ⟨⟨_, P.k2⟩,
          ⟨⟨_, P.k1⟩,
            ⟨⟨_, P.k0⟩, P.link0 on0 N, P.linkWK on0 N S hS.fairW hS.listW hS.evW⟩,
            P.linkPt on0 N εf hF⟩,
          P.linkUK on0 N S hS.fairU hS.listU hS.evU⟩,
        P.linkLoc on0 N⟩,
      P.linkOK N S hS.fairO hS.listO hS.evO⟩,
    P.linkZeta N hpy⟩

/-- T11: every link of the core has point oracles and a local verifier. -/
theorem ldLinC_plK (εf : ℕ) (S : P.Snd) (hF : P.FoldErr on0 εf)
    (hpy : Function.Injective P.D.py) (hS : S.OKK) : (P.chain on0 S εf).Each (PLk Unit) := by
  have h0 : (P.lk0 on0).PL :=
    ⟨(ldLin_step0 P on0 fun _ => True).good.point, (ldLin_step0 P on0 fun _ => True).good.isLocal⟩
  have hW : (P.lkW on0 S).PL :=
    ⟨⟨P.NW.pt P.SdW⟩, ldSendFam_isLocal P.NW P.SdW P.X0 P.E0 hS.lawsW⟩
  have hP : (P.lkPt on0 εf).PL :=
    ⟨(ldLin_pt P on0 εf (fun _ => True) hF).good.point,
      (ldLin_pt P on0 εf (fun _ => True) hF).good.isLocal⟩
  have hU : (P.lkU on0 S).PL :=
    ⟨⟨P.NU.pt P.SdU⟩, ldSendFam_isLocal P.NU P.SdU P.X2 P.E1 hS.lawsU⟩
  have hLc : (P.lkLoc on0).PL :=
    ⟨(ldLin_loc P on0 S fun _ => True).good.point, (ldLin_loc P on0 S fun _ => True).good.isLocal⟩
  have hO : (P.lkO S).PL :=
    ⟨⟨P.NO.pt P.SdO⟩, ldSendFam_isLocal P.NO P.SdO P.X4 P.E4 hS.lawsO⟩
  have hZ : P.lkZeta.PL :=
    ⟨(ldLin_zeta P (fun _ => True) hpy).good.point, (ldLin_zeta P (fun _ => True) hpy).good.isLocal⟩
  unfold LdLinP.chain
  simp only [Chain.each_snoc, Chain.each_one]
  exact ⟨⟨⟨⟨⟨⟨h0, hW⟩, hP⟩, hU⟩, hLc⟩, hO⟩, hZ⟩

end
end Cb

