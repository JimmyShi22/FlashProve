-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefPackSLay.lean: under the hypotheses of its statement (`refPackS_cross`), masks
cross a reference segment whose closing comes from a bundle, with riders: of the closing only
conditions on places, `Rd.OK` and `Rd.Far` are left.

A definition, statements as theorems, proofs: wiring of Cb/Ld/LdGroupLinkRef.lean,
Cb/Ld/LdGroupNewRide.lean, Cb/Ld/LdGroupNewCut.lean into Cb/Req1/LdReqRefLayProofs.lean. Nothing of
a text is rendered here.

Why: Cb/Req1/LdReqRefLay.lean: "the wide fact crosses a reference segment" (`ldReqRefLay_cross`)
asks six things of the closing: two of the link's honest prover, one on the group's members, two of
the one sender, one of the cut. The names below are at S := `LdRefS.ofPack ..`
(Cb/Req1/LdSegRefPackS.lean).
Names: `LdStage.wideFact`: Cb/Req1/LdSegCarry.lean; `LdRefS.Carries`, `LdRefS.Enters`:
Cb/Req1/LdReqRefLay.lean; `LdCloseD.cutN`: Cb/Req1/LdSegFit.lean.

Main names:
  `Rd.Far`: a condition on the riders: their senders read the further witness alone, not the pairs
    of the oracle messages that are open.
  `refPackS_close`: five of the six are theorems: of the witness the link reads the group's members
    only; it hands the rest on; the one sender's laws (from `Rd.OK`); two witnesses with the same
    further part give the same messages and the same rest (`(Sn.rest w).2`) (the new messages hold
    the witness of the open test; from `Rd.Far`); the cut reads entries of the new messages that
    are no pads.
  `refPackS_cross`: for pp the characteristic of E, `Nonempty I.C.E0.Str`, Mk finite and not empty:
    the wide fact crosses: S.Carries g' (the wide fact behind the locations), from: what the body
    asks (as in ldReqRefLay_cross); the members: every oracle message with "mem" is shown whole
    (entries and encoding randomness) and holds no own entry; Rd.OK, Rd.Far; RdN holds of every
    entry of a new message that is no pad; the entry step hands g' on.

Limits: this file says nothing on masks that are coins of a rider (laid down by the one sending:
S.New). It does not say that the conditions on places can be met. No theorem of this library states
that the hypotheses of `refPackS_cross` can be met together.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefPackS
import Cb.Ld.LdGroupLinkRef
import Cb.Ld.LdGroupNewCut

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

/-- The riders' senders read the further witness alone: not the pairs of the oracle messages that
are open. -/
def RideD.Far {E Wl Wr : Type} [Field E] (Rd : RideD E (Wl × Wr)) : Prop :=
  ∀ b (w w' : Wl × Wr) k, w'.2 = w.2 → (Rd.m b).put w' k = (Rd.m b).put w k

section
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {a : LdStage E Kc} (A : LdRefD E Kc I)
  (Z : Evader E A.Gr.B) {mem kp : A.Xa.Q.T.O → Prop} [DecidablePred kp] {clP : {o // kp o} → Prop}
  {Pn : Type} [Fintype Pn] {d e t : ℕ} {Lst mC mS mW : ℕ → ℕ} {L L₂ t₂ : ℕ}
  (pk : GPack A.Xa.Q.T mem kp clP Pn d e t Lst mC mS mW L L₂ t₂) (Zb : Evader E (pk.G.Row Unit))
  (St₁ : Type) (fz : A.X.bt.par.Mid → St₁)
  (A₀c : Rels Kc St₁ I.C.E0 ((A.Xa.Q.T.sub kp).Msg × (I.C.PIdx × (A.W₁ × A.Gh))))
  (dw : A.Xa.Q.T.Wit × (I.C.PIdx × (A.W₁ × A.Gh)))
  (w0 : (pk.fold (fun _ : Unit => GPack.Sx (fun _ : A.Gr.B => A.Gr.Sx) Z)
      (pk.row1 (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z) Zb A₀c).tgt.S.Wit ×
    (pk.fold (fun _ : Unit => GPack.Sx (fun _ : A.Gr.B => A.Gr.Sx) Z)
      (pk.row1 (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z) Zb A₀c).tgt.Wp)
  (tl : ℕ)
  (Rd : RideD E
    ((pk.fold (fun _ : Unit => GPack.Sx (fun _ : A.Gr.B => A.Gr.Sx) Z)
        (pk.row1 (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z) Zb A₀c).tgt.S.Wit ×
      (pk.fold (fun _ : Unit => GPack.Sx (fun _ : A.Gr.B => A.Gr.Sx) Z)
        (pk.row1 (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z) Zb A₀c).tgt.Wp))
  (f : a.X → Option A.V.Fp.s0.X) (g : ExtMap a.Ex A.V.Fp.s0.Ex)
  (m : a.X × a.W → A.V.Fp.s0.X × A.V.Fp.s0.W) (back : a.X × a.Ex.Str → A.V.Fp.s0.W → a.W)

/-- Under `hR`, `hF`: five of the closing's six premises of "the wide fact crosses a reference
segment", at `LdRefS.ofPack ..`: of the witness the link reads the group's members only; it hands
the rest on; the one sender's laws; it does not look at the open oracle messages; the cut reads
entries of the new messages that are no pads. -/
theorem refPackS_close (hR : Rd.OK) (hF : Rd.Far) :
    (∀ (w w' : (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g
          m back).K.R.c1.fold.src.J.W) x c ρ,
        (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).K.R.c1.fold.G.wit w'.1 =
          (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).K.R.c1.fold.G.wit w.1 →
        (((LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).l.H.strat w' x c).run ρ).1 =
          (((LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).l.H.strat w x c).run ρ).1 ∧
        (((LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).l.H.strat w' x c).run ρ).2.1 =
          (((LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).l.H.strat
            w x c).run ρ).2.1 ∧
        (((LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).l.H.strat
            w' x c).run ρ).2.2.1 =
          (((LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).l.H.strat w x c).run
            ρ).2.2.1) ∧
    (∀ (w : (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).K.R.c1.fold.src.J.W) x c ρ,
      (((LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).l.H.strat w x c).run ρ).2.2.2 =
        ((LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).K.R.c1.fold.S.res
            (T := OMsg.Wit)
            (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).K.R.c1.fold.kp w.1,
          w.2)) ∧
    (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Qc.Sn.Laws
      ((LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).K.R.c1.fold.tgt.S.backN
        (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Qc.N
        (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Qc.snd.bk) ∧
    (∀ w w' : (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).K.R.c1.fold.tgt.W, w'.2 =
        w.2 →
      (∀ k, (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Qc.Sn.put w' k =
        (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Qc.Sn.put w k) ∧
      ((LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Qc.Sn.rest w').2 =
        ((LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Qc.Sn.rest w).2) ∧
    (∀ (RdN : (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Qc.N.Ent → Prop),
      (∀ n : pk.V.N.N₀.Ent, ¬ pk.V.IsPad n → RdN ⟨.inl n.1, n.2⟩) →
      ∀ m₁ m₂ : (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Qc.N.Msg,
        (∀ n : (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Qc.N.Ent,
          RdN n → m₂ n.1 n.2 = m₁ n.1 n.2) →
        (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Qc.cutN m₂ =
          (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Qc.cutN m₁) := by
  refine ⟨fun w w' x c ρ h =>
      ldGroup_link_run pk.Hd (fun _ : Unit => GPack.Sx (fun _ : A.Gr.B => A.Gr.Sx) Z)
        (pk.row1 (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z) Zb A₀c pk.hc dw d t Lst mC mS mW L w w' x c
        ρ h,
    fun w x c ρ =>
      ldGroup_link_carry pk.Hd (fun _ : Unit => GPack.Sx (fun _ : A.Gr.B => A.Gr.Sx) Z)
        (pk.row1 (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z) Zb A₀c pk.hc dw d t Lst mC mS mW L w x c ρ,
    (stdNewR_snd pk.V _ _ Zb A₀c w0 L₂ t₂ tl Rd pk.new hR).sender,
    fun w w' h => ⟨fun k => funext fun o => ?_, (show w'.2.2 = w.2.2 from congrArg Prod.snd h)⟩,
    fun RdN hN m₁ m₂ h => ?_⟩
  · rcases o with (_ | o) | b
    · show (pk.V.Mc.snd pk.V.datC w0).put w' (k (.inl none)) =
        (pk.V.Mc.snd pk.V.datC w0).put w (k (.inl none))
      funext j
      show Sum.elim (pk.V.datC w') _ _ = Sum.elim (pk.V.datC w) _ _
      unfold StdNew.datC
      rw [h]
    · show ((pk.V.Mn o).snd (pk.V.datN o) w0).put w' (k (.inl (some o))) =
        ((pk.V.Mn o).snd (pk.V.datN o) w0).put w (k (.inl (some o)))
      funext j
      show Sum.elim (pk.V.datN o w') _ _ = Sum.elim (pk.V.datN o w) _ _
      unfold StdNew.datN
      rw [h]
    · exact hF b w w' (k (.inr b)) h
  · exact stdNewR_cut_congr pk.V (fun _ : Unit => GPack.Sx (fun _ : A.Gr.B => A.Gr.Sx) Z)
      (pk.row1 (fun _ : A.Gr.B => A.Gr.Sx) A.Gr.sl Z) Zb A₀c w0 L₂ t₂ tl Rd m₁ m₂
      fun n hn => h ⟨.inl n.1, n.2⟩ (hN n hn)

/-- Under the hypotheses below, the wide fact crosses the reference segment, at `LdRefS.ofPack ..`:
of the closing only conditions on places, `Rd.OK` and `Rd.Far` are left. -/
theorem refPackS_cross (pp : ℕ) [CharP E pp] [Nonempty I.C.E0.Str] (W : LdRefW A) (F : LdRefF A)
    (κ : A.Gh → Kc) (own : A.Xa.Q.D.S.Ent → Prop) (Mk : Type) [Fintype Mk] [Nonempty Mk]
    (val : Mk → A.Xa.Q.D.S.Ent → E)
    (RdN : (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Qc.N.Ent → Prop)
    (RrN : (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Qc.N.O → Prop)
    (g' : MaskFact a.J.W) (hA : A.OK pp) (hG : A.Ghost κ) (hFo : F.OK pp)
    (hq : W.PassQ F own Mk val) (hM : A.Xa.A.MaskOK A.Xa.Dt)
    (hL : ∀ n, A.Xa.A.srAll A.Xa.Dt n → W.Rd2 n ∧ ¬ A.own2 own n) (hO : A.X.Own)
    (hT : ∀ n, A.Rdt n → W.Rd2 n ∧ ¬ A.own2 own n)
    (hmem : ∀ o, mem o → W.Rr2 o ∧ ∀ j, W.Rd2 ⟨o, j⟩ ∧ ¬ A.own2 own ⟨o, j⟩) (hR : Rd.OK)
    (hFar : Rd.Far) (hN : ∀ n : pk.V.N.N₀.Ent, ¬ pk.V.IsPad n → RdN ⟨.inl n.1, n.2⟩)
    (hE : (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Enters
      g' (W.fact own Mk val)) :
    (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Carries g'
      ((LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Qc.loc.tgt.wideFact
        ((LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).K.R.c1.fold.tgt.S.sumP
          (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Qc.N
          ((LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).K.R.c1.fold.S₁.subQ _
            ((LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).K.R.c1.fold.S.subQ
              (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).K.R.c1.fold.kp W.Rd2))
          RdN)
        ((LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).K.R.c1.fold.tgt.S.sumO
          (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Qc.N
          (fun a => W.Rr2 a.1.1) RrN)
        ((LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).K.R.c1.fold.tgt.S.sumP
          (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Qc.N
          ((LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).K.R.c1.fold.S₁.subQ _
            ((LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).K.R.c1.fold.S.subQ
              (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).K.R.c1.fold.kp
              (A.own2 own))) fun _ => False)
        Mk fun M =>
          (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).K.R.c1.fold.tgt.S.sumV
              (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).Qc.N
              ((LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).K.R.c1.fold.S₁.subF _
                ((LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).K.R.c1.fold.S.subF
                  (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back).K.R.c1.fold.kp
                  (A.val2 val M)))
              fun _ => 0) := by
  obtain ⟨c1, c2, c4, c5, c6⟩ := refPackS_close A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back hR hFar
  exact ldReqRefLay_cross E Kc pp I a (LdRefS.ofPack A Z pk Zb St₁ fz A₀c dw w0 tl Rd f g m back)
    W F κ own Mk val RdN RrN g' hA hG hFo hq hM hL hO hT c1 c2
    (fun o ho => hmem o ((pk.memI o).1 ho)) c4 (fun w w' _ _ h => c5 w w' h) (c6 RdN hN) hE

end
end Cb
