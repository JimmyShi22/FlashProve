-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupNewRideWFresh.lean: this file is for toys (a toy: a small example instance). This file
is on a closing whose riders give a part of the further witness back. Under the hypotheses of its
statements, the one sending of such a closing lays down the masks that stand in the riders: both
clauses of `LdRefS.New` (Cb/Req1/LdReqRefLay.lean).

Definitions, statements as theorems, proofs. Generic: abstract fields, variable codes.
Rider (lean/GLOSSARY.md): a further oracle message that a closing's one sending sends with the
closing's own new messages (`RideD`, Cb/Ld/LdGroupNewRide.lean).
Further witness (lean/GLOSSARY.md): the part of a stage's witness beside the messages of the open
oracle messages (`LdStage`, Cb/Req1/LdSegKit.lean).

Cb/Ld/LdGroupNewRideFresh.lean and Cb/Ld/LdGroupRideStdFresh.lean, said again for the closing of
Cb/Ld/LdGroupNewRideW.lean (`V.closeRW`: the same members' senders; of the further witness rst is
handed on, bkR reads the whole back off the riders and what was handed on). The proofs are the same:
freshness at a sender made from members' senders (Cb/Ld/LdSendMemOwn.lean) asks nothing of what is
handed on.

Main names:
  `stdNewW_fresh`, `stdNewW_cutQuiet`: for any riders with a split XR of their coins (free coins,
    pad coins): as `stdNewR_fresh`, `stdNewR_cutQuiet` (Cb/Ld/LdGroupNewRideFresh.lean), each under
    the hypotheses of its statement.
  `V.rideFactW`, `rideStdW_fresh`, `rideStdW_cutQuiet`: I → E finite and nonempty; at riders under
    the standard sender of a layout Y, masks at any injective family of free entries: from
    `V.OK L t` and `Y.OK tR` alone (`rideStdW_fresh`). `rideStdW_cutQuiet` is on two witnesses whose
    wide readings differ by the overwriting (`hw`).
The reading holds the whole further witness that is handed on (rst of the old one), not what went
into the riders' data; the riders' data entries are read as entries.
In all of them the group's set of common long positions, `G.P`, is nonempty (the closing needs it).

Limits: this file says nothing on any instance. This file gives no instance that meets its
hypotheses, so as far as this file shows its theorems may hold of nothing.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupNewRideW
import Cb.Ld.LdGroupRideStdFresh
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

section
variable {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  {Sh : GShape G} {kp : S.O → Prop} [DecidablePred kp] {Hd : GHeld Sh kp} {Pn : Type} [Fintype Pn]
  (V : StdNew Hd Pn) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  {St₀ Wp : Type} {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (w0 : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp) (L t tl : ℕ)
  (Rd : RideD E ((Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp)) (Wp' : Type)
  (rst : Wp → Wp') (bkR : Rd.N.Msg → Wp' → Wp)

/-- For `G.P` nonempty and under the hypotheses of its statement: the one sending is fresh for the
wide fact of masks that stand in riders. -/
theorem stdNewW_fresh (XR : MemSplit Rd.m) {Mb M0 : Type} [Fintype Mb] [Nonempty Mb] [Fintype M0]
    [Nonempty M0] (εR : (∀ b, XR.Fr b) ≃ Mb × M0) (RdOld : (Hd.foldD Sb sl Z A₀).tgt.S.Ent → Prop)
    (RrOld : (Hd.foldD Sb sl Z A₀).tgt.S.O → Prop) (RdR own : Rd.N.Ent → Prop)
    (val : Mb → Rd.N.Ent → E) (h : V.OK L t)
    (hH : ∀ b, (Rd.m b).N.Hides ((Rd.N.om b).C.budT (Rd.t b))) (hX : XR.Unif)
    (hs : ∀ n, own n → RdR n)
    (ho : ∀ w M k₀ (η : ∀ b, XR.Pd b) (n : Rd.N.Ent), own n →
      (Rd.m n.1).upM ((Rd.m n.1).put w ((XR.κ n.1).symm (εR.symm (M, k₀) n.1, η n.1))) n.2 =
        val M n)
    (hf : ∀ w M M' k₀ (η η' : ∀ b, XR.Pd b) (n : Rd.N.Ent), RdR n → ¬ own n →
      (Rd.m n.1).upM ((Rd.m n.1).put w ((XR.κ n.1).symm (εR.symm (M, k₀) n.1, η n.1))) n.2 =
        (Rd.m n.1).upM ((Rd.m n.1).put w ((XR.κ n.1).symm (εR.symm (M', k₀) n.1, η' n.1))) n.2) :
    (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).snd.link.H.Fresh
      (Hd.foldD Sb sl Z A₀).tgt.J.rels.rel
      (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).snd.link.P.bud
      ((V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).snd.tgt.wideFact
        ((Hd.foldD Sb sl Z A₀).tgt.S.sumP (V.N.N₀.sum Rd.N) RdOld (V.rdR Sb sl Z A₀ Rd RdR))
        ((Hd.foldD Sb sl Z A₀).tgt.S.sumO (V.N.N₀.sum Rd.N) RrOld fun _ => False)
        ((Hd.foldD Sb sl Z A₀).tgt.S.sumP
          (V.N.N₀.sum Rd.N) (fun _ => False) (V.ownR Sb sl Z A₀ Rd own))
        Mb fun M =>
          (Hd.foldD Sb sl Z A₀).tgt.S.sumV
            (V.N.N₀.sum Rd.N) (fun _ => 0) (V.valR Sb sl Z A₀ Rd (val M))).kc
      Mb ((V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).snd.tgt.wideFact
        ((Hd.foldD Sb sl Z A₀).tgt.S.sumP (V.N.N₀.sum Rd.N) RdOld (V.rdR Sb sl Z A₀ Rd RdR))
        ((Hd.foldD Sb sl Z A₀).tgt.S.sumO (V.N.N₀.sum Rd.N) RrOld fun _ => False)
        ((Hd.foldD Sb sl Z A₀).tgt.S.sumP
          (V.N.N₀.sum Rd.N) (fun _ => False) (V.ownR Sb sl Z A₀ Rd own))
        Mb fun M =>
          (Hd.foldD Sb sl Z A₀).tgt.S.sumV
              (V.N.N₀.sum Rd.N) (fun _ => 0) (V.valR Sb sl Z A₀ Rd (val M))).put := by
  refine memOwn_fresh (Hd.foldD Sb sl Z A₀).tgt (V.N.N₀.sum Rd.N) (Sig.Seeds.indep _)
    Wp' (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).snd.bk
    (Sum.elim (fun _ => L) Rd.L) (Sum.elim (fun _ => t) Rd.t) (V.memR Sb sl Z A₀ w0 Rd)
    (fun w => (w.1, rst w.2.2)) w0 (V.splitR Sb sl Z A₀ w0 Rd XR) Mb M0
    (V.epsR Sb sl Z A₀ w0 Rd XR εR) RdOld (V.rdR Sb sl Z A₀ Rd RdR) RrOld
    (V.ownR Sb sl Z A₀ Rd own) (fun M => V.valR Sb sl Z A₀ Rd (val M))
    (stdNewR_unif V Sb sl Z A₀ w0 L t Rd XR h hX) ?_ ?_ ?_ ?_
  · rintro ((_ | k) | b)
    · exact stdM_hides V.Mc h.1 _ _
    · exact stdM_hides (V.Mn k) (h.2 k) _ _
    · exact hH b
  · rintro ⟨a | b, j⟩ hn
    · exact hn.elim
    · exact hs ⟨b, j⟩ hn
  · rintro w M k₀ η ⟨a | b, j⟩ hn
    · exact hn.elim
    · exact ho w M k₀ (fun b => η (.inr b)) ⟨b, j⟩ hn
  · rintro w M M' k₀ η η' ⟨(_ | k) | b, j⟩ h1 h2
    · exact stdNewR_noPad V Sb sl Z A₀ w0 w ⟨none, j⟩ h1 (η (.inl none)) (η' (.inl none))
    · exact stdNewR_noPad V Sb sl Z A₀ w0 w ⟨some k, j⟩ h1 (η (.inl (some k))) (η' (.inl (some k)))
    · exact hf w M M' k₀ (fun b => η (.inr b)) (fun b => η' (.inr b)) ⟨b, j⟩ h1 h2

/-- For `G.P` nonempty and under the hypotheses of its statement: the cut of the locations does not
look. -/
theorem stdNewW_cutQuiet {Mb : Type} [Fintype Mb] [Nonempty Mb]
    (RdOld : (Hd.foldD Sb sl Z A₀).tgt.S.Ent → Prop) (RrOld : (Hd.foldD Sb sl Z A₀).tgt.S.O → Prop)
    (RdR own : Rd.N.Ent → Prop) (val : Mb → Rd.N.Ent → E)
    (w w' : (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.src.J.W) (M : Mb)
    (hw : ((V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).snd.tgt.wideFact
        ((Hd.foldD Sb sl Z A₀).tgt.S.sumP (V.N.N₀.sum Rd.N) RdOld (V.rdR Sb sl Z A₀ Rd RdR))
        ((Hd.foldD Sb sl Z A₀).tgt.S.sumO (V.N.N₀.sum Rd.N) RrOld fun _ => False)
        ((Hd.foldD Sb sl Z A₀).tgt.S.sumP
          (V.N.N₀.sum Rd.N) (fun _ => False) (V.ownR Sb sl Z A₀ Rd own))
        Mb fun M =>
          (Hd.foldD Sb sl Z A₀).tgt.S.sumV
            (V.N.N₀.sum Rd.N) (fun _ => 0) (V.valR Sb sl Z A₀ Rd (val M))).kc w' =
      ((V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).snd.tgt.wideFact
          ((Hd.foldD Sb sl Z A₀).tgt.S.sumP (V.N.N₀.sum Rd.N) RdOld (V.rdR Sb sl Z A₀ Rd RdR))
          ((Hd.foldD Sb sl Z A₀).tgt.S.sumO (V.N.N₀.sum Rd.N) RrOld fun _ => False)
          ((Hd.foldD Sb sl Z A₀).tgt.S.sumP
            (V.N.N₀.sum Rd.N) (fun _ => False) (V.ownR Sb sl Z A₀ Rd own))
          Mb fun M =>
            (Hd.foldD Sb sl Z A₀).tgt.S.sumV
              (V.N.N₀.sum Rd.N) (fun _ => 0) (V.valR Sb sl Z A₀ Rd (val M))).put
        M (((V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).snd.tgt.wideFact
          ((Hd.foldD Sb sl Z A₀).tgt.S.sumP (V.N.N₀.sum Rd.N) RdOld (V.rdR Sb sl Z A₀ Rd RdR))
          ((Hd.foldD Sb sl Z A₀).tgt.S.sumO (V.N.N₀.sum Rd.N) RrOld fun _ => False)
          ((Hd.foldD Sb sl Z A₀).tgt.S.sumP
            (V.N.N₀.sum Rd.N) (fun _ => False) (V.ownR Sb sl Z A₀ Rd own))
          Mb fun M =>
            (Hd.foldD Sb sl Z A₀).tgt.S.sumV
              (V.N.N₀.sum Rd.N) (fun _ => 0) (V.valR Sb sl Z A₀ Rd (val M))).kc w)) :
    (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.cut
        ((V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.S.msgs w'.1) =
      (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.cut
        ((V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.S.msgs w.1) := by
  have hA :=
    (segWide_alike (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).snd.tgt _ _ _ Mb _ w w' M hw).1
  exact stdNewW_cut_congr V Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR _ _ fun n hn =>
    hA ⟨.inr (.inl n.1), n.2⟩ hn fun hh => hh

end

section
variable {F E B Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Fintype B]
  {S : Sig E} {G : Grp S} [Nonempty G.P] {Sh : GShape G} {kp : S.O → Prop} [DecidablePred kp]
  {Hd : GHeld Sh kp} {Pn : Type} [Fintype Pn] (V : StdNew Hd Pn) (Sb : B → Type)
  (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) {St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (w0 : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp) (L t tl : ℕ) (N : Sig E)
  (Y : N.StdL F)
  (dat : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp → ∀ a, Y.Dt a → E)
  (LR tR : N.O → ℕ) (Wp' : Type) (rst : Wp → Wp') (bkR : N.Msg → Wp' → Wp) {I : Type}
  (pl : I → Σ a, Y.Fr a)

/-- The wide fact of masks at free entries of standard riders. -/
def StdNew.rideFactW [Fintype (I → E)] [Nonempty (I → E)]
    (RdOld : (Hd.foldD Sb sl Z A₀).tgt.S.Ent → Prop)
    (RrOld : (Hd.foldD Sb sl Z A₀).tgt.S.O → Prop) :
    MaskFact (V.closeRW Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR)
        Wp' rst bkR).snd.tgt.J.W :=
  (V.closeRW Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR)
      Wp' rst bkR).snd.tgt.wideFact
    ((Hd.foldD Sb sl Z A₀).tgt.S.sumP
      (V.N.N₀.sum N) RdOld (V.rdR Sb sl Z A₀ (rideStdD Sb sl Z A₀ w0 N Y dat LR tR) Y.NoPad))
    ((Hd.foldD Sb sl Z A₀).tgt.S.sumO (V.N.N₀.sum N) RrOld fun _ => False)
    ((Hd.foldD Sb sl Z A₀).tgt.S.sumP (V.N.N₀.sum N) (fun _ => False)
      (V.ownR Sb sl Z A₀ (rideStdD Sb sl Z A₀ w0 N Y dat LR tR) (Y.ownP pl)))
    (I → E) fun M =>
      (Hd.foldD Sb sl Z A₀).tgt.S.sumV (V.N.N₀.sum N) (fun _ => 0)
        (V.valR Sb sl Z A₀ (rideStdD Sb sl Z A₀ w0 N Y dat LR tR) (Y.valP pl M))

/-- For `G.P` nonempty and under the hypotheses of its statement: the one sending is fresh for it.
-/
theorem rideStdW_fresh [Fintype (I → E)] [Nonempty (I → E)] (hpl : Function.Injective pl)
    (RdOld : (Hd.foldD Sb sl Z A₀).tgt.S.Ent → Prop) (RrOld : (Hd.foldD Sb sl Z A₀).tgt.S.O → Prop)
    (h : V.OK L t) (hY : Y.OK tR) :
    (V.closeRW Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR)
        Wp' rst bkR).snd.link.H.Fresh
      (Hd.foldD Sb sl Z A₀).tgt.J.rels.rel
      (V.closeRW Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR)
        Wp' rst bkR).snd.link.P.bud
      (V.rideFactW Sb sl Z A₀ w0 L t tl N Y dat LR tR Wp' rst bkR pl RdOld RrOld).kc (I → E)
      (V.rideFactW Sb sl Z A₀ w0 L t tl N Y dat LR tR Wp' rst bkR pl RdOld RrOld).put := by
  classical
  have hinj : Function.Injective fun i => Y.entF (pl i) := Y.entF_injective.comp hpl
  refine stdNewW_fresh V Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR) Wp' rst bkR
    (Y.memSplit dat w0) (Y.epsAt pl hpl) RdOld RrOld Y.NoPad (Y.ownP pl) (Y.valP pl) h hY.hides
    (stdL_memUnif Y dat w0 hY) ?_ ?_ ?_
  · rintro n ⟨i, rfl⟩
    exact ⟨_, rfl⟩
  · rintro w M k₀ η n ⟨i, rfl⟩
    refine (hY.lay (pl i).1 _ _ (Sum.inl (Sum.inr (pl i).2))).trans
      (Eq.trans ?_ (hinj.extend_apply M _ i).symm)
    exact Y.splitAt_symm_at pl hpl (fun _ => M, k₀) i
  · rintro w M M' k₀ η η' ⟨a, j⟩ ⟨x, hx⟩ ho
    have hx' : j = (Y.ν a).symm (Sum.inl x) := hx
    show Y.upM a (Y.msgOf a (Sum.elim (dat w a) ((Y.epsAt pl hpl).symm (M, k₀) a)) (η a)) j =
      Y.upM a (Y.msgOf a (Sum.elim (dat w a) ((Y.epsAt pl hpl).symm (M', k₀) a)) (η' a)) j
    rw [hx']
    rcases x with d | u
    · rw [hY.lay, hY.lay]
      rfl
    · have hu : ∀ i, pl i ≠ ⟨a, u⟩ := fun i hi => ho ⟨i, by rw [hx', hi]; rfl⟩
      rw [hY.lay, hY.lay]
      show (Y.splitAt pl hpl).symm (fun _ => M, k₀) a u =
        (Y.splitAt pl hpl).symm (fun _ => M', k₀) a u
      exact (Y.splitAt_symm_off pl hpl (fun _ => M, k₀) ⟨a, u⟩ hu).trans
        (Y.splitAt_symm_off pl hpl (fun _ => M', k₀) ⟨a, u⟩ hu).symm

/-- For `G.P` nonempty and under the hypotheses of its statement: the cut of the locations does not
look at it. -/
theorem rideStdW_cutQuiet [Fintype (I → E)] [Nonempty (I → E)]
    (RdOld : (Hd.foldD Sb sl Z A₀).tgt.S.Ent → Prop) (RrOld : (Hd.foldD Sb sl Z A₀).tgt.S.O → Prop)
    (w w' : (V.closeRW Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR)
      Wp' rst bkR).loc.src.J.W)
    (M : I → E)
    (hw : (V.rideFactW Sb sl Z A₀ w0 L t tl N Y dat LR tR Wp' rst bkR pl RdOld RrOld).kc w' =
      (V.rideFactW Sb sl Z A₀ w0 L t tl N Y dat LR tR Wp' rst bkR pl RdOld RrOld).put
        M ((V.rideFactW Sb sl Z A₀ w0 L t tl N Y dat LR tR Wp' rst bkR pl RdOld RrOld).kc w)) :
    (V.closeRW Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR) Wp' rst bkR).loc.cut
        ((V.closeRW Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR)
          Wp' rst bkR).loc.S.msgs w'.1) =
      (V.closeRW Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR) Wp' rst bkR).loc.cut
        ((V.closeRW Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR)
          Wp' rst bkR).loc.S.msgs w.1) :=
  stdNewW_cutQuiet V Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR)
    Wp' rst bkR RdOld RrOld Y.NoPad (Y.ownP pl) (Y.valP pl) w w' M hw

end
end Cb
