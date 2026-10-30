-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupRideStdFresh.lean: for toys: where the riders of a closing are sent by the standard
sender, the closing's one sending lays down the masks at the riders' free entries: both clauses
(`rideStd_fresh`, `rideStd_cutQuiet`), from conditions on codes, formats and samples. (not all
hypotheses are named here: see `rideStd_fresh`)

Definitions, statements as theorems, proofs. Generic: abstract fields, variable codes. A toy: a
small example instance. A closing: the last part of a test, of the link or of a segment. A rider: a
further oracle message that a closing's one sending sends with the closing's own new messages
(`RideD`, Cb/Ld/LdGroupNewRide.lean).
Cb/Ld/LdGroupNewRideFresh.lean shows the two clauses that Cb/Req1/LdReqRefLay.lean asks of a fact
which the one sending of a closing lays down, from a split of the riders' coins with three
conditions. (not all hypotheses are named here: see `stdNewR_fresh`) Here the riders are sent by the
standard sender of a layout Y (Cb/Ld/LdGroupRideStd.lean: `RideD.std`; Cb/Ld/LdSendStdL.lean: data
off the witness, free entries coins, pads), and the conditions are theorems.
`H.Fresh Ri bud kc Mk put`: for every (x, y, w) in Ri, every ρ outside `H.withheld w x` and every T
with `bud ρ T`: the distribution of `H.seen …` over uniform coins does not change if its third part
is overwritten by `put M` at an independent uniform M. In `rideStd_fresh` `Fresh` stands as the
conclusion.

Main names:
  `Y.memSplit dat w0`: the coins of a member: (its free entries, its pads).
  `stdL_memUnif`: `Y.OK t` ⇒ with the free entries fixed every member's answers are uniform over its
    pads.
  `Y.epsAt pl hpl`: all free entries as (those at pl, all others), for any injective family pl of
    free entries, in whichever members (Cb/Ld/LdSendStdOwn.lean: `splitAt`).
  `rideStd_fresh`: `G.P` nonempty, I → E finite and nonempty, hpl, `V.OK L t`, `Y.OK tR` ⇒ the
    sending's link is `Fresh` (`Honest.Fresh`, Ior/KnowCollRulesMask.lean) for the wide fact
    (`StdNew.rideFact`; `LdStage.wideFact`, Cb/Req1/LdSegCarry.lean): of what was left: any reading;
    of the new messages all entries that are no pads; of the riders all entries that are no pads; no
    new encoding randomness; own: the free entries at pl.
  `rideStd_cutQuiet`: for `G.P` nonempty and under the hypotheses of its statement, the cut of the
    locations does not look at it.

Limits: this file says nothing on any instance at this closing. This file gives no instance that
meets its hypotheses, so as far as this file shows its theorems may hold of nothing.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupRideStd
import Cb.Ld.LdGroupNewRideFresh
import Cb.Ld.LdSendStdOwn
import Cb.Req1.LdReqStdFresh
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

namespace Sig.StdL
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] {N : Sig E}
  (Y : N.StdL F) {W : Type} (dat : W → ∀ a, Y.Dt a → E) (w0 : W)

/-- the coins of a member: (its free entries, its pads) -/
@[reducible] def memSplit : MemSplit (Y.mem dat w0) where
  Fr := fun a => Y.Fr a → E
  Pd := fun a => Y.Pd a → F
  finPd := fun a => (Y.mem' dat w0 (fun _ _ => 0) a).finMk
  nePd := fun a => (Y.mem' dat w0 (fun _ _ => 0) a).neMk
  κ := fun _ => Equiv.refl _

/-- all free entries as (those at pl, all others) -/
def epsAt {I : Type} (pl : I → Σ a, Y.Fr a) (hpl : Function.Injective pl) :
    (∀ a, Y.Fr a → E) ≃ (I → E) × ({x : Σ a, Y.Fr a // ∀ i, pl i ≠ x} → E) :=
  (Y.splitAt pl hpl).trans (Equiv.prodCongr (Equiv.punitArrowEquiv _) (Equiv.refl _))

end Sig.StdL

theorem stdL_memUnif {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    {N : Sig E} (Y : N.StdL F) {W : Type} (dat : W → ∀ a, Y.Dt a → E) (w0 : W)
    {t : N.O → ℕ} (h : Y.OK t) : (Y.memSplit dat w0).Unif :=
  fun x a => Y.unifM' dat w0 h x a

section
variable {F E B Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Fintype B]
  {S : Sig E} {G : Grp S} [Nonempty G.P] {Sh : GShape G} {kp : S.O → Prop} [DecidablePred kp]
  {Hd : GHeld Sh kp} {Pn : Type} [Fintype Pn] (V : StdNew Hd Pn) (Sb : B → Type)
  (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) {St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (w0 : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp) (L t tl : ℕ) (N : Sig E)
  (Y : N.StdL F)
  (dat : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp → ∀ a, Y.Dt a → E)
  (LR tR : N.O → ℕ) {I : Type} (pl : I → Σ a, Y.Fr a)

/-- the riders -/
@[reducible] def rideStdD :
    RideD E ((Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp) :=
  RideD.std N Y dat w0 LR tR

/-- The wide fact of masks at free entries of standard riders. -/
def StdNew.rideFact [Fintype (I → E)] [Nonempty (I → E)]
    (RdOld : (Hd.foldD Sb sl Z A₀).tgt.S.Ent → Prop)
    (RrOld : (Hd.foldD Sb sl Z A₀).tgt.S.O → Prop) :
    MaskFact (V.closeR Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR)).snd.tgt.J.W :=
  (V.closeR Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR)).snd.tgt.wideFact
    ((Hd.foldD Sb sl Z A₀).tgt.S.sumP
      (V.N.N₀.sum N) RdOld (V.rdR Sb sl Z A₀ (rideStdD Sb sl Z A₀ w0 N Y dat LR tR) Y.NoPad))
    ((Hd.foldD Sb sl Z A₀).tgt.S.sumO (V.N.N₀.sum N) RrOld fun _ => False)
    ((Hd.foldD Sb sl Z A₀).tgt.S.sumP (V.N.N₀.sum N) (fun _ => False)
      (V.ownR Sb sl Z A₀ (rideStdD Sb sl Z A₀ w0 N Y dat LR tR) (Y.ownP pl)))
    (I → E) fun M =>
      (Hd.foldD Sb sl Z A₀).tgt.S.sumV (V.N.N₀.sum N) (fun _ => 0)
        (V.valR Sb sl Z A₀ (rideStdD Sb sl Z A₀ w0 N Y dat LR tR) (Y.valP pl M))

/-- For `G.P` nonempty and under the hypotheses of its statement: the one sending is fresh for
it (`StdNew.rideFact`). -/
theorem rideStd_fresh [Fintype (I → E)] [Nonempty (I → E)] (hpl : Function.Injective pl)
    (RdOld : (Hd.foldD Sb sl Z A₀).tgt.S.Ent → Prop) (RrOld : (Hd.foldD Sb sl Z A₀).tgt.S.O → Prop)
    (h : V.OK L t) (hY : Y.OK tR) :
    (V.closeR Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR)).snd.link.H.Fresh
      (Hd.foldD Sb sl Z A₀).tgt.J.rels.rel
      (V.closeR Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR)).snd.link.P.bud
      (V.rideFact Sb sl Z A₀ w0 L t tl N Y dat LR tR pl RdOld RrOld).kc (I → E)
      (V.rideFact Sb sl Z A₀ w0 L t tl N Y dat LR tR pl RdOld RrOld).put := by
  classical
  have hinj : Function.Injective fun i => Y.entF (pl i) := Y.entF_injective.comp hpl
  refine stdNewR_fresh V Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR)
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
look at it (`StdNew.rideFact`). -/
theorem rideStd_cutQuiet [Fintype (I → E)] [Nonempty (I → E)]
    (RdOld : (Hd.foldD Sb sl Z A₀).tgt.S.Ent → Prop) (RrOld : (Hd.foldD Sb sl Z A₀).tgt.S.O → Prop)
    (w w' : (V.closeR Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR)).loc.src.J.W)
    (M : I → E)
    (hw : (V.rideFact Sb sl Z A₀ w0 L t tl N Y dat LR tR pl RdOld RrOld).kc w' =
      (V.rideFact Sb sl Z A₀ w0 L t tl N Y dat LR tR pl RdOld RrOld).put
        M ((V.rideFact Sb sl Z A₀ w0 L t tl N Y dat LR tR pl RdOld RrOld).kc w)) :
    (V.closeR Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR)).loc.cut
        ((V.closeR Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR)).loc.S.msgs w'.1) =
      (V.closeR Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR)).loc.cut
        ((V.closeR Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR)).loc.S.msgs w.1) :=
  stdNewR_cutQuiet V Sb sl Z A₀ w0 L t tl (rideStdD Sb sl Z A₀ w0 N Y dat LR tR) RdOld RrOld Y.NoPad
    (Y.ownP pl) (Y.valP pl) w w' M hw

end
end Cb
