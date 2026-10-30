-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchLeadsMaps.lean: the law of the code switch over two written rounds, in the plain
form, carried along the library's own maps of written rounds, so that the test of work is in the
written counts.

Johnson/Top/H/SwitchLeads.lean carries the typed block's law along `Rd.carS`
(Johnson/Top/H/LocPlace.lean), whose readings are letters; that the written counts bear the typed
ones (`hFit`) is a premise there. A written verifier's message of a round with bits of work holds
these bits (`GChal`, Iop/Grind.lean). At readings that forget them every pattern of the bits is read
as one typed message, and the work does not enter the counts. The library's `Maps`
(OnBytes/Flat/CarrySMaps.lean) read a message whose test of work fails as nothing (`chalTo`,
OnBytes/Slice/Draws.lean); `Maps.fits` gives the counts, and `Maps.below_err` bounds them as shares
with the sampler's bias and the work counted. Here the same law is carried along such maps.
Definitions, statements and proofs; no new reasoning.
Main names:
  `OnBytes.Flat.leads_maps`: for any typed reduction with a law in the plain form
    (`Iop.Reduction.Leads`, Johnson/Desc/Plain/Leads.lean) and any maps M with `M.OK`: a text over
    the written rounds has the law at the counts `M.err ε`, if, where it says yes, all tests of work
    pass and the typed verifier puts something out at the image `M.view τ`.
  `selOut`, `selOut_is`: what the typed block puts out at a typed transcript; by definition
    (`out_eq`, `imp_eq`, Cb/Pv/Switch/SendLocRide.lean).
  `sel_law_maps`: `sel_law` with maps M in the readings' place: `hFit` is gone; the tie `hT` says:
    where the text says yes, all tests of work pass, and what stands behind gives the typed joint
    behind at `selOut (fa a) (M.view τ)`.
Limits: M is a letter and `M.OK` a premise: no maps into this block's rounds are written here
(OnBytes/Flat/CarrySForms.lean has the forms for a round that draws a seed and for one that draws
positions). Those of SwitchLeads.lean. Called at no value. No number is evaluated.

-/
import Johnson.Top.H.SwitchLeads
import OnBytes.Flat.CarrySMaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Flat
open Iop OnBytes.Maker OnBytes.Slice

/-- **A plain law carried to written rounds along the library's maps.** Where the text says yes, all
tests of work of the rounds that are read pass, and the typed verifier puts something out at the
image. The written counts are the maps' own. -/
theorem leads_maps {A B A' B' : Type} (K' : Reduction A' B') {ds : List RDT}
    (M : Maps ds K'.shape) (hM : M.OK) (ε : Err K'.shape)
    (out : A → Tr (uLT (_root_.Run.ckP .two) ds) → Option B) (fa : A → A') (on : A → Prop)
    (on' : A' → Prop)
    (Q : A → B → Prop) (Q' : A' → B' → Prop) (hon : ∀ a, on a → on' (fa a))
    (hout : ∀ a τ b, on a → out a τ = some b → M.pass τ = true ∧
      ∃ b', K'.out (fa a) (M.view τ) = some b' ∧ (Q' (fa a) b' → Q a b))
    (h : K'.Leads on' Q' ε) :
    (⟨uLT (_root_.Run.ckP .two) ds, out⟩ : Reduction A B).Leads on Q (M.err ε) :=
  leads_carryS ⟨uLT (_root_.Run.ckP .two) ds, out⟩ K' (fun _ => M.carry) ε (M.err ε)
    (fun _ => M.fits hM ε) fa on on' Q Q' hon
    (fun a τ b ha hb => by
      obtain ⟨hp, b', h1, h2⟩ := hout a τ b ha hb
      exact ⟨M.view τ, b', M.tr_of_pass τ hp, h1, h2⟩) h

end OnBytes.Flat

namespace Johnson.Top.H
open OnBytes.Slice Cb Iop IOR Johnson.Pack OnBytes.Tie.Pv.Switch OnBytes.Flat OnBytes.Maker

variable {S : Sig GE} {G : Grp S} [Nonempty G.P] {Sh : GShape G} {kp : S.O → Prop}
  [DecidablePred kp] (Hd : GHeld Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) G.C.J) (Z : Evader GE (G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (iJ : Sh.Cf.J → (sigOf cs l).Ent) (iQ : Sh.Cf.Q → (sigOf cs l).Ent)
  (t : ℕ) (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W) {Pw : Type} (Cw : LdCode GE Pw)

set_option quotPrecheck false in
local notation "zS" => switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw
set_option quotPrecheck false in
local notation "hdS" => (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.hd

/-- What the typed block puts out at a typed transcript: it never rejects. -/
noncomputable def selOut
    (a : (Cb.Pv.SendLoc.stage (zS).sw).X × (Cb.Pv.SendLoc.stage (zS).sw).Ex.Str)
    (τ : Tr (Cb.Pv.SendLocRide.R (zS)).shape) :
    (Cb.Pv.SendLoc.loc (zS).sw).tgt.X × ((Cb.Pv.SendLoc.loc (zS).sw).tgt.Ex.prod Cw.nat).Str :=
  ((((a.1.1.1, (τ.2.2.2.1, fun i => (zS).sw.C.T a.2.1.1 (τ.2.2.2.1 i))), a.1.1.2),
      (zS).sw.S₀.join (zS).sw.d.N (T := OMsg.Smp) a.1.2
        fun o => ((zS).sw.d.Sd.sd o τ.2.1, (Round.msgFst τ.2.2.1).2 o)),
    (Cb.Pv.SendLocRide.R (zS)).imp a.2 τ)

theorem selOut_is
    (a : (Cb.Pv.SendLoc.stage (zS).sw).X × (Cb.Pv.SendLoc.stage (zS).sw).Ex.Str)
    (τ : Tr (Cb.Pv.SendLocRide.R (zS)).shape) :
    (Cb.Pv.SendLocRide.R (zS)).red.out a τ =
      some (selOut Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw a τ) := rfl

/-- **The law of the code switch over two written rounds, along the library's maps**: the written
counts are the maps' own, with the test of work in them. -/
theorem sel_law_maps {d₁ d₂ : RDT} (M : Maps [d₁, d₂] (Cb.Pv.SendLocRide.R (zS)).shape)
    (hM : M.OK) {A Bt : Type} (hz : Cb.Pv.SendLocRide.OK (zS))
    (out : A → Tr (uLT (_root_.Run.ckP .two) [d₁, d₂]) → Option Bt)
    (fa : A → (Cb.Pv.SendLoc.stage (zS).sw).X × (Cb.Pv.SendLoc.stage (zS).sw).Ex.Str)
    (on : A → Prop) (hon : ∀ a, on a → (Cb.Pv.SendLocRide.inJ (zS)).on (fa a))
    (hpr : ∀ a, on a →
      ((Cb.Pv.SendLoc.stage (zS).sw).S.over (Cb.Pv.SendLoc.stage (zS).sw).A).on (fa a))
    (Rb : A → Bt → (Cb.Pv.SendLoc.loc (zS).sw).tgt.W → Prop)
    (hT : ∀ a τ b, on a → out a τ = some b → M.pass τ = true ∧
      ∀ w, Rb a b w →
        (Cb.Pv.SendLocRide.outJ (zS)).relR
          (selOut Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw (fa a) (M.view τ)) w) :
    (⟨uLT (_root_.Run.ckP .two) [d₁, d₂], out⟩ : Reduction A Bt).Leads on
      (fun a b => ∀ w, Rb a b w →
        ((Cb.Pv.SendLoc.stage (zS).sw).S.over (Cb.Pv.SendLoc.stage (zS).sw).A).relR (fa a)
            (selBack Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw w) ∧
          ∀ k : (hdS).K, ((hdS).o k).decW ((hdS).sW k (fa a).2.1.1) ((fa a).1.1.1.2 k) =
            some ((hdS).msg (cutSel cs l iJ iQ (newOf Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw w)).1 k))
      (M.err (Cb.Pv.SendLocRide.eps (zS))) := by
  refine (leads_maps (Cb.Pv.SendLocRide.R (zS)).red M hM (Cb.Pv.SendLocRide.eps (zS)) out fa on
    (Cb.Pv.SendLocRide.inJ (zS)).on
    (fun a b => on a → ∀ w, Rb a b w →
      ((Cb.Pv.SendLoc.stage (zS).sw).S.over (Cb.Pv.SendLoc.stage (zS).sw).A).relR (fa a)
          (selBack Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw w) ∧
        ∀ k : (hdS).K, ((hdS).o k).decW ((hdS).sW k (fa a).2.1.1) ((fa a).1.1.1.2 k) =
          some ((hdS).msg (cutSel cs l iJ iQ (newOf Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw w)).1 k))
    _ hon ?_ (ride_leads (zS) hz (selBack Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw)
      (sel_ext_is Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw))).conseq
    (fun _ h => h) fun a _ b ha _ hq => hq ha
  intro a τ b ha hb
  obtain ⟨hp, h3⟩ := hT a τ b ha hb
  refine ⟨hp, _, selOut_is Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw (fa a) (M.view τ),
    fun himp _ w hw => ?_⟩
  have hr := (himp w (h3 w hw)).resolve_right (not_not.2 (hpr a ha))
  exact ⟨hr, fun k => hr.2.2.1 k⟩

end Johnson.Top.H

#print axioms OnBytes.Flat.leads_maps
#print axioms Johnson.Top.H.selOut_is
#print axioms Johnson.Top.H.sel_law_maps
