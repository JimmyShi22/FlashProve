-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchLeads.lean: the law of the code switch ("SEND seed", "LOC") over two written
rounds, in the plain form, for every witness behind: the typed block, which the library has proved,
is carried to written rounds, not proved again.

The plain form (`Iop.Reduction.Leads`, Johnson/Desc/Plain/Leads.lean): on the statements with `on`
the prover has lost, at the start, towards "whatever the verifier puts out stands in Q to the
statement in front". `Know.toLeads` of that file gives it from the library's knowledge soundness
with "there is a witness" on both sides. Here the extractor is named: at this block its value hangs
on the witness behind alone (Johnson/Top/H/SwitchBack.lean), so Q can say: for EVERY witness w
behind, the joint in front holds at the extractor's value at w. The carriage is `leads_carryS`
(Johnson/Desc/Plain/Carry.lean) along the place's map `Rd.carS` (Johnson/Top/H/LocPlace.lean), with
`Rd.carS_tr` and `Rd.after` of that file. Definitions, statements and proofs; no new reasoning.
Main names:
  `ride_leads`: at any size of the kind: the typed law, where the extractor's value is a map E of
    the witness behind: `Know.toLeadsMap` (Johnson/Desc/Plain/KnowMap.lean) at the block's `hAt`.
  `switch_leads`: carried to two written rounds r₁, r₂: for a text `out` over them, a reading fa
    of its statements, and any Q that follows, where the text says yes, from the typed law at the
    statement that the typed block puts out at the readings.
  `selBack`, `sel_ext_is`: the map E at `switchSel` (Johnson/Top/H/SwitchSel.lean); by definition.
  `sel_law`: at `switchSel`: for every witness w of what stands behind (Rb, a letter, in the text's
    own terms): the relaxed relation in front holds at `selBack w`, and each held message's word
    decodes with its sample to what the cut reads off w's new messages.
Near kin: `loc_place` (LocPlace.lean) has this place's law for a run of the programs' routine.
Premises of `sel_law`: the kind's condition; that `on` gives the joint's condition and the promise
in front; `hFit`: the written counts bear the typed block's own errors along the readings
(`Rd.carS_fits` gives it from bounds on fibres); and the tie `hT`: where the text says yes, the seed
and the positions have readings, and what stands behind gives the typed joint behind.
Limits: the text, fa, the seven readings and Rb are letters, and `hT` is a premise: nothing here
says that a text of the programs meets it. Called at no value: at `on` := never, at Rb := never,
or at counts as large as a round's number of challenges it is true and says nothing. Those of
SwitchBack.lean. Nothing on an honest prover or on hiding.

-/
import Johnson.Top.H.LocPlace
import Johnson.Top.H.SwitchBack
import Johnson.Desc.Plain.Carry
import Johnson.Desc.Plain.KnowMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Switch
open OnBytes OnBytes.Slice Iop OnBytes.Flat Cb Cb.Pv

variable {K : Type} [Field K] [Fintype K] (s : SendLocRide.Size K)

/-- **The typed block's law in the plain form, the extractor named**: where the extractor's value is
a map E of the witness behind alone. -/
theorem ride_leads (h : SendLocRide.OK s) (E : (SendLoc.loc s.sw).tgt.W → (SendLoc.stage s.sw).W)
    (hE : ∀ a τ w, SendLocRide.ext s a τ w = E w) :
    (SendLocRide.R s).red.Leads (SendLocRide.inJ s).on
      (fun a b => ∀ w, (SendLocRide.outJ s).relR b w → (SendLocRide.inJ s).relR a (E w))
      (SendLocRide.eps s) :=
  (SendLocRide.hAt s h).toLeadsMap (fun _ _ w => E w) fun a τ _ w _ => hE a τ w

variable {s} {r₁ r₂ : Round} (ρ : Rd s r₁ r₂) {A B : Type}

/-- **Carried to two written rounds**, along the place's map. out: a text over the two written
rounds, as a reduction. -/
theorem switch_leads (h : SendLocRide.OK s)
    (E : (SendLoc.loc s.sw).tgt.W → (SendLoc.stage s.sw).W)
    (hE : ∀ a τ w, SendLocRide.ext s a τ w = E w) (out : A → Tr [r₁, r₂] → Option B)
    (fa : A → (SendLoc.stage s.sw).X × (SendLoc.stage s.sw).Ex.Str) (on : A → Prop)
    (Q : A → B → Prop) (hon : ∀ a, on a → (SendLocRide.inJ s).on (fa a)) (ε' : Err [r₁, r₂])
    (hFit : ρ.carS.Fits (SendLocRide.eps s) ε')
    (hout : ∀ a τ b, on a → out a τ = some b → ∃ sd Qs,
      ρ.rdSeed (ρ.view₁ τ.1 τ.2.1).drawn = some sd ∧
      ρ.rdPos (ρ.view₂ τ.2.2.1 τ.2.2.2.1).drawn = some Qs ∧
      ((∀ w, (SendLocRide.outJ s).relR (ρ.after (fa a) sd Qs (ρ.answ τ.2.2.1) τ.1) w →
        (SendLocRide.inJ s).relR (fa a) (E w)) → Q a b)) :
    (⟨[r₁, r₂], out⟩ : Reduction A B).Leads on Q ε' :=
  leads_carryS ⟨[r₁, r₂], out⟩ (SendLocRide.R s).red (fun _ => ρ.carS) (SendLocRide.eps s) ε'
    (fun _ => hFit) fa on (SendLocRide.inJ s).on Q _ hon
    (fun a τ b ha hb => by
      obtain ⟨sd, Qs, h1, h2, h3⟩ := hout a τ b ha hb
      exact ⟨_, ρ.after (fa a) sd Qs (ρ.answ τ.2.2.1) τ.1, ρ.carS_tr τ sd Qs h1 h2, rfl, h3⟩)
    (ride_leads s h E hE)

end OnBytes.Tie.Pv.Switch

namespace Johnson.Top.H
open OnBytes.Slice Cb Iop IOR Johnson.Pack OnBytes.Tie.Pv.Switch

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

/-- What the block's extractor hands back, as a map of the witness behind. -/
noncomputable def selBack (w : (Cb.Pv.SendLoc.loc (zS).sw).tgt.W) :
    (Cb.Pv.SendLoc.stage (zS).sw).W :=
  ((zS).sw.S₀.left (sigOf cs l) (T := OMsg.Wit) w.1,
    (cutSel cs l iJ iQ (newOf Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw w), w.2))

theorem sel_ext_is (a : (Cb.Pv.SendLoc.stage (zS).sw).X × (Cb.Pv.SendLoc.stage (zS).sw).Ex.Str)
    (τ : Tr (Cb.Pv.SendLocRide.R (zS)).shape) (w : (Cb.Pv.SendLoc.loc (zS).sw).tgt.W) :
    Cb.Pv.SendLocRide.ext (zS) a τ w = selBack Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw w := rfl

/-- **The law of the code switch over two written rounds, in the plain form, for every witness.**
out: a text over the two written rounds. Rb: what stands behind, in the text's own terms. The tie
hT: where the text says yes, the seed and the positions have readings, and what stands behind gives
the typed joint behind at the statement that the typed block puts out there. -/
theorem sel_law {r₁ r₂ : Round} (ρ : Rd (zS) r₁ r₂) {A Bt : Type}
    (hz : Cb.Pv.SendLocRide.OK (zS)) (out : A → Tr [r₁, r₂] → Option Bt)
    (fa : A → (Cb.Pv.SendLoc.stage (zS).sw).X × (Cb.Pv.SendLoc.stage (zS).sw).Ex.Str)
    (on : A → Prop) (hon : ∀ a, on a → (Cb.Pv.SendLocRide.inJ (zS)).on (fa a))
    (hpr : ∀ a, on a →
      ((Cb.Pv.SendLoc.stage (zS).sw).S.over (Cb.Pv.SendLoc.stage (zS).sw).A).on (fa a))
    (ε' : Err [r₁, r₂]) (hFit : ρ.carS.Fits (Cb.Pv.SendLocRide.eps (zS)) ε')
    (Rb : A → Bt → (Cb.Pv.SendLoc.loc (zS).sw).tgt.W → Prop)
    (hT : ∀ a τ b, on a → out a τ = some b → ∃ sd Qs,
      ρ.rdSeed (ρ.view₁ τ.1 τ.2.1).drawn = some sd ∧
      ρ.rdPos (ρ.view₂ τ.2.2.1 τ.2.2.2.1).drawn = some Qs ∧
      ∀ w, Rb a b w →
        (Cb.Pv.SendLocRide.outJ (zS)).relR (ρ.after (fa a) sd Qs (ρ.answ τ.2.2.1) τ.1) w) :
    (⟨[r₁, r₂], out⟩ : Reduction A Bt).Leads on
      (fun a b => ∀ w, Rb a b w →
        ((Cb.Pv.SendLoc.stage (zS).sw).S.over (Cb.Pv.SendLoc.stage (zS).sw).A).relR (fa a)
            (selBack Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw w) ∧
          ∀ k : (hdS).K, ((hdS).o k).decW ((hdS).sW k (fa a).2.1.1) ((fa a).1.1.1.2 k) =
            some ((hdS).msg (cutSel cs l iJ iQ (newOf Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw w)).1 k))
      ε' := by
  refine (switch_leads ρ hz (selBack Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw)
    (sel_ext_is Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw) out fa on
    (fun a b => on a → ∀ w, Rb a b w →
      ((Cb.Pv.SendLoc.stage (zS).sw).S.over (Cb.Pv.SendLoc.stage (zS).sw).A).relR (fa a)
          (selBack Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw w) ∧
        ∀ k : (hdS).K, ((hdS).o k).decW ((hdS).sW k (fa a).2.1.1) ((fa a).1.1.1.2 k) =
          some ((hdS).msg (cutSel cs l iJ iQ (newOf Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw w)).1 k))
    hon ε' hFit ?_).conseq
    (fun _ h => h) fun a _ b ha _ hq => hq ha
  intro a τ b ha hb
  obtain ⟨sd, Qs, h1, h2, h3⟩ := hT a τ b ha hb
  refine ⟨sd, Qs, h1, h2, fun himp _ w hw => ?_⟩
  have hr := (himp w (h3 w hw)).resolve_right (not_not.2 (hpr a ha))
  exact ⟨hr, fun k => hr.2.2.1 k⟩

end Johnson.Top.H

#print axioms OnBytes.Tie.Pv.Switch.ride_leads
#print axioms OnBytes.Tie.Pv.Switch.switch_leads
#print axioms Johnson.Top.H.sel_ext_is
#print axioms Johnson.Top.H.sel_law
