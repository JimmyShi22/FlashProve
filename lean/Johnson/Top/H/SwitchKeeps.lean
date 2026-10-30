-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchKeeps.lean: the code switch keeps the promise: outside what the prover may win,
at the block's own errors, no message that is open behind the block, old or new, has a collision at
its seed, and the carried joint's condition holds; under the same "has lost" as the block's
knowledge soundness.

The library states the block's knowledge soundness between joints whose condition (no open message
has a collision at its seed) is moved into the relaxed relation, or, which is the same, in the form
"into" (`HAtInto`, Cb/Pv/Switch/SendLocInto.lean): where the condition behind fails, the relation in
front holds at what the extractor hands back. A rule that lays blocks behind each other and hands
each block its condition from the law in front wants more: the condition behind holds, be the
statement in front true or false (it keeps the condition in front: that is asked). Two laws at one
list of errors join only at the sum of the errors. Here the two are had at once, from the library's
one statement, without opening its proof.
SendLocInto.lean says in its limits that every output statement meets the condition behind "is not
stated, and it is not so": that is said of every output, at all transcripts; here it is said outside
what the prover may win at these errors. The gap that is closed stands in the docstring of
`Reduction.KnowInto` (Ior/KnowColl.lean): to reach an output outside the condition counts as a win
of the prover "unless `ext a τ w` is a witness of a for every w": with the flag false it is none.
How. The base joint A₀ is a letter of the typed block. `flagJ A₀` lays a flag beside its further
witness: its relations ask that the flag be true; its condition is A₀'s. The caller at `flagJ A₀`
has the same rounds, verifier, errors and conditions, by definition. The extractor hands the flag
back untouched. So at a witness behind whose flag is false the relation in front is false, and the
library's statement says that the condition behind holds; at a witness whose flag is true it is the
statement at A₀. The first half alone would need no flag: a base joint whose relaxed relation never
holds would give it in the same way (not typed here). So it was in the library's statement all
along, which holds at every base joint. What the flag adds is that both halves stand under one "has
lost". Definitions, statements and proofs.
Main names:
  `flagJ`, `flagW`: the base joint with a flag; the extractor's default value with it.
  `flag_red`, `flag_eps`, `flag_onIn`, `flag_onOut`: the caller at `flagJ A₀` has the same
    reduction, errors and conditions: by definition. Controls: `sel_keeps` does not call them.
  `sel_keeps`: at `switchSel` (Johnson/Top/H/SwitchSel.lean), in the plain form
    (`Iop.Reduction.Leads`, Johnson/Desc/Plain/Leads.lean), between the library's joints with their
    conditions (`inJP`, `outJP`): the condition behind, and for every witness behind the relation in
    front at `selBack w`; at `eps`.
  `sel_keeps_lang`: so the block has `Reduction.Keeps` at the languages "there is a witness" of the
    two relaxed relations.
  `KeepsQ`, `keepsQ_of`: what the written-rounds laws conclude, and the step that they share.
  `sel_keeps_law`: over two written rounds along the place's readings (`Rd.carS`,
    Johnson/Top/H/LocPlace.lean). `sel_keeps_maps`: along the library's maps
    (Johnson/Top/H/SwitchLeadsMaps.lean).
Near kin: `Reduction.Keeps` (Johnson/Desc/Plain/Leads.lean) is the form "the promise behind is kept,
and a true statement behind gives a true statement in front": `sel_keeps` is that form for every
witness, the extractor named; `sel_keeps_lang` gives `Keeps` at the two languages.
`leads_map2_of_goodIn` (Johnson/Desc/Plain/FromGood.lean) has a conclusion
of the same form for a piece of a description, from that piece's `GoodIn`; here it is had of a typed
block, from the library's statement: neither can call the other. `Cb.alsoJ`
(Cb/Req1/LdSegRefRng.lean) and `Cb.ghostJ` (Cb/Req1/LdSegGhost.lean) lay a further part beside a
joint's witness in the same way, but their relaxed relations do not read it; `flagJ`'s does.
`Spec.ldSendFam_cnt` (Cb/Ld/LdSendFam.lean) counts, for any words sent, the joint seeds at which
some member has a collision: at most `ldSendFamErr`, which is this block's first error
(`SendLocRide.errs`). `sel_law`, `sel_law_maps` are these laws without the condition behind; their
ties ask the joint behind in the form "the relation holds or the condition fails", the ties here the
relation itself.
Limits: those of SwitchLeads.lean and SwitchLeadsMaps.lean. In the ties Pb and Rb are letters. The
condition behind is the typed one: of the words and at the seeds that the typed statement behind
has; of the messages that are held no more nothing is said behind. It is the law of the library's
typed block at a caller made of letters, not of a text of the programs. The errors are counts: that
the first is below the number of joint seeds is not said here (Johnson/G/SwitchCovers.lean bounds
both counts as shares at the callers `switchVec` of the written records). Where an error is as
large as its round's number of challenges (so at no positions, t = 0) all these laws say nothing,
the condition behind too.

-/
import Johnson.Top.H.SwitchLeadsMaps
import Cb.Pv.Switch.SendLocInto

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes.Slice Cb Iop IOR Johnson.Pack OnBytes.Tie.Pv.Switch OnBytes.Flat OnBytes.Maker

/-- A base joint with a flag beside the further witness: the relations ask that the flag be true. -/
def flagJ {Kc St₀ M Wp : Type} {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ (M × Wp)) :
    Rels Kc St₀ E₀ (M × (Wp × Bool)) where
  rel := fun x y w => A₀.rel x y (w.1, w.2.1) ∧ w.2.2 = true
  relR := fun a w => A₀.relR a (w.1, w.2.1) ∧ w.2.2 = true
  on := A₀.on
  core := fun w => A₀.core (w.1, w.2.1)

variable {S : Sig GE} {G : Grp S} [Nonempty G.P] {Sh : GShape G} {kp : S.O → Prop}
  [DecidablePred kp] (Hd : GHeld Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) G.C.J) (Z : Evader GE (G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))

/-- The extractor's default value, with the flag. -/
def flagW (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W) : (Hd.foldD Sb sl Z (flagJ A₀)).tgt.W :=
  (w₀.1, (w₀.2.1, (w₀.2.2, true)))

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (iJ : Sh.Cf.J → (sigOf cs l).Ent) (iQ : Sh.Cf.Q → (sigOf cs l).Ent)
  (t : ℕ) (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W) {Pw : Type} (Cw : LdCode GE Pw)

set_option quotPrecheck false in
local notation "zS" => switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw
set_option quotPrecheck false in
local notation "zF" => switchSel Hd Sb sl Z (flagJ A₀) cs l iJ iQ t (flagW Hd Sb sl Z A₀ w₀) Cw

/-- The caller at the joint with a flag is the same block: one reduction (rounds and verifier). This
and the next three hold by definition; they fail if the base joint ever enters the rounds. -/
theorem flag_red : (Cb.Pv.SendLocRide.R (zF)).red = (Cb.Pv.SendLocRide.R (zS)).red := rfl

/-- The same errors. -/
theorem flag_eps : Cb.Pv.SendLocRide.eps (zF) = Cb.Pv.SendLocRide.eps (zS) := rfl

/-- The same condition in front. -/
theorem flag_onIn (a : (Cb.Pv.SendLoc.stage (zS).sw).X × (Cb.Pv.SendLoc.stage (zS).sw).Ex.Str) :
    (Cb.Pv.SendLocRide.inJP (zF)).on a ↔ (Cb.Pv.SendLocRide.inJP (zS)).on a := Iff.rfl

/-- The same condition behind. -/
theorem flag_onOut (b : (Cb.Pv.SendLoc.loc (zS).sw).tgt.X ×
      ((Cb.Pv.SendLoc.loc (zS).sw).tgt.Ex.prod Cw.nat).Str) :
    (Cb.Pv.SendLocRide.outJP (zF)).on b ↔ (Cb.Pv.SendLocRide.outJP (zS)).on b := Iff.rfl

/-- **The typed block keeps the promise**: on the statements that keep the promise in front the
prover has lost, at the block's own errors, towards: what the verifier puts out keeps the promise
behind, and for every witness of the relation behind, the relation in front holds at what the
extractor hands back. -/
theorem sel_keeps (h : allMeet cs l = true) (hL : Hd.Laws) (hF : G.Fits) :
    (Cb.Pv.SendLocRide.R (zS)).red.Leads (Cb.Pv.SendLocRide.inJP (zS)).on
      (fun a b => (Cb.Pv.SendLocRide.outJP (zS)).on b ∧
        ∀ w, (Cb.Pv.SendLocRide.outJP (zS)).relR b w →
          (Cb.Pv.SendLocRide.inJP (zS)).relR a (selBack Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw w))
      (Cb.Pv.SendLocRide.eps (zS)) := fun a ha =>
  Doomed.mono _ _
    (fun τ hτ b hb => by
      have hτ' : ∀ (b' : (Cb.Pv.SendLoc.loc (zF).sw).tgt.X ×
            ((Cb.Pv.SendLoc.loc (zF).sw).tgt.Ex.prod Cw.nat).Str)
          (w' : (Cb.Pv.SendLoc.loc (zF).sw).tgt.W),
          (Cb.Pv.SendLocRide.R (zF)).red.out a τ = some b' →
          (Cb.Pv.SendLocRide.outJ (zF)).relR b' w' →
          (Cb.Pv.SendLocRide.inJ (zF)).relR a (Cb.Pv.SendLocRide.ext (zF) a τ w') := hτ
      refine ⟨?_, fun w hw => ?_⟩
      · by_contra hn
        have r := (hτ' b (fun _ => (fun _ => 0, fun _ => 0), (w₀.2.2, false)) hb
          (Or.inr hn)).resolve_right (not_not.2 ha)
        exact Bool.false_ne_true r.2.2.2.2
      · have r := (hτ' b (w.1, (w.2, true)) hb
          (Or.inl ⟨hw.1, hw.2.1, hw.2.2, rfl⟩)).resolve_right (not_not.2 ha)
        exact ⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1⟩)
    (Cb.Pv.SendLocRide.hAt (zF)
      (switchSel_ok Hd Sb sl Z (flagJ A₀) cs l iJ iQ t (flagW Hd Sb sl Z A₀ w₀) Cw h hL hF) a
      trivial)

/-- So the typed block has the form "the promise behind is kept, and a true statement behind gives a
true statement in front", at the languages "there is a witness". -/
theorem sel_keeps_lang (h : allMeet cs l = true) (hL : Hd.Laws) (hF : G.Fits) :
    (Cb.Pv.SendLocRide.R (zS)).red.Keeps (Cb.Pv.SendLocRide.inJP (zS)).on
      (Cb.Pv.SendLocRide.outJP (zS)).on (fun a => ∃ w, (Cb.Pv.SendLocRide.inJP (zS)).relR a w)
      (fun b => ∃ w, (Cb.Pv.SendLocRide.outJP (zS)).relR b w) (Cb.Pv.SendLocRide.eps (zS)) :=
  (sel_keeps Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw h hL hF).conseq (fun _ h => h)
    fun _ _ _ _ _ hq => ⟨hq.1, fun ⟨w, hw⟩ => ⟨_, hq.2 w hw⟩⟩

set_option quotPrecheck false in
local notation "hdS" => (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.hd

/-- What the law concludes of a statement in front (read as the typed a') and of what stands behind:
Pb: the promise behind, Rb: the relation behind, both in the text's own terms. -/
def KeepsQ {Bt : Type} (Pb : Bt → Prop) (Rb : Bt → (Cb.Pv.SendLoc.loc (zS).sw).tgt.W → Prop)
    (a' : (Cb.Pv.SendLoc.stage (zS).sw).X × (Cb.Pv.SendLoc.stage (zS).sw).Ex.Str) (b : Bt) : Prop :=
  Pb b ∧ ∀ w, Rb b w →
    (Cb.Pv.SendLocRide.inJP (zS)).relR a' (selBack Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw w) ∧
      ∀ k : (hdS).K, ((hdS).o k).decW ((hdS).sW k a'.2.1.1) (a'.1.1.1.2 k) =
        some ((hdS).msg (cutSel cs l iJ iQ (newOf Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw w)).1 k)

/-- The step that both roads share: from the typed law's conclusion at the typed statement
behind. -/
theorem keepsQ_of {Bt : Type} {Pb : Bt → Prop}
    {Rb : Bt → (Cb.Pv.SendLoc.loc (zS).sw).tgt.W → Prop}
    {a' : (Cb.Pv.SendLoc.stage (zS).sw).X × (Cb.Pv.SendLoc.stage (zS).sw).Ex.Str} {b : Bt}
    {b' : (Cb.Pv.SendLoc.loc (zS).sw).tgt.X × ((Cb.Pv.SendLoc.loc (zS).sw).tgt.Ex.prod Cw.nat).Str}
    (hP : (Cb.Pv.SendLocRide.outJP (zS)).on b' → Pb b)
    (hR : ∀ w, Rb b w → (Cb.Pv.SendLocRide.outJP (zS)).relR b' w)
    (h : (Cb.Pv.SendLocRide.outJP (zS)).on b' ∧
      ∀ w, (Cb.Pv.SendLocRide.outJP (zS)).relR b' w →
        (Cb.Pv.SendLocRide.inJP (zS)).relR a' (selBack Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw w)) :
    KeepsQ Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw Pb Rb a' b :=
  ⟨hP h.1, fun w hw => ⟨h.2 w (hR w hw), fun k => (h.2 w (hR w hw)).2.2.1 k⟩⟩

/-- **The law of the code switch over two written rounds, the promise behind kept**, along the
place's readings. -/
theorem sel_keeps_law {r₁ r₂ : Round} (ρ : Rd (zS) r₁ r₂) {A Bt : Type}
    (h : allMeet cs l = true) (hL : Hd.Laws) (hF : G.Fits)
    (out : A → Tr [r₁, r₂] → Option Bt)
    (fa : A → (Cb.Pv.SendLoc.stage (zS).sw).X × (Cb.Pv.SendLoc.stage (zS).sw).Ex.Str)
    (on : A → Prop) (hpr : ∀ a, on a → (Cb.Pv.SendLocRide.inJP (zS)).on (fa a))
    (ε' : Err [r₁, r₂]) (hFit : ρ.carS.Fits (Cb.Pv.SendLocRide.eps (zS)) ε')
    (Pb : A → Bt → Prop) (Rb : A → Bt → (Cb.Pv.SendLoc.loc (zS).sw).tgt.W → Prop)
    (hT : ∀ a τ b, on a → out a τ = some b → ∃ sd Qs,
      ρ.rdSeed (ρ.view₁ τ.1 τ.2.1).drawn = some sd ∧
      ρ.rdPos (ρ.view₂ τ.2.2.1 τ.2.2.2.1).drawn = some Qs ∧
      ((Cb.Pv.SendLocRide.outJP (zS)).on (ρ.after (fa a) sd Qs (ρ.answ τ.2.2.1) τ.1) → Pb a b) ∧
      ∀ w, Rb a b w →
        (Cb.Pv.SendLocRide.outJP (zS)).relR (ρ.after (fa a) sd Qs (ρ.answ τ.2.2.1) τ.1) w) :
    (⟨[r₁, r₂], out⟩ : Reduction A Bt).Leads on
      (fun a b => KeepsQ Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw (Pb a) (Rb a) (fa a) b) ε' :=
  leads_carryS ⟨[r₁, r₂], out⟩ (Cb.Pv.SendLocRide.R (zS)).red (fun _ => ρ.carS)
    (Cb.Pv.SendLocRide.eps (zS)) ε' (fun _ => hFit) fa on (Cb.Pv.SendLocRide.inJP (zS)).on _ _ hpr
    (fun a τ b ha hb => by
      obtain ⟨sd, Qs, h1, h2, h3, h4⟩ := hT a τ b ha hb
      exact ⟨_, ρ.after (fa a) sd Qs (ρ.answ τ.2.2.1) τ.1, ρ.carS_tr τ sd Qs h1 h2, rfl,
        keepsQ_of Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw h3 h4⟩)
    (sel_keeps Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw h hL hF)

/-- **The same along the library's maps**: the written counts are the maps' own. -/
theorem sel_keeps_maps {d₁ d₂ : RDT} (M : Maps [d₁, d₂] (Cb.Pv.SendLocRide.R (zS)).shape)
    (hM : M.OK) {A Bt : Type} (h : allMeet cs l = true) (hL : Hd.Laws) (hF : G.Fits)
    (out : A → Tr (uLT (_root_.Run.ckP .two) [d₁, d₂]) → Option Bt)
    (fa : A → (Cb.Pv.SendLoc.stage (zS).sw).X × (Cb.Pv.SendLoc.stage (zS).sw).Ex.Str)
    (on : A → Prop) (hpr : ∀ a, on a → (Cb.Pv.SendLocRide.inJP (zS)).on (fa a))
    (Pb : A → Bt → Prop) (Rb : A → Bt → (Cb.Pv.SendLoc.loc (zS).sw).tgt.W → Prop)
    (hT : ∀ a τ b, on a → out a τ = some b → M.pass τ = true ∧
      ((Cb.Pv.SendLocRide.outJP (zS)).on
        (selOut Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw (fa a) (M.view τ)) → Pb a b) ∧
      ∀ w, Rb a b w →
        (Cb.Pv.SendLocRide.outJP (zS)).relR
          (selOut Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw (fa a) (M.view τ)) w) :
    (⟨uLT (_root_.Run.ckP .two) [d₁, d₂], out⟩ : Reduction A Bt).Leads on
      (fun a b => KeepsQ Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw (Pb a) (Rb a) (fa a) b)
      (M.err (Cb.Pv.SendLocRide.eps (zS))) :=
  leads_maps (Cb.Pv.SendLocRide.R (zS)).red M hM (Cb.Pv.SendLocRide.eps (zS)) out fa on
    (Cb.Pv.SendLocRide.inJP (zS)).on _ _ hpr
    (fun a τ b ha hb => by
      obtain ⟨hp, h3, h4⟩ := hT a τ b ha hb
      exact ⟨hp, _, selOut_is Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw (fa a) (M.view τ),
        keepsQ_of Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw h3 h4⟩)
    (sel_keeps Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw h hL hF)

end Johnson.Top.H

#print axioms Johnson.Top.H.flag_red
#print axioms Johnson.Top.H.flag_eps
#print axioms Johnson.Top.H.flag_onIn
#print axioms Johnson.Top.H.flag_onOut
#print axioms Johnson.Top.H.sel_keeps
#print axioms Johnson.Top.H.sel_keeps_lang
#print axioms Johnson.Top.H.keepsQ_of
#print axioms Johnson.Top.H.sel_keeps_law
#print axioms Johnson.Top.H.sel_keeps_maps
