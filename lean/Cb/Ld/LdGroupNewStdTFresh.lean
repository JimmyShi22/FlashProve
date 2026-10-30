-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupNewStdTFresh.lean: this file is on the closing whose one sending is the standard
sending (`V.closeRT`: proved under the hypothesis of `stdNewT_eq`, Cb/Ld/LdGroupNewStdT.lean). Under
the hypotheses of its statements it lays down masks at free entries of its riders: both clauses of
"laid down by the one sending" (`LdRefS.New`, Cb/Req1/LdReqRefLay.lean), for the same wide fact
(`LdStage.wideFact`, Cb/Req1/LdSegCarry.lean) as for `V.closeRW`.

Definitions, statements as theorems, proofs: wiring, but for `stdM_noPad` and `stdNewT_fact`.
Rider (lean/GLOSSARY.md): a further oracle message that a closing's one sending sends with the
closing's own new messages (`RideD`, Cb/Ld/LdGroupNewRide.lean).
Locations (lean/GLOSSARY.md): the one-round step in which the prover sends nothing and the verifier
draws long positions of an open word and reads it there.

Cb/Ld/LdGroupNewStdT.lean: `V.closeRT`: the second half of a closing with riders, all but the sender
as in `V.closeRW` (Cb/Ld/LdGroupNewRideW.lean) at standard riders; its sending is `LdSendD.std` (an
equation, `stdNewT_eq`, if what is read back off the riders is read off their data).
Cb/Ld/LdGroupNewRideWFresh.lean has, for `V.closeRW`, the wide fact `V.rideFactW` (of what was left
any reading; of the new messages and of the riders all entries that are no pads; no new encoding
randomness; own: free entries of riders at any injective family of places) and, under the hypotheses
of their statements, the two clauses. The stage behind the two closings is the same term, so the
fact is a fact of both.
Here the first clause for `V.closeRT` comes from the general rule for standard sendings
(Cb/Req1/LdReqStdLay.lean: `ldReqStdLay_fresh`, along the equation); the second is that of
`V.closeRW` (the locations are the same term).

Main names:
  `stdNew_noPad`: an entry of a new message is no pad in the layout's sense iff it is none in the
    closing's sense.
  `stdM_noPad`: the same for one message (`StdM`).
  `stdNewT_fact`: I → E finite and nonempty; pl injective ⇒ `(V.closeRT ..).snd.tgt.wideFact ..`, at
    the layout's readings, = `V.rideFactW ..`.
  `stdNewT_fresh`: I → E finite and nonempty; `V.OK L t`, `Y₁.OK t₁`, what is read back off the
    riders is read off their data, pl injective ⇒ the link of `(V.closeRT ..).snd` is `Fresh` for
    `V.rideFactW ..`.
  `stdNewT_cutQuiet`: I → E finite and nonempty: overwriting the own masks does not change the cut
    of the locations.
In the last three the group's set of common long positions, `G.P`, is nonempty (the closing needs
it).

Limits: Its statements are about data structures of this library.
This file says nothing on any instance.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupNewStdT
import Cb.Ld.LdGroupNewRideWFresh
import Cb.Req1.LdReqStdLay

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

section
variable {E : Type} [Field E] [Fintype E] {S : Sig E} {G : Grp S} {Sh : GShape G} {kp : S.O → Prop}
  [DecidablePred kp] {Hd : GHeld Sh kp} {Pn : Type} [Fintype Pn] (V : StdNew Hd Pn)

omit [Field E] [Fintype E] in
theorem stdM_noPad {P : Type} [Fintype P] (M : StdM E P) (j : M.Cm.J) :
    (∃ x, j = (stdMNu (fun _ : Unit => M) ()).symm (Sum.inl x)) ↔ ¬ j = M.place (.inr ()) := by
  constructor
  · rintro ⟨x, rfl⟩ h
    have h2 := congrArg (stdMNu (fun _ : Unit => M) ()) h
    rw [Equiv.apply_symm_apply] at h2
    have h3 : stdMNu (fun _ : Unit => M) () (M.place (.inr ())) = Sum.inr () := by
      show Sum.map _ _ (M.place.symm (M.place (.inr ()))) = _
      rw [Equiv.symm_apply_apply]
      rfl
    rw [h3] at h2
    exact Sum.inl_ne_inr h2
  · intro h
    rcases hx : stdMNu (fun _ : Unit => M) () j with x | u
    · exact ⟨x, by rw [← hx, Equiv.symm_apply_apply]⟩
    · refine absurd ?_ h
      have h3 : stdMNu (fun _ : Unit => M) () (M.place (.inr ())) = Sum.inr () := by
        show Sum.map _ _ (M.place.symm (M.place (.inr ()))) = _
        rw [Equiv.symm_apply_apply]
        rfl
      exact (stdMNu (fun _ : Unit => M) ()).injective (hx.trans h3.symm)

theorem stdNew_noPad : ∀ n : V.N.N₀.Ent, V.layN.NoPad n ↔ ¬ V.IsPad n
  | ⟨none, j⟩ => stdM_noPad V.Mc j
  | ⟨some k, j⟩ => stdM_noPad (V.Mn k) j

end

section
variable {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  {Sh : GShape G} {kp : S.O → Prop} [DecidablePred kp] {Hd : GHeld Sh kp} {Pn : Type} [Fintype Pn]
  (V : StdNew Hd Pn) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  {St₀ Wp : Type} {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (w0 : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp) (L t tl : ℕ) (N₁ : Sig E)
  (Y₁ : N₁.StdL E)
  (dat₁ : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp → ∀ b, Y₁.Dt b → E)
  (L₁ t₁ : N₁.O → ℕ) (Wp' : Type) (rst : Wp → Wp') (bkR : N₁.Msg → Wp' → Wp) {I : Type}
  (pl : I → Σ a, Y₁.Fr a)

/-- the places, as free entries of the whole family -/
def StdNew.plS (i : I) : Σ a, (V.layS N₁ Y₁).Fr a := ⟨.inr (pl i).1, (pl i).2⟩

theorem stdNewT_fact [Fintype (I → E)] [Nonempty (I → E)] (hpl : Function.Injective pl)
    (RdOld : (Hd.foldD Sb sl Z A₀).tgt.S.Ent → Prop)
    (RrOld : (Hd.foldD Sb sl Z A₀).tgt.S.O → Prop) :
    (V.closeRT Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR).snd.tgt.wideFact
      ((Hd.foldD Sb sl Z A₀).tgt.S.sumP (V.N.N₀.sum N₁) RdOld (V.layS N₁ Y₁).NoPad)
      ((Hd.foldD Sb sl Z A₀).tgt.S.sumO (V.N.N₀.sum N₁) RrOld fun _ => False)
      ((Hd.foldD Sb sl Z A₀).tgt.S.sumP
        (V.N.N₀.sum N₁) (fun _ => False) ((V.layS N₁ Y₁).ownP (V.plS N₁ Y₁ pl)))
      (I → E) (fun M =>
        (Hd.foldD Sb sl Z A₀).tgt.S.sumV
          (V.N.N₀.sum N₁) (fun _ => 0) ((V.layS N₁ Y₁).valP (V.plS N₁ Y₁ pl) M)) =
      V.rideFactW Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR pl RdOld RrOld := by
  have eRd : (V.layS N₁ Y₁).NoPad =
      V.rdR Sb sl Z A₀ (rideStdD Sb sl Z A₀ w0 N₁ Y₁ dat₁ L₁ t₁) Y₁.NoPad := by
    funext n
    rcases n with ⟨a | b, j⟩
    · exact propext (stdNew_noPad V ⟨a, j⟩)
    · rfl
  have up : ∀ i,
      (V.layS N₁ Y₁).entF (V.plS N₁ Y₁ pl i) = ⟨.inr (Y₁.entF (pl i)).1, (Y₁.entF (pl i)).2⟩ :=
    fun _ => rfl
  have eOwn : (V.layS N₁ Y₁).ownP (V.plS N₁ Y₁ pl) =
      V.ownR Sb sl Z A₀ (rideStdD Sb sl Z A₀ w0 N₁ Y₁ dat₁ L₁ t₁) (Y₁.ownP pl) := by
    funext n
    rcases n with ⟨a | b, j⟩
    · exact propext ⟨fun ⟨i, e⟩ => absurd (congrArg Sigma.fst e) Sum.inl_ne_inr, fun h => h.elim⟩
    · refine propext ⟨fun ⟨i, e⟩ => ⟨i, ?_⟩, fun ⟨i, e⟩ => ⟨i, ?_⟩⟩
      · rw [up] at e
        have hh := Sigma.mk.inj e
        exact Sigma.ext (Sum.inr_injective hh.1) hh.2
      · rw [up, ← e]
  have hinj : Function.Injective fun i => Y₁.entF (pl i) := Y₁.entF_injective.comp hpl
  have hinjS : Function.Injective fun i =>
      (V.layS N₁ Y₁).entF (V.plS N₁ Y₁ pl i) := fun i i' e => by
    have e' : (⟨.inr (Y₁.entF (pl i)).1, (Y₁.entF (pl i)).2⟩ : (V.N.N₀.sum N₁).Ent) =
        ⟨.inr (Y₁.entF (pl i')).1, (Y₁.entF (pl i')).2⟩ := e
    have hh := Sigma.mk.inj e'
    exact hinj (Sigma.ext (Sum.inr_injective hh.1) hh.2)
  have eVal : ∀ M : I → E, (V.layS N₁ Y₁).valP (V.plS N₁ Y₁ pl) M =
      V.valR Sb sl Z A₀ (rideStdD Sb sl Z A₀ w0 N₁ Y₁ dat₁ L₁ t₁) (Y₁.valP pl M) := by
    intro M
    funext n
    by_cases h : ∃ i, (V.layS N₁ Y₁).entF (V.plS N₁ Y₁ pl i) = n
    · obtain ⟨i, rfl⟩ := h
      show Function.extend (fun i => (V.layS N₁ Y₁).entF (V.plS N₁ Y₁ pl i)) M (fun _ => 0) _ =
        Function.extend (fun i => Y₁.entF (pl i)) M (fun _ => 0) (Y₁.entF (pl i))
      rw [hinjS.extend_apply, hinj.extend_apply]
    · have l : (V.layS N₁ Y₁).valP (V.plS N₁ Y₁ pl) M n = 0 := Function.extend_apply' _ _ _ h
      rw [l]
      rcases n with ⟨a | b, j⟩
      · rfl
      · have r : Function.extend (fun i => Y₁.entF (pl i)) M (fun _ => 0) (⟨b, j⟩ : N₁.Ent) = 0 :=
          Function.extend_apply' _ _ _ fun ⟨i, e⟩ => h ⟨i, by rw [up, e]⟩
        exact r.symm
  unfold StdNew.rideFactW
  rw [eRd, eOwn,
    show (fun M : I → E =>
        (Hd.foldD Sb sl Z A₀).tgt.S.sumV
          (V.N.N₀.sum N₁) (fun _ => 0) ((V.layS N₁ Y₁).valP (V.plS N₁ Y₁ pl) M)) =
      fun M =>
        (Hd.foldD Sb sl Z A₀).tgt.S.sumV (V.N.N₀.sum N₁) (fun _ => 0)
          (V.valR Sb sl Z A₀ (rideStdD Sb sl Z A₀ w0 N₁ Y₁ dat₁ L₁ t₁) (Y₁.valP pl M))
          from funext fun M => by rw [eVal M]]

/-- For `G.P` nonempty and under the hypotheses of its statement: the one sending is fresh for it.
(`V.rideFactW`, Cb/Ld/LdGroupNewRideWFresh.lean.) -/
theorem stdNewT_fresh [Fintype (I → E)] [Nonempty (I → E)] (hpl : Function.Injective pl)
    (RdOld : (Hd.foldD Sb sl Z A₀).tgt.S.Ent → Prop) (RrOld : (Hd.foldD Sb sl Z A₀).tgt.S.O → Prop)
    (h : V.OK L t) (hY : Y₁.OK t₁) (bkD : (∀ b, Y₁.Dt b → E) → Wp' → Wp)
    (hD : ∀ m w', bkR m w' = bkD (Y₁.dataOf m) w') :
    (V.closeRT Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR).snd.link.H.Fresh
      (Hd.foldD Sb sl Z A₀).tgt.J.rels.rel
      (V.closeRT Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR).snd.link.P.bud
      (V.rideFactW Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR pl RdOld RrOld).kc (I → E)
      (V.rideFactW Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR pl RdOld RrOld).put := by
  haveI : Finite I := Finite.of_injective _ (Y₁.entF_injective.comp hpl)
  haveI : Fintype I := Fintype.ofFinite I
  have hS : Function.Injective (V.plS N₁ Y₁ pl) := fun i i' e => by
    have hh := Sigma.mk.inj e
    exact hpl (Sigma.ext (Sum.inr_injective hh.1) hh.2)
  have f := ldReqStdLay_fresh E E Kc _
    (V.closeRT Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR).snd (V.layS N₁ Y₁)
    (V.datS Sb sl Z A₀ N₁ Y₁ dat₁) (fun x => rst x.2) (V.bkS Sb sl Z A₀ N₁ Y₁ Wp' bkD) w0 I
    (V.plS N₁ Y₁ pl) RdOld RrOld
    (stdNewT_eq V Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR bkD hD) hS
    (stdL_sum E E _ _ V.layN Y₁ _ _ (stdNew_layN_ok V h) hY).1
  have key : ∀ g g' : MaskFact
          (V.closeRT Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR).snd.tgt.J.W,
        g = g' →
        (V.closeRT Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR).snd.link.H.Fresh
          (Hd.foldD Sb sl Z A₀).tgt.J.rels.rel
          (V.closeRT Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR).snd.link.P.bud
          g.kc g.Mk g.put →
        (V.closeRT Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR).snd.link.H.Fresh
          (Hd.foldD Sb sl Z A₀).tgt.J.rels.rel
          (V.closeRT Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR).snd.link.P.bud
          g'.kc g'.Mk g'.put :=
    fun _ _ e hg => e ▸ hg
  exact key _ _
    (stdNewT_fact V Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR pl hpl RdOld RrOld) f

/-- For `G.P` nonempty and under the hypotheses of its statement: the cut of the locations does not
look. (`V.rideFactW`; see `stdNewT_cutQuiet` in the head.) -/
theorem stdNewT_cutQuiet [Fintype (I → E)] [Nonempty (I → E)]
    (RdOld : (Hd.foldD Sb sl Z A₀).tgt.S.Ent → Prop) (RrOld : (Hd.foldD Sb sl Z A₀).tgt.S.O → Prop)
    (w w' : (V.closeRT Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR).loc.src.J.W) (M : I → E)
    (hw : (V.rideFactW Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR pl RdOld RrOld).kc w' =
      (V.rideFactW Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR pl RdOld RrOld).put
        M ((V.rideFactW Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR pl RdOld RrOld).kc w)) :
    (V.closeRT Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR).loc.cut
        ((V.closeRT Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR).loc.S.msgs w'.1) =
      (V.closeRT Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR).loc.cut
        ((V.closeRT Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR).loc.S.msgs w.1) :=
  rideStdW_cutQuiet V Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR pl RdOld RrOld w w' M hw

end
end Cb
