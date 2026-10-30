-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupNewStdT.lean: for toys: in the code switch that follows the fold of several oracle
codewords the prover sends, in one message, the new codewords and the first codewords of the next
part of the protocol; this file defines that step with one generic sender for the whole message.

It shows, under a condition on what is read back off the messages, that the step is equal, as a
term, to the form in which the theorems of Cb/Req1/LdReqProtoStd.lean ask for every such step. A
toy: a small example instance.

Definitions, statements as theorems, proofs. Generic.
Riders (Cb/Ld/LdGroupNewRide.lean) are further oracle messages that the one sending of a closing
sends with the closing's new messages; here their layout is `Y₁ : N₁.StdL E`.

Why: the closing of Cb/Ld/LdGroupNewStdS.lean (`V.closeS`) has the equation "the one sending is
`LdSendD.std`" by definition, at the price that its cut and what it reads back are other terms than
those of `V.closeRW` (Cb/Ld/LdGroupNewRideW.lean); so the stage after it is another term. Here the
cut and what is read back are the same terms as in `V.closeRW`.

Main names:
  `V.closeRT`, `pk.closeRT`: that step. `stdNewT_loc`: its locations. `stdNewT_eq`: its sending.
  `stdNewT_isStd`: under the hypotheses of its statement, its sending is `IsStd`
    (Cb/Req1/LdReqProtoStd.lean). `stdNewT_snd`: under the hypotheses of its statement, the seven
    hypotheses of the sending.
In the statements on `V.closeRT` the group's set of common long positions, `G.P`, is nonempty; a
bundle has that as a field.

Limits: this file says nothing on masks (Cb/Ld/LdGroupNewStdTFresh.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupNewStdS
import Cb.Ld.LdGroupRideStd
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

section
variable {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  {Sh : GShape G} {kp : S.O → Prop} [DecidablePred kp] {Hd : GHeld Sh kp} {Pn : Type} [Fintype Pn]
  (V : StdNew Hd Pn) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  {St₀ Wp : Type} {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (w0 : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp) (L t tl : ℕ) (N₁ : Sig E)
  (Y₁ : N₁.StdL E)
  (dat₁ : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp → ∀ b, Y₁.Dt b → E)
  (L₁ t₁ : N₁.O → ℕ) (Wp' : Type) (rst : Wp → Wp') (bkR : N₁.Msg → Wp' → Wp)

/-- `V.closeRW` at standard riders, with the standard sender for the new messages too: all but the
sender is as there. -/
@[reducible] def StdNew.closeRT : LdCloseD (Hd.foldD Sb sl Z A₀) where
  N := V.N.N₀.sum N₁
  Sd := Sig.Seeds.indep _
  Wp' := Wp'
  cutN := fun m => V.N.cut fun a => m (.inl a)
  bk₀ := fun m w' => bkR (fun b => m (.inr b)) w'
  Sn := (V.layS N₁ Y₁).snd (V.datS Sb sl Z A₀ N₁ Y₁ dat₁) (fun w => (w.1, rst w.2.2)) w0
  L := Sum.elim (fun _ => L) L₁
  tN := Sum.elim (fun _ => t) t₁
  t := tl
  neP := inferInstanceAs (Nonempty G.P)

/-- For `G.P` nonempty: the locations, and so the stage after the closing, are those of `V.closeRW`
at standard riders (`RideD.std`, Cb/Ld/LdGroupRideStd.lean), by definition -/
theorem stdNewT_loc :
    (V.closeRT Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR).loc =
      (V.closeRW Sb sl Z A₀ w0 L t tl (RideD.std N₁ Y₁ dat₁ w0 L₁ t₁) Wp' rst bkR).loc := rfl

/-- For `G.P` nonempty: the sending of `V.closeRT` is the standard one, if what is read back off the
riders is read off their data (hypothesis hD). This is proved, not by definition: the cut read off
the data of messages is their cut. -/
theorem stdNewT_eq (bkD : (∀ b, Y₁.Dt b → E) → Wp' → Wp)
    (hD : ∀ m w', bkR m w' = bkD (Y₁.dataOf m) w') :
    (V.closeRT Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR).snd =
      LdSendD.std (Hd.foldD Sb sl Z A₀).tgt (V.N.N₀.sum N₁) (Sig.Seeds.indep _) Wp'
        (Sum.elim (fun _ => L) L₁) (Sum.elim (fun _ => t) t₁) (V.layS N₁ Y₁)
        (V.datS Sb sl Z A₀ N₁ Y₁ dat₁) (fun x => rst x.2) (V.bkS Sb sl Z A₀ N₁ Y₁ Wp' bkD) w0 := by
  have e : (fun (n : (V.N.N₀.sum N₁).Msg) (w' : Wp') =>
        ((V.N.cut fun a => n (.inl a),
          bkR (fun b => n (.inr b)) w') : (Hd.foldD Sb sl Z A₀).tgt.Wp)) =
      fun m r => V.bkS Sb sl Z A₀ N₁ Y₁ Wp' bkD ((V.layS N₁ Y₁).dataOf m) r := by
    funext n w'
    exact Prod.ext (stdNew_cutD_of V fun a => n (.inl a)).symm (hD _ w')
  show (⟨V.N.N₀.sum N₁, Sig.Seeds.indep _, Wp', _, _, _, _⟩ : LdSendD (Hd.foldD Sb sl Z A₀).tgt) =
    ⟨V.N.N₀.sum N₁, Sig.Seeds.indep _, Wp', _, _, _, _⟩
  rw [e]

theorem stdNewT_isStd (h : V.OK L t) (h₁ : Y₁.OK t₁) (hl : ∀ b, (N₁.om b).C.Laws)
    (hs₁ : ∀ b, (N₁.om b).ListLE (L₁ b)) (he : ∀ b, (N₁.om b).Evades)
    (bkD : (∀ b, Y₁.Dt b → E) → Wp' → Wp) (hD : ∀ m w', bkR m w' = bkD (Y₁.dataOf m) w')
    (hbk : ∀ w, bkD (dat₁ w) (rst w.2.2) = w.2.2) :
    (V.closeRT Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR).snd.IsStd E :=
  ⟨V.layS N₁ Y₁, V.datS Sb sl Z A₀ N₁ Y₁ dat₁, fun x => rst x.2, V.bkS Sb sl Z A₀ N₁ Y₁ Wp' bkD, w0,
    stdNewT_eq V Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR bkD hD,
    (stdL_sum E E _ _ V.layN Y₁ _ t₁ (stdNew_layN_ok V h) h₁).1,
    fun w => Prod.ext (stdNew_cutD_dat V w0 w) (hbk w),
    fun i => match i with
      | .inl none => h.1.laws
      | .inl (some k) => (h.2 k).laws
      | .inr b => hl b,
    (ldSendFam_fair_indep E _).1,
    fun i => match i with
      | .inl none => stdM_list V.Mc h.1
      | .inl (some k) => stdM_list (V.Mn k) (h.2 k)
      | .inr b => hs₁ b,
    fun i => match i with
      | .inl none => stdM_evades V.Mc h.1
      | .inl (some k) => stdM_evades (V.Mn k) (h.2 k)
      | .inr b => he b⟩

/-- What the sending asks. -/
theorem stdNewT_snd (h : V.OK L t) (h₁ : Y₁.OK t₁) (hl : ∀ b, (N₁.om b).C.Laws)
    (hs₁ : ∀ b, (N₁.om b).ListLE (L₁ b)) (he : ∀ b, (N₁.om b).Evades)
    (bkD : (∀ b, Y₁.Dt b → E) → Wp' → Wp) (hD : ∀ m w', bkR m w' = bkD (Y₁.dataOf m) w')
    (hbk : ∀ w, bkD (dat₁ w) (rst w.2.2) = w.2.2) :
    (V.closeRT Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR).snd.Hyp :=
  ldReqProtoStd_send E E Kc _ _
    (stdNewT_isStd V Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR h h₁ hl hs₁ he bkD hD hbk)

/-- For `G.P` nonempty: messages that agree at all entries of the new messages that are no pads have
the same cut -/
theorem stdNewT_cut_congr
    (m m' : (V.closeRT Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR).N.Msg)
    (h : ∀ n : V.N.N₀.Ent, ¬ V.IsPad n → m' (.inl n.1) n.2 = m (.inl n.1) n.2) :
    (V.closeRT Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR).cutN m' =
      (V.closeRT Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR).cutN m :=
  stdNew_cut_congr V (fun a => m (.inl a)) (fun a => m' (.inl a)) h

end

section
variable {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {mem kp : S.O → Prop}
  [DecidablePred kp] {clP : {o // kp o} → Prop} {Pn : Type} [Fintype Pn] {d e t : ℕ}
  {Lst mC mS mW : ℕ → ℕ} {L L₂ t₂ : ℕ} (pk : GPack S mem kp clP Pn d e t Lst mC mS mW L L₂ t₂)
  (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) S.Ent) (Z : Evader E B) (Zb : Evader E (pk.G.Row Unit))
  {St₀ Wp : Type} {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (w0 : (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).tgt.S.Wit ×
    (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).tgt.Wp)
  (tl : ℕ) (N₁ : Sig E) (Y₁ : N₁.StdL E)
  (dat₁ : (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).tgt.S.Wit ×
      (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).tgt.Wp →
    ∀ b, Y₁.Dt b → E)
  (L₁ t₁ : N₁.O → ℕ) (Wp' : Type) (rst : Wp → Wp') (bkR : N₁.Msg → Wp' → Wp)

/-- the same from a bundle -/
@[reducible] def GPack.closeRT :
    LdCloseD (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀) :=
  pk.V.closeRT (fun _ : Unit => GPack.Sx Sb Z)
    (pk.row1 Sb sl Z) Zb A₀ w0 L₂ t₂ tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkR

end
end Cb
