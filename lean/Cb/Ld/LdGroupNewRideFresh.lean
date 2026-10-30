-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupNewRideFresh.lean: this file is for toys (a toy: a small example instance). Under the
hypotheses of its statements, the one sending of a closing with riders lays down the masks that
stand in the riders: the sending is fresh for their wide fact, and the cut of the locations does not
look.
(`LdStage.wideFact`, Cb/Req1/LdSegCarry.lean; `MaskFact`, Cb/Req1/LdSegFresh.lean; `Honest.Fresh`,
Ior/KnowCollRulesMask.lean.)

Definitions, statements as theorems, proofs. Generic: an abstract field, variable codes.
Rider (lean/GLOSSARY.md): a further oracle message that a closing's one sending sends with the
closing's own new messages (`RideD`, Cb/Ld/LdGroupNewRide.lean).
Locations (lean/GLOSSARY.md): the one-round step in which the prover sends nothing and the verifier
draws long positions of an open word and reads it there.

Why: Cb/Ld/LdGroupNewRide.lean: the one sending of a closing sends the closing's new messages and
further oracle messages ("riders": the first messages of the next segment), with independent coins.
Cb/Req1/LdReqRefLay.lean asks of a fact that this sending lays down (`S.New`): the sending is
`Fresh` for it, and the cut of the locations does not look at it. The second clause can hold for a
wide fact only: its reading must determine what the locations' prover cuts out of the new messages.

The data. `XR : MemSplit Rd.m`: the coins of each rider as (free coins, pad coins)
(Cb/Ld/LdSendMemOwn.lean); εR: all riders' free coins as (own masks of a coming block, the others):
the masks of one block may stand in many riders.

Main names:
  `V.splitR XR`, `V.epsR εR`: the same for the whole family (new messages beside riders): a new
    message has no free coin, its one coin is its pad.
  `V.rdR RdR`, `V.ownR own`, `V.valR val`: the sets and values over the whole family: read: of the
    new messages all entries that are no pads, of the riders the entries in RdR; own: entries of
    riders.
  `stdNewR_fresh`: Mb, M0 finite and nonempty; `V.OK L t`, the riders' encoders hide, `XR.Unif`; own
    ⊆ RdR; an own entry holds the mask's value; an entry of a rider in RdR that is not own reads
    neither the own masks nor a pad coin ⇒ the sending's link is `Fresh` for the wide fact (of what
    was left: any reading; no new encoding randomness).
  `stdNewR_cutQuiet`: Mb finite and nonempty: two witnesses whose wide readings differ by the
    overwriting give the locations the same cut (Cb/Ld/LdGroupNewCut.lean: the cut reads no pad and
    no rider).
In all of them the group's set of common long positions, `G.P`, is nonempty (the closing needs it).

Limits: no instance at this closing. This file gives no instance that meets its hypotheses, so as
far as this file shows its theorems may hold of nothing.
The fact does not cross a later closing whose group holds a member of this sending
(Cb/Ld/LdSendMemOwn.lean's head).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupNewCut
import Cb.Ld.LdSendMemOwn
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
  (Rd : RideD E ((Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp))

/-- A local instance, so that `Nonempty E` is found whatever is imported. -/
local instance neFldR : Nonempty E := ⟨0⟩

/-- The coins of the whole family: a new message has no free coin; its one coin is its pad. -/
@[reducible] def StdNew.splitR (XR : MemSplit Rd.m) :
    MemSplit (V.memR Sb sl Z A₀ w0 Rd) where
  Fr := Sum.elim (fun _ => Unit) XR.Fr
  Pd := Sum.elim (fun _ => E) XR.Pd
  finPd := fun a => match a with
    | .inl _ => inferInstanceAs (Fintype E)
    | .inr b => XR.finPd b
  nePd := fun a => match a with
    | .inl _ => inferInstanceAs (Nonempty E)
    | .inr b => XR.nePd b
  κ := fun a => match a with
    | .inl none => (Equiv.punitProd E).symm
    | .inl (some _) => (Equiv.punitProd E).symm
    | .inr b => XR.κ b

/-- all free coins are the riders' -/
def StdNew.epsR (XR : MemSplit Rd.m) {Mb M0 : Type} (εR : (∀ b, XR.Fr b) ≃ Mb × M0) :
    (∀ a, (V.splitR Sb sl Z A₀ w0 Rd XR).Fr a) ≃ Mb × M0 :=
  Equiv.trans
    { toFun := fun f b => f (.inr b)
      invFun := fun g a => match a with
        | .inl _ => ()
        | .inr b => g b
      left_inv := fun f => funext fun a => by
        rcases a with a | b
        · rfl
        · rfl
      right_inv := fun _ => rfl } εR

/-- the sets and values over the whole family -/
def StdNew.rdR (RdR : Rd.N.Ent → Prop) : (V.N.N₀.sum Rd.N).Ent → Prop :=
  V.N.N₀.sumP Rd.N (fun n => ¬ V.IsPad n) RdR
def StdNew.ownR (own : Rd.N.Ent → Prop) : (V.N.N₀.sum Rd.N).Ent → Prop :=
  V.N.N₀.sumP Rd.N (fun _ => False) own
def StdNew.valR (val : Rd.N.Ent → E) : (V.N.N₀.sum Rd.N).Ent → E :=
  V.N.N₀.sumV Rd.N (fun _ => 0) val

/-- For `G.P` nonempty and under the hypotheses of its statement: over its pad coins alone every
member's answers are uniform. -/
theorem stdNewR_unif (XR : MemSplit Rd.m) (h : V.OK L t) (hX : XR.Unif) :
    (V.splitR Sb sl Z A₀ w0 Rd XR).Unif := by
  intro x a
  rcases a with (_ | k) | b
  · exact stdM_uniform V.Mc h.1 V.datC w0
  · exact stdM_uniform (V.Mn k) (h.2 k) (V.datN k) w0
  · exact hX (fun b => x (.inr b)) b

/-- For `G.P` nonempty and under the hypotheses of its statement: an entry of a new message that is
no pad does not read the pad coin. -/
theorem stdNewR_noPad (w : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp)
    (n : V.N.N₀.Ent) (hn : ¬ V.IsPad n) (η η' : E) :
    (V.mem w0 n.1).upM ((V.mem w0 n.1).put w (match n.1 with | none => η | some _ => η)) n.2 =
      (V.mem w0 n.1).upM
        ((V.mem w0 n.1).put w (match n.1 with | none => η' | some _ => η')) n.2 := by
  obtain ⟨_ | k, j⟩ := n
  · obtain ⟨x, rfl⟩ := V.Mc.place.surjective j
    rcases x with d | ⟨⟩
    · exact (stdM_put V.Mc V.datC w0 w η d).trans (stdM_put V.Mc V.datC w0 w η' d).symm
    · exact absurd rfl hn
  · obtain ⟨x, rfl⟩ := (V.Mn k).place.surjective j
    rcases x with d | ⟨⟩
    · exact (stdM_put (V.Mn k) (V.datN k) w0 w η d).trans
        (stdM_put (V.Mn k) (V.datN k) w0 w η' d).symm
    · exact absurd rfl hn

/-- For `G.P` nonempty and under the hypotheses of its statement: the one sending is fresh for the
wide fact of masks that stand in riders. -/
theorem stdNewR_fresh (XR : MemSplit Rd.m) {Mb M0 : Type} [Fintype Mb] [Nonempty Mb] [Fintype M0]
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
    (V.closeR Sb sl Z A₀ w0 L t tl Rd).snd.link.H.Fresh (Hd.foldD Sb sl Z A₀).tgt.J.rels.rel
      (V.closeR Sb sl Z A₀ w0 L t tl Rd).snd.link.P.bud
      ((V.closeR Sb sl Z A₀ w0 L t tl Rd).snd.tgt.wideFact
        ((Hd.foldD Sb sl Z A₀).tgt.S.sumP (V.N.N₀.sum Rd.N) RdOld (V.rdR Sb sl Z A₀ Rd RdR))
        ((Hd.foldD Sb sl Z A₀).tgt.S.sumO (V.N.N₀.sum Rd.N) RrOld fun _ => False)
        ((Hd.foldD Sb sl Z A₀).tgt.S.sumP
          (V.N.N₀.sum Rd.N) (fun _ => False) (V.ownR Sb sl Z A₀ Rd own))
        Mb fun M =>
          (Hd.foldD Sb sl Z A₀).tgt.S.sumV
            (V.N.N₀.sum Rd.N) (fun _ => 0) (V.valR Sb sl Z A₀ Rd (val M))).kc
      Mb ((V.closeR Sb sl Z A₀ w0 L t tl Rd).snd.tgt.wideFact
        ((Hd.foldD Sb sl Z A₀).tgt.S.sumP (V.N.N₀.sum Rd.N) RdOld (V.rdR Sb sl Z A₀ Rd RdR))
        ((Hd.foldD Sb sl Z A₀).tgt.S.sumO (V.N.N₀.sum Rd.N) RrOld fun _ => False)
        ((Hd.foldD Sb sl Z A₀).tgt.S.sumP
          (V.N.N₀.sum Rd.N) (fun _ => False) (V.ownR Sb sl Z A₀ Rd own))
        Mb fun M =>
          (Hd.foldD Sb sl Z A₀).tgt.S.sumV
              (V.N.N₀.sum Rd.N) (fun _ => 0) (V.valR Sb sl Z A₀ Rd (val M))).put := by
  refine memOwn_fresh (Hd.foldD Sb sl Z A₀).tgt (V.N.N₀.sum Rd.N) (Sig.Seeds.indep _) Wp
    (V.closeR Sb sl Z A₀ w0 L t tl Rd).snd.bk (Sum.elim (fun _ => L) Rd.L)
    (Sum.elim (fun _ => t) Rd.t) (V.memR Sb sl Z A₀ w0 Rd) (fun w => (w.1, w.2.2)) w0
    (V.splitR Sb sl Z A₀ w0 Rd XR) Mb M0 (V.epsR Sb sl Z A₀ w0 Rd XR εR) RdOld
    (V.rdR Sb sl Z A₀ Rd RdR) RrOld (V.ownR Sb sl Z A₀ Rd own)
    (fun M => V.valR Sb sl Z A₀ Rd (val M))
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
theorem stdNewR_cutQuiet {Mb : Type} [Fintype Mb] [Nonempty Mb]
    (RdOld : (Hd.foldD Sb sl Z A₀).tgt.S.Ent → Prop) (RrOld : (Hd.foldD Sb sl Z A₀).tgt.S.O → Prop)
    (RdR own : Rd.N.Ent → Prop) (val : Mb → Rd.N.Ent → E)
    (w w' : (V.closeR Sb sl Z A₀ w0 L t tl Rd).loc.src.J.W) (M : Mb)
    (hw : ((V.closeR Sb sl Z A₀ w0 L t tl Rd).snd.tgt.wideFact
        ((Hd.foldD Sb sl Z A₀).tgt.S.sumP (V.N.N₀.sum Rd.N) RdOld (V.rdR Sb sl Z A₀ Rd RdR))
        ((Hd.foldD Sb sl Z A₀).tgt.S.sumO (V.N.N₀.sum Rd.N) RrOld fun _ => False)
        ((Hd.foldD Sb sl Z A₀).tgt.S.sumP
          (V.N.N₀.sum Rd.N) (fun _ => False) (V.ownR Sb sl Z A₀ Rd own))
        Mb fun M =>
          (Hd.foldD Sb sl Z A₀).tgt.S.sumV
            (V.N.N₀.sum Rd.N) (fun _ => 0) (V.valR Sb sl Z A₀ Rd (val M))).kc w' =
      ((V.closeR Sb sl Z A₀ w0 L t tl Rd).snd.tgt.wideFact
          ((Hd.foldD Sb sl Z A₀).tgt.S.sumP (V.N.N₀.sum Rd.N) RdOld (V.rdR Sb sl Z A₀ Rd RdR))
          ((Hd.foldD Sb sl Z A₀).tgt.S.sumO (V.N.N₀.sum Rd.N) RrOld fun _ => False)
          ((Hd.foldD Sb sl Z A₀).tgt.S.sumP
            (V.N.N₀.sum Rd.N) (fun _ => False) (V.ownR Sb sl Z A₀ Rd own))
          Mb fun M =>
            (Hd.foldD Sb sl Z A₀).tgt.S.sumV
              (V.N.N₀.sum Rd.N) (fun _ => 0) (V.valR Sb sl Z A₀ Rd (val M))).put
        M (((V.closeR Sb sl Z A₀ w0 L t tl Rd).snd.tgt.wideFact
          ((Hd.foldD Sb sl Z A₀).tgt.S.sumP (V.N.N₀.sum Rd.N) RdOld (V.rdR Sb sl Z A₀ Rd RdR))
          ((Hd.foldD Sb sl Z A₀).tgt.S.sumO (V.N.N₀.sum Rd.N) RrOld fun _ => False)
          ((Hd.foldD Sb sl Z A₀).tgt.S.sumP
            (V.N.N₀.sum Rd.N) (fun _ => False) (V.ownR Sb sl Z A₀ Rd own))
          Mb fun M =>
            (Hd.foldD Sb sl Z A₀).tgt.S.sumV
              (V.N.N₀.sum Rd.N) (fun _ => 0) (V.valR Sb sl Z A₀ Rd (val M))).kc w)) :
    (V.closeR Sb sl Z A₀ w0 L t tl Rd).loc.cut
        ((V.closeR Sb sl Z A₀ w0 L t tl Rd).loc.S.msgs w'.1) =
      (V.closeR Sb sl Z A₀ w0 L t tl Rd).loc.cut
        ((V.closeR Sb sl Z A₀ w0 L t tl Rd).loc.S.msgs w.1) := by
  have hA := (segWide_alike (V.closeR Sb sl Z A₀ w0 L t tl Rd).snd.tgt _ _ _ Mb _ w w' M hw).1
  exact stdNewR_cut_congr V Sb sl Z A₀ w0 L t tl Rd _ _ fun n hn =>
    hA ⟨.inr (.inl n.1), n.2⟩ hn fun hh => hh

end
end Cb
