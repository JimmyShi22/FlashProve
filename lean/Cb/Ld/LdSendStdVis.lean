-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendStdVis.lean: under the hypotheses of its statements, at the standard sender: a sending
of a request is fresh for masks at free entries of one member o, for the wide reading (`Sig.wide`,
Cb/Req1/LdSegCarry.lean) that sees all entries but o's pads and the encoding randomness of all
members but o.

This file is book-keeping for those coins of an honest prover that go into its messages
(`Sig.Sender.Mk`). A layout marks coordinates of the prover's messages as free, for coins; this file
takes a set of free coordinates of one message as the masks that one later reduction of a chain will
use, and splits that message's coins accordingly (`Y.splitO`).

Definitions, statements and proofs.

`H.Fresh Ri bud kc Mk put`: for every (x, y, w) in Ri, every ρ outside `H.withheld w x` and every T
with `bud ρ T`: the distribution of `H.seen …` over uniform coins does not change if its third part
is overwritten by `put M` at an independent uniform M. Here it is the conclusion of `Spec.stdL_vis`.

Why: a message with masks (that of the masks for the rows on the encoded index) goes out in one
prover message with oracle messages that are tested, in a closing, before these masks are used. To
cross that closing (Cb/Req1/LdSegCarryClose.lean) the fact's reading (`MaskFact`,
Cb/Req1/LdSegFresh.lean) must show every member of the closing's group whole: all entries, pads
included, and the encoding randomness.
Cb/Ld/LdSendStdOwn.lean has, under the hypotheses of its statement, the conditions on the sender's
coins at the standard sender for masks in any members, but for a reading that forgets all pads and
all encoding randomness: good for the blocks that follow at once; it cannot cross.
Here (`Spec.stdL_vis`: `Honest.Fresh`) the form that can, for masks that stand in one member. The
standard sender (Cb/Ld/LdSendStdL.lean: `Y.snd`) is made from senders of the members with
independent coins, so Cb/Ld/LdSendFreshVis.lean applies; Cb/Req1/LdSegSendFresh.lean brings it into
the letters of the wide fact.

Main names, each under the hypotheses of its statement:
  `Y.splitO o pl hpl`: the coins of the member o as ((the free entries at pl, its other free
    entries), its pads), for any injective family pl of free entries of o.
  `Y.entO o x`: a free entry of o as an entry of the family; `Y.rdBut o`: all entries but o's pads;
    `Y.rrBut o`: all names but o; `Y.ownO o pl`, `Y.valO o pl M`: the own entries, a vector laid at
    them.
  `Spec.stdL_vis`: `Y.OK t` ⇒ the link of `LdSendD.std .. Y ..` is Fresh (`Honest.Fresh`,
    Ior/KnowCollRulesMask.lean) for the wide fact (`LdStage.wideFact`, Cb/Req1/LdSegCarry.lean) (old
    part of the reading: arbitrary).
  `Spec.stdL_visAfter`: so that fact is among the facts that are fresh after the move (`LdMv.After`,
    Cb/Req1/LdReq.lean), whatever was fresh before.

Limits: this file says nothing on masks of one block in several members, for a reading of this kind.
Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectSenders
import Cb.Ld.LdSendStdOwn
import Cb.Req1.LdSegSendFreshProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

namespace Sig.StdL
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] {N : Sig E}
  (Y : N.StdL F) (o : N.O) {I : Type} (pl : I → Y.Fr o)

open Classical in
/-- The coins of the member o as ((own masks, its other free entries), its pads). -/
def splitO (hpl : Function.Injective pl) :
    ((Y.Fr o → E) × (Y.Pd o → F)) ≃
      ((I → E) × ({x : Y.Fr o // ¬ ∃ i, pl i = x} → E)) × (Y.Pd o → F) where
  toFun := fun k => ((fun i => k.1 (pl i), fun x => k.1 x.1), k.2)
  invFun := fun y => (fun x => if h : ∃ i, pl i = x then y.1.1 h.choose else y.1.2 ⟨x, h⟩, y.2)
  left_inv := fun k => Prod.ext (funext fun x => by
    by_cases h : ∃ i, pl i = x
    · show (if h : ∃ i, pl i = x then k.1 (pl h.choose) else k.1 x) = k.1 x
      rw [dif_pos h, h.choose_spec]
    · show (if h : ∃ i, pl i = x then k.1 (pl h.choose) else k.1 x) = k.1 x
      rw [dif_neg h]) rfl
  right_inv := fun y => Prod.ext (Prod.ext (funext fun i => by
      have h : ∃ i', pl i' = pl i := ⟨i, rfl⟩
      show (if h : ∃ i', pl i' = pl i then y.1.1 h.choose else y.1.2 ⟨pl i, h⟩) = y.1.1 i
      rw [dif_pos h, hpl h.choose_spec]) (funext fun x => by
      show (if h : ∃ i, pl i = x.1 then y.1.1 h.choose else y.1.2 ⟨x.1, h⟩) = y.1.2 x
      rw [dif_neg x.2])) rfl

/-- a free entry of o, as an entry of the family -/
def entO (x : Y.Fr o) : N.Ent := ⟨o, Y.atF o x⟩
/-- all entries but o's pads; all names but o -/
def rdBut : N.Ent → Prop := fun n => n.1 = o → Y.NoPad n
def rrBut (_ : N.StdL F) : N.O → Prop := fun a => a ≠ o
/-- the own entries; a vector laid at them -/
def ownO : N.Ent → Prop := fun n => ∃ i, Y.entO o (pl i) = n
def valO (M : I → E) : N.Ent → E :=
  Function.extend (fun i => Y.entO o (pl i)) M fun _ => 0

theorem entO_inj : Function.Injective (Y.entO o) := fun _ _ h =>
  Sum.inr_injective (Sum.inl_injective ((Y.ν o).symm.injective (eq_of_heq (Sigma.mk.inj h).2)))

end Sig.StdL

namespace Spec
section
variable (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- Under the hypotheses below, the sending is fresh for the wide fact. -/
def stdL_vis : Prop :=
  ∀ (a : LdStage E Kc) (N : Sig E) (Sd : N.Seeds) (Wp' : Type) (L t : N.O → ℕ)
      (Y : N.StdL F) (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → Wp')
      (bk₀ : (∀ i, Y.Dt i → E) → Wp' → a.Wp) (w0 : a.S.Wit × a.Wp) (o : N.O)
      (I : Type) [Fintype (I → E)] [Nonempty (I → E)] (pl : I → Y.Fr o)
      (RdOld : a.S.Ent → Prop) (RrOld : a.S.O → Prop),
    Function.Injective pl → Y.OK t →
    (LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).link.H.Fresh a.J.rels.rel
      (LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).link.P.bud
      ((LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).tgt.wideFact (a.S.sumP N RdOld (Y.rdBut o))
        (a.S.sumO N RrOld (Y.rrBut o)) (a.S.sumP N (fun _ => False) (Y.ownO o pl)) (I → E)
        fun M => a.S.sumV N (fun _ => 0) (Y.valO o pl M)).kc
      (I → E) ((LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).tgt.wideFact
        (a.S.sumP N RdOld (Y.rdBut o)) (a.S.sumO N RrOld (Y.rrBut o))
        (a.S.sumP N (fun _ => False) (Y.ownO o pl)) (I → E)
        fun M => a.S.sumV N (fun _ => 0) (Y.valO o pl M)).put

/-- Under the hypotheses below, it is among the facts that are fresh after the move. -/
def stdL_visAfter : Prop :=
  ∀ (a : LdStage E Kc) (N : Sig E) (Sd : N.Seeds) (Wp' : Type) (L t : N.O → ℕ) (Y : N.StdL F)
      (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → Wp')
      (bk₀ : (∀ i, Y.Dt i → E) → Wp' → a.Wp) (w0 : a.S.Wit × a.Wp) (o : N.O) (I : Type)
      [Fintype (I → E)] [Nonempty (I → E)] (pl : I → Y.Fr o) (RdOld : a.S.Ent → Prop)
      (RrOld : a.S.O → Prop) (base : MaskFact a.J.W → Prop),
    Function.Injective pl → Y.OK t →
    (LdMv.send a (LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0)).After base
      ((LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).tgt.wideFact (a.S.sumP N RdOld (Y.rdBut o))
        (a.S.sumO N RrOld (Y.rrBut o)) (a.S.sumP N (fun _ => False) (Y.ownO o pl)) (I → E)
        fun M => a.S.sumV N (fun _ => 0) (Y.valO o pl M))

end
end Spec

section
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem stdL_vis : Spec.stdL_vis F E Kc := by
  classical
  intro a N Sd Wp' L t Y dat rst bk₀ w0 o I _ _ pl RdOld RrOld hpl h
  have hinj : Function.Injective fun i => Y.entO o (pl i) := fun _ _ e => hpl (Y.entO_inj o e)
  have atF : ∀ (w : a.S.Wit × a.Wp) (k : (Y.Fr o → E) × (Y.Pd o → F)) (x : Y.Fr o),
      Y.upM o (Y.msgOf o (Sum.elim (dat w o) k.1) k.2) (Y.atF o x) = k.1 x :=
    fun w k x => h.lay o _ _ (Sum.inl (Sum.inr x))
  have atD : ∀ (w : a.S.Wit × a.Wp) (k : (Y.Fr o → E) × (Y.Pd o → F)) (x : Y.Dt o),
      Y.upM o (Y.msgOf o (Sum.elim (dat w o) k.1) k.2) ((Y.ν o).symm (Sum.inl (Sum.inl x))) =
        dat w o x :=
    fun w k x => h.lay o _ _ (Sum.inl (Sum.inl x))
  -- over o's pads alone the answers of o are uniform, whatever its free entries
  have key : ∀ ρ (w : a.S.Wit × a.Wp) (x : Y.Fr o → E),
      (unif (Y.Pd o → F)).map (fun η => (Y.mem dat w0 o).ans ρ w (x, η)) =
        (unif (Y.Pd o → F)).map fun η => (Y.mem dat w0 o).ans ρ w ((fun _ => 0), η) := by
    have one : ∀ ρ (w : a.S.Wit × a.Wp) (x : Y.Fr o → E), ∃ Mx : ∀ b, Y.Fr b → E, (Y.mem' dat w0 Mx o).ans ρ w = fun η => (Y.mem dat w0 o).ans ρ w (x, η) := fun ρ w x => by
      refine ⟨fun b => if e : b = o then e ▸ x else fun _ => 0, funext fun η => ?_⟩
      have ex : (if e : o = o then (e ▸ x : Y.Fr o → E) else fun _ => 0) = x := dif_pos rfl
      show (N.om o).Z.val ρ
          (Y.upM o (Y.msgOf o
              (Sum.elim (dat w o) (if e : o = o then (e ▸ x : Y.Fr o → E) else fun _ => 0)) η)) =
        (N.om o).Z.val ρ (Y.upM o (Y.msgOf o (Sum.elim (dat w o) x) η))
      rw [ex]
    intro ρ w x
    obtain ⟨M1, e1⟩ := one ρ w x
    obtain ⟨M2, e2⟩ := one ρ w fun _ => 0
    have h1 := Y.unifM' dat w0 h M1 o ρ w
    have h2 := Y.unifM' dat w0 h M2 o ρ w
    rw [e1] at h1
    rw [e2] at h2
    exact h1.trans h2.symm
  refine segSend_fresh E Kc a (LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0) (I → E)
    (Sig.Sender.ofMemOwn (Y.mem dat w0) (fun w => (w.1, rst w.2)) w0 o (Y.splitO o pl hpl)) RdOld
    (Y.rdBut o) RrOld (Y.rrBut o) (Y.ownO o pl) (Y.valO o pl) ?_ ?_ ?_ ?_ ?_
  · rintro n ⟨i, rfl⟩ _
    exact ⟨_, rfl⟩
  · rintro w M k₀ η n ⟨i, rfl⟩
    show (Y.mem dat w0 o).upM
        ((Y.mem dat w0 o).put w
          ((Sig.Sender.ofMemOwn (Y.mem dat w0) (fun w => (w.1, rst w.2))
              w0 o (Y.splitO o pl hpl)).mk'
            M k₀ η o))
        (Y.atF o (pl i)) =
      Y.valO o pl M (Y.entO o (pl i))
    rw [ofMemOwn_self]
    refine (atF w _ (pl i)).trans (Eq.trans ?_ (hinj.extend_apply M (fun _ => 0) i).symm)
    have hx : ∃ i', pl i' = pl i := ⟨i, rfl⟩
    show (if hh : ∃ i', pl i' = pl i then M hh.choose else k₀.1 ⟨pl i, hh⟩) = M i
    rw [dif_pos hx, hpl hx.choose_spec]
  · rintro w M M' k₀ η η' ⟨b, j⟩ hn ho
    show (Y.mem dat w0 b).upM
        ((Y.mem dat w0 b).put w
          ((Sig.Sender.ofMemOwn (Y.mem dat w0) (fun w => (w.1, rst w.2))
              w0 o (Y.splitO o pl hpl)).mk'
            M k₀ η b)) j =
      (Y.mem dat w0 b).upM
        ((Y.mem dat w0 b).put w
          ((Sig.Sender.ofMemOwn (Y.mem dat w0) (fun w => (w.1, rst w.2))
              w0 o (Y.splitO o pl hpl)).mk'
            M' k₀ η' b)) j
    by_cases hb : b = o
    · subst hb
      rw [ofMemOwn_self, ofMemOwn_self]
      obtain ⟨x, hx⟩ := hn rfl
      have hx' : j = (Y.ν b).symm (Sum.inl x) := hx
      rw [hx']
      rcases x with d | u
      · exact (atD w _ d).trans (atD w _ d).symm
      · have hu : ¬ ∃ i, pl i = u := fun ⟨i, e⟩ => ho ⟨i, by rw [e, hx']; rfl⟩
        refine (atF w _ u).trans (Eq.trans ?_ (atF w _ u).symm)
        show (if hh : ∃ i, pl i = u then M hh.choose else k₀.1 ⟨u, hh⟩) =
          if hh : ∃ i, pl i = u then M' hh.choose else k₀.1 ⟨u, hh⟩
        rw [dif_neg hu, dif_neg hu]
    · rw [ofMemOwn_ne _ _ _ _ _ _ _ _ b hb, ofMemOwn_ne _ _ _ _ _ _ _ _ b hb]
  · refine ofMem_pad E N _ _ (Y.mem dat w0) (fun w => (w.1, rst w.2)) w0 o _ _ _
      (Y.splitO o pl hpl) Sd fun ρ w M M' k => ?_
    exact (key ρ w ((Y.splitO o pl hpl).symm ((M, k), 0)).1).trans
      (key ρ w ((Y.splitO o pl hpl).symm ((M', k), 0)).1).symm
  · intro T hT w M M' k₀ η η'
    obtain ⟨e, he⟩ := ofMem_hid E N _ _ (Y.mem dat w0) (fun w => (w.1, rst w.2)) w0 o _ _ _
      (Y.splitO o pl hpl) t (h.hides o) T hT w M M' k₀ η η'
    exact ⟨e, fun r =>
        ⟨(he r).1, segSend_hid_but E N o (Y.rrBut o) _ _ (fun hh => hh rfl) (he r).2⟩⟩

theorem stdL_visAfter :
    Spec.stdL_visAfter F E
      Kc := fun a N Sd Wp' L t Y dat rst bk₀ w0 o I _ _ pl RdOld RrOld base hpl h =>
  (Chain.freshGiven_one _ base _).2
    (Or.inl (stdL_vis a N Sd Wp' L t Y dat rst bk₀ w0 o I pl RdOld RrOld hpl h))

end
end Cb
