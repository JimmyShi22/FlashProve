-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfProofs.lean: proof of the theorem on the preamble of weights-formedness (Cb/Ld/LdWf.lean:
`Spec.ldWf`; what it states: the docstring of `Spec.ldWf` and the head there). By the composition
lemmas alone. Nothing is assumed beside the hypotheses in the statement's text.

A parameter list is what is asked of one sub-protocol, in two parts: a record of all items but
round-by-round knowledge soundness (`PreListR`, Hiop/RecSubs.lean), and that item, which is a
definition of its own (`PreKnowR`, Hiop/RecSubs.lean). `Spec.ldWf` concludes both, under `P.Laws`
and `B.Hyp` (`PreKnowR`: on the statements without a collision, `C.free`).

Why: the links have their bundles (Cb/Ld/LdWfProofsLinks.lean). The chain is of the two kinds
(Ior/KnowCollRulesChain.lean: `Chain.Ok`): the first link, the sending, has the whole bundle; every
later link is a masked block whose masks are fresh after the chain before it: for a wide reading of
the witness they are fresh after the sending and no lookup in between looks at them (hypotheses);
the block's own reading is coarser (Ior/KnowCollRulesChainConseq.lean).
So the chain as one link has the whole bundle (`chain_ok`). Its formats (`IdxPrefix`, `IdxStep`,
`Passes`, `Hands`) go link by link (Cb/Ld/LdWfPre.lean). The closing rule (Cb/Ld/LdWfClose.lean)
ends the proof.

`H.Fresh Ri bud kc Mk put`: for every (x, y, w) in Ri, every ρ outside `H.withheld w x` and every T
with `bud ρ T`: the distribution of `H.seen …` over uniform coins does not change if its third part
is overwritten by `put M` at an independent uniform M. Here it is a premise: a clause of `B.Fr`
(Cb/Ld/LdWf.lean), asked by the fields `fresh` and `freshB` of `B.Hyp`.

Limits: what the head of Cb/Ld/LdWf.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfProofsLinks
import Cb.Ld.LdWfCloseProofs
import Ior.KnowCollRulesMaskFrame
import Ior.KnowCollRulesChainConseq

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp IOR.Chain

namespace LdWfP
variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample} {P : LdWfP E C}

theorem cLkp_zero (B : P.Blk) : B.cLkp 0 = (Chain.one B.lSend).snoc (B.lLkp 0) := by
  unfold Blk.cLkp
  rw [Chain.fam, append_one]

theorem cLkp_succ (B : P.Blk) (l : ℕ) : B.cLkp (l + 1) = (B.cLkp l).snoc (B.lLkp (l + 1)) := by
  unfold Blk.cLkp
  rw [Chain.fam, append_snoc]

/-! ### Masks sent in advance -/

section Fresh
variable {Kc : Type} (kc : P.W → Kc) (Mk : Type) [Fintype Mk] [Nonempty Mk] (put : Mk → Kc → Kc)

theorem lSend_fresh (hL : P.Laws) (B : P.Blk)
    (hf : (ldSendFamHon P.Sd P.WSt C.E0 B.D).Fresh
      P.A0.rel (ldSendFamNums P.S P.Sd P.WSt C.E0 Unit B.L B.t).bud kc Mk put) :
    B.lSend.H.Fresh P.jIn.rels.rel B.lSend.P.bud kc Mk put :=
  fresh_pre _ _ _ _ _ _ _ _ _ _ _ P.A0.rel P.jIn.rels.rel _ _ _ _ _ kc Mk put
    (fun x y w h => ((step0 hL).acc x y w h).2) hf

omit [Fintype Mk] [Nonempty Mk] in
theorem lLkp_blind (B : P.Blk) (j : ℕ) (hb : (B.sub j).H.Blind kc kc Mk put put) :
    (B.lLkp j).H.Blind kc kc Mk put put :=
  blind_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ kc kc kc Mk put put put
    (fun _ _ _ _ h => ⟨rfl, h⟩) hb

theorem cLkp_fresh (hL : P.Laws) (B : P.Blk)
    (hf : (ldSendFamHon P.Sd P.WSt C.E0 B.D).Fresh
      P.A0.rel (ldSendFamNums P.S P.Sd P.WSt C.E0 Unit B.L B.t).bud kc Mk put) :
    ∀ l, (∀ j, j ≤ l → (B.sub j).H.Blind kc kc Mk put put) → (B.cLkp l).FreshFor kc Mk put
  | 0, hb => by
      rw [cLkp_zero, freshFor_snoc]
      exact Or.inr
        ⟨Kc, kc, put,
          (freshFor_one (A := P.jIn) (B := P.J 0) B.lSend kc Mk put).2
            (lSend_fresh kc Mk put hL B hf),
          lLkp_blind kc Mk put B 0 (hb 0 (Nat.le_refl 0))⟩
  | l + 1, hb => by
      rw [cLkp_succ, freshFor_snoc]
      exact Or.inr
        ⟨Kc, kc, put, cLkp_fresh hL B hf l (fun j hj => hb j (Nat.le_succ_of_le hj)),
          lLkp_blind kc Mk put B (l + 1) (hb (l + 1) (Nat.le_refl _))⟩

/-- Fresh behind the sending alone (`FreshFor`). -/
theorem fr_one (hL : P.Laws) (B : P.Blk) (h : B.Fr 0 kc Mk put) :
    (Chain.one B.lSend).FreshFor kc Mk put := by
  obtain ⟨KW, kW, putW, g, h1, h2, hf, _⟩ := h
  obtain rfl : kc = fun w => g (kW w) := funext h1
  exact freshFor_conseq Unit _ _ (Chain.one B.lSend) KW _ kW g Mk putW put h2
    ((freshFor_one (A := P.jIn) (B := P.J 0) B.lSend kW Mk putW).2 (lSend_fresh kW Mk putW hL B hf))

/-- Fresh behind the sending and the lookups 0, .., l (`FreshFor`): for the wide reading link by
link, then coarsened. -/
theorem fr_cLkp (hL : P.Laws) (B : P.Blk) (l : ℕ) (h : B.Fr (l + 1) kc Mk put) :
    (B.cLkp l).FreshFor kc Mk put := by
  obtain ⟨KW, kW, putW, g, h1, h2, hf, hb⟩ := h
  obtain rfl : kc = fun w => g (kW w) := funext h1
  exact freshFor_conseq Unit _ _ (B.cLkp l) KW _ kW g Mk putW put h2
    (cLkp_fresh kW Mk putW hL B hf l fun j hj => hb j (Nat.lt_succ_of_le hj))

end Fresh

/-! ### The two kinds -/

theorem cLkp_ok (hL : P.Laws) {B : P.Blk} (h : B.Hyp) : ∀ l, l ≤ P.n → (B.cLkp l).Ok
  | 0, hl => by
      rw [cLkp_zero, ok_snoc, ok_one]
      exact ⟨lSend_goodT hL h,
        Or.inr
          ⟨_, lLkp_goodM hL h hl, fr_one (B.Dm 0).kc (B.Dm 0).Mk (B.Dm 0).put hL B (h.fresh 0 hl)⟩⟩
  | l + 1, hl => by
      rw [cLkp_succ, ok_snoc]
      exact ⟨cLkp_ok hL h l (Nat.le_of_succ_le hl),
        Or.inr ⟨_, lLkp_goodM hL h hl,
            fr_cLkp (B.Dm (l + 1)).kc (B.Dm (l + 1)).Mk (B.Dm (l + 1)).put
              hL B l (h.fresh (l + 1) hl)⟩⟩

theorem chain_isOk (hL : P.Laws) {B : P.Blk} (h : B.Hyp) : B.chain.Ok := by
  unfold Blk.chain
  rw [ok_snoc]
  exact ⟨cLkp_ok hL h P.n (Nat.le_refl _),
    Or.inr ⟨DmL B, lBatt_goodM hL h, fr_cLkp B.DmB.kc B.DmB.Mk B.DmB.put hL B P.n h.freshB⟩⟩

theorem link_goodT (hL : P.Laws) {B : P.Blk} (h : B.Hyp) :
    GoodT B.link.R B.link.H P.jIn.rels P.jLast.rels B.link.ext B.link.P :=
  chain_ok Unit _ _ B.chain B.p0 (chain_isOk hL h)

/-! ### The formats -/

theorem lSend_idx (B : P.Blk) : B.lSend.R.IdxPrefix := by
  obtain ⟨_, _, h3, _, h5, _, h7, h8, _⟩ := ldSendFam_data E P.S P.Sd P.WSt C.E0
  exact IdxPrefix.pre ⟨h3, h5, fun _ _ => rfl, h7, fun ρ q => (h8 ρ q).1⟩ _

theorem lBatt_idx : P.lBatt.R.IdxStep := by
  have hc : (P.bt.batt C.E0).OnlyCopies :=
    (OnlyCopies.draw _ _ _).seq
      ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩
  exact ((IdxStep.keep hc.noReads hc.noTie hc.copy hc.src P.S.Smp P.S.ext).pre _).post _

theorem lSend_passes (B : P.Blk) : B.lSend.R.Passes (fun rec => rec) (fun x : P.X => x.1.1) :=
  Passes.pre (r₂ := fun st : P.WSt => st.1) (fun x y τ x' hx => by rw [← Option.some.inj hx]) _ _
    fun x x' hx => by rw [← Option.some.inj hx]; rfl

theorem lLkp_passes {B : P.Blk} (h : B.Hyp) {l : ℕ} (hl : l ≤ P.n) :
    (B.lLkp l).R.Passes (fun x : P.X => x.1.1) (fun x : P.X => x.1.1) :=
  Passes.post (r₂ := fun x : TX P.WSt E P.N × P.S.Smp => x.1.1.1)
    (fun x y τ x' hx => congrArg (fun a : P.X => a.1.1) (h.lkpP l hl x y τ x' hx)) _ _
    fun x x' hx => by obtain ⟨_, rfl⟩ := file_eq l x x' hx; rfl

theorem lBatt_passes :
    P.lBatt.R.Passes (fun x : P.X => x.1.1) (fun b : (P.Cl × C.Rec) × P.S.Smp => b.1.2) := by
  refine Passes.post (r₂ := fun x : P.Cl × P.S.Smp => (P.stOf x.1).1) ?_ _ _
    fun x x' hx => by rw [← Option.some.inj hx]; rfl
  refine Passes.pre (r₂ := fun x : ((P.bt.Q → E) × P.bt.St) × P.S.Smp => P.rcIn x.1) ?_ _ _
    fun x x' hx => by rw [← Option.some.inj hx]; rfl
  exact (Passes.keepX (r₁ := P.rcIn) (r₂ := P.rcOut)
    (fun x y τ z hz => congrArg Prod.fst (batt_st x y τ z hz)) P.S.Smp).keepE P.S.ext

theorem lSend_hands {B : P.Blk} (h : B.Hyp) :
    B.lSend.H.Hands P.jIn.rels.rel (fun p => p) (fun w : P.W => w.2.1) := by
  intro x y w c ρ _ _
  have e := h.sender.back (P.bodyOf w.1.1, (w, ())) c.1
  exact congrArg (fun a : P.Body × P.Wp => a.2.1) e

theorem lLkp_hands {B : P.Blk} (h : B.Hyp) {l : ℕ} (hl : l ≤ P.n) :
    (B.lLkp l).H.Hands (P.J l).rels.rel (fun w : P.W => w.2.1) (fun w : P.W => w.2.1) :=
  Honest.Hands.post (p₂ := fun w : P.W => w.2.1)
    (fun x y w c ρ _ _ => by rw [h.lkpH l hl]) _ _ _ fun _ => rfl

theorem lBatt_hands :
    P.lBatt.H.Hands (P.J (P.n + 1)).rels.rel (fun w : P.W => w.2.1) (fun w : P.W => w.2.1) := by
  have h0 : (idxH C (P.bt.hon C.E0 fun w : (C.Msg × P.S.Msg) × Unit => P.msg w.1)).Hands
      (fun _ _ _ => True) (fun w : P.S.Msg × P.Wp => w.2.1) (fun w : P.S.Msg × P.Wp => w.2.1) :=
    Honest.Hands.mapW _ _ _ _ _ _ fun _ _ => rfl
  have h1 := (h0.keepX P.S.Smp).keepE P.S.ext
  have h2 : (P.S.liftH (idxH C (P.bt.hon C.E0 fun w : (C.Msg × P.S.Msg) × Unit => P.msg w.1))).Hands
      (fun _ _ _ => True) (fun w : P.W => w.2.1) (fun w : P.W => w.2.1) :=
    Honest.Hands.mapW' h1 _ _ _ _ (fun _ _ _ _ => trivial) fun _ _ => rfl
  have h3 := Honest.Hands.pre (Ri' := fun _ _ _ => True) (p₁ := fun w : P.W => w.2.1) h2
    (fun x => some (P.toBatt x)) (ExtMap.id P.Ex) (fun a : P.X × P.W => (P.toBatt a.1, a.2))
    (fun _ _ _ _ => trivial) fun _ => rfl
  have h4 := Honest.Hands.post (p₃ := fun w : P.W => w.2.1) h3 (fun x => some (P.toLast x))
    (ExtMap.id P.Ex) (fun a : (P.Cl × P.S.Smp) × P.W => (P.toLast a.1, a.2)) fun _ => rfl
  exact h4.sub fun _ _ _ _ => trivial

/-- The chain up to the lookup on forest l, as one link: its formats. -/
theorem cLkp_all (hL : P.Laws) {B : P.Blk} (h : B.Hyp) :
    ∀ l, l ≤ P.n →
      ((B.cLkp l).link B.p0).R.IdxPrefix ∧
      ((B.cLkp l).link B.p0).R.Passes (fun rec => rec) (fun x : P.X => x.1.1) ∧
      ((B.cLkp l).link B.p0).H.Hands P.jIn.rels.rel (fun p => p) (fun w : P.W => w.2.1)
  | 0, hl => by
      rw [cLkp_zero, link_snoc, link_one]
      exact ⟨(lSend_idx B).seq ((h.lkpI 0 hl).post _),
        (lSend_passes B).seq (lLkp_passes h hl),
        (lSend_hands h).seq (lSend_goodT hL h).acc (lLkp_hands h hl)⟩
  | l + 1, hl => by
      obtain ⟨h1, h2, h3⟩ := cLkp_all hL h l (Nat.le_of_succ_le hl)
      have g := chain_ok Unit _ _ (B.cLkp l) B.p0 (cLkp_ok hL h l (Nat.le_of_succ_le hl))
      rw [cLkp_succ, link_snoc]
      exact ⟨h1.seq ((h.lkpI (l + 1) hl).post _),
        h2.seq (lLkp_passes h hl),
        h3.seq g.acc (lLkp_hands h hl)⟩

theorem link_all (hL : P.Laws) {B : P.Blk} (h : B.Hyp) :
    B.link.R.IdxPrefix ∧
    B.link.R.Passes (fun rec => rec) (fun b : (P.Cl × C.Rec) × P.S.Smp => b.1.2) ∧
    B.link.H.Hands P.jIn.rels.rel (fun p => p) (fun w : P.W => w.2.1) := by
  obtain ⟨h1, h2, h3⟩ := cLkp_all hL h P.n (Nat.le_refl _)
  have g := chain_ok Unit _ _ (B.cLkp P.n) B.p0 (cLkp_ok hL h P.n (Nat.le_refl _))
  unfold Blk.link Blk.chain
  rw [link_snoc]
  exact ⟨h1.seq lBatt_idx, h2.seq lBatt_passes, h3.seq g.acc lBatt_hands⟩

end LdWfP

/-- The theorem on the preamble of weights-formedness, conditional on its blocks (`B.Hyp`) and on
`P.Laws`: the two parts of the parameter list (`PreListR`, `PreKnowR`). -/
theorem ldWf (E : Type) [Field E] [Fintype E] : Spec.ldWf E := by
  intro C P B hL h
  obtain ⟨h1, h2, h3⟩ := LdWfP.link_all hL h
  exact ldClose E C P.S Unit C.Rec C.PIdx Unit P.Cl P.Wp P.holds B.link.R B.link.H P.jIn.rels
    P.lastB B.link.ext B.link.P id id Prod.fst C.RwfR (fun _ => ()) (B.p0, ()) B.r0
    (LdWfP.link_goodT hL h) h1 h2 h3 (fun _ _ _ hw => hw) (fun _ _ U hU hh => ⟨U, hU, hh⟩)
    (fun _ ha => ha) (fun _ _ _ hw => hw)

end Cb
