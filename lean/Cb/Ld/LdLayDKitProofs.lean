-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLayDKitProofs.lean: four definitions of Cb/Ld/LdLayDKit.lean (`LdPend.JD`, `LdPend.StepD`,
`LdSendD.StdBl`, `LdSendD.LaysD`) tied to the calculus of fresh facts (`MaskFact`,
Cb/Req1/LdSegFresh.lean; its closure `MaskFact.JCl`, Cb/Req1/LdSegFreshS.lean).

In standard terms: book-keeping for the honest prover's side of a request's sub-protocol: the four
definitions named above, conditions on which entries of earlier oracle messages a later step uses
and on who reads them in between, are tied to the predicates on facts, senders and honest provers
that other files work with. Theorems.
A `MaskFact W` is a reading `kc` of witnesses of type W into a type `Kc`, a finite, non-empty type
`Mk`, and a map `put : Mk → Kc → Kc`.

Main names:
  `ldLayD_jd`: the closure on data goes into the closure of facts: if every block of X has its fact
    in `JCl G`, so has every block of `JD X`.
  `ldLayD_step`: under the own condition of a step without rounds (`h : LdPend.StepD m β β'`), if
    the fact of β is in a set G that is closed under `JCl`, there is some g in G that the step hands
    on as the fact of β' (`LdMv.After`, Cb/Req1/LdReq.lean).
  `ldLayD_noLook`, `ldLayD_one`: `d.StdBl Q` gives "the sender does not look", and, for Q sound, the
    two clauses on the sender of a closing's one sending at a crossing (`Spec.stdSend_one`,
    Cb/Req1/LdReqStdFresh.lean).
  `ldLayD_lays`: `d.LaysD Q`, Q sound, gives: d's link is `Fresh` for the block's fact. Here `Fresh`
    is the conclusion. `H.Fresh Ri bud kc Mk put`: for every (x, y, w) in Ri, every ρ outside
    `H.withheld w x` and every T with `bud ρ T`: the distribution of `H.seen …` over uniform coins
    does not change if its third part is overwritten by `put M` at an independent uniform M.
    `H.seen kc w x ρ T c` is a triple: the view with T of the honest prover's run at ρ with the
    coins c, the explicit statement with which it ends, and `kc` of the witness with which it ends.

Limits: This file says nothing on any instance.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLayDKit
import Cb.Req1.LdSegCarryJoin
import Cb.Req1.LdSegRefLastLay

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

section
variable {E Kc : Type} [Field E] [Fintype E]

/-- The closure on data goes into the closure of facts. -/
theorem ldLayD_jd {a : LdStage E Kc} (X : LdPend a → Prop) (G : MaskFact a.J.W → Prop)
    (h : ∀ β, X β → MaskFact.JCl G β.fact) :
    ∀ β, LdPend.JD X β → MaskFact.JCl G β.fact := by
  intro β hβ
  induction hβ with
  | base β hx => exact h β hx
  | pair β₁ β₂ Rd Rr hd hr ho _ _ i1 i2 =>
    exact wideJ_pair a G β₁.Rd β₂.Rd Rd β₁.Rr β₂.Rr Rr β₁.own β₂.own β₁.Mk β₂.Mk
      β₁.val β₂.val hd hr ho i1 i2
  | less β Rd Rr h1 h2 h3 _ ih => exact wideJ_sub a G β.Rd Rd β.Rr Rr β.own β.Mk β.val h1 h2 h3 ih
  | reMk β Mk' e _ ih => exact MaskFact.JCl.equiv β.fact Mk' e ih
  | same β own val h1 h2 _ ih =>
      have e := LdStage.wideFact_ext a β.Rd β.Rr β.own own β.Mk β.val val h1 h2
      show MaskFact.JCl G (a.wideFact β.Rd β.Rr own β.Mk val)
      rw [← e]
      exact ih

/-- A step's own condition: under `hG`, `hβ`, `h` there is some g in G that the step hands on as the
fact of β'. -/
theorem ldLayD_step {a b : LdStage E Kc} (f : a.X → Option b.X) (g₀ : ExtMap a.Ex b.Ex)
    (m : a.X × a.W → b.X × b.W) (back : a.X × a.Ex.Str → b.W → a.W)
    (G : MaskFact a.J.W → Prop) (hG : ∀ f, MaskFact.JCl G f → G f) (β : LdPend a)
    (β' : LdPend b) (hβ : G β.fact) (h : LdPend.StepD m β β') :
    ∃ g, G g ∧ ∀ Y : MaskFact a.J.W → Prop, Y g → (LdMv.step a b f g₀ m back).After Y β'.fact := by
  obtain ⟨e, he⟩ := h
  refine ⟨⟨β.fact.Kc, β.fact.kc, β'.Mk, fun M k => β.fact.put (e.symm M) k⟩,
    hG _ (MaskFact.JCl.equiv β.fact β'.Mk e (.base _ hβ)),
    fun Y hY => ?_⟩
  exact segCarry_step a b f g₀ m back Y _ β'.fact.Kc β'.fact.kc β'.fact.put hY fun x w w' M hk => by
    have h1 := he x w w' (e.symm M) hk
    rw [e.apply_symm_apply] at h1
    exact h1

end

section
variable {E Kc : Type} [Field E] [Fintype E]

theorem ldLayD_noLook :
    ∀ (a : LdStage E Kc) (d : LdSendD a) (Rd : a.S.Ent → Prop) (Rr : a.S.O → Prop)
        (own : a.S.Ent → Prop) (Q : LdLayQ E),
      d.StdBl Q Rd Rr own → d.NoLook Rd Rr own := by
  rintro a ⟨N, Sd, Wp', bk, D, L, t⟩ Rd Rr own Q ⟨F, _, _, _, Y, dat, rst, bk₀, w0, h, -, -, hd⟩
  have h' : (⟨N, Sd, Wp', bk, D, L, t⟩ : LdSendD a) = LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0 :=
    h
  rw [h']
  exact stdSend_noLook F E Kc a N Sd Wp' L t Y dat rst bk₀ w0 Rd Rr own hd

theorem ldLayD_one :
    ∀ (a : LdStage E Kc) (d : LdSendD a) (Rd : a.S.Ent → Prop) (Rr : a.S.O → Prop)
        (own : a.S.Ent → Prop) (Q : LdLayQ E),
      Q.Sound → d.StdBl Q Rd Rr own →
      d.D.Laws (a.S.backN d.N d.bk) ∧
      ∀ w w' : a.W, a.S.Alike Rd own (a.S.msgs w.1) (a.S.msgs w'.1) →
        (∀ o, Rr o → (w'.1 o).2 = (w.1 o).2) → w'.2 = w.2 →
        (∀ k, d.D.put w' k = d.D.put w k) ∧ (d.D.rest w').2 = (d.D.rest w).2 := by
  rintro a ⟨N, Sd, Wp', bk, D, L, t⟩ Rd Rr own Q hQ
    ⟨F, _, _, _, Y, dat, rst, bk₀, w0, h, h1, h2, hd⟩
  have h' : (⟨N, Sd, Wp', bk, D, L, t⟩ : LdSendD a) = LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0 :=
    h
  rw [h']
  exact stdSend_one F E Kc a N Sd Wp' L t Y dat rst bk₀ w0 Rd Rr own (hQ _ _ _ _ h1) h2 hd

/-- Under `hQ`, `h`: the sending is Fresh for the fact of a block that it lays. -/
theorem ldLayD_lays (a : LdStage E Kc) (d : LdSendD a) (β : LdPend d.tgt) (Q : LdLayQ E)
    (hQ : Q.Sound) (h : d.LaysD Q β) :
    d.link.H.Fresh a.J.rels.rel d.link.P.bud β.fact.kc β.fact.Mk β.fact.put := by
  obtain ⟨F, _, _, _, Y, dat, rst, bk₀, w0, hS, hY, h⟩ := h
  rcases h with ⟨I, _, _, _, pl, RdOld, RrOld, hpl, rfl⟩ | ⟨o, I, _, _, pl, RdOld, RrOld, hpl, rfl⟩
  · exact ldReqStdLay_fresh F E Kc a d Y dat rst bk₀ w0 I pl RdOld RrOld hS hpl (hQ _ _ _ _ hY)
  · exact ldReqStdLay_freshVis F E Kc a d Y dat rst bk₀ w0 o I pl RdOld RrOld hS hpl (hQ _ _ _ _ hY)

end
end Cb
