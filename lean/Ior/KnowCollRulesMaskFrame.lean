-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowCollRulesMaskFrame.lean: "the masks are fresh" and "does not look at the masks" through the
constructions that add no round.

The matter is sequential composition of interactive oracle reductions (IORs, Ior/Ior.lean).
Statements and proofs. No protocol, no code occurs here.
A block is an IOR with its honest side H (`IOR.Honest`, Ior/Honest.lean), taken as a part of a
chain. A prefix is all of a chain that comes before a given block, as one IOR with its honest side.
A link is here an IOR with its honest side, as a step of a chain (as a record with extractor and
numbers: `IOR.Link`, Ior/KnowCollRulesChain.lean).

Ior/KnowCollRulesMask.lean has two properties of honest sides: `H.Fresh` (given all that a run
shows, the masks are still uniform and independent of the rest of what is read of the witness
handed on) and `H.Blind` (a link sends the same whatever the masks are, and hands them on).
Exactly, of `H.Fresh Ri bud kc Mk put`, for a non-empty `Mk`: on every triple of Ri, at every ρ
that is not withheld, for every set T of further positions within the budget, the triple (what the
run shows at T, the explicit part handed on, kc of the witness handed on) has the same law, over
the prefix's coins, as the triple in which the own mask entries are overwritten by fresh uniform
ones (`Honest.Fresh`, Ior/KnowCollRulesMask.lean).
A block is seldom used as it is defined: it acts on a part of a larger statement (Ior/Frame.lean:
`keepX`, `keepE`, `carry`, `pre`, `post`; Ior/KnowCollRulesFrame.lean: `mapW`). Here `Fresh` is
carried through all of these, `Blind` through all but `carry`, each under the hypotheses of its
statement.

Main names:
  `MaskKit.fresh_push`, for non-empty `C` and `Mk`: the one lemma on laws that all the rules for
    `Fresh` of this file use: if what is seen of the new run is ψ (what is seen of the old run),
    and ψ commutes with the overwriting of the masks, the equation of laws goes over.
  `Spec.fresh_mapW`: the witness re-typed: Ri' gives Ri at fi w; the new reading of the new last
    witness is g w (old reading of the old one), g w commuting with the overwriting.
    `Spec.fresh_carry`: a further part of the witness, read in full.
  `Spec.fresh_keepX`, `Spec.fresh_keepE`: copied components.
  `Spec.fresh_pre`: a step without rounds before: Ri' gives Ri at the step's image (m, g.map).
  `Spec.fresh_post`: a step without rounds after: explicit part and reading after the step are G
    (explicit part, reading before it), G commuting with the overwriting.
  `Spec.blind_mapW`, `Spec.blind_keepX`, `Spec.blind_keepE`, `Spec.blind_pre`, `Spec.blind_post`:
    the like for `Blind`, each under the hypotheses of its statement.
  `Spec.blind_seq`: two blind links in a row are a blind link (with one reading and overwriting at
    the joint: kc₂, put₂).

Limits: this file says nothing on constructions that change the rounds, but for two in a row
(`Spec.blind_seq`).
Terms: lean/GLOSSARY.md.
-/
import Ior.KnowCollRulesMaskProofs
import Ior.KnowCollRulesFrameProofs

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace MaskKit

/-- For non-empty `C` and `Mk`: the equation of laws goes over along a map that commutes with the
overwriting. -/
theorem fresh_push {C Mk V X K V' X' K' : Type} [Fintype C] [Nonempty C] [Fintype Mk] [Nonempty Mk]
    (s : C → V × X × K) (ψ : V × X × K → V' × X' × K') (put : Mk → K → K) (put' : Mk → K' → K')
    (hψ : ∀ z M, ψ (z.1, z.2.1, put M z.2.2) = ((ψ z).1, (ψ z).2.1, put' M (ψ z).2.2))
    (e : (unif (C × Mk)).map (fun a => ((s a.1).1, (s a.1).2.1, put a.2 (s a.1).2.2)) =
      (unif C).map s) :
    (unif (C × Mk)).map (fun a => ((ψ (s a.1)).1, (ψ (s a.1)).2.1, put' a.2 (ψ (s a.1)).2.2)) =
      (unif C).map fun c => ψ (s c) := by
  have e' := congrArg (PMF.map ψ) e
  rw [PMF.map_comp, PMF.map_comp] at e'
  refine Eq.trans (congrArg (fun f => PMF.map f (unif (C × Mk))) (funext fun a => ?_)) e'
  exact (hψ (s a.1) a.2).symm

end MaskKit

namespace Spec
open IOR

def fresh_mapW : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wi' Wo Wo' : Type)
      (H : R.Honest Wi Wo) (fi : Wi' → Wi) (fo : Wi' → Wo → Wo') (Ri : Xi → Ei.Str → Wi → Prop)
      (Ri' : Xi → Ei.Str → Wi' → Prop) (bud : Rho R.shape → Finset (OPos R.shape) → Prop)
      (Kc Kc' : Type) (kc : Wo → Kc) (kc' : Wo' → Kc') (g : Wi' → Kc → Kc') (Mk : Type) [Fintype Mk]
      [Nonempty Mk] (put : Mk → Kc → Kc) (put' : Mk → Kc' → Kc'),
    (∀ x y w, Ri' x y w → Ri x y (fi w)) → (∀ w wo, kc' (fo w wo) = g w (kc wo)) →
    (∀ w M k, g w (put M k) = put' M (g w k)) → H.Fresh Ri bud kc Mk put →
    (H.mapW fi fo).Fresh Ri' bud kc' Mk put'

def fresh_carry : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wz : Type) (H : R.Honest Wi Wo)
      (Ri : Xi → Ei.Str → Wi → Prop) (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (Kc : Type)
      (kc : Wo → Kc) (Mk : Type) [Fintype Mk] [Nonempty Mk] (put : Mk → Kc → Kc),
    H.Fresh Ri bud kc Mk put →
    (H.carry Wz).Fresh (fun x y w => Ri x y w.1) bud (fun w : Wo × Wz => (kc w.1, w.2))
      Mk (fun M k => (put M k.1, k.2))

def fresh_keepX : Prop :=
  ∀ (Xi Xo Z : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (Ri : Xi → Ei.Str → Wi → Prop) (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (Kc : Type)
      (kc : Wo → Kc) (Mk : Type) [Fintype Mk] [Nonempty Mk] (put : Mk → Kc → Kc),
    H.Fresh Ri bud kc Mk put → (H.keepX Z).Fresh (fun a y w => Ri a.1 y w) bud kc Mk put

def fresh_keepE : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo F : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (Ri : Xi → Ei.Str → Wi → Prop) (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (Kc : Type)
      (kc : Wo → Kc) (Mk : Type) [Fintype Mk] [Nonempty Mk] (put : Mk → Kc → Kc),
    H.Fresh Ri bud kc Mk put → (H.keepE F).Fresh (fun x y w => Ri x y.1 w) bud kc Mk put

def fresh_pre : Prop :=
  ∀ (Xi Xi' Xo : Type) (Ei Ei' Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wi' Wo : Type)
      (H : R.Honest Wi Wo) (Ri : Xi → Ei.Str → Wi → Prop) (Ri' : Xi' → Ei'.Str → Wi' → Prop)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (f : Xi' → Option Xi)
      (g : ExtMap Ei' Ei) (m : Xi' × Wi' → Xi × Wi) (Kc : Type) (kc : Wo → Kc) (Mk : Type)
      [Fintype Mk] [Nonempty Mk] (put : Mk → Kc → Kc),
    (∀ x y w, Ri' x y w → Ri (m (x, w)).1 (g.map y) (m (x, w)).2) →
    H.Fresh Ri bud kc Mk put → (H.pre f g m).Fresh Ri' bud kc Mk put

/-- A step without rounds after. -/
def fresh_post : Prop :=
  ∀ (Xi Xo Xo' : Type) (Ei Eo Eo' : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wo' : Type)
      (H : R.Honest Wi Wo) (Ri : Xi → Ei.Str → Wi → Prop)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (f : Xo → Option Xo')
      (g : ExtMap Eo Eo') (m : Xo × Wo → Xo' × Wo') (Kc Kc' : Type) (kc : Wo → Kc)
      (kc' : Wo' → Kc') (G : Xo × Kc → Xo' × Kc') (Mk : Type) [Fintype Mk] [Nonempty Mk]
      (put : Mk → Kc → Kc) (put' : Mk → Kc' → Kc'),
    (∀ xo wo, ((m (xo, wo)).1, kc' (m (xo, wo)).2) = G (xo, kc wo)) →
    (∀ xo M k, G (xo, put M k) = ((G (xo, k)).1, put' M (G (xo, k)).2)) →
    H.Fresh Ri bud kc Mk put → (H.post f g m).Fresh Ri bud kc' Mk put'

def blind_mapW : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wi' Wo Wo' : Type)
      (H : R.Honest Wi Wo) (fi : Wi' → Wi) (fo : Wi' → Wo → Wo') (Ki Ki' Ko Ko' : Type)
      (kci : Wi → Ki) (kco : Wo → Ko) (kci' : Wi' → Ki') (kco' : Wo' → Ko') (Mk : Type)
      (puti : Mk → Ki → Ki) (puto : Mk → Ko → Ko) (puti' : Mk → Ki' → Ki') (puto' : Mk → Ko' → Ko'),
    (∀ w w' M, kci' w' = puti' M (kci' w) → kci (fi w') = puti M (kci (fi w))) →
    (∀ w w' M wo wo', kci' w' = puti' M (kci' w) → kco wo' = puto M (kco wo) →
      kco' (fo w' wo') = puto' M (kco' (fo w wo))) →
    H.Blind kci kco Mk puti puto → (H.mapW fi fo).Blind kci' kco' Mk puti' puto'

def blind_keepX : Prop :=
  ∀ (Xi Xo Z : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (Ki Ko : Type) (kci : Wi → Ki) (kco : Wo → Ko) (Mk : Type)
      (puti : Mk → Ki → Ki) (puto : Mk → Ko → Ko),
    H.Blind kci kco Mk puti puto → (H.keepX Z).Blind kci kco Mk puti puto

def blind_keepE : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo F : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (Ki Ko : Type) (kci : Wi → Ki) (kco : Wo → Ko) (Mk : Type)
      (puti : Mk → Ki → Ki) (puto : Mk → Ko → Ko),
    H.Blind kci kco Mk puti puto → (H.keepE F).Blind kci kco Mk puti puto

/-- The step before maps the explicit part by mx and the witness by mw (which may read the explicit
part). -/
def blind_pre : Prop :=
  ∀ (Xi Xi' Xo : Type) (Ei Ei' Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wi' Wo : Type)
      (H : R.Honest Wi Wo) (f : Xi' → Option Xi) (g : ExtMap Ei' Ei) (mx : Xi' → Xi)
      (mw : Xi' → Wi' → Wi) (Ki Ki' Ko : Type) (kci : Wi → Ki) (kci' : Wi' → Ki') (kco : Wo → Ko)
      (Mk : Type) (puti : Mk → Ki → Ki) (puti' : Mk → Ki' → Ki') (puto : Mk → Ko → Ko),
    (∀ x w w' M, kci' w' = puti' M (kci' w) → kci (mw x w') = puti M (kci (mw x w))) →
    H.Blind kci kco Mk puti puto →
    (H.pre f g fun a => (mx a.1, mw a.1 a.2)).Blind kci' kco Mk puti' puto

def blind_post : Prop :=
  ∀ (Xi Xo Xo' : Type) (Ei Eo Eo' : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wo' : Type)
      (H : R.Honest Wi Wo) (f : Xo → Option Xo') (g : ExtMap Eo Eo') (m : Xo × Wo → Xo' × Wo')
      (Ki Ko Ko' : Type) (kci : Wi → Ki) (kco : Wo → Ko) (kco' : Wo' → Ko') (Mk : Type)
      (puti : Mk → Ki → Ki) (puto : Mk → Ko → Ko) (puto' : Mk → Ko' → Ko'),
    (∀ xo wo wo' M, kco wo' = puto M (kco wo) →
      (m (xo, wo')).1 = (m (xo, wo)).1 ∧ kco' (m (xo, wo')).2 = puto' M (kco' (m (xo, wo)).2)) →
    H.Blind kci kco Mk puti puto → (H.post f g m).Blind kci kco' Mk puti puto'

/-- States, under the hypotheses below: two blind links in a row are a blind link. -/
def blind_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (K₁ K₂ K₃ : Type)
      (kc₁ : W₁ → K₁) (kc₂ : W₂ → K₂) (kc₃ : W₃ → K₃) (Mk : Type) (put₁ : Mk → K₁ → K₁)
      (put₂ : Mk → K₂ → K₂) (put₃ : Mk → K₃ → K₃),
    H₁.Blind kc₁ kc₂ Mk put₁ put₂ → H₂.Blind kc₂ kc₃ Mk put₂ put₃ →
    (H₁.seq H₂).Blind kc₁ kc₃ Mk put₁ put₃

end Spec

open IOR MaskKit

theorem fresh_mapW : Spec.fresh_mapW := by
  intro Xi Xo Ei Eo R Wi Wi' Wo Wo' H fi fo Ri Ri' bud Kc Kc' kc kc' g Mk _ _ put put' hR hk
    hg hF x y w hw ρ hρ T hT
  have e := fresh_push (H.seen kc (fi w) x ρ T) (fun z => (z.1, z.2.1, g w z.2.2)) put put' (fun z M => by
    show (z.1, z.2.1, g w (put M z.2.2)) = (z.1, z.2.1, put' M (g w z.2.2))
    rw [hg]) (hF x y (fi w) (hR x y w hw) ρ hρ T hT)
  have s : ∀ c : H.Coin, (H.mapW fi fo).seen kc' w x ρ T c =
      ((H.seen kc (fi w) x ρ T c).1,
        (H.seen kc (fi w) x ρ T c).2.1,
        g w (H.seen kc (fi w) x ρ T c).2.2) := by
    intro c
    unfold Honest.seen
    rw [Honest.mapW_run, hk]
  refine Eq.trans (congrArg (fun f => PMF.map f (unif (H.Coin × Mk))) (funext fun a => ?_))
    (e.trans (congrArg (fun f => PMF.map f (unif H.Coin)) (funext fun c => (s c).symm)))
  rw [s a.1]

theorem fresh_carry : Spec.fresh_carry := by
  intro Xi Xo Ei Eo R Wi Wo Wz H Ri bud Kc kc Mk _ _ put hF
  exact fresh_mapW Xi Xo Ei Eo R Wi (Wi × Wz) Wo (Wo × Wz) H Prod.fst (fun w o => (o, w.2)) Ri
    (fun x y w => Ri x y w.1) bud Kc (Kc × Wz) kc (fun w => (kc w.1, w.2)) (fun w k => (k, w.2))
    Mk put (fun M k => (put M k.1, k.2)) (fun _ _ _ h => h) (fun _ _ => rfl) (fun _ _ _ => rfl) hF

theorem fresh_keepX : Spec.fresh_keepX := by
  intro Xi Xo Z Ei Eo R Wi Wo H Ri bud Kc kc Mk _ _ put hF a y w hw ρ hρ T hT
  have e := fresh_push (H.seen kc w a.1 ρ T) (fun z => (viewKeepX R Z z.1, (z.2.1, a.2), z.2.2))
    put put (fun _ _ => rfl) (hF a.1 y w hw ρ hρ T hT)
  have s : ∀ c : H.Coin, (H.keepX Z).seen kc w a ρ T c =
      (viewKeepX R Z (H.seen kc w a.1 ρ T c).1,
        ((H.seen kc w a.1 ρ T c).2.1, a.2),
        (H.seen kc w a.1 ρ T c).2.2) := by
    intro c
    unfold Honest.seen
    rw [Honest.keepX_run]
    rfl
  refine Eq.trans (congrArg (fun f => PMF.map f (unif (H.Coin × Mk))) (funext fun b => ?_))
    (e.trans (congrArg (fun f => PMF.map f (unif H.Coin)) (funext fun c => (s c).symm)))
  rw [s b.1]

theorem fresh_keepE : Spec.fresh_keepE := by
  intro Xi Xo Ei Eo F R Wi Wo H Ri bud Kc kc Mk _ _ put hF x y w hw ρ hρ T hT
  exact fresh_push (H.seen kc w x ρ T) (fun z => (View.keepE F z.1, z.2.1, z.2.2)) put put
    (fun _ _ => rfl) (hF x y.1 w hw ρ hρ T hT)

theorem fresh_pre : Spec.fresh_pre := by
  intro Xi Xi' Xo Ei Ei' Eo R Wi Wi' Wo H Ri Ri' bud f g m Kc kc Mk _ _ put hR hF x y w hw ρ hρ T hT
  exact fresh_push (H.seen kc (m (x, w)).2 (m (x, w)).1 ρ T)
    (fun z => (View.pre f g z.1, z.2.1, z.2.2)) put put
    (fun _ _ => rfl) (hF _ _ _ (hR x y w hw) ρ hρ T hT)

theorem fresh_post : Spec.fresh_post := by
  intro Xi Xo Xo' Ei Eo Eo' R Wi Wo Wo' H Ri bud f g m Kc Kc' kc kc' G Mk _ _ put put' hG
    hp hF x y w hw ρ hρ T hT
  have e := fresh_push (H.seen kc w x ρ T) (fun z => (View.post f g z.1, (G (z.2.1, z.2.2)).1, (G (z.2.1, z.2.2)).2)) put put' (fun z M => by
    show (_, (G (z.2.1, put M z.2.2)).1, (G (z.2.1, put M z.2.2)).2) = _
    rw [hp]) (hF x y w hw ρ hρ T hT)
  have s : ∀ c : H.Coin, (H.post f g m).seen kc' w x ρ T c =
      (View.post f g (H.seen kc w x ρ T c).1,
        (G ((H.seen kc w x ρ T c).2.1, (H.seen kc w x ρ T c).2.2)).1,
        (G ((H.seen kc w x ρ T c).2.1, (H.seen kc w x ρ T c).2.2)).2) := by
    intro c
    have r : ((H.post f g m).strat w x c).run ρ =
        (((H.strat w x c).run ρ).1, m ((H.strat w x c).run ρ).2) :=
      Strat.run_map _ _ _
    unfold Honest.seen
    rw [r, ← hG]
    rfl
  refine Eq.trans (congrArg (fun f => PMF.map f (unif (H.Coin × Mk))) (funext fun a => ?_))
    (e.trans (congrArg (fun f => PMF.map f (unif H.Coin)) (funext fun c => (s c).symm)))
  rw [s a.1]

theorem blind_mapW : Spec.blind_mapW := by
  intro Xi Xo Ei Eo R Wi Wi' Wo Wo' H fi fo Ki Ki' Ko Ko' kci kco kci' kco' Mk puti puto puti'
    puto' h1 h2 hB w w' M x c ρ h
  obtain ⟨b1, b2, b3⟩ := hB (fi w) (fi w') M x c ρ (h1 w w' M h)
  rw [Honest.mapW_run, Honest.mapW_run]
  exact ⟨b1, b2, h2 w w' M _ _ h b3⟩

theorem blind_keepX : Spec.blind_keepX := by
  intro Xi Xo Z Ei Eo R Wi Wo H Ki Ko kci kco Mk puti puto hB w w' M a c ρ h
  obtain ⟨b1, b2, b3⟩ := hB w w' M a.1 c ρ h
  rw [Honest.keepX_run, Honest.keepX_run]
  exact ⟨b1, congrArg (fun xo => (xo, a.2)) b2, b3⟩

theorem blind_keepE : Spec.blind_keepE := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB w w' M x c ρ h =>
  hB w w' M x c ρ h

theorem blind_pre : Spec.blind_pre :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ mx mw _ _ _ _ _ _ _ _ _ _ h1 hB w w' M x c ρ h =>
    hB (mw x w) (mw x w') M (mx x) c ρ (h1 x w w' M h)

theorem blind_post : Spec.blind_post := by
  intro Xi Xo Xo' Ei Eo Eo' R Wi Wo Wo' H f g m Ki Ko Ko' kci kco kco' Mk puti puto
    puto' h1 hB w w' M x c ρ h
  obtain ⟨b1, b2, b3⟩ := hB w w' M x c ρ h
  have r : ∀ v : Wi, ((H.post f g m).strat v x c).run ρ =
      (((H.strat v x c).run ρ).1, m ((H.strat v x c).run ρ).2) :=
    fun v => Strat.run_map _ _ _
  rw [r, r]
  have e : ((H.strat w' x c).run ρ).2 =
      (((H.strat w x c).run ρ).2.1, ((H.strat w' x c).run ρ).2.2) := Prod.ext b2 rfl
  obtain ⟨c1, c2⟩ :=
    h1 ((H.strat w x c).run ρ).2.1 ((H.strat w x c).run ρ).2.2 ((H.strat w' x c).run ρ).2.2 M b3
  refine ⟨b1, ?_, ?_⟩
  · show (m ((H.strat w' x c).run ρ).2).1 = (m ((H.strat w x c).run ρ).2).1
    rw [e]
    exact c1
  · show kco' (m ((H.strat w' x c).run ρ).2).2 = puto' M (kco' (m ((H.strat w x c).run ρ).2).2)
    rw [e]
    exact c2

theorem blind_seq : Spec.blind_seq := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ K₁ K₂ K₃ kc₁ kc₂ kc₃ Mk put₁ put₂
    put₃ h₁ h₂ w w' M x c ρ h
  obtain ⟨a1, a2, a3⟩ := h₁ w w' M x c.1 (Rho.fst ρ) h
  obtain ⟨b1, b2, b3⟩ := h₂ ((H₁.strat w x c.1).run (Rho.fst ρ)).2.2
    ((H₁.strat w' x c.1).run (Rho.fst ρ)).2.2 M ((H₁.strat w x c.1).run (Rho.fst ρ)).2.1 c.2
    (Rho.snd (s := R₁.shape) ρ) a3
  rw [Honest.run_seq, Honest.run_seq]
  dsimp only
  rw [a1, a2, b1, b2, b3]
  exact ⟨rfl, rfl, rfl⟩

end Iop
