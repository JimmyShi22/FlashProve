-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/GlVal/GlThird.lean: proximity tests (groups, towers), the sendings of the link and of the linear
test, the configuration and weights-formedness, for Reed-Solomon codes over the field with
p = 2^64 - 2^32 + 1 elements, at radii within a third of the distance: most hypotheses on codes that
the generic theorems take are derived from the way in which the codes are built.

Definitions (`TowGl`, `TowGGl`), statements (in `Cb.Gl.Spec`) and proofs (an assembly).
F: the integers modulo p; E = F[x] / (x^3 - 2) (Cb/Gl/GlField.lean). Every code is built, by
interleaving and by putting codes side by side, from families of plain Reed-Solomon codes on
subgroups of orders 2^a ≤ 2^32, with rows, read evenly. In Lean this is `GlC C d t`
(Cb/Gl/GlLd.lean): the closure of `IsGl` and of `IsGlCp` (copied plain Reed-Solomon codes,
Cb/Gl/GlCopy.lean), also under complexes (`LdCode.fam`); a closure, because the codes at the joints
of a tower are pairs of interleavings, so `IsGl` itself could not hold of them. Lengths, dimensions,
numbers of rows, readings and radii are parameters.
The records (Cb/Obj/LdObjectThirdTests.lean, Cb/Obj/LdObjectTowerThird.lean,
Cb/Ld/LdWfEndThird.lean) ask of codes: laws, a distance as read, transparency, "reads what it
declares", zero knowledge of the encoding, the core of a code with encoder. All these clauses fall.
(`Spec.glC_code`, Cb/Gl/GlLd.lean: `GlC C d t` → `C.Laws` ∧ `C.Transparent` ∧ `C.Reads` ∧
`C.Dist d` ∧ `C.Zk t`.)
What stays a premise beside `GlC` (for the configuration: beside `Cf.C₀ = rs a k msg r e mca`), in
each statement's text, among them: plain inequalities (3 e < d and the like), samples and
zero-evaders, senders, packings, places, numbers, the model.
`rs a k msg r e mca` (Cb/Gl/GlCodes.lean) is the plain Reed-Solomon code of length 2^a and dimension
k + 1; the message has msg symbols and is followed by r uniform coordinates; the proximity parameter
e and the count mca for mutual correlated agreement are parameters.

Main names ("Stays:" lists the premises that are left beside those on codes):
  `Spec.gl3_conf`: the configuration: `Cf.Third` for `Cf.C₀ = rs a k msg r e mca`. Stays: a ≤ 32,
    k < 2^a, msg + r ≤ k + 1; 3 eM < 2^a - k; the sample map; the model.
  `Spec.gl3_group`: a group: `G.Third d` from "each member's code, at the group's positions, is
    `GlC`". Stays: 3 e < d; `Fits`.
  `Spec.gl3_sndK`, `Spec.gl3_sndL`: the sendings of the link and of the linear test: `S.Third dN`,
    `S.Third dW dU dO`, from `GlC` of each member's code. "Evades" falls too (lists of at most one
    message). Stays: 2 e < d; L = 1; seeds; the senders' three clauses each.
  `Spec.gl3_fold`, `Spec.gl3_switch`: a fold, a code switch of a tower: `Y.Third d e t`,
    `D.Third d' e' t'`, from `GlC` of their codes. Stays: 3 e < d, 2 e' < d'; challenges, degree,
    packing (`Y.PackOK`, `Y.QwDeg`); samples, the batching's zero-evader (`D.Zb.OK`), privacy; for
    the switch, P and P' are not empty.
  `Spec.gl3_base`: the base case's four clauses, from `GlC` of its code. Stays: 3 e < d.
  `TowGl T`, `Spec.gl3_tower`, `Spec.gl3_tail`: a whole tower, any number of stages: `TowGl T`, by
    the recursion of `T.Third`: the three codes of each fold, each new code and the base case's code
    are `GlC` (the fold's output, the mask oracle, the switch's input code follow); the inequalities
    at every joint; challenges, degree, packing (`PackOK`, `QwDeg`), samples, the batching's
    zero-evader (`Zb.OK`), privacy. Then `T.Third`, so the tower is a tail of a chain.
    `TowGGl`, `Spec.gl3_towerG`: on a group's complex, G.P not empty.
  `Spec.gl3_wf`: weights-formedness: `Z.Third p dS` from "each oracle message's code is `GlC`", at a
    configuration on `rs`, and `Z.Rest0 p` (Cb/Ld/LdWfEnd.lean: the clauses that speak neither of a
    code of an oracle message nor of a list, and the sender's three clauses, of which `hides` speaks
    of sender and codes together: see Limits). Stays: what stays in `Spec.gl3_conf`; 3 e < dS o; L o
    = 1.

Limits:
One kind of clause speaks of sender and code together and is asked, not derived: "hides": what the
encodings of the oracle messages sent hide (`S.dS.Nn.Hides (budT t)`; five such clauses in the
offline phase). It stands among the senders' clauses. The sent oracle messages' codes are asked
`GlC` at t = 0 only. For the standard family of two oracle messages it is derived: `Spec.gl3_stdFam`
(under the hypotheses of its statement: `GlC` at t₁, t₂, 2 e₁ < d₁, 2 e₂ < d₂, `Fm.Z₁.OK`,
`Fm.Z₂.OK`, private samples give `Fm.Hyp 1 1 t₁ t₂`; Cb/Ld/LdSendToyFam.lean: `stdFam_all` then
gives the sender's clauses).
In the shaped case of `TowGGl` the laws of the base code and of the mask code, the fold's main code
and the switch's input code are derived; asked of the shape: the law of its re-arrangement, where
rows stand, at least one variable.
This file does not say that the inequalities can be met by numbers of interest.

It says nothing beyond a third, but for the sendings, a switch's new
code and the standard family, of which 2 e < d is asked. It says nothing on lengths above 2^32.
Terms: lean/GLOSSARY.md.
-/
import Cb.Gl.GlLd
import Cb.Obj.LdObjectThirdTestsProofs
import Cb.Obj.LdObjectTowerThird
import Cb.Ld.LdWfEndThird
import Cb.Ld.LdSendToyFam

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks Iop Hiop IOR

/-- All codes of a tower are built from plain Reed-Solomon families; the inequalities at every
joint; what does not speak of codes. By recursion, as `LdTow3.Third`. -/
def TowGl : {a : LdJoint E} → LdTow3 a → Prop
  | _, .base a _ _ d => GlC a.C d 0 ∧ 3 * a.e < d
  | _, @LdTow3.step _ _ _ _ _ _ _ _ _ _ Y sl e S d e' d' rest =>
      (GlC Y.C d 0 ∧ GlC Y.Z d 0 ∧ GlC Y.Zw d S.ts ∧ 3 * e < d ∧
        Function.Injective (Y.reform sl).val ∧ 2 ≤ (Y.reform sl).n ∧
        (Y.reform sl).PackOK ∧ (Y.reform sl).QwDeg) ∧
      (GlC S.Cnew d' rest.toC.q ∧ 2 * e' < d' ∧ (S.D e).Zo.OK ∧
        (S.D e).Zb.OK ∧ (S.D e).Zo.PrivateSim E) ∧
      TowGl rest

/-- The same on a group's complex. -/
def TowGGl {B : Type} [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P] {Sb : B → Type}
    {sl : ∀ b, Slf E (Sb b) G.C.J} {Z : Evader E (G.Row B)} : LdTowG3 G Sb sl Z → Prop
  | .plain T => TowGl T
  | @LdTowG3.shaped _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sh Sw d e' d' rest =>
      (Sh.view.Laws ∧
        (∀ r b, Sh.dst r = .inl b → Sh.ord b = some r) ∧
        (∀ r j, Sh.dst r = .inr j → Sh.kept j = r) ∧
        (∀ r, Sh.ordZ (Sh.dstZ r) = some r) ∧
        1 ≤ Sh.h + Sh.g) ∧
      (GlC Sh.Cb d 0 ∧ GlC Sh.Zb d 0 ∧ GlC Sh.par.Zw d Sw.ts ∧ 3 * G.e < d ∧
        Function.Injective Sh.par.val ∧ 2 ≤ Sh.par.n ∧ Sh.par.PackOK ∧ Sh.par.QwDeg) ∧
      (GlC (Sw.D G.e).Cout d' rest.toC.q ∧ 2 * e' < d' ∧ (Sw.D G.e).Zo.OK ∧
        (Sw.D G.e).Zb.OK ∧ (Sw.D G.e).Zo.PrivateSim E) ∧
      TowGl rest

/-- Where the main rows of a shape stand, as two implications, from `Sh.OK`. -/
theorem shape_main {S : Sig E} {G : Grp S} {Sh : GShape G} (h : Sh.OK) :
    (∀ r b, Sh.dst r = .inl b → Sh.ord b = some r) ∧ ∀ r j, Sh.dst r = .inr j → Sh.kept j = r :=
  ⟨fun r b hb => by have h1 := h.main r; rw [hb] at h1; exact h1,
    fun r j hj => by have h1 := h.main r; rw [hj] at h1; exact h1⟩

namespace Spec

/-- The configuration. -/
def gl3_conf : Prop :=
  ∀ (Cf : LdCf F E) (a k msg r e mca : ℕ), Cf.C₀ = rs a k msg r e mca → a ≤ 32 → k < 2 ^ a →
    msg + r ≤ k + 1 → 3 * Cf.eM < 2 ^ a - k → Cf.Z.OKOn (Ood.PadInF F) → Cf.ModelOK → Cf.Third

/-- A group. -/
def gl3_group : Prop :=
  ∀ (S : Sig E) (G : Grp S) (d : ℕ),
    (∀ a : G.A, GlC ((S.om a.1).C.atPos (G.pos a)) d 0) → 3 * G.e < d → G.Fits → G.Third d

/-- The link's sending. -/
def gl3_sndK : Prop :=
  ∀ (ι κ J Λ : Type) [Fintype ι] [Fintype κ] [Fintype J] (P : LdLkP E ι κ J Λ)
      (S : P.Snd) (dN : P.N.O → ℕ),
    (∀ a, GlC (P.N.om a).C (dN a) 0) → (∀ a, 2 * (P.N.om a).e < dN a) → (∀ a, S.L a = 1) →
    S.Sd.Fair → S.dS.Laws P.back → S.dS.Blind S.Sd → S.dS.Nn.Hides (P.N.budT S.t) → S.Third dN

/-- The linear test's three sendings. -/
def gl3_sndL : Prop :=
  ∀ (ι κ J Y : Type) [Fintype ι] [Fintype κ] [Fintype J] [Fintype Y] (P : LdLinP E ι κ J Y)
      (S : P.Snd) (dW : P.NW.O → ℕ) (dU : P.NU.O → ℕ) (dO : P.NO.O → ℕ),
    (∀ a, GlC (P.NW.om a).C (dW a) 0) → (∀ a, 2 * (P.NW.om a).e < dW a) → (∀ a, S.LW a = 1) →
    P.SdW.Fair → S.dW.Laws P.backW → S.dW.Blind P.SdW → S.dW.Nn.Hides (P.NW.budT S.tW) →
    (∀ a, GlC (P.NU.om a).C (dU a) 0) → (∀ a, 2 * (P.NU.om a).e < dU a) → (∀ a, S.LU a = 1) →
    P.SdU.Fair → S.dU.Laws P.backU → S.dU.Blind P.SdU → S.dU.Nn.Hides (P.NU.budT S.tU) →
    (∀ a, GlC (P.NO.om a).C (dO a) 0) → (∀ a, 2 * (P.NO.om a).e < dO a) → (∀ a, S.LO a = 1) →
    P.SdO.Fair → S.dO.Laws P.backO → S.dO.Blind P.SdO → S.dO.Nn.Hides (P.NO.budT S.tO) →
    S.Third dW dU dO

/-- A fold of a tower. -/
def gl3_fold : Prop :=
  ∀ (P : Type) [Fintype P] (Y : SumPar E P) (d e t : ℕ), GlC Y.C d 0 → GlC Y.Z d 0 → GlC Y.Zw d t →
    3 * e < d → Function.Injective Y.val → 2 ≤ Y.n → Y.PackOK → Y.QwDeg → Y.Third d e t

/-- A code switch of a tower. -/
def gl3_switch : Prop :=
  ∀ (P P' St : Type) [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']
      (D : LdSw E P P' St) (d' e' t' : ℕ),
    GlC D.Cout d' t' → GlC D.Cin 0 0 → 2 * e' < d' → D.Zo.OK → D.Zb.OK →
    D.Zo.PrivateSim E → D.Third d' e' t'

/-- The base case. -/
def gl3_base : Prop :=
  ∀ (a : LdJoint E) (d : ℕ),
    GlC a.C d 0 → 3 * a.e < d → a.C.Laws ∧ a.C.Dist d ∧ 3 * a.e < d ∧ a.C.Transparent

/-- A whole tower, any number of stages. -/
def gl3_tower : Prop := ∀ (a : LdJoint E) (T : LdTow3 a), TowGl T → T.Third

/-- The same on a group's complex. -/
def gl3_towerG : Prop :=
  ∀ (B : Type) [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P] (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (T : LdTowG3 G Sb sl Z),
    TowGGl T → T.Third

/-- So such a tower (`TowGl T`) is a tail of a chain. -/
def gl3_tail : Prop := ∀ (a : LdJoint E) (T : LdTow3 a), TowGl T → T.toC.toEnd.OK T.toC.q

/-- The standard family of two oracle messages (Cb/Ld/LdSendToyFam.lean): under the hypotheses
below, its own hypotheses, so (`stdFam_all`) all that a sending asks of sender and codes together,
what its encodings hide included. -/
def gl3_stdFam : Prop :=
  ∀ (Fm : StdFam E) (d₁ d₂ t₁ t₂ : ℕ), GlC Fm.C₁ d₁ t₁ → GlC Fm.C₂ d₂ t₂ → 2 * Fm.e₁ < d₁ →
    2 * Fm.e₂ < d₂ → Fm.Z₁.OK → Fm.Z₂.OK → (Fm.Z₁.Private E fun _ => True) →
    (Fm.Z₂.Private E fun _ => True) → Fm.Hyp 1 1 t₁ t₂

/-- Weights-formedness. -/
def gl3_wf : Prop :=
  ∀ (Z : LdWfE F E) (p : ℕ) (dS : Z.W.P.S.O → ℕ) (a k msg r e mca : ℕ), Z.W.Cf.C₀ =
      rs a k msg r e mca →
    a ≤ 32 → k < 2 ^ a → msg + r ≤ k + 1 → 3 * Z.W.Cf.eM < 2 ^ a - k →
    Z.W.Cf.Z.OKOn (Ood.PadInF F) → Z.W.Cf.ModelOK → (∀ o, GlC (Z.W.P.S.om o).C (dS o) 0) →
    (∀ o, 3 * (Z.W.P.S.om o).e < dS o) → (∀ o, Z.L o = 1) → Z.Rest0 p → Z.Third p dS

end Spec

theorem gl3_conf : Spec.gl3_conf := by
  intro Cf a k msg r e mca hC ha hk hp h3 hZ hM
  refine ⟨?_, ?_, ?_, hZ, hM⟩
  · rw [hC]
    exact gl_rs_core a k msg r e mca ha hk hp
  · rw [hC]
    exact rs_hasDist msg r e mca ha hk
  · rw [hC, rs_d msg r e mca hk]
    exact h3

theorem gl3_group : Spec.gl3_group := fun _ G d h h3 hF =>
  ⟨fun a => (glC_code G.P _ d 0 (h a)).1, fun a => (glC_code G.P _ d 0 (h a)).2.2.2.1,
    fun a => (glC_code G.P _ d 0 (h a)).2.1, h3, hF⟩

theorem gl3_sndK : Spec.gl3_sndK := fun _ _ _ _ _ _ _ P _ dN h h2 h1 hf hs hb hh =>
  ⟨fun a => (glC_code _ _ _ 0 (h a)).1, fun a => (glC_code _ _ _ 0 (h a)).2.2.2.1, h2, h1, hf,
    fun a => (gl_code_list (P.N.om a) (dN a) 0 (h a) (h2 a)).2, hs, hb, hh⟩

theorem gl3_sndL :
    Spec.gl3_sndL := fun _ _ _ _ _ _ _ _ P _ dW dU dO hW w2 w1 wf ws wb wh hU u2 u1 uf us ub uh hO o2 o1 of' os ob oh =>
  { lawsW := fun a => (glC_code _ _ _ 0 (hW a)).1,
    distW := fun a => (glC_code _ _ _ 0 (hW a)).2.2.2.1, ltW := w2, oneW := w1,
    fairW := wf, evW := fun a => (gl_code_list (P.NW.om a) (dW a) 0 (hW a) (w2 a)).2,
    sndW := ws, blW := wb, hidW := wh
    lawsU := fun a =>
      (glC_code _ _ _ 0 (hU a)).1,
        distU := fun a =>
            (glC_code _ _ _ 0 (hU a)).2.2.2.1,
              ltU := u2, oneU := u1, fairU := uf,
              evU := fun a =>
                  (gl_code_list (P.NU.om a) (dU a) 0 (hU a) (u2 a)).2,
                    sndU := us, blU := ub, hidU := uh
    lawsO := fun a =>
      (glC_code _ _ _ 0 (hO a)).1,
        distO := fun a =>
            (glC_code _ _ _ 0 (hO a)).2.2.2.1,
              ltO := o2, oneO := o1, fairO := of',
              evO := fun a =>
                  (gl_code_list (P.NO.om a) (dO a) 0 (hO a) (o2 a)).2,
                    sndO := os, blO := ob, hidO := oh }

theorem gl3_fold : Spec.gl3_fold := fun P _ Y d _ t hC hZ hW h3 hi hn hp hq =>
  ⟨(glC_code P _ d 0 hC).1, (glC_code P _ d 0 hZ).1, (glC_code P _ d t hW).1,
    (glC_code P _ d 0 hC).2.2.2.1, (glC_code P _ d 0 hZ).2.2.2.1, (glC_code P _ d t hW).2.2.2.1,
    h3, hi, hn, hp, hq, (glC_code P Y.Cw d t (.il _ hW)).2.2.2.2⟩

theorem gl3_switch : Spec.gl3_switch := fun P P' _ _ _ _ _ _ d' _ t' hO hI h2 hZo hZb hp =>
  ⟨(glC_code P' _ d' t' hO).1, (glC_code P' _ d' t' hO).2.2.2.1, h2, (glC_code P _ 0 0 hI).1,
    (glC_code P' _ d' t' hO).2.2.1, hZo, hZb, hp, (glC_code P' _ d' t' hO).2.2.2.2⟩

theorem gl3_base : Spec.gl3_base := fun a d h h3 =>
  ⟨(glC_code a.P _ d 0 h).1, (glC_code a.P _ d 0 h).2.2.2.1, h3, (glC_code a.P _ d 0 h).2.1⟩

theorem gl3_tower : Spec.gl3_tower := by
  intro a T
  induction T with
  | base a t cov d => exact fun h => gl3_base a d h.1 h.2
  | step Y sl e S d e' d' rest ih =>
    rintro ⟨⟨hC, hZ, hW, h3, hi, hn, hp, hq⟩, ⟨hN, h2, hZo, hZb, hP⟩, hr⟩
    refine ⟨gl3_fold _ (Y.reform sl) d e S.ts hC hZ hW h3 hi hn hp hq,
      gl3_switch _ _ _ (S.D e) d' e' rest.toC.q hN ?_ h2 hZo hZb hP,
      ih hr⟩
    exact glC_mono _ _ d 0 0 0
      (.pair hC (.pair hZ (glC_mono _ _ d S.ts d 0 hW le_rfl (Nat.zero_le _)))) (Nat.zero_le _)
      le_rfl

theorem gl3_towerG : Spec.gl3_towerG := by
  intro B _ S G _ Sb sl Z T h
  cases T with
  | plain T => exact gl3_tower _ T h
  | shaped Sh Sw d e' d' rest =>
    obtain ⟨⟨hv, hm1, hm2, hz, h1⟩, ⟨hB, hZ, hW, h3, hi, hn, hp, hq⟩, ⟨hN, h2, hZo, hZb, hP⟩, hr⟩ :=
      h
    have hC : GlC Sh.par.C d 0 := .il _ hB
    have hI : GlC (Sw.D G.e).Cin 0 0 :=
      glC_mono _ _ d 0 0 0
        (.pair hC (.pair hZ (glC_mono _ _ d Sw.ts d 0 hW le_rfl (Nat.zero_le _)))) (Nat.zero_le _)
        le_rfl
    exact ⟨⟨hv, (glC_code _ _ d 0 hB).1, (glC_code _ _ d 0 hZ).1, fun r => by
        split
        · next b hb => exact hm1 r b hb
        · next j hj => exact hm2 r j hj, hz, h1⟩, gl3_fold _ Sh.par d G.e Sw.ts hC hZ hW h3 hi hn hp hq, gl3_switch _ _ _ (Sw.D G.e) d' e' rest.toC.q hN hI h2 hZo hZb hP, gl3_tower _ rest hr⟩

theorem gl3_tail : Spec.gl3_tail := fun a T h => ldTow3_tail E a T (gl3_tower a T h)

theorem gl3_stdFam : Spec.gl3_stdFam := fun _ d₁ d₂ t₁ t₂ h₁ h₂ l₁ l₂ o₁ o₂ p₁ p₂ =>
  have g₁ := glC_code _ _ d₁ t₁ h₁
  have g₂ := glC_code _ _ d₂ t₂ h₂
  ⟨g₁.1, g₂.1, ld_list_unique E _ _ d₁ _ g₁.1 g₁.2.2.2.1 l₁,
    ld_list_unique E _ _ d₂ _ g₂.1 g₂.2.2.2.1 l₂, o₁, o₂, p₁, p₂, g₁.2.2.2.2, g₂.2.2.2.2⟩

theorem gl3_wf : Spec.gl3_wf := fun Z _ _ a k msg r e mca hC ha hk hp h3 hZ hM hG hlt h1 hR =>
  { toRest := { toRest0 := hR, laws := fun o => (glC_code _ _ _ 0 (hG o)).1 }
    conf3 := gl3_conf Z.W.Cf a k msg r e mca hC ha hk hp h3 hZ hM
    one := h1
    dist := fun o => (glC_code _ _ _ 0 (hG o)).2.2.2.1
    lt := hlt }

end Cb.Gl
