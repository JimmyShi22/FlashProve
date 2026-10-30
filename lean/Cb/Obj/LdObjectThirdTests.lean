-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectThirdTests.lean: the link's and the offline linear test's parameter lists; no bound
on lists or on agreement is assumed: all radii within a third of the distance (exactly: the radii of
the encoded index and of the groups; the sendings' radii: see `S.Third`, `Sn.Third`).

In standard terms: two sub-protocols, the sub-protocol for the claim that two encoded indices hold
the same index (the link) and the proximity test with claims at one instance, where the radii of the
encoded index and of the groups are below a third of the minimum distance.

Definitions and statements (`Cb.Spec.ldT3_end` to `Cb.Spec.ldT3_lin`); the proofs are in
Cb/Obj/LdObjectThirdTestsProofs.lean. Lists: `LdCode.ListAt`; agreement (mutual correlated
agreement): `LdCode.MCAat` (both in Cb/Ld/LdRel.lean).

Why: the theorems on the link with its closing (`ldOl_full`, Cb/Obj/LdObjectLinkFull.lean) and on
the test for linear constraints at one instance with its closing (`ldOLF_lin`,
Cb/Obj/LdObjectLinFull.lean; the plan without a splitting: Cb/Ld/LdLinClosePlan.lean) take bounds on
lists and counts of exceptional coefficients ("agreement"; for the folds; the link through
`FoldErr`, by `ldLk_foldErr_rec`, Cb/Ld/LdLink.lean) as hypotheses. Beyond a third of the distance
such bounds are facts on codes that the tree proves for toy codes only (Cb/Ld/LdRelToy7*.lean), but
for some cases, among them lists below the Johnson radius for every code with laws and a distance
(`ld_list_johnson`, Cb/Ld/LdRelJohnsonProofs.lean), and agreement of Reed-Solomon codes within half
the distance (Cb/Gl/GlAgreeHalf.lean).
Within a third of the distance, for codes that have their laws, they are theorems: lists have at
most one member (twice the radius is below the distance: Cb/Ld/LdRelJohnson.lean,
Cb/Obj/LdObjectConfMore.lean), and at most e + 1 coefficients are exceptional (`ld_mca_third`,
Cb/Ld/LdBaseCode.lean; for the fold of the index, v (e + 1) q^(v-1) points: `ldCm_mca_third`). Here
they are put in.
What is left to ask: laws of codes, distances, "three times the radius is below the distance",
transparency, what encodings hide, the conditions on samples, senders and zero-evaders, the model's
conditions, and inequalities between numbers. Beside these kinds, the two main statements ask that
each whole test on a group is a tail (`LdEnd.OK`: `TailTr`, Cb/Ld/LdTowerKit.lean: a premise, which
has, nested in `good : GoodT` (Ior/KnowCollGood.lean), among others the test's own `acc`, `know` and
`exact`), that the maps `K.pl`, `O.py` are injective, and that each group has `Fits`;
`Spec.ldT3_lin` asks the plan's clauses on restG, `p.SaysA` and `T.Q'` (`T.Q'.OK`: `LdTc.OK`,
Cb/Ld/LdLinCloseChain.lean: a premise, which has among others `GoodT` of each link of `T.Q'.c`:
`AllT`, Ior/KnowCollRulesChain.lean); the whole list is in the two statements and in whatever the
arguments hold as proofs.

Main names:
  `G.Third d`: a group within a third: each member's code, as read at the common positions, has its
    laws, distance d and is transparent; 3 · (the joint radius) < d; the joint radius implies each
    member's own.
  `S.Third dN` (the link), `Sn.Third dW dU dO` (the test): what the sendings ask, without the clause
    on lists (`list` of `S.OK`; `listW`, `listU`, `listO` of `Sn.OK`): instead distances, twice the
    radius below them, and the bound 1; but with the clause `ev` ("evades"; `evW`, `evU`, `evO` in
    the test).
  `Cf.Third`: the configuration within a third (its fields: see the record).
  `Spec.ldT3_link`: under the hypotheses of its statement, the link with its closing has
    `Hiop.LinkListR` ∧ `Hiop.LinkKnowR`. The folds' errors: ε = v (e + 1) q^(v-1) + v q^(v-1) at
    e = e₀, e₁.
  `Spec.ldT3_lin`: under the hypotheses of its statement, the test at one instance with the plan
    without a splitting has `Hiop.LinListR` ∧ `Hiop.LinKnowR`. The fold's error:
    v (e' + 1) q^(v-1) + v q^(v-1). What closes the rest of the plan (`T.Q'`) stays a parameter with
    its property.

Limits:
On the radii of the encoded index and of the groups this file says nothing beyond a third of the
distance (lists it has within half the distance: `Spec.ldT3_list`; and so the sendings' radii: asked
in `S.Third`, `Sn.Third`).
This file does not say that the conditions can be met together. No theorem of this library states
that the hypotheses of `ldT3_link` or `ldT3_lin` can be met together. A guard within a third, over
two fields, on part of `ldT3_lin`'s hypotheses (`Sn.Third` of a toy's sendings: `Gl.Off8.snd1`):
Cb/GlVal/GlToyLin.lean. (The toys Cb/Obj/LdObjectLinkToy.lean, Cb/Obj/LdObjectLinToy.lean stand at
other radii.)
This file does not say the lists of errors in the order of the rounds: Cb/Obj/LdObjectErr.lean.
Declared:
(1) The link's and the test's radii e₀, e₁, e' are at most eM, and 3 · eM < d (d: the code's
distance, `Cf.C₀.d`): so 2 · eM < d too; the third is what
the proved count of exceptional coefficients needs.
(2) The folds' errors are upper bounds, not this protocol's own numbers. The second summand, v
q^(v-1), pays for members of the list that violate the record.


(3) The link takes both indices by the first regime (no collision; radius at most eM).
For 2 eM below d the write-up takes the first index by the second regime (it
decodes: no point is bad, ε₀ = 0, and its radius may go up to d - eM - 1); that pairing is
Cb/Ld/LdLink.lean's ldLk_foldErr; the object's theorem on the link (Cb/Obj/LdObjectLinkFull.lean) is
stated for the pairing taken here.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Obj.LdObjectLinkFull
import Cb.Obj.LdObjectLinFullProofs
import Cb.Ld.LdLinCloseDemandProofs
import Cb.Obj.LdObjectConfMore
import Cb.Ld.LdBaseCode
import Cb.Ld.LdRelJohnson
import Cb.Ld.LdTowerMain
import Cb.Ld.LdTowerThird

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- A group within a third of the distance. -/
structure Grp.Third {E : Type} [Field E] {S : Sig E} (G : Grp S) (d : ℕ) : Prop where
  laws   : ∀ a : G.A, ((S.om a.1).C.atPos (G.pos a)).Laws
  dist   : ∀ a : G.A, ((S.om a.1).C.atPos (G.pos a)).Dist d
  transp : ∀ a : G.A, ((S.om a.1).C.atPos (G.pos a)).Transparent
  lt     : 3 * G.e < d
  fits   : G.Fits

/-- What the link's sending asks, without the clause on lists, but with the clause `ev`
("evades"). -/
structure LdLkP.Snd.Third {E ι κ J Λ : Type} [Field E] [Fintype E] [Fintype ι] [Fintype κ]
    [Fintype J] {P : LdLkP E ι κ J Λ} (S : P.Snd) (dN : P.N.O → ℕ) : Prop where
  laws : ∀ a, (P.N.om a).C.Laws
  dist : ∀ a, (P.N.om a).C.Dist (dN a)
  lt   : ∀ a, 2 * (P.N.om a).e < dN a
  one  : ∀ a, S.L a = 1
  fair : S.Sd.Fair
  ev   : ∀ a, (P.N.om a).Evades
  snd  : S.dS.Laws P.back
  bl   : S.dS.Blind S.Sd
  hid  : S.dS.Nn.Hides (P.N.budT S.t)

/-- What the test's three sendings ask, without the clauses on lists, but with the clauses `evW`,
`evU`, `evO` ("evades"). -/
structure LdLinP.Snd.Third {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Fintype κ]
    [Fintype J] [Fintype Y] {P : LdLinP E ι κ J Y} (S : P.Snd) (dW : P.NW.O → ℕ)
    (dU : P.NU.O → ℕ) (dO : P.NO.O → ℕ) : Prop where
  lawsW : ∀ a, (P.NW.om a).C.Laws
  distW : ∀ a, (P.NW.om a).C.Dist (dW a)
  ltW   : ∀ a, 2 * (P.NW.om a).e < dW a
  oneW  : ∀ a, S.LW a = 1
  fairW : P.SdW.Fair
  evW   : ∀ a, (P.NW.om a).Evades
  sndW  : S.dW.Laws P.backW
  blW   : S.dW.Blind P.SdW
  hidW  : S.dW.Nn.Hides (P.NW.budT S.tW)
  lawsU : ∀ a, (P.NU.om a).C.Laws
  distU : ∀ a, (P.NU.om a).C.Dist (dU a)
  ltU   : ∀ a, 2 * (P.NU.om a).e < dU a
  oneU  : ∀ a, S.LU a = 1
  fairU : P.SdU.Fair
  evU   : ∀ a, (P.NU.om a).Evades
  sndU  : S.dU.Laws P.backU
  blU   : S.dU.Blind P.SdU
  hidU  : S.dU.Nn.Hides (P.NU.budT S.tU)
  lawsO : ∀ a, (P.NO.om a).C.Laws
  distO : ∀ a, (P.NO.om a).C.Dist (dO a)
  ltO   : ∀ a, 2 * (P.NO.om a).e < dO a
  oneO  : ∀ a, S.LO a = 1
  fairO : P.SdO.Fair
  evO   : ∀ a, (P.NO.om a).Evades
  sndO  : S.dO.Laws P.backO
  blO   : S.dO.Blind P.SdO
  hidO  : S.dO.Nn.Hides (P.NO.budT S.tO)

/-- The configuration within a third of the distance. -/
structure LdCf.Third {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) :
    Prop where
  core   : Cf.C₀.Core
  dist   : HasDist Cf.C₀.G Cf.C₀.d
  lt     : 3 * Cf.eM < Cf.C₀.d
  evades : Cf.Z.OKOn (PadInF F)
  model  : Cf.ModelOK

/-- the error of a fold of the index at the radius e, within a third: exceptional coefficients, and
one member of the list -/
def LdCf.εThird {F E : Type} [Field F] [Field E] [Fintype E] [Algebra F E] (Cf : LdCf F E) (e : ℕ) :
    ℕ :=
  Cf.v * (e + 1) * Fintype.card E ^ (Cf.v - 1) + 1 * (Cf.X.v * Fintype.card E ^ (Cf.X.v - 1))

namespace Spec

/-- States, for `G.P` non-empty and under `G.Third d`: the base case alone is a whole test. -/
def ldT3_end : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (G : Grp S) [Nonempty G.P] (B : Type) [Fintype B]
      (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (d t : ℕ)
      (cov : (G.joint Sb sl Z).C.NP → (G.joint Sb sl Z).P),
    G.Third d → (ldBaseEnd (G.joint Sb sl Z) t cov d (G.e + 1) 1).OK t

/-- States, under the hypotheses below: a test on a group within a third meets its conditions
(`LdRunD.OK`). -/
def ldT3_run : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (d : ℕ),
    D.G.Third d → D.L = 1 → D.Z.OK → D.T.OK D.t → D.OK

def ldT3_list : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (o : OMsg E) (d : ℕ),
    o.C.Laws → o.C.Dist d → 2 * o.e < d → o.ListLE 1

def ldT3_sndK : Prop :=
  ∀ (E ι κ J Λ : Type) [Field E] [Fintype E] [Fintype ι] [Fintype κ] [Fintype J]
      (P : LdLkP E ι κ J Λ) (S : P.Snd) (dN : P.N.O → ℕ),
    S.Third dN → S.OK

def ldT3_sndL : Prop :=
  ∀ (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype Y]
      (P : LdLinP E ι κ J Y) (S : P.Snd) (dW : P.NW.O → ℕ) (dU : P.NU.O → ℕ) (dO : P.NO.O → ℕ),
    S.Third dW dU dO → S.OK

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldT3_conf : Prop := ∀ (Cf : LdCf F E), Cf.Third → Cf.OK 1

/-- The link with its closing, within a third. -/
def ldT3_link : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (K : Cf.LinkPar) (S : K.P.Snd) (dN : K.P.N.O → ℕ)
      (Kc : K.P.Cl) (dG : ℕ) (d₂ : K.P.W2) (d : K.P.W0),
    Cf.Third → K.e₀ ≤ Cf.eM → K.e₁ ≤ Cf.eM → Function.Injective K.pl → S.Third dN → Kc.G.Third dG →
    Kc.L = 1 → Kc.Z.OK → Kc.T.OK Kc.t → (∀ a, Kc.t ≤ S.t a) →
    LinkListR (C := Cf.conf) (K.link (K.full S (Cf.εThird K.e₀) (Cf.εThird K.e₁) Kc d₂ d))
      (K.hLink (K.full S (Cf.εThird K.e₀) (Cf.εThird K.e₁) Kc d₂ d))
      (K.nums (K.full S (Cf.εThird K.e₀) (Cf.εThird K.e₁) Kc d₂ d)) ∧
    LinkKnowR (C := Cf.conf) (K.link (K.full S (Cf.εThird K.e₀) (Cf.εThird K.e₁) Kc d₂ d))
      (K.nums (K.full S (Cf.εThird K.e₀) (Cf.εThird K.e₁) Kc d₂ d)).err

/-- The test at one instance, with the plan without a splitting, within a third. -/
def ldT3_lin : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (p : LdLinPl O.toC) (T : LdLinPlT p)
      (Sn : O.toC.P.Snd) (dW : O.toC.P.NW.O → ℕ) (dU : O.toC.P.NU.O → ℕ) (dO : O.toC.P.NO.O → ℕ)
      (dG₁ dG₂ : ℕ) (q₀ : Finset O.toC.E₀.Pos → Prop) (ba : O.toC.Sa.O → ℕ) (b' : p.S₂.O → ℕ)
      (d : O.toC.P.W0) (d0 : O.left.AMsg),
    HasDist O.Cf.C₀.G O.Cf.C₀.d → 3 * O.Cf.eM < O.Cf.C₀.d → O.e' ≤ O.Cf.eM →
    Function.Injective O.py → Sn.Third dW dU dO →
    (∀ sa m, p.restG.val sa (p.G₂.msg (O.toC.S.res (T := OMsg.Msg) p.kp₁ m)) =
      O.toC.rest sa (O.toC.aM m)) →
    p.SaysA T.Q'.base T.fa → p.G₁.Third dG₁ → T.L₁ = 1 → T.Z₁.OK → T.T₁.OK T.t₁ → p.G₂.Third dG₂ →
    T.L₂ = 1 → T.Z₂.OK → T.T₂.OK T.t₂ → T.Q'.OK → (∀ V, T.Q'.q V → p.S₂.qFam q₀ b' V) →
    (∀ a, T.D₁.need (T.D₂.need b') (.inl (.inl (.inl a))) ≤ ba a) →
    (∀ a, T.D₁.need (T.D₂.need b') (.inl (.inl (.inr a))) ≤ Sn.tW a) →
    (∀ a, T.D₁.need (T.D₂.need b') (.inl (.inr a)) ≤ Sn.tU a) →
    (∀ a, T.D₁.need (T.D₂.need b') (.inr a) ≤ Sn.tO a) →
    LinListR O.left (O.full Sn (O.Cf.εThird O.e') T.Q T.fq d)
      (O.hFull Sn (O.Cf.εThird O.e') T.Q T.fq d) (O.numsF Sn (O.Cf.εThird O.e') T.Q T.fq d) ∧
    LinKnowR O.left (O.full Sn (O.Cf.εThird O.e') T.Q T.fq d) d0
      (O.numsF Sn (O.Cf.εThird O.e') T.Q T.fq d).err

end
end Spec
end Cb
