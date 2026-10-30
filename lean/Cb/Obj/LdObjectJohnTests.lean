-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectJohnTests.lean: hypotheses of a holographic IOP's sub-protocols below the Johnson
radius: the sendings, the link with its closing, the test for linear constraints at one instance and
weights-formedness with no hypothesis on a list, but in the clauses "evades" (`ev`, `evW`, `evU`,
`evO`) and in the clause `list` of `LdRunD.OK` (inside `Kc.OK`, `T.D₁.OK`, `T.D₂.OK`): lists by the
proved Johnson bound.

Its main statements give the requirements of Hiop/RecSubs.lean on the link and on the test at one
instance (`LinkListR`, `LinkKnowR`, `LinListR`, `LinKnowR`), under the hypotheses told in their rows
below.
Definitions and statements (each a `Prop` in `Cb.Spec`, named `ldJn_..` or `ldJe_..`); the proofs
are in Cb/Obj/LdObjectJohnTestsProofs.lean. Generic: any finite fields, any codes; no theorem of the
literature is assumed here, and none is named but the Johnson bound, which is proved
(Cb/Ld/LdRelJohnson.lean: `ld_list_johnson`).
A bound on lists says that every word has at most L codewords within the radius e (`ListAt`,
Cb/Ld/LdRel.lean; for the messages of an oracle message: `OMsg.ListLE`, Cb/Ld/LdSig.lean).
Cb/Obj/LdObjectThirdTests.lean, Cb/Obj/LdObjectThirdNil.lean, Cb/Ld/LdWfEndThird.lean do this within
a third of the distances, where lists have one member and agreement is e + 1. Beyond a third two
kinds of hypotheses come back.
  Lists need none: every code read under a transformation with the laws and a distance d as read
    has, at a radius e with n (n - d) < (n - e)^2 (`InJohnson n d e`), lists of at most
    `listMax n d e` members (Cb/Ld/LdRelJohnson.lean: `ld_list_johnson`, proved). Here that bound is
    put in for each clause on a list in the records below (but `Cf.Half`: within unique
    decoding) and in `Spec.ldJn_run`. In `Spec.ldJn_link` and `Spec.ldJn_lin` the clause `list` of
    `LdRunD.OK` (Cb/Ld/LdLinCloseRuns.lean) stays asked.
  Agreement stays a hypothesis, in two places, each with letters: the bounds on the points that are
    bad for a fold of the index (`FoldErr .. ε`: Cb/Ld/LdLink.lean, Cb/Ld/LdLin.lean); what each
    whole test on a group asks (`D.OK`: no clause of it names agreement or a tower (agreement comes
    in where `D.OK` is derived, below): its clause `tail : D.T.OK D.t` asks of the whole test `D.T`,
    a free value, the record `TailTr` (Cb/Ld/LdTowerKit.lean), whose `good : GoodT`
    (Ior/KnowCollGood.lean) has, among its clauses, `acc` (pointwise completeness), `know`
    (round-by-round knowledge soundness, at the errors `D.T.N.err`) and `exact` (`Honest.Exact`,
    Ior/Honest.lean, at the budget `D.T.N.bud`)). Other files derive both (`D.OK`:
    Cb/Obj/LdObjectTowerJohn.lean: `ldTowGJ_run`, from `D.PreJ T d`, whose `tow` asks, among others,
    `MCArows`, `MCAat`; `FoldErr`: Cb/Obj/LdObjectDataThird.lean: `LdObjD.Own3.own`, from `Own3` and
    `Cf.Third`).

Main names, the records:
  `G.John d`: a group: its members as read at the group's positions: laws, distance d, transparent;
    `InJohnson |G.P| d G.e`; the joint radius implies each member's own.
  `S.John dN`: what the link's sending asks without the clause on lists: laws, a distance dN a as
    read, `InJohnson` at the member's own positions and radius, the bound is L a = `listMax ..`;
    fair seeds, evading samples, the sender's three (`snd`, `bl`, `hid`).
  `Sn.John dW dU dO`: the same for the test's three sendings.
  `Cf.Half`: the configuration within unique decoding: code, distance, 2 eM below it, sample map,
    model. (`Cf.Third` asks 3 eM.)
  `Z.John p dS`: weights-formedness: all clauses that do not speak of lists (`Z.Rest p`); `Cf.Half`;
    (its other fields: see the record).
  "Evading samples" when lists have more than one member: with lists of one member the clause is
    empty (there are no two members). Here it is a real condition: two different messages of one
    list have the same answers at no more than `o.Z.err` seeds (`o` the oracle message, `o.Z` its
    sample map). It follows from the sample map's own condition "a vector other than 0 has the value
    0 at no more than Z.err seeds" (Cb/Ld/LdSig.lean: `sig_evades_of_ok`; on a subspace:
    `sig_evades_of_okOn`). It speaks of no bound on a list.
Main names, the statements:
  `Spec.ldJn_link`: the link with its closing, at any pair of conditions that the object's condition
    gives (Cb/Obj/LdObjectLinkPair.lean: `FitsK`): `Cf.Half`; `K.FitsK on0 on1`;
    `FoldErr on0 on1 ε₀ ε₁`; distinct places; `S.John dN`; the closing's test meets its conditions
    (`Kc.OK`: among its clauses `list`, and `tail`: `TailTr` of the whole test `Kc.T`, so `GoodT`
    with `acc`, `know` and `exact`); what it needs is at most what the encodings bear
    (`∀ a, Kc.t ≤ S.t a`) ⇒ `Hiop.LinkListR` ∧ `Hiop.LinkKnowR`.
  `Spec.ldJn_lin`: the test at one instance with the plan without a splitting: distance, 2 eM below
    it; `FoldErr on0 εf`; distinct places; `Sn.John`; the plan's two facts; its tests meet their
    conditions (`T.D₁.OK`, `T.D₂.OK`: in each, among its clauses, `list`, and `tail`: `TailTr` of
    its whole test; `T.Q'.OK`: every link of the free chain `T.Q'.c` is `GoodT`, and `SidesCT`
    (Cb/Ld/LdTowerKitChain.lean)); `∀ V, T.Q'.q V → p.S₂.qFam q₀ b' V`; the four families of
    inequalities ⇒ `Hiop.LinListR` ∧ `Hiop.LinKnowR`.
  `Spec.ldJn_link`, `Spec.ldJn_lin`, `Spec.ldJe_link` and `Spec.ldJe_lin` also take, as an instance,
    that the index code has a position (`Nonempty (Fin Cf.C₀.n)`).
  `Spec.ldJn_wf`: `Z.John p dS` ⇒ `Z.OK p 1` (Cb/Ld/LdWfEnd.lean): so, for p the characteristic of
    E, the object's two items on weights-formedness.
  The errors, in the order of the rounds, for any bounds on lists: `Spec.ldJe_send`,
    `Spec.ldJe_link`, `Spec.ldJe_lin`. (What errGam, errLoc, errPhi, errPt, errZeta say:
    Cb/Obj/LdObjectThirdErr.lean: `ldT3e_names`.)

Limits: on bounds on agreement: `FoldErr .. ε` is a premise of `Spec.ldJn_link` and `Spec.ldJn_lin`;
no statement of this file concludes one. This file does not say that the records can be met beyond a
third: the guards: over p = 2^64 - 2^32 + 1, at the radius 3 of the distance 6:
Cb/GlVal/GlToyWfJ.lean (`Z.John`), Cb/GlVal/GlToyLinJ.lean (`Sn.John`; `G.John`). It says nothing on
the batch, and nothing on plans with a splitting.
Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectThirdNil
import Cb.Ld.LdWfEnd
import Cb.Ld.LdRelJohnson
import Cb.Ld.LdTowerJohn

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- A group below the Johnson radius. -/
structure Grp.John {E : Type} [Field E] {S : Sig E} (G : Grp S) (d : ℕ) : Prop where
  laws   : ∀ a : G.A, ((S.om a.1).C.atPos (G.pos a)).Laws
  dist   : ∀ a : G.A, ((S.om a.1).C.atPos (G.pos a)).Dist d
  transp : ∀ a : G.A, ((S.om a.1).C.atPos (G.pos a)).Transparent
  inJ    : InJohnson (Fintype.card G.P) d G.e
  fits   : G.Fits

/-- What the link's sending asks, without the clause on lists. -/
structure LdLkP.Snd.John {E ι κ J Λ : Type} [Field E] [Fintype E] [Fintype ι] [Fintype κ]
    [Fintype J] {P : LdLkP E ι κ J Λ} (S : P.Snd) (dN : P.N.O → ℕ) : Prop where
  laws : ∀ a, (P.N.om a).C.Laws
  dist : ∀ a, (P.N.om a).C.Dist (dN a)
  inJ  : ∀ a, InJohnson (Fintype.card (P.N.om a).P) (dN a) (P.N.om a).e
  isL  : ∀ a, S.L a = listMax (Fintype.card (P.N.om a).P) (dN a) (P.N.om a).e
  fair : S.Sd.Fair
  ev   : ∀ a, (P.N.om a).Evades
  snd  : S.dS.Laws P.back
  bl   : S.dS.Blind S.Sd
  hid  : S.dS.Nn.Hides (P.N.budT S.t)

/-- What the test's three sendings ask, without the clauses on lists. -/
structure LdLinP.Snd.John {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Fintype κ]
    [Fintype J] [Fintype Y] {P : LdLinP E ι κ J Y} (S : P.Snd) (dW : P.NW.O → ℕ)
    (dU : P.NU.O → ℕ) (dO : P.NO.O → ℕ) : Prop where
  lawsW : ∀ a, (P.NW.om a).C.Laws
  distW : ∀ a, (P.NW.om a).C.Dist (dW a)
  inJW  : ∀ a, InJohnson (Fintype.card (P.NW.om a).P) (dW a) (P.NW.om a).e
  isLW  : ∀ a, S.LW a = listMax (Fintype.card (P.NW.om a).P) (dW a) (P.NW.om a).e
  fairW : P.SdW.Fair
  evW   : ∀ a, (P.NW.om a).Evades
  sndW  : S.dW.Laws P.backW
  blW   : S.dW.Blind P.SdW
  hidW  : S.dW.Nn.Hides (P.NW.budT S.tW)
  lawsU : ∀ a, (P.NU.om a).C.Laws
  distU : ∀ a, (P.NU.om a).C.Dist (dU a)
  inJU  : ∀ a, InJohnson (Fintype.card (P.NU.om a).P) (dU a) (P.NU.om a).e
  isLU  : ∀ a, S.LU a = listMax (Fintype.card (P.NU.om a).P) (dU a) (P.NU.om a).e
  fairU : P.SdU.Fair
  evU   : ∀ a, (P.NU.om a).Evades
  sndU  : S.dU.Laws P.backU
  blU   : S.dU.Blind P.SdU
  hidU  : S.dU.Nn.Hides (P.NU.budT S.tU)
  lawsO : ∀ a, (P.NO.om a).C.Laws
  distO : ∀ a, (P.NO.om a).C.Dist (dO a)
  inJO  : ∀ a, InJohnson (Fintype.card (P.NO.om a).P) (dO a) (P.NO.om a).e
  isLO  : ∀ a, S.LO a = listMax (Fintype.card (P.NO.om a).P) (dO a) (P.NO.om a).e
  fairO : P.SdO.Fair
  evO   : ∀ a, (P.NO.om a).Evades
  sndO  : S.dO.Laws P.backO
  blO   : S.dO.Blind P.SdO
  hidO  : S.dO.Nn.Hides (P.NO.budT S.tO)

/-- The configuration within unique decoding. -/
structure LdCf.Half {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) :
    Prop where
  core   : Cf.C₀.Core
  dist   : HasDist Cf.C₀.G Cf.C₀.d
  lt     : 2 * Cf.eM < Cf.C₀.d
  evades : Cf.Z.OKOn (PadInF F)
  model  : Cf.ModelOK

/-- Weights-formedness below the Johnson radius. -/
structure LdWfE.John {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (Z : LdWfE F E) (p : ℕ) (dS : Z.W.P.S.O → ℕ) : Prop extends Z.Rest p where
  confH : Z.W.Cf.Half
  dist  : ∀ a, (Z.W.P.S.om a).C.Dist (dS a)
  inJ   : ∀ a, InJohnson (Fintype.card (Z.W.P.S.om a).P) (dS a) (Z.W.P.S.om a).e
  isL   : ∀ a, Z.L a = listMax (Fintype.card (Z.W.P.S.om a).P) (dS a) (Z.W.P.S.om a).e
  ev    : ∀ a, (Z.W.P.S.om a).Evades

namespace Spec

def ldJn_list : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (o : OMsg E) (d : ℕ), o.C.Laws → o.C.Dist d →
    InJohnson (Fintype.card o.P) d o.e → o.ListLE (listMax (Fintype.card o.P) d o.e)

def ldJn_run : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (d : ℕ),
    D.G.John d → D.L = listMax (Fintype.card D.G.P) d D.G.e → D.Z.OK → D.T.OK D.t → D.OK

def ldJn_sndK : Prop :=
  ∀ (E ι κ J Λ : Type) [Field E] [Fintype E] [Fintype ι] [Fintype κ] [Fintype J]
      (P : LdLkP E ι κ J Λ) (S : P.Snd) (dN : P.N.O → ℕ),
    S.John dN → S.OK

def ldJn_sndL : Prop :=
  ∀ (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype Y]
      (P : LdLinP E ι κ J Y) (S : P.Snd) (dW : P.NW.O → ℕ) (dU : P.NU.O → ℕ) (dO : P.NO.O → ℕ),
    S.John dW dU dO → S.OK

/-- a sending's seed round -/
def ldJe_send : Prop :=
  ∀ (E : Type) [Field E] (N : Sig E) (Sd : N.Seeds) (L : N.O → ℕ),
    ldSendFamErr N Sd L = ∑ a, Sd.mult a * ((L a).choose 2 * (N.om a).Z.err)

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldJn_conf : Prop := ∀ Cf : LdCf F E, Cf.Half → Cf.OK 1

/-- The link with its closing. -/
def ldJn_link : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (K : Cf.LinkPar)
      (on0 on1 : (K.P.D.X.Row → Fin Cf.C₀.n → E) → K.P.D.X.Rec → Prop) (S : K.P.Snd)
      (dN : K.P.N.O → ℕ) (ε₀ ε₁ : ℕ) (Kc : K.P.Cl) (d₂ : K.P.W2) (d : K.P.W0),
    Cf.Half → K.FitsK on0 on1 → K.P.FoldErr on0 on1 ε₀ ε₁ → Function.Injective K.pl → S.John dN →
    Kc.OK → (∀ a, Kc.t ≤ S.t a) →
    LinkListR (C := Cf.conf) (K.link (K.fullAt on0 on1 S ε₀ ε₁ Kc d₂ d))
      (K.hLink (K.fullAt on0 on1 S ε₀ ε₁ Kc d₂ d)) (K.nums (K.fullAt on0 on1 S ε₀ ε₁ Kc d₂ d)) ∧
    LinkKnowR (C := Cf.conf) (K.link (K.fullAt on0 on1 S ε₀ ε₁ Kc d₂ d))
      (K.nums (K.fullAt on0 on1 S ε₀ ε₁ Kc d₂ d)).err

/-- The test at one instance. -/
def ldJn_lin : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (p : LdLinPl O.toC) (T : LdLinPlT p)
      (Sn : O.toC.P.Snd) (dW : O.toC.P.NW.O → ℕ) (dU : O.toC.P.NU.O → ℕ) (dO : O.toC.P.NO.O → ℕ)
      (εf : ℕ) (q₀ : Finset O.toC.E₀.Pos → Prop) (ba : O.toC.Sa.O → ℕ) (b' : p.S₂.O → ℕ)
      (d : O.toC.P.W0) (d0 : O.left.AMsg),
    HasDist O.Cf.C₀.G O.Cf.C₀.d → 2 * O.Cf.eM < O.Cf.C₀.d → O.toC.P.FoldErr O.on0 εf →
    Function.Injective O.py → Sn.John dW dU dO →
    (∀ sa m, p.restG.val sa (p.G₂.msg (O.toC.S.res (T := OMsg.Msg) p.kp₁ m)) =
      O.toC.rest sa (O.toC.aM m)) →
    p.SaysA T.Q'.base T.fa → T.D₁.OK → T.D₂.OK → T.Q'.OK → (∀ V, T.Q'.q V → p.S₂.qFam q₀ b' V) →
    (∀ a, T.D₁.need (T.D₂.need b') (.inl (.inl (.inl a))) ≤ ba a) →
    (∀ a, T.D₁.need (T.D₂.need b') (.inl (.inl (.inr a))) ≤ Sn.tW a) →
    (∀ a, T.D₁.need (T.D₂.need b') (.inl (.inr a)) ≤ Sn.tU a) →
    (∀ a, T.D₁.need (T.D₂.need b') (.inr a) ≤ Sn.tO a) →
    LinListR O.left (O.full Sn εf T.Q T.fq d)
      (O.hFull Sn εf T.Q T.fq d) (O.numsF Sn εf T.Q T.fq d) ∧
    LinKnowR O.left (O.full Sn εf T.Q T.fq d) d0 (O.numsF Sn εf T.Q T.fq d).err

/-- Weights-formedness. -/
def ldJn_wf : Prop := ∀ (Z : LdWfE F E) (p : ℕ) (dS : Z.W.P.S.O → ℕ), Z.John p dS → Z.OK p 1

/-- the link's errors, in the order of the rounds -/
def ldJe_link : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (K : Cf.LinkPar)
      (on0 on1 : (K.P.D.X.Row → Fin Cf.C₀.n → E) → K.P.D.X.Rec → Prop) (S : K.P.Snd) (ε₀ ε₁ : ℕ)
      (Kc : K.P.Cl) (d₂ : K.P.W2) (d : K.P.W0),
    (K.nums (K.fullAt on0 on1 S ε₀ ε₁ Kc d₂ d)).err.toList =
      [K.P.errGam ε₀ ε₁, ldSendFamErr K.P.N S.Sd S.L, 0, K.P.errLoc, K.P.errPhi, Kc.L * Kc.Z.err] ++
        Kc.T.N.err.toList

/-- the test's errors, in the order of the rounds -/
def ldJe_lin : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (p : LdLinPl O.toC) (T : LdLinPlT p)
      (Sn : O.toC.P.Snd) (εf : ℕ) (d : O.toC.P.W0),
    (O.numsF Sn εf T.Q T.fq d).err.toList =
      [ldSendFamErr O.toC.P.NW O.toC.P.SdW Sn.LW, 0, O.toC.P.errPt εf,
          ldSendFamErr O.toC.P.NU O.toC.P.SdU Sn.LU, 0, O.toC.P.errLoc,
          ldSendFamErr O.toC.P.NO O.toC.P.SdO Sn.LO, 0, O.toC.P.errZeta] ++
        ((T.L₁ * T.Z₁.err) :: T.T₁.N.err.toList ++
          ((T.L₂ * T.Z₂.err) :: T.T₂.N.err.toList ++ T.Q'.c.errs))

end
end Spec
end Cb
