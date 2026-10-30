-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaWorkObj.lean: "every round's error, counting its proof-of-work bits, is at most κ":
the tests for linear constraints, the link, the whole tests as towers: w bits at each round that
draws locations, none elsewhere.

Definitions (records on numbers; lists of bits) and theorems: glue on Cb/Ld/LdKappaBits.lean,
Cb/Ld/LdKappaWork.lean; nothing is evaluated. "At most κ with the bits B" is `Err.BelowB`
(Cb/Ld/LdKappaBits.lean): B has one entry for each round, and in each round e ≤ κ · (2^b · v), with
e the error (a count: `Err`, Iop/Rbr.lean), b the round's entry of B, v the number of all values of
the round's verifier message. These errors are numbers that a link or a block lists (the data fields
`Nums.err`, `Link.P.err`, `LinkA.err`, and `N.err` of `ldSwBlock`, `ldBaseEnd`, `T.toEnd`, `D.T`):
that a link or a block is sound at the numbers that it lists is no statement of this file; for the
test at N instances with a closing that tie is `Spec.ldLinCB_know` (Cb/Ld/LdLinChainB.lean), under
its hypotheses (that condition itself asks soundness of some of the parts one level down: for these
the tie carries soundness, it does not found it): `KnowB` for the vectors that share the encoded
index and its record
(`SameKey P.k0`), on the statements with the condition `(P.j0 on0).on`.

The rounds that draw locations: the cores' round "locations" (one in each of the two tests for
linear constraints and in the link); the second round of each code switch; the second round of each
base case. In these, and only in these, the clause reads err ≤ κ · (2^w · number of values).

Main names:
  `LdLinP.KapCW`, `LdLinP.KapCBW`, `LdLkP.KapCW`: the records of Cb/Ld/LdKappaKit.lean,
    Cb/Ld/LdKappaBat.lean, with w at "loc".
  `LdSw.KapW` (code switch), `LdJoint.KapBW` (base case): bits 0 w.
  `LdTowC.KapW`, `LdTowG.KapW`, `LdTowC.bits`, `LdTowG.bits` (towers): by recursion.
  `D.BelowBT L κ` (one whole test): its `IOR.Link` (`D.link`) has the bits 0 :: L (`ldKappaW_run`).
  `ldKappaW_lin`, `ldKappaW_linA`, `ldKappaW_link`, `ldKappaW_sw`, `ldKappaW_base`,
    `ldKappaW_towC`, `ldKappaW_towG`: each of these records → the errors of its chain or block are
    at most κ with its bits.
  `ldKappaW_linC`, `ldKappaW_linCA`, `ldKappaW_linkC`: the core's record, and a closing at most κ
    with its bits → the test (the link) with that closing, as one step of a chain (`IOR.Link`; for
    `ldKappaW_linCA` a `LinkA`), is at most κ with the core's bits, then the closing's. For
    `ldKappaW_linkC` the closing is `K.cZ d₂` of a `K : P.Cl`, the premise is `K.run.BelowBT L κ`,
    and the closing's bits are 0 :: L.
  `ldKappaW_pre`: a test D whose whole test is the tower T (`e`), the bridge's number (`hb`),
    `T.KapW w κ` → `D.BelowBT (T.bits w) κ`.
  The statements with `P : LdLinP` or `P : LdLkP` take the type ι of positions nonempty; the types
    of positions P, P' of a code switch and `G.P` of a group are taken nonempty too.

Limits: this file says nothing on the way back. This file says nothing on the value of any number.
It does not say that a protocol should put work at these rounds and no others: that is the technical
report's choice at its reference parameters (by a reading of a print of the technical report;
not held against the report's latest edition).

Terms: lean/GLOSSARY.md.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
import Cb.Ld.LdKappaWork
import Cb.Ld.LdKappaTow
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain IOR.ChainA
open scoped ENNReal

theorem belowB_send {E : Type} [Field E] (N : Sig E) (Sd : N.Seeds) (X : Type) (E₀ : ExtSpec)
    (Kc : Type) (L t : N.O → ℕ) (κ : ℝ≥0∞)
    (h : (ldSendFamErr N Sd L : ℝ≥0∞) ≤ κ * (Fintype.card Sd.D : ℝ≥0∞)) :
    Err.BelowB (ldSendFamNums N Sd X E₀ Kc L t).err [0, 0] κ :=
  belowB_none _ κ (kap_send N Sd X E₀ Kc L t κ h)

theorem belowB_peek {K Xi Xo : Type} {Ei Eo : ExtSpec} (V : PeekV Xi Ei Xo Eo) (err w : ℕ)
    (κ : ℝ≥0∞) (h : (err : ℝ≥0∞) ≤ κ * ((2 : ℝ≥0∞) ^ w * (Fintype.card V.D : ℝ≥0∞))) :
    Err.BelowB (Nums.peek K V err).err [w] κ := ⟨h, rfl⟩

theorem belowB_peek0 {K Xi Xo : Type} {Ei Eo : ExtSpec} (V : PeekV Xi Ei Xo Eo) (err : ℕ) (κ : ℝ≥0∞)
    (h : (err : ℝ≥0∞) ≤ κ * (Fintype.card V.D : ℝ≥0∞)) :
    Err.BelowB (Nums.peek K V err).err [0] κ :=
  ⟨by simpa using h, rfl⟩

/-- the bits of the core of a test for linear constraints; of the link's core; in the order of the
rounds, a sending having two: sW, sW, pt, sU, sU, loc, sO, sO, zeta; gam, snd, snd, loc, phi -/
def linBits (w : ℕ) : List ℕ := [0, 0, 0, 0, 0, w, 0, 0, 0]
def lkBits (w : ℕ) : List ℕ := [0, 0, 0, w, 0]

section
variable {E ι κ' J Y : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ'] [Fintype J] [Fintype Y]

structure LdLinP.KapCW (P : LdLinP E ι κ' J Y) (S : P.Snd) (εf w : ℕ) (κ : ℝ≥0∞) : Prop where
  sW   : (ldSendFamErr P.NW P.SdW S.LW : ℝ≥0∞) ≤ κ * (Fintype.card P.SdW.D : ℝ≥0∞)
  pt   : (P.errPt εf : ℝ≥0∞) ≤ κ * (Fintype.card P.vPt.D : ℝ≥0∞)
  sU   : (ldSendFamErr P.NU P.SdU S.LU : ℝ≥0∞) ≤ κ * (Fintype.card P.SdU.D : ℝ≥0∞)
  loc  : (P.errLoc : ℝ≥0∞) ≤ κ * ((2 : ℝ≥0∞) ^ w * (Fintype.card P.vLoc.D : ℝ≥0∞))
  sO   : (ldSendFamErr P.NO P.SdO S.LO : ℝ≥0∞) ≤ κ * (Fintype.card P.SdO.D : ℝ≥0∞)
  zeta : (P.errZeta : ℝ≥0∞) ≤ κ * (Fintype.card P.vZeta.D : ℝ≥0∞)

structure LdLinP.KapCBW (P : LdLinP E ι κ' J Y) (S : P.Snd) (εf N w : ℕ) (κ : ℝ≥0∞) : Prop where
  sW   : (ldSendFamErr P.NW P.SdW S.LW : ℝ≥0∞) ≤ κ * (Fintype.card P.SdW.D : ℝ≥0∞)
  pt   : (P.errPtB εf N : ℝ≥0∞) ≤ κ * (Fintype.card P.vPt.D : ℝ≥0∞)
  sU   : (ldSendFamErr P.NU P.SdU S.LU : ℝ≥0∞) ≤ κ * (Fintype.card P.SdU.D : ℝ≥0∞)
  loc  : (P.errLoc : ℝ≥0∞) ≤ κ * ((2 : ℝ≥0∞) ^ w * (Fintype.card P.vLoc.D : ℝ≥0∞))
  sO   : (ldSendFamErr P.NO P.SdO S.LO : ℝ≥0∞) ≤ κ * (Fintype.card P.SdO.D : ℝ≥0∞)
  zeta : (P.errZeta : ℝ≥0∞) ≤ κ * (Fintype.card P.vZeta.D : ℝ≥0∞)

theorem ldKappaW_lin (P : LdLinP E ι κ' J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (S : P.Snd) (εf w : ℕ) (κ : ℝ≥0∞) (h : P.KapCW S εf w κ) :
    (P.chain on0 S εf).BelowB (linBits w) κ :=
  Chain.belowB_mk _ _ [0, 0, 0, 0, 0, w, 0, 0] [0] κ
    (Chain.belowB_mk _ _ [0, 0, 0, 0, 0, w] [0, 0] κ
      (Chain.belowB_mk _ _ [0, 0, 0, 0, 0] [w] κ
        (Chain.belowB_mk _ _ [0, 0, 0] [0, 0] κ
          (Chain.belowB_mk _ _ [0, 0] [0] κ
            (Chain.belowB_mk _ _ [] [0, 0] κ ((Chain.belowB_one _ _ κ).2 rfl)
              (belowB_send _ _ _ _ _ _ _ κ h.sW))
            (belowB_peek0 _ _ κ h.pt))
          (belowB_send _ _ _ _ _ _ _ κ h.sU))
        (belowB_peek _ _ w κ h.loc))
      (belowB_send _ _ _ _ _ _ _ κ h.sO))
    (belowB_peek0 _ _ κ h.zeta)

theorem ldKappaW_linA (P : LdLinP E ι κ' J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (S : P.Snd) (εf N w : ℕ) (κ : ℝ≥0∞) (h : P.KapCBW S εf N w κ) :
    (P.chainA on0 S εf N).BelowB (linBits w) κ :=
  ChainA.belowB_mk _ _ [0, 0, 0, 0, 0, w, 0, 0] [0] κ
    (ChainA.belowB_mk _ _ [0, 0, 0, 0, 0, w] [0, 0] κ
      (ChainA.belowB_mk _ _ [0, 0, 0, 0, 0] [w] κ
        (ChainA.belowB_mk _ _ [0, 0, 0] [0, 0] κ
          (ChainA.belowB_mk _ _ [0, 0] [0] κ
            (ChainA.belowB_mk _ _ [] [0, 0] κ ((ChainA.belowB_one _ _ κ).2 rfl)
              (belowB_send P.NW P.SdW P.X0 P.E0 Unit S.LW S.tW κ h.sW))
            ⟨by simpa using h.pt, rfl⟩)
          (belowB_send P.NU P.SdU P.X2 P.E1 Unit S.LU S.tU κ h.sU)) ⟨h.loc, rfl⟩)
      (belowB_send P.NO P.SdO P.X4 P.E4 Unit S.LO S.tO κ h.sO))
    ⟨by simpa using h.zeta, rfl⟩

theorem ldKappaW_linC (P : LdLinP E ι κ' J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (S : P.Snd) (εf w : ℕ) (cZ : Chain Unit P.J6 LdLinP.JT) (d : P.W0) (κ : ℝ≥0∞) (LZ : List ℕ)
    (h : P.KapCW S εf w κ) (hZ : cZ.BelowB LZ κ) :
    Err.BelowB (P.linC on0 S εf cZ d).P.err (linBits w ++ LZ) κ := by
  unfold LdLinP.linC
  exact (chain_belowB _ _ κ _).2 (Chain.belowB_app _ _ _ _ κ (ldKappaW_lin P on0 S εf w κ h) hZ)

theorem ldKappaW_linCA (P : LdLinP E ι κ' J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (S : P.Snd) (εf N w : ℕ) (cZ : ChainA Unit P.J6 LdLinP.JT) (d : P.W0) (κ : ℝ≥0∞) (LZ : List ℕ)
    (h : P.KapCBW S εf N w κ) (hZ : cZ.BelowB LZ κ) :
    Err.BelowB (P.linCA on0 S εf N cZ d).err (linBits w ++ LZ) κ := by
  unfold LdLinP.linCA
  exact (chainA_belowB _ _ κ _).2
    (ChainA.belowB_app _ _ _ _ κ (ldKappaW_linA P on0 S εf N w κ h) hZ)

omit [Fintype E] [Nonempty ι] in
theorem ldKappaW_linZ (C : LdLinC E ι κ' J Y) (Q : LdTc C.S C.E₀ C.Wpa) (fq : C.St6 → Q.St)
    (κ : ℝ≥0∞) (L : List ℕ) (h : Q.c.BelowB L κ) : (C.cZ Q fq).BelowB L κ :=
  Chain.belowB_app _ _ [] L κ ((Chain.belowB_one _ _ κ).2 rfl) h

omit [Fintype E] [Nonempty ι] in
theorem ldKappaW_linZA (C : LdLinC E ι κ' J Y) (QA : LdTcA C.S C.E₀ C.Wpa) (fq : C.St6 → QA.Q.St)
    (κ : ℝ≥0∞) (L : List ℕ) (h : QA.cA.BelowB L κ) : (C.cZA QA fq).BelowB L κ :=
  ChainA.belowB_app _ _ [] L κ ((ChainA.belowB_one _ _ κ).2 rfl) h

end

section
variable {E : Type} [Field E] [Fintype E] {S : Sig E}

/-- One whole test: the bridge's number (no work), and the whole test's errors (`D.T.N.err`) are at
most κ with the bits L. -/
structure LdRunD.BelowBT (D : LdRunD S) (L : List ℕ) (κ : ℝ≥0∞) : Prop where
  bridge : ((D.L * D.Z.err : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card D.Z.D : ℝ≥0∞)
  test   : Err.BelowB D.T.N.err L κ

theorem ldKappaW_run (D : LdRunD S) {St₀ Wp : Type} {E₀ : ExtSpec}
    (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp)
    (κ : ℝ≥0∞) (L : List ℕ) (h : D.BelowBT L κ) :
    Err.BelowB (D.link A₀ d d').P.err (0 :: L) κ :=
  (belowB_app (ldBridgeN D.G D.kp D.Sb D.Z St₀ E₀ Unit (D.L * D.Z.err)).err
      ((D.T.N.beside Unit (LdCarX D.kp St₀) (LdCarE D.kp E₀)).seq (IOR.Nums.pure Unit _ _)).err
      (0 :: L) κ).2
    ⟨[0], L, rfl,
      ⟨by simpa using h.bridge, rfl⟩,
      (belowB_app (D.T.N.beside Unit (LdCarX D.kp St₀) (LdCarE D.kp E₀)).err _ L κ).2
        ⟨L, [], (List.append_nil L).symm, h.test, rfl⟩⟩

omit [Fintype E] in
theorem ldKappaW_nil (E₀ : ExtSpec) (Wp : Type) (w₀ : S.Wit × Wp) (κ : ℝ≥0∞) :
    (LdTc.nil S E₀ Wp w₀).c.BelowB [] κ :=
  (Chain.belowB_one _ _ κ).2 rfl

omit [Fintype E] in
theorem ldKappaW_nilA (E₀ : ExtSpec) (Wp : Type) (w₀ : S.Wit × Wp) (κ : ℝ≥0∞) :
    (LdTcA.nil S E₀ Wp w₀).cA.BelowB [] κ :=
  (ChainA.belowB_one _ _ κ).2 rfl

theorem ldKappaW_cons {E₀ : ExtSpec} {Wp : Type} (D : LdRunD S)
    (Q : LdTc (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) (κ : ℝ≥0∞)
    (L LQ : List ℕ) (h : D.BelowBT L κ) (hQ : Q.c.BelowB LQ κ) :
    (LdTc.cons D Q d d').c.BelowB ((0 :: L) ++ LQ) κ :=
  Chain.belowB_app _ _ _ _ κ ((Chain.belowB_one _ _ κ).2 (ldKappaW_run D Q.base d d' κ L h)) hQ

theorem ldKappaW_consLo {E₀ : ExtSpec} {Wp : Type} (D : LdRunD S)
    (QA : LdTcA (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) (κ : ℝ≥0∞)
    (L LQ : List ℕ) (h : D.BelowBT L κ) (hQ : QA.cA.BelowB LQ κ) :
    (LdTcA.consLo D QA d d').cA.BelowB ((0 :: L) ++ LQ) κ :=
  ChainA.belowB_app _ _ _ _ κ ((ChainA.belowB_one _ _ κ).2 (ldKappaW_run D QA.Q.base d d' κ L h)) hQ

theorem ldKappaW_consSh {E₀ : ExtSpec} {Wp : Type} (D : LdRunD S)
    (QA : LdTcA (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) (κ : ℝ≥0∞)
    (L LQ : List ℕ) (h : D.BelowBT L κ) (hQ : QA.cA.BelowB LQ κ) :
    (LdTcA.consSh D QA d d').cA.BelowB ((0 :: L) ++ LQ) κ :=
  ChainA.belowB_app _ _ _ _ κ ((ChainA.belowB_one _ _ κ).2 (ldKappaW_run D QA.Q.base d d' κ L h)) hQ

end

section
variable {E ι κ' J Λ : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ'] [Fintype J] [Fintype Λ]

structure LdLkP.KapCW (P : LdLkP E ι κ' J Λ) (S : P.Snd) (ε₀ ε₁ w : ℕ) (κ : ℝ≥0∞) : Prop where
  gam : (P.errGam ε₀ ε₁ : ℝ≥0∞) ≤ κ * (Fintype.card P.vGam.D : ℝ≥0∞)
  snd : (ldSendFamErr P.N S.Sd S.L : ℝ≥0∞) ≤ κ * (Fintype.card S.Sd.D : ℝ≥0∞)
  loc : (P.errLoc : ℝ≥0∞) ≤ κ * ((2 : ℝ≥0∞) ^ w * (Fintype.card P.vLoc.D : ℝ≥0∞))
  phi : (P.errPhi : ℝ≥0∞) ≤ κ * (Fintype.card P.vPhi.D : ℝ≥0∞)

theorem ldKappaW_link (P : LdLkP E ι κ' J Λ) (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (S : P.Snd) (ε₀ ε₁ w : ℕ) (κ : ℝ≥0∞) (h : P.KapCW S ε₀ ε₁ w κ) :
    (P.coreC on0 on1 S ε₀ ε₁).BelowB (lkBits w) κ :=
  Chain.belowB_mk _ _ [0, 0, 0, w] [0] κ
    (Chain.belowB_mk _ _ [0, 0, 0] [w] κ
      (Chain.belowB_mk _ _ [0] [0, 0] κ ((Chain.belowB_one _ _ κ).2 (belowB_peek0 _ _ κ h.gam))
        (belowB_send _ _ _ _ _ _ _ κ h.snd))
      (belowB_peek _ _ w κ h.loc))
    (belowB_peek0 _ _ κ h.phi)

theorem ldKappaW_linkC (P : LdLkP E ι κ' J Λ) (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (S : P.Snd) (ε₀ ε₁ w : ℕ) (K : P.Cl) (d₂ : P.W2) (d : P.W0) (κ : ℝ≥0∞) (L : List ℕ)
    (h : P.KapCW S ε₀ ε₁ w κ) (hK : K.run.BelowBT L κ) :
    Err.BelowB (P.linkC on0 on1 S ε₀ ε₁ (K.cZ d₂) d).P.err (lkBits w ++ ((0 :: L) ++ [])) κ := by
  unfold LdLkP.linkC
  exact (chain_belowB _ _ κ _).2
    (Chain.belowB_app _ _ _ _ κ (ldKappaW_link P on0 on1 S ε₀ ε₁ w κ h)
      (Chain.belowB_app _ _ [] _ κ ((Chain.belowB_one _ _ κ).2 rfl)
        (ldKappaW_cons K.run _ _ _ κ L [] hK (ldKappaW_nil _ _ _ κ))))

end

section
variable {E : Type} [Field E] [Fintype E]

structure LdSw.KapW {P P' St : Type} [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']
    (D : LdSw E P P' St) (e L w : ℕ) (κ : ℝ≥0∞) : Prop where
  ood : (D.W.err1 L : ℝ≥0∞) ≤ κ * (Fintype.card D.Zo.D : ℝ≥0∞)
  loc : (D.W.err2 e L : ℝ≥0∞) ≤
    κ * ((2 : ℝ≥0∞) ^ w * (Fintype.card ((Fin D.t → P) × D.Zb.D) : ℝ≥0∞))

theorem ldKappaW_sw {P P' St : Type} [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']
    (D : LdSw E P P' St) (e e' L t' w : ℕ) (κ : ℝ≥0∞) (h : D.KapW e L w κ) :
    Err.BelowB (ldSwBlock D e e' L t').N.err [0, w] κ :=
  ⟨by simpa using h.ood, h.loc, rfl⟩

structure LdJoint.KapBW (a : LdJoint E) (t bad L2 w : ℕ) (κ : ℝ≥0∞) : Prop where
  comb : ((bad + L2 : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card E : ℝ≥0∞)
  loc  : (((Fintype.card a.P - a.e - 1) ^ t : ℕ) : ℝ≥0∞) ≤
    κ * ((2 : ℝ≥0∞) ^ w * (Fintype.card (Fin t → a.P) : ℝ≥0∞))

theorem ldKappaW_base (a : LdJoint E) (t : ℕ) (cov : a.C.NP → a.P) (d bad L2 w : ℕ)
    (κ : ℝ≥0∞) (h : a.KapBW t bad L2 w κ) :
    Err.BelowB (ldBaseEnd a t cov d bad L2).N.err [0, w] κ :=
  ⟨by simpa using h.comb, h.loc, rfl⟩

/-- A concrete tower: its numbers with proof of work, its bits. -/
def LdTowC.KapW (w : ℕ) (κ : ℝ≥0∞) : {a : LdJoint E} → LdTowC a → Prop
  | _, .base a t _ _ bad L2 => a.KapBW t bad L2 w κ
  | _, @LdTowC.step _ _ _ _ _ _ _ _ _ _ Y sl e S _ Lst mC mS mW _ L rest =>
    (Y.reform sl).Kap Lst mC mS mW κ ∧ (S.D e).KapW e L w κ ∧ rest.KapW w κ

def LdTowC.bits (w : ℕ) : {a : LdJoint E} → LdTowC a → List ℕ
  | _, .base _ _ _ _ _ _ => [0, w]
  | _, @LdTowC.step _ _ _ _ _ _ _ _ _ _ Y sl _ _ _ _ _ _ _ _ _ rest =>
    (List.replicate (Y.reform sl).ior.shape.nAll 0 ++ [0, w]) ++ rest.bits w

theorem ldKappaW_step {a : LdJoint E} {P' StM : Type} [Fintype P'] [Nonempty P']
    (D : LdSw E a.P P' StM) (F : LdBlock a (D.jIn a.e)) (e' L : ℕ) (rest : LdTower (D.jOut e'))
    (κ : ℝ≥0∞) (L₁ L₂ L₃ : List ℕ) (h₁ : Err.BelowB F.N.err L₁ κ)
    (h₂ : Err.BelowB (ldSwBlock D a.e e' L rest.q).N.err L₂ κ)
    (h₃ : Err.BelowB rest.toEnd.N.err L₃ κ) :
    Err.BelowB (LdTower.step a D F e' L rest).toEnd.N.err ((L₁ ++ L₂) ++ L₃) κ :=
  (belowB_app (Err.app F.N.err (ldSwBlock D a.e e' L rest.q).N.err) rest.toEnd.N.err _ κ).2
    ⟨L₁ ++ L₂, L₃, rfl,
      (belowB_app F.N.err (ldSwBlock D a.e e' L rest.q).N.err _ κ).2 ⟨L₁, L₂, rfl, h₁, h₂⟩, h₃⟩

theorem ldKappaW_towC (w : ℕ) (κ : ℝ≥0∞) :
    ∀ {a : LdJoint E} (T : LdTowC a), T.KapW w κ → Err.BelowB T.toEnd.N.err (T.bits w) κ := by
  intro a T
  induction T with
  | base a t cov d bad L2 => exact fun h => ldKappaW_base a t cov d bad L2 w κ h
  | step Y sl e S d Lst mC mS mW e' L rest ih =>
    rintro ⟨h1, h2, h3⟩
    exact ldKappaW_step (a := ldWhole (Y.C.il (Fin Y.k → Bool)) (Y.Z.il (Fin Y.h → Bool)) sl e)
      (S.D e) (ldSumAfter Y e S.ts Lst mC mS mW sl ((Y.reform sl).ext d)) e' L rest.toTower κ _ _ _
      (belowB_none (s := (Y.reform sl).ior.shape) ((Y.reform sl).err Lst mC mS mW) κ
        (ld_sum_below (Y.reform sl) Lst mC mS mW κ h1.first h1.round))
      (ldKappaW_sw (S.D e) e e' L rest.toTower.q w κ h2) (ih h3)

section
variable {B : Type} [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P] {Sb : B → Type}
  {sl : ∀ b, Slf E (Sb b) G.C.J} {Z : Evader E (G.Row B)}

def LdTowG.KapW (w : ℕ) (κ : ℝ≥0∞) : LdTowG G Sb sl Z → Prop
  | .plain T => T.KapW w κ
  | @LdTowG.shaped _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sh Sw _ Lst mC mS mW _ L rest =>
    (Sh.fold Sb sl Z).Kap Lst mC mS mW κ ∧ (Sw.D G.e).KapW G.e L w κ ∧ rest.KapW w κ

def LdTowG.bits (w : ℕ) : LdTowG G Sb sl Z → List ℕ
  | .plain T => T.bits w
  | @LdTowG.shaped _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sh _ _ _ _ _ _ _ _ rest =>
    (List.replicate (Sh.fold Sb sl Z).ior.shape.nAll 0 ++ [0, w]) ++ rest.bits w

theorem ldKappaW_towG (w : ℕ) (κ : ℝ≥0∞) (T : LdTowG G Sb sl Z) (h : T.KapW w κ) :
    Err.BelowB T.toEnd.N.err (T.bits w) κ := by
  cases T with
  | plain T => exact ldKappaW_towC w κ T h
  | shaped Sh Sw d Lst mC mS mW e' L rest =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ldKappaW_step (a := G.joint Sb sl Z) (Sw.D G.e) (Sh.block Sb sl Z d Sw.ts Lst mC mS mW)
      e' L rest.toTower κ _ _ _
      (belowB_none (s := (Sh.fold Sb sl Z).ior.shape) ((Sh.fold Sb sl Z).err Lst mC mS mW) κ
        (ld_sum_below (Sh.fold Sb sl Z) Lst mC mS mW κ h1.first h1.round))
      (ldKappaW_sw (Sw.D G.e) G.e e' L rest.toTower.q w κ h2) (ldKappaW_towC w κ rest h3)

end

/-- A test whose whole test is a tower (`e`): the bridge's number (`hb`) and `T.KapW w κ` (`h`)
give `D.BelowBT (T.bits w) κ`. -/
theorem ldKappaW_pre {S : Sig E} (D : LdRunD S) (T : LdTowG D.G D.Sb D.sl D.Z) (w : ℕ)
    (κ : ℝ≥0∞) (e : D.T = T.toEnd)
    (hb : ((D.L * D.Z.err : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card D.Z.D : ℝ≥0∞)) (h : T.KapW w κ) :
    D.BelowBT (T.bits w) κ :=
  ⟨hb, by rw [e]; exact ldKappaW_towG w κ T h⟩

end
end Cb
