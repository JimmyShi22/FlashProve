-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/Gl/GlFinalEv.lean: the conditions of `Final` (Cb/Gl/GlFinal.lean) over p
= 2^64 - 2^32 + 1, with the properties listed under "Why" (of maps of coefficients, samples and
formats) each replaced by a condition on how the map, sample or format is built, from which the
property follows by a theorem;
the generic hypotheses on the protocol object follow under a named hypothesis on mutual correlated
agreement. No instance that meets the whole of `FinalEv` is exhibited: see Limits.

Definitions and statements (`Cb.Spec.fmtPlain_fmt`; the others in `Cb.Gl.Spec`); the proofs are in
Cb/Gl/GlFinalEvProofs.lean. Nothing assumed but in the last statement (`Spec.glEv_hyp`: its premise
`Cb.BCHKS46At F E`), beyond the hypotheses of the statements.
(The source of the statement on codes: the head of Cb/Gen/CodeListRS.lean.)
Forms in the place of properties: every public map of coefficients is of a form that has a theorem
(not: "is a zero-evader"); every switch's sample and the configuration's sample are rows with a pad
(not: "is a zero-evader", "is private") (the configuration's sample is the row with a pad, or has no
answer at all: `CfForm F`); every format is the plain one (not: "its encoder hides what the code's
hides").

Why: `Cb.Gl.Final` (Cb/Gl/GlFinal.lean) asks, as they stand: `Evader.OK` at twelve definitions,
`Sample.OK` and `Sample.PrivateSim` of each switch's sample, `Sample.OKOn` of the configuration's
sample, and in each format the clause `Y.Fmt.zk`: properties of public data, but properties. Here
each is replaced by a condition on the data's form, from which it follows by a theorem of this
library.

Main names, generic:
  `Y.PlainAt a`: a word as sent is a native word of the code.
  `Y.FmtPlain`: `Y.Fmt` (Cb/Gl/GlSenders.lean) with "plain : ∀ a, Y.PlainAt a" in the place of "zk";
    enc and lay as they stand (equations between maps).
Main names, at this field: each is the analogue of the record named in the last brackets of its row,
with the replacements named:
  `MsgsGlEv`, `LayGlEv`, `IsStdGlEv`, `IsGrpGlEv`, `ProtoGlAEv`, `ProtoGlSEv`, `ProtoGlLEv`:
    `Y.FmtPlain` for `Y.Fmt`, `Form` for `OK` of each evader (the records of the same names without
    Ev: Cb/GlVal/GlReqJohn.lean; `LayGl`: Cb/Gl/GlFinal.lean).
  `TowGlEv`, `TowGGlEv`, `TowGlJEv`, `TowGGlJEv`: at each switch: Zo.PadFillForm ∧ Zb.Form for Zo.OK
    ∧ Zb.OK ∧ Zo.PrivateSim E (`PadFillForm`: Cb/Ld/LdBldSw.lean: the row with a pad whose "pad"
    places are filler entries, read with equality weights like entries proper, and one pad entry)
    (`TowGl`, `TowGGl`, Cb/GlVal/GlThird.lean; `TowGlJ`, `TowGGlJ`, Cb/GlVal/GlJohn.lean).
  `RunGlAtEv`, `RunGlJAtEv`: `D.Z.Form` for `D.Z.OK`; the analogues above (`RunGlAt`, `RunGlJAt`,
    Cb/Gl/GlObjMix.lean).
  `ReqRefGlEv`: `R.Z.Form`; layD at `LayGlEv`; the analogues above (`ReqRefGlU`).
  `FinalEv X V p₀ plR a k msg r e mca`: smp : the configuration's sample is the row with a pad
    (`PadFormOn F`: with its three clauses of injectivity), or has no answer at all and a count
    `err` of at least the number of its seeds (`CfForm F`: Cb/Req1/LdReqJohnEvRec.lean);
    wfRest2 : `Rest2Ev`; the
    analogues above (`Final`).
  `Spec.glEv_msgs` and `Spec.glEv_std` to `Spec.glEv_runJ`: each analogue gives the record in its
    last brackets (in `glEv_towG3`, `glEv_towGJ`: G.P nonempty).
  `Spec.glEv_hyp`: BCHKS46At F E → FinalEv X .. → X.Z.HypRefJU LayGlEv p ..
  (FinalEv ⇒ Final is not stated: the record on masks stands at another letter, `LayGlEv`, the
  stronger one; the generic record takes every sound letter.)

`smp` admits two forms (`Sample.CfForm`: Cb/Req1/LdReqJohnEvRec.lean): the row with a pad, which
has one answer by definition (Cb/Gen/OodDecPad.lean: S := Unit), and a sample with no answer.



Why `Zo.PadFillForm`: the clause `Zo.PadForm E` (one pad entry and nothing else beside old message
and old randomness; as a theorem: `Cb.bldSw_pad_one`) is too narrow for the reference's numbers,
where the next mask rows are filled with uniform entries up to a power of two. `Zo.PadFillForm` is,
by reading, the write-up's sample of a stage; `Zo.PadForm E` is a case of `Zo.PadFillForm`
(`Cb.bldSw_of_pad`).

Which forms: Cb/Req1/LdReqJohnEvForm.lean (independent coefficients, powers, equality weights on the
cube and on numbers, the line, the one coefficient, Lagrange weights; products, fewer rows, a larger
number), Cb/Req1/LdReqJohnEvRec.lean (the row with a pad). Narrower than `Final`: whoever has a
zero-evader of another form is served by `Final`, not by this. By reading, all maps that the
write-up names are among these forms (equality weights; powers; for the zerocheck a product of
coefficients and equality weights; Lagrange weights times equality weights; at the reference the
equality weights on numbers, on fewer rows); in its theorems the map is any zero-evader: narrower
here. The switch's sample as the row with filler entries and one pad entry over E is, by
reading, what the write-up fixes for a stage's switch.
The plain format loses nothing new: under a standard layout a format over a proper subfield was
impossible already, but for a member that holds neither data nor free entries
(Cb/Req1/LdReqJohnSubNo.lean, under the hypotheses of the statement there); the pads' field is the
layout's, not the format's: pads in the base field within unique decoding stay possible.

Notation: `F`: the integers modulo p (Cb/Gl/GlField.lean); `E`: the challenge field
(Cb/Gl/GlField.lean); `a`, `k`, `msg`, `r`, `e`, `mca`: numbers; the field `code` asks that the code
of the encoded index be `rs a k msg r e mca` (Cb/Gl/GlCodes.lean), which is
`Code.RS.code (pts a) (k + 1) msg r e mca` (Code/RS.lean); `msg`, `r`, `e`, `mca` are handed on to
the fields of these names of `Code.Enc` (Code/Iface.lean): `e`: proximity parameter in positions;
`mca`: count of bad θ.

Limits: no instance that meets the whole of `FinalEv` is exhibited.


Until an instance is exhibited, a contradiction in the hypothesis on `Gl.FinalEv` cannot be
excluded, and, as far as this file shows, every
theorem that assumes `FinalEv` may hold of nothing. A form in the place of a property can be too
strong; `FinalEv` has no guard.
No value of this record is shown.
Beside `Spec.glEv_hyp` here, the statement `Spec.glAg_evHyp` (Cb/Gl/GlFinalAg.lean)
alone has `FinalEv` as a premise.
What is still asked and is not "families, places, forms and numbers": the model's duties (by a
reading of the definitions they cannot be met by a model with a condition that multiplies an entry
of the index with a cell); Fits of each group, the held
messages' laws, the laws of each shape's view; "the data map does not look" inside req.layD; formats
along the request ("fmt").
This file does not say that `FinalEv` can be met: no instance in this file. What the heads of
Cb/Gl/GlFinal.lean, Cb/Gl/GlFinJ.lean and Cb/GlVal/GlReqJohn.lean list as not said is not said here
either.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Gl.GlFinalAt
import Cb.Req1.LdReqJohnEvRec
import Cb.Ld.LdBldSwProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Sig.StdL
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
  {N : Sig E} (Y : N.StdL F)

/-- The member a is sent in the plain format. -/
def PlainAt (a : N.O) : Prop :=
  (⟨N.om a, Y.En a⟩ : Σ o : OMsg E, Hiop.Enc o.nat) =
    ⟨OMsg.plain (N.om a).C (N.om a).Z (N.om a).e (N.om a).rank, (N.om a).C.Nn⟩

/-- The format is the plain one. -/
structure FmtPlain : Prop where
  enc   : ∀ a m r, (N.om a).upW ((Y.En a).enc m r) = (N.om a).C.enc (Y.upM a m) (Y.upR a r)
  lay   : ∀ a x η n, Y.upM a (Y.msgOf a x η) ((Y.ν a).symm n) = withPad (F := F) x η n
  plain : ∀ a, Y.PlainAt a

end Sig.StdL

def Spec.fmtPlain_fmt : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
      (N : Sig E) (Y : N.StdL F),
    Y.FmtPlain → Y.Fmt

end Cb

namespace Cb.Gl
open Code Prob Blocks Iop Hiop IOR IOR.Chain Cb.Ood Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp
open scoped ENNReal

structure MsgsGlEv {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E] (N : Sig E)
    (Y : N.StdL Fp) (L t d : N.O → ℕ) : Prop where
  fmt  : Y.FmtPlain
  smp  : Y.PadSmp
  code : ∀ a, GlC (N.om a).C (d a) (t a)
  near : ∀ a, NearGl Y a (d a) (L a)

def LayGlEv : LdLayQ E := fun N t _ _ _ _ Y =>
  Y.FmtPlain ∧ Y.PadSmp ∧ ∃ d : N.O → ℕ, ∀ a, GlC (N.om a).C (d a) (t a)

section
variable {Kc : Type}

def IsStdGlEv {a : LdStage E Kc} (d : LdSendD a) : Prop :=
  ∃ (Fp : Type) (_ : Field Fp) (_ : Fintype Fp) (_ : Algebra Fp E) (Y : d.N.StdL Fp)
      (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → d.Wp')
      (bk₀ : (∀ i, Y.Dt i → E) → d.Wp' → a.Wp) (w0 : a.S.Wit × a.Wp) (dd : d.N.O → ℕ),
    d = LdSendD.std a d.N d.Sd d.Wp' d.L d.t Y dat rst bk₀ w0 ∧
    (∀ w, bk₀ (dat w) (rst w.2) = w.2) ∧
    d.Sd.Fair ∧
    MsgsGlEv d.N Y d.L d.t dd

def IsGrpGlEv (D : LdFoldD E Kc) (l : Link Kc D.src.J D.mid) : Prop :=
  ∃ (_ : Fintype D.B) (_ : Nonempty D.G.P) (Sh : GShape D.G) (Hd : GHeld Sh D.kp)
      (Z : Evader E (D.G.Row D.B)) (hc : ∀ o, D.G.mem o ∨ D.kp o)
      (dw : D.S.Wit × D.Wp) (d t bC bZ bW : ℕ),
    (⟨D, l⟩ : Σ D : LdFoldD E Kc, Link Kc D.src.J D.mid) =
      ⟨Hd.foldD D.Sb D.sl Z D.A₀,
        Hd.link D.Sb D.sl Z D.A₀ hc dw d t (fun _ => listMax (Fintype.card D.G.P) d D.G.e)
          (fun _ => bC) (fun _ => bZ) (fun _ => bW) (listMax (Fintype.card D.G.P) d D.G.e)⟩ ∧
    (Sh.view.Laws ∧
      (∀ r b, Sh.dst r = .inl b → Sh.ord b = some r) ∧
      (∀ r j, Sh.dst r = .inr j → Sh.kept j = r) ∧
      (∀ r, Sh.ordZ (Sh.dstZ r) = some r) ∧
      1 ≤ Sh.h + Sh.g) ∧
    Hd.Laws ∧
    (GlJ Sh.Cb d 0 D.G.e bC ∧
      GlJ Sh.Zb d 0 D.G.e bZ ∧
      GlJ Sh.par.Zw d t D.G.e bW ∧
      InJohnson (Fintype.card D.G.P) d D.G.e) ∧
    (Function.Injective Sh.val ∧ 2 ≤ Sh.n ∧ Sh.par.PackOK ∧ Sh.par.QwDeg) ∧
    Z.Form ∧ D.G.Fits

structure ProtoGlAEv {I : LdRefIx E} (A : LdRefD E Kc I) (pp : ℕ) : Prop where
  front  : A.V.ProtoEv pp
  ok     : A.Xa.Q.D.p.OK
  places : A.Xa.Q.Places
  uniq   : Uniq (2 * A.Xa.Q.D.p.D) A.Xa.Q.D.p.rdx A.Xa.Q.D.p.P pp
  send1  : IsStdGlEv A.Xa.Q.D.d1
  send3  : IsStdGlEv A.Xa.Q.D.d3
  tabQ   : A.Xa.Q.D.p.q ≤ 2 ^ A.Xa.Q.d
  tabH   : A.Xa.Q.D.p.H ≤ 2 ^ A.Xa.Q.d
  keys   : A.Xa.Q.K ≤ 2 ^ A.Xa.Q.v
  tags   : A.Xa.Q.tag 0 ≠ A.Xa.Q.tag 1
  inj    : Function.Injective A.Xa.ι
  named  : A.Xa.A.PlacesIn (fun j => j ∈ Set.range A.Xa.ι)
  adm    : A.Xa.A.H.lkb.Adm pp
  bits   : A.Xa.Bits
  reads  : A.Gr.Reads
  deg    : 2 ≤ A.nt
  ev     : A.Zt.Form

structure ProtoGlSEv {I : LdRefIx E} {a : LdStage E Kc} (S : LdRefS E Kc I a) (pp : ℕ) : Prop where
  body  : ProtoGlAEv S.A pp
  ev    : S.K.Z.Form
  named : ∀ n, S.A.Gr.Named n → S.K.grp.mem n.1
  fold  : IsGrpGlEv S.K.R.c1.fold S.l
  snd   : IsStdGlEv S.Qc.snd

def ProtoGlLEv {I : LdRefIx E} {a : LdStage E Kc} (pp : ℕ) :
    {b : LdStage E Kc} → LdRefL E Kc I a b → Prop
  | _, .nil => True
  | _, .snoc L S => ProtoGlLEv pp L ∧ ProtoGlSEv S pp

end

def TowGlEv : {a : LdJoint E} → LdTow3 a → Prop
  | _, .base a _ _ d => GlC a.C d 0 ∧ 3 * a.e < d
  | _, @LdTow3.step _ _ _ _ _ _ _ _ _ _ Y sl e S d e' d' rest =>
      (GlC Y.C d 0 ∧ GlC Y.Z d 0 ∧ GlC Y.Zw d S.ts ∧ 3 * e < d ∧
        Function.Injective (Y.reform sl).val ∧ 2 ≤ (Y.reform sl).n ∧
        (Y.reform sl).PackOK ∧ (Y.reform sl).QwDeg) ∧
      (GlC S.Cnew d' rest.toC.q ∧ 2 * e' < d' ∧ (S.D e).Zo.PadFillForm ∧ (S.D e).Zb.Form) ∧
      TowGlEv rest

def TowGGlEv {B : Type} [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P] {Sb : B → Type}
    {sl : ∀ b, Slf E (Sb b) G.C.J} {Z : Evader E (G.Row B)} : LdTowG3 G Sb sl Z → Prop
  | .plain T => TowGlEv T
  | @LdTowG3.shaped _ _ _ _ _ _ _ _ _ _ _ _ _ _ Sh Sw d e' d' rest =>
      (Sh.view.Laws ∧
        (∀ r b, Sh.dst r = .inl b → Sh.ord b = some r) ∧
        (∀ r j, Sh.dst r = .inr j → Sh.kept j = r) ∧
        (∀ r, Sh.ordZ (Sh.dstZ r) = some r) ∧
        1 ≤ Sh.h + Sh.g) ∧
      (GlC Sh.Cb d 0 ∧ GlC Sh.Zb d 0 ∧ GlC Sh.par.Zw d Sw.ts ∧ 3 * G.e < d ∧
        Function.Injective Sh.par.val ∧ 2 ≤ Sh.par.n ∧ Sh.par.PackOK ∧ Sh.par.QwDeg) ∧
      (GlC (Sw.D G.e).Cout d' rest.toC.q ∧ 2 * e' < d' ∧
        (Sw.D G.e).Zo.PadFillForm ∧ (Sw.D G.e).Zb.Form) ∧
      TowGlEv rest

def TowGlJEv : {a : LdJoint E} → LdTowJ a → Prop
  | _, .base a _ _ d b => GlJ a.C d 0 a.e b ∧ InJohnson (Fintype.card a.P) d a.e
  | _, @LdTowJ.step _ _ _ P P' _ _ _ _ _ Y sl e S d bC bZ bW e' d' rest =>
      (GlJ Y.C d 0 e bC ∧ GlJ Y.Z d 0 e bZ ∧ GlJ Y.Zw d S.ts e bW ∧
        InJohnson (Fintype.card P) d e ∧ Function.Injective (Y.reform sl).val ∧
        2 ≤ (Y.reform sl).n ∧ (Y.reform sl).PackOK ∧ (Y.reform sl).QwDeg) ∧
      (GlC S.Cnew d' rest.toC.q ∧ InJohnson (Fintype.card P') d' e' ∧
        (S.D e).Zo.PadFillForm ∧ (S.D e).Zb.Form) ∧
      TowGlJEv rest

def TowGGlJEv {B : Type} [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P] {Sb : B → Type}
    {sl : ∀ b, Slf E (Sb b) G.C.J} {Z : Evader E (G.Row B)} : LdTowGJ G Sb sl Z → Prop
  | .plain T => TowGlJEv T
  | @LdTowGJ.shaped _ _ _ _ _ _ _ _ _ _ _ P' _ _ Sh Sw d bC bZ bW e' d' rest =>
      (Sh.view.Laws ∧
        (∀ r b, Sh.dst r = .inl b → Sh.ord b = some r) ∧
        (∀ r j, Sh.dst r = .inr j → Sh.kept j = r) ∧
        (∀ r, Sh.ordZ (Sh.dstZ r) = some r) ∧
        1 ≤ Sh.h + Sh.g) ∧
      (GlJ Sh.Cb d 0 G.e bC ∧ GlJ Sh.Zb d 0 G.e bZ ∧ GlJ Sh.par.Zw d Sw.ts G.e bW ∧
        InJohnson (Fintype.card G.P) d G.e ∧ Function.Injective Sh.par.val ∧ 2 ≤ Sh.par.n ∧
        Sh.par.PackOK ∧ Sh.par.QwDeg) ∧
      (GlC (Sw.D G.e).Cout d' rest.toC.q ∧
        InJohnson (Fintype.card P') d' e' ∧
        (Sw.D G.e).Zo.PadFillForm ∧
        (Sw.D G.e).Zb.Form) ∧
      TowGlJEv rest

def RunGlAtEv {S : Sig E} (D : LdRunD S) (Tw : D.Tow3) (d : ℕ) : Prop :=
  D.T = Tw.toG.toEnd ∧ D.t = Tw.toG.q ∧ D.L = 1 ∧
  (∀ a : D.G.A, GlC ((S.om a.1).C.atPos (D.G.pos a)) d 0) ∧
  3 * D.G.e < d ∧ D.G.Fits ∧ D.Z.Form ∧ TowGGlEv Tw

def RunGlJAtEv {S : Sig E} (D : LdRunD S) (Tw : D.TowJ) (d : ℕ) : Prop :=
  D.T = Tw.toG.toEnd ∧ D.t = Tw.toG.q ∧ D.L = listMax (Fintype.card D.G.P) d D.G.e ∧
  (∀ a : D.G.A, GlC ((S.om a.1).C.atPos (D.G.pos a)) d 0) ∧
  InJohnson (Fintype.card D.G.P) d D.G.e ∧ D.G.Fits ∧ D.Z.Form ∧ TowGGlJEv Tw

structure ReqRefGlEv {Kc : Type} (pp : ℕ) (R : LdORE F E Kc)
    (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
    (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
    (L : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
    (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
    (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) : Prop where
  duty   : LdModelDuty R L T
  std    : IsStdGlEv first ∧ ProtoGlLEv pp L ∧ ProtoGlAEv T.A pp
  deg    : 2 ≤ R.n
  ev     : R.Z.Form
  tie    : R.Tie
  own    : R.X.Own
  layD   : LdReqRefLayD LayGlEv pp R first b L T
  fmt    : ∃ (px' : first.Wp' → R.Cf.conf.PIdx)
        (φb : JFmt Kc R.Cf.conf.E0 R.Cf.conf.Rec R.Cf.conf.PIdx b.J),
      (∀ w, px' (first.D.rest w).2 = w.2.1) ∧
      L.FmtP (first.tgt.fmt (⟨id, id⟩ : IxAt R.Cf.conf.E0 R.Cf.conf.E0) Prod.snd px'
          ((LdStage.start E Kc (R.O.jReq core)).S.qSum first.N qφ first.t)) φb ∧
      T.FmtAt φb q
  bFirst : (ldSendFamErr first.N first.Sd first.L : ℝ≥0∞) ≤ κ * (Fintype.card first.Sd.D : ℝ≥0∞)
  bSegs  : L.Nums κ
  bTail  : T.A.Nums κ
  bLast  : Err.Below (R.X.bt.nums R.Cf.conf.E0 Kc).err κ

/-- The conditions of `Final` (Cb/Gl/GlFinal.lean), forms in the place of properties. -/
structure FinalEv (X : LdFinJ F E) [∀ b, Fintype (X.Z.Zw.K.wfI X.Z.Zw.Rl b → E)] {Fp : Type}
    [Field Fp] [Fintype Fp] [Algebra Fp E] (V : X.Z.Zw.StdW Fp) (p₀ : LdLinPl X.R.O.d.ol.toC)
    (plR : X.R.Bn → X.R.S.Ent → Prop) (a k msg r e mca : ℕ) : Prop where
  /-- which terms stand in the object -/
  wfIs    : (⟨X.Z.R.W, X.Z.R.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨X.Z.Zw.W, X.Z.Zw.G.B⟩
  sndIs   : X.Z.R.toLdObjD = X.Z.R.toLdObjD.std X.Z.Y
  reqIs   : X.Z.R.toLdObjD.pack =
    ldRefPack X.R X.core X.first X.first.tgt (.nil X.first.tgt)
      (LdProg.all_nilK _ _) X.c X.Ls X.T X.qφ X.q
  onIs    : X.Z.R.onPack = ldRefOn X.R p₀
  /-- the code of the encoded index: within a third -/
  code    : X.Z.Zw.W.Cf.C₀ = rs a k msg r e mca
  ha      : a ≤ 32
  hk      : k < 2 ^ a
  hp      : msg + r ≤ k + 1
  h3      : 3 * X.Z.Zw.W.Cf.eM < 2 ^ a - k
  smp     : X.Z.Zw.W.Cf.Z.CfForm F
  model   : X.Z.Zw.W.Cf.ModelOK
  /-- weights-formedness, its sender the standard one -/
  wfStd   : (⟨X.Z.Zw.D, X.Z.Zw.X⟩ : Σ D, X.Z.Zw.K.MaskPl D X.Z.Zw.Rl) =
    ⟨X.Z.Zw.W.P.stdD V.Y V.dat V.w0,
      X.Z.Zw.K.stdX X.Z.Zw.Rl V.Y V.dat V.w0 V.nAt V.RdW V.atL V.pl V.hpl⟩
  wfBody  : ∀ m, X.Z.Zw.W.P.body m = V.bd (V.Y.dataOf m)
  wfBd    : ∀ b, V.bd (V.dat b) = b
  wfAtL   : ∀ l i, V.nAt (V.atL l i) = V.Y.entF (V.pl (some l) i)
  wfAtB   : ∀ i, V.nAt (X.Z.Zw.W.P.wAt i) = V.Y.entF (V.pl none i)
  wfNoPad : ∀ n, V.RdW n → V.Y.NoPad n
  wfRest2 : X.Z.Zw.Rest2Ev p
  wfM     : MsgsGlEv X.Z.Zw.W.P.S V.Y X.Z.Zw.L X.Z.Zw.t X.Z.dS
  /-- the offline test's three sendings -/
  plS     : X.Z.Y.TS.Places
  fW      : X.Z.R.W.O.toC.P.SdW.Fair
  fU      : X.Z.R.W.O.toC.P.SdU.Fair
  fO      : X.Z.R.W.O.toC.P.SdO.Fair
  sW      : MsgsGlEv X.Z.R.W.O.toC.P.NW X.Z.Y.TS.YW X.Z.Y.LW X.Z.Y.tW X.Z.dW
  sU      : MsgsGlEv X.Z.R.W.O.toC.P.NU X.Z.Y.TS.YU X.Z.Y.LU X.Z.Y.tU X.Z.dU
  sO      : MsgsGlEv X.Z.R.W.O.toC.P.NO X.Z.Y.TS.YO X.Z.Y.LO X.Z.Y.tO X.Z.dO
  /-- the link's sending -/
  rdK     : X.Z.Y.YK.Reads X.Z.Y.ixK fun m => Sum.elim (X.Z.R.K.P.uv₀ m) (X.Z.R.K.P.uv₁ m)
  fK      : X.Z.Y.SdK.Fair
  sK      : MsgsGlEv X.Z.R.K.P.N X.Z.Y.YK X.Z.Y.LK X.Z.Y.tK X.Z.dN
  /-- the batch test's three sendings -/
  plB     : X.Z.Y.TB.Places
  fWB     : X.Z.R.on.ol.toC.P.SdW.Fair
  fUB     : X.Z.R.on.ol.toC.P.SdU.Fair
  fOB     : X.Z.R.on.ol.toC.P.SdO.Fair
  sWB     : MsgsGlEv X.Z.R.on.ol.toC.P.NW X.Z.Y.TB.YW X.Z.Y.LWB X.Z.Y.tWB X.Z.dWB
  sUB     : MsgsGlEv X.Z.R.on.ol.toC.P.NU X.Z.Y.TB.YU X.Z.Y.LUB X.Z.Y.tUB X.Z.dUB
  sOB     : MsgsGlEv X.Z.R.on.ol.toC.P.NO X.Z.Y.TB.YO X.Z.Y.LOB X.Z.Y.tOB X.Z.dOB
  /-- the index's folds -/
  own₀    : X.Z.R.toLdObjD.Own3₀
  /-- the request -/
  req     : ReqRefGlEv p X.R X.core X.first X.c X.Ls X.T X.qφ X.q X.κ
  places  : X.R.PlacesOK p₀ plR
  pl₁     : X.Z.R.HypPl₁
  /-- the link's test and the offline test's three: within a third -/
  tK      : RunGlAtEv X.Z.R.Kc.run X.Z.twK X.Z.dK
  t₁      : RunGlAtEv X.Z.R.TP₀.D₁ X.Z.tw₁ X.Z.d₁
  t₂      : RunGlAtEv X.Z.R.TP₀.D₂ X.Z.tw₂ X.Z.d₂
  t₃      : RunGlAtEv X.Z.R.X.run X.Z.tw₃ X.Z.d₃
  /-- the session's three tests: below the Johnson radius -/
  t₁B     : RunGlJAtEv X.Z.R.TB₀.D₁ X.Z.tw₁B X.Z.d₁B
  t₂B     : RunGlJAtEv X.Z.R.TB₀.D₂ X.Z.tw₂B X.Z.d₂B
  t₃B     : RunGlJAtEv X.Z.R.XB.run X.Z.tw₃B X.Z.d₃B

namespace Spec

def glEv_msgs : Prop :=
  ∀ (Fp : Type) [Field Fp] [Fintype Fp] [Algebra Fp E] (N : Sig E)
      (Y : N.StdL Fp) (L t d : N.O → ℕ),
    MsgsGlEv N Y L t d → MsgsGl N Y L t d

def glEv_lay : Prop := LayGlEv.Sound

def glEv_std : Prop := ∀ (Kc : Type) (a : LdStage E Kc) (d : LdSendD a), IsStdGlEv d → IsStdGl d

def glEv_grp : Prop :=
  ∀ (Kc : Type) (D : LdFoldD E Kc) (l : Link Kc D.src.J D.mid), IsGrpGlEv D l → IsGrpGl D l

def glEv_body : Prop :=
  ∀ (Kc : Type) (I : LdRefIx E) (A : LdRefD E Kc I) (pp : ℕ), ProtoGlAEv A pp → ProtoGlA A pp

def glEv_seg : Prop :=
  ∀ (Kc : Type) (I : LdRefIx E) (a : LdStage E Kc) (S : LdRefS E Kc I a) (pp : ℕ),
    ProtoGlSEv S pp → ProtoGlS S pp

def glEv_list : Prop :=
  ∀ (Kc : Type) (I : LdRefIx E) (a b : LdStage E Kc) (L : LdRefL E Kc I a b) (pp : ℕ),
    ProtoGlLEv pp L → ProtoGlL pp L

def glEv_tow3 : Prop := ∀ (a : LdJoint E) (T : LdTow3 a), TowGlEv T → TowGl T

def glEv_towG3 : Prop :=
  ∀ (B : Type) [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P] (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (T : LdTowG3 G Sb sl Z),
    TowGGlEv T → TowGGl T

def glEv_towJ : Prop := ∀ (a : LdJoint E) (T : LdTowJ a), TowGlJEv T → TowGlJ T

def glEv_towGJ : Prop :=
  ∀ (B : Type) [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P] (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (T : LdTowGJ G Sb sl Z),
    TowGGlJEv T → TowGGlJ T

def glEv_run3 : Prop :=
  ∀ (S : Sig E) (D : LdRunD S) (Tw : D.Tow3) (d : ℕ), RunGlAtEv D Tw d → RunGlAt D Tw d

def glEv_runJ : Prop :=
  ∀ (S : Sig E) (D : LdRunD S) (Tw : D.TowJ) (d : ℕ), RunGlJAtEv D Tw d → RunGlJAt D Tw d

/-- The generic record, from forms (`FinalEv`), under the statement on codes (`Cb.BCHKS46At`) at one
field. -/
def glEv_hyp : Prop :=
  Cb.BCHKS46At F E →
  ∀ (X : LdFinJ F E) [∀ b, Fintype (X.Z.Zw.K.wfI X.Z.Zw.Rl b → E)] (Fp : Type) [Field Fp]
      [Fintype Fp] [Algebra Fp E] (V : X.Z.Zw.StdW Fp) (p₀ : LdLinPl X.R.O.d.ol.toC)
      (plR : X.R.Bn → X.R.S.Ent → Prop) (a k msg r e mca : ℕ),
    FinalEv X V p₀ plR a k msg r e mca →
    X.Z.HypRefJU LayGlEv p X.R X.core X.first X.c X.Ls X.T X.qφ X.q X.κ V p₀ plR

end Spec
end Cb.Gl
