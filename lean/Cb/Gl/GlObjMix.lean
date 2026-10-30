-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in forms of some of its theorems (files named `…Codes.lean` under
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
Cb/Gen/CodeListRS.lean.) Cb/Gl/GlObjMix.lean: clauses on codes in the hypotheses on the protocol
object over
p = 2^64 - 2^32 + 1 follow from conditions on its Reed-Solomon codes and radii, under a named
hypothesis on mutual correlated agreement; the other clauses, those on the request's codes (inside
`own`: `rHyp`) among them, are asked as they stand.

Exactly: the object over p with plain Reed-Solomon codes: the offline phase and the link within a
third of the distances (their four sendings: 2 e below the distance), the groups of a session below
the Johnson radius: under the one hypothesis BCHKS46F F, by name.

Definitions, four lemmas, one statement (`Cb.Gl.Spec.glM_hyp`) and its proof: an assembly.
Cb/Obj/LdObjectDataMix.lean: the object's hypotheses on data at the point that a write-up of
ours (lean/CREDITS.md) takes as its reference (`Z.Hyp p` for `Z : LdObjZM F E`). Here: F the
integers modulo p,
E = F[x] / (x^3 - 2); the encoded index under rs a k msg r (Cb/Gl/GlCodes.lean); every other code
but the request's `GlC` / `GlJ` (Cb/Gl/GlLd.lean, Cb/Gl/GlLdJ.lean: built from families of plain
Reed-Solomon codes on subgroups of orders at most 2^32). The clauses on codes are derived, but for
the request's (`own`: `rHyp`) and those listed below as asked.

The hypothesis. Cb.BCHKS46F F (Cb/Gen/CodeListRSF.lean): mutual correlated agreement of Reed-Solomon
codes below the Johnson radius, for two words, for the finite extensions of F and points in F.
A case of the Theorem 4.6 that the lines at the top name, for which the source gives an outline of a
proof; NOT proved here; NO axiom: it stands in the text of the statement. It is used for one thing:
`T.John` of the three towers of the session's test (the agreement inside them). Offline phase and
link use nothing.
(The source of the statement on codes: the head of Cb/Gen/CodeListRS.lean.)

Main names:
  `RunGlAt D T d`: a test on a group within a third, its tower T given as data: the whole test is
    the tower, its number of positions the tower's; bound 1; each member's code at the group's
    positions `GlC` with distance d; 3 e < d; Fits; the bridge's evader; `TowGGl T`. `gl3_runAt`: ⇒
    `D.Pre3 T d`.
  `RunGlJAt D T d`: the same below the Johnson radius: the bound is listMax; InJohnson; `TowGGlJ T`
    (the three codes of each fold and the last code `GlJ`: Cb/Gl/GlLdJ.lean). `glJ_runAt`: BCHKS46F
    F → .. ⇒ `D.PreJ T d`.
  `SndGl3 N Y Sd L t d`: one standard sending within unique decoding; `SndGlJ`: below the Johnson
    radius (both for a layout with pads in any subfield Fp of E; `ObjGlM` takes `Z.Y.Fp`: see On the
    pads' field).
  `Spec.glM_hyp`: BCHKS46F F → ObjGlM Z .. → `Z.Hyp p`.

Which clauses of `Z.Hyp p` are derived here, and from what.
  Of weights-formedness (Zw.Third p dS): the configuration within a third (from the index's code and
  four inequalities), laws and distances of its messages' codes: from `GlC`; its clauses lt
  (3 e < dS) and one (bound 1) are asked as they stand.
  Of the seven standard sendings: laws, distances; what the sent encodings hide (from t uniform
  coefficients inside `GlC`, through the format's clause zk); offline and link: "evades": from `GlC`
  at (d, t), 2 e < d.
  Of the seven tests on groups: laws and distances at the group's positions; `T.Third` of four
  towers; `T.John` of three towers: under BCHKS46F F.
Which clauses are asked as they stand in `Z.Hyp p` (they pass through this theorem unchanged).
  wfIs, sndIs (two equations); own : D.Own3 (inside it, of the request, a parameter: `rHyp`, which
  at a move `sub` is `c.AllB` (`LdMv.Hyp`, Cb/Req1/LdSeg.lean; Ior/KnowCollRulesChain.lean): `GoodB`
  (Ior/Masked.lean) of every link of a chain, completeness and knowledge soundness among its fields;
  at a move `fold` it holds `GoodT` of a link, zero knowledge (`exact`) included; at a sending
  `blind` and `hides` of the sender; and `rZk`, what honest-verifier zero knowledge asks of the
  request beside `rHyp`: asked, not derived); pl : R.HypPl; the sample map and the model of the
  configuration.
  `Zw.Rest0 p`, which holds, beside its clauses on places, numbers, keys, the model, fair seeds, the
  multiplicities and more (`Rest2`, Cb/Ld/LdWfEnd.lean), six clauses on the sender of
  weights-formedness, a term of the data: for the standard sender these six are theorems, under the
  hypotheses of their statements (Cb/Ld/LdWfEndStd.lean): not put in here. The six clauses:
    sender: it sends what "back" undoes;
    sBlind: the law of its answers does not depend on the witness;
    hides: what its encodings hide: a clause on sender and codes together, asked here, not derived
      from GlC: the codes of weights-formedness' messages are asked GlC at t = 0 only;
    pad: the pads alone fix the law of the answers;
    sOwn: the entry at a mask place is the mask's value;
    sOff: other entries shown read neither these masks nor the pads
  (the last three exactly: `Rest1`, Cb/Ld/LdWfEnd.lean, which `Rest0` extends).
  Of the sendings: Places, Reads (places); seeds fair; `Y.Fmt` (three clauses on the format; the
  third, zk, stands not in `Z.Hyp p`: it is asked here in the place of the field `hides` of `Y.OK t`
  (Cb/Ld/LdSendStdL.lean)); "the sample's answers are private over the pads"; the radii's
  inequalities; the bounds on lists as equations; for the session's three sendings: "evades" (two
  members of a list agree at few seeds: beyond unique decoding it is a condition on the sample, not
  derived).
  Of the tests: "the whole test is the tower", its number of positions, Fits, the bridge's evader,
  the bound on the list as an equation, the radius's inequality (within a third: 3 e < d is asked,
  `Z.Hyp p` has 2 e < d); inside `TowGGl` / `TowGGlJ`: what does not speak of codes (packing,
  degrees, evaders of the switches, the privacy of their samples (`Zo.PrivateSim E`), injective
  challenges, the radii's inequalities), and of a shaped tower where its main rows and mask rows
  stand (three clauses), at least one variable, and `Sh.view.Laws` (Cb/Ld/LdGroupFold.lean), which
  does.

On the pads' field. The object's record of standard senders (Cb/Obj/LdObjectSendersLin.lean:
`D.StdS`) holds a pads' field of its own, `Y.Fp` (any subfield of E), for its seven layouts;
`ObjGlM` takes `Z.Y.Fp` as it comes (`SndGl3`, `SndGlJ` are stated for any pads' field). The
write-up gives each oracle message a field of its own (F if all its rows are over F, else E) and
pads of that field; the messages of the test for linear constraints and of the link are all over E:
one pad entry of E an answer: the write-up's case is Z.Y.Fp := E.
  A caution for Z.Y.Fp := F. Private answers then want three pad entries an answer. By the warning
  in the head of Cb/Gl/GlSenders.lean, for the padded sample of Cb/Gen/OodDecPad.lean three F-valued
  pads at places of a message over E are no evader: two messages over E that differ at the pad
  places by a vector that the weights annihilate have the same answers at every seed. Within unique
  decoding nothing is lost. Beyond half the distance "private over pads in F" and "evades" may not
  be meetable together: at that choice it is not known that the session's three clauses `SndGlJ` can
  be met. The write-up excludes that case.
  (One pads' field for all seven families is enough here. It is not the write-up's
  generality:
  there the field goes with the single oracle message.)

Notation: `p` in `Z.Hyp p`, `Rest0 p`: the prime of the title (`Cb.Gl.p`, Cb/Gl/GlField.lean); `a`,
`k`, `msg`, `r`, `e`, `mca`: numbers; `ObjGlM`'s field `code` asks that the code of the encoded
index be `rs a k msg r e mca` (Cb/Gl/GlCodes.lean), which is
`Code.RS.code (pts a) (k + 1) msg r e mca` (Code/RS.lean); `msg`, `r`, `e`, `mca` are handed on to
the fields of these names of `Code.Enc` (Code/Iface.lean): `e`: proximity parameter in positions;
`mca`: count of bad θ.

Limits: this file does not say that `ObjGlM` can be met: no instance of `ObjGlM` is shown. This file
gives no instance that meets its hypotheses, so as far as this file shows its theorems may hold of
nothing.  Whether the source proves what it
states: that is not said either. Not said either: that its count is small against the field. All
that the head of Cb/Obj/LdObjectDataMix.lean declares holds here too (the request is a parameter;
the plan of the linear test).

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Obj.LdObjectDataMix
import Cb.GlVal.GlJohn
import Cb.Gl.GlSenders

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks Iop Hiop IOR

/-- A test on a group within a third, its tower given. -/
def RunGlAt {S : Sig E} (D : LdRunD S) (Tw : D.Tow3) (d : ℕ) : Prop :=
  D.T = Tw.toG.toEnd ∧ D.t = Tw.toG.q ∧ D.L = 1 ∧
  (∀ a : D.G.A, GlC ((S.om a.1).C.atPos (D.G.pos a)) d 0) ∧
  3 * D.G.e < d ∧ D.G.Fits ∧ D.Z.OK ∧ TowGGl Tw

/-- A test on a group below the Johnson radius, its tower given. -/
def RunGlJAt {S : Sig E} (D : LdRunD S) (Tw : D.TowJ) (d : ℕ) : Prop :=
  D.T = Tw.toG.toEnd ∧ D.t = Tw.toG.q ∧ D.L = listMax (Fintype.card D.G.P) d D.G.e ∧
  (∀ a : D.G.A, GlC ((S.om a.1).C.atPos (D.G.pos a)) d 0) ∧
  InJohnson (Fintype.card D.G.P) d D.G.e ∧ D.G.Fits ∧ D.Z.OK ∧ TowGGlJ Tw

theorem gl3_runAt {S : Sig E} (D : LdRunD S) (Tw : D.Tow3) (d : ℕ) :
    RunGlAt D Tw d → D.Pre3 Tw d := by
  rintro ⟨h1, h2, h3, hG, hlt, hF, hZ, hT⟩
  exact ⟨h1, h2, h3, fun a => (glC_code D.G.P _ d 0 (hG a)).1,
    fun a => (glC_code D.G.P _ d 0 (hG a)).2.2.2.1, by omega, hZ,
    hF, gl3_towerG _ S D.G D.Sb D.sl D.Z Tw hT⟩

theorem glJ_runAt (H : Cb.BCHKS46F F) {S : Sig E} (D : LdRunD S) (Tw : D.TowJ) (d : ℕ) :
    RunGlJAt D Tw d → D.PreJ Tw d := by
  rintro ⟨h1, h2, h3, hG, hJ, hF, hZ, hT⟩
  exact ⟨h1, h2, h3, fun a => (glC_code D.G.P _ d 0 (hG a)).1,
    fun a => (glC_code D.G.P _ d 0 (hG a)).2.2.2.1, hJ, hZ, hF,
    glJ_towerG H _ S D.G D.Sb D.sl D.Z Tw hT⟩

/-- One standard sending, within unique decoding. -/
structure SndGl3 {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E] (N : Sig E) (Y : N.StdL Fp)
    (Sd : N.Seeds) (L t d : N.O → ℕ) : Prop where
  fmt  : Y.Fmt
  priv : ∀ a, ((N.om a).Z.comap (Y.ν a).symm).Private Fp fun _ => True
  code : ∀ a, GlC (N.om a).C (d a) (t a)
  lt   : ∀ a, 2 * (N.om a).e < d a
  one  : ∀ a, L a = 1
  fair : Sd.Fair

/-- One standard sending, below the Johnson radius. -/
structure SndGlJ {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E] (N : Sig E) (Y : N.StdL Fp)
    (Sd : N.Seeds) (L t d : N.O → ℕ) : Prop where
  fmt  : Y.Fmt
  priv : ∀ a, ((N.om a).Z.comap (Y.ν a).symm).Private Fp fun _ => True
  code : ∀ a, GlC (N.om a).C (d a) (t a)
  inJ  : ∀ a, InJohnson (Fintype.card (N.om a).P) (d a) (N.om a).e
  isL  : ∀ a, L a = listMax (Fintype.card (N.om a).P) (d a) (N.om a).e
  fair : Sd.Fair
  ev   : ∀ a, (N.om a).Evades

theorem SndGl3.ok {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E] {N : Sig E} {Y : N.StdL Fp}
    {Sd : N.Seeds} {L t d : N.O → ℕ} (h : SndGl3 N Y Sd L t d) : Y.OK t :=
  ⟨h.fmt.enc, h.fmt.lay, h.priv, fun a => h.fmt.zk a _ (glC_code _ _ _ _ (h.code a)).2.2.2.2⟩

theorem SndGlJ.ok {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E] {N : Sig E} {Y : N.StdL Fp}
    {Sd : N.Seeds} {L t d : N.O → ℕ} (h : SndGlJ N Y Sd L t d) : Y.OK t :=
  ⟨h.fmt.enc, h.fmt.lay, h.priv, fun a => h.fmt.zk a _ (glC_code _ _ _ _ (h.code a)).2.2.2.2⟩

/-- The object at this field: the conditions. -/
structure ObjGlM (Z : LdObjZM F E) (a k msg r e mca : ℕ) : Prop where
  wfIs  : (⟨Z.R.W, Z.R.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨Z.Zw.W, Z.Zw.G.B⟩
  sndIs : Z.R.toLdObjD = Z.R.toLdObjD.std Z.Y
  /-- the code of the encoded index: within a third -/
  code  : Z.Zw.W.Cf.C₀ = rs a k msg r e mca
  ha    : a ≤ 32
  hk    : k < 2 ^ a
  hp    : msg + r ≤ k + 1
  h3    : 3 * Z.Zw.W.Cf.eM < 2 ^ a - k
  smp   : Z.Zw.W.Cf.Z.OKOn (Ood.PadInF F)
  model : Z.Zw.W.Cf.ModelOK
  /-- weights-formedness: within a third -/
  wfC   : ∀ o, GlC (Z.Zw.W.P.S.om o).C (Z.dS o) 0
  wfLt  : ∀ o, 3 * (Z.Zw.W.P.S.om o).e < Z.dS o
  wfOne : ∀ o, Z.Zw.L o = 1
  wfRest : Z.Zw.Rest0 p
  /-- the offline test's three sendings -/
  plS : Z.Y.TS.Places
  sW  : SndGl3 Z.R.W.O.toC.P.NW Z.Y.TS.YW Z.R.W.O.toC.P.SdW Z.Y.LW Z.Y.tW Z.dW
  sU  : SndGl3 Z.R.W.O.toC.P.NU Z.Y.TS.YU Z.R.W.O.toC.P.SdU Z.Y.LU Z.Y.tU Z.dU
  sO  : SndGl3 Z.R.W.O.toC.P.NO Z.Y.TS.YO Z.R.W.O.toC.P.SdO Z.Y.LO Z.Y.tO Z.dO
  /-- the link's sending -/
  rdK : Z.Y.YK.Reads Z.Y.ixK fun m => Sum.elim (Z.R.K.P.uv₀ m) (Z.R.K.P.uv₁ m)
  sK  : SndGl3 Z.R.K.P.N Z.Y.YK Z.Y.SdK Z.Y.LK Z.Y.tK Z.dN
  /-- the session's three sendings: below the Johnson radius -/
  plB : Z.Y.TB.Places
  sWB : SndGlJ Z.R.on.ol.toC.P.NW Z.Y.TB.YW Z.R.on.ol.toC.P.SdW Z.Y.LWB Z.Y.tWB Z.dWB
  sUB : SndGlJ Z.R.on.ol.toC.P.NU Z.Y.TB.YU Z.R.on.ol.toC.P.SdU Z.Y.LUB Z.Y.tUB Z.dUB
  sOB : SndGlJ Z.R.on.ol.toC.P.NO Z.Y.TB.YO Z.R.on.ol.toC.P.SdO Z.Y.LOB Z.Y.tOB Z.dOB
  /-- clauses as they stand in Z.Hyp p -/
  own : Z.R.toLdObjD.Own3
  pl  : Z.R.HypPl
  /-- the link's test and the offline test's three: within a third -/
  tK  : RunGlAt Z.R.Kc.run Z.twK Z.dK
  t₁  : RunGlAt Z.R.TP₀.D₁ Z.tw₁ Z.d₁
  t₂  : RunGlAt Z.R.TP₀.D₂ Z.tw₂ Z.d₂
  t₃  : RunGlAt Z.R.X.run Z.tw₃ Z.d₃
  /-- the session's three tests: below the Johnson radius -/
  t₁B : RunGlJAt Z.R.TB₀.D₁ Z.tw₁B Z.d₁B
  t₂B : RunGlJAt Z.R.TB₀.D₂ Z.tw₂B Z.d₂B
  t₃B : RunGlJAt Z.R.XB.run Z.tw₃B Z.d₃B

/-- The object's hypotheses on data, at this field. Limit: the statement has the premise
`Cb.BCHKS46F F`, a hypothesis; this file does not prove it. -/
def Spec.glM_hyp : Prop :=
  Cb.BCHKS46F F → ∀ (Z : LdObjZM F E) (a k msg r e mca : ℕ), ObjGlM Z a k msg r e mca → Z.Hyp p

theorem glM_hyp : Spec.glM_hyp := fun H Z a k msg r e mca h =>
  { wfIs := h.wfIs
    sndIs := h.sndIs
    wf3 := gl3_wf Z.Zw p Z.dS a k msg r e mca h.code h.ha h.hk h.hp h.h3 h.smp h.model
      h.wfC h.wfLt h.wfOne h.wfRest
    sOff :=
      { places := h.plS, okW := h.sW.ok, okU := h.sU.ok, okO := h.sO.ok
        lawsW := fun o =>
          (glC_code _ _ _ _ (h.sW.code o)).1,
            fairW := h.sW.fair,
            distW := fun o =>
                (glC_code _ _ _ _ (h.sW.code o)).2.2.2.1,
                  ltW := h.sW.lt, oneW := h.sW.one,
                  evW := fun o => (gl_code_list _ _ _ (h.sW.code o) (h.sW.lt o)).2
        lawsU := fun o =>
          (glC_code _ _ _ _ (h.sU.code o)).1,
            fairU := h.sU.fair,
            distU := fun o =>
                (glC_code _ _ _ _ (h.sU.code o)).2.2.2.1,
                  ltU := h.sU.lt, oneU := h.sU.one,
                  evU := fun o => (gl_code_list _ _ _ (h.sU.code o) (h.sU.lt o)).2
        lawsO := fun o =>
          (glC_code _ _ _ _ (h.sO.code o)).1,
            fairO := h.sO.fair,
            distO := fun o =>
                (glC_code _ _ _ _ (h.sO.code o)).2.2.2.1,
                  ltO := h.sO.lt, oneO := h.sO.one,
                  evO := fun o => (gl_code_list _ _ _ (h.sO.code o) (h.sO.lt o)).2 }
    sLink :=
      { ok := h.sK.ok, reads := h.rdK, laws := fun o => (glC_code _ _ _ _ (h.sK.code o)).1,
        fair := h.sK.fair, dist := fun o => (glC_code _ _ _ _ (h.sK.code o)).2.2.2.1,
        lt := h.sK.lt, one := h.sK.one
        ev := fun o => (gl_code_list _ _ _ (h.sK.code o) (h.sK.lt o)).2 }
    sOn :=
      { places := h.plB, okW := h.sWB.ok, okU := h.sUB.ok, okO := h.sOB.ok
        lawsW := fun o =>
          (glC_code _ _ _ _ (h.sWB.code o)).1,
            fairW := h.sWB.fair,
            distW := fun o =>
                (glC_code _ _ _ _ (h.sWB.code o)).2.2.2.1,
                  inJW := h.sWB.inJ, isLW := h.sWB.isL, evW := h.sWB.ev
        lawsU := fun o =>
          (glC_code _ _ _ _ (h.sUB.code o)).1,
            fairU := h.sUB.fair,
            distU := fun o =>
                (glC_code _ _ _ _ (h.sUB.code o)).2.2.2.1,
                  inJU := h.sUB.inJ, isLU := h.sUB.isL, evU := h.sUB.ev
        lawsO := fun o =>
          (glC_code _ _ _ _ (h.sOB.code o)).1,
            fairO := h.sOB.fair,
            distO := fun o =>
                (glC_code _ _ _ _ (h.sOB.code o)).2.2.2.1,
                  inJO := h.sOB.inJ, isLO := h.sOB.isL, evO := h.sOB.ev }
    own := h.own
    pl := h.pl
    pK := gl3_runAt _ _ _ h.tK
    p₁ := gl3_runAt _ _ _ h.t₁
    p₂ := gl3_runAt _ _ _ h.t₂
    p₃ := gl3_runAt _ _ _ h.t₃
    p₁B := glJ_runAt H _ _ _ h.t₁B
    p₂B := glJ_runAt H _ _ _ h.t₂B
    p₃B := glJ_runAt H _ _ _ h.t₃B }

end Cb.Gl
