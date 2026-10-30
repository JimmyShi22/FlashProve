-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectDataRefJ.lean: book-keeping for the hypotheses of a holographic IOP, with list
decoding up to the Johnson radius: the object with the hypotheses of `Z.HypRefJ ..`, at the
reference request, at the point that a write-up of ours (lean/CREDITS.md) takes as its
reference (but for the plan of the linear test, and for the field of a session's messages): the
offline phase and the link
within a third of the distances, all groups of a session below the Johnson radius.

`Z.HypRefJ` has no clause on a list, on a fold's bad points, on "two members of one list agree at
few seeds"; agreement is asked of codes only, in one form (`MCArows`, at a base case `MCAat`),
online only.
Its statements are implications between records of hypotheses.
Records, statements and proofs: an assembly of Cb/Obj/LdObjectDataMix.lean's pieces and
Cb/Req1/LdReqJohn.lean, towards `Z.HypRefA` of Cb/Obj/LdObjectDataRefJAny.lean. No assumed theorem
beyond the hypotheses of this file's statements.
The object's data: the head of Cb/Obj/LdObjectData.lean. The reference request and a request's end
R: the head of Cb/Obj/LdObjectDataRef.lean.
A radius e is below the Johnson radius, at length n and distance d, if n (n - d) < (n - e)^2
(`InJohnson n d e`, Cb/Gen/JohnsonList.lean).
A bound on lists says that every word has at most L codewords within the radius e (`ListAt`,
Cb/Ld/LdRel.lean; for the messages of an oracle message: `OMsg.ListLE`, Cb/Ld/LdSig.lean).
Agreement is mutual correlated agreement, as a count of exceptional coefficients (`MCAat`,
Cb/Ld/LdRel.lean; `MCArows`, Cb/Ld/LdRelRows.lean).
The object's hypotheses at the reference request (`Z.HypRefT`, Cb/Obj/LdObjectDataRefT.lean; with
the request's pads' field chosen sending by sending: `Z.HypRefA`, Cb/Obj/LdObjectDataRefJAny.lean)
speak of lists, agreement, folds' errors or list members in: `wfS` (the configuration's lists;
lists and "evades" of the messages of weights-formedness), `sndOK` (seven sendings), `own₀` (three
bounds on the bad points of folds of the index), `req` (Cb/Req1/LdReqJohn.lean's head), the seven
tests (the list of each group's complex; each tower's blocks). Here each is replaced.

Main names:
  The data are Cb/Obj/LdObjectDataMix.lean's: `Z : LdObjZM F E` (four towers within a third: no
    numbers for lists or agreement; three towers below the Johnson radius: the counts for agreement
    are data; distances); the object's data are `Z.toZ`.
  `V.HypJ p dS`: `wfS` with: the configuration within a third (`Cf.Third`); each message of
    weights-formedness within unique decoding or below the Johnson radius (`o.NearJ`,
    Cb/Req1/LdReqJohn.lean).
  `D.Own3₀`: `own₀` within a third, that is the clauses of `D.Own3` (Cb/Obj/LdObjectDataThird.lean)
    that are not the request's. The radii of the index's folds are at most `eM`, and their numbers
    are the sums for "agreement e + 1, one member" (`Cf.εThird`, Cb/Obj/LdObjectThirdTests.lean) at
    these radii; the link's first index goes by either of two regimes; online "the index decodes
    with its record", e' + eM below the distance, the number is 0.
  `Z.HypRefJ p R core first b Ls T qφ q κ V p₀ plR` (its fields, under five labels: see the
    record).
  `Spec.ldObjRefJ_hyp`: `Z.HypRefJ ..` → `Z.toZ.HypRefA p 1 ..` (not `Z.HypRefT`: that record has
    one pads' field for the whole request).

Notation: `p`: a natural number (`Spec.ldObjZ_hyp`, Cb/Obj/LdObjectData.lean, asks `CharP E p`); the
`1` in `Z.toZ.HypRefA p 1 ..`: the argument `L` of `LdObjZ.HypRefA`: a natural number (`LdCf.OK L`,
Cb/Obj/LdObjectConf.lean, says that it bounds the lists at the radius of decoding); `eM`: a natural
number (`LdCf.eM`, Cb/Obj/LdObjectConf.lean; as `LdIx.eM` of `Cf.X`, Cb/Ld/LdFoldEq.lean: the radius
of decoding, in columns); `first`: the first sending: the data (`LdSendD`, Cb/Req1/LdSegKit.lean);
`Ls`: a list of reference segments, up to the stage `b` (`LdRefL`, Cb/Req1/LdReqRef.lean); `T`: the
last segment: the data (`LdRefT`, the same file); `κ`: a number in `ℝ≥0∞` (the request's record
`req` (`LdReqRefDJ`, Cb/Req1/LdReqJohn.lean) asks, in `bFirst` to `bLast`, that its errors are below
it, in the sense of `Err.Below`, Iop/InteractiveOracleProof.lean); `V`: the standard sender of weights-formedness:
the data beside `Z.Zw` (`LdWfE.StdW`, Cb/Obj/LdObjectDataSnd.lean); `Fp`: a finite field, with
`Algebra Fp E`; `p₀`: the plan without a splitting: the data (`LdLinPl`, Cb/Ld/LdLinClosePlan.lean);
`plR`: for each row that stays open (`R.Bn`: `LdORE`, Cb/Obj/LdObjectReqEnd.lean), a set of entries.

Limits: agreement is still a premise: (1) in the batch test's three towers (`T.John` inside
`D.PreJ`: `MCArows` of each fold's three codes, `MCAat` at each base case); (2) in each closing of
the request (`Sh.par.John` inside `D.IsGrpJ`: `MCArows` of the shape's three codes). Nowhere
offline, nowhere at the link, in no sending.
Sendings offline and at the link may stand below the Johnson radius too (`o.NearJ` is asked, not
`o.Half`): lists are proved there, so no hypothesis on a list (but `OMsg.John` asks `smp : o.Z.OK`
of the sample, which `OMsg.Half` does not) is assumed by that; the write-up has them
at 2 e below the distance. There `o.Half` asks nothing of a sample: the pads may lie in the base
field (weights-formedness has a pads' field of its own: V's); the words as sent are over E all the
same, offline too (declared difference (1)).
Declared differences (not a complete list; beside those of the head of
Cb/Obj/LdObjectDataMix.lean: the plan of the linear test is the one without a splitting) (by a
reading). (1) All
oracle messages are words over E, everywhere; the pads' field is free within unique decoding and is
E beyond half the distance, so in a session at the reference radii (one pad entry of E for each
answer). In the write-up most rows of a segment are over the base field, with pads and
encoding randomness there. The reason is the type of the standard sender's data (a theorem:
Cb/Req1/LdReqJohnSubNo.lean), not the lemma on lists of words over a subfield (proved:
Cb/Req1/LdReqJohnSub.lean). (The form of mask rows, native or copied, is no difference of this
generic record: its codes are any.) Head of Cb/Req1/LdReqJohn.lean.
What stays asked and could be taken for derived: (1) zero-evaders (`Evader.OK` of each test's bridge
and of the switches' evaders; `Sample.OK` of samples beyond unique decoding; `Cf.Third`'s condition
on the configuration's sample map): conditions on public coefficients, no code, no list; (2) the
layouts' conditions (`Y.OK t`); (3) all that the heads of Cb/Obj/LdObjectDataRefT.lean,
Cb/Req1/LdReqRefStd.lean list: the model's duty, `lay`, `layT`, `layB`, formats, equations. Asked
too: `Evader.OK` of the batchings' evaders (weights-formedness': `Rest2.zOK`, Cb/Ld/LdWfEnd.lean,
and the request's: the head of Cb/Req1/LdReqJohn.lean) and `Sample.OK` of the switches' samples.
A type-class instance is declared (`LdObjZM.finWfI`): it holds no hypothesis beside the instance
argument `[i : ∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)]`, which it hands on unchanged.
This file does not say that `Z.HypRefJ` can be met: there is no instance of it in this file. It does
not say that any code has `MCArows` beyond a third.


The plan of the linear test is the one without a splitting.
No bound is evaluated.
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Obj.LdObjectDataRefJAny
import Cb.Obj.LdObjectDataMix
import Cb.Req1.LdReqJohn

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

/-- The standard sender of weights-formedness: the configuration within a third; no clause on a
list. -/
structure LdWfE.StdW.HypJ {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    {Z : LdWfE F E} [∀ b, Fintype (Z.K.wfI Z.Rl b → E)] {Fp : Type} [Field Fp] [Fintype Fp]
    [Algebra Fp E] (V : Z.StdW Fp) (p : ℕ) (dS : Z.W.P.S.O → ℕ) : Prop where
  isStd  : (⟨Z.D, Z.X⟩ : Σ D, Z.K.MaskPl D Z.Rl) =
    ⟨Z.W.P.stdD V.Y V.dat V.w0, Z.K.stdX Z.Rl V.Y V.dat V.w0 V.nAt V.RdW V.atL V.pl V.hpl⟩
  ok     : V.Y.OK Z.t
  body   : ∀ m, Z.W.P.body m = V.bd (V.Y.dataOf m)
  bdDat  : ∀ b, V.bd (V.dat b) = b
  plL    : ∀ l i, V.nAt (V.atL l i) = V.Y.entF (V.pl (some l) i)
  plB    : ∀ i, V.nAt (Z.W.P.wAt i) = V.Y.entF (V.pl none i)
  noPad  : ∀ n, V.RdW n → V.Y.NoPad n
  rest2  : Z.Rest2 p
  conf3  : Z.W.Cf.Third
  near   : ∀ a, (Z.W.P.S.om a).NearJ (dS a) (Z.L a)

/-- The three standard senders of a test: no clause on a list. -/
structure LdLinP.Std.NearS {F E ι κ J Y : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] {P : LdLinP E ι κ J Y} (T : P.Std F) (LW : P.NW.O → ℕ) (LU : P.NU.O → ℕ)
    (LO : P.NO.O → ℕ) (tW : P.NW.O → ℕ) (tU : P.NU.O → ℕ) (tO : P.NO.O → ℕ) (dW : P.NW.O → ℕ)
    (dU : P.NU.O → ℕ) (dO : P.NO.O → ℕ) : Prop where
  places : T.Places
  okW   : T.YW.OK tW
  okU   : T.YU.OK tU
  okO   : T.YO.OK tO
  fairW : P.SdW.Fair
  fairU : P.SdU.Fair
  fairO : P.SdO.Fair
  nearW : ∀ a, (P.NW.om a).NearJ (dW a) (LW a)
  nearU : ∀ a, (P.NU.om a).NearJ (dU a) (LU a)
  nearO : ∀ a, (P.NO.om a).NearJ (dO a) (LO a)

/-- The standard sender of the link: no clause on a list. -/
structure LdLkP.StdNear {F E ι κ J Λ : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] (P : LdLkP E ι κ J Λ) (Sd : P.N.Seeds) (L t : P.N.O → ℕ) (Y : P.N.StdL F)
    (ix : ∀ a, Y.Dt a → Option (κ ⊕ κ)) (dN : P.N.O → ℕ) : Prop where
  ok    : Y.OK t
  reads : Y.Reads ix fun m => Sum.elim (P.uv₀ m) (P.uv₁ m)
  fair  : Sd.Fair
  near  : ∀ a, (P.N.om a).NearJ (dN a) (L a)

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The clauses of `Own3` that are not the request's. -/
structure LdObjD.Own3₀ (T : LdObjD F E) : Prop where
  lay    : T.LayOK
  q₀e    : T.q₀ ∅
  /-- the offline test's fold -/
  e'le   : T.W.O.e' ≤ T.W.Cf.eM
  εfIs   : T.εf = T.W.Cf.εThird T.W.O.e'
  pyInj  : Function.Injective T.W.O.py
  /-- the link's two folds: the first index by either regime, the further one by the first -/
  par    : T.Par3
  on1Is  : T.on1K = T.K.free
  e₁le   : T.K.e₁ ≤ T.W.Cf.eM
  ε₁Is   : T.ε₁ = T.W.Cf.εThird T.K.e₁
  plInj  : Function.Injective T.K.pl
  bearK  : ∀ a, T.Kc.t ≤ T.Sl.t a
  /-- the online test's fold: the index decodes with its record -/
  onBIs  : T.onB = T.on.ol.onDec
  εfBIs  : T.εfB = 0
  e'far  : T.on.ol.e' + T.W.Cf.eM < T.W.Cf.C₀.d
  pyInjB : Function.Injective T.on.ol.py
  monoB  : ∀ U V, V ⊆ U → T.qaB U → T.qaB V

/-- finiteness of the tables of weights-formedness, given at `Z.Zw`, read at `Z.toZ.Zw`: the same
type by definition -/
instance LdObjZM.finWfI (Z : LdObjZM F E) [i : ∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] :
    ∀ b, Fintype (Z.toZ.Zw.K.wfI Z.toZ.Zw.Rl b → E) := i

/-- `Z.toZ`'s hypotheses at the reference request: offline phase and link within a third, the
session below the Johnson radius (the exceptions: "Limits" and the row of `D.Own3₀` in the head). -/
structure LdObjZM.HypRefJ (Z : LdObjZM F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (p : ℕ)
    {Kc : Type} (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
    (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
    (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
    (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
    (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) {Fp : Type} [Field Fp] [Fintype Fp] [Algebra Fp E]
    (V : Z.Zw.StdW Fp) (p₀ : LdLinPl R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop) : Prop where
  /-- which terms are in `Z.R` -/
  wfIs   : (⟨Z.R.W, Z.R.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨Z.Zw.W, Z.Zw.G.B⟩
  sndIs  : Z.R.toLdObjD = Z.R.toLdObjD.std Z.Y
  reqIs  : Z.R.toLdObjD.pack =
    ldRefPack R core first first.tgt (.nil first.tgt) (LdProg.all_nilK _ _) b Ls T qφ q
  onIs   : Z.R.onPack = ldRefOn R p₀
  /-- weights-formedness, the seven sendings, the index's folds -/
  wfJ    : V.HypJ p Z.dS
  sOff   : Z.Y.TS.NearS Z.Y.LW Z.Y.LU Z.Y.LO Z.Y.tW Z.Y.tU Z.Y.tO Z.dW Z.dU Z.dO
  sLink  : Z.R.K.P.StdNear Z.Y.SdK Z.Y.LK Z.Y.tK Z.Y.YK Z.Y.ixK Z.dN
  sOn    : Z.Y.TB.NearS Z.Y.LWB Z.Y.LUB Z.Y.LOB Z.Y.tWB Z.Y.tUB Z.Y.tOB Z.dWB Z.dUB Z.dOB
  own₀   : Z.R.toLdObjD.Own3₀
  /-- the request -/
  req    : LdReqRefDJ p R core first b Ls T qφ q κ
  places : R.PlacesOK p₀ plR
  pl₁    : Z.R.HypPl₁
  /-- the link's test and the offline test's three: within a third -/
  pK     : Z.R.Kc.run.Pre3 Z.twK Z.dK
  p₁     : Z.R.TP₀.D₁.Pre3 Z.tw₁ Z.d₁
  p₂     : Z.R.TP₀.D₂.Pre3 Z.tw₂ Z.d₂
  p₃     : Z.R.X.run.Pre3 Z.tw₃ Z.d₃
  /-- the batch test's three: below the Johnson radius -/
  p₁B    : Z.R.TB₀.D₁.PreJ Z.tw₁B Z.d₁B
  p₂B    : Z.R.TB₀.D₂.PreJ Z.tw₂B Z.d₂B
  p₃B    : Z.R.XB.run.PreJ Z.tw₃B Z.d₃B

end

namespace Spec

def ldObjRefJ_wf : Prop :=
  ∀ (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
      [Fintype Fp] [Algebra Fp E] (Z : LdWfE F E) [∀ b, Fintype (Z.K.wfI Z.Rl b → E)]
      (V : Z.StdW Fp) (p : ℕ) (dS : Z.W.P.S.O → ℕ),
    V.HypJ p dS → V.Hyp p 1

def ldObjRefJ_lin : Prop :=
  ∀ (F E ι κ J Y : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
      (P : LdLinP E ι κ J Y) (T : P.Std F) (LW : P.NW.O → ℕ) (LU : P.NU.O → ℕ)
      (LO : P.NO.O → ℕ) (tW : P.NW.O → ℕ) (tU : P.NU.O → ℕ) (tO : P.NO.O → ℕ) (dW : P.NW.O → ℕ)
      (dU : P.NU.O → ℕ) (dO : P.NO.O → ℕ),
    T.NearS LW LU LO tW tU tO dW dU dO → T.Hyp LW LU LO tW tU tO

def ldObjRefJ_link : Prop :=
  ∀ (F E ι κ J Λ : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
      (P : LdLkP E ι κ J Λ) (Sd : P.N.Seeds) (L t : P.N.O → ℕ) (Y : P.N.StdL F)
      (ix : ∀ a, Y.Dt a → Option (κ ⊕ κ)) (dN : P.N.O → ℕ),
    P.StdNear Sd L t Y ix dN → P.StdHyp Sd L t Y ix

def ldObjRefJ_own : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (T : LdObjD F E),
    T.Own3₀ → T.W.Cf.Third → T.HypOwn₀

/-- States: the record without lists (`Z.HypRefJ ..`) gives `Z.toZ.HypRefA p 1 ..` (the request's
pads' field chosen sending by sending). -/
def ldObjRefJ_hyp : Prop :=
  ∀ (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
      [Fintype Fp] [Algebra Fp E] (Kc : Type) (p : ℕ) (Z : LdObjZM F E)
      [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (R : LdORE F E Kc)
      (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (V : Z.Zw.StdW Fp)
      (p₀ : LdLinPl R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop),
    Z.HypRefJ p R core first b Ls T qφ q κ V p₀ plR →
    Z.toZ.HypRefA p 1 R core first b Ls T qφ q κ V p₀ plR

end Spec

theorem ldObjRefJ_wf : Spec.ldObjRefJ_wf := fun F E _ _ _ _ _ _ _ _ _ Z _ _ _ _ h =>
  { isStd := h.isStd, ok := h.ok, body := h.body, bdDat := h.bdDat, plL := h.plL, plB := h.plB,
    noPad := h.noPad, rest2 := h.rest2
    laws := fun a => (ldReqJohn_msg E _ _ _ (h.near a)).1
    conf := ldT3_conf F E Z.W.Cf h.conf3
    list := fun a => (ldReqJohn_msg E _ _ _ (h.near a)).2.1
    evades := fun a => (ldReqJohn_msg E _ _ _ (h.near a)).2.2 }

theorem ldObjRefJ_lin : Spec.ldObjRefJ_lin := fun _ E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h =>
  { places := h.places, okW := h.okW, okU := h.okU, okO := h.okO
    lawsW := fun a =>
      (ldReqJohn_msg E _ _ _ (h.nearW a)).1,
        fairW := h.fairW,
        listW := fun a =>
            (ldReqJohn_msg E _ _ _ (h.nearW a)).2.1,
              evW := fun a => (ldReqJohn_msg E _ _ _ (h.nearW a)).2.2
    lawsU := fun a =>
      (ldReqJohn_msg E _ _ _ (h.nearU a)).1,
        fairU := h.fairU,
        listU := fun a =>
            (ldReqJohn_msg E _ _ _ (h.nearU a)).2.1,
              evU := fun a => (ldReqJohn_msg E _ _ _ (h.nearU a)).2.2
    lawsO := fun a =>
      (ldReqJohn_msg E _ _ _ (h.nearO a)).1,
        fairO := h.fairO,
        listO := fun a =>
            (ldReqJohn_msg E _ _ _ (h.nearO a)).2.1,
              evO := fun a => (ldReqJohn_msg E _ _ _ (h.nearO a)).2.2 }

theorem ldObjRefJ_link : Spec.ldObjRefJ_link := fun _ E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h =>
  ⟨h.ok, h.reads, fun a => (ldReqJohn_msg E _ _ _ (h.near a)).1, h.fair,
    fun a => (ldReqJohn_msg E _ _ _ (h.near a)).2.1,
    fun a => (ldReqJohn_msg E _ _ _ (h.near a)).2.2⟩

theorem ldObjRefJ_own : Spec.ldObjRefJ_own := by
  intro F E _ _ _ _ _ T h hC
  have hl := ldCm_list_unique F E T.W.Cf hC.dist (by have := hC.lt; omega)
  have hlt : T.W.Cf.eM < T.W.Cf.C₀.d := by have := hC.lt; omega
  exact
    { lay := h.lay, q₀e := h.q₀e
      fold := by
        rw [h.εfIs]
        exact ldLin_foldErr T.W.O.toC.P T.W.Cf.C₀.d _ 1 (ldCm_dist F E T.W.Cf hC.dist) hlt h.e'le
          (ldCm_mca_third F E T.W.Cf T.W.O.e' hC.dist (by have := hC.lt; have := h.e'le; omega))
          (ldCm_list_le F E T.W.Cf 1 T.W.O.e' hl h.e'le)
      pyInj := h.pyInj
      fitsK := by
        rcases h.par with ⟨e0, -, -⟩ | ⟨e0, -, -⟩
        · rw [e0, h.on1Is]
          exact ⟨fun _ _ _ hh => hh, fun _ _ hh => hh⟩
        · rw [e0, h.on1Is]
          exact ⟨fun _ _ hd _ => hd, fun _ _ hh => hh⟩
      foldK := by
        rcases h.par with ⟨e0, hle, hε⟩ | ⟨e0, hfar, hε⟩
        · rw [e0, h.on1Is, hε, h.ε₁Is]
          exact ldLk_foldErr_rec T.K.P T.W.Cf.C₀.d _ 1 _ 1 (ldCm_dist F E T.W.Cf hC.dist) hlt hle
            h.e₁le (ldCm_mca_third F E T.W.Cf T.K.e₀ hC.dist (by have := hC.lt; omega))
            (ldCm_list_le F E T.W.Cf 1 T.K.e₀ hl hle)
            (ldCm_mca_third F E T.W.Cf T.K.e₁ hC.dist (by have := hC.lt; have := h.e₁le; omega))
              (ldCm_list_le F E T.W.Cf 1 T.K.e₁ hl h.e₁le)
        · rw [e0, h.on1Is, hε, h.ε₁Is]
          exact ldLk_foldErr T.K.P T.W.Cf.C₀.d _ 1 (ldCm_dist F E T.W.Cf hC.dist) hfar h.e₁le
            (ldCm_mca_third F E T.W.Cf T.K.e₁ hC.dist (by have := hC.lt; have := h.e₁le; omega))
            (ldCm_list_le F E T.W.Cf 1 T.K.e₁ hl h.e₁le)
      plInj := h.plInj, bearK := h.bearK
      fitsB := by rw [h.onBIs]; exact (ldOB_fits F E T.on.ol).1
      foldB := by rw [h.onBIs, h.εfBIs]; exact ldOB_foldErr F E T.on.ol hC.dist h.e'far
      pyInjB := h.pyInjB, monoB := h.monoB }

theorem ldObjRefJ_hyp : Spec.ldObjRefJ_hyp := by
  intro F E Fp _ _ _ _ _ _ _ _ Kc p Z _ R core first b Ls T qφ q κ V p₀ plR h
  have hC : Z.R.W.Cf.Third := by
    have key : ∀ x : Σ W : LdOWf F E, W.P.Blk, x = ⟨Z.Zw.W, Z.Zw.G.B⟩ → x.1.Cf.Third := by
      rintro _ rfl
      exact h.wfJ.conf3
    exact key ⟨Z.R.W, Z.R.Bw⟩ h.wfIs
  exact
    { wfIs := h.wfIs
      sndIs := h.sndIs
      reqIs := h.reqIs
      onIs := h.onIs
      wfS := ldObjRefJ_wf F E Fp Z.Zw V p Z.dS h.wfJ
      sndOK := ⟨ldObjRefJ_lin _ E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.sOff,
        ldObjRefJ_link _ E _ _ _ _ _ _ _ _ _ _ _ h.sLink,
        ldObjRefJ_lin _ E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.sOn⟩
      own₀ := ldObjRefJ_own F E Z.R.toLdObjD h.own₀ hC
      req := ldReqRefJ F E Kc p R core first b Ls T qφ q κ h.req
      places := h.places
      pl₁ := h.pl₁
      pK := h.pK.pre
      p₁ := h.p₁.pre
      p₂ := h.p₂.pre
      p₃ := h.p₃.pre
      p₁B := (ldTowGJ_run E _ _ Z.tw₁B Z.d₁B h.p₁B).1
      p₂B := (ldTowGJ_run E _ _ Z.tw₂B Z.d₂B h.p₂B).1
      p₃B := (ldTowGJ_run E _ _ Z.tw₃B Z.d₃B h.p₃B).1 }

end Cb
