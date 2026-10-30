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
Cb/Gen/CodeListRS.lean.) Cb/Obj/LdObjectDataJohn.lean: book-keeping for the hypotheses of a
holographic IOP, with list decoding up to the Johnson radius: the object with the hypotheses of
`Z.Hyp p`, among them properties of the request's program and of the sender `Zw.D` of
weights-formedness, the index within a third of its distance, all other groups below the Johnson
radius: no hypothesis on a list is left, but inside the request's program and in the clauses
"evades"; agreement is asked of the codes in the seven towers.

Its main statement is an implication between two records of hypotheses: `Cb.Spec.ldObjZJ_hyp`:
`Z.Hyp p` ⇒ `Z.toZ.Hyp p 1`.
Definitions, that statement, two lemmas on the senders' records, and proofs: an assembly. A step
towards `LdObjZ.Hyp p L` of Cb/Obj/LdObjectData.lean, whose head says what the object and the
request's program are.
A bound on lists says that every word has at most L codewords within the radius e (`ListAt`,
Cb/Ld/LdRel.lean; for the messages of an oracle message: `OMsg.ListLE`, Cb/Ld/LdSig.lean).
Agreement is mutual correlated agreement, as a count of exceptional coefficients (`MCAat`,
Cb/Ld/LdRel.lean; `MCArows`, Cb/Ld/LdRelRows.lean).
The analogue of Cb/Obj/LdObjectDataThird.lean at another point of the parameter space. Lists need no
hypothesis below the Johnson radius (`InJohnson`, Cb/Gen/JohnsonList.lean): every code with laws and
a distance has lists of at most `listMax |P| d e` members (Cb/Ld/LdRelJohnson.lean, proved).
Agreement does: it stands as counts in the towers' records (Cb/Obj/LdObjectTowerJohn.lean: `T.John`:
`MCArows`, `MCAat`), asked, not proved.

Main names:
  `LdObjZJ F E`: data only: `R : LdObjR`; `Zw`; `Y`; seven towers without numbers for lists
    (`D.TowJ`, an `LdTowGJ`: the counts for agreement are data); distances.
  `T.JohnS ..`, `P.StdJohn ..`: what the standard senders ask, without lists: a distance, "e below
    the Johnson radius", "the bound is listMax"; "evades" stays (`evW`, `evU`, `evO`; `ev`).
  `Z.Hyp p`: `wfIs`, `sndIs` (two equations that say which terms are in `Z.R`: hypotheses here); the
    configuration within a third (`conf3`); `Zw.John p dS` (Cb/Obj/LdObjectJohnTests.lean); the
    senders' three records; `D.Own3` (Cb/Obj/LdObjectDataThird.lean: the index's folds within a
    third, the link's first index by either case of `D.Par3`; online "the index decodes with its
    record"; the request; its last base joint a standard one); `R.HypPl`; `D.PreJ T d` for each of
    the seven tests.






Notation: `p`: a natural number (`Spec.ldObjZ_hyp`, Cb/Obj/LdObjectData.lean, asks `CharP E p`); the
`1` in `Z.toZ.Hyp p 1`: the argument `L` of `LdObjZ.Hyp`: a natural number (`LdCf.OK L`,
Cb/Obj/LdObjectConf.lean, says that it bounds the lists at the radius of decoding).

Limits: what is left that speaks of lists is only what stands inside `r.Hyp`, and the clauses `evW`,
`evU`, `evO` of `JohnS`, `ev` of `StdJohn` and `ev` of `Zw.John` (`OMsg.Evades`, Cb/Ld/LdSig.lean:
two different messages of one list have the same answers at no more than `o.Z.err` seeds (`o` the
oracle message, `o.Z` its sample map)). What is left that speaks of agreement: `T.John` of the seven
towers (the field `tow` of `D.PreJ T d`), and `r.Hyp`.
Six clauses on the sender `Zw.D` of weights-formedness are not on data: it is a free value with laws
(Cb/Ld/LdWfEnd.lean: `Rest0`, `Rest1`).
That `Z.Hyp p` can be met is not shown in this file. No instance that meets the hypotheses of
`ldObjZJ_hyp` is part of this library; as far as the library shows, this theorem may hold of
nothing.
This file does not say the two things that follow. That the counts for agreement hold for any
code: that is the part of the statement on codes (stated in its source with an outline of a proof;
not proved here). (The statement on codes: `Cb.BCHKS46F`, Cb/Gen/CodeListRSF.lean.) (The source of
the statement on codes: the head of Cb/Gen/CodeListRS.lean.) The index beyond a third.


Online the request is not built: its program r is a parameter, and its "conditions" are the security
properties (found by reading). Its moves: `LdMv`, Cb/Req1/LdSeg.lean; what each asks: `LdMv.Hyp`. At
a move `sub a b c`, `r.Hyp` is `c.AllB` for any chain c: completeness and round-by-round knowledge
soundness, link by link, are assumed of a parameter. At a move `fold D l` it asks of any link l the
whole bundle `GoodT`, honest-verifier zero knowledge included: that l is the
proximity test that closes each segment. A move `step` asks `StepT` (its clauses `acc`, `know`: the
arithmetization). For every first sending d and every chain c to the last stage there is a request
with r.Hyp ↔ d.Hyp ∧ c.AllB.
So "an accepted proof implies `Rno`" (the model's relaxed relation, Hiop/RecConf.lean) is, online,
assumed at the level of the oracle reduction: that the claim on the instance x is about the
extracted index is not derived from data.



The cure in Lean is the reference request as a term (Cb/Req1/LdReqRef*.lean,
Cb/Obj/LdObjectDataRef.lean). Among what is still a property of terms
there: each closing's fold link, senders, entry and exit steps, the model's side, where the masks
come from. No theorem of this library states that the hypotheses of `ldReqRefFinal`
(Cb/Req1/LdReqRefFinal.lean) can be met together.


Declared: this protocol's technical report (lean/CREDITS.md) has another plan for the closing of the
test for linear constraints: one splitting, in the shared part. That plan is not the one under this
file (here: the plan without a splitting). The object at that plan stands beside:
Cb/Obj/LdObjectPlanPaper.lean (`LdObjPp`; `ldObjPp_hyp`); the records on data (`LdObjR`, `LdObjZ`
and what stands on them) are
at the plan without a splitting; among those at the plan with a splitting: `LdObjRp`, `LdObjZp` and
what stands on them (Cb/Obj/LdObjectPpRows.lean, Cb/Obj/LdObjectPpData.lean).
Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectDataThird
import Cb.Obj.LdObjectTowerJohn
import Cb.Obj.LdObjectJohnTestsProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- What the three standard senders of a test ask, below the Johnson radius. -/
structure LdLinP.Std.JohnS {F E ι κ J Y : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] {P : LdLinP E ι κ J Y} (T : P.Std F) (LW : P.NW.O → ℕ) (LU : P.NU.O → ℕ)
    (LO : P.NO.O → ℕ) (tW : P.NW.O → ℕ) (tU : P.NU.O → ℕ) (tO : P.NO.O → ℕ) (dW : P.NW.O → ℕ)
    (dU : P.NU.O → ℕ) (dO : P.NO.O → ℕ) : Prop where
  places : T.Places
  okW   : T.YW.OK tW
  okU   : T.YU.OK tU
  okO   : T.YO.OK tO
  lawsW : ∀ a, (P.NW.om a).C.Laws
  fairW : P.SdW.Fair
  distW : ∀ a, (P.NW.om a).C.Dist (dW a)
  inJW  : ∀ a, InJohnson (Fintype.card (P.NW.om a).P) (dW a) (P.NW.om a).e
  isLW  : ∀ a, LW a = listMax (Fintype.card (P.NW.om a).P) (dW a) (P.NW.om a).e
  evW   : ∀ a, (P.NW.om a).Evades
  lawsU : ∀ a, (P.NU.om a).C.Laws
  fairU : P.SdU.Fair
  distU : ∀ a, (P.NU.om a).C.Dist (dU a)
  inJU  : ∀ a, InJohnson (Fintype.card (P.NU.om a).P) (dU a) (P.NU.om a).e
  isLU  : ∀ a, LU a = listMax (Fintype.card (P.NU.om a).P) (dU a) (P.NU.om a).e
  evU   : ∀ a, (P.NU.om a).Evades
  lawsO : ∀ a, (P.NO.om a).C.Laws
  fairO : P.SdO.Fair
  distO : ∀ a, (P.NO.om a).C.Dist (dO a)
  inJO  : ∀ a, InJohnson (Fintype.card (P.NO.om a).P) (dO a) (P.NO.om a).e
  isLO  : ∀ a, LO a = listMax (Fintype.card (P.NO.om a).P) (dO a) (P.NO.om a).e
  evO   : ∀ a, (P.NO.om a).Evades

theorem LdLinP.Std.JohnS.hyp {F E ι κ J Y : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] {P : LdLinP E ι κ J Y} {T : P.Std F} {LW : P.NW.O → ℕ} {LU : P.NU.O → ℕ}
    {LO : P.NO.O → ℕ} {tW : P.NW.O → ℕ} {tU : P.NU.O → ℕ} {tO : P.NO.O → ℕ} {dW : P.NW.O → ℕ}
    {dU : P.NU.O → ℕ} {dO : P.NO.O → ℕ} (h : T.JohnS LW LU LO tW tU tO dW dU dO) :
    T.Hyp LW LU LO tW tU tO :=
  { places := h.places, okW := h.okW, okU := h.okU, okO := h.okO
    lawsW := h.lawsW, fairW := h.fairW,
      listW := fun a => by
          rw [h.isLW a]; exact ldJn_list E _ (dW a) (h.lawsW a) (h.distW a) (h.inJW a), evW := h.evW
    lawsU := h.lawsU, fairU := h.fairU,
      listU := fun a => by
          rw [h.isLU a]; exact ldJn_list E _ (dU a) (h.lawsU a) (h.distU a) (h.inJU a), evU := h.evU
    lawsO := h.lawsO, fairO := h.fairO, listO := fun a => by rw [h.isLO a]; exact ldJn_list E _ (dO a) (h.lawsO a) (h.distO a) (h.inJO a), evO := h.evO }

/-- What the standard sender of the link asks, below the Johnson radius. -/
structure LdLkP.StdJohn {F E ι κ J Λ : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] (P : LdLkP E ι κ J Λ) (Sd : P.N.Seeds) (L t : P.N.O → ℕ) (Y : P.N.StdL F)
    (ix : ∀ a, Y.Dt a → Option (κ ⊕ κ)) (dN : P.N.O → ℕ) : Prop where
  ok    : Y.OK t
  reads : Y.Reads ix fun m => Sum.elim (P.uv₀ m) (P.uv₁ m)
  laws  : ∀ a, (P.N.om a).C.Laws
  fair  : Sd.Fair
  dist  : ∀ a, (P.N.om a).C.Dist (dN a)
  inJ   : ∀ a, InJohnson (Fintype.card (P.N.om a).P) (dN a) (P.N.om a).e
  isL   : ∀ a, L a = listMax (Fintype.card (P.N.om a).P) (dN a) (P.N.om a).e
  ev    : ∀ a, (P.N.om a).Evades

theorem LdLkP.StdJohn.hyp {F E ι κ J Λ : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] {P : LdLkP E ι κ J Λ} {Sd : P.N.Seeds} {L t : P.N.O → ℕ} {Y : P.N.StdL F}
    {ix : ∀ a, Y.Dt a → Option (κ ⊕ κ)} {dN : P.N.O → ℕ} (h : P.StdJohn Sd L t Y ix dN) :
    P.StdHyp Sd L t Y ix :=
  ⟨h.ok, h.reads, h.laws, h.fair,
    fun a => by rw [h.isL a]; exact ldJn_list E _ (dN a) (h.laws a) (h.dist a) (h.inJ a), h.ev⟩

/-- The object below the Johnson radius: the data. -/
structure LdObjZJ (F E : Type) [Field F] [Field E] [Fintype F] [Fintype E] [Algebra F E] where
  R    : LdObjR F E
  Zw   : LdWfE F E
  Y    : R.toLdObjD.StdS
  twK  : R.Kc.run.TowJ
  tw₁  : R.TP₀.D₁.TowJ
  tw₂  : R.TP₀.D₂.TowJ
  tw₃  : R.X.run.TowJ
  tw₁B : R.TB₀.D₁.TowJ
  tw₂B : R.TB₀.D₂.TowJ
  tw₃B : R.XB.run.TowJ
  /-- distances -/
  dS   : Zw.W.P.S.O → ℕ
  dK   : ℕ
  d₁   : ℕ
  d₂   : ℕ
  d₃   : ℕ
  d₁B  : ℕ
  d₂B  : ℕ
  d₃B  : ℕ
  dW   : R.W.O.toC.P.NW.O → ℕ
  dU   : R.W.O.toC.P.NU.O → ℕ
  dO   : R.W.O.toC.P.NO.O → ℕ
  dN   : R.K.P.N.O → ℕ
  dWB  : R.on.ol.toC.P.NW.O → ℕ
  dUB  : R.on.ol.toC.P.NU.O → ℕ
  dOB  : R.on.ol.toC.P.NO.O → ℕ

namespace LdObjZJ
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (Z : LdObjZJ F E)

def toZ : LdObjZ F E :=
  { R := Z.R, Zw := Z.Zw, Y := Z.Y, twK := Z.R.Kc.run.upJ Z.twK, tw₁ := Z.R.TP₀.D₁.upJ Z.tw₁,
    tw₂ := Z.R.TP₀.D₂.upJ Z.tw₂, tw₃ := Z.R.X.run.upJ Z.tw₃
    tw₁B := Z.R.TB₀.D₁.upJ Z.tw₁B, tw₂B := Z.R.TB₀.D₂.upJ Z.tw₂B, tw₃B := Z.R.XB.run.upJ Z.tw₃B }

structure Hyp (p : ℕ) : Prop where
  wfIs  : (⟨Z.R.W, Z.R.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨Z.Zw.W, Z.Zw.G.B⟩
  sndIs : Z.R.toLdObjD = Z.R.toLdObjD.std Z.Y
  conf3 : Z.R.W.Cf.Third
  wfJ   : Z.Zw.John p Z.dS
  sOff  : Z.Y.TS.JohnS Z.Y.LW Z.Y.LU Z.Y.LO Z.Y.tW Z.Y.tU Z.Y.tO Z.dW Z.dU Z.dO
  sLink : Z.R.K.P.StdJohn Z.Y.SdK Z.Y.LK Z.Y.tK Z.Y.YK Z.Y.ixK Z.dN
  sOn   : Z.Y.TB.JohnS Z.Y.LWB Z.Y.LUB Z.Y.LOB Z.Y.tWB Z.Y.tUB Z.Y.tOB Z.dWB Z.dUB Z.dOB
  own   : Z.R.toLdObjD.Own3
  pl    : Z.R.HypPl
  pK    : Z.R.Kc.run.PreJ Z.twK Z.dK
  p₁    : Z.R.TP₀.D₁.PreJ Z.tw₁ Z.d₁
  p₂    : Z.R.TP₀.D₂.PreJ Z.tw₂ Z.d₂
  p₃    : Z.R.X.run.PreJ Z.tw₃ Z.d₃
  p₁B   : Z.R.TB₀.D₁.PreJ Z.tw₁B Z.d₁B
  p₂B   : Z.R.TB₀.D₂.PreJ Z.tw₂B Z.d₂B
  p₃B   : Z.R.XB.run.PreJ Z.tw₃B Z.d₃B

end LdObjZJ

def Spec.ldObjZJ_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Prop :=
  ∀ (Z : LdObjZJ F E) (p : ℕ), Z.Hyp p → Z.toZ.Hyp p 1

theorem ldObjZJ_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldObjZJ_hyp F E := fun Z p h =>
  { wfIs := h.wfIs
    sndIs := h.sndIs
    wfOK := ldJn_wf F E Z.Zw p Z.dS h.wfJ
    sndOK := ⟨h.sOff.hyp, h.sLink.hyp, h.sOn.hyp⟩
    own := h.own.own h.conf3
    pl := h.pl
    pK := (ldTowGJ_run E _ _ Z.twK Z.dK h.pK).1
    p₁ := (ldTowGJ_run E _ _ Z.tw₁ Z.d₁ h.p₁).1
    p₂ := (ldTowGJ_run E _ _ Z.tw₂ Z.d₂ h.p₂).1
    p₃ := (ldTowGJ_run E _ _ Z.tw₃ Z.d₃ h.p₃).1
    p₁B := (ldTowGJ_run E _ _ Z.tw₁B Z.d₁B h.p₁B).1
    p₂B := (ldTowGJ_run E _ _ Z.tw₂B Z.d₂B h.p₂B).1
    p₃B := (ldTowGJ_run E _ _ Z.tw₃B Z.d₃B h.p₃B).1 }

end Cb
