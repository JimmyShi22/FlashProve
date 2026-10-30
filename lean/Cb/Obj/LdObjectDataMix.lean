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
Cb/Gen/CodeListRS.lean.) Cb/Obj/LdObjectDataMix.lean: book-keeping for the hypotheses of a
holographic IOP, with list decoding up to the Johnson radius online: the object with the hypotheses
of `Z.Hyp p` (among them properties of the request's program and of the sender `Zw.D` of
weights-formedness), at the point that a write-up of ours (lean/CREDITS.md) takes as its
reference (but for the plan of the linear test): the offline phase and the link within a third of
the distances,
only the groups of a session below the Johnson radius.

Its main statement is an implication between two records of hypotheses: `Cb.Spec.ldObjZM_hyp`:
`Z.Hyp p` ⇒ `Z.toZ.Hyp p 1`.
Definitions, that statement and its proof: an assembly of Cb/Obj/LdObjectDataThird.lean (offline
half) and Cb/Obj/LdObjectDataJohn.lean (online half). A step towards `LdObjZ.Hyp p L` of
Cb/Obj/LdObjectData.lean, whose head says what the object and the request's program are; no top
theorem of its own.
A radius e is within a third of a distance d if 3 e < d (`LdCf.Third.lt`,
Cb/Obj/LdObjectThirdTests.lean).
A radius e is below the Johnson radius, at length n and distance d, if n (n - d) < (n - e)^2
(`InJohnson n d e`, Cb/Gen/JohnsonList.lean).

Main names:
  `LdObjZM F E`: data only, but for the proofs inside its fields' types (among them `LdObjD.ne`,
    `LdCf.hp`, `LdLinPl.hU` .., `LdLinPlT.hc₁`, `hc₂`, `LdLkP.Cl.all`): `R : LdObjR`; `Zw`; `Y`;
    four towers within a third (the link's; the offline test's three: no numbers for lists or
    agreement), three towers below the Johnson radius (the batch test's: the counts for agreement
    are data); distances.
  `Z.Hyp p`: `wfIs`, `sndIs` (two equations that say which terms are in `Z.R`: hypotheses here);
    offline phase and link, within a third: `Zw.Third p dS`; the offline test's and the link's
      standard senders without lists (`Third3`, `StdThird`: these ask 2 e < d); `D.Pre3 T d` for the
      link's test and the offline test's three: nothing on lists or agreement is asked here, but
      "evades" of the senders' messages (`evW`, `evU`, `evO`; `StdThird.ev`);
    the session, below the Johnson radius: the batch test's standard senders (`JohnS`: a distance,
      "e below the Johnson radius", "the bound is listMax", "evades"); `D.PreJ T d` for its three
      tests: no list is asked; agreement is, of the codes in these three towers (`T.John`, the field
      `tow` of `D.PreJ T d`);
    `D.Own3` (the index's folds within a third, the link's first index by either case of `D.Par3`;
      online "the index decodes with its record"; the request; its last base joint a standard one);
      `R.HypPl`.

Notation: `p`: a natural number (`Spec.ldObjZ_hyp`, Cb/Obj/LdObjectData.lean, asks `CharP E p`); the
`1` in `Z.toZ.Hyp p 1`: the argument `L` of `LdObjZ.Hyp`: a natural number (`LdCf.OK L`,
Cb/Obj/LdObjectConf.lean, says that it bounds the lists at the radius of decoding); `eM`: a natural
number (`LdIx.eM`, Cb/Ld/LdFoldEq.lean: the radius of decoding, in columns); `e₀`: a natural number
(the radius at the link's fold of the first index, the parent's: `Z.R.K.e₀`).

Limits: so the statement on codes (`Cb.BCHKS46F`, Cb/Gen/CodeListRSF.lean) is needed for
the online phase alone: the three towers of the batch test, and what stands inside `r.Hyp` (a
request's own closings: the request's program is a parameter here).
"Evades" is `OMsg.Evades` (Cb/Ld/LdSig.lean): two different messages of one list have the same
answers at no more than `o.Z.err` seeds (`o` the oracle message, `o.Z` its sample map).
Six clauses on the sender `Zw.D` of weights-formedness are not on data: it is a free value with laws
(Cb/Ld/LdWfEnd.lean: `Rest0`, `Rest1`).
That `Z.Hyp p` can be met is not shown in this file. No instance that meets the hypotheses of
`ldObjZM_hyp` is part of this library; as far as the library shows, this theorem may hold of
nothing.
This file does not say that the counts for agreement hold for any code
(the part of the statement on codes: stated in its source with an outline of a proof; not proved
here).
(The source of the statement on codes: the head of Cb/Gen/CodeListRS.lean.)


Online the request is not built: its program r is a parameter, and its "conditions" are the security
properties (found by reading). Its moves: `LdMv`, Cb/Req1/LdSeg.lean; what each asks: `LdMv.Hyp`. At
a move `sub a b c`, `r.Hyp` is `c.AllB` for any chain c: completeness and round-by-round knowledge
soundness, link by link, are assumed of a parameter. At a move `fold D l` it asks of any link l the
whole bundle `GoodT`, honest-verifier zero knowledge included: that l is the proximity test that
closes each segment. A move `step` asks `StepT` (its clauses `acc`, `know`: the arithmetization).
For every first sending d and every chain c to the last stage there is a request with r.Hyp ↔ d.Hyp
∧ c.AllB. So "an accepted proof implies `Rno`" (the model's relaxed relation, Hiop/RecConf.lean) is,
online, assumed at the level of the oracle reduction: that the claim on the instance x is about the
extracted index is not derived from data.



In Lean the reference request is a term (Cb/Req1/LdReqRef*.lean,
Cb/Obj/LdObjectDataRef.lean). Among what is asked as a property of terms
there: each closing's fold link, senders, entry and exit steps, the model's side, where the masks
come from. No theorem of this library states that the hypotheses of `ldReqRefFinal`
(Cb/Req1/LdReqRefFinal.lean) can be met together.


Declared: the write-up has another plan for the closing of the test for linear
constraints: one splitting, in the shared part. That plan is not the one under this file (here: the
plan without a splitting). The object at that plan stands beside: Cb/Obj/LdObjectPlanPaper.lean
(`LdObjPp`; `ldObjPp_hyp`); the records on data (`LdObjR`, `LdObjZ` and what stands on them) are
at the plan without a splitting;
among those at the plan with a splitting: `LdObjRp`, `LdObjZp` and what stands on them
(Cb/Obj/LdObjectPpRows.lean, Cb/Obj/LdObjectPpData.lean).






Why `D.Par3` (the link's first index): for 2 eM below the distance the write-up allows for the
parent's fold any radius with e₀ + eM below the distance, with error 0, and its reference takes that
(far fewer locations on the parent than on the further index) (by a reading). `Own3` admits it:
`D.Par3` (Cb/Obj/LdObjectDataThird.lean) has both regimes for the link's first index.
Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Obj.LdObjectDataJohn
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The object, offline phase and link within a third, the session below the Johnson radius: the
data. -/
structure LdObjZM (F E : Type) [Field F] [Field E] [Fintype F] [Fintype E] [Algebra F E] where
  R    : LdObjR F E
  Zw   : LdWfE F E
  Y    : R.toLdObjD.StdS
  twK  : R.Kc.run.Tow3
  tw₁  : R.TP₀.D₁.Tow3
  tw₂  : R.TP₀.D₂.Tow3
  tw₃  : R.X.run.Tow3
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

namespace LdObjZM
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (Z : LdObjZM F E)

def toZ : LdObjZ F E :=
  { R := Z.R, Zw := Z.Zw, Y := Z.Y, twK := Z.R.Kc.run.up3 Z.twK, tw₁ := Z.R.TP₀.D₁.up3 Z.tw₁,
    tw₂ := Z.R.TP₀.D₂.up3 Z.tw₂, tw₃ := Z.R.X.run.up3 Z.tw₃
    tw₁B := Z.R.TB₀.D₁.upJ Z.tw₁B, tw₂B := Z.R.TB₀.D₂.upJ Z.tw₂B, tw₃B := Z.R.XB.run.upJ Z.tw₃B }

structure Hyp (p : ℕ) : Prop where
  wfIs  : (⟨Z.R.W, Z.R.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨Z.Zw.W, Z.Zw.G.B⟩
  sndIs : Z.R.toLdObjD = Z.R.toLdObjD.std Z.Y
  /-- offline phase and link: within a third -/
  wf3   : Z.Zw.Third p Z.dS
  sOff  : Z.Y.TS.Third3 Z.Y.LW Z.Y.LU Z.Y.LO Z.Y.tW Z.Y.tU Z.Y.tO Z.dW Z.dU Z.dO
  sLink : Z.R.K.P.StdThird Z.Y.SdK Z.Y.LK Z.Y.tK Z.Y.YK Z.Y.ixK Z.dN
  /-- the session's standard senders: below the Johnson radius -/
  sOn   : Z.Y.TB.JohnS Z.Y.LWB Z.Y.LUB Z.Y.LOB Z.Y.tWB Z.Y.tUB Z.Y.tOB Z.dWB Z.dUB Z.dOB
  own   : Z.R.toLdObjD.Own3
  pl    : Z.R.HypPl
  pK    : Z.R.Kc.run.Pre3 Z.twK Z.dK
  p₁    : Z.R.TP₀.D₁.Pre3 Z.tw₁ Z.d₁
  p₂    : Z.R.TP₀.D₂.Pre3 Z.tw₂ Z.d₂
  p₃    : Z.R.X.run.Pre3 Z.tw₃ Z.d₃
  p₁B   : Z.R.TB₀.D₁.PreJ Z.tw₁B Z.d₁B
  p₂B   : Z.R.TB₀.D₂.PreJ Z.tw₂B Z.d₂B
  p₃B   : Z.R.XB.run.PreJ Z.tw₃B Z.d₃B

end LdObjZM

def Spec.ldObjZM_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Prop :=
  ∀ (Z : LdObjZM F E) (p : ℕ), Z.Hyp p → Z.toZ.Hyp p 1

theorem ldObjZM_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldObjZM_hyp F E := by
  intro Z p h
  have hC : Z.R.W.Cf.Third := by
    have key : ∀ x : Σ W : LdOWf F E, W.P.Blk, x = ⟨Z.Zw.W, Z.Zw.G.B⟩ → x.1.Cf.Third := by
      rintro _ rfl
      exact h.wf3.conf3
    exact key ⟨Z.R.W, Z.R.Bw⟩ h.wfIs
  exact
    { wfIs := h.wfIs
      sndIs := h.sndIs
      wfOK := ldWfEnd3_ok Z.Zw p Z.dS h.wf3
      sndOK := ⟨h.sOff.hyp, h.sLink.hyp, h.sOn.hyp⟩
      own := h.own.own hC
      pl := h.pl
      pK := h.pK.pre
      p₁ := h.p₁.pre
      p₂ := h.p₂.pre
      p₃ := h.p₃.pre
      p₁B := (ldTowGJ_run E _ _ Z.tw₁B Z.d₁B h.p₁B).1
      p₂B := (ldTowGJ_run E _ _ Z.tw₂B Z.d₂B h.p₂B).1
      p₃B := (ldTowGJ_run E _ _ Z.tw₃B Z.d₃B h.p₃B).1 }

end Cb
