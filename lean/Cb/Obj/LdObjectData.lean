-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectData.lean: book-keeping for the hypotheses of a holographic IOP: the object with the
terms that the library builds for its sub-protocols, with the hypotheses of `Z.Hyp p L`, among them
those on codes, samples, evaders, places, numbers, the model; and on a request's program, a
parameter whose "conditions" include assumed completeness and soundness of its sub-chains; and on
the sender `Zw.D` of weights-formedness, a free value with laws.

Its main statement is an implication between two records of hypotheses.
Definitions, statements and proofs: an assembly.
The object (`LdObj`, Cb/Obj/LdObject.lean) is a configuration with five terms, each an interactive
oracle reduction with its honest prover, extractor and error numbers, for four sub-protocols (the
test for linear constraints at two settings); Hiop/RecBuild.lean builds the holographic IOP, with an
untrusted committer, from them.
"On data" is a way of speaking of these comments, no Lean notion: a condition on codes, samples,
evaders, places, numbers or the model, as against a property of a term.
The preamble of a request reduces an instance, with the encoded index as oracle, to a claim for the
test for linear constraints (`ReqT`, Cb/Obj/LdObjectReq.lean); its program is the field `r` of
`LdObjD` (Cb/Obj/LdObjectTerms.lean), an `LdReq` (Cb/Req1/LdReq.lean).
What the files below it leave as parameters with a property is put in here, level by level:
  the closings of the two tests for linear constraints: the plan without a splitting, "the rest" one
    more test on one group (Cb/Obj/LdObjectPlan.lean, Cb/Obj/LdObjectPlanRows.lean);
  the seven whole tests on groups: concrete towers (Cb/Obj/LdObjectTower.lean,
    Cb/Obj/LdObjectTowers.lean);
  the blocks of weights-formedness: the lookups, the batching, the sender's masks as values
    (Cb/Ld/LdWfEnd.lean: `Zw : LdWfE`; `Zw.OK`: its hypotheses, among them six clauses on the
    sender);
  the seven senders of the two tests and of the link: standard senders
    (Cb/Obj/LdObjectSendersLin.lean: `Y : StdS`; `Y.Hyp`: no clause speaks of a sender).

Main names:
  `LdObjZ F E`: data only, but for the proofs inside its fields' types (among them `LdObjD.ne`,
    `LdCf.hp`, `LdLinPl.hU` .., `LdLinPlT.hc₁`, `hc₂`, `LdLkP.Cl.all`): `R : LdObjR`; `Zw`; `Y`;
    seven towers.
  `D.HypOwn`: the three layouts; the bounds on the bad points of the three kinds of folds of the
    index (conditions on the index code); places on cubes are distinct; inequalities; `q₀e`,
    `fitsK`, `fitsB`, `monoB`; and the request's: `r.Hyp`, `r.ZkS`, `r.Fmt`, `EndOK`.
  `Z.Hyp p L`: two equations that say which terms are in R (whoever builds R from Zw and Y has them
    by definition; they are hypotheses here, not fields). Then `Zw.OK p L`; `Y.Hyp`; `HypOwn`;
    `R.HypPl` (places, numbers, forms of the two plans); `D.Pre T` for each of the seven tests (two
    equations each; the bridge's evader, the list of the complex, `Fits`; the tower's blocks' own
    hypotheses).
  `Spec.ldObjZ_hyp`: for p the characteristic of E, `Z.Hyp p L` ⇒ `Z.R.Hyp L`. So (`Cb.ldObjR_hyp`,
    `Cb.ldObjP_hyp`, `Cb.ldObjT_ok`) `Z.R.toP.toT.obj.OK L`, and all that follows from it.

Notation: `L`: a natural number (`LdCf.OK L`, Cb/Obj/LdObjectConf.lean, says that it bounds the
lists at the radius of decoding).

Limits: the request's program r is still a parameter with a property (its moves: `r.Hyp`; its masks:
`r.ZkS`; its formats: `r.Fmt`; its last claims: `abRel`, `abRelR`, `restVal` in `R.HypPl`).
Six clauses on the sender `Zw.D` of weights-formedness are not on data: it is a free value with laws
(Cb/Ld/LdWfEnd.lean: `Rest0`, `Rest1`).
`Z.Hyp p L` is a very long conjunction of conditions from many files. That they can be met together
is not shown in this file. No instance that meets the hypotheses of `ldObjZ_hyp` is part of this
library; as far as the library shows, this theorem may hold of nothing. These hypotheses have not
been met by a request that says something. Several clauses of `LdObjT.Hyp`, which follows from
`Z.Hyp p L` (the row of `Spec.ldObjZ_hyp`), were unsatisfiable as first written and have been mended
(head of Cb/Obj/LdObjectTerms.lean); until an instance of `Z.Hyp` with a request that says something
is exhibited, more such finds are to be expected, and, as far as this file shows, every theorem that
assumes `Z.Hyp` may hold of nothing.
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



Proved are: the composition, the batch test behind the request, the offline phase, the link, the
compilation, each under the hypotheses of its statement.
The cure in Lean is the reference request as a term (Cb/Req1/LdReqRef*.lean,
Cb/Obj/LdObjectDataRef.lean). Among what is still a property of terms
there: each closing's fold link, senders, entry and exit steps, the model's side, where the masks
come from. No theorem of this library states that the hypotheses of `ldReqRefFinal`
(Cb/Req1/LdReqRefFinal.lean) can be met together.


On `rZk`. What honest-verifier zero knowledge asks of the request's program is `r.ZkS`
(Cb/Req1/LdReqS.lean), beside
its hypotheses (`r.Hyp`): `r.Zk` with the set of fresh facts closed, at each segment's entry and
before the last part, under join at one reading, a coarser reading, another type for the same masks.
`r.Zk` gives `r.ZkS` (`ldReqS_of_zk`). Why: in this protocol's technical report (lean/CREDITS.md) a
later segment's sumcheck that ends at a map of the index has own masks from two sendings; by our
reading `r.Zk` cannot be met by that layout.
Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectPlanRows
import Cb.Obj.LdObjectTowers
import Cb.Obj.LdObjectSendersLin
import Cb.Ld.LdWfEnd

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- the clauses of `HypRest` that are neither the configuration's nor weights-formedness' -/
structure LdObjD.HypOwn {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] (T : LdObjD F E) : Prop where
  lay    : T.LayOK
  q₀e    : T.q₀ ∅
  fold   : T.W.O.toC.P.FoldErr T.W.O.on0 T.εf
  pyInj  : Function.Injective T.W.O.py
  fitsK  : T.K.FitsK T.on0K T.on1K
  foldK  : T.K.P.FoldErr T.on0K T.on1K T.ε₀ T.ε₁
  plInj  : Function.Injective T.K.pl
  bearK  : ∀ a, T.Kc.t ≤ T.Sl.t a
  rHyp   : T.r.Hyp
  rZk    : T.r.ZkS
  rFmt   : T.r.Fmt (T.on.ol.fmtA T.cr T.qφ) (T.on.ol.fmtZAt T.Bz T.piz T.qiB)
  rEnd   : T.on.ol.EndOK T.piz T.Bz
  fitsB  : T.on.ol.Fits T.onB
  foldB  : T.on.ol.toC.P.FoldErr T.onB T.εfB
  pyInjB : Function.Injective T.on.ol.py
  monoB  : ∀ U V, V ⊆ U → T.qaB U → T.qaB V

/-- The object with the hypotheses of `Z.Hyp p L`: the data. -/
structure LdObjZ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] where
  R    : LdObjR F E
  Zw   : LdWfE F E
  Y    : R.toLdObjD.StdS
  twK  : R.Kc.run.Tow
  tw₁  : R.TP₀.D₁.Tow
  tw₂  : R.TP₀.D₂.Tow
  tw₃  : R.X.run.Tow
  tw₁B : R.TB₀.D₁.Tow
  tw₂B : R.TB₀.D₂.Tow
  tw₃B : R.XB.run.Tow

structure LdObjZ.Hyp {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (Z : LdObjZ F E) (p L : ℕ) : Prop where
  /-- which terms are in `R` -/
  wfIs  : (⟨Z.R.W, Z.R.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨Z.Zw.W, Z.Zw.G.B⟩
  sndIs : Z.R.toLdObjD = Z.R.toLdObjD.std Z.Y
  /-- conditions: weights-formedness, the standard senders, the object's own clauses, the plans -/
  wfOK  : Z.Zw.OK p L
  sndOK : Z.Y.Hyp
  own   : Z.R.toLdObjD.HypOwn
  pl    : Z.R.HypPl
  /-- the seven tests -/
  pK    : Z.R.Kc.run.Pre Z.twK
  p₁    : Z.R.TP₀.D₁.Pre Z.tw₁
  p₂    : Z.R.TP₀.D₂.Pre Z.tw₂
  p₃    : Z.R.X.run.Pre Z.tw₃
  p₁B   : Z.R.TB₀.D₁.Pre Z.tw₁B
  p₂B   : Z.R.TB₀.D₂.Pre Z.tw₂B
  p₃B   : Z.R.XB.run.Pre Z.tw₃B

def Spec.ldObjZ_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] : Prop :=
  ∀ (p : ℕ) [CharP E p] (Z : LdObjZ F E) (L : ℕ), Z.Hyp p L → Z.R.Hyp L

/-- the clauses on the configuration and on weights-formedness, at every pair that is `Zw`'s (not
all hypotheses are named here: see the statement below) -/
theorem ldObjZ_wf {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (p : ℕ)
    [CharP E p] (Zw : LdWfE F E) (L : ℕ) (h : Zw.OK p L) :
    ∀ x : Σ W : LdOWf F E, W.P.Blk, x = ⟨Zw.W, Zw.G.B⟩ →
      x.1.Cf.OK L ∧ x.1.Tie ∧ x.1.P.Laws ∧ x.2.Hyp ∧
      (∀ l, l ≤ x.1.P.n → ∀ ρ, (x.2.sub l).P.bud ρ ∅) ∧
      ∀ l, l ≤ x.1.P.n → ∀ ρ U, (x.2.sub l).R.need ρ U = U := by
  rintro _ rfl
  exact ⟨h.conf, h.tie,
    ldWfEnd_laws p Zw L h,
    ldWfEnd_hyp p Zw L h,
    fun l _ ρ =>
      lift_bud Zw.W.P.S
        (ldLkpAsm2N_plainI E (Zw.K.asm l) Zw.W.P.N Sum.inr Zw.W.Cf.conf Zw.W.P.S.Msg Zw.W.P.msg)
        ρ ∅,
    fun l _ ρ U =>
      lift_need Zw.W.P.S
        (ldLkpAsm2N_plainI E (Zw.K.asm l) Zw.W.P.N Sum.inr Zw.W.Cf.conf Zw.W.P.S.Msg Zw.W.P.msg)
        ρ U⟩

theorem ldObjZ_hyp (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldObjZ_hyp F E := by
  intro p _ Z L h
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := ldObjZ_wf p Z.Zw L h.wfOK ⟨Z.R.W, Z.R.Bw⟩ h.wfIs
  have hs : Z.R.toLdObjD.HypSnd := by
    rw [h.sndIs]
    exact ldObjS_snd Z.R.toLdObjD Z.Y h.sndOK
  exact
    { r :=
        { base :=
            { rest :=
                { conf := w1, lay := h.own.lay, tie := w2, wfLaws := w3, wfHyp := w4, wfBud := w5,
                  wfNeed := w6, q₀e := h.own.q₀e, fold := h.own.fold, pyInj := h.own.pyInj
                  fitsK := h.own.fitsK, foldK := h.own.foldK, plInj := h.own.plInj,
                    bearK := h.own.bearK, rHyp := h.own.rHyp, rZk := h.own.rZk,
                    rFmt := h.own.rFmt, rEnd := h.own.rEnd
                  fitsB := h.own.fitsB, foldB := h.own.foldB,
                    pyInjB := h.own.pyInjB, monoB := h.own.monoB }
              snds := hs }
          pl := h.pl }
      close := h.pK.ok
      test₁ := h.p₁.ok
      test₂ := h.p₂.ok
      test₃ := h.p₃.ok
      test₁B := h.p₁B.ok
      test₂B := h.p₂B.ok
      test₃B := h.p₃B.ok }

end Cb
