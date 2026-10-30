-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectDataSnd.lean: book-keeping for the hypotheses of a holographic IOP: the object with
the hypotheses of `Z.HypS p L V`: the sender of weights-formedness a standard sender, and the
request's last base joint a standard one; among the hypotheses are also properties of the request's
program.

Its statements are implications between records of hypotheses.
Definitions, statements and proofs: a step towards `Z.Hyp p L` of Cb/Obj/LdObjectData.lean, whose
head says what the object and the request's program are. Later files use
`ldWfE_okStd` (for example Cb/Obj/LdObjectDataRefT.lean); no other file of this library uses
`ldObjZs_hyp`.
Weights-formedness is the offline sub-protocol for the relation `Rwf` (Hiop/RecConf.lean).
A sender (`Sig.Sender`, Cb/Ld/LdSendFam.lean) is the honest prover's data for sending a family of
oracle messages.
A joint (`IOR.Rels`, Ior/Chain.lean) is what a chain of reductions says of the statements at one of
its ends or between two of its reductions.
Among the clauses of `Z.Hyp p L` that still speak of more than data, beside the request's program,
are two groups:
  those on the sender of weights-formedness inside `Zw.OK` (its two laws; it does not look; its
    encoder hides; the pads' law; a mask stands at its own places; an entry elsewhere reads neither
    that mask nor a pad; exactly: `sender`, `sBlind`, `hides` of `Rest0`, `pad`, `sOwn`, `sOff` of
    `Rest1`, Cb/Ld/LdWfEnd.lean). With the standard sender and its layout of masks they are a
    theorem (Cb/Ld/LdWfEndStd.lean: `ldWfE_std`, under its hypotheses);
  those on the request's last base joint (`EndOK`'s three facts). For the two standard joints they
    are a theorem (Cb/Obj/LdObjectDataThird.lean: `EndStd.ok`).

Main names:
  `V : Zw.StdW Fp`: data (its fields: see the record), and a proof among the data: `hpl` (the masks'
    places are different): it is needed to write the layout of masks down. (The statements also
    take, as an instance, that each block's masks are finitely many.)
  `V.Hyp p L`: one equation: (Zw.D, Zw.X) is (the standard sender, its record of mask places) (true
    by definition for whoever builds Zw so; a hypothesis here); `V.Y.OK Zw.t`; two equations on body
    and dat; three on places; `Zw.Rest2 p` (no clause on the sender but "fair seeds" and "the
    vectors are the multiplicities"); laws of the codes; the configuration; lists; evading samples.
  `Spec.ldWfE_okStd`: `V.Hyp p L` ⇒ `Zw.OK p L`.
  `Z.HypS p L V`: `Z.Hyp p L` with `wfOK` replaced by `V.Hyp p L`, and `rEnd` by `D.EndStd`.
  `Spec.ldObjZs_hyp`: `Z.HypS p L V` ⇒ `Z.Hyp p L`.

Limits: the request's program stays a parameter with properties (`rHyp`, `rZk`, `rFmt`; its last
claims: `abRel`, `abRelR`, `restVal` in `R.HypPl`): "Limits" in the head of
Cb/Obj/LdObjectData.lean.
That `Z.HypS` can be met is not shown in this file. No instance that meets the hypotheses of
`ldObjZs_hyp` is part of this library; as far as the library shows, this theorem may hold of
nothing. This file says nothing on the sender of the request's first sending (inside `r.Hyp`).
On `rZk`. What honest-verifier zero knowledge asks of the request's program is `r.ZkS`
(Cb/Req1/LdReqS.lean), beside its hypotheses (`r.Hyp`): `r.Zk` with the set of fresh facts closed,
at each segment's entry and before the last part, under join at one reading, a coarser reading,
another type for the same masks. `r.Zk` gives `r.ZkS` (`ldReqS_of_zk`). Why: in
this protocol's technical report (lean/CREDITS.md) a later segment's sumcheck that ends at a map of
the index has own masks from two sendings; by our reading `r.Zk` cannot be met by that layout.
Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectDataThird
import Cb.Ld.LdWfEndStd

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The standard sender of weights-formedness: the data beside `Z : LdWfE F E`. -/
structure LdWfE.StdW {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (Z : LdWfE F E) (Fp : Type) [Field Fp] [Fintype Fp] [Algebra Fp E] where
  Y   : Z.W.P.S.StdL Fp
  dat : Z.W.P.Body → ∀ a, Y.Dt a → E
  w0  : Z.W.P.Body × Z.W.P.Wp
  bd  : (∀ a, Y.Dt a → E) → Z.W.P.Body
  nAt : Z.W.P.N → Z.W.P.S.Ent
  RdW : Z.W.P.S.Ent → Prop
  atL : ∀ l : Fin (Z.W.P.n + 1), (Z.K.pl Z.Rl l).I → Z.W.P.N
  pl  : ∀ b, Z.K.wfI Z.Rl b → Σ a, Y.Fr a
  hpl : Function.Injective fun x : Σ b, Z.K.wfI Z.Rl b => pl x.1 x.2

structure LdWfE.StdW.Hyp {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    {Z : LdWfE F E} [∀ b, Fintype (Z.K.wfI Z.Rl b → E)] {Fp : Type} [Field Fp] [Fintype Fp]
    [Algebra Fp E] (V : Z.StdW Fp) (p L : ℕ) : Prop where
  isStd  : (⟨Z.D, Z.X⟩ : Σ D, Z.K.MaskPl D Z.Rl) =
    ⟨Z.W.P.stdD V.Y V.dat V.w0, Z.K.stdX Z.Rl V.Y V.dat V.w0 V.nAt V.RdW V.atL V.pl V.hpl⟩
  ok     : V.Y.OK Z.t
  body   : ∀ m, Z.W.P.body m = V.bd (V.Y.dataOf m)
  bdDat  : ∀ b, V.bd (V.dat b) = b
  plL    : ∀ l i, V.nAt (V.atL l i) = V.Y.entF (V.pl (some l) i)
  plB    : ∀ i, V.nAt (Z.W.P.wAt i) = V.Y.entF (V.pl none i)
  noPad  : ∀ n, V.RdW n → V.Y.NoPad n
  rest2  : Z.Rest2 p
  laws   : ∀ a, (Z.W.P.S.om a).C.Laws
  conf   : Z.W.Cf.OK L
  list   : ∀ a, (Z.W.P.S.om a).ListLE (Z.L a)
  evades : ∀ a, (Z.W.P.S.om a).Evades

/-- `HypOwn` with "the last base joint is a standard one" in the place of `EndOK` -/
structure LdObjD.HypOwnS {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E]
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
  rEnd   : T.EndStd
  fitsB  : T.on.ol.Fits T.onB
  foldB  : T.on.ol.toC.P.FoldErr T.onB T.εfB
  pyInjB : Function.Injective T.on.ol.py
  monoB  : ∀ U V, V ⊆ U → T.qaB U → T.qaB V

structure LdObjZ.HypS {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (Z : LdObjZ F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (p L : ℕ) {Fp : Type} [Field Fp]
    [Fintype Fp] [Algebra Fp E] (V : Z.Zw.StdW Fp) : Prop where
  wfIs  : (⟨Z.R.W, Z.R.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨Z.Zw.W, Z.Zw.G.B⟩
  sndIs : Z.R.toLdObjD = Z.R.toLdObjD.std Z.Y
  wfS   : V.Hyp p L
  sndOK : Z.Y.Hyp
  own   : Z.R.toLdObjD.HypOwnS
  pl    : Z.R.HypPl
  pK    : Z.R.Kc.run.Pre Z.twK
  p₁    : Z.R.TP₀.D₁.Pre Z.tw₁
  p₂    : Z.R.TP₀.D₂.Pre Z.tw₂
  p₃    : Z.R.X.run.Pre Z.tw₃
  p₁B   : Z.R.TB₀.D₁.Pre Z.tw₁B
  p₂B   : Z.R.TB₀.D₂.Pre Z.tw₂B
  p₃B   : Z.R.XB.run.Pre Z.tw₃B

namespace Spec

def ldWfE_okStd : Prop :=
  ∀ (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
      [Fintype Fp] [Algebra Fp E] (Z : LdWfE F E) [∀ b, Fintype (Z.K.wfI Z.Rl b → E)]
      (V : Z.StdW Fp) (p L : ℕ),
    V.Hyp p L → Z.OK p L

def ldObjZs_hyp : Prop :=
  ∀ (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
      [Fintype Fp] [Algebra Fp E] (Z : LdObjZ F E) [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)]
      (V : Z.Zw.StdW Fp) (p L : ℕ),
    Z.HypS p L V → Z.Hyp p L

end Spec

theorem ldWfE_okStd : Spec.ldWfE_okStd := by
  intro F E Fp _ _ _ _ _ _ _ _ Z _ V p L h
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ :=
    ldWfE_std F E Fp Z V.Y V.dat V.w0 V.bd V.nAt V.RdW V.atL V.pl V.hpl h.isStd h.ok h.body
      h.bdDat h.plL h.plB h.noPad
  exact { toRest2 := h.rest2, pad := s4, sOwn := s5, sOff := s6, sender := s1, sBlind := s2,
          hides := s3, laws := h.laws, conf := h.conf, list := h.list, evades := h.evades }

theorem ldObjZs_hyp : Spec.ldObjZs_hyp := fun F E Fp _ _ _ _ _ _ _ _ Z _ V p L h =>
  { wfIs := h.wfIs, sndIs := h.sndIs, wfOK := ldWfE_okStd F E Fp Z.Zw V p L h.wfS, sndOK := h.sndOK
    own :=
      { lay := h.own.lay, q₀e := h.own.q₀e, fold := h.own.fold, pyInj := h.own.pyInj,
        fitsK := h.own.fitsK, foldK := h.own.foldK, plInj := h.own.plInj, bearK := h.own.bearK,
        rHyp := h.own.rHyp, rZk := h.own.rZk, rFmt := h.own.rFmt
        rEnd := h.own.rEnd.ok, fitsB := h.own.fitsB, foldB := h.own.foldB,
          pyInjB := h.own.pyInjB, monoB := h.own.monoB }
    pl := h.pl, pK := h.pK, p₁ := h.p₁, p₂ := h.p₂, p₃ := h.p₃, p₁B := h.p₁B,
      p₂B := h.p₂B, p₃B := h.p₃B }

end Cb
