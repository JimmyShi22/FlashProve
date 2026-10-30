-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPartsD.lean: the data of an object without the closings of its two linear tests
(`LdObjD`). This file puts `LdObjD` together from parts that carry no plan; and it proves
`D.HypRest L`, `D.HypSnd` from the parts' clauses, their senders' clauses and `Cf.OK L`.

The object (`LdObj`, Cb/Obj/LdObject.lean) is one record with a configuration and, over it, the
sub-protocols of the proof system, as five terms.
Definitions, statements (`Cb.Spec.ldPartsD_rest`, `Cb.Spec.ldPartsD_snd`, `Cb.Spec.ldPartsD_old`)
and proofs. Generic; no protocol is given.
A closing is the last part of a test, of the link or of a segment. In a test for linear constraints
and in the link it is a chain of whole tests on groups, down to the trivial statement (`LdTc`,
Cb/Ld/LdLinCloseChain.lean; `LdLinP.Closing`, Cb/Ld/LdLin.lean). A plan, of the closing of a test
for linear constraints: which groups of oracle messages are tested, in which order, what is kept
after each test and, where a row lies on two groups, how it is split (`LdLinPp`,
Cb/Ld/LdLinClosePlanP.lean; without a splitting `LdLinPl`, Cb/Ld/LdLinClosePlan.lean).
Why: Cb/Obj/LdObjectParts.lean and Cb/Obj/LdObjectPartsG.lean put an object `LdObjP` together from
five parts; their second and fifth parts (`PLin`, `PBat`) carry a plan of whole tests with its
bundle. A record that closes the two tests in another way (Cb/Obj/LdObjectPlanPaper.lean: the plan
with a splitting) starts from `LdObjD`, the data without closings, and asks `D.HypRest L`
(Cb/Obj/LdObjectTerms.lean). Here `LdObjD` is put together from: the first, third and fourth parts
as they are (`PWf`, `PLink`, `PReqG`), and the bare data of the two tests.

Main names:
  `PLinD A`: its data are `εf`, the senders `Sn`, `q₀` and two fixed values. `Ln.Hyp` asks: `q₀ ∅`;
    the fold's bad points; distinct places.
  `PBatD Cf on`: its data are `N`, `onB`, the senders `SnB`, the bound `qaB`, `εfB` and three fixed
    values. `Bt.Hyp` asks: `Fits`; the fold's bad points; distinct places; the bound is monotone.
  `ldPartsD A Ln Lk Rq Bt z0 r0 dOff dOn : LdObjD F E`.
  `Spec.ldPartsD_rest`: `Cf.OK L`, `A.Hyp`, `Ln.Hyp`, `Lk.Hyp`, `Rq.Hyp Bt.qaB`, `Bt.Hyp` ⇒
    `(ldPartsD ..).HypRest L` (all twenty-two clauses).
  `Spec.ldPartsD_snd`: `Sn.OK`, `Lk.Hyp` (whole; the proof uses its `sndK`), `SnB.OK`, `SnB.Apart` ⇒
    `(ldPartsD ..).HypSnd`.
  `PLin.toD`, `PBat.toD`; `Spec.ldPartsD_old`: the parts with plans give parts without;
    `(ldPartsG ..).toLdObjD` is `ldPartsD` at these, by definition.

No theorem of this library states that the hypotheses of `Spec.ldPartsD_rest` can be met together.

Notation: `L`: a natural number (`LdCf.OK L`, Cb/Obj/LdObjectConf.lean, says that it bounds the
lists at the radius of decoding); `εf`, `εfB`: natural numbers, in `LdLinP.FoldErr`
(Cb/Ld/LdLin.lean): `∀ f rec, on0 f rec → cnt (P.D.X.Bad f rec P.e') ≤ εf`, taken at `A.W.O.on0`,
`Ln.εf` (`fold`) and at `Bt.onB`, `Bt.εfB` (`foldB`); `onB`: a condition on the encoded index and
its record (`LdIx`, Cb/Ld/LdFoldEq.lean).

Limits: nothing on closings, but for the link's: its closing `Kc` is in `PLink`, and `Lk.Hyp` has
`close` and `bearK`.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectPartsG

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The test at one instance, without a closing: the data. -/
structure PLinD (A : PWf F E) where
  εf  : ℕ
  Sn  : A.W.O.toC.P.Snd
  q₀  : Finset extNone.Pos → Prop
  dT  : A.W.O.toC.P.W0
  dT₀ : A.W.O.P.W0

structure PLinD.Hyp {A : PWf F E} (Ln : PLinD A) : Prop where
  q₀e   : Ln.q₀ ∅
  fold  : A.W.O.toC.P.FoldErr A.W.O.on0 Ln.εf
  pyInj : Function.Injective A.W.O.py

/-- The test at N instances, without a closing: the data. -/
structure PBatD (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (on : LdOLd Cf) where
  N   : ℕ
  onB : (on.ol.P.D.X.Row → Fin Cf.C₀.n → E) → on.ol.P.D.X.Rec → Prop
  SnB : on.ol.toC.P.Snd
  qaB : Finset on.ol.toC.P.Ea.Pos → Prop
  εfB : ℕ
  dB  : on.ol.toC.P.W0
  dB₀ : on.ol.P.W0
  yB  : on.ol.toC.P.Ea.Str

structure PBatD.Hyp {Cf : LdCf F E} [Nonempty (Fin Cf.C₀.n)] {on : LdOLd Cf} (Bt : PBatD Cf on) :
    Prop where
  fitsB  : on.ol.Fits Bt.onB
  foldB  : on.ol.toC.P.FoldErr Bt.onB Bt.εfB
  pyInjB : Function.Injective on.ol.py
  monoB  : ∀ U V, V ⊆ U → Bt.qaB U → Bt.qaB V

/-- The parts with plans give parts without. -/
@[reducible] def PLin.toD {A : PWf F E} (Ln : PLin A) : PLinD A :=
  ⟨Ln.εf, Ln.Sn, Ln.q₀, Ln.dT, Ln.dT₀⟩
@[reducible] def PBat.toD {Cf : LdCf F E} [Nonempty (Fin Cf.C₀.n)]
    {on : LdOLd Cf} (Bt : PBat Cf on) : PBatD Cf on :=
  ⟨Bt.N, Bt.onB, Bt.SnB, Bt.qaB, Bt.εfB, Bt.dB, Bt.dB₀, Bt.yB⟩

/-- The data put together. -/
@[reducible] def ldPartsD (A : PWf F E) (Ln : PLinD A) (Lk : PLink A.W.Cf)
    (Rq : PReqG A.W.Cf) (Bt : PBatD A.W.Cf Rq.on) (z0 : Rq.Wz) (r0 : Rq.on.S.Rnd)
    (dOff : A.W.O.left.AMsg) (dOn : Rq.on.ol.left.AMsg) : LdObjD F E where
  W := A.W
  Bw := A.Bw
  εf := Ln.εf
  Sn := Ln.Sn
  q₀ := Ln.q₀
  dT := Ln.dT
  dT₀ := Ln.dT₀
  K := Lk.K
  on0K := Lk.on0
  on1K := Lk.on1
  Sl := Lk.Sl
  ε₀ := Lk.ε₀
  ε₁ := Lk.ε₁
  Kc := Lk.Kc
  dK₂ := Lk.dK₂
  dK := Lk.dK
  on := Rq.on
  N := Bt.N
  Kr := Rq.Kr
  cr := Rq.cr
  Wz := Rq.Wz
  piz := Rq.piz
  Bz := Rq.Bz
  r := Rq.r
  w₀ := Rq.w₀
  qφ := Rq.qφ
  onB := Bt.onB
  SnB := Bt.SnB
  qaB := Bt.qaB
  εfB := Bt.εfB
  dB := Bt.dB
  dB₀ := Bt.dB₀
  yB := Bt.yB
  z0 := z0
  r0 := r0
  dOff := dOff
  dOn := dOn

end

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldPartsD_rest : Prop :=
  ∀ (A : PWf F E) (Ln : PLinD A) (Lk : PLink A.W.Cf) (Rq : PReqG A.W.Cf) (Bt : PBatD A.W.Cf Rq.on)
      (z0 : Rq.Wz) (r0 : Rq.on.S.Rnd) (dOff : A.W.O.left.AMsg) (dOn : Rq.on.ol.left.AMsg) (L : ℕ),
    A.W.Cf.OK L → A.Hyp → Ln.Hyp → Lk.Hyp → Rq.Hyp Bt.qaB → Bt.Hyp →
    (ldPartsD A Ln Lk Rq Bt z0 r0 dOff dOn).HypRest L

def ldPartsD_snd : Prop :=
  ∀ (A : PWf F E) (Ln : PLinD A) (Lk : PLink A.W.Cf) (Rq : PReqG A.W.Cf) (Bt : PBatD A.W.Cf Rq.on)
      (z0 : Rq.Wz) (r0 : Rq.on.S.Rnd) (dOff : A.W.O.left.AMsg) (dOn : Rq.on.ol.left.AMsg),
    Ln.Sn.OK → Lk.Hyp → Bt.SnB.OK → Bt.SnB.Apart → (ldPartsD A Ln Lk Rq Bt z0 r0 dOff dOn).HypSnd

def ldPartsD_old : Prop :=
  ∀ (A : PWf F E) (Ln : PLin A) (Lk : PLink A.W.Cf) (Rq : PReqG A.W.Cf) (Bt : PBat A.W.Cf Rq.on)
      (z0 : Rq.Wz) (r0 : Rq.on.S.Rnd) (dOff : A.W.O.left.AMsg) (dOn : Rq.on.ol.left.AMsg),
    (ldPartsG A Ln Lk Rq Bt z0 r0 dOff dOn).toLdObjD = ldPartsD A Ln.toD Lk Rq Bt.toD z0 r0 dOff dOn

end
end Spec

theorem ldPartsD_rest (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldPartsD_rest F E :=
  fun _ _ _ _ _ _ _ _ _ _ hC hA hn hk hr hb =>
    { conf := hC, lay := ⟨hA.lay, hr.lay⟩, tie := hA.tie, wfLaws := hA.wfLaws, wfHyp := hA.wfHyp,
      wfBud := hA.wfBud, wfNeed := hA.wfNeed, q₀e := hn.q₀e, fold := hn.fold, pyInj := hn.pyInj
      fitsK := hk.fitsK, foldK := hk.foldK, plInj := hk.plInj, bearK := hk.bearK, rHyp := hr.rHyp,
        rZk := hr.rZk, rFmt := hr.rFmt, rEnd := hr.rEnd, fitsB := hb.fitsB, foldB := hb.foldB,
        pyInjB := hb.pyInjB, monoB := hb.monoB }

theorem ldPartsD_snd (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldPartsD_snd F E :=
  fun _ _ _ _ _ _ _ _ _ hn hk hb ha => ⟨hn, hk.sndK, hb, ha⟩

theorem ldPartsD_old (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldPartsD_old F E :=
  fun _ _ _ _ _ _ _ _ _ => rfl

end Cb
