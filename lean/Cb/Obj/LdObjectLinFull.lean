-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectLinFull.lean: the test for linear constraints on the encoded index, one instance,
with its closing as a term.

The test for linear constraints is the interactive oracle proof of proximity (IOPP) for the
constraint relation; it follows a preamble (Hiop/RecSubs.lean, Hiop/RecBuild.lean). This file takes
the test's last part, the closing, as a chain of reductions from the joint after the test's core to
the trivial statement, puts a step without rounds before the test so that the whole has the types
of the object's list (`LinListR` with `LinKnowR`, Hiop/RecSubs.lean), and states the two items of
the object for it, under the hypotheses that "Limits" names.

Definitions and statements (Cb.Spec.ldOLF_*); the proofs are in Cb/Obj/LdObjectLinFullProofs.lean.

Two forms of one test are in this library, and they do not meet by definition.
  Cb/Obj/LdObjectLin.lean, `O.P`: the test over the configuration. What the preamble left stands on
    the words of S themselves (oracles `S.ext`, witnesses the pairs, the joint `S.alone more`): so
    that the test's explicit part and oracles are those of the object's list. The four bridging
    facts to that list are proved for its first joint `O.P.j0`.
  Cb/Ld/LdLinClosePre.lean, `C.P`: the test over a signature. What the preamble left is a joint
    over a signature beside further oracles and a further witness (oracles `E₀.prod Sa.ext`,
    witnesses pairs × Wpa, the joint `Sa.over Ab`): the form in which the closing is built
    (Cb/Ld/LdLinCloseLin.lean).
Here they are joined, at the first joint, where both are short.

Main names:
  `O.toC`: the second form made from O: no further oracle (E₀ := none), no further witness
    (Wpa := Unit).
  `O.full`: the step (`O.enter`), then the test on chains with the closing (`O.lkC`); the closing is
    the step to one signature, then the plan's tests (`LdLinC.cZ`, Cb/Ld/LdLinCloseLin.lean).
  `Spec.ldOLF_tail`: under the hypotheses of its statement, the step, then the test with its
    closing, is a tail from `O.P.j0` to the trivial statement, within t positions of the encoded
    index and within the same demand qa on the oracles left as the test's own theorem has. This is
    the bound that the preamble's budget has to bear.
  `Spec.ldOLF_qFam`, `Spec.ldOLF_tailF`: the same bound in the form in which a preamble's budget is
    stated (Cb/Ld/LdSendPiece.lean: `qFam`): at most t positions of the encoded index, at most b a
    long positions of each oracle message a that the preamble left.
  `Spec.ldOLF_items`: under the hypotheses of its statement, `Hiop.LinListR` ∧ `Hiop.LinKnowR` for
    `O.full`, for any bound εf on the points that are bad for the fold. `Spec.ldOLF_lin`: the same,
    with the first regime's bound put in (the first regime: `O.on0`, Cb/Obj/LdObjectLin.lean).

Limits: what is still asked, all in the statements' own text:
  the index code has a position (`Nonempty (Fin O.Cf.C₀.n)`);
  distance of the index code and radius below it;
  εf (or: `HasDist O.Cf.X.G O.Cf.C₀.d`, `O.e' ≤ O.Cf.eM`, agreement and lists at e');
  the layout's places on the cube are distinct;
  what the three sendings ask (`Sn.OK`);
  the plan: Qt : whole tests on groups, one after the other (`Qt.OK`: `LdTc.OK`,
    Cb/Ld/LdLinCloseChain.lean), which says exactly the rows that are left and what the preamble
    left (`C.Says`), and needs no more positions than the sent words bear, and of the oracles left
    only what qa allows (`O.toC.P.q5 Sn qa`);
    by `Spec.ldChain_cons`, `D.OK` and `Q.OK` give `(LdTc.cons D Q d d').OK`, and `D.OK`
    (`LdRunD.OK`, Cb/Ld/LdLinCloseRuns.lean) is: each test's evader, list, radii, and its whole
    test T is a tail (`TailTr`, Cb/Ld/LdTowerKit.lean, whose `good : GoodT` (Ior/KnowCollGood.lean)
    has `acc`, `know` and `exact` among its clauses);
  `q₀ ∅` (in `Spec.ldOLF_qFam`, `Spec.ldOLF_tailF`);
  qa is kept by subsets (in `Spec.ldOLF_sub`).
No plan is chosen (Cb/Ld/LdLinClosePlan.lean); no splitting; no tower. This file does not say that
the hypotheses can be met together: parts of a guard within a third, over two fields:
Cb/GlVal/GlToyLin.lean. One instance.


Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectLinProofs
import Cb.Ld.LdLinCloseLin
import Cb.Ld.LdSendPiece
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LdOL
variable {F E : Type} [Field F] [Field E] [Algebra F E] (O : LdOL F E)

/-- The test over a signature, made from O. -/
@[reducible] def toC : LdLinC E (Fin O.Cf.C₀.n) (Fin O.Cf.C₀.k) O.Cf.J O.Y where
  D := O.D
  Sy := O.Cf.Sg
  up := fun s r => algebraMap F E (s r)
  e' := O.e'
  t := O.t
  Sa := O.S
  E₀ := extNone
  Sta := O.Cl
  Wpa := Unit
  Ab := O.S.pred (fun cl m _ => O.more cl m) fun cl m _ => O.more cl m
  g := O.g
  ψ := O.ψ
  τ := O.τ
  rest := O.restM
  NW := O.NW
  SdW := O.SdW
  iW := O.iW
  lW := O.lW
  NU := O.NU
  SdU := O.SdU
  iU := O.iU
  lU := O.lU
  NO := O.NO
  SdO := O.SdO
  iO := O.iO
  lO := O.lO

/-- the words are copied -/
def enG : ExtMap O.P.E0 O.toC.P.E0 where
  map y := (y.1, ((), y.2))
  src q := match q with
    | .inl p => {.inl p}
    | .inr (.inl p) => p.elim
    | .inr (.inr p) => {.inr p}

/-- a demand on the positions of the oracles left, stated on the second form's oracles, read on the
words of S themselves -/
def qaIn (qa : Finset O.toC.P.Ea.Pos → Prop) : Finset O.P.Ea.Pos → Prop := fun U =>
  qa (U.map ⟨Sum.inr, Sum.inr_injective⟩)

/-- The step in front of the test. -/
def enter : IOR O.P.X0 O.P.E0 O.toC.P.X0 O.toC.P.E0 := IOR.pure some O.enG
def hEnter : O.enter.Honest O.P.W0 O.toC.P.W0 :=
  IOR.Honest.pure some O.enG fun a => (a.1, (a.2.1, (a.2.2, ())))

variable [Fintype F] [Fintype E] [Nonempty (Fin O.Cf.C₀.n)]
variable (Sn : O.toC.P.Snd)
  (εf : ℕ) (Qt : LdTc O.toC.S O.toC.E₀ O.toC.Wpa) (fq : O.toC.St6 → Qt.St) (d : O.toC.P.W0)

/-- the test on chains with its closing, as one link -/
def lkC : Link Unit (O.toC.P.J0 O.on0) LdLinP.JT :=
  O.toC.P.linC O.on0 Sn εf (O.toC.cZ Qt fq) d

/-- The test with its closing, over the configuration: the step, then the test. -/
def full : IOR (O.left.Xl × O.Cf.conf.Rec) O.left.El Unit extNone :=
  O.enter.seq (O.lkC Sn εf Qt fq d).R

def hFull0 : (O.full Sn εf Qt fq d).Honest O.P.W0 Unit :=
  O.hEnter.seq (O.lkC Sn εf Qt fq d).H
def numsF0 : IOR.Nums Unit (O.full Sn εf Qt fq d) :=
  (IOR.Nums.pure Unit some O.enG).seq (O.lkC Sn εf Qt fq d).P
def extF (d₀ : O.P.W0) :
    O.P.X0 × O.P.E0.Str → Tr (O.full Sn εf Qt fq d).shape → Unit → O.P.W0 :=
  IOR.extSeq O.enter (O.lkC Sn εf Qt fq d).R (fun _ _ w => (w.1, w.2.1))
    (O.lkC Sn εf Qt fq d).ext d₀

/-- `O.full`'s honest side and numbers, in `LinListR`'s types -/
def hFull : (O.full Sn εf Qt fq d).Honest (O.Cf.conf.PIdx × O.left.WAux) Unit :=
  IOR.Honest.mapW (O.hFull0 Sn εf Qt fq d) O.fi fun _ u => u
def numsF : LinNumsR (O.full Sn εf Qt fq d).shape :=
  ⟨(O.numsF0 Sn εf Qt fq d).err, (O.numsF0 Sn εf Qt fq d).pBad, O.t, fun _ T => T = ∅⟩

end LdOL

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- States: the step is a piece of a chain from `O.P.j0` to `O.toC.P.j0`, on the same condition (no
collision of the index at the record's seed). -/
def ldOLF_enter : Prop :=
  ∀ (O : LdOL F E) (qa : Finset O.toC.P.Ea.Pos → Prop),
    PieceTr O.enter O.hEnter (O.P.j0 O.on0) (O.toC.P.j0 O.on0) (fun _ _ w => (w.1, w.2.1))
      (Nums.pure Unit some O.enG) (O.P.q0 (O.qaIn qa)) (O.toC.P.q0 qa)

/-- States: the demand is kept by subsets if qa is. -/
def ldOLF_sub : Prop :=
  ∀ (O : LdOL F E) (qa : Finset O.toC.P.Ea.Pos → Prop),
    (∀ U V, V ⊆ U → qa U → qa V) → ∀ U V, V ⊆ U → O.qaIn qa U → O.qaIn qa V

open Classical in
/-- States, under the hypotheses below: the step, then the test with its closing, is a tail. -/
def ldOLF_tail : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (εf : ℕ) (Sn : O.toC.P.Snd)
      (qa : Finset O.toC.P.Ea.Pos → Prop) (Qt : LdTc O.toC.S O.toC.E₀ O.toC.Wpa)
      (fq : O.toC.St6 → Qt.St) (d : O.toC.P.W0) (d₀ : O.P.W0),
    O.toC.P.FoldErr O.on0 εf → Function.Injective O.py → Sn.OK → O.toC.Says Qt.base fq → Qt.OK →
    (∀ V, Qt.q V → O.toC.P.q5 Sn qa (V.biUnion O.toC.toE.src)) →
    TailTr (O.full Sn εf Qt fq d) (O.hFull0 Sn εf Qt fq d) (O.P.j0 O.on0) trivRels
      (O.extF Sn εf Qt fq d d₀) (O.numsF0 Sn εf Qt fq d) (O.P.q0 (O.qaIn qa))

/-- States: if `q₀ ∅`, the tail's bound at the demand `O.S.qFam q₀ b` is equivalent to the bound in
the form "of each oracle message at most b a long positions". -/
def ldOLF_qFam : Prop :=
  ∀ (O : LdOL F E) (q₀ : Finset extNone.Pos → Prop) (b : O.S.O → ℕ) (U : Finset O.P.E0.Pos), q₀ ∅ →
    (O.P.q0 (O.qaIn (O.S.qFam (E₀ := extNone) q₀ b)) U ↔
      O.S.qFam (E₀ := O.P.ix) (fun V => V.card ≤ O.t) b U)

open Classical in
/-- The tail, with that bound: at most t positions of the encoded index, at most b a long positions
of the oracle message a that the preamble left. -/
def ldOLF_tailF : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (εf : ℕ) (Sn : O.toC.P.Snd)
      (q₀ : Finset extNone.Pos → Prop) (b : O.S.O → ℕ) (Qt : LdTc O.toC.S O.toC.E₀ O.toC.Wpa)
      (fq : O.toC.St6 → Qt.St) (d : O.toC.P.W0) (d₀ : O.P.W0),
    q₀ ∅ → O.toC.P.FoldErr O.on0 εf → Function.Injective O.py → Sn.OK → O.toC.Says Qt.base fq →
    Qt.OK →
    (∀ V, Qt.q V → O.toC.P.q5 Sn (O.S.qFam (E₀ := extNone) q₀ b) (V.biUnion O.toC.toE.src)) →
    TailTr (O.full Sn εf Qt fq d) (O.hFull0 Sn εf Qt fq d) (O.P.j0 O.on0) trivRels
      (O.extF Sn εf Qt fq d d₀) (O.numsF0 Sn εf Qt fq d)
      (O.S.qFam (E₀ := O.P.ix) (fun V => V.card ≤ O.t) b)

open Classical in
/-- The two items of the object, for the test with its closing. -/
def ldOLF_items : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (εf : ℕ) (Sn : O.toC.P.Snd)
      (qa : Finset O.toC.P.Ea.Pos → Prop) (Qt : LdTc O.toC.S O.toC.E₀ O.toC.Wpa)
      (fq : O.toC.St6 → Qt.St) (d : O.toC.P.W0) (d0 : O.left.AMsg),
    HasDist O.Cf.C₀.G O.Cf.C₀.d → O.Cf.eM < O.Cf.C₀.d → O.toC.P.FoldErr O.on0 εf →
    Function.Injective O.py → Sn.OK → O.toC.Says Qt.base fq → Qt.OK →
    (∀ V, Qt.q V → O.toC.P.q5 Sn qa (V.biUnion O.toC.toE.src)) →
    LinListR O.left (O.full Sn εf Qt fq d) (O.hFull Sn εf Qt fq d) (O.numsF Sn εf Qt fq d) ∧
    LinKnowR O.left (O.full Sn εf Qt fq d) d0 (O.numsF Sn εf Qt fq d).err

open Classical in
/-- The same, with the fold's error of the first regime put in. -/
def ldOLF_lin : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (bad L : ℕ) (Sn : O.toC.P.Snd)
      (qa : Finset O.toC.P.Ea.Pos → Prop) (Qt : LdTc O.toC.S O.toC.E₀ O.toC.Wpa)
      (fq : O.toC.St6 → Qt.St) (d : O.toC.P.W0) (d0 : O.left.AMsg),
    HasDist O.Cf.C₀.G O.Cf.C₀.d → HasDist O.Cf.X.G O.Cf.C₀.d → O.Cf.eM < O.Cf.C₀.d →
    O.e' ≤ O.Cf.eM → O.Cf.X.MCAeq O.e' bad →
    (∀ f : O.Cf.X.Row → Fin O.Cf.C₀.n → E, ListLE (DecodesTo O.Cf.X.G O.e' f) L) →
    Function.Injective O.py → Sn.OK → O.toC.Says Qt.base fq → Qt.OK →
    (∀ V, Qt.q V → O.toC.P.q5 Sn qa (V.biUnion O.toC.toE.src)) →
    LinListR O.left (O.full Sn (bad + L * (O.Cf.X.v * Fintype.card E ^ (O.Cf.X.v - 1))) Qt fq d)
      (O.hFull Sn _ Qt fq d) (O.numsF Sn _ Qt fq d) ∧
    LinKnowR O.left (O.full Sn (bad + L * (O.Cf.X.v * Fintype.card E ^ (O.Cf.X.v - 1))) Qt fq d)
      d0 (O.numsF Sn _ Qt fq d).err

end
end Spec
end Cb
