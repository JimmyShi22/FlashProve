-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectStd.lean: for toys: the smallest object, which fills the frame's five terms with two
real tests and three null terms; its `LdObj.OK` from conditions on codes and on the model.


Definitions, statements and proofs. A tool for a guard against emptiness; no parameter of a
protocol.
The frame is the record `LdObj` (Cb/Obj/LdObject.lean): it takes, as its five terms, any value of
each of five kinds.

Main names:
  `StdObj Cf Pl Pk`: Lo: the data of the test of the offline phase (any claims); Ln: the data of the
    online phase (all its claims have trivial rows, by `T.Hyp`); cl₀, cl₁: the claims that
    weights-formedness and a request write; Lk: the link's data.
  `T.Hyp`: all that is asked of T, among it: conditions on the index code; `Lo.Hyp`
    (Cb/Obj/LdObjectLinStd.lean); the link's conditions (Cb/Obj/LdObjectLinkStd.lean: those of
    `ldOl_std` but `Cf.OK`); the rows of cl₀ and of all claims of Ln are trivial; every message
    holds an index; every cell value is a witness in Rno.
  In the statement `Fin Cf.C₀.n`, Pl and Pk are non-empty (instance binders).
  `Spec.stdObj_ok`: `Cf.OK L₀` and `T.Hyp` ⇒ `T.obj.OK L₀`.



Why: where the hypotheses of `Spec.stdObj_ok` are met, this file shows that the frame's
conditions are consistent: the types of the five kinds, the two "what a preamble leaves" and the
two lines on budgets can be met together, with two real
tests among the terms.

Limits: degenerate, and declared so. Of the five terms of the frame:
  lin: real: the test for linear constraints on the encoded index at one instance, with standard
    parts and its closing (Cb/Obj/LdObjectLinStd.lean). At the claim that weights-formedness writes
    here it proves: the encoded index decodes.
  link: real: the link between two encoded indices, with standard parts and its closing
    (Cb/Obj/LdObjectLinkStd.lean).
  wf, req, linB: null: without rounds (Cb/Obj/LdObjectNull.lean): the two preambles write a claim
    whose row reads nothing of the index; the batch test accepts. The online phase has no round.
    That the rows read nothing is a hypothesis (`T.Hyp`: `triv₀`, `triv`).
This file does not show that the lots' own terms for weights-formedness, for a request and for the
batch test meet the frame's conditions, alone or together. This file shows nothing about a model
that is not trivial.
Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectNull
import Cb.Obj.LdObjectLinkStd
import Cb.Obj.LdObjectProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The smallest object: the data. -/
structure StdObj {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (Cf : LdCf F E) (Pl Pk : Type) [Fintype Pl] [Fintype Pk] where
  Lo  : StdLn Cf Pl
  cl₀ : Lo.Cl
  Ln  : StdLn Cf Pl
  cl₁ : Ln.Cl
  Lk  : StdLk Cf Pk
  N   : ℕ
  /-- the numbers of the test: exceptional coefficients and list at the fold's radius; lists of the
  sent messages; positions that their encodings bear -/
  badF : ℕ
  LF   : ℕ
  L    : ℕ
  tW   : ℕ
  tU   : ℕ
  tO   : ℕ
  /-- the numbers of the link -/
  ε₀ : ℕ
  ε₁ : ℕ
  Ll : ℕ
  tl : ℕ
  /-- fixed values -/
  z0 : Cf.conf.PIdx
  c0 : Cf.conf.Cells

namespace StdObj
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
  {Cf : LdCf F E} [Nonempty (Fin Cf.C₀.n)] {Pl Pk : Type} [Fintype Pl] [Fintype Pk]
  [Nonempty Pl] [Nonempty Pk] (T : StdObj Cf Pl Pk)

/-- The bound on the fold's bad points, first regime (`Spec.ldLin_foldErr`, Cb/Ld/LdLin.lean). -/
def εf : ℕ := T.badF + T.LF * (Cf.X.v * Fintype.card E ^ (Cf.X.v - 1))

/-- fixed witnesses -/
def wLo : T.Lo.Od.ol.P.W0 := (fun _ _ => 0, fun a => a.elim)
def wLn : T.Ln.Od.ol.P.W0 := (fun _ _ => 0, fun a => a.elim)
def wK0 : T.Lk.K.P.W0 := (fun _ _ => 0, fun _ _ => 0)
def wK2 : T.Lk.K.P.W2 := (fun _ => (fun _ => 0, fun _ => 0), T.wK0)

/-- The test at one instance, as a term of the frame. -/
def lin : T.Lo.Od.ol.LinT where
  Q := T.Lo.O.full (T.Lo.Sn T.L T.tW T.tU T.tO) T.εf T.Lo.T.Q T.Lo.T.fq T.Lo.w0
  H := T.Lo.O.hFull0 (T.Lo.Sn T.L T.tW T.tU T.tO) T.εf T.Lo.T.Q T.Lo.T.fq T.Lo.w0
  ext := T.Lo.O.extF (T.Lo.Sn T.L T.tW T.tU T.tO) T.εf T.Lo.T.Q T.Lo.T.fq T.Lo.w0 T.wLo
  N := T.Lo.O.numsF0 (T.Lo.Sn T.L T.tW T.tU T.tO) T.εf T.Lo.T.Q T.Lo.T.fq T.Lo.w0
  qi := T.Lo.O.P.q0 (T.Lo.O.qaIn fun _ => True)

/-- The object. -/
def obj : LdObj F E where
  Cf := Cf
  off := T.Lo.Od
  on := T.Ln.Od
  K := T.Lk.K
  N := T.N
  Kw := Unit
  Kr := Unit
  wf := T.Lo.nullWf T.cl₀ T.z0
  lin := T.lin
  link := T.Lk.K.full (T.Lk.S T.Ll T.tl) T.ε₀ T.ε₁ T.Lk.Kc T.wK2 T.wK0
  req := T.Ln.nullReq T.cl₁ T.c0
  linB := T.Ln.nullLinB T.N T.wLn
  cw := fun _ => ()
  cr := fun _ => ()
  z0 := T.z0
  r0 := fun a => a.elim
  dOff := fun a => a.elim
  dOn := fun a => a.elim

/-- All that is asked of T. -/
structure Hyp : Prop where
  distX : HasDist Cf.X.G Cf.C₀.d
  rad   : Cf.eM < Cf.C₀.d
  /-- the test -/
  e'    : T.Lo.e' ≤ Cf.eM
  mca   : Cf.X.MCAeq T.Lo.e' T.badF
  list  : ∀ f : Cf.X.Row → Fin Cf.C₀.n → E, ListLE (DecodesTo Cf.X.G T.Lo.e' f) T.LF
  py    : Function.Injective T.Lo.py
  lo    : T.Lo.Hyp T.L T.tW T.tU T.tO
  /-- the link -/
  fold  : T.Lk.K.P.FoldErr T.Lk.K.free T.Lk.K.free T.ε₀ T.ε₁
  pl    : Function.Injective T.Lk.pl
  mOK   : T.Lk.M.OK T.Ll T.tl
  mDist : T.Lk.M.Cm.Dist T.Lk.d
  mTr   : T.Lk.M.Cm.Transparent
  mRad  : T.Lk.M.e < T.Lk.d
  kLc   : ∀ C : LdCode E Pk, C.Laws → C.Dist T.Lk.d → C.ListAt T.Lk.M.e T.Lk.Lc
  kL2   : ∀ C : LdCode E Pk, C.Laws → C.Dist T.Lk.d → C.ListAt T.Lk.M.e T.Lk.L2
  kMca  : ∀ C : LdCode E Pk, C.Laws → C.MCAat T.Lk.M.e T.Lk.bad
  kPos  : T.Lk.tb ≤ T.tl
  /-- the null terms -/
  triv₀ : T.Lo.Triv T.cl₀
  triv  : ∀ cl, T.Ln.Triv cl
  held  : ∀ U, (Cf.conf.held U).isSome
  rno   : ∀ i x c, Cf.conf.Rno i x c

end StdObj

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def stdObj_ok : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (Pl Pk : Type) [Fintype Pl] [Fintype Pk] [Nonempty Pl]
      [Nonempty Pk] (T : StdObj Cf Pl Pk) (L₀ : ℕ),
    Cf.OK L₀ → T.Hyp → T.obj.OK L₀

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

open Classical in
theorem stdObj_ok : Spec.stdObj_ok F E := by
  intro Cf _ Pl Pk _ _ _ _ T L₀ hC h
  exact
    { conf := hC
      wf := stdLn_nullWf T.Lo T.cl₀ T.z0 h.triv₀ h.held
      lin :=
        { tail := ldOLF_tail F E T.Lo.O T.εf (T.Lo.Sn T.L T.tW T.tU T.tO) (fun _ => True)
            T.Lo.T.Q T.Lo.T.fq T.Lo.w0 T.wLo
            (ldLin_foldErr T.Lo.O.toC.P Cf.C₀.d T.badF T.LF h.distX h.rad h.e' h.mca h.list)
            h.py (stdLn_snd T.Lo h.lo.okW h.lo.okU h.lo.okO) stdLn_says
            (stdLn_q h.lo) (stdLn_demand h.lo)
          reads := ldOL_reads F E T.Lo.O _ }
      fitsK := ⟨fun _ _ _ h => h, fun _ _ h => h⟩
      link := ldLkC_tail _ _ _ _ _ T.Lk.K.P T.Lk.K.free T.Lk.K.free T.ε₀ T.ε₁ (T.Lk.S T.Ll T.tl)
        T.Lk.Kc T.wK2 T.wK0 h.fold h.pl (stdLk_snd T.Lk h.mOK)
        (stdLk_cl T.Lk h.mOK h.mDist h.mTr h.mRad h.kLc h.kL2 h.kMca) fun _ => h.kPos
      req := stdLn_nullReq T.Ln T.cl₁ T.c0 (h.triv T.cl₁) h.rno
      linB := stdLn_nullLinB T.Ln T.N T.wLn h.triv
      fitOff := fun _ _ => trivial
      fitOn := fun _ _ => trivial }

end
end Cb
