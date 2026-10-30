-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdHonOnB.lean: the honest items of the test for linear constraints at N instances
(`T : O.LinBT N`, Cb/Obj/LdObjectOnB.lean; `O.termT` at a closing cZ, Cb/Obj/LdObjectOnBTerm.lean)
do not read the round errors: they pass from a closing to every closing that agrees with it off the
errors.

Definitions, statements (in `Cb.Spec`) and proofs. Generic: variable O, variable closings. Nothing
assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.
Closings cZ, cZ' agree off the errors if cZ.full = cZ'.full (`ChainV.full`,
Cb/Gen/FullErrChainV.lean: every `LinkV`'s round errors overwritten by the full list). The full list
(`Err.full`, Cb/Gen/FullErr.lean) has, for each round, the number of all values of that round's
verifier message: as a probability, the error 1.

Why: it gives the session's clause of the honest half (linOn of `SubsR.HypH`, Hiop/RecBuild.lean):
if some closing that agrees with cZ off the errors meets the six conditions of `Cb.ldOnT_ok` on a
closing, and that theorem's other premises hold, the term at cZ itself has all honest items.

Main names:
  `T.OKH` (the honest items): `T.OK`'s clauses but fits and know, word for word: point, isLocal,
    coherent, tied, idxShared, idxReads, acc, exact, bud0, prBad, bridge, reads, mono.
  `Spec.ldHonB_ofOK`: `T.OK` → `T.OKH`.
  `Spec.ldHonB_full`: `T.full.OKH ↔ T.OKH`: field by field, by unfolding: no clause reads the
    errors.
  `Spec.ldHonB_list`: `T.OKH` → `Hiop.LinBListR O.left T.Q T.hQ N T.P` (by `Hiop.rec_linB_list`, as
    in `Cb.ldOBT_object`).
  `O.termOfV v pw`: the term read off one link v with the honest side of a batch, its errors the
    full list, pw its bound on the withheld set.
  `Spec.ldHonB_term`, for `Fin O.Cf.C₀.n` nonempty: cZ.full = cZ'.full → the terms `O.termT` at cZ
    and at cZ' have the same `full`.
  `Spec.ldHonB_carry`, for `Fin O.Cf.C₀.n` nonempty: cZ.full = cZ'.full → `OK` of `O.termT` at cZ' →
    `OKH` of `O.termT` at cZ.

Limits: this file says nothing on the chance of a cheating prover at cZ. It does not say that such a
closing exists (for `R : LdObjRp` (Cb/Obj/LdObjectPpRows.lean), cZ := `R.toPp.cZ`, cZ' :=
`R.fullB.toPp.cZ`: `ldHonEq_obj`, Cb/Ld/LdHonPlanEq.lean; `ldHonF_term`, Cb/Ld/LdHonPlanFull.lean,
under its hypotheses). It says nothing on a protocol. This file says nothing on the value of any
number.

Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.FullErrChainV
import Cb.Obj.LdObjectOnBTermProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR
open scoped ENNReal

namespace LdOL
section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] {O : LdOL F E} {N : ℕ}

/-- the term with the full list for its batch errors -/
def LinBT.full (T : O.LinBT N) : O.LinBT N := { T with P := { T.P with err := Err.full T.R.shape } }

open Classical in
/-- `T.OK`'s clauses but fits and know. -/
structure LinBT.OKH (T : O.LinBT N) : Prop where
  point    : Nonempty T.R.shape.IsPoint
  isLocal  : T.R.IsLocal
  coherent : T.A.Coherent
  tied     : T.R.Tied
  idxShared : ∀ ρ ρ', Rho.sh T.A ρ = Rho.sh T.A ρ' →
    (T.R.extReads ρ).filter (fun p => p.isLeft) = (T.R.extReads ρ').filter (fun p => p.isLeft)
  idxReads : ∀ ρ, ((T.R.extReads ρ).filter fun p => p.isLeft).card ≤ T.P.q
  acc      : T.H.AccV T.RiV T.RoV
  exact    : T.H.ExactV N T.RiV T.P.bud
  bud0     : ∀ J ρs, T.P.bud J ρs fun _ => ∅
  prBad    : prRho T.H.withheld ≤ T.P.pBad
  bridge   : ∀ x y w, O.left.Rlin x y w → T.RiV x y (w.1, T.mkW w.1 w.2)
  reads    : ∀ ρ, T.qi (T.R.given ρ ∅) ∧ T.R.extReads ρ ⊆ T.R.given ρ ∅
  mono     : ∀ U V, V ⊆ U → T.qi U → T.qi V

end

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] (O : LdOL F E) [Fintype F]
  [Fintype E] [Nonempty (Fin O.Cf.C₀.n)]
variable (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop)
  (qa : Finset O.toC.P.Ea.Pos → Prop) (N : ℕ) {VT : JV N LdLinP.JT}

/-- the term read off one link with the honest side of a batch; its errors: the full list -/
def termOfV (v : LinkV Unit N (O.VIn on0 qa N) VT) (pw : ℝ≥0∞) : O.LinBT N where
  R := v.a.l.R
  A := v.a.ann
  Wi := O.P.W0
  W0' := VT.W0
  Wo := Unit
  H := v.hv
  mkW := fun p a => O.fi (p, a)
  RiV := (O.VIn on0 qa N).rel
  RoV := VT.rel
  P := ⟨Err.full v.a.l.R.shape, pw, O.t, fun _ _ Ts => ∀ j, Ts j = ∅⟩
  on0 := on0
  ext := v.a.l.ext
  qi := O.P.q0 (O.qaIn qa)

end
end LdOL

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldHonB_ofOK : Prop := ∀ (O : LdOL F E) (N : ℕ) (T : O.LinBT N), T.OK → T.OKH

def ldHonB_full : Prop := ∀ (O : LdOL F E) (N : ℕ) (T : O.LinBT N), T.full.OKH ↔ T.OKH

def ldHonB_list : Prop :=
  ∀ (O : LdOL F E) (N : ℕ) (T : O.LinBT N), T.OKH → LinBListR O.left T.Q T.hQ N T.P

def ldHonB_term : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)]
      (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop) (Sn : O.toC.P.Snd)
      (qa : Finset O.toC.P.Ea.Pos → Prop) (εf N : ℕ) (VT : JV N LdLinP.JT)
      (cZ cZ' : ChainV Unit N (O.toC.P.V6 Sn qa N) VT) (d : O.toC.P.W0) (d₀ : O.P.W0),
    cZ.full = cZ'.full →
    (O.termT on0 Sn qa εf N cZ d d₀).full = (O.termT on0 Sn qa εf N cZ' d d₀).full

/-- States, for `Fin O.Cf.C₀.n` nonempty: the honest items pass to every closing that agrees off
the errors: if cZ.full = cZ'.full and the term at cZ' has `OK`, the term at cZ has `OKH`. -/
def ldHonB_carry : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)]
    (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop) (Sn : O.toC.P.Snd)
    (qa : Finset O.toC.P.Ea.Pos → Prop) (εf N : ℕ) (VT : JV N LdLinP.JT)
    (cZ cZ' : ChainV Unit N (O.toC.P.V6 Sn qa N) VT) (d : O.toC.P.W0) (d₀ : O.P.W0), cZ.full = cZ'.full → (O.termT on0 Sn qa εf N cZ' d d₀).OK → (O.termT on0 Sn qa εf N cZ d d₀).OKH

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

omit [Fintype E] in
theorem ldHonB_ofOK : Spec.ldHonB_ofOK F E := fun _ _ _ h =>
  { point := h.point, isLocal := h.isLocal, coherent := h.coherent, tied := h.tied,
    idxShared := h.idxShared, idxReads := h.idxReads, acc := h.acc, exact := h.exact,
    bud0 := h.bud0, prBad := h.prBad, bridge := h.bridge, reads := h.reads, mono := h.mono }

omit [Fintype E] in
theorem ldHonB_full : Spec.ldHonB_full F E := fun _ _ _ =>
  ⟨fun h =>
      { point := h.point, isLocal := h.isLocal, coherent := h.coherent, tied := h.tied,
        idxShared := h.idxShared, idxReads := h.idxReads, acc := h.acc, exact := h.exact,
        bud0 := h.bud0, prBad := h.prBad, bridge := h.bridge, reads := h.reads, mono := h.mono },
    fun h =>
      { point := h.point, isLocal := h.isLocal, coherent := h.coherent, tied := h.tied,
        idxShared := h.idxShared, idxReads := h.idxReads, acc := h.acc, exact := h.exact,
        bud0 := h.bud0, prBad := h.prBad, bridge := h.bridge, reads := h.reads, mono := h.mono }⟩

omit [Fintype E] in
theorem ldHonB_list : Spec.ldHonB_list F E := fun O N T h =>
  rec_linB_list O.Cf.conf O.left T.R T.A T.Wi T.W0' T.Wo T.H T.mkW T.RiV T.RoV N T.P h.point
    h.isLocal h.coherent h.tied h.idxShared h.idxReads h.acc h.exact h.bud0 h.prBad h.bridge

theorem ldHonB_term : Spec.ldHonB_term F E := by
  intro O _ on0 Sn qa εf N VT cZ cZ' d d₀ h
  have hc : ((O.toC.P.chainV Sn qa N on0 εf).append cZ).full =
      ((O.toC.P.chainV Sn qa N on0 εf).append cZ').full := by
    rw [chainVFull_append, chainVFull_append, h]
  have hl : (O.toC.P.linCV Sn qa N on0 εf cZ d).full = (O.toC.P.linCV Sn qa N on0 εf cZ' d).full :=
    chainVFull_linkOf hc d
  have hv : (O.termV on0 Sn qa εf N cZ d d₀).full = (O.termV on0 Sn qa εf N cZ' d d₀).full := by
    show ((O.lvE on0 qa N).seq (O.toC.P.linCV Sn qa N on0 εf cZ d) d₀).full =
      ((O.lvE on0 qa N).seq (O.toC.P.linCV Sn qa N on0 εf cZ' d) d₀).full
    rw [linkVFull_seq, hl, ← linkVFull_seq]
  have hw : cZ.pWh = cZ'.pWh := by rw [← chainVFull_wh, h, chainVFull_wh]
  have e : ∀ c : ChainV Unit N (O.toC.P.V6 Sn qa N) VT, (O.termT on0 Sn qa εf N c d d₀).full =
      O.termOfV on0 qa N (O.termV on0 Sn qa εf N c d d₀).full c.pWh := fun _ => rfl
  rw [e, e, hv, hw]

theorem ldHonB_carry : Spec.ldHonB_carry F E := fun O _ on0 Sn qa εf N VT cZ cZ' d d₀ h hk =>
  (ldHonB_full F E O N _).1
    (ldHonB_term F E O on0 Sn qa εf N VT cZ cZ' d d₀ h ▸
      (ldHonB_full F E O N _).2 (ldHonB_ofOK F E O N _ hk))

end
end Cb
