-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Seg/HeadSteps.lean

The steps to the three statements of Policy/Seg/Head.lean: what each family's value is at a vertex,
and the assembly over `Gl.E`.

Definitions and statements, after `head_key_live`, `head_key_dead`, `head_idn_val`, `head_holds` of
Cm/TargetSegHead.lean. The proofs are in Policy/Seg/HeadForms.lean, HeadKeys.lean, HeadIdn.lean,
HeadAsm.lean and HeadProofs.lean.
`segKey np t H y f a i` is the value that family f is to have at the vertex of (a, i): the
relation's key `LedgerHead.key`, at HD0 times the inverse of 2^23 in `Gl.E`. The statements say: ρ,
ρC, NB and the checked tokens are the same at `Cm.reqOf x` and at `Head.Req.of pol x`; what the
forms `cEx`, `cHid`, `cHe` are worth at matrices A; a family of keys has the value `segKey` at a
live vertex and the image of an entry of its table at a dead one; the 17 identities and the ledger's
four have the relation's values; and the assembly, `Spec.headPol_holds`.
Live and dead vertices, `va`, `vOf`: Cm/SegHead.lean.

Limits: definitions and statements only. Nothing on the request's form, on bounds of cells, or on
protocols.
-/
import Policy.Seg.Head
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Policy
open Cb Inst.Model Finset Cm.Seg Cm.Seg.Ex

/-- The value of the segment's family f at the vertex of (a, i): the relation's key; at HD0 divided
by 2^23. -/
def segKey (np : NormPar) (t : Head.Cells Gl.E) (H : ℕ → ℕ → Gl.E) (y : Head.Req) :
    Head.Fam → ℕ → ℕ → Gl.E
  | .HD0, a, i => ((2 : Gl.E) ^ 23)⁻¹ * LedgerHead.key np t H y .HD0 a i
  | f, a, i => LedgerHead.key np t H y f a i

namespace Spec

/-- States: ρ, ρC, NB and the checked tokens are the same at `Cm.reqOf x` and at
`Head.Req.of pol x`, for every policy pol. -/
def headPol_req : Prop :=
  ∀ (pol : AcceptancePolicy) (x : XI),
    (∀ i, (Cm.reqOf x).rho i = (Head.Req.of pol x).rho i) ∧
    (∀ i, (Cm.reqOf x).rhoC i = (Head.Req.of pol x).rhoC i) ∧
    (Cm.reqOf x).NB = (Head.Req.of pol x).NB ∧
    (Cm.reqOf x).win = (Head.Req.of pol x).win

/-- States: at matrices A the form `cEx v i` has the value `Head.ex` at the cells `TS.tH A`. -/
def headPol_cEx_val : Prop :=
  ∀ (A : ℕ → ℕ → ℕ → Gl.E) (v i : ℕ), (cEx v i).val A = Head.ex (TS.tH A) v i

/-- States: the form `cHid a n i` has the value `Ledger.b256` of the bytes `Head.Dv` at position i,
n bytes from byte a on. -/
def headPol_cHid_val : Prop :=
  ∀ (A : ℕ → ℕ → ℕ → Gl.E) (a n i : ℕ),
    (cHid a n i).val A = Ledger.b256 (fun m => Head.Dv (TS.tH A) m i) a n

/-- States: the form `cHe v i` has the value d1 + 2^16 ex at the token v and the position i. -/
def headPol_cHe_val : Prop :=
  ∀ (A : ℕ → ℕ → ℕ → Gl.E) (v i : ℕ),
    (cHe v i).val A = Head.d1 (TS.tH A) v i + 2 ^ 16 * Head.ex (TS.tH A) v i

/-- States: at the vertex of (a, i), a < `Head.len f`, i < `Head.nT`, the value of the family f of
keys is `segKey` at (`TS.tH A`, `TS.HW W`, `Head.Req.of pol x`), for every policy pol. -/
def headPol_key_live : Prop :=
  ∀ (np : NormPar) (pol : AcceptancePolicy) (f : Head.Fam) (x : XI) (W : ℕ → ℕ → Gl.F)
      (A : ℕ → ℕ → ℕ → Gl.E) (a i : ℕ),
    a < Head.len f → i < Head.nT →
    (keyFamPol np f).val TS.fmtRef x W A (vOf a i) =
      segKey np (TS.tH A) (TS.HW W) (Head.Req.of pol x) f a i

/-- States: at a vertex whose index is not below `Head.len f` the value of the family f of keys is
the image of an entry of the family's table. -/
def headPol_key_dead : Prop :=
  ∀ (np : NormPar) (f : Head.Fam) (x : XI) (W : ℕ → ℕ → Gl.F) (A : ℕ → ℕ → ℕ → Gl.E) (b : ℕ),
    b < 2 ^ (vxPol f + 10) → Head.len f ≤ va (vxPol f) b →
    ∃ u ∈ (keyTabPol f).set, (keyFamPol np f).val TS.fmtRef x W A b = algebraMap Gl.F Gl.E u

/-- States: at the vertex i < `Head.nT` the value of identity k of the final normalisation is
`Head.N.idn` at the cells `TS.tH A`. -/
def headPol_idn_val : Prop :=
  ∀ (np : NormPar) (k : ℕ) (x : XI) (W : ℕ → ℕ → Gl.F) (A : ℕ → ℕ → ℕ → Gl.E) (i : ℕ),
    i < Head.nT → (TS.idnFam np k).val TS.fmtRef x W A i = Head.N.idn np (TS.tH A) i k

/-- States: the values of the ledger's four identities are `Head.dB4`, `Head.dZ` at the vertex
i < `Head.nT`, and `Head.sB2`, `Head.sB3` at the one vertex 0. -/
def headPol_led_val : Prop :=
  ∀ (pol : AcceptancePolicy) (x : XI) (W : ℕ → ℕ → Gl.F) (A : ℕ → ℕ → ℕ → Gl.E),
    (∀ i < Head.nT,
      (jB4Fam pol).val TS.fmtRef x W A i = Head.dB4 (TS.tH A) (Head.Req.of pol x) i ∧
      jZFam.val TS.fmtRef x W A i = Head.dZ (TS.tH A) (Head.Req.of pol x) i) ∧
    (sB2Fam pol).val TS.fmtRef x W A 0 = Head.sB2 (TS.tH A) (Head.Req.of pol x) ∧
    (sB3Fam pol).val TS.fmtRef x W A 0 = Head.sB3 (TS.tH A) (Head.Req.of pol x)

/-- States the assembly: the segment's conditions hold at (x, W, A) if and only if every key of the
relation at (`TS.tH A`, `TS.HW W`) is the image of an entry of the relation's table, and the 17
identities and the ledger's four are 0. -/
def headPol_holds : Prop :=
  ∀ (s : Cm.Scales) (pol : AcceptancePolicy) (x : XI) (W : ℕ → ℕ → Gl.F) (A : ℕ → ℕ → ℕ → Gl.E),
    (segHeadPol s pol).Holds TS.fmtRef x W A ↔
    (∀ f a i, a < Head.len f → i < Head.nT →
      ∃ u < (LedgerHead.tableOf f).rows,
        LedgerHead.key s.nf (TS.tH A) (TS.HW W) (Head.Req.of pol x) f a i =
          algebraMap Gl.F Gl.E (((LedgerHead.tableOf f).row u : ℤ) : Gl.F)) ∧
    (∀ i < Head.nT, ∀ k < 17, Head.N.idn s.nf (TS.tH A) i k = 0) ∧
    (∀ i < Head.nT,
      Head.dB4 (TS.tH A) (Head.Req.of pol x) i = 0 ∧
      Head.dZ (TS.tH A) (Head.Req.of pol x) i = 0) ∧
    (Head.sB2 (TS.tH A) (Head.Req.of pol x) = 0 ∧ Head.sB3 (TS.tH A) (Head.Req.of pol x) = 0)

end Spec

end Policy
