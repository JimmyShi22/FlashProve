-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdHonSide.lean: four things on the object at the technical report's plan, beside its
parameter lists, follow here from the hypotheses named below,
without the records that hold the tests' knowledge side. The four: the format of the batch test's
closing, countability, a list of bits that fits the shapes, the configuration in order. The
hypotheses: `Z.IsTow`, `Z.FinZp`, `Z.KapW ws κ`, `V.HypJ` and the other premises under
"Main names:".

Definitions, statements (in `Cb.Spec`) and proofs. Generic: any finite fields F, Fp and any finite
field E that is an algebra over both. Nothing assumed beyond the hypotheses of the statements and
whatever the arguments hold as proofs.
Countability: positions, symbols and plain parts of every round are countable (`CtbSh`,
CompileK/ImplCountable.lean; of the object: `LdObjPp.CtbPp`, Cb/Obj/LdObjectCtbPaper.lean;
`LdObjT.CtbT`, Cb/Obj/LdObjectCtbTerms.lean).

Why: the library's other proofs of these four take `P.Hyp L`, `Z.HypRefPP` or
`Z.HypRefPJ` whole (Cb/Obj/LdObjectFmtPaper.lean, Cb/Obj/LdObjectCtbPaper.lean;
the last two: Cb/Ld/LdKappaPp.lean, proved in Cb/Ld/LdKappaPpProofs.lean):
records in which each of the session's four whole tests is "in order", knowledge side included. What
they draw from these records is little, among it: an equation of chains that holds without them, and
for each of the nine whole tests the equation "the test's term is its tower's".

Main names:
  `Z.IsTow`: nine equations: the whole test of the link's closing, and each of the four whole tests
    of the offline test's and of the session's closing, is the term of its tower.

  `Spec.ldHon_forget`: the online closing, its honest side forgotten, is the annotated chain of the
    plan: no premise beside whatever the argument `P` holds as proofs, among them `same'`
    (`ldObjPp_forget`, Cb/Obj/LdObjectFmtPaper.lean, takes `P.Hyp L`).
  `Spec.ldHon_runs`: so: the closing runs in the format's phases as its rest does:
    `P.cA'.Runs .aft ph'` → `P.toT.cZ.forget.Runs .shr ph'`.
  `Spec.ldHon_ctbT`: `P.CtbPp` → `P.toT.CtbT`.
  `Spec.ldHon_ctbPp`: "which terms stand for weights-formedness" (the equation of pairs ⟨`Z.R.W`,
    `Z.R.Bw`⟩ = ⟨`Z.Zw.W`, `Z.Zw.G.B`⟩), `Z.IsTow`, `Z.FinZp` ⇒ `Z.R.toPp.CtbPp`.
  `Spec.ldHon_below`: `Z.IsTow`, `Z.KapW ws κ`, the request's rounds at most κ with proof of work ⇒
    every round of the five lists is at most κ with the bits `Z.bitsP ws`. A statement on numbers:
    the error lists are terms of the object; that they are errors of anything is not said.
  `Spec.ldHon_wfRound`, `Spec.ldHon_reqBits`: the preamble of weights-formedness has a round (its
    last link is a batching, which begins with a draw); a request's list of bits is not empty (its
    first link is a sending): for all data.
  `Spec.ldHon_conf`: E of characteristic p, weights-formedness' own hypotheses (`V.HypJ p Z.δ.dS`,
    Cb/Obj/LdObjectDataRefJ.lean), "which terms stand" ⇒ the configuration is in order at lists of
    one member: `Z.R.W.Cf.OK 1`.

Limits: this file says nothing on the parameter lists. It says nothing on a protocol's soundness,
completeness or hiding. It does not say that `Z.IsTow`, `Z.FinZp`, `Z.KapW` hold of any object.

Terms: lean/GLOSSARY.md.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
import Cb.Gl.GlFinalPpP
import Cb.Ld.LdKappaPpProofs
import Cb.Obj.LdObjectCtbPaper

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR
open scoped ENNReal

/-- the whole test of D is the term of the tower T -/
def LdRunD.IsT {E : Type} [Field E] [Fintype E] {S : Sig E} (D : LdRunD S) (T : D.Tow) : Prop :=
  D.T = T.toEnd

/-- each of the nine whole tests is the term of its tower -/
structure LdObjZp.IsTow {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] (Z : LdObjZp F E) : Prop where
  tK  : Z.R.Kc.run.IsT (Z.R.Kc.run.up3 Z.twK)
  t₁  : Z.R.TP₀.D₁.IsT (Z.R.TP₀.D₁.up3 Z.tw₁)
  t₂  : Z.R.TP₀.D₂.IsT (Z.R.TP₀.D₂.up3 Z.tw₂)
  t₃  : Z.R.TP₀.D₃.IsT (Z.R.TP₀.D₃.up3 Z.tw₃)
  t₄  : Z.R.X.run.IsT (Z.R.X.run.up3 Z.tw₄)
  t₁B : Z.R.TB₀.D₁.IsT (Z.R.TB₀.D₁.upJ Z.tw₁B)
  t₂B : Z.R.TB₀.D₂.IsT (Z.R.TB₀.D₂.upJ Z.tw₂B)
  t₃B : Z.R.TB₀.D₃.IsT (Z.R.TB₀.D₃.upJ Z.tw₃B)
  t₄B : Z.R.XB.run.IsT (Z.R.XB.run.upJ Z.tw₄B)

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldHon_forget : Prop :=
  ∀ P : LdObjPp F E, P.cZ.forget = P.on.ol.toC.cZA (P.TB.QA P.cA' P.same') (P.on.ol.toC.fqP P.TB.fa)

def ldHon_runs : Prop :=
  ∀ (P : LdObjPp F E) (ph' : FPhase), P.cA'.Runs .aft ph' → P.toT.cZ.forget.Runs .shr ph'

def ldHon_ctbT : Prop := ∀ P : LdObjPp F E, P.CtbPp → P.toT.CtbT

def ldHon_ctbPp : Prop :=
  ∀ Z : LdObjZp F E, (⟨Z.R.W, Z.R.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨Z.Zw.W, Z.Zw.G.B⟩ →
    Z.IsTow → Z.FinZp → Z.R.toPp.CtbPp

def ldHon_below : Prop :=
  ∀ (Z : LdObjZp F E) (ws : LdWk4) (κ : ℝ≥0∞),
    Z.IsTow → Z.KapW ws κ → Z.R.r.BelowW ws.ins κ → Z.R.toPp.toT.obj.nums.BelowB (Z.bitsP ws) κ

def ldHon_wfRound : Prop := ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (B : P.Blk), B.link.R.shape ≠ []

def ldHon_reqBits : Prop :=
  ∀ (Kc : Type) (a z : LdStage E Kc) (r : LdReq a z) (w : ℕ), r.bits w ≠ []

def ldHon_conf : Prop :=
  ∀ (Fp : Type) [Field Fp] [Fintype Fp] [Algebra Fp E] (p : ℕ) [CharP E p] (Z : LdObjZp F E)
      [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (V : Z.Zw.StdW Fp),
    V.HypJ p Z.δ.dS →
    (⟨Z.R.W, Z.R.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨Z.Zw.W, Z.Zw.G.B⟩ → Z.R.W.Cf.OK 1

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldHon_forget : Spec.ldHon_forget F E := fun P =>
  (ldLinV_cZ_same E _ _ _ _ P.on.ol.toC P.N (P.TB.QA P.cA' P.same')
    (P.on.ol.toC.fqP P.TB.fa) _ _ _ _).1

theorem ldHon_runs : Spec.ldHon_runs F E := by
  intro P ph' hA
  show P.cZ.forget.Runs .shr ph'
  rw [ldHon_forget F E P]
  exact ldPlanP_runs E _ _ _ _ P.on.ol.toC P.pB P.TB P.cA' P.same' ph' hA

theorem ldHon_ctbT : Spec.ldHon_ctbT F E := fun P c =>
  { inst := c.inst, wf := c.wf, nW := c.nW, nU := c.nU, nO := c.nO
    plan := ldPlanP_ctb P.W.O.toC P.p P.TP c.t₁ c.t₂ c.t₃ c.rest
    nK := c.nK, tK := c.tK, req := c.req, nWB := c.nWB, nUB := c.nUB, nOB := c.nOB
    cz := by
      show P.cZ.forget.CtbA
      rw [ldHon_forget F E P]
      exact ldPlanP_ctbA P.on.ol.toC P.pB P.TB P.cA' P.same' c.t₁B c.t₂B c.t₃B c.restB }

/-- A test whose whole test is a tower (`e`) with `D.TowFin T` (`hT`) has `CtbSh` of that test's
shape. -/
theorem ldHon_ctbRun {E : Type} [Field E] [Fintype E] {S : Sig E} {D : LdRunD S} {T : D.Tow}
    (e : D.T = T.toEnd) (hT : D.TowFin T) : CtbSh D.T.R.shape := by
  rw [e]
  exact ctb_towG T hT

theorem ldHon_ctbPp : Spec.ldHon_ctbPp F E := fun Z hw h c =>
  { inst := c.inst
    wf := ldObjZ_ctbWf Z.Zw c.sP ⟨Z.R.W, Z.R.Bw⟩ hw
    nW := c.nW, nU := c.nU, nO := c.nO
    t₁ := ldHon_ctbRun h.t₁ c.t₁, t₂ := ldHon_ctbRun h.t₂ c.t₂, t₃ := ldHon_ctbRun h.t₃ c.t₃
    rest := ctb_cons Z.R.X.run _ Z.R.X.d Z.R.X.d' (ldHon_ctbRun h.t₄ c.t₄) (ctb_nil _ _ _ _)
    nK := c.nK
    tK := ldHon_ctbRun h.tK c.tK
    req := ctb_req Z.R.r c.req
    nWB := c.nWB, nUB := c.nUB, nOB := c.nOB
    t₁B := ldHon_ctbRun h.t₁B c.t₁B,
      t₂B := ldHon_ctbRun h.t₂B c.t₂B,
      t₃B := ldHon_ctbRun h.t₃B c.t₃B
    restB :=
      ctbA_consLo Z.R.XB.run _ Z.R.XB.d Z.R.XB.d' (ldHon_ctbRun h.t₄B c.t₄B) (ctbA_tcNil _ _ _ _) }

theorem ldHon_below : Spec.ldHon_below F E := fun Z ws κ h hK hR =>
  ldKappaPp_objR Z.R κ ws.off ws.lk ws.sh ws.ins _ _ _ _ _ _ _ _ _ hK.wf hK.lin
    (ldKappaW_pre _ (Z.R.TP₀.D₁.up3 Z.tw₁) ws.off κ h.t₁ hK.t₁.bridge hK.t₁.tow)
    (ldKappaW_pre _ (Z.R.TP₀.D₂.up3 Z.tw₂) ws.off κ h.t₂ hK.t₂.bridge hK.t₂.tow)
    (ldKappaW_pre _ (Z.R.TP₀.D₃.up3 Z.tw₃) ws.off κ h.t₃ hK.t₃.bridge hK.t₃.tow)
    (ldKappaW_pre _ (Z.R.X.run.up3 Z.tw₄) ws.off κ h.t₄ hK.t₄.bridge hK.t₄.tow) hK.link
    (ldKappaW_pre _ (Z.R.Kc.run.up3 Z.twK) ws.lk κ h.tK hK.tK.bridge hK.tK.tow) hR hK.linB
    (ldKappaW_pre _ (Z.R.TB₀.D₁.upJ Z.tw₁B) ws.sh κ h.t₁B hK.t₁B.bridge hK.t₁B.tow)
    (ldKappaW_pre _ (Z.R.TB₀.D₂.upJ Z.tw₂B) ws.sh κ h.t₂B hK.t₂B.bridge hK.t₂B.tow)
    (ldKappaW_pre _ (Z.R.TB₀.D₃.upJ Z.tw₃B) ws.ins κ h.t₃B hK.t₃B.bridge hK.t₃B.tow)
    (ldKappaW_pre _ (Z.R.XB.run.upJ Z.tw₄B) ws.ins κ h.t₄B hK.t₄B.bridge hK.t₄B.tow)

omit [Field F] [Fintype F] [Algebra F E] in
theorem ldHon_wfRound : Spec.ldHon_wfRound E := by
  intro C P B
  have e : B.link.R.shape = ((B.cLkp P.n).link B.p0).R.shape ++ P.lBatt.R.shape := by
    unfold LdWfP.Blk.link LdWfP.Blk.chain
    rw [Chain.link]
    rfl
  rw [e]
  exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)

omit [Field F] [Fintype F] [Algebra F E] in
theorem ldHon_reqBits : Spec.ldHon_reqBits E := by
  intro Kc a z r w h
  have h1 := congrArg List.length h
  unfold LdReq.bits at h1
  simp only [List.length_append, List.length_replicate, List.length_nil] at h1
  have h2 : r.first.link.R.shape.nAll = 0 := by omega
  have h3 : r.first.link.R.shape ≠ [] := List.cons_ne_nil _ _
  exact h3 (List.length_eq_zero_iff.1 h2)

theorem ldHon_conf : Spec.ldHon_conf F E := fun Fp _ _ _ p _ Z _ V hJ hw =>
  (ldObjZ_wf p Z.Zw 1 (ldWfE_okStd F E Fp Z.Zw V p 1 (ldObjRefJ_wf F E Fp Z.Zw V p Z.δ.dS hJ))
    ⟨Z.R.W, Z.R.Bw⟩ hw).1

end
end Cb
