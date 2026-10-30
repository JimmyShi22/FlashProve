-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Door/Law/K5LeftFitsI.lean: kind K5: FOUR FIELDS ON PUBLIC DATA OF "WHAT IS LEFT OF THE KIND's LAW AT THE TABLE" (the structure K5Rest, Door/Law/K5AtMgPaid.lean) AS THEOREMS: each concludes the field's own text, with Lean's own check of the field's type (rest_‹field›_fits).
  lmIs_plus: the place's packing number is the shape's (place_att, Att/GuardPlan.lean).
  posG_plus: the geometry's numbers are positive: a clause of the one test on the plan (okAll_plus, Door/Law/K5LeftFitsD.lean; posG_of_ok, Att/Claims/PlanLaw.lean).
  planesOkAt_plus: the program's own test on the planes' packing says yes (guard_theorems' fifth clause, Att/GuardPlan.lean).
  colsFit_plus: THE ONE COMPARISON OF PUBLIC NUMBERS ("the planes' columns fit the matrix of the reads") IS NO TEST TO BE RUN: IT FOLLOWS FROM THE PLAN's OWN MAKE, WITH EQUALITY: the planner lays the planes' matrix with 2 ^ lmb rows (ofPlan_rows) and S.kbA columns (ofPlan_cols, here), and S.kbA is what
    Forest.planeCols returns at the lookup's shape: NC * 2 ^ (kT + 5 - lmb) (kb_of_hid · planeCols_ok, Att/Claims/PlanesHost.lean).
IS IT EMPTY HERE? Implications from the plan's and the guard's public facts.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5AtMgPaid
import Johnson.Desc.First.Att.Door.Law.K5LeftFitsD

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Road

/-- **The planes' matrix has S.kbA columns**, in the list of matrices of a plan that Attention.plan returns. (bA_rows' like: Att/Claims/PlanesHost.lean.) -/
theorem bA_cols {settings : Model.Settings} {j : Attention.In} {cf : Attention.Cfg} {X : Attention.Plan}
    (h : Attention.plan settings j cf = Except.ok X) : (X.seam.tl.mats.getD (X.S.cf.NAs + 2) {}).k = X.S.kbA := by
  have e : (Attention.matrices X.S X.inp)[X.S.cf.NAs + 2]? =
      some (Attention.ownMatrix X.inp "bA" (2 ^ X.S.cf.lmb) X.S.kbA (X.S.cf.NAs + 2) X.inp.wpbA) := by
    unfold Attention.matrices
    exact (L5.append_at _ _ 2 (by simp)).trans (by simp)
  rw [L5.plan_mats h, Array.getD_eq_getD_getElem?, Array.getElem?_map, e]
  rfl

theorem ofPlan_cols {A : Attention.Plan} (h : OfPlan A) : (A.seam.tl.mats.getD (A.S.cf.NAs + 2) {}).k = A.S.kbA := by
  obtain ⟨_, _, _, A0, pf, h0, rfl⟩ := h
  exact bA_cols (X := A0) h0

/-- **The number of the planes' columns is the matrix's**, at a plan that the planner returns. -/
theorem ofPlan_colsFit {A : Attention.Plan} (h : OfPlan A) :
    A.fs.NC * 2 ^ (A.fs.kT + 5 - A.S.cf.lmb) =
      (A.seam.tl.mats.getD (A.S.cf.NAs + 2) {}).k * ((A.seam.tl.mats.getD (A.S.cf.NAs + 2) {}).m / 2 ^ A.S.cf.lmb) := by
  obtain ⟨lid, cf, hid⟩ := ofPlan_shape h
  have ecf : A.S.cf = cf := (L5.shaped_of_hid hid).cfg
  have hk := kb_of_hid hid
  rw [← ecf] at hk
  obtain ⟨_, ekb⟩ := planeCols_ok hk
  rw [ofPlan_rows h, Nat.div_self (Nat.two_pow_pos _), Nat.mul_one, ofPlan_cols h, ekb]
  rfl

end K5Law

namespace H2K5.Door
open Cb Cb.Fo Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent attSg JAtt enMask lookAt sigListCalls keptAt CellsAre)
open VerifiableInference.Desc.K9 (RunOf readerOf)
open VerifiableInference.Desc.K13.Law (DataK13)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K12.Door (Laid)
open OnBytes.Road.L5 (dimOf Zs cellsA)

section
variable {Pp Xi Cells Tok Cl Ix : Type} {nR : ℕ} {Fr : Frame}
  (Mg Mg0 : Meaning Pp (Wit Cells Tok MsgT)) (D : PubData) (Dn : Sent) (G0 : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf Dn.codes s.l).om i).Smp) (ms : List Mem)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) (in0 : Pp × S → Bool)
  (Ld : Laid) (Ms : List OracleShape) (D13 : DataK13 Pp (Wit Cells Tok MsgT) nR)
  (bs : ℕ) (claim : Aff → Cl) (Wv : Verify.Public) (g : ℕ) (before : List (ℕ × ℕ)) (a : Attention.Plan) (x : Look.Place)
  (links : List ModelPart) (pl : VerifiableInference.Desc.Place) (rad : OracleShape → Nat) (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
  (O : List Item) (Q : List Pub) (uL uH : ℕ → UFn)
  (seat : Fin (sigListCalls Dn rad x.link).length → ℕ × ℕ)
  (smpR : Array OnBytes.Oracle × OnBytes.TreeBook → (i : Fin (sigListCalls Dn rad x.link).length) →
    Option ((sigOf Dn.codes (sigListCalls Dn rad x.link)).om i).Smp)
  (lk : ℕ → Option (Link S Claim)) (Lk : Link S Claim) (same : S → S → Bool) (blk : Block S Claim)
  (claimC : Aff → Claim) (nm : String)
  (Hd : Cells → Ix → Prop) (bsW : ℕ → Wit Cells Tok MsgT → Prop)
  (dP : ℕ → Pp × S → Strs → Wit Cells Tok MsgT → Prop) (body : ℕ → First.Part → Ix → Pp × S → Strs → Wit Cells Tok MsgT → Prop)
  (Zof : Wit Cells Tok MsgT → Zs)

theorem lmIs_plus (h4 : Wv.p4 = true) (ha : Wv.A[g]? = some a) (hx : lookAt Wv (2 * g + 1) false = some x) : x.lm = a.S.cf.lmb :=
  (place_att h4 ha hx).2.1

include Dn rad in
theorem posG_plus (hP : PlanIs Wv) (h4 : Wv.p4 = true) (ha : Wv.A[g]? = some a) (hG : k5GuardN Wv (2 * g + 1) g = true)
    (hb : planOk (parO Wv (2 * g + 1) a before) = true) (hc : claimsOkAtO a = true) : K5Law.PosG (parCOf a).geo := by
  have h := okAll_plus Wv g before a Dn rad hP h4 ha hG hb hc
  simp only [planOkAll, K5Law.planOkLaw, Bool.and_eq_true] at h
  exact K5Law.posG_of_ok h.1.2

theorem planesOkAt_plus (hP : PlanIs Wv) (h4 : Wv.p4 = true) (ha : Wv.A[g]? = some a) (hx : lookAt Wv (2 * g + 1) false = some x) :
    Look.planesOk x.fs (parCOf a).geo.lmb = true :=
  (guard_theorems hP h4 ha hx (Params.settingOf Wv.P.frame)).2.2.2.2

theorem colsFit_plus (hOP : K5Law.OfPlan a) (hfs : x.fs = a.fs) :
    x.fs.NC * 2 ^ (x.fs.kT + 5 - a.S.cf.lmb) ≤
      (a.seam.tl.mats.getD (a.S.cf.NAs + 2) {}).k * ((a.seam.tl.mats.getD (a.S.cf.NAs + 2) {}).m / 2 ^ a.S.cf.lmb) := by
  rw [hfs]
  exact Nat.le_of_eq (K5Law.ofPlan_colsFit hOP)

/-! ## Lean's own checks of the fields' types -/

theorem rest_lmIs_fits (h4 : Wv.p4 = true) (ha : Wv.A[g]? = some a) (hx : lookAt Wv (2 * g + 1) false = some x)
    (R : K5Rest (Fr := Fr) Mg Mg0 D Dn arr smp ms decT in0 Ld Ms D13 bs Wv g before a x links pl rad O Q seat smpR lk Lk same blk claimC nm Hd bsW dP body Zof) :
    K5Rest (Fr := Fr) Mg Mg0 D Dn arr smp ms decT in0 Ld Ms D13 bs Wv g before a x links pl rad O Q seat smpR lk Lk same blk claimC nm Hd bsW dP body Zof :=
  { R with lmIs := lmIs_plus Wv g a x h4 ha hx }

theorem rest_posG_fits (hP : PlanIs Wv) (h4 : Wv.p4 = true) (ha : Wv.A[g]? = some a) (hG : k5GuardN Wv (2 * g + 1) g = true)
    (hb : planOk (parO Wv (2 * g + 1) a before) = true) (hc : claimsOkAtO a = true)
    (R : K5Rest (Fr := Fr) Mg Mg0 D Dn arr smp ms decT in0 Ld Ms D13 bs Wv g before a x links pl rad O Q seat smpR lk Lk same blk claimC nm Hd bsW dP body Zof) :
    K5Rest (Fr := Fr) Mg Mg0 D Dn arr smp ms decT in0 Ld Ms D13 bs Wv g before a x links pl rad O Q seat smpR lk Lk same blk claimC nm Hd bsW dP body Zof :=
  { R with posG := posG_plus Dn Wv g before a rad hP h4 ha hG hb hc }

theorem rest_planesOkAt_fits (hP : PlanIs Wv) (h4 : Wv.p4 = true) (ha : Wv.A[g]? = some a) (hx : lookAt Wv (2 * g + 1) false = some x)
    (R : K5Rest (Fr := Fr) Mg Mg0 D Dn arr smp ms decT in0 Ld Ms D13 bs Wv g before a x links pl rad O Q seat smpR lk Lk same blk claimC nm Hd bsW dP body Zof) :
    K5Rest (Fr := Fr) Mg Mg0 D Dn arr smp ms decT in0 Ld Ms D13 bs Wv g before a x links pl rad O Q seat smpR lk Lk same blk claimC nm Hd bsW dP body Zof :=
  { R with planesOkAt := planesOkAt_plus Wv g a x hP h4 ha hx }

theorem rest_colsFit_fits (hOP : K5Law.OfPlan a) (hfs : x.fs = a.fs)
    (R : K5Rest (Fr := Fr) Mg Mg0 D Dn arr smp ms decT in0 Ld Ms D13 bs Wv g before a x links pl rad O Q seat smpR lk Lk same blk claimC nm Hd bsW dP body Zof) :
    K5Rest (Fr := Fr) Mg Mg0 D Dn arr smp ms decT in0 Ld Ms D13 bs Wv g before a x links pl rad O Q seat smpR lk Lk same blk claimC nm Hd bsW dP body Zof :=
  { R with colsFit := colsFit_plus a x hOP hfs }

end

end H2K5.Door

#print axioms K5Law.ofPlan_colsFit
#print axioms H2K5.Door.lmIs_plus
#print axioms H2K5.Door.posG_plus
#print axioms H2K5.Door.planesOkAt_plus
#print axioms H2K5.Door.colsFit_plus
#print axioms H2K5.Door.rest_lmIs_fits
#print axioms H2K5.Door.rest_posG_fits
#print axioms H2K5.Door.rest_planesOkAt_fits
#print axioms H2K5.Door.rest_colsFit_fits
