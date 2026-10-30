-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/AttForInScope.lean: attention's joint at the lookup's own clause, and the
public premises on attention's tables, at all public files in the goals' scope.

attOrd_iff_in_scope (Johnson/Goal/Meaning/AttScope.lean) has InTables at the calls callsA. The
lookup's own clause is ForInA (Johnson/Road/Lane5ForIn.lean:57), at the record's own numbers nF and
rows tauF: another term.
  hid_in_scope: the plan X.A[g]: its shape and its lookup's record are what shapeHid returns on a
    configuration with the reference numbers, kFD = 16 and the usual call list.
  tabsA_in_scope: TabsA (Johnson/Road/Lane5BridgeA.lean:70): every row of the verifier's table of a
    call is a row of the library's, and each call has room for the library's key vector.
  sameCalls_in_scope: the lookup's record has the shape's own four calls.
  attKeys_of_forIn: ForInA at the reading cellZ of a list gives AttKeys, the library's clause on
    attention's keys (AttKey of Johnson/Goal/Meaning/Row.lean is the same term).
  attOrd_iff_forIn_in_scope: AttOrd if and only if AttR0 and ForInA.
  attOrds_of_forIn: all twelve, at a family of lists.
All at Hd.shapeA X g and fsA X g. The key vectors are the library's kvA.
Not claimed: ForInA or AttR0 of anything.
-/
import Johnson.Goal.Meaning.AttScope
import Johnson.Road.Lane5SameCalls

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.Att

open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Verify (publicOf Public layerShape)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- The plan of group g, with all that the theorems on attention's seam ask of it. -/
theorem hid_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) :
    ∃ cf : Attention.Cfg,
      Attention.shapeHid X.P.settings.lidb cf = .ok (Hd.shapeA X g, fsA X g) ∧ CfRef cf ∧
        cf.kFD = 16 ∧ cf.S = 12 ∧ cf.rx = 8 ∧ UsualCalls cf := by
  have A := Hd.core_of_scope hZ hR h
  have B := Hd.public_of_core h A
  have U := attUsualK_at (attUsualK_in_scope hZ hR h) hg
  obtain ⟨Ag, lines, cf, hA, eS, hf, hh, -⟩ := hid_of_public h B.p4 (by rw [B.groups]; exact hg)
  obtain ⟨hc, h12, h8, -⟩ := cfRef_of_fill hf (Hd.fillRef_of_core A B)
  have ec : (Hd.shapeA X g).cf = cf := by
    rw [← eS]
    exact (shaped_of_hid hh).cfg
  have ef : fsA X g = Ag.fs := by
    unfold fsA
    rw [hA]
    rfl
  rw [ec] at U
  refine ⟨cf, ?_, hc, U.2, h12, h8, usual_of_test U.1⟩
  rw [← eS, ef]
  exact hh

theorem tabsA_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) :
    TabsA (Hd.shapeA X g) (fsA X g) := by
  obtain ⟨cf, hh, hc, hk, h12, h8, U⟩ := hid_in_scope hZ hR h hg
  exact tabsA_of_usual hh hc hk h12 h8 U

theorem sameCalls_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) :
    SameCalls (Hd.shapeA X g) (fsA X g) := by
  obtain ⟨cf, hh, -, -, -, -, U⟩ := hid_in_scope hZ hR h hg
  exact sameCalls_of_usual hh U

/-- The lookup's own clause is InTables at callsA. -/
theorem forInA_iff_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) (Za : Zs) :
    ForInA (Hd.shapeA X g) (fsA X g) (cellZ Za) ↔
      (callsA (Hd.shapeA X g) (fsA X g) Za).InTables :=
  forInA_iff_inTables (sameCalls_in_scope hZ hR h hg) (cellZ Za)

/-- From the lookup's own clause to the library's clause on attention's keys. -/
theorem attKeys_of_forIn (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) {Za : Zs}
    (I : ForInA (Hd.shapeA X g) (fsA X g) (cellZ Za)) : AttKeys (Hd.shapeA X g) Za := by
  obtain ⟨cf, hh, hc, hk, h12, h8, U⟩ := hid_in_scope hZ hR h hg
  exact attBridge_of_usual hh hc hk h12 h8 U Za ((forInA_iff_in_scope hZ hR h hg Za).1 I)

/-- ATTENTION's JOINT AT THE LOOKUP's OWN CLAUSE. -/
theorem attOrd_iff_forIn_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ}
    (hg : g < 12) (Za : Zs) :
    AttOrd (Hd.shapeA X g) Za ↔
      AttR0 (Hd.shapeA X g) Za ∧ ForInA (Hd.shapeA X g) (fsA X g) (cellZ Za) := by
  obtain ⟨cf, hh, hc, hk, h12, h8, U⟩ := hid_in_scope hZ hR h hg
  exact (attOrd_iff_usual hh hc hk h12 h8 U Za).trans
    (and_congr_right fun _ => (forInA_iff_in_scope hZ hR h hg Za).symm)

/-- All twelve groups, at a family of lists. -/
theorem attOrds_of_forIn (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (own : ℕ → Zs)
    (R : ∀ g < 12, AttR0 (Hd.shapeA X g) (own (2 * g + 1)))
    (I : ∀ g < 12, ForInA (Hd.shapeA X g) (fsA X g) (cellZ (own (2 * g + 1)))) :
    ∀ g < 12, AttOrd (Hd.shapeA X g) (own (2 * g + 1)) :=
  fun g hg => (attOrd_iff_forIn_in_scope hZ hR h hg _).2 ⟨R g hg, I g hg⟩

#print axioms config_lines
#print axioms hid_in_scope
#print axioms tabsA_in_scope
#print axioms sameCalls_in_scope
#print axioms forInA_iff_in_scope
#print axioms attKeys_of_forIn
#print axioms attOrd_iff_forIn_in_scope
#print axioms attOrds_of_forIn

end Meaning.Att
