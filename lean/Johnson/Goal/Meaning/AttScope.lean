-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/AttScope.lean: attention's joint: at all public files in the goals' scope, the
library's record on an attention sub-proof (AttOrd, Johnson/Road/Lane5AttDef.lean:151) is two named
relations together, with no premise on public data left.

The law attOrd_iff_public (Johnson/Road/Lane5AttSeamPub.lean:109) says so under three premises on
public data beside publicOf's line: the fourteen numbers FillRef, the test usualB (the usual call
list; one shift in the group) and kFD = 16. Its head says of the call list in the configuration:
"that this list is the parameter file's is not shown, which is why the call list must be a test".
  config_lines, lines_of_public: that is shown here: the list is what readLines returns on the
    parameter file's lines callA. (They are config_groups and groups_of_public,
    Johnson/Road/HeadL5Grp.lean:102, :206, proved again with that one line kept.)
  sh_in_scope: the shift of layer L, as the verifier reads it off the scale file, is the goals'
    reader's (pp.w L).sh. shifts_in_scope: so a group of four layers has one shift: the scale file
    is free in the goals' scope, but the goals' reader refuses settings that are not lawful, and
    lawful settings have one shift in a group (LawfulBut.one, Inst/Model/Scales.lean:98). A fact of
    the scope, not of a test of the verifier, which takes groups with two shifts.
  attUsualK_in_scope: the test attUsualK (Johnson/Road/Lane5AttSeamAt.lean:53) says yes.
  attOrd_iff_in_scope: for every g below 12: X.A[g] is there, has the shape Hd.shapeA X g, and for
    every list Z: AttOrd ↔ AttR0 ∧ InTables at the calls callsA of the plan's own records.
  fsA, attOrds_in_scope: for all twelve groups at a family of lists.
Not claimed: AttR0 or InTables of anything; all that the head of Lane5AttSeamPub.lean does not claim
on the key vectors kvA and the rule addrA.
-/
import Johnson.Goal.Meaning.RopeFlags
import Johnson.Road.Lane5AttSeamAt

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.Att

open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Verify (publicOf Public layerShape)

/-! ## The call list -/

/-- The plans that Attention.config returns are the values of Attention.group at the list that
readLines returns on the parameter file's lines callA. -/
theorem config_lines {P : PolScan} {y : Layer.Lay} {s : Layer.Scales} {midQ : ℕ → ℕ}
    {c : Attention.Config} (h : Attention.config P y s midQ = .ok c) :
    ∃ lines, Attention.readLines P.polCallsA = .ok lines ∧ c.plans.size = y.NGr ∧
      ∀ g, g < y.NGr →
        ∃ Xg, c.plans[g]? = some Xg ∧ Attention.group P y s midQ lines g = .ok Xg := by
  unfold Attention.config at h
  obtain ⟨lines, hl, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨plans, hm, h⟩ := ok_of_bind h
  cases plans with
  | nil => cases h
  | cons X0 rest =>
    obtain ⟨-, -, h⟩ := ok_of_bind h
    cases h
    refine ⟨lines, hl, ?_, fun g hg => ?_⟩
    · have k := Hd.mapM_length _ _ _ hm
      rw [List.length_range] at k
      show (X0 :: rest).toArray.size = y.NGr
      rw [List.size_toArray]
      exact k
    · obtain ⟨Xg, h1, h2⟩ := Hd.mapM_ok _ _ _ hm g g (by simp [hg])
      exact ⟨Xg, by simpa using h1, h2⟩

/-- At profile 4, the shape of each attention plan in the public part is that of what
Attention.group returns at the list that readLines returns on the parameter file's lines callA. -/
theorem lines_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOf pol KL lay = .ok X) (hp4 : (layerShape X.P).p4 = true) :
    ∃ lines, Attention.readLines X.P.polCallsA = .ok lines ∧
      ∀ g, g < X.y.NGr →
        ∃ Xg, Attention.group X.P X.y X.layers.sc (Hd.midQOf X.y) lines g = .ok Xg ∧
          Hd.shapeA X g = Xg.S := by
  obtain ⟨P, y, hpl1, eP, -⟩ := Hd.public_parts h
  have hq1 : y.h.p4 = true := by
    rw [layout_shape (Hd.layerLayout_of_polLayout hpl1), ← eP]
    exact hp4
  unfold Model.Verify.publicOf at h
  obtain ⟨⟨P', y'⟩, hpl, h⟩ := ok_of_bind h
  have e : (P, y) = (P', y') := Except.ok.inj (hpl1.symm.trans hpl)
  cases e
  obtain ⟨sc, -, h⟩ := ok_of_bind h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨_, h⟩ := Hd.ok_of_ite h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  dsimp only at h
  rw [if_pos hq1] at h
  obtain ⟨c, hcfg, h⟩ := ok_of_bind h
  obtain ⟨⟨A0, hC⟩, hpure, h⟩ := ok_of_bind h
  have e2 : (c.plans, c.hCallsA) = (A0, hC) := Except.ok.inj hpure
  cases e2
  obtain ⟨layers, hPub, h⟩ := ok_of_bind h
  obtain ⟨G, -, h⟩ := ok_of_bind h
  obtain ⟨seenA, hown, h⟩ := ok_of_bind h
  obtain ⟨owner, -, h⟩ := ok_of_bind h
  obtain ⟨H, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  cases h
  have ey : layers.y = y := Hd.pubOf_y hPub
  have es : layers.sc = sc := Hd.pubOf_sc hPub
  obtain ⟨lines, hrl, hsz, hgrp⟩ := config_lines hcfg
  have hs2 : seenA.size = c.plans.size := by rw [Hd.owners_size hown, Array.size_map]
  refine ⟨lines, hrl, fun g hg => ?_⟩
  have hg' : g < y.NGr := by
    have k : g < layers.y.NGr := hg
    rw [ey] at k
    exact k
  obtain ⟨Xg, h1, h2⟩ := hgrp g hg'
  have hlt : g < seenA.size := by
    rw [hs2, hsz]
    exact hg'
  have hb : seenA[g]? = some seenA[g] := by simp [hlt]
  refine ⟨Xg, ?_, ?_⟩
  · show Attention.group P layers.y layers.sc (Hd.midQOf layers.y) lines g = .ok Xg
    rw [ey, es]
    exact h2
  · unfold Hd.shapeA
    dsimp only
    rw [Hd.zipWith_atA _ _ _ h1 hb]
    rfl

/-! ## The shifts -/

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- The shift of layer L, as the verifier reads it, is the goals' reader's. -/
theorem sh_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (L : Fin 48) :
    X.layers.sc.klSh L.val = (pp.w L).sh := by
  obtain ⟨P, f, hP, hf, ho⟩ := OnBytes.Flat.settingsAny_parts (OnBytes.Flat.settingsAtRef_eq hR)
  have ew : (pp.w L).sh = f.lay L 11 := by
    unfold Inst.Model.ofKL at ho
    split at ho
    · cases ho
      rfl
    · cases ho
  have eP' : P = X.P := Except.ok.inj (hP.symm.trans (Hd.scan_of_public h))
  subst eP'
  obtain ⟨g1, -⟩ := VerifiableInference.OnPublicFiles.Flat.klFileOf_fields hf
  have A := Hd.core_of_scope hZ hR h
  have hL : X.P.h.L = 48 := A.num 2
  have hr := Hd.scales_of_public h
  rw [shape_of_public h] at hr
  have hsc := reader_record hr
  rw [if_pos (Hd.public_of_core h A).p4] at hsc
  rw [ew, g1 L 11 (by rw [hL]; exact L.isLt), VerifiableInference.OnPublicFiles.Flat.word_same, hsc]
  rfl

/-- A group of four layers has one shift. -/
theorem shifts_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g l : ℕ} (hg : g < 12) (hl : l < 4) :
    X.layers.sc.klSh (g * 4 + l) = X.layers.sc.klSh (g * 4 + 0) := by
  obtain ⟨-, -, -, hLaw⟩ :=
    OnBytes.Flat.settingsAny_iff.1 (OnBytes.Flat.settingsAtRef_eq hR)
  have one := hLaw.one ⟨g, hg⟩ ⟨l, hl⟩
  have h1 : 4 * g + l < 48 := by omega
  have h0 : 4 * g < 48 := by omega
  have k1 : (pp.kap (4 * g + l)).sh = (pp.w ⟨4 * g + l, h1⟩).sh := by
    unfold Inst.Model.ScalesAndPolicy.kap
    rw [dif_pos h1]
    rfl
  have k0 : (pp.kap (4 * g)).sh = (pp.w ⟨4 * g, h0⟩).sh := by
    unfold Inst.Model.ScalesAndPolicy.kap
    rw [dif_pos h0]
    rfl
  have one' : (pp.kap (4 * g + l)).sh = (pp.kap (4 * g)).sh := one
  rw [k1, k0, ← sh_in_scope hZ hR h ⟨4 * g + l, h1⟩, ← sh_in_scope hZ hR h ⟨4 * g, h0⟩] at one'
  have e1 : g * 4 + l = 4 * g + l := by omega
  have e0 : g * 4 + 0 = 4 * g := by omega
  rw [e1, e0]
  exact one'

/-! ## The test -/

/-- What readLines returns on the stored example's lines callA. -/
theorem lines_ref : Attention.readLines VerifierAndGoals.Lines.callsARef =
    .ok [⟨"KR", .kr, [.rm, .rd]⟩, ⟨"KFD", .kfd, [.fm, .fd]⟩, ⟨"R16", .r16, [.wl, .ix]⟩,
      ⟨"WH", .wh, [.wh]⟩] := by decide +kernel

/-- The test on publicOf's own record says yes, at all public files in the goals' scope. -/
theorem attUsualK_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : attUsualK X = true := by
  have A := Hd.core_of_scope hZ hR h
  have B := Hd.public_of_core h A
  obtain ⟨lines, hrl, hgr⟩ := lines_of_public h B.p4
  rw [(Hd.calls_of_scope hZ hR h).2.1, lines_ref] at hrl
  have el := Except.ok.inj hrl
  have hLam : X.y.Lam = 4 := by
    rw [(laid_of_layout B.lay B.switches.p3).2.Lam, shape_of_public h]
    show 2 ^ X.P.h.ll = 4
    rw [show X.P.h.ll = 2 from A.num 3]
    norm_num
  have hk : X.P.h.kFD = 16 := by
    rw [Hd.scan_of_scope hZ hR h]
    rfl
  unfold attUsualK
  rw [List.all_eq_true]
  intro g hg
  have hg12 : g < 12 := List.mem_range.mp hg
  obtain ⟨Xg, hG, eS⟩ := hgr g (by rw [B.groups]; exact hg12)
  obtain ⟨cf, hf, hS, -, -⟩ := shaped_of_group hG
  have ec : (Hd.shapeA X g).cf = cf := by
    rw [eS]
    exact hS.cfg
  have ef := fill_eq hf
  rw [Bool.and_eq_true, decide_eq_true_eq, ec, ef]
  refine ⟨?_, hk⟩
  unfold usualB
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨?_, fun l hl => ?_⟩
  · show (lines.map fun l => (l.kind, l.segs)) = _
    rw [← el]
    rfl
  · have hl4 : l < 4 := by
      have := List.mem_range.mp hl
      have e2 : (2 : ℕ) ^ X.P.h.ll = 4 := by
        rw [show X.P.h.ll = 2 from A.num 3]
        norm_num
      exact e2 ▸ this
    rw [decide_eq_true_eq]
    show ((Array.range X.y.Lam).map fun lam => X.layers.sc.klSh (g * X.y.Lam + lam)).getD l 0 =
      ((Array.range X.y.Lam).map fun lam => X.layers.sc.klSh (g * X.y.Lam + lam)).getD 0 0
    rw [hLam, Hd.getD_rangeMap _ _ _ hl4, Hd.getD_rangeMap _ _ _ (by norm_num)]
    exact shifts_in_scope hZ hR h hg12 hl4

/-! ## The joint -/

/-- ATTENTION's JOINT. -/
theorem attOrd_iff_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) :
    ∃ Ag : Attention.Plan, X.A[g]? = some Ag ∧ Ag.S = Hd.shapeA X g ∧
      ∀ Zs' : Zs, AttOrd Ag.S Zs' ↔ AttR0 Ag.S Zs' ∧ (callsA Ag.S Ag.fs Zs').InTables := by
  have A := Hd.core_of_scope hZ hR h
  have B := Hd.public_of_core h A
  have U := attUsualK_at (attUsualK_in_scope hZ hR h) hg
  exact attOrd_iff_public h B.p4 (Hd.fillRef_of_core A B) (by rw [B.groups]; exact hg) U.1 U.2

/-- The lookup's record in the attention plan of group g; the default where there is no plan. -/
def fsA (X : Public) (g : ℕ) : Forest.Shape := ((X.A[g]?).map (·.fs)).getD default

/-- All twelve groups, at a family of lists: own (2 g + 1) is the list of the attention sub-proof of
group g. -/
theorem attOrds_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (own : ℕ → Zs)
    (R : ∀ g < 12, AttR0 (Hd.shapeA X g) (own (2 * g + 1)))
    (I : ∀ g < 12, (callsA (Hd.shapeA X g) (fsA X g) (own (2 * g + 1))).InTables) :
    ∀ g < 12, AttOrd (Hd.shapeA X g) (own (2 * g + 1)) := by
  intro g hg
  obtain ⟨Ag, hA, eS, hiff⟩ := attOrd_iff_in_scope hZ hR h hg
  have ef : fsA X g = Ag.fs := by
    unfold fsA
    rw [hA]
    rfl
  have r := R g hg
  have i := I g hg
  rw [← eS] at r i ⊢
  rw [ef] at i
  exact (hiff _).2 ⟨r, i⟩

#print axioms lines_of_public
#print axioms sh_in_scope
#print axioms shifts_in_scope
#print axioms lines_ref
#print axioms attUsualK_in_scope
#print axioms attOrd_iff_in_scope
#print axioms attOrds_in_scope

end Meaning.Att
