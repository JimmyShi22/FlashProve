-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HeadCondScope.lean: the premises on public numbers that the laws on the
output head's own rounds ask hold at all public files in the goals' scope. (It stands under
Johnson/Goal/ because it names the goals' scope: scripts/IMPORTS.txt.)

What the file holds. Z: three public files with VerifierAndGoals.InScope Z = true. pp: what the goals' reader
returns on them. X: what the verifier's own function publicOf returns on them.
  ok_in_scope        the kind's tests on the plan pass: (parOf X.hS w).ok = true.
  laidOk_in_scope    the tests on how the head's cells are laid pass: laidOk X = true.
  k06Cond_in_scope   the record K06CondAt X (Johnson/Desc/Kinds/Law/K06ConditionSpends.lean), all
                     eighteen fields. That the plan names the array of reads holds wherever
                     publicOf returns (Johnson/Desc/Kinds/Law/ReadsNamed.lean).
  seated_in_scope    the block that a lot seats (Head.seatedClaims X l ms, at any l and ms) passes
                     its own test on the plan. there_in_scope: and there is such a block.
  reply_in_scope     the next token's block (Reply.blockOf X l) passes its own test on the plan.
  k06Ref_in_scope, k06Whole_in_scope   the reference model's sizes; no padding of the vocabulary
                     (Johnson/Desc/Kinds/Law/K06ConditionWide.lean).
  k07Cond_in_scope, k06Full_in_scope   2 ≤ V; the digits' shift is 8.
  numbers_in_scope, stream_in_scope    the numbers themselves, as two records.
  planOk_of_numbers, laid_of_numbers   the two tests at these numbers, at any sizes and policy.

The scope is a family of files, not one. Eight numbers of the parameter file are free in it. The
head reads six of them: MF, KF and epsF of the final normalisation, and C, theta and cap of the
policy. Seventeen of the kind's tests on the plan read a free number:
  the policy's three      theta ≤ C; cap ≤ T; cap < 2^16.
  eight of the ranges     24 ≤ MF ≤ 47; MF ≤ KF + 14; 17 ≤ KF ≤ 32; KF ≤ MF; 1 ≤ epsF < 2^48.
  six no-overflow tests   U-NF (KF); W-NF (MF, KF); E2 (C, theta); E3 (cap); E4 (C);
                          no-wrap-ledger-eps (epsF).
Two more, of the tests on how the cells are laid: C < 2^40; theta < 2^40.
All of them follow from what the goals' reader tests before it returns
(OnBytes.Flat.settingsAtRef_lawful): the final normalisation's intervals, K ≤ M, C < 2^32,
theta ≤ C and cap ≤ 1,024. The scope's own clause 2^8 ≤ theta is not used. They reach X by the
scope's equation between the parameter file and the reader's numbers, and by publicOf's own scan of
that file: so the reader, the scope and publicOf's return are all three spent. The letter w of
ok_in_scope is idle (the tests on the plan do not read it); pp stands in no conclusion.
The other numbers are fixed in scope: lt = 10, la = 16, d = 5120, V = 202048, the shift 8, the
table's exponent 4, F = 24, five limbs; of the layers' layout: the stream's matrix has 65536 rows
and 400 columns, and its one tensor begins at feature 0 with five limbs of 5120 features.

On what it rests. Johnson/Goal/Meaning/HeadShapeScope.lean and HeadScope.lean (the head's shape in
scope), Johnson/Goal/Meaning/ScopeScan.lean (hdr_free, for epsF), Johnson/Meaning/PublicCore.lean
(public_of_core), Johnson/Road/HeadPlace.lean (borderH_of_layout), Johnson/Road/HeadLaid.lean
(admittedH_of_layout), and the record at the full size, Cond.k06Cond_full
(Johnson/Desc/Kinds/Law/K06Condition.lean), from which the fields that read fixed sizes alone are
carried over.

What it does not give. THAT ANY FILES MEET THE THREE PREMISES IS NOT SHOWN HERE: every theorem
below begins "if Z is in scope, the reader returns pp and publicOf returns X". For the stored
full-size example the first two are the matter of Johnson/Goal/Files/FilesReadProof.lean, which
this file does not import; that publicOf returns there is held by an evaluation alone (a #guard in
Johnson/Goal/Meaning/ScopeRun.lean), by no theorem. So the family's theorem is checked by the
kernel; that the release's files belong to the family is, in that third part, the evaluator's word.
Nothing on soundness: these are premises of laws, not the laws. That the
list of premises is complete is not shown (that file's head says how it was gathered). Nothing on
the request, the heard token, the carried record, the transcript or the cells. Nothing outside
the scope: at another size of model none of this is claimed. The eighteen fields are not eighteen
separate facts: once holds at every record by rfl (the setting's reader never lays that field);
features, point, rows, blocks and half of index follow from admitted (admitted_pays,
Johnson/Desc/Kinds/Law/K06ConditionSpends.lean); block follows from features and blocks
(block_follows, Johnson/Desc/Kinds/Law/K06ConditionWide.lean); admitted, numbers and reads hold
wherever publicOf returns. That no proof of work is asked
(work_ref) is read off the stored example's security lines by evaluation in the kernel.

-/
import Johnson.Goal.Meaning.HeadShapeScope
import Johnson.Meaning.Scope
import Johnson.Road.HeadPlace
import Johnson.Desc.Kinds.Law.K06ConditionSpends
import Johnson.Desc.Kinds.Law.K06ConditionWide
import Johnson.Desc.Kinds.Law.ReadsNamed
import Johnson.Desc.Kinds.Law.SeatedBridge
import Johnson.Stored.ReplySeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.InScope

open Norm (lt ls d lPd T S2)
open FinalNorm (MF KF epsF)
open OnBytes.Model.Verify (publicOf Public borderOf)
open Cond (K06Cond K06CondAt K07Cond)

/-- The kind's tests on the plan pass at the full size's seven fixed numbers, wherever the six free
ones lie in the reader's intervals. -/
theorem planOk_of_numbers [Sizes] [Policy] (sT : Nat)
    (hlt : lt = 10) (hls : ls = 6) (hd : d = 5120) (hV : V = 202048) (hsh : sh = 8) (hF : F = 24)
    (hsT : sT = 4)
    (m1 : 24 ≤ MF) (m2 : MF ≤ 47) (m3 : MF ≤ KF + 14) (k1 : 17 ≤ KF) (k2 : KF ≤ 32)
    (k3 : KF ≤ MF)
    (e1 : 1 ≤ epsF) (e2 : epsF < 2 ^ 48)
    (c1 : C < 2 ^ 32) (c2 : theta ≤ C) (c3 : cap ≤ 1024) : planOk sT = true := by
  have hT : T = 1024 := by unfold Norm.T; rw [hlt]
  have hS2 : S2 = 64 := by unfold Norm.S2; rw [hls]
  have hlPd : lPd = 13 := by unfold Norm.lPd; rw [hd]; decide
  have hJV : JV = 202048 := by unfold JV; rw [hV, hS2]
  have hJVa : JVa = 131072 := by unfold JVa; rw [hJV]; decide
  have pM : 2 ^ MF ≤ 2 ^ 47 := Nat.pow_le_pow_right (by norm_num) m2
  have pK1 : 2 ^ (KF - 1) ≤ 2 ^ 31 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have pK2 : 2 ^ (15 + KF) ≤ 2 ^ 47 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have pK3 : 2 ^ (16 + KF) ≤ 2 ^ 48 := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold planOk
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [Policy.ok, Bool.and_eq_true, decide_eq_true_eq, hT]
    omega
  · simp only [Sizes.ranges, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, hF,
      hsh, hsT, hV, hd, hS2, hJVa, hlPd, hlt]
    norm_num at e2 ⊢
    omega
  · simp only [noOverflow, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true,
      decide_eq_true_eq, hF, hsh, hV, hd, hJV, hT, Ty, BW, BC, BIG, off1, off2, offE]
    norm_num at pM pK1 pK2 pK3 e2 c1 ⊢
    omega

/-- The tests on how the head's cells are laid pass at the full size's numbers. -/
theorem laid_of_numbers [Sizes] [Policy] (x : Laid)
    (hlt : lt = 10) (hls : ls = 6) (hd : d = 5120) (hV : V = 202048) (hsh : sh = 8)
    (c1 : C < 2 ^ 32) (c2 : theta ≤ C)
    (x1 : x.la = 16) (x2 : x.padLog = 13) (x3 : x.limbs = 5) (x4 : x.laidLimbs = 5)
    (x5 : x.off = 0)
    (x6 : x.step = 5120) (x7 : 400 ≤ x.room) : x.ok = true := by
  have hS2 : S2 = 64 := by unfold Norm.S2; rw [hls]
  have hlPd : lPd = 13 := by unfold Norm.lPd; rw [hd]; decide
  have hJV : JV = 202048 := by unfold JV; rw [hV, hS2]
  unfold Laid.ok Laid.tests
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, hlt, hls, hd, hV, hsh, hS2, hlPd, hJV, x1, x2, x3, x4, x5, x6]
  norm_num at c1 ⊢
  omega

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- What the scope and the reader give of the head's numbers. -/
structure Numbers (X : Public) : Prop where
  lt : X.hS.lt = 10
  la : X.hS.la = 16
  d : X.hS.d = 5120
  V : X.hS.V = 202048
  sh : X.hS.digSh = 8
  sT : X.hS.tabS = 4
  F : X.hS.famF = 24
  XL : X.hS.XL = 5
  lPd : X.hS.lPd = 13
  m1 : 24 ≤ X.hS.MF
  m2 : X.hS.MF ≤ 47
  m3 : X.hS.MF ≤ X.hS.KF + 14
  k1 : 17 ≤ X.hS.KF
  k2 : X.hS.KF ≤ 32
  k3 : X.hS.KF ≤ X.hS.MF
  e1 : 1 ≤ X.hS.epsF
  e2 : X.hS.epsF < 2 ^ 48
  c1 : X.hS.clipC < 2 ^ 32
  c2 : X.hS.theta ≤ X.hS.clipC
  c3 : X.hS.cap ≤ 1024

theorem numbers_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : Numbers X := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := Meaning.HeadS.sizes_in_scope hZ hR h
  obtain ⟨p1, p2, p3, p4, p5⟩ := Meaning.HeadS.policy_in_scope hZ hR h
  have hd := Meaning.HeadS.d_in_scope hZ hR h
  have pe : X.hS.epsF = (VerifierAndGoals.freeLinesOf pp).epsF := by
    have hX := OnBytes.Road.Hd.scan_of_public h
    rw [OnBytes.Road.Hd.policy_of_scope hZ hR] at hX
    rw [Meaning.HeadS.headShape_of_public h]
    exact (VerifierAndGoals.Lines.hdr_free hX).2.2.2.1
  have L := OnBytes.Flat.settingsAtRef_lawful hR
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := L.nf
  obtain ⟨q1, q2, q3⟩ := L.pol
  have km := L.km.2
  have B := OnBytes.Road.Hd.public_of_core h (OnBytes.Road.Hd.core_of_scope hZ hR h)
  have adm := (OnBytes.Road.Hd.admittedH_of_layout B.head).adm
  have hl : X.hS.lPd = 13 := by
    unfold OnBytes.Model.Head.admitted at adm
    simp only [Bool.and_eq_true, beq_iff_eq] at adm
    rw [adm.1.2, hd]
    decide
  refine ⟨s1, s2, hd, s3, s4, s5, s6, s7, hl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [p4]; show _ ≤ pp.nf.M; omega)
    | (rw [p4]; show pp.nf.M ≤ _; omega)
    | (rw [p4, p5]; show pp.nf.M ≤ pp.nf.K + 14; omega)
    | (rw [p5]; show _ ≤ pp.nf.K; omega)
    | (rw [p5]; show pp.nf.K ≤ _; omega)
    | (rw [p4, p5]; exact km)
    | (rw [pe]; show _ ≤ pp.nf.eps.toNat; omega)
    | (rw [pe]; show pp.nf.eps.toNat < _; omega)
    | (rw [p1]; exact q1)
    | (rw [p1, p2]; exact q2)
    | (rw [p3]; exact q3)

/-- **The kind's tests on the plan pass at all public files in the goals' scope.** -/
theorem ok_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (w : Nat) : (parOf X.hS w).ok = true := by
  have N := numbers_in_scope hZ hR h
  have hls : X.hS.ls = 6 := by unfold OnBytes.Model.Head.Shape.ls; rw [N.la, N.lt]
  exact @planOk_of_numbers (parOf X.hS w).sizes (parOf X.hS w).policy X.hS.tabS N.lt hls N.d N.V
    N.sh N.F N.sT N.m1 N.m2 N.m3 N.k1 N.k2 N.k3 N.e1 N.e2 N.c1 N.c2 N.c3

/-- What the scope gives of the stream's matrix in the layers' layout. -/
structure Stream (X : Public) : Prop where
  kxb : (borderOf X.y).kxb = 400
  mxb : (borderOf X.y).mxb = 65536
  off : (borderOf X.y).off = 0
  nl : (borderOf X.y).nl = 5
  cnt : (borderOf X.y).cnt = 1
  J : (borderOf X.y).J = 5120

theorem stream_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : Stream X := by
  have B := OnBytes.Road.Hd.public_of_core h (OnBytes.Road.Hd.core_of_scope hZ hR h)
  have BH := OnBytes.Road.Hd.borderH_of_layout B.lay B.switches B.sized B.sized2
  obtain ⟨e, L1⟩ := OnBytes.Road.laid_of_layout B.lay B.switches.p3
  have hd : X.y.h.d = 5120 := by rw [e]; exact B.sized.d.symm
  have hx : X.y.h.xl = 5 := by
    have := Meaning.HeadS.border_in_scope hZ hR h
    have e2 : (borderOf X.y).nl = X.y.h.xl := by
      show X.y.xb.nl = X.y.h.xl
      rw [L1.xb]
    rw [← e2]; exact this
  refine ⟨BH.kxb, BH.mxb, ?_, Meaning.HeadS.border_in_scope hZ hR h, ?_, ?_⟩
  · show X.y.xb.off = 0
    rw [L1.xb]
  · show X.y.xb.cnt = 1
    rw [L1.xb]
  · show X.y.xb.J = 5120
    rw [L1.xb]
    exact hd

/-- **The tests on how the head's cells are laid pass at all public files in the goals' scope.**
-/
theorem laidOk_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : laidOk X = true := by
  have N := numbers_in_scope hZ hR h
  have S := stream_in_scope hZ hR h
  have hls : X.hS.ls = 6 := by unfold OnBytes.Model.Head.Shape.ls; rw [N.la, N.lt]
  refine @laid_of_numbers (parOf X.hS 0).sizes (parOf X.hS 0).policy (laidAt X.hS (borderOf X.y))
    N.lt hls N.d N.V N.sh N.c1 N.c2 N.la N.lPd N.XL S.nl S.off ?_ ?_
  · show (borderOf X.y).cnt * (borderOf X.y).J = 5120
    rw [S.cnt, S.J]
  · show 400 ≤ (borderOf X.y).kxb * ((borderOf X.y).mxb / 2 ^ X.hS.la)
    rw [S.kxb, S.mxb, N.la]
    decide

/-- The head's sizes at a public record in scope: the full-size record's, but for the final
normalisation's three free numbers. -/
theorem sizes_eq (N : Numbers X) :
    sizesOf X.hS = { sizesOf Cond.hFull with MF := X.hS.MF, KF := X.hS.KF, epsF := X.hS.epsF } := by
  have hls : X.hS.ls = 6 := by unfold OnBytes.Model.Head.Shape.ls; rw [N.la, N.lt]
  unfold sizesOf
  rw [N.lt, hls, N.d, N.V, N.sh, N.F]
  rfl

/-- The stored example's security lines ask no proof of work in front of a field's challenge in a
request's own rounds. -/
theorem work_ref :
    (OnBytes.Params.settingOf VerifierAndGoals.Lines.frameRef).workOf .field .request = 0 := by
  decide +kernel

/-- **The premises on public numbers that the laws on the output head ask hold at all public files
in the goals' scope.** -/
theorem k06Cond_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : K06CondAt X := by
  have N := numbers_in_scope hZ hR h
  have S := stream_in_scope hZ hR h
  have B := OnBytes.Road.Hd.public_of_core h (OnBytes.Road.Hd.core_of_scope hZ hR h)
  have hls : X.hS.ls = 6 := by unfold OnBytes.Model.Head.Shape.ls; rw [N.la, N.lt]
  have hS2 : X.hS.S2 = 64 := by unfold OnBytes.Model.Head.Shape.S2; rw [hls]
  have hfr := Meaning.HeadS.frame_in_scope hZ hR h
  have hnum : (OnBytes.Model.Head.numbers X.hS).toOption.isSome = true := by
    have hy := B.head
    unfold OnBytes.Model.Head.layout at hy
    obtain ⟨-, hy⟩ := OnBytes.Road.Hd.ok_of_needed hy
    obtain ⟨-, -, hy⟩ := OnBytes.Road.ok_of_bind hy
    obtain ⟨L0, hn, -⟩ := OnBytes.Road.ok_of_bind hy
    rw [hn]
    rfl
  have F := Cond.k06Cond_full
  have eS := sizes_eq N
  unfold K06CondAt
  exact
    { ok := ok_in_scope hZ hR h _
      admitted := (OnBytes.Road.Hd.admittedH_of_layout B.head).adm
      numbers := hnum
      features := by show 0 < X.hS.d; rw [N.d]; decide
      point := by show 0 < X.hS.lt; rw [N.lt]; decide
      rows := by rw [N.lt, N.la]; decide
      block := by rw [eS]; exact F.block
      pad := by rw [eS, N.lPd]; exact F.pad
      limbs := N.XL
      blocks := by rw [eS]; exact F.blocks
      table := by rw [eS]; exact F.table
      keys := by rw [eS]; exact F.keys
      index := by rw [eS, N.la]; exact F.index
      stream := by rw [N.d, hS2, S.kxb, S.mxb, N.la]
      origin := ⟨S.off, by rw [S.cnt, S.J, N.d]⟩
      work := by rw [hfr, work_ref]; decide
      once := rfl
      reads := by rw [show X.H.tl.ix.U.getD 2 none = some 0 from ReadsNamed.public_third h]; rfl }

theorem k07Cond_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : K07Cond X.hS := by
  unfold K07Cond
  rw [(numbers_in_scope hZ hR h).V]
  decide

theorem k06Full_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : Cond.K06Full X.hS := (numbers_in_scope hZ hR h).sh

/-- The reference model's sizes. -/
theorem k06Ref_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : Cond.K06Ref X.hS := by
  have eS := sizes_eq (numbers_in_scope hZ hR h)
  have F := Cond.k06Ref_full
  exact
    { T := by rw [eS]; exact F.T
      d := by rw [eS]; exact F.d
      V := by rw [eS]; exact F.V
      JV := by rw [eS]; exact F.JV
      F := by rw [eS]; exact F.F
      blocks := by rw [eS]; exact F.blocks
      sh := by rw [eS]; exact F.sh
      JVa := by rw [eS]; exact F.JVa }

theorem k06Whole_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : Cond.K06Whole X.hS :=
  Cond.whole_of_ref (k06Ref_in_scope hZ hR h)

/-- **The block that a lot seats passes its own test on the plan.** -/
theorem seated_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {l : Nat} {ms : List (Nat × Nat)}
    {b : VerifiableInference.Desc.Block VerifiableInference.Desc.First.S Claim}
    (hb : seatedClaims X l ms = some b) : b.planOk = true := by
  obtain ⟨b0, h0, rfl⟩ := seatedClaims_some hb
  rw [tested_planOk, Bool.and_eq_true]
  refine ⟨?_, laidOk_in_scope hZ hR h⟩
  unfold blockClaims at h0
  obtain ⟨iU3, _, rfl⟩ := Option.map_eq_some_iff.mp h0
  exact ok_in_scope hZ hR h _

/-- And there is such a block, wherever publicOf returns. -/
theorem there_in_scope (h : publicOf Z.pol Z.KL lay = .ok X) (l : Nat) (ms : List (Nat × Nat)) :
    (seatedClaims X l ms).isSome = true := by
  unfold seatedClaims blockClaims
  rw [show X.H.tl.ix.U.getD 2 none = some 0 from ReadsNamed.public_third h]
  rfl

/-- **The next token's block passes its own test on the plan.** -/
theorem reply_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (l : Nat) : (Reply.blockOf X l).planOk = true := by
  show Decidable.decide (2 ≤ X.hS.V) = true
  rw [(numbers_in_scope hZ hR h).V]
  decide

end VerifiableInference.Desc.Kinds.Head.Law.InScope

#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.planOk_of_numbers
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.numbers_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.ok_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.stream_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.laidOk_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.k06Cond_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.k07Cond_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.work_ref
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.k06Ref_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.seated_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.there_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.reply_in_scope
