-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyPayClauses.lean: theorems. From the public tests on a key file's source (Bool; Johnson/Desc/Key/Source.lean: sourceClauses, sourceOk, instanceOk) to propositions, clause by clause. It speaks of that file alone: of no
description. The laws are those of two other files (not in this library), letter for letter, gathered so that they can stand beneath any description that asks these tests.
  clause_of_ok · Fits | fits_of_joinOk · Tied | tied_of_ok | Tied.numbers · oneLeaf_of_ok · Front1 | front1_of_ok · TestFits | Tests | tests_of_ok · Start | start_of_okStart · Cut | cut_of_ok · Sizes | sizes_of_fits
  setting_of_ok    one number of samples in the three plans
  read_of_ok | made_of_ok   the values are a reading of their own bytes; the declared rounds and the tenants are what the rule makes of the values alone
Limits. oneLeaf_of_ok: binding.logLeaves = 0: that the wire's depth of the request tree is made of that number is said nowhere. Start.factors speaks of words (isZeroE): «not 0 in the field» wants the bound on the key's words beside it
(instanceOk asks it: Start.record | Start.seeds; the law: KeyPayD.lean's factors). Several conclusions are Bool equations of `verify-on-bytes`'s own pure tests (Wf.admitted · Lkp.Public.ok · ioppOk · linOk): what these give is their spenders' matter. Nothing on soundness is claimed.

-/
import Johnson.Desc.Key.Source

set_option autoImplicit false

namespace Johnson.RunOne.KeyPay

open OnBytes OnBytes.Params VerifiableInference.Desc.Key

theorem clause_of_ok {Y : KeySource} (h : sourceOk Y = true) {n : String} {b : Bool} (hm : (n, b) ∈ sourceClauses Y) : b = true := by
  unfold sourceOk at h
  exact (List.all_eq_true.mp h) (n, b) hm

/-- A message's shape says that it is sampled, and has a group's two codes where it has such rows. -/
structure Fits (code maskCode : Nat) (s : OracleShape) : Prop where
  sampled : s.answers ≠ 0
  main : s.mainRows = 0 ∨ s.code = code
  mask : s.maskRows = 0 ∨ s.maskCode = maskCode

theorem fits_of_joinOk {codes : Codes} {code maskCode : Nat} {members : List OracleShape} (h : joinPublicOk codes code maskCode members = true) :
    ∀ s ∈ members, Fits code maskCode s := by
  intro s hs
  unfold joinPublicOk at h
  rw [Bool.and_eq_true] at h
  have := (List.all_eq_true.mp h.2) s hs
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, ne_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- What ties blocks of different chains. -/
structure Tied (k : KeyChains) : Prop where
  codes : k.oneTime.codes = k.shared.codes
  shape : k.oneTime.lin = k.shared.lin
  idx : Fits k.shared.lin.w.code k.shared.lin.ownMaskCode k.oneTime.indexMasks.shape
  w : Fits k.shared.lin.w.code k.shared.lin.ownMaskCode k.shared.lin.w
  omega : Fits k.shared.lin.w.code k.shared.lin.ownMaskCode k.shared.lin.omega

theorem tied_of_ok {Y : KeySource} (h : sourceOk Y = true) : Tied Y.k := by
  have hc := clause_of_ok h (n := "codes") (b := sameItem Y.k.oneTime.given Y.k.shared.given "codes" && Y.k.oneTime.codes == Y.k.shared.codes) (by simp [sourceClauses])
  have hs := clause_of_ok h (n := "shape") (b := sameItem Y.k.oneTime.given Y.k.shared.given "the test on the table" && Y.k.oneTime.lin == Y.k.shared.lin) (by simp [sourceClauses])
  have hj := clause_of_ok h (n := "join.own")
    (b := joinPublicOk Y.k.shared.codes Y.k.shared.lin.w.code Y.k.shared.lin.ownMaskCode [Y.k.oneTime.indexMasks.shape, Y.k.shared.lin.w, Y.k.shared.lin.omega]) (by simp [sourceClauses])
  simp only [Bool.and_eq_true, beq_iff_eq] at hc hs
  have f := fits_of_joinOk hj
  exact ⟨hc.2, hs.2, f _ (by simp), f _ (by simp), f _ (by simp)⟩

/-- The numbers of the table are one value in the chains. -/
theorem Tied.numbers {k : KeyChains} (t : Tied k) :
    k.oneTime.lin.kLo = k.shared.lin.kLo ∧ k.oneTime.lin.kCol = k.shared.lin.kCol ∧ k.oneTime.lin.matrixRows = k.shared.lin.matrixRows := by
  rw [t.shape]; exact ⟨rfl, rfl, rfl⟩

theorem oneLeaf_of_ok {Y : KeySource} (h : sourceOk Y = true) : Y.k.oneTime.binding.logLeaves = 0 := by
  have := clause_of_ok h (n := "binding") (b := Y.k.oneTime.binding.logLeaves == 0) (by simp [sourceClauses])
  simpa using this

/-- Of chain 1 as a whole. -/
structure Front1 (o : OneTime) : Prop where
  samples : o.ranges.message.shape.answers = o.given.plan.samples
  messageId : o.ranges.messageId = 1
  admitted : Wf.admitted o.codes o.ranges (Wf.matrixOf o.lin) = true
  lookups : ∀ S ∈ Wf.lookupsOf o.ranges (Wf.matrixOf o.lin), S.ok = true
  lin : linOk o.codes o.lin = true

theorem front1_of_ok {Y : KeySource} (h : sourceOk Y = true) : Front1 Y.k.oneTime := by
  have h1 := clause_of_ok h (n := "samples") (b := Y.k.oneTime.ranges.message.shape.answers == Y.k.oneTime.given.plan.samples) (by simp [sourceClauses])
  have h2 := clause_of_ok h (n := "messageId") (b := Y.k.oneTime.ranges.messageId == 1) (by simp [sourceClauses])
  have h3 := clause_of_ok h (n := "ranges") (b := Wf.admitted Y.k.oneTime.codes Y.k.oneTime.ranges (Wf.matrixOf Y.k.oneTime.lin)) (by simp [sourceClauses])
  have h4 := clause_of_ok h (n := "lookups") (b := (Wf.lookupsOf Y.k.oneTime.ranges (Wf.matrixOf Y.k.oneTime.lin)).all (·.ok)) (by simp [sourceClauses])
  have h5 := clause_of_ok h (n := "lin") (b := linOk Y.k.oneTime.codes Y.k.oneTime.lin) (by simp [sourceClauses])
  exact ⟨by simpa using h1, by simpa using h2, h3, fun S hS => (List.all_eq_true.mp h4) S hS, h5⟩

/-- A proximity test's public side: its stages' sizes fit under the codes and the samples; its group's two codes are its first stage's. -/
structure TestFits (codes : Codes) (samples : Nat) (stages : List IoppStage) (code maskCode : Nat) : Prop where
  sizes : ioppOk codes stages samples = true
  first : ∃ t, stages.head? = some t ∧ t.code = code ∧ t.maskCode = maskCode

theorem testFits_of_testOk {codes : Codes} {samples : Nat} {stages : List IoppStage} {code maskCode : Nat} (h : testPublicOk codes samples stages code maskCode = true) :
    TestFits codes samples stages code maskCode := by
  unfold testPublicOk at h
  rw [Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  cases hh : stages.head? with
  | none => rw [hh] at h; simp at h
  | some t =>
    rw [hh] at h
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨t, rfl, h.2.1, h.2.2⟩

/-- The four tests, under ONE list of codes and ONE number of samples. -/
structure Tests (k : KeyChains) : Prop where
  rng : TestFits k.oneTime.codes k.oneTime.given.plan.samples k.oneTime.ranges.stages k.oneTime.ranges.message.shape.code k.oneTime.ranges.message.shape.maskCode
  u : TestFits k.oneTime.codes k.oneTime.given.plan.samples k.shared.lin.testU k.shared.lin.fold.u.code k.shared.lin.sharedMaskCode
  omega : TestFits k.oneTime.codes k.oneTime.given.plan.samples k.shared.lin.testOmega k.shared.lin.omega.code k.shared.lin.sharedMaskCode
  own : TestFits k.oneTime.codes k.oneTime.given.plan.samples k.shared.lin.testOwn k.shared.lin.w.code k.shared.lin.ownMaskCode

theorem tests_of_ok {Y : KeySource} (h : sourceOk Y = true) : Tests Y.k := by
  have t := tied_of_ok h
  have h1 := clause_of_ok h (n := "test.rng")
    (b := testPublicOk Y.k.oneTime.codes Y.k.oneTime.given.plan.samples Y.k.oneTime.ranges.stages Y.k.oneTime.ranges.message.shape.code Y.k.oneTime.ranges.message.shape.maskCode) (by simp [sourceClauses])
  have h2 := clause_of_ok h (n := "test.U")
    (b := testPublicOk Y.k.shared.codes Y.k.oneTime.given.plan.samples Y.k.shared.lin.testU Y.k.shared.lin.fold.u.code Y.k.shared.lin.sharedMaskCode) (by simp [sourceClauses])
  have h3 := clause_of_ok h (n := "test.O")
    (b := testPublicOk Y.k.shared.codes Y.k.oneTime.given.plan.samples Y.k.shared.lin.testOmega Y.k.shared.lin.omega.code Y.k.shared.lin.sharedMaskCode) (by simp [sourceClauses])
  have h4 := clause_of_ok h (n := "test.own")
    (b := testPublicOk Y.k.shared.codes Y.k.oneTime.given.plan.samples Y.k.shared.lin.testOwn Y.k.shared.lin.w.code Y.k.shared.lin.ownMaskCode) (by simp [sourceClauses])
  rw [← t.codes] at h2 h3 h4
  exact ⟨testFits_of_testOk h1, testFits_of_testOk h2, testFits_of_testOk h3, testFits_of_testOk h4⟩

/-- The instance. -/
structure Start (S : LinShape) (x : Xi) : Prop where
  item : x.key.item = 0
  fits : x.key.fits S.fold.index = true
  /-- every word of the key is below the prime: the record's answers; each seed's point and factor -/
  record : ∀ a ∈ x.key.record.toList, okE a = true
  seeds : ∀ z ∈ x.key.seeds, okE z.beta = true ∧ ∀ a ∈ z.z, okE a = true
  factors : ∀ z ∈ x.key.seeds, isZeroE z.beta = false

theorem start_of_okStart {S : LinShape} {x : Xi} (h : instanceOk S x = true) : Start S x := by
  unfold instanceOk keyWordsBelow at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := h
  rw [← Array.all_toList] at h3
  refine ⟨h1, h2, fun a ha => (List.all_eq_true.mp h3) a ha, fun z hz => ?_, fun z hz => ?_⟩
  · have := (List.all_eq_true.mp h4) z hz
    rw [Bool.and_eq_true] at this
    exact ⟨this.2, fun a ha => (List.all_eq_true.mp this.1) a ha⟩
  · have := (List.all_eq_true.mp h5) z hz
    simpa using this

/-- The clause «cut», as equations. -/
structure Cut (Y : KeySource) : Prop where
  shape : Y.cutShape = Y.k.oneTime.lin
  codes₁ : Y.cutCodes.1 = Y.k.oneTime.codes
  codes₂ : Y.cutCodes.2.1 = Y.k.oneTime.codes
  codes₃ : Y.cutCodes.2.2 = Y.k.oneTime.codes
  idx : Y.cutIdx = Y.k.oneTime.indexMasks
  ranges : Y.cutRanges = Y.k.oneTime.ranges
  samples : Y.cutSamples = Y.k.oneTime.given.plan.samples

theorem cut_of_ok {Y : KeySource} (h : sourceOk Y = true) : Cut Y := by
  have hc := clause_of_ok h (n := "cut")
    (b := Y.cutShape == Y.k.oneTime.lin && Y.cutCodes.1 == Y.k.oneTime.codes && Y.cutCodes.2.1 == Y.k.oneTime.codes && Y.cutCodes.2.2 == Y.k.oneTime.codes && Y.cutIdx == Y.k.oneTime.indexMasks &&
      Y.cutRanges == Y.k.oneTime.ranges && Y.cutSamples == Y.k.oneTime.given.plan.samples) (by simp [sourceClauses])
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  exact ⟨hc.1.1.1.1.1.1, hc.1.1.1.1.1.2, hc.1.1.1.1.2, hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩

/-- The key's sizes. -/
structure Sizes (key : TableKey) (s : IndexShape) : Prop where
  record : key.record.size = s.rows * s.answers
  seeds : key.seeds.length = s.answers
  points : ∀ z ∈ key.seeds, z.z.length = s.cubeBits

theorem sizes_of_fits {key : TableKey} {s : IndexShape} (h : key.fits s = true) : Sizes key s := by
  unfold TableKey.fits at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, fun z hz => by simpa using (List.all_eq_true.mp h.2) z hz⟩

/-- **«read»**: the values are a reading of their own bytes: the program's own reader, at the bytes that the three chains' values hold as «the bytes as they are hashed», returns a key that is the same, field by field. -/
theorem read_of_ok {Y : KeySource} (h : sourceOk Y = true) :
    ∃ k', KeyChains.read Y.k.oneTime.given.bytes Y.k.shared.given.bytes Y.k.second.given.bytes = some k' ∧ sameKeyChains k' Y.k = true := by
  have hr := clause_of_ok h (n := "read") (b := readAgainOk Y.k) (by simp [sourceClauses])
  unfold readAgainOk at hr
  cases hk : KeyChains.read Y.k.oneTime.given.bytes Y.k.shared.given.bytes Y.k.second.given.bytes with
  | none => rw [hk] at hr; cases hr
  | some k' => rw [hk] at hr; exact ⟨k', rfl, hr⟩

/-- **«made»**: the declared rounds are what the rule (madeAgain) makes of the values alone; the tenants as told likewise (as that test's own Bool on them). -/
theorem made_of_ok {Y : KeySource} (h : sourceOk Y = true) : ∃ x, madeAgain Y.k = .ok x ∧ x.1 = Y.D ∧ (x.2 == Y.told) = true := by
  have hr := clause_of_ok h (n := "made") (b := madeAgainOk Y) (by simp [sourceClauses])
  unfold madeAgainOk at hr
  cases hk : madeAgain Y.k with
  | error e => rw [hk] at hr; cases hr
  | ok x =>
    rw [hk] at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    exact ⟨x, rfl, hr.1, hr.2⟩

/-- One number of samples in the three plans. -/
theorem setting_of_ok {Y : KeySource} (h : sourceOk Y = true) :
    Y.k.oneTime.given.plan.samples = Y.k.shared.given.plan.samples ∧ Y.k.oneTime.given.plan.samples = Y.k.second.given.plan.samples := by
  have hs := clause_of_ok h (n := "setting")
    (b := sameSetting Y.k.oneTime.given Y.k.shared.given && sameSetting Y.k.oneTime.given Y.k.second.given && Y.k.shared.given.record.isNone && Y.k.second.given.record.isNone) (by simp [sourceClauses])
  simp only [sameSetting, Bool.and_eq_true, beq_iff_eq] at hs
  exact ⟨hs.1.1.1.1.1.2, hs.1.1.2.1.1.2⟩

end Johnson.RunOne.KeyPay

#print axioms Johnson.RunOne.KeyPay.tied_of_ok
#print axioms Johnson.RunOne.KeyPay.front1_of_ok
#print axioms Johnson.RunOne.KeyPay.tests_of_ok
#print axioms Johnson.RunOne.KeyPay.start_of_okStart
#print axioms Johnson.RunOne.KeyPay.cut_of_ok
#print axioms Johnson.RunOne.KeyPay.sizes_of_fits
#print axioms Johnson.RunOne.KeyPay.setting_of_ok
#print axioms Johnson.RunOne.KeyPay.read_of_ok
#print axioms Johnson.RunOne.KeyPay.made_of_ok
