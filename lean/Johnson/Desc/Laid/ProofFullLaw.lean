-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Laid/ProofFullLaw.lean: what Johnson/Desc/Laid/ProofFull.lean's value is, as equations,
at the full size.

  instOf_request | instOf_key | instOf_reply | requests_to_instances
                      what `instanceAsPlainRecord` lays: the request file's bytes, the record's key, the reply
                      file's bytes
  runPOf_eq           `proofDecisionOfDescription F` is F's run at `instanceAsPlainRecord z`
  pull_data           the data of a description that is pulled along a map are the description's
  planOk_of_planWord | planWord_of_planOk
                      the plan's word is none just where its tests say yes
  planOk_of_run       a yes of a description's run: its tests on the plan have said yes
  data_depth          the data that a description's own road makes stand at its depth of the table
  laidOfDesc_iff      **what is laid of a description, both ways**: its tests on the plan say yes,
                      the data are its own, every test that the laws ask says yes, the decision is
                      `(F.pull instanceAsPlainRecord).run`
  laidPOf_ok | laidPOf_of
                      **where the value is laid**, and the converse: a description F was made of the
                      three files, and the four of `laidOfDesc_iff`
  laidPOf_depth | laidPOf_run
                      the laid data stand at F's depth of the table; the laid decision at z is F's
                      run at `instanceAsPlainRecord z`
  laidOk_iff          `laidOk` says yes just where the value is laid, and then `laidData` and
                      `laidRun` are its two parts
  laidRun_no | laidData_empty
                      where `laidOk` says no, the decision says no to all and the data are those of
                      three empty lists

Limits: what follows from the definitions by unfolding. Nothing is said on what a yes of F's run
gives, on whether `instanceAsPlainRecord` loses anything of a request, or on whether a description is made at given
files. Nothing ties F's plan to the frame's.

-/
import Johnson.Desc.Laid.ProofFull
import Johnson.Desc.Laid.AsksFirstLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD.Full
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat OnBytes.Slice OnBytes.Maker
open OnBytes
open VerifiableInference.Desc (FileDescription)

/-- The instance's request is the request file's bytes. -/
theorem instOf_request (z : XF × RecFull) : (instanceAsPlainRecord z).pub.request = requestBytesOf z.1.val := by
  dsimp only [instanceAsPlainRecord, instPartsOf]

/-- The instance's key is the key that is written of the entry's record. -/
theorem instOf_key (z : XF × RecFull) :
    (instanceAsPlainRecord z).pub.key = keyOf (fun β : NZ => β.val) z.2 := rfl

/-- What the instance asks is the reply file's bytes. -/
theorem instOf_reply (z : XF × RecFull) : (instanceAsPlainRecord z).y = replyBytesOf z.1.val := rfl

/-- **The three equations together.** -/
theorem requests_to_instances (z : XF × RecFull) :
    (instanceAsPlainRecord z).pub.request = requestBytesOf z.1.val ∧
      (instanceAsPlainRecord z).pub.key = keyOf (fun β : NZ => β.val) z.2 ∧
      (instanceAsPlainRecord z).y = replyBytesOf z.1.val :=
  ⟨instOf_request z, instOf_key z, instOf_reply z⟩

/-- The decision at a description is the description's run at `instanceAsPlainRecord z`. -/
theorem runPOf_eq (F : FileDescription ProofFile.Inst) (z : XF × RecFull) (v₁ v₂ v₃ : _root_.Fmt.View) :
    proofDecisionOfDescription F z v₁ v₂ v₃ = F.run (instanceAsPlainRecord z) v₁ v₂ v₃ := rfl

/-- The data of a description that is pulled along a map are the description's. -/
theorem pull_data {Xi Xi' : Type} (f : Xi' → Xi) (G : FileDescription Xi) (file : String) :
    (G.pull f).data file = G.data file := rfl

/-- Where the plan's word is none, the tests on the plan say yes. -/
theorem planOk_of_planWord {Xi : Type} (G : FileDescription Xi) (h : G.planWord = none) :
    G.planOk = true := by
  cases hp : G.planOk with
  | true => rfl
  | false =>
    unfold FileDescription.planWord at h
    rw [hp] at h
    cases h

/-- Where the tests on the plan say yes, the plan's word is none. -/
theorem planWord_of_planOk {Xi : Type} (G : FileDescription Xi) (h : G.planOk = true) :
    G.planWord = none := by
  unfold FileDescription.planWord
  rw [h]
  rfl

/-- A yes of a description's run: its tests on the plan have said yes. -/
theorem planOk_of_run {Xi : Type} (G : FileDescription Xi) {x : Xi} {v₁ v₂ v₃ : _root_.Fmt.View}
    (h : G.run x v₁ v₂ v₃ = true) : G.planOk = true := by
  cases hw : G.planWord with
  | none => exact planOk_of_planWord G hw
  | some w =>
    have he : G.runEnd x v₁ v₂ v₃ = .error w := by
      unfold FileDescription.runEnd VerifiableInference.Desc.runCore
      rw [hw]
      rfl
    unfold FileDescription.run at h
    rw [he] at h
    cases h

/-- The data that a description's own road makes stand at its depth of the table. -/
theorem data_depth {Xi : Type} (G : FileDescription Xi) {file : String} {D : WholeD}
    (h : G.data file = .ok D) : D.a = G.tableDepth := by
  unfold FileDescription.data at h
  cases hR : Johnson.G.OfPlan.writtenOf file G.roundsDeclaredByBlocks with
  | error e => rw [hR] at h; cases h
  | ok R =>
    rw [hR] at h
    by_cases ho : okAt G.tableDepth (some R) = true
    · simp [ho, bind, Except.bind, pure, Except.pure] at h
      rw [← h]
      rfl
    · simp [ho, bind, Except.bind] at h

/-- **What is laid of a description, both ways.** -/
theorem laidOfDesc_iff (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription ProofFile.Inst)
    (D : WholeD) (r : RunPF) :
    proofDataAndDecisionOfDescription o pol lay KL F = .ok (D, r) ↔
      F.planOk = true ∧ F.data "proof file" = .ok D ∧
        (∀ t ∈ _root_.LPFD.lawsAsk o pol lay KL F D, t.2 = true) ∧ r = (F.pull instanceAsPlainRecord).run := by
  constructor
  · intro h
    unfold proofDataAndDecisionOfDescription at h
    cases hw : F.planWord with
    | some w => rw [hw] at h; cases h
    | none =>
      rw [hw] at h
      dsimp only at h
      cases hD : F.data "proof file" with
      | error e => rw [hD] at h; cases h
      | ok D' =>
        rw [hD] at h
        dsimp only at h
        cases hs : _root_.LPFD.firstNo (_root_.LPFD.lawsAsk o pol lay KL F D') with
        | some t => rw [hs] at h; cases h
        | none =>
          rw [hs] at h
          dsimp only at h
          have e := Except.ok.inj h
          have e₁ : D' = D := congrArg Prod.fst e
          have e₂ : proofDecisionOfDescription F = r := congrArg Prod.snd e
          subst e₁
          exact ⟨planOk_of_planWord F hw, rfl, (_root_.LPFD.firstNo_none _).1 hs, e₂.symm⟩
  · rintro ⟨hp, hD, hs, rfl⟩
    unfold proofDataAndDecisionOfDescription
    rw [planWord_of_planOk F hp]
    dsimp only
    rw [hD]
    dsimp only
    rw [(_root_.LPFD.firstNo_none _).2 hs]
    rfl

variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}

/-- **Where the value is laid.** -/
theorem laidPOf_ok {D : WholeD} {r : RunPF} (h : proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r)) :
    ∃ F, ProofFile.onlineDescription o pol lay KL = .ok F ∧ F.planOk = true ∧ F.data "proof file" = .ok D ∧
      (∀ t ∈ _root_.LPFD.lawsAsk o pol lay KL F D, t.2 = true) ∧ r = (F.pull instanceAsPlainRecord).run := by
  unfold proofDataAndDecisionOfPublicFiles at h
  cases hd : ProofFile.onlineDescription o pol lay KL with
  | error e => rw [hd] at h; cases h
  | ok F =>
    rw [hd] at h
    exact ⟨F, rfl, (laidOfDesc_iff o pol lay KL F D r).1 h⟩

/-- The converse. -/
theorem laidPOf_of {F : FileDescription ProofFile.Inst} {D : WholeD}
    (hd : ProofFile.onlineDescription o pol lay KL = .ok F) (hp : F.planOk = true)
    (hD : F.data "proof file" = .ok D)
    (hs : ∀ t ∈ _root_.LPFD.lawsAsk o pol lay KL F D, t.2 = true) :
    proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, (F.pull instanceAsPlainRecord).run) := by
  unfold proofDataAndDecisionOfPublicFiles
  rw [hd]
  exact (laidOfDesc_iff o pol lay KL F D _).2 ⟨hp, hD, hs, rfl⟩

/-- The laid data stand at the description's depth of the table. -/
theorem laidPOf_depth {D : WholeD} {r : RunPF} (h : proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r)) :
    ∃ F, ProofFile.onlineDescription o pol lay KL = .ok F ∧ D.a = F.tableDepth := by
  obtain ⟨F, hd, -, hD, -, -⟩ := laidPOf_ok h
  exact ⟨F, hd, data_depth F hD⟩

/-- The laid decision at z is the description's run at `instanceAsPlainRecord z`. -/
theorem laidPOf_run {D : WholeD} {r : RunPF} (h : proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r)) :
    ∃ F, ProofFile.onlineDescription o pol lay KL = .ok F ∧
      ∀ z v₁ v₂ v₃, r z v₁ v₂ v₃ = F.run (instanceAsPlainRecord z) v₁ v₂ v₃ := by
  obtain ⟨F, hd, -, -, -, hr⟩ := laidPOf_ok h
  exact ⟨F, hd, fun z v₁ v₂ v₃ => by rw [hr]; rfl⟩

/-- **`laidOk` says yes just where the value is laid, and then the two letters are its parts.** -/
theorem laidOk_iff :
    laidOk o pol lay KL = true ↔
      proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (laidData o pol lay KL, laidRun o pol lay KL) := by
  unfold laidOk laidData laidRun
  cases proofDataAndDecisionOfPublicFiles o pol lay KL with
  | error e => simp [Except.isOk, Except.toBool]
  | ok x => simp [Except.isOk, Except.toBool]

/-- Where `laidOk` says no, the decision says no to all. -/
theorem laidRun_no (h : laidOk o pol lay KL = false) (z : XF × RecFull)
    (v₁ v₂ v₃ : _root_.Fmt.View) : laidRun o pol lay KL z v₁ v₂ v₃ = false := by
  unfold laidOk at h
  unfold laidRun
  cases hl : proofDataAndDecisionOfPublicFiles o pol lay KL with
  | error e => rfl
  | ok x => rw [hl] at h; simp [Except.isOk, Except.toBool] at h

/-- Where `laidOk` says no, the data are those of three empty lists. -/
theorem laidData_empty (h : laidOk o pol lay KL = false) : laidData o pol lay KL = emptyD := by
  unfold laidOk at h
  unfold laidData
  cases hl : proofDataAndDecisionOfPublicFiles o pol lay KL with
  | error e => rfl
  | ok x => rw [hl] at h; simp [Except.isOk, Except.toBool] at h

end LPFD.Full

#print axioms LPFD.Full.requests_to_instances
#print axioms LPFD.Full.planOk_of_run
#print axioms LPFD.Full.laidOfDesc_iff
#print axioms LPFD.Full.laidPOf_ok
#print axioms LPFD.Full.laidPOf_of
#print axioms LPFD.Full.laidPOf_depth
#print axioms LPFD.Full.laidPOf_run
#print axioms LPFD.Full.laidOk_iff
#print axioms LPFD.Full.laidRun_no
#print axioms LPFD.Full.laidData_empty
