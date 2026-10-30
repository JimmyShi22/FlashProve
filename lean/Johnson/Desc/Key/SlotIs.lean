-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/SlotIs.lean: what the key file's piece for the verifier's text is
(Johnson/Desc/Key/Slot.lean): where it is made, its decision is the run of `descriptionFromSource X N P`, pulled to
the records, its data are that description's own, and that description passes its tests on the plan,
the two tests beside them and the door's; and X, N, P are made of the planner's answer at the same
files. So a law that speaks of `(descriptionFromSource X N P).pull keyInstanceOfOutOfDomainSample` speaks of the decision that is laid.

Main names.
  descOfMade_is: where `descriptionFromPlan m` returns F there are X, N, P, made of m by `sourceOf`,
    `rangesNumbers`, `laterPlaces`, with F = `descriptionFromSource X N P`.
  descAt_is: where `descAt Z lay cfg` returns F, `madeAt Z lay cfg` returns some m, and the same
    holds at m.
  planOk_of_planWord: the tests on the plan have no word to say only where they say yes.
  planWord_of_planOk: and there they have none.
  laidOfDesc_iff: `keyDataAndDecisionOfDescription F` returns (D, r) just where F.planOk = true, F.wantedOk = true,
    F.owedOk = true, F.data "key file" = .ok D and r = (F.pull keyInstanceOfOutOfDomainSample).run.
  laidOfMade_iff: `keyDataAndDecisionOfPlannerAnswer X lay m` returns (D, r) just where `descriptionFromPlan m` returns some F,
    `keyDataAndDecisionOfDescription F` returns (D, r), and every test of the door `lawsAsk X lay m F D` says yes.
  laidAt_is, laidFixed_is: where the piece is returned: F = `descriptionFromSource X N P`, what ties X, N,
    P to the arguments (they are made of m, and m is what `madeAt` returns), and all that was
    asked: the tests on the plan, the two beside them, the door's, the data, the decision.
  laidAt_of, laidFixed_of: the converse: what was asked gives the piece.
  fixedDigest_size, fixedDigest_ne: the fixed digest has 32 bytes and is not 32 zero bytes.
  laidOk_iff, laidRun_no, laidData_empty: the three total letters of a piece: `laidOk` says yes
    just where the piece is (`laidData`, `laidRun`); where it says no, `laidRun` says no to all and
    `laidData` is `emptyData`.
  pulled_is: the tests on the plan and the data are the same at the description pulled to the
    records.

Limits. By unfolding. That a piece is returned at any files is not shown. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.Slot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Maker

theorem descOfMade_is (m : Johnson.G.OfPlan.Made) (F : FileDescription Xi) (h : descriptionFromPlan m = .ok F) :
    ∃ X N P, sourceOf m = .ok X ∧ rangesNumbers m = .ok N ∧ laterPlaces m = .ok P ∧
      F = descriptionFromSource X N P := by
  unfold descriptionFromPlan at h
  split at h
  · rename_i X N P hX hN hP
    exact ⟨X, N, P, hX, hN, hP, (Except.ok.inj h).symm⟩
  · cases h
  · cases h
  · cases h

theorem descAt_is (Z : Model.Verify.Public) (lay cfg : ByteArray) (F : FileDescription Xi)
    (h : descAt Z lay cfg = .ok F) :
    ∃ m X N P, madeAt Z lay cfg = .ok m ∧ sourceOf m = .ok X ∧ rangesNumbers m = .ok N ∧
      laterPlaces m = .ok P ∧ F = descriptionFromSource X N P := by
  unfold descAt at h
  cases hm : madeAt Z lay cfg with
  | error e =>
    rw [hm] at h
    cases h
  | ok m =>
    rw [hm] at h
    obtain ⟨X, N, P, hX, hN, hP, e⟩ := descOfMade_is m F h
    exact ⟨m, X, N, P, rfl, hX, hN, hP, e⟩

/-- The tests on the plan have no word to say only where they say yes. -/
theorem planOk_of_planWord (F : FileDescription Xi) (h : F.planWord = none) : F.planOk = true := by
  unfold FileDescription.planWord at h
  split at h
  · assumption
  · cases h

/-- Where the tests on the plan say yes they have no word to say. -/
theorem planWord_of_planOk (F : FileDescription Xi) (h : F.planOk = true) : F.planWord = none := by
  unfold FileDescription.planWord
  rw [if_pos h]

/-- **What the data and the decision of a description are, and when they are given.** -/
theorem laidOfDesc_iff (F : FileDescription Xi) (D : WholeD) (r : KeyRun) :
    keyDataAndDecisionOfDescription F = .ok (D, r) ↔ F.planOk = true ∧ F.wantedOk = true ∧ F.owedOk = true ∧
      F.data "key file" = .ok D ∧ r = (F.pull keyInstanceOfOutOfDomainSample).run := by
  constructor
  · intro h
    unfold keyDataAndDecisionOfDescription at h
    split at h
    · cases h
    · rename_i hw
      cases h1 : F.wantedOk with
      | false =>
        rw [h1] at h
        cases h
      | true =>
        cases h2 : F.owedOk with
        | false =>
          rw [h1, h2] at h
          cases h
        | true =>
          rw [h1, h2] at h
          cases hd : F.data "key file" with
          | error e =>
            rw [hd] at h
            cases h
          | ok D' =>
            rw [hd] at h
            have e : (D', (F.pull keyInstanceOfOutOfDomainSample).run) = (D, r) := Except.ok.inj h
            exact ⟨planOk_of_planWord F hw, rfl, rfl, congrArg Except.ok (congrArg Prod.fst e),
              (congrArg Prod.snd e).symm⟩
  · rintro ⟨hp, h1, h2, hd, rfl⟩
    unfold keyDataAndDecisionOfDescription
    rw [planWord_of_planOk F hp, h1, h2, hd]
    rfl

/-- No test of a list says no just where every test of it says yes. -/
theorem find_no_none (l : List (String × Bool)) :
    l.find? (!·.2) = none ↔ ∀ t ∈ l, t.2 = true := by
  simp [List.find?_eq_none]

/-- **What the key file's piece is, and when it is given**, of the planner's answer and the
sendings. -/
theorem laidOfMade_iff (X : Model.Verify.Public) (lay : ByteArray) (m : Johnson.G.OfPlan.Made)
    (D : WholeD) (r : KeyRun) :
    keyDataAndDecisionOfPlannerAnswer X lay m = .ok (D, r) ↔ ∃ F, descriptionFromPlan m = .ok F ∧ keyDataAndDecisionOfDescription F = .ok (D, r) ∧
      ∀ t ∈ lawsAsk X lay m F D, t.2 = true := by
  constructor
  · intro h
    unfold keyDataAndDecisionOfPlannerAnswer at h
    cases hF : descriptionFromPlan m with
    | error e =>
      rw [hF] at h
      cases h
    | ok F =>
      rw [hF] at h
      cases hx : keyDataAndDecisionOfDescription F with
      | error e =>
        have h' : ((keyDataAndDecisionOfDescription F).bind fun x =>
          match (lawsAsk X lay m F x.1).find? (!·.2) with
          | some t => (.error ("the key file's description: " ++ t.1) : KeyDataAndDecisionOrRefusal)
          | none => .ok x) = .ok (D, r) := h
        rw [hx] at h'
        cases h'
      | ok x =>
        have h' : ((keyDataAndDecisionOfDescription F).bind fun x =>
          match (lawsAsk X lay m F x.1).find? (!·.2) with
          | some t => (.error ("the key file's description: " ++ t.1) : KeyDataAndDecisionOrRefusal)
          | none => .ok x) = .ok (D, r) := h
        rw [hx] at h'
        have h2 : (match (lawsAsk X lay m F x.1).find? (!·.2) with
          | some t => (.error ("the key file's description: " ++ t.1) : KeyDataAndDecisionOrRefusal)
          | none => .ok x) = .ok (D, r) := h'
        cases hf : (lawsAsk X lay m F x.1).find? (!·.2) with
        | some t =>
          rw [hf] at h2
          cases h2
        | none =>
          rw [hf] at h2
          obtain rfl : x = (D, r) := Except.ok.inj h2
          exact ⟨F, rfl, hx, (find_no_none _).1 hf⟩
  · rintro ⟨F, hF, hx, ha⟩
    unfold keyDataAndDecisionOfPlannerAnswer
    rw [hF]
    show ((keyDataAndDecisionOfDescription F).bind fun x =>
      match (lawsAsk X lay m F x.1).find? (!·.2) with
      | some t => (.error ("the key file's description: " ++ t.1) : KeyDataAndDecisionOrRefusal)
      | none => .ok x) = .ok (D, r)
    rw [hx]
    show (match (lawsAsk X lay m F D).find? (!·.2) with
      | some t => (.error ("the key file's description: " ++ t.1) : KeyDataAndDecisionOrRefusal)
      | none => .ok (D, r)) = .ok (D, r)
    rw [(find_no_none _).2 ha]

/-- **What the key file's piece is**, at what the program has read, the layout file and a digest. -/
theorem laidAt_is (Z : Model.Verify.Public) (lay cfg : ByteArray) (D : WholeD) (r : KeyRun)
    (h : keyDataAndDecisionAtDigest Z lay cfg = .ok (D, r)) :
    ∃ m X N P, madeAt Z lay cfg = .ok m ∧ sourceOf m = .ok X ∧ rangesNumbers m = .ok N ∧
      laterPlaces m = .ok P ∧ descAt Z lay cfg = .ok (descriptionFromSource X N P) ∧
      (descriptionFromSource X N P).planOk = true ∧ (descriptionFromSource X N P).wantedOk = true ∧ (descriptionFromSource X N P).owedOk = true ∧
      (∀ t ∈ lawsAsk Z lay m (descriptionFromSource X N P) D, t.2 = true) ∧
      (descriptionFromSource X N P).data "key file" = .ok D ∧ r = ((descriptionFromSource X N P).pull keyInstanceOfOutOfDomainSample).run := by
  unfold keyDataAndDecisionAtDigest at h
  cases hm : madeAt Z lay cfg with
  | error e =>
    rw [hm] at h
    cases h
  | ok m =>
    rw [hm] at h
    obtain ⟨F, hF, hx, ha⟩ := (laidOfMade_iff Z lay m D r).1 h
    obtain ⟨X, N, P, hX, hN, hP, rfl⟩ := descOfMade_is m F hF
    obtain ⟨h1, h2, h3, h4, h5⟩ := (laidOfDesc_iff _ D r).1 hx
    refine ⟨m, X, N, P, rfl, hX, hN, hP, ?_, h1, h2, h3, ha, h4, h5⟩
    unfold descAt
    rw [hm]
    exact hF

/-- **The converse**: what was asked gives the piece. -/
theorem laidAt_of (Z : Model.Verify.Public) (lay cfg : ByteArray) (m : Johnson.G.OfPlan.Made)
    (F : FileDescription Xi) (D : WholeD) (hm : madeAt Z lay cfg = .ok m) (hF : descriptionFromPlan m = .ok F)
    (h1 : F.planOk = true) (h2 : F.wantedOk = true) (h3 : F.owedOk = true)
    (h4 : F.data "key file" = .ok D) (ha : ∀ t ∈ lawsAsk Z lay m F D, t.2 = true) :
    keyDataAndDecisionAtDigest Z lay cfg = .ok (D, (F.pull keyInstanceOfOutOfDomainSample).run) := by
  unfold keyDataAndDecisionAtDigest
  rw [hm]
  exact (laidOfMade_iff Z lay m D _).2 ⟨F, hF, (laidOfDesc_iff F D _).2 ⟨h1, h2, h3, h4, rfl⟩, ha⟩

/-- The fixed digest has 32 bytes. -/
theorem fixedDigest_size : fixedDigest.size = 32 := rfl

/-- The fixed digest is not 32 zero bytes. -/
theorem fixedDigest_ne : (fixedDigest != Fmt.zero32) = true := by decide

/-- **What the key file's piece at the fixed digest is.** -/
theorem laidFixed_is (Z : Model.Verify.Public) (lay : ByteArray) (D : WholeD) (r : KeyRun)
    (h : keyDataAndDecisionAtFixedDigest Z lay = .ok (D, r)) :
    ∃ m X N P, madeAt Z lay fixedDigest = .ok m ∧ sourceOf m = .ok X ∧ rangesNumbers m = .ok N ∧
      laterPlaces m = .ok P ∧ descAt Z lay fixedDigest = .ok (descriptionFromSource X N P) ∧
      (descriptionFromSource X N P).planOk = true ∧ (descriptionFromSource X N P).wantedOk = true ∧ (descriptionFromSource X N P).owedOk = true ∧
      (∀ t ∈ lawsAsk Z lay m (descriptionFromSource X N P) D, t.2 = true) ∧
      (descriptionFromSource X N P).data "key file" = .ok D ∧ r = ((descriptionFromSource X N P).pull keyInstanceOfOutOfDomainSample).run :=
  laidAt_is Z lay fixedDigest D r h

/-- **The converse at the fixed digest.** -/
theorem laidFixed_of (Z : Model.Verify.Public) (lay : ByteArray) (m : Johnson.G.OfPlan.Made)
    (F : FileDescription Xi) (D : WholeD) (hm : madeAt Z lay fixedDigest = .ok m)
    (hF : descriptionFromPlan m = .ok F) (h1 : F.planOk = true) (h2 : F.wantedOk = true)
    (h3 : F.owedOk = true) (h4 : F.data "key file" = .ok D)
    (ha : ∀ t ∈ lawsAsk Z lay m F D, t.2 = true) :
    keyDataAndDecisionAtFixedDigest Z lay = .ok (D, (F.pull keyInstanceOfOutOfDomainSample).run) :=
  laidAt_of Z lay fixedDigest m F D hm hF h1 h2 h3 h4 ha

/-- **`laidOk` says yes just where the piece is laid, and then the two other letters are its
parts.** -/
theorem laidOk_iff (v : KeyDataAndDecisionOrRefusal) : laidOk v = true ↔ v = .ok (laidData v, laidRun v) := by
  cases v with
  | error e => simp [laidOk, Except.isOk, Except.toBool]
  | ok x => simp [laidOk, laidData, laidRun, Except.isOk, Except.toBool]

/-- Where `laidOk` says no, the decision says no to all. -/
theorem laidRun_no (v : KeyDataAndDecisionOrRefusal) (h : laidOk v = false) (rec : RecFull) (v₁ v₂ v₃ : Fmt.View) :
    laidRun v rec v₁ v₂ v₃ = false := by
  cases v with
  | error e => rfl
  | ok x => simp [laidOk, Except.isOk, Except.toBool] at h

/-- Where `laidOk` says no, the data are those of three empty lists. -/
theorem laidData_empty (v : KeyDataAndDecisionOrRefusal) (h : laidOk v = false) : laidData v = emptyData := by
  cases v with
  | error e => rfl
  | ok x => simp [laidOk, Except.isOk, Except.toBool] at h

/-- The tests on the plan and the data, at the description pulled to the records: the form in which
the laws on the key file's description speak. -/
theorem pulled_is (F : FileDescription Xi) (D : WholeD) (h1 : F.planOk = true)
    (h2 : F.data "key file" = .ok D) :
    (F.pull keyInstanceOfOutOfDomainSample).planOk = true ∧ (F.pull keyInstanceOfOutOfDomainSample).data "key file" = .ok D :=
  ⟨h1, h2⟩

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.descOfMade_is
#print axioms VerifiableInference.Desc.Key.descAt_is
#print axioms VerifiableInference.Desc.Key.planOk_of_planWord
#print axioms VerifiableInference.Desc.Key.planWord_of_planOk
#print axioms VerifiableInference.Desc.Key.laidOfDesc_iff
#print axioms VerifiableInference.Desc.Key.find_no_none
#print axioms VerifiableInference.Desc.Key.laidOfMade_iff
#print axioms VerifiableInference.Desc.Key.laidAt_is
#print axioms VerifiableInference.Desc.Key.laidAt_of
#print axioms VerifiableInference.Desc.Key.fixedDigest_size
#print axioms VerifiableInference.Desc.Key.fixedDigest_ne
#print axioms VerifiableInference.Desc.Key.laidFixed_is
#print axioms VerifiableInference.Desc.Key.laidFixed_of
#print axioms VerifiableInference.Desc.Key.laidOk_iff
#print axioms VerifiableInference.Desc.Key.laidRun_no
#print axioms VerifiableInference.Desc.Key.laidData_empty
#print axioms VerifiableInference.Desc.Key.pulled_is
