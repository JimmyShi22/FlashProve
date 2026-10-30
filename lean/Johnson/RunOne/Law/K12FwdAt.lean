-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12FwdAt.lean: ROWS 2.9 · 2.10 · 3.2 OF THE KEY FILE's TABLES: THE PROMISE's HALVES (Johnson/RunOne/Law/K12Fwd29 | K12Fwd210 | K12Fwd32.lean) AT THE KEY FILE's OWN PLACES, WITH THE PUBLIC PREMISES ON THE PLACES' PARAMETERS PAID OFF THE DESCRIPTION's OWN TEST ON THE FILE. Statements with proofs; each proof is a reading of named clauses, or a call.
OBJECT. (descriptionFromSource X N P).fileOk's clauses "k12.U" | "k12.O" | "k12.own" (what the ranges' test's seat asks on the plan, asked at the three later places) · "stages.U" | "stages.O" | "stages.own" · the shape clauses' last ("the shape off which the declared rounds and the tenants are made is that shape"). USER. Whoever fills the fields r2_9 · r2_10 · r3_2 of The21.
LETTERS. The tables' own. WHAT FALLS against the three files: early · answers = 1 · hst (each place's number of stages is the shape's) · hlen. WHAT STAYS: hf : (descriptionFromSource X N P).fileOk = true · hft at 2.9 | 2.10, now on the place's numbers themselves (P.U.nums.firstTree = 0 | nO.nums.firstTree = 0: the maker's literal; no test asks it) · ha1: one answer to a sample (samples_in_scope, Johnson/RunOne/KeySamples.lean, has it in scope) · B.SmOnly · hcoll · hb · at 3.2: the codes' lengths at the state's codes.
  p12At_nums: where the parameters at a place say "early" they bear the place's numbers. shape_is · asks_U | asks_O | asks_W · stages_U | stages_O | stages_W: the clauses.
  fwd_29_at · fwd_210_at · fwd_32_at.
Limits. The clauses are taken by their places in the lists: loud if the file's test gains a clause. A block that says no to all meets every statement. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Fwd29
import Johnson.RunOne.Law.K12Fwd210
import Johnson.RunOne.Law.K12Fwd32
import Johnson.RunOne.Law.K12Join15

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12FwdAt
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open H2K.JointK (Blk' Gs)
open Johnson.RunOne.KeyRows23
open Johnson.RunOne.Law.RngAsked (asksPlan_ok)
open Johnson.RunOne.Law.K12Join15 (lengths_of_fileOk)

/-- Where the parameters at a place say "early" they bear the place's numbers. -/
theorem p12At_nums (place : Place) (x : H2U.PlaceNums) (h : (H2U.proximityTestParametersAt place x).early = true) : (H2U.proximityTestParametersAt place x).nums = x.nums := by
  unfold H2U.proximityTestParametersAt at h ⊢
  by_cases c : (place.chain != x.chain) = true
  · rw [if_pos c] at h
    cases h
  · rw [if_neg c] at h ⊢
    cases e : H2U.testOracles5 x.nums x.firstGroup with
    | none =>
      rw [e] at h
      cases h
    | some os => rfl

variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)

/-- The shape of the tables is the shared chain's. -/
theorem shape_is (h : (descriptionFromSource X N P).fileOk = true) : shapeAt X = X.Y.k.shared.lin := by
  obtain ⟨r₁, r₂, r₃, ha⟩ := fileOk_all X N P h
  have h11 := List.all_eq_true.1 ha _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr
    (List.mem_of_getElem? (l := shapeClauses X.Y.k (shapeAt X)) (i := 11) rfl)))))))
  exact of_decide_eq_true h11

theorem asks_U (h : (descriptionFromSource X N P).fileOk = true) : asksOnPlan (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) = true := by
  obtain ⟨r₁, r₂, r₃, ha⟩ := fileOk_all X N P h
  exact List.all_eq_true.1 ha (_, asksOnPlan (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U)) (List.mem_append.2 (Or.inr (List.mem_of_getElem? (i := 9) rfl)))

theorem asks_W (h : (descriptionFromSource X N P).fileOk = true) : asksOnPlan (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) = true := by
  obtain ⟨r₁, r₂, r₃, ha⟩ := fileOk_all X N P h
  exact List.all_eq_true.1 ha (_, asksOnPlan (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W)) (List.mem_append.2 (Or.inr (List.mem_of_getElem? (i := 11) rfl)))

theorem asks_O (h : (descriptionFromSource X N P).fileOk = true) (nO : H2U.PlaceNums) (hO : P.O = some nO) : asksOnPlan (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) = true := by
  obtain ⟨r₁, r₂, r₃, ha⟩ := fileOk_all X N P h
  have k := List.all_eq_true.1 ha _ (List.mem_append.2 (Or.inr (List.mem_of_getElem? (i := 10) rfl)))
  dsimp only at k
  rw [hO] at k
  exact k

theorem len_of_sized {codes : Codes} {st : List IoppStage} {x : H2U.PlaceNums} (h : stagesAsSized codes st x = true) : x.nums.stages.length = st.length := by
  unfold stagesAsSized at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

theorem stages_U (h : (descriptionFromSource X N P).fileOk = true) : P.U.nums.stages.length = (shapeAt X).testU.length := by
  obtain ⟨r₁, r₂, r₃, ha⟩ := fileOk_all X N P h
  rw [shape_is X N P h]
  exact len_of_sized (List.all_eq_true.1 ha ("stages.U", stagesAsSized X.Y.k.shared.codes X.Y.k.shared.lin.testU P.U)
    (List.mem_append.2 (Or.inr (List.mem_of_getElem? (i := 5) rfl))))

theorem stages_W (h : (descriptionFromSource X N P).fileOk = true) : P.W.nums.stages.length = (shapeAt X).testOwn.length := by
  obtain ⟨r₁, r₂, r₃, ha⟩ := fileOk_all X N P h
  rw [shape_is X N P h]
  exact len_of_sized (List.all_eq_true.1 ha ("stages.own", stagesAsSized X.Y.k.shared.codes X.Y.k.shared.lin.testOwn P.W)
    (List.mem_append.2 (Or.inr (List.mem_of_getElem? (i := 7) rfl))))

theorem stages_O (h : (descriptionFromSource X N P).fileOk = true) (nO : H2U.PlaceNums) (hO : P.O = some nO) : nO.nums.stages.length = (shapeAt X).testOmega.length := by
  obtain ⟨r₁, r₂, r₃, ha⟩ := fileOk_all X N P h
  have k := List.all_eq_true.1 ha _ (List.mem_append.2 (Or.inr (List.mem_of_getElem? (i := 6) rfl)))
  dsimp only at k
  rw [hO] at k
  rw [shape_is X N P h]
  exact len_of_sized k

variable {Cells M Smp Rec : Type} (D : WholeD) (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M)
  (enc : (Nat → OnBytes.E) → Nat → OnBytes.E) (rad : Nat) (coll : Strs → Rec → Prop) (off₂ off₃ : Nat → Nat)

/-- **The promise's half of row 2.9, at the key file's own place.** -/
theorem fwd_29_at (hf : (descriptionFromSource X N P).fileOk = true) (hft : P.U.nums.firstTree = 0) (ha1 : (oneAt X).given.plan.samples = 1) (hSm : B.SmOnly)
    (hcoll : ∀ (y y' : Strs) (r : Rec), y'.cell = y.cell → coll y' r → coll y r)
    (b : Block St₂ Key.Claim) (hb : b.decide = (K12.Seat.onGu (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) : Blk')).decide) :
    ∀ a c rs gs, On₂ X N P D B at_ R enc rad coll off₂ 9 a → (held b : Block (P₂ × St₂) Key.Claim).decide a.1 rs gs = .ok c.1 →
      StrsStay (Fk X N P) at_ (open₂ 9) (strsOf (fr₂ D) a.2) (strsOf (fr₂ D) c.2) → On₂ X N P D B at_ R enc rad coll off₂ 10 c := by
  obtain ⟨he, ha, _, _⟩ := asksPlan_ok (asks_U X N P hf)
  have en := p12At_nums _ _ he
  exact K12Fwd29.fwd_29 X N P D B at_ R enc rad coll off₂ _ he ha (by rw [en]; exact stages_U X N P hf) (by rw [en]; exact hft) ha1
    (lengths_of_fileOk X N P hf) hSm hcoll b hb

/-- **The promise's half of row 2.10, at the key file's own place.** -/
theorem fwd_210_at (hf : (descriptionFromSource X N P).fileOk = true) (nO : H2U.PlaceNums) (hO : P.O = some nO) (hft : nO.nums.firstTree = 0)
    (ha1 : (oneAt X).given.plan.samples = 1) (hSm : B.SmOnly) (hcoll : ∀ (y y' : Strs) (r : Rec), y'.cell = y.cell → coll y' r → coll y r)
    (b : Block St₂ Key.Claim) (hb : b.decide = (K12.Seat.onGomega (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) : Blk')).decide) :
    ∀ a c rs gs, On₂ X N P D B at_ R enc rad coll off₂ 10 a → (held b : Block (P₂ × St₂) Key.Claim).decide a.1 rs gs = .ok c.1 →
      StrsStay (Fk X N P) at_ (open₂ 10) (strsOf (fr₂ D) a.2) (strsOf (fr₂ D) c.2) → On₂ X N P D B at_ R enc rad coll off₂ 11 c := by
  obtain ⟨he, ha, _, _⟩ := asksPlan_ok (asks_O X N P hf nO hO)
  have en := p12At_nums _ _ he
  exact K12Fwd210.fwd_210 X N P D B at_ R enc rad coll off₂ _ he ha (by rw [en]; exact stages_O X N P hf nO hO) (by rw [en]; exact hft) ha1
    (lengths_of_fileOk X N P hf) hSm hcoll b hb

/-- **The promise's half of row 3.2, at the key file's own place.** -/
theorem fwd_32_at (hf : (descriptionFromSource X N P).fileOk = true) (ha1 : (oneAt X).given.plan.samples = 1)
    (hcoll : ∀ (y y' : Strs) (r : Rec), y'.cell = y.cell → coll y' r → coll y r)
    (b : Block St₃ Key.Claim) (hb : b.decide = (K12.Seat.onOwn (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) : Blk')).decide) :
    ∀ a c rs gs, On₃ X N P D B at_ R coll off₂ off₃ 2 a → a.1.2.st.codes.lengthsOk = true → (held b : Block (P₃ × St₃) Key.Claim).decide a.1 rs gs = .ok c.1 →
      StrsStay (Fk X N P) at_ (open₃ 2) (strsOf (fr₃ X N P D) a.2) (strsOf (fr₃ X N P D) c.2) → On₃ X N P D B at_ R coll off₂ off₃ 3 c := by
  obtain ⟨he, ha, _, _⟩ := asksPlan_ok (asks_W X N P hf)
  have en := p12At_nums _ _ he
  exact K12Fwd32.fwd_32 X N P D B at_ R coll off₂ off₃ _ he ha (by rw [en]; exact stages_W X N P hf) ha1 hcoll b hb

end Johnson.RunOne.Law.K12FwdAt

#print axioms Johnson.RunOne.Law.K12FwdAt.p12At_nums
#print axioms Johnson.RunOne.Law.K12FwdAt.shape_is
#print axioms Johnson.RunOne.Law.K12FwdAt.asks_O
#print axioms Johnson.RunOne.Law.K12FwdAt.stages_O
#print axioms Johnson.RunOne.Law.K12FwdAt.fwd_29_at
#print axioms Johnson.RunOne.Law.K12FwdAt.fwd_210_at
#print axioms Johnson.RunOne.Law.K12FwdAt.fwd_32_at
