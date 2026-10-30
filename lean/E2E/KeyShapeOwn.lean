--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeOwn.lean: THE OWN PROXIMITY TEST, THE KEY FILE's THIRD CHAIN's SUB-PROTOCOL NUMBER 2, ON
THE CHAIN's SHAPE: ONE DIRECTION. Its guards as a function `gOwn` of the shape
(E2E/KeyShapeThird.lean), and (B1) of Johnson/Desc/ProofFile/Honest/Thread/Shape.lean's cut: where
the sub-protocol's decision returns and
`gOwn` returns, `gOwn` returns the shape behind. So (B1) holds AT EVERY NUMBER of the third chain's
flat list, under two conditions on public numbers of the own test's place. Definitions, statements
and proofs. NOTHING IS SHOWN OF ANY PROVER.

The test on the core's shape is Johnson/Desc/K12/Honest/Shape/TestCore.lean's `testCore`, with its
law
`k12_core_sh` (from the test's accept alone). Here it is seated: the sub-protocol makes the test's
own state of the chain's, runs the test, and lays statement, book and count of roots back.

  `own_inv`: the seated test's accept, read back.
  **`gOwn p`**: it asks the mark on the statement and that the codes' message lengths are powers of
    two; then `testCore p` at the own group's and the mask's numbers. The named values stay.
  **`own_carries`**: (B1), at a place whose masks are sent ahead and whose samples have one answer.
    The mark is kept by the library's `k12_tidy`; the codes by its `k12_grows`.
  `Z₃Own`: the third chain's letters with `gOwn` at number 2.
  **`carries_all_own`**: (B1) at every number of `(keyFileDescription X N P).second.blocksInOrder`, under these two
    public conditions on the own test's place.
  `p12At_fields`, **`own_place_in_scope`**: under `KeySourced` (E2E/KeyPublic.lean) and
    `VerifierAndGoals.InScope Z` the place meets the two conditions: by the library's `later_of_full` and two
      evaluations in the kernel.
  **`carries_all_in_scope`**: so there (B1) holds at every number with no further premise.
  `ZW`, **`yes_four`**: at the full size's written values and the library's written place of the own
    test, the run on shapes over ALL FOUR sub-protocols returns, from E2E/KeyShapeChain.lean's
    written shape: by the kernel. `no_second_test`: a negative test: asked again at the shape
    behind, the own test's guards reject.

Limits.
- THE FIRST SHAPE OF THE EVALUATION IS A SYNTHETIC STATE's, not a run's.
- (B2) IS NOT HERE: `testCore` asks fewer guards than the test does: that `gOwn` returns says
  nothing on whether the test accepts. The test's named tests on values stay a letter.
- Out of scope the two conditions on the place are premises on public numbers.


-/
import E2E.KeyShapeChain
import Johnson.Desc.K12.Honest.Shape.TestCore
import Johnson.Desc.K12.Law.GrowsTest
import Johnson.Desc.K12.Coin.TidyThrough

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes
open OnBytes.Params (LinShape)
open ProofFile.Honest (Shape Carries CarriesR)
open ProofFile.Honest.Sh (testCore k12_core_sh)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)

/-- The seated test's accept, read back. -/
theorem own_inv (p : P12) (s s' : S₃) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.onOwn (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide s rs
      gs = .ok s') :
    ∃ tE : T12, (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide
        { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing
          mask := s.loc.mask } rs gs = .ok tE ∧
      s' = { s with st := tE.st, book := tE.book, roots := tE.roots } := by
  have h' : ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide
      { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing
        mask := s.loc.mask } rs gs).bind (VerifiableInference.Desc.K12.Seat.leaveOwn s) =
      .ok s' := h
  cases hk : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide
      { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing
        mask := s.loc.mask } rs gs with
  | error e =>
    rw [hk] at h'
    cases h'
  | ok tE =>
    rw [hk] at h'
    exact ⟨tE, rfl, (Except.ok.inj h').symm⟩

/-- **The own proximity test on the shape.** -/
def gOwn (p : P12) (a : Sh₃) : Except String Sh₃ :=
  if a.2.tidy && a.1.st.codes.lengthsOk then
    match testCore p a.1 a.2.own a.2.mask with
    | some c => .ok (c, a.2)
    | none => .error "the own proximity test: a guard on the core's shape"
  else .error "the mark on the statement, or the codes' message lengths"

/-- **(B1).** -/
theorem own_carries (S : LinShape) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    CarriesR (sh₃ S)
      (fun s => (VerifiableInference.Desc.K12.Seat.onOwn
        (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide s rs gs) (gOwn p) := by
  intro s s' t hf hg
  obtain ⟨tE, hk, rfl⟩ := own_inv p s s' rs gs hf
  have c := k12_core_sh p he ha _ tE rs gs hk
  unfold gOwn at hg
  split at hg
  · rename_i hm
    rw [Bool.and_eq_true] at hm
    have hT : stTidyB s.st = true := hm.1
    have hl : s.st.codes.lengthsOk = true := hm.2
    have c' : testCore p (sh₃ S s).1 (sh₃ S s).2.own (sh₃ S s).2.mask =
        some (coreSh ⟨tE.st, tE.book, tE.roots⟩) := c
    rw [c'] at hg
    obtain rfl := Except.ok.inj hg
    have hTE : stTidyB tE.st = true :=
      tidy_mark (VerifiableInference.Desc.K12.Coin.k12_tidy p _ tE rs gs hk hl (tidy_of hT))
    have hc : tE.st.codes = s.st.codes := (H2K.Out.k12_grows p _ tE rs gs hk).1
    show (coreSh ⟨tE.st, tE.book, tE.roots⟩, locSh S s.st s.loc) =
      (coreSh ⟨tE.st, tE.book, tE.roots⟩, locSh S tE.st s.loc)
    unfold locSh
    rw [hT, hTE, hc]
  · cases hg

section At
variable (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces)
  (vOwn : S₃ → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) (ft : Nat)

/-- The third chain's letters, with the own test's guards at number 2. -/
abbrev Z₃Own : Shape S₃ := Z₃At X P (gOwn (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W)) vOwn

/-- **(B1) at every number of the third chain's flat list.** -/
theorem carries_all_own (he : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W).early = true)
    (ha : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W).answers = 1) (j : Nat) :
    Carries (keyFileDescription X N P).second.blocksInOrder ft (Z₃Own X P vOwn) j :=
  carries_all X N P _ vOwn ft (fun rs gs => own_carries _ _ he ha rs gs) j

end At

/-! ## The two conditions, in scope -/

/-- A place at which the test's sub-protocol passes its own test on public values (`planOk`) has the
answers' number and the flag "masks are sent ahead" that it was made of. -/
theorem p12At_fields {Cl : Type} (place : VerifiableInference.Desc.Place) (x : H2U.PlaceNums)
    (hp : (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt place x) : Block T12 Cl).planOk = true) :
    (H2U.proximityTestParametersAt place x).answers = x.answers ∧ (H2U.proximityTestParametersAt place x).early = x.early := by
  unfold H2U.proximityTestParametersAt at hp ⊢
  split
  · rename_i hc
    rw [if_pos hc] at hp
    exact absurd hp (by simp [proximityTestKind, H2U.noP12])
  · rename_i hc
    rw [if_neg hc] at hp
    split
    · exact ⟨rfl, rfl⟩
    · rename_i ho
      rw [ho] at hp
      exact absurd hp (by simp [proximityTestKind, H2U.noP12])

/-- **In scope the own test's place meets the two conditions.** -/
theorem own_place_in_scope {Z : VerifierAndGoals.PublicFiles} {X : VerifiableInference.Desc.Key.Source}
    {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces} (hs : KeySourced Z X N P)
    (scope : VerifierAndGoals.InScope Z = true) :
    (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W).early = true ∧
      (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W).answers = 1 := by
  obtain ⟨X₀, m, h0, hm, hX, -, hP⟩ := hs.source
  have hR := Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0
  have hk := Johnson.RunOne.Law.KeyInScope.key_in_scope scope hR hm
  have hset : m.p.chains.made.sized.set = H2K.Member.setAt :=
    (Johnson.RunOne.Law.K12Facts15.set_in_scope scope hR hm).trans (by decide +kernel)
  obtain ⟨-, -, -, -, -, e6, e7⟩ := (H2K.Sizes.later_of_full hk hset hP).2.1
  obtain ⟨a, b⟩ := p12At_fields (Cl := Unit) ⟨3, none, 2, .K12⟩ P.W
    (H2K.JointK.keyPlan_W X N P hs.named.plan)
  exact ⟨b.trans (e7.trans (by decide +kernel)), a.trans (e6.trans (by decide +kernel))⟩

/-- **(B1) at every number of the third chain's flat list, in scope.** -/
theorem carries_all_in_scope {Z : VerifierAndGoals.PublicFiles} {X : VerifiableInference.Desc.Key.Source}
    {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces} (hs : KeySourced Z X N P)
    (scope : VerifierAndGoals.InScope Z = true)
    (vOwn : S₃ → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) (ft j : Nat) :
    Carries (keyFileDescription X N P).second.blocksInOrder ft (Z₃Own X P vOwn) j :=
  carries_all_own X N P vOwn ft (own_place_in_scope hs scope).1 (own_place_in_scope hs scope).2 j

/-! ## An evaluation over all four -/

/-- The letters at the written values, with the own test's guards at the library's written place. -/
def ZW : Shape S₃ :=
  Z₃ SF (H2K.Member.dsOf H2K.Member.piKWFull) (gOwn H2K.Member.piKWFull) fun _ _ _ => true

set_option maxRecDepth 100000 in
/-- **The shape's own run over all four sub-protocols returns**, from the written shape of
E2E/KeyShapeChain.lean: by the kernel. -/
theorem yes_four : ZW.yes aF 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **A negative test**: asked again at the shape behind it, the third sub-protocol's guards reject.
-/
theorem no_second_test :
    (match ZW.run 3 aF with
      | .ok t => (ZW.g 2 t).toOption.isNone
      | .error _ => false) = true := by decide +kernel

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.own_inv
#print axioms AtPublicFiles.AtFiles.own_carries
#print axioms AtPublicFiles.AtFiles.carries_all_own
#print axioms AtPublicFiles.AtFiles.p12At_fields
#print axioms AtPublicFiles.AtFiles.own_place_in_scope
#print axioms AtPublicFiles.AtFiles.carries_all_in_scope
#print axioms AtPublicFiles.AtFiles.yes_four
#print axioms AtPublicFiles.AtFiles.no_second_test
