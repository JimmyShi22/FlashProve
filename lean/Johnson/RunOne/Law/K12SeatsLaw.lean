-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12SeatsLaw.lean: THE LAW OF THE PROXIMITY TEST IN THE PLAIN FORM (Johnson/Desc/K12/Coin/LawY.lean: k12_lawY, k12_lawYO, at the kind's own record) CARRIED TO THE FOUR BLOCKS THAT A KEY FILE's DESCRIPTION SEATS: the ranges' test (chain 1), the folded row's and Omega's (chain 2), the own group's (chain 3). Statements with proofs. NOTHING OF THAT LAW IS PROVED ANEW, AND ALL ITS PREMISES STAY: the place's (AtPlace | AtPlaceOwn) and, in the promise, FirstOpens | FirstOpensOwn and the batching's converse (BatAtY).
OBJECT. The four blocks of the proximity test in a key file's description: `rangesTest (enterRanges one) leaveRanges N` (Johnson/Desc/Key/Chain1.lean: firstChain) and `Seat.onGu`, `Seat.onGomega`, `Seat.onOwn` of `proximityTestKind guardedProximityTestParts π` (Johnson/Desc/Key/Chains23.lean: sharedTests, ownTest), each in whatever dress B' is Seated over it. That they stand in the flat lists: rng_in_flat here; Johnson/RunOne/Sound/KeyMapAtFK.lean: fk_rng_at; Johnson/RunOne/Law/K12SeatsAt.lean.
USER. Johnson/RunOne/Law/K12SeatsHeld.lean calls law_over, law_overO, over_same and the Seated lemmas. Nobody calls law_rng, law_U, law_O, law_own themselves yet.
LETTERS. Free: F, W, num, no, L, mC, mS, mW, rad, rd, base, dB, dt, e₀, εt, Nn. The premise hA (AtPlace, AtPlaceOwn): its five fields on the plan are paid at the ranges' test's seat by Johnson/RunOne/Law/PlanPays.lean (rng_pays); five more by tests with code (Johnson/Desc/K12/Coin/Bools.lean: atPlace_of);
the whole premise at the key file's three later proximity tests, under that file's section premises
(in scope, the planner's and the laws' tests passed, the written key file): place_29, place_210,
place_32 (K12PlaceAtName.lean). In the promise FirstOpens and BatAtY: not paid here (under premises:
firstOpens_of_yes, Johnson/Desc/K12/Coin/FirstBook.lean; batAtY_pay,
Johnson/Desc/K12/Law/BatValsPay.lean).
  step_same, over_same: a seat's sentence (Coin/Over.lean: Over) hangs on the seated block's declared rounds and decision alone: so it goes over to the same block under another name, another test on the plan, another type of claims.
  Seated B B': B' declares B's rounds and decides as B does. seated_bare, seated_recl, seated_ownAt: the three dresses in which a description's flat list holds a block (Chain.blocksInOrder's test "no claims"; Block.retype's other type of claims; Third.ownAt's stamp of the place in the last chain).
  law_over, law_overO: the two arms of the law at whatever block stands over the kind's.
  law_rng, law_U, law_O, law_own: at the four seats, for every block B' that is Seated over the seat's own term.
  rng_in_flat: the ranges' test's term, in Chain.blocksInOrder's dress, IS a block of Key.firstChain's flat list.
Limits. That the three later terms are blocks of the description's flat lists, and at which seats: Johnson/RunOne/Law/K12SeatsAt.lean. Which stretch of rounds, which errors: letters of that law. Nothing on soundness.

-/
import Johnson.RunOne.Law.RngOverCoin
import Johnson.Desc.K12.Coin.LawY

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12SeatsLaw
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (FirstState Claim enterRanges leaveRanges firstChain)

/-! ## 1 The sentence hangs on rounds and decision alone -/

/-- B' declares B's rounds and decides as B does. -/
structure Seated {S A A' : Type} (B : Block S A) (B' : Block S A') : Prop where
  rounds : B'.rounds = B.rounds
  decide : B'.decide = B.decide

theorem Seated.refl {S A : Type} (B : Block S A) : Seated B B := ⟨rfl, rfl⟩

theorem Seated.trans {S A A' A'' : Type} {B : Block S A} {B' : Block S A'} {B'' : Block S A''}
    (h : Seated B B') (k : Seated B' B'') : Seated B B'' := ⟨k.rounds.trans h.rounds, k.decide.trans h.decide⟩

/-- Chain.blocksInOrder's dress. -/
theorem seated_bare {S A : Type} (B : Block S A) : Seated B { B with planOk := B.planOk && B.hasNoClaimsAndNothingAfter } := ⟨rfl, rfl⟩

/-- `Block.retype`'s dress: the same block at another type of claims. -/
theorem seated_recl {S A' : Type} (B : Block S Unit) : Seated B (B.retype : Block S A') := ⟨rfl, rfl⟩

/-- The stamp of the own test's place in the last chain (`Third.ownAt`): the place alone turns. -/
theorem seated_ownAt {A : Type} (B : Block Third.S₃ A) : Seated B (Third.ownAt B) := ⟨rfl, rfl⟩

theorem step_same {S A A' : Type} {B : Block S A} {B' : Block S A'} (h : Seated B B') (ft : ℕ) (s s' : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (k : ℕ) :
    B'.step ft s rs cols = .ok (s', k) ↔ B.step ft s rs cols = .ok (s', k) := by
  obtain ⟨f1, f2, f3⟩ := RngOver.form_over B' B h.rounds ft rs cols
  rw [step_iff, step_iff, f1, f2, f3, h.decide]

variable {S A A' W : Type} {C : PQ.CK} {F : Frame}

theorem over_same {T Cl : Type} (p : Piece C F T Cl W) {B : Block S A} {B' : Block S A'} (h : Seated B B')
    {R : S → T → Prop} {R' : S → T → S → Prop} (hO : Over p B R R') : Over p B' R R' where
  rounds := by rw [h.rounds]; exact hO.rounds
  step := fun s rs cols s' k hs => hO.step s rs cols s' k ((step_same h _ _ _ _ _ _).1 hs)
  one := hO.one

/-! ## 2 The law's two arms at whatever block stands over the kind's -/

section
variable (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
  (base : ℕ) (dB : RDT) (dt : List RDT) (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (Nn : ConclK F)

theorem law_over (B' : Block S A') (R : S → T12 → Prop) (R' : S → T12 → S → Prop)
    (hO : Over (pieceT F W π base dB dt e₀ εt) B' R R')
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt) :
    (Coin.«over» (pieceT F W π base dB dt e₀ εt) B').ior.red.Leads
      (fun a => ∀ t, R a.1 t → FirstOpens π num no base t ∧ BatAtY F W π no rad rd base dB dt e₀ εt Nn (t, a.2))
      (fun a b => ∃ t t', R a.1 t ∧ R' a.1 t' b.1 ∧ QN π Nn (t, a.2))
      (Coin.«over» (pieceT F W π base dB dt e₀ εt) B').err :=
  leads_over _ B' R R' hO _ _ (k12_lawY F W π num no L mC mS mW rad rd base dB dt e₀ εt Nn hA)

theorem law_overO (B' : Block S A') (R : S → T12 → Prop) (R' : S → T12 → S → Prop)
    (hO : Over (pieceT F W π base dB dt e₀ εt) B' R R')
    (hA : AtPlaceOwn F π num L mC mS mW rad base dB dt εt) :
    (Coin.«over» (pieceT F W π base dB dt e₀ εt) B').ior.red.Leads
      (fun a => ∀ t, R a.1 t → FirstOpensOwn π num no base t ∧ BatAtY F W π no rad rd base dB dt e₀ εt Nn (t, a.2))
      (fun a b => ∃ t t', R a.1 t ∧ R' a.1 t' b.1 ∧ QN π Nn (t, a.2))
      (Coin.«over» (pieceT F W π base dB dt e₀ εt) B').err :=
  leads_over _ B' R R' hO _ _ (k12_lawYO F W π num no L mC mS mW rad rd base dB dt e₀ εt Nn hA)

end

/-! ## 3 At the four seats -/

section
variable (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
  (base : ℕ) (dB : RDT) (dt : List RDT) (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (Nn : ConclK F)

/-- **The ranges' test.** -/
theorem law_rng (one : OneTime) (N : H2U.PlaceNums) (B' : Block Key.FirstState A')
    (hB : Seated (rangesTest (Key.enterRanges one) Key.leaveRanges N : Block Key.FirstState Key.Claim) B')
    (hA : AtPlace F (rangesParams N) num L mC mS mW rad base dB dt εt) :
    (Coin.«over» (pieceT F W (rangesParams N) base dB dt e₀ εt) B').ior.red.Leads
      (fun a => ∀ t, enterAndAsk (Key.enterRanges one) (rangesParams N) a.1 = .ok t →
        FirstOpens (rangesParams N) num no base t ∧ BatAtY F W (rangesParams N) no rad rd base dB dt e₀ εt Nn (t, a.2))
      (fun a b => ∃ t t', enterAndAsk (Key.enterRanges one) (rangesParams N) a.1 = .ok t ∧ Key.leaveRanges a.1 t' = .ok b.1 ∧
        QN (rangesParams N) Nn (t, a.2))
      (Coin.«over» (pieceT F W (rangesParams N) base dB dt e₀ εt) B').err :=
  law_over (rangesParams N) num no L mC mS mW rad rd base dB dt e₀ εt Nn B' _ _
    (over_same _ hB (RngOverCoin.over_keyD one N _ rfl)) hA

/-- **The folded row's test.** -/
theorem law_U (π : P12) (B' : Block _root_.Desc.K14.St A') (hB : Seated (Seat.onGu (proximityTestKind guardedProximityTestParts π)) B')
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt) :
    (Coin.«over» (pieceT F W π base dB dt e₀ εt) B').ior.red.Leads
      (fun a => ∀ t, Seat.enter (·.gU) (·.firstMask) a.1 = .ok t →
        FirstOpens π num no base t ∧ BatAtY F W π no rad rd base dB dt e₀ εt Nn (t, a.2))
      (fun a b => ∃ t t', Seat.enter (·.gU) (·.firstMask) a.1 = .ok t ∧ Seat.leave a.1 t' = .ok b.1 ∧
        QN π Nn (t, a.2))
      (Coin.«over» (pieceT F W π base dB dt e₀ εt) B').err :=
  law_over π num no L mC mS mW rad rd base dB dt e₀ εt Nn B' _ _
    (over_same _ hB (over_inside (pieceT F W π base dB dt e₀ εt) _ _)) hA

/-- **Omega's test**: the arm in which the first fold sends its own mask. -/
theorem law_O (π : P12) (B' : Block _root_.Desc.K14.St A') (hB : Seated (Seat.onGomega (proximityTestKind guardedProximityTestParts π)) B')
    (hA : AtPlaceOwn F π num L mC mS mW rad base dB dt εt) :
    (Coin.«over» (pieceT F W π base dB dt e₀ εt) B').ior.red.Leads
      (fun a => ∀ t, Seat.enter (·.gOmega) (fun _ => none) a.1 = .ok t →
        FirstOpensOwn π num no base t ∧ BatAtY F W π no rad rd base dB dt e₀ εt Nn (t, a.2))
      (fun a b => ∃ t t', Seat.enter (·.gOmega) (fun _ => none) a.1 = .ok t ∧ Seat.leave a.1 t' = .ok b.1 ∧
        QN π Nn (t, a.2))
      (Coin.«over» (pieceT F W π base dB dt e₀ εt) B').err :=
  law_overO π num no L mC mS mW rad rd base dB dt e₀ εt Nn B' _ _
    (over_same _ hB (over_inside (pieceT F W π base dB dt e₀ εt) _ _)) hA

/-- **The own group's test.** -/
theorem law_own (π : P12) (B' : Block VerifiableInference.Desc.Third.S₃ A')
    (hB : Seated (Seat.onOwn (proximityTestKind guardedProximityTestParts π : Block T12 Unit)) B')
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt) :
    (Coin.«over» (pieceT F W π base dB dt e₀ εt) B').ior.red.Leads
      (fun a => ∀ t, Seat.enterOwn a.1 = .ok t →
        FirstOpens π num no base t ∧ BatAtY F W π no rad rd base dB dt e₀ εt Nn (t, a.2))
      (fun a b => ∃ t t', Seat.enterOwn a.1 = .ok t ∧ Seat.leaveOwn a.1 t' = .ok b.1 ∧ QN π Nn (t, a.2))
      (Coin.«over» (pieceT F W π base dB dt e₀ εt) B').err :=
  law_over π num no L mC mS mW rad rd base dB dt e₀ εt Nn B' _ _
    (over_same _ hB (over_inside (pieceT F W π base dB dt e₀ εt) _ _)) hA

end

/-! ## 4 The term is the description's -/

/-- The ranges' test's term, in Chain.blocksInOrder's dress, is a block of chain 1's flat list. -/
theorem rng_in_flat (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root) (set : Setting) (N : H2U.PlaceNums) :
    ({ (rangesTest (Key.enterRanges one) Key.leaveRanges N : Block Key.FirstState Key.Claim) with
        planOk := (rangesTest (Key.enterRanges one) Key.leaveRanges N : Block Key.FirstState Key.Claim).planOk && (rangesTest (Key.enterRanges one) Key.leaveRanges N : Block Key.FirstState Key.Claim).hasNoClaimsAndNothingAfter }) ∈
      (Key.firstChain one D told set N).blocksInOrder := by
  unfold Key.firstChain Chain.blocksInOrder
  refine List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.2 ⟨rangesTest (Key.enterRanges one) Key.leaveRanges N, ?_, rfl⟩))
  simp

end Johnson.RunOne.Law.K12SeatsLaw

#print axioms Johnson.RunOne.Law.K12SeatsLaw.over_same
#print axioms Johnson.RunOne.Law.K12SeatsLaw.law_over
#print axioms Johnson.RunOne.Law.K12SeatsLaw.law_overO
#print axioms Johnson.RunOne.Law.K12SeatsLaw.law_rng
#print axioms Johnson.RunOne.Law.K12SeatsLaw.law_U
#print axioms Johnson.RunOne.Law.K12SeatsLaw.law_O
#print axioms Johnson.RunOne.Law.K12SeatsLaw.law_own
#print axioms Johnson.RunOne.Law.K12SeatsLaw.rng_in_flat
