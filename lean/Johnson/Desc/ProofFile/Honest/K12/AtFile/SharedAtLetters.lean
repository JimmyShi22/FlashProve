-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/SharedAtLetters.lean: NOT IN FRONT OF A LAW OVER COINS. The
shared chain's fields of the object at TheLetters' names: the thread at shared, reads, the letter said₂.

  walk_letters         WalkFacts at the thread
  five_front_letters, five_end_letters   the five at members 0 and 11
  five_all_letters     the five at every member, at any Said that gives the field at 10
  owes_letters, yes_letters, next_letters   owes₂, yes₂, next₂ at said₂
  yesJ_letters, carryJ_letters   yes₂ and carry₂ in the third family's form, J₂ saying nothing
  stand_letters        the stand at 12 at said₂

Premises left. hw: the input's key is the committer's. stand_letters: ready's return, the lists.

By what. walk_at_term, five_front, five_at_end, five_letters_eight, five_letters_nine, five_letters_ten,
saidNext_walk, saidWalk_start, walk_of_paid.

Limits. At the base return alone. ready's return is a premise of
stand_letters: it is H2's, and T2's socket takes it. Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.AtTheLetters
import Johnson.Desc.ProofFile.Honest.K12.AtFile.SharedOwes
import Johnson.Desc.ProofFile.Honest.Thread.WalkedTo
import Johnson.Desc.ProofFile.Honest.Thread.DoorWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest.TheLetters
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.FirstThread
open OnBytes (TableKey)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc (K1.qAt)
open Desc.K14 (St blocks)
open ProofFile.Honest.Term (matrixFilling five_front five_at_end keepsEq)
open ProofFile.Honest.K12.AtFile (twelve_members field_of_saidNil runs_of_ready)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)
  (O : OpenShared A) (w : Common FullSizeMatrix IndexCommitterCoins TableKey)

local notation "𝐓" => sharedThread h (reads h) (shared h O) w

/-- **WalkFacts at the thread.** -/
theorem walk_letters (base : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) :
    WalkFacts (𝐓) 12 := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, nO, pO, hb, -, hO⟩ := letters_head h
  show WalkFacts (sharedThread h (reads h) (sharedParts h (later (h := h) O)) w) 12
  rw [later_at_head h hb hO O]
  exact ProofFile.Honest.Term.walk_at_term h base pO hO O.rest keepsOff w

/-- **The five at member 0.** -/
theorem five_front_letters (Said : ℕ → Coins A.B → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
    (fall : ℕ → St → List Fmt.Drawn → Option String) : FiveAtBorder (𝐓) Said fall 0 := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, nO, pO, hb, -, hO⟩ := letters_head h
  show FiveAtBorder (sharedThread h (reads h) (sharedParts h (later (h := h) O)) w) Said fall 0
  rw [later_at_head h hb hO O]
  exact five_front h w pO O.rest hb Said fall

/-- **The five at the chain's end.** -/
theorem five_end_letters (scope : VerifierAndGoals.InScope Z = true)
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (hw : AtFullSide.K14.KeyIsTheCommitters A w)
    (Said : ℕ → Coins A.B → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
    (fall : ℕ → St → List Fmt.Drawn → Option String) : FiveAtBorder (𝐓) Said fall 11 := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, nO, pO, hb, h₁, hO⟩ := letters_head h
  show FiveAtBorder (sharedThread h (reads h) (sharedParts h (later (h := h) O)) w) Said fall 11
  rw [later_at_head h hb hO O]
  exact five_at_end h w pO O.rest h₁ hb
    (ProofFile.Honest.Term.key_fits_term h scope base _ _ w hw)
    (ProofFile.Honest.Term.none_at_end h base hb hO) Said fall

/-- The thread has twelve members. -/
theorem twelve_letters : (𝐓).bs.length = 12 := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, nO, pO, hb, h₁, hO⟩ := letters_head h
  exact twelve_members h.head h₁

/-- **The five at every member.** -/
theorem five_all_letters (scope : VerifierAndGoals.InScope Z = true)
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (hw : AtFullSide.K14.KeyIsTheCommitters A w)
    (Said : ℕ → Coins A.B → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
    (hfield : ∀ k s m E, ThrS (𝐓) Said 10 k s m E → ∀ cols,
      (𝐓).colsTo 10 m E = .ok cols → m.opened = some cols)
    (fall : ℕ → St → List Fmt.Drawn → Option String) (b : ℕ) (hlt : b < (𝐓).bs.length) :
    FiveAtBorder (𝐓) Said fall b := by
  rw [twelve_letters] at hlt
  by_cases h0 : b = 0
  · subst h0
    exact five_front_letters h O w Said fall
  by_cases h8 : b ≤ 8
  · exact five_letters_eight h w base O hw Said fall b (by omega) h8
  by_cases h9 : b = 9
  · subst h9
    exact five_letters_nine h w base O Said fall
  by_cases h10 : b = 10
  · subst h10
    exact five_letters_ten h w base O Said hfield fall
  have e : b = 11 := by omega
  subst e
  exact five_end_letters h O w scope base hw Said fall

section Said
variable (m₀ : Coins A.B → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit)

/-- At the walk's letter the field holds the columns of the fold. -/
theorem field_at_walk (k : Coins A.B) (s : St) (m : Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit) (E : Env)
    (u : ThrS (𝐓) (SaidWalk (𝐓) BaseNil m₀) 10 k s m E) (cols : List VerifiableInference.Desc.OpenedColumn)
    (hc : (𝐓).colsTo 10 m E = .ok cols) : m.opened = some cols :=
  field_of_saidNil _ ⟨u.1, u.2.1⟩ cols hc

/-- **owes₂.** -/
theorem owes_letters (scope : VerifierAndGoals.InScope Z = true)
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (hw : AtFullSide.K14.KeyIsTheCommitters A w) : OwesS (𝐓) (SaidWalk (𝐓) BaseNil m₀) :=
  owesS_of_five (fall := fun _ _ _ => none) (five_all_letters h O w scope base hw _
    (field_at_walk h O w m₀) _)

/-- **yes₂.** -/
theorem yes_letters (scope : VerifierAndGoals.InScope Z = true)
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (hw : AtFullSide.K14.KeyIsTheCommitters A w)
    (fall : ℕ → St → List Fmt.Drawn → Option String) : YesS (𝐓) (SaidWalk (𝐓) BaseNil m₀) fall :=
  yesS_of_five (five_all_letters h O w scope base hw _ (field_at_walk h O w m₀) fall)

/-- **next₂.** -/
theorem next_letters (scope : VerifierAndGoals.InScope Z = true)
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (hw : AtFullSide.K14.KeyIsTheCommitters A w) (b : ℕ) :
    SaidNext (𝐓) (SaidWalk (𝐓) BaseNil m₀) b := by
  intro blk hblk
  have hj := lt_of_member _ hblk
  have e12 := twelve_letters h O w
  have F := walk_letters h O w base
  have hf := five_all_letters h O w scope base hw _ (field_at_walk h O w m₀)
    (fun _ _ _ => none) b hj
  exact saidNext_walk _ (n := 12) F.fits (by omega)
    (treesNext_of_playsS _ hf.plays fun blk _ m ds => AtPublicFiles.Stops.chainStopAt_none _ F.stops [blk] _ _)
    (baseNil_kept _ b) (F.opens _ (by omega)) (fun k m _ => F.depths _ (by omega) k m) blk hblk

/-- **yes₂ in the third family's form, at any J.** -/
theorem yesJ_letters (scope : VerifierAndGoals.InScope Z = true)
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (hw : AtFullSide.K14.KeyIsTheCommitters A w) (J : ℕ → St → Prop)
    (fall : ℕ → St → List Fmt.Drawn → Option String) (b : ℕ) (hb : b < (𝐓).bs.length) :
    AcceptedJ (𝐓) (SaidWalk (𝐓) BaseNil m₀) J fall b :=
  acceptedJ_of _ _ _ (yes_letters h O w m₀ scope base hw fall b hb)

/-- **carry₂ where the third family says nothing.** -/
theorem carryJ_letters (fall : ℕ → St → List Fmt.Drawn → Option String) (b : ℕ) :
    NextJ (𝐓) (SaidWalk (𝐓) BaseNil m₀) (fun _ _ => True) fall b := by
  unfold NextJ
  intros
  trivial

end Said

/-- **The stand at 12 at the letter said₂.** -/
theorem stand_letters (scope : VerifierAndGoals.InScope Z = true)
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (hw : AtFullSide.K14.KeyIsTheCommitters A w) {k : Coins A.B}
    {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit} {x : ProofFile.Inst}
    (hR : ready h.description A.B A.H w.w₀ w.rc x k = .ok R) (hc : R.common = w)
    (ds : ℕ → List Fmt.Drawn)
    (hds : ∀ j, j < 12 → ∃ blk, (𝐓).bs[j]? = some blk ∧ drawsFit blk.rounds (ds j) = true) :
    ∃ (s : St) (m : Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit) (E : Env),
      ThrS (𝐓) (SaidWalk (𝐓) BaseNil (sharedStand A.H R)) 12 k s m E := by
  have E₂ := enters_sharedParts (reads := reads h) (L := later (h := h) O) hR
    (fun _ hc => absurd hc List.not_mem_nil)
  rw [hc] at E₂
  have F := walk_letters h O w base
  have st : ThrS (𝐓) (SaidWalk (𝐓) BaseNil (sharedStand A.H R)) 0 k
      (h.description.start₂ (h.description.pub x)) { R.start₂ A.H with opened := some [] }
      (envOf (A.H.storedWords w.w₀ w.rc) (fun _ _ => none) []) :=
    ⟨E₂, saidWalk_start _ rfl rfl⟩
  have paid : ∀ j, j < 12 → MemberPaid (𝐓) (SaidWalk (𝐓) BaseNil (sharedStand A.H R)) (0 + j) := by
    intro j hj
    rw [Nat.zero_add]
    have hj' : j < (𝐓).bs.length := by rw [twelve_letters]; exact hj
    have hf := five_all_letters h O w scope base hw _ (field_at_walk h O w (sharedStand A.H R))
      (fun _ _ _ => none) j hj'
    exact ⟨next_letters h O w (sharedStand A.H R) scope base hw j, hf.plays, hf.accepted, hf.behind, hf.exchange,
      hf.ridesPast, made_next _ F.fits F.shaped j⟩
  obtain ⟨s, m, E, u, -⟩ := walk_of_paid (𝐓) _ (n := 12) F.fits 0 k ds st 12 (by omega) paid
    fun j hj => by
      obtain ⟨blk, e, hd⟩ := hds (0 + j) (by omega)
      exact runs_of_ready hR _ rfl rfl rfl rfl F.stops e hd
  exact ⟨s, m, E, by simpa using u⟩

end AtFullSide.Honest.TheLetters

#print axioms AtFullSide.Honest.TheLetters.walk_letters
#print axioms AtFullSide.Honest.TheLetters.five_front_letters
#print axioms AtFullSide.Honest.TheLetters.five_end_letters
#print axioms AtFullSide.Honest.TheLetters.five_all_letters
#print axioms AtFullSide.Honest.TheLetters.owes_letters
#print axioms AtFullSide.Honest.TheLetters.yes_letters
#print axioms AtFullSide.Honest.TheLetters.next_letters
#print axioms AtFullSide.Honest.TheLetters.yesJ_letters
#print axioms AtFullSide.Honest.TheLetters.carryJ_letters
#print axioms AtFullSide.Honest.TheLetters.stand_letters
