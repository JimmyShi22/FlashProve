-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/LawAtLight.lean: the public premises of the law and of the game of the
proximity test (the kind K12), general in the place, without the record's codes: in the place of
`K12Condition` stands `ChainAt`, which reads the place's stages and written rounds alone.
Definitions, statements and proofs.

Why. Of the four fields of `K12Condition` (Johnson/Desc/K12/Law/ChainHolds.lean) «pub» alone reads
the table of codes K and the place's idx. Johnson/Desc/K12/Coin/LawAt.lean spends of it, through
`K12Condition.gives`, just this: the place's chain is there, over the written rounds. «spend»
follows from the block's test on the plan (`spendOk_of_planOk`), «codes» from `johOk`
(`codes_of_johOk`). So what is left is one statement on the stages and the written rounds, which two
equations carry from a closed place to any place that has the same (`ChainAt.congr`).
What it is not, first.
  (1) `ClosedL.plan`, the block's own test on the plan, still reads all of the place, idx too: the
    lighter record frees the condition's place, not the plan's.
  (2) `ChainAt` holds of the chain: that it is there, that it stands over the written rounds, and
    the comparison «each count is at most εs of its own round's verifier messages». That the chain
    holds (`Chain.Holds`), its radius and the library's law on it are not in `ChainAt`: the law
    takes what it wants of them through the fields codes, spend and bears of `AtPlace` |
    `AtPlaceOwn`.
  (3) All that stands first at the heads of LawAt.lean and Johnson/Desc/K12/Coin/GameAt.lean stands
    here.
  (4) The conclusions are those files' to the letter: nothing new is concluded. The ten theorems on
    `ClosedL` and those of the same names on `Closed` are one family: `Closed.light` carries the
    heavier record to the lighter.
  (5) Why `ChainAt` says outright that the chain is there: where `chainFrom` gives none, `cnts` is
    empty and `εAt` is all zeros, and a bound on it holds of nothing: `ChainAt` is false there
    (`noChain_nil` at a place without a stage).
Main names.
  `ChainAt π r εs`; `chainAt_of_cond`: the condition gives it; `ChainAt.congr`; `noChain_nil`: it is
    false at a place without a stage.
  `bears_atL`, `small_atL`, `counts_atL`, `bat_small_atL`, `atPlace_atL`, `atPlaceOwn_atL`,
    `law_atL`, `lawOwn_atL`: LawAt.lean's theorems of these names without the L, from the block's
    test on the plan, `ChainAt`, `placeOk`, `johOk`.
  `ClosedL π r ch b₁ b₂ T`: plan, chain, place, joh, bat; `Closed.light`.
  `ClosedL.atPlace`, `.atPlaceOwn`, `.law`, `.lawOwn`, `.small`, `.batSmall`, `.counts`, `.game`,
    `.gameOwn`, `.gameV`.
Limits: those of LawAt.lean and GameAt.lean; the game's files of GameAt.lean lie beneath this file.
No soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.GameAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pin (NTuple PayRec)
open H2K.Pub (WR sgOf writtenOf chainFrom K12Condition johOk batV0 batPriceOk codes_of_johOk)
open H2K.Member (wsAt w0At dBAt dtAt placeOk placeOk_parts wsAt_cons)
open scoped ENNReal

/-! ## The chain is there -/

/-- **The place's chain at the Johnson letters and the radii r is there, stands over the written
rounds, and each of its counts is at most εs of its own round's verifier messages.** It reads the
place's stages and written rounds alone. -/
def ChainAt (π : P12) (r : Fmt.M1.Stage → ℕ) (εs : ℝ≥0∞) : Prop :=
  ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR)
    (c : OnBytes.Slice.Chain (sgOf a)),
    π.nums.stages = a :: rest ∧ writtenOf π.nums = some (w0 :: l) ∧
    chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest a l = some c ∧
    c.rds = l.map WR.rd ∧ Err.Below c.err εs

theorem chainAt_of_cond {π : P12} {r : Fmt.M1.Stage → ℕ} {K : Codes} {εs : ℝ≥0∞}
    (hK : K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) π K εs) : ChainAt π r εs := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, _, _, _, e8, _⟩ := hK.gives
  exact ⟨a, rest, w0, l, c, e1, e2, e3, e4, e8⟩

/-- Two equations carry it from place to place. -/
theorem ChainAt.congr {π q : P12} {r : Fmt.M1.Stage → ℕ} {εs : ℝ≥0∞}
    (hs : π.nums.stages = q.nums.stages) (hw : writtenOf π.nums = writtenOf q.nums)
    (h : ChainAt q r εs) : ChainAt π r εs := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, e8⟩ := h
  exact ⟨a, rest, w0, l, c, hs.trans e1, hw.trans e2, e3, e4, e8⟩

/-- It can fail: at a place without a stage. -/
theorem noChain_nil {π : P12} (r : Fmt.M1.Stage → ℕ) (εs : ℝ≥0∞) (h : π.nums.stages = []) :
    ¬ ChainAt π r εs := by
  rintro ⟨a, rest, _, _, _, e1, _⟩
  rw [h] at e1
  cases e1

/-- At the written rounds' own names. -/
theorem chain_atL (π : P12) (r : Fmt.M1.Stage → ℕ) (εs : ℝ≥0∞)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (hC : ChainAt π r εs) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (c : OnBytes.Slice.Chain (sgOf a)),
      π.nums.stages = a :: rest ∧
      chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest a (wsAt π).tail = some c ∧
      c.rds = (wsAt π).tail.map WR.rd ∧ Err.Below c.err εs := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, e8⟩ := hC
  obtain ⟨_, rfl⟩ := List.cons.inj (Option.some.inj (e2.symm.trans (wsAt_cons π hp).1))
  exact ⟨a, rest, c, e1, e3, e4, e8⟩

/-! ## The fields -/

section
variable (π : P12) (r : Fmt.M1.Stage → ℕ) (εs : ℝ≥0∞)
  (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (hC : ChainAt π r εs)
  {T : List (Fmt.TreeSource × ℕ)} (hO : H2K.Member.opensOk π T = true) (num : Fmt.TreeSource → ℕ)
include hp hC hO

theorem bears_atL : ∀ a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), π.nums.stages = a :: rest →
    writtenOf π.nums = some (w0 :: l) →
    chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest a l = some c →
    Bears c.errL (εAt num π r) := by
  obtain ⟨a₀, rest₀, c₀, e1, e3, e4, _⟩ := chain_atL π r εs hp hC
  have hε : εAt num π r = errOfList (uLT (ckP .two) (dtAt num π)) (errList _ c₀.errL) := by
    unfold εAt
    rw [cnts_eq π r a₀ rest₀ (w0At π) (wsAt π).tail c₀ e1 (wsAt_cons π hp).1 e3]
  rw [hε]
  refine bears_own π Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) (dtAt num π) a₀ rest₀ (w0At π)
    (wsAt π).tail c₀ e1 (wsAt_cons π hp).1 e3 ?_
  rw [e4]
  exact len_like _ _ (likeT_at π hO num)

theorem small_atL : Err.Below (εAt num π r) εs := by
  obtain ⟨a₀, rest₀, c₀, e1, e3, e4, e8⟩ := chain_atL π r εs hp hC
  have hε : εAt num π r = errOfList (uLT (ckP .two) (dtAt num π)) (errList _ c₀.errL) := by
    unfold εAt
    rw [cnts_eq π r a₀ rest₀ (w0At π) (wsAt π).tail c₀ e1 (wsAt_cons π hp).1 e3]
  rw [hε]
  exact below_like (dtAt num π) (wsAt π).tail (likeT_at π hO num) c₀.rds e4 c₀.errL _
    (Chain.errL_below c₀ _ e8)

theorem counts_atL : CountsAre num π r := by
  unfold CountsAre
  obtain ⟨a₀, rest₀, c₀, e1, e3, e4, _⟩ := chain_atL π r εs hp hC
  refine ⟨a₀, rest₀, c₀, e1, e3, ?_⟩
  unfold εAt
  rw [cnts_eq π r a₀ rest₀ (w0At π) (wsAt π).tail c₀ e1 (wsAt_cons π hp).1 e3]
  refine errList_errOfList _ _ ((errList_length _ _).trans ?_)
  rw [e4]
  exact len_like _ _ (likeT_at π hO num)

theorem bat_small_atL (k : ℕ) (hb : batPriceOk π r k = true) :
    RoundBelow (batV0 π r) (OnBytes.Flat.toRD (dBAt num π)) ((2 : ℝ≥0∞)⁻¹ ^ k) := by
  obtain ⟨a₀, rest₀, _, e1, _⟩ := chain_atL π r εs hp hC
  exact H2K.Pin.batBelow_like π r k a₀ rest₀ e1 (dBAt num π) (dtAt num π) (like_at π hp hO num) hb

end

section
variable (π : P12) (r : Fmt.M1.Stage → ℕ) (εs : ℝ≥0∞) (ch b₁ b₂ : ℕ)
  (T : List (Fmt.TreeSource × ℕ)) (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ)
  (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (hC : ChainAt π r εs)
  (hT : placeOk π ch b₁ b₂ T = true) (h₁ : b₁ ≤ t₁) (h₂ : b₂ ≤ t₂) (hj : johOk π r = true)
include hp hC hT h₁ h₂ hj

/-- **AtPlace: all thirteen fields.** -/
theorem atPlace_atL (ho : π.nums.ownMask = false) : AtN π r ch T t₁ t₂ a more key :=
  atPlace_of_plan _ π (numAt t₁ t₂ ch) Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) _ _ _ _
    (H2K.JointK.early_of_planOk π hp) (H2K.JointK.answers_of_planOk π hp) hp
    (H2K.Made.spendOk_of_planOk π hp) (codes_of_johOk r π hj)
    (like_at π hp (placeOk_parts hT).2.1 _) rfl ho
    (wants_at π ch b₁ b₂ T t₁ t₂ a more key hp hT h₁ h₂)
    (numOwn_numAt t₁ t₂ ch π.nums.free _ rfl)
    (bears_atL π r εs hp hC (placeOk_parts hT).2.1 _)

/-- **AtPlaceOwn: all thirteen fields.** -/
theorem atPlaceOwn_atL (ho : π.nums.ownMask = true) : AtOwnN π r ch T t₁ t₂ a more key :=
  atPlaceOwn_of_plan _ π (numAt t₁ t₂ ch) Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) _ _ _ _
    (H2K.JointK.early_of_planOk π hp) (H2K.JointK.answers_of_planOk π hp) hp
    (H2K.Made.spendOk_of_planOk π hp) (codes_of_johOk r π hj)
    (like_at π hp (placeOk_parts hT).2.1 _) rfl ho
    (wants_at π ch b₁ b₂ T t₁ t₂ a more key hp hT h₁ h₂)
    (numOwn_numAt t₁ t₂ ch π.nums.free _ rfl)
    (bears_atL π r εs hp hC (placeOk_parts hT).2.1 _)

/-- **The first arm called.** -/
theorem law_atL (ho : π.nums.ownMask = false) (W : Type) (no rd : ℕ → ℕ) :
    LawAt π r ch T t₁ t₂ a more key W no rd := by
  unfold LawAt pieceAt
  exact k12_lawRecFree _ W π (numAt t₁ t₂ ch) no Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) rd
    _ _ _ _ π.nums.free (H2K.JointK.early_of_planOk π hp) hp
    (fun _ => atPlace_atL π r εs ch b₁ b₂ T t₁ t₂ a more key hp hC hT h₁ h₂ hj ho) r
    (fun _ => rfl) hj (H2K.Made.batOneOk_of_planOk guardedProximityTestParts π hp)

/-- **The second arm called.** -/
theorem lawOwn_atL (ho : π.nums.ownMask = true) (W : Type) (no rd : ℕ → ℕ) :
    LawOwnAt π r ch T t₁ t₂ a more key W no rd := by
  have hb := H2K.First.batOne_of_ok π (w0At π) (wsAt π).tail (wsAt_cons π hp).1
    (H2K.Made.batOneOk_of_planOk guardedProximityTestParts π hp)
  unfold LawOwnAt pieceAt
  exact k12_lawRecFreeO _ W π (numAt t₁ t₂ ch) no Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) rd
    _ _ _ (batV0 π r) _ π.nums.free (H2K.JointK.early_of_planOk π hp) hp
    (fun _ => atPlaceOwn_atL π r εs ch b₁ b₂ T t₁ t₂ a more key hp hC hT h₁ h₂ hj ho)
    (H2K.Pub.payPub_of_joh π r (fun s => r s.st) (fun _ => rfl) hj (w0At π) (wsAt π).tail
      (wsAt_cons π hp).1) hb.1 hb.2

end

/-! ## The lighter record -/

/-- Four tests with code, and the chain at 2⁻¹ ^ 128: no table of codes. -/
structure ClosedL (π : P12) (r : Fmt.M1.Stage → ℕ) (ch b₁ b₂ : ℕ)
    (T : List (Fmt.TreeSource × ℕ)) : Prop where
  plan : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true
  chain : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ 128)
  place : placeOk π ch b₁ b₂ T = true
  joh : johOk π r = true
  bat : batPriceOk π r 128 = true

theorem Closed.light {π : P12} {r : Fmt.M1.Stage → ℕ} {K : Codes} {ch b₁ b₂ : ℕ}
    {T : List (Fmt.TreeSource × ℕ)} (h : Closed π r K ch b₁ b₂ T) : ClosedL π r ch b₁ b₂ T :=
  ⟨h.plan, chainAt_of_cond h.cond, h.place, h.joh, h.bat⟩

namespace ClosedL
variable {π : P12} {r : Fmt.M1.Stage → ℕ} {ch b₁ b₂ : ℕ}
  {T : List (Fmt.TreeSource × ℕ)} (h : ClosedL π r ch b₁ b₂ T)
include h

theorem atPlace (ho : π.nums.ownMask = false) (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ)
    (h₁ : b₁ ≤ t₁) (h₂ : b₂ ≤ t₂) : AtN π r ch T t₁ t₂ a more key :=
  atPlace_atL π r _ ch b₁ b₂ T t₁ t₂ a more key h.plan h.chain h.place h₁ h₂ h.joh ho

theorem atPlaceOwn (ho : π.nums.ownMask = true) (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ)
    (h₁ : b₁ ≤ t₁) (h₂ : b₂ ≤ t₂) : AtOwnN π r ch T t₁ t₂ a more key :=
  atPlaceOwn_atL π r _ ch b₁ b₂ T t₁ t₂ a more key h.plan h.chain h.place h₁ h₂ h.joh ho

theorem law (ho : π.nums.ownMask = false) (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ)
    (h₁ : b₁ ≤ t₁) (h₂ : b₂ ≤ t₂) (W : Type) (no rd : ℕ → ℕ) :
    LawAt π r ch T t₁ t₂ a more key W no rd :=
  law_atL π r _ ch b₁ b₂ T t₁ t₂ a more key h.plan h.chain h.place h₁ h₂ h.joh ho W no rd

theorem lawOwn (ho : π.nums.ownMask = true) (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ)
    (h₁ : b₁ ≤ t₁) (h₂ : b₂ ≤ t₂) (W : Type) (no rd : ℕ → ℕ) :
    LawOwnAt π r ch T t₁ t₂ a more key W no rd :=
  lawOwn_atL π r _ ch b₁ b₂ T t₁ t₂ a more key h.plan h.chain h.place h₁ h₂ h.joh ho W no rd

/-- A comparison of numbers alone, at radii that `joh` has tested. -/
theorem small (num : Fmt.TreeSource → ℕ) : Err.Below (εAt num π r) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  small_atL π r _ h.plan h.chain (placeOk_parts h.place).2.1 num

/-- A comparison of numbers alone, at radii that `joh` has tested. -/
theorem batSmall (num : Fmt.TreeSource → ℕ) :
    RoundBelow (batV0 π r) (OnBytes.Flat.toRD (dBAt num π)) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  bat_small_atL π r _ h.plan h.chain (placeOk_parts h.place).2.1 num 128 h.bat

theorem counts (num : Fmt.TreeSource → ℕ) : CountsAre num π r :=
  counts_atL π r _ h.plan h.chain (placeOk_parts h.place).2.1 num

theorem game (ho : π.nums.ownMask = false) (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ)
    (h₁ : b₁ ≤ t₁) (h₂ : b₂ ≤ t₂) : SeatGameAt π r ch T t₁ t₂ a more key := by
  unfold SeatGameAt
  intro S enter leave W no rd ext e hle
  exact k12_gameSeat S enter leave _ W π (numAt t₁ t₂ ch) no Sg.lstJ Sg.flC Sg.flZ Sg.flZ
    (fun s => r s.st) rd _ _ _ ext e _ r (h.atPlace ho t₁ t₂ a more key h₁ h₂) (fun _ => rfl) h.joh
    (H2K.Made.batOneOk_of_planOk guardedProximityTestParts π h.plan) hle

theorem gameV (ho : π.nums.ownMask = false) (hl : ownLabelsFreeB π = true) (t₁ t₂ a : ℕ)
    (more : List LeftT) (key : ℕ → ℕ) (h₁ : b₁ ≤ t₁) (h₂ : b₂ ≤ t₂) :
    SeatGameVAt π r ch T t₁ t₂ a more key := by
  unfold SeatGameVAt
  intro S enter leave W rd ext e hle
  exact k12_gameSeatV S enter leave _ W π (numAt t₁ t₂ ch) _ Sg.lstJ Sg.flC Sg.flZ Sg.flZ
    (fun s => r s.st) rd _ _ _ ext e _ r (h.atPlace ho t₁ t₂ a more key h₁ h₂) (fun _ => rfl) h.joh
    (H2K.Made.batOneOk_of_planOk guardedProximityTestParts π h.plan) hle (labelsPub_own π ch t₁ t₂ hl)

theorem gameOwn (ho : π.nums.ownMask = true) (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ)
    (h₁ : b₁ ≤ t₁) (h₂ : b₂ ≤ t₂) : SeatGameOwnAt π r ch T t₁ t₂ a more key := by
  have hb := H2K.First.batOne_of_ok π (w0At π) (wsAt π).tail (wsAt_cons π h.plan).1
    (H2K.Made.batOneOk_of_planOk guardedProximityTestParts π h.plan)
  unfold SeatGameOwnAt
  intro S enter leave W no rd ext e hle
  exact k12_gameSeatO S enter leave _ W π (numAt t₁ t₂ ch) no Sg.lstJ Sg.flC Sg.flZ Sg.flZ
    (fun s => r s.st) rd _ _ _ ext e (batV0 π r) _ (h.atPlaceOwn ho t₁ t₂ a more key h₁ h₂)
    (H2K.Pub.payPub_of_joh π r (fun s => r s.st) (fun _ => rfl) h.joh (w0At π) (wsAt π).tail
      (wsAt_cons π h.plan).1) hb.1 hb.2 hle

end ClosedL

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.chainAt_of_cond
#print axioms VerifiableInference.Desc.K12.Coin.ChainAt.congr
#print axioms VerifiableInference.Desc.K12.Coin.noChain_nil
#print axioms VerifiableInference.Desc.K12.Coin.small_atL
#print axioms VerifiableInference.Desc.K12.Coin.counts_atL
#print axioms VerifiableInference.Desc.K12.Coin.bat_small_atL
#print axioms VerifiableInference.Desc.K12.Coin.atPlace_atL
#print axioms VerifiableInference.Desc.K12.Coin.atPlaceOwn_atL
#print axioms VerifiableInference.Desc.K12.Coin.law_atL
#print axioms VerifiableInference.Desc.K12.Coin.lawOwn_atL
#print axioms VerifiableInference.Desc.K12.Coin.Closed.light
#print axioms VerifiableInference.Desc.K12.Coin.ClosedL.atPlace
#print axioms VerifiableInference.Desc.K12.Coin.ClosedL.atPlaceOwn
#print axioms VerifiableInference.Desc.K12.Coin.ClosedL.law
#print axioms VerifiableInference.Desc.K12.Coin.ClosedL.lawOwn
#print axioms VerifiableInference.Desc.K12.Coin.ClosedL.small
#print axioms VerifiableInference.Desc.K12.Coin.ClosedL.batSmall
#print axioms VerifiableInference.Desc.K12.Coin.ClosedL.counts
#print axioms VerifiableInference.Desc.K12.Coin.ClosedL.game
#print axioms VerifiableInference.Desc.K12.Coin.ClosedL.gameOwn
#print axioms VerifiableInference.Desc.K12.Coin.ClosedL.gameV
