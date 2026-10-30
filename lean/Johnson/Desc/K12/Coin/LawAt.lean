-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/LawAt.lean: the law of the proximity test (the kind K12) in the plain form,
both arms (`k12_lawRecFree`, `k12_lawRecFreeO`, Johnson/Desc/K12/Coin/FreeOff.lean), general in the
place π: every field of `AtPlace` | `AtPlaceOwn` is paid from tests with code on the plan and the
condition `K12Condition`. Definitions, statements and proofs.

What it is not, first. The law's public premises are paid and the law is called at public letters:
whether any statement meets the promise (`PromAt` | `PromOwnAt`) is not shown here. The frame and
the data are made by hand off the plan (Johnson/Desc/K12/Law/DataAt.lean): they are no description's
tiling, and the frame's list of trees need not be the chain's whole list in its order. A law called,
not a law shown to bite: no oracles and transcript with a yes of the piece are exhibited; where the
piece never says yes the law is true for nothing. `small_at` and `bat_small_at` speak of one round's
share of its own verifier messages, bits of work among them: no sum over rounds, no level of
security of the whole.
Main names.
  `cnts π r`: the counts of the place's chain at the Johnson letters and the radii r, as a list of
    numbers; the empty list where there is no chain: then `εAt` is all zeros and the field bears is
    idle; the condition shuts that case (`counts_at`). `εAt num π r`: these counts as the errors of
    the stretch behind "BAT".
  `frAt`, `frN`: the frame: a; the trees of `allAt`; key; the place's firstTree. `baseAt`: the
    number over the file of the first tree that the stretch sends.
  `like_at`, `wants_at`, `bears_at`: the fields like, wants, bears.
  `AtN`, `AtOwnN`: `AtPlace` | `AtPlaceOwn` at the letters. `atPlace_at`, `atPlaceOwn_at`: all
    thirteen fields.
  `PromAt`, `PromOwnAt`: the promise on the statement in front, each under one name, so that a
    clause which the kind's own text comes to pay leaves at one place. `pieceAt`: the piece.
    `LawAt`, `LawOwnAt`: the law's statement at the letters.
  `law_at`, `lawOwn_at`: the law called.
  `small_at`, `bat_small_at`: every count of `εAt`, and "BAT"'s own count, is at most εs | 2⁻¹ ^ k
    of its own round's verifier messages, in the stretch's shape. `CountsAre`, `counts_at`: the
    chain is there and `εAt`'s numbers are its own.
  `Closed π r K ch b₁ b₂ T`: what a caller at a closed place lays: four tests with code and the
    condition at 2⁻¹ ^ 128; `Closed.atPlace`, `.atPlaceOwn`, `.law`, `.lawOwn`, `.small`,
    `.batSmall`, `.counts`.
The premises, all on public data, and where each is spent. The block's test on the plan: early,
answers, planOk, deal, own0 | own1, trees, like, batNone, and that "BAT" draws one element. ownMask:
which arm. `placeOk π ch b₁ b₂ T` with b₁ ≤ t₁ and b₂ ≤ t₂: wants. `K12Condition` at π and r: spend,
codes, that the chain is there (bears), and, in `small_at` alone, the bound εs; its table of codes K
is any table at which `pubOk` says yes, and the law reads nothing else of K or εs. `johOk π r`: the
batching's converse (`PayPub`); it would also give codes. `batPriceOk π r k`: `bat_small_at` alone.
Beside it. `errJ` (Johnson/Desc/K12/Coin/GameJ.lean) has the numbers of `εAt`,
typed apart, with `Err.zero` where there is no chain; `chainFrom_rds`, there, gives outright that
the chain stands over the written rounds, which here comes through `K12Condition.gives`. Where both
lie in one library one of the two should go.
Limits: those of FreeOff.lean and of DataAt.lean. `early_of_planOk` and `answers_of_planOk` want the
block's test on the plan to ask early and answers = 1, as `guardedProximityTestParts` does in this library. No
soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.LawAtO
import Johnson.Desc.K12.Law.DataAt
import Johnson.Desc.K12.Law.BatOneLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pin (NTuple PayRec)
open H2K.Pub (WR sgOf writtenOf chainFrom K12Condition johOk batV0 batPriceOk)
open H2K.Member (rdtOf like_dataOf rdsAt wsAt r0At w0At dBAt dtAt allAt stAt placeOk placeOk_parts
  opensOk_parts wsAt_cons rdsAt_cons data_at len_at depth_at)
open scoped ENNReal

/-! ## The letters -/

/-- The counts of the place's chain at the Johnson letters and the radii r. -/
noncomputable def cnts (π : P12) (r : Fmt.M1.Stage → ℕ) : List ℕ :=
  match π.nums.stages, writtenOf π.nums with
  | a :: rest, some (_ :: l) =>
    ((chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest a l).map
      fun c => errList _ c.errL).getD []
  | _, _ => []

theorem cnts_eq (π : P12) (r : Fmt.M1.Stage → ℕ) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (w0 : WR) (l : List WR) (c : OnBytes.Slice.Chain (sgOf a)) (hs : π.nums.stages = a :: rest)
    (hw : writtenOf π.nums = some (w0 :: l))
    (hc : chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest a l = some c) :
    cnts π r = errList _ c.errL := by
  unfold cnts
  rw [hs, hw]
  show ((chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest a l).map
      fun c => errList _ c.errL).getD [] = _
  rw [hc]
  rfl

noncomputable def εAt (num : Fmt.TreeSource → ℕ) (π : P12) (r : Fmt.M1.Stage → ℕ) :
    Err (uLT (ckP .two) (dtAt num π)) :=
  errOfList (uLT (ckP .two) (dtAt num π)) (cnts π r)

/-- The frame: a (idle: the kind opens no stored table) · the trees in front by source, the test's
own, and more · key · the place's firstTree. -/
def frAt (num : Fmt.TreeSource → ℕ) (π : P12) (T : List (Fmt.TreeSource × ℕ)) (base a : ℕ)
    (more : List LeftT) (key : ℕ → ℕ) : Frame :=
  ⟨a, allAt num π T base more, key, π.nums.firstTree⟩

/-! ## The fields -/

section
variable (π : P12) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
  {T : List (Fmt.TreeSource × ℕ)} (hO : H2K.Member.opensOk π T = true) (num : Fmt.TreeSource → ℕ)
include hp hO

omit hp in
theorem likeT_at : List.Forall₂ Like (dtAt num π) (wsAt π).tail :=
  like_dataOf num (wsAt π).tail (rdsAt π).tail (len_at hO)

theorem like_at : ∃ w0 l, writtenOf π.nums = some (w0 :: l) ∧
    List.Forall₂ Like (dBAt num π :: dtAt num π) (w0 :: l) :=
  ⟨w0At π, (wsAt π).tail, (wsAt_cons π hp).1,
    .cons ⟨rfl, rfl, rfl, rfl, rfl⟩ (likeT_at π hO num)⟩

end

/-- The place's chain at the Johnson letters and the radii r is there, and εAt's numbers are its
own counts. -/
def CountsAre (num : Fmt.TreeSource → ℕ) (π : P12) (r : Fmt.M1.Stage → ℕ) : Prop :=
  ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (c : OnBytes.Slice.Chain (sgOf a)),
    π.nums.stages = a :: rest ∧
    chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest a (wsAt π).tail = some c ∧
    errList _ (εAt num π r) = errList _ c.errL

/-- What K12Condition gives, at the written rounds' own names. -/
theorem chain_at (π : P12) (r : Fmt.M1.Stage → ℕ) (K : Codes) (εs : ℝ≥0∞)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hK : K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) π K εs) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (c : OnBytes.Slice.Chain (sgOf a)),
      π.nums.stages = a :: rest ∧
      chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest a (wsAt π).tail = some c ∧
      c.rds = (wsAt π).tail.map WR.rd ∧ Err.Below c.err εs := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, _, _, _, e8, _⟩ := hK.gives
  obtain ⟨_, rfl⟩ := List.cons.inj (Option.some.inj (e2.symm.trans (wsAt_cons π hp).1))
  exact ⟨a, rest, c, e1, e3, e4, e8⟩

section
variable (π : P12) (r : Fmt.M1.Stage → ℕ) (K : Codes) (εs : ℝ≥0∞)
  (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
  (hK : K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) π K εs)
  {T : List (Fmt.TreeSource × ℕ)} (hO : H2K.Member.opensOk π T = true) (num : Fmt.TreeSource → ℕ)
include hp hK hO

theorem bears_at : ∀ a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), π.nums.stages = a :: rest →
    writtenOf π.nums = some (w0 :: l) →
    chainFrom (.at Sg.lstJ Sg.flC Sg.flZ Sg.flZ fun s => r s.st) rest a l = some c →
    Bears c.errL (εAt num π r) := by
  obtain ⟨a₀, rest₀, c₀, e1, e3, e4, _⟩ := chain_at π r K εs hp hK
  have hε : εAt num π r = errOfList (uLT (ckP .two) (dtAt num π)) (errList _ c₀.errL) := by
    unfold εAt
    rw [cnts_eq π r a₀ rest₀ (w0At π) (wsAt π).tail c₀ e1 (wsAt_cons π hp).1 e3]
  rw [hε]
  refine bears_own π Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) (dtAt num π) a₀ rest₀ (w0At π)
    (wsAt π).tail c₀ e1 (wsAt_cons π hp).1 e3 ?_
  rw [e4]
  exact len_like _ _ (likeT_at π hO num)

/-- **Every count of εAt is at most εs of ITS OWN round's verifier messages, in the stretch's
shape.** -/
theorem small_at : Err.Below (εAt num π r) εs := by
  obtain ⟨a₀, rest₀, c₀, e1, e3, e4, e8⟩ := chain_at π r K εs hp hK
  have hε : εAt num π r = errOfList (uLT (ckP .two) (dtAt num π)) (errList _ c₀.errL) := by
    unfold εAt
    rw [cnts_eq π r a₀ rest₀ (w0At π) (wsAt π).tail c₀ e1 (wsAt_cons π hp).1 e3]
  rw [hε]
  exact below_like (dtAt num π) (wsAt π).tail (likeT_at π hO num) c₀.rds e4 c₀.errL _
    (Chain.errL_below c₀ _ e8)

/-- The chain is there, and εAt's numbers are its own. -/
theorem counts_at : CountsAre num π r := by
  unfold CountsAre
  obtain ⟨a₀, rest₀, c₀, e1, e3, e4, _⟩ := chain_at π r K εs hp hK
  refine ⟨a₀, rest₀, c₀, e1, e3, ?_⟩
  unfold εAt
  rw [cnts_eq π r a₀ rest₀ (w0At π) (wsAt π).tail c₀ e1 (wsAt_cons π hp).1 e3]
  refine errList_errOfList _ _ ((errList_length _ _).trans ?_)
  rw [e4]
  exact len_like _ _ (likeT_at π hO num)

end

/-- **"BAT"'s own count is at most 2⁻¹ ^ k of the verifier messages of the stretch's first
round.** -/
theorem bat_small_at (π : P12) (r : Fmt.M1.Stage → ℕ) (K : Codes) (εs : ℝ≥0∞) (k : ℕ)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hK : K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) π K εs)
    {T : List (Fmt.TreeSource × ℕ)} (hO : H2K.Member.opensOk π T = true) (num : Fmt.TreeSource → ℕ)
    (hb : batPriceOk π r k = true) :
    RoundBelow (batV0 π r) (OnBytes.Flat.toRD (dBAt num π)) ((2 : ℝ≥0∞)⁻¹ ^ k) := by
  obtain ⟨a₀, rest₀, _, e1, _⟩ := chain_at π r K εs hp hK
  exact H2K.Pin.batBelow_like π r k a₀ rest₀ e1 (dBAt num π) (dtAt num π) (like_at π hp hO num) hb

/-! ## At numAt -/

/-- The number over the file of the first tree that the stretch sends. -/
abbrev baseAt (t₁ t₂ ch : ℕ) (π : P12) : ℕ := numAt t₁ t₂ ch (.own π.nums.free)

/-- The frame at numAt. -/
abbrev frN (π : P12) (ch : ℕ) (T : List (Fmt.TreeSource × ℕ)) (t₁ t₂ a : ℕ) (more : List LeftT)
    (key : ℕ → ℕ) : Frame :=
  frAt (numAt t₁ t₂ ch) π T (baseAt t₁ t₂ ch π) a more key

/-- **The promise in front, first arm**: the record's count of roots is the place's «free»; the
trees that the first switch's openings name are those at the book's places D.ts, along no, each sent
in front of the stretch; PayRec. -/
def PromAt (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (base : ℕ)
    (x : T12 × F.E.Str) : Prop :=
  x.1.roots = π.nums.free ∧ (FirstOpens π num no base x.1 ∧ PayRec π x.1)

/-- **The promise in front, second arm.** -/
def PromOwnAt (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (base : ℕ)
    (x : T12 × F.E.Str) : Prop :=
  x.1.roots = π.nums.free ∧ (FirstOpensOwn π num no base x.1 ∧ PayRec π x.1)

/-- The piece: the block at its own record, at the stretch made off the plan; "BAT"'s error is
batV0 π r times the sampler's number; the errors behind it are the chain's own counts. -/
noncomputable def pieceAt (π : P12) (r : Fmt.M1.Stage → ℕ) (ch : ℕ) (T : List (Fmt.TreeSource × ℕ))
    (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) (W : Type) :
    Piece (ckP .two) (frN π ch T t₁ t₂ a more key) T12 Unit W :=
  pieceT (frN π ch T t₁ t₂ a more key) W π (baseAt t₁ t₂ ch π) (dBAt (numAt t₁ t₂ ch) π)
    (dtAt (numAt t₁ t₂ ch) π)
    (batV0 π r * (bsRound .two (dBAt (numAt t₁ t₂ ch) π).entry (dBAt (numAt t₁ t₂ ch) π).kind).w)
    (εAt (numAt t₁ t₂ ch) π r)

/-- **The law's statement, first arm, at the letters.** -/
def LawAt (π : P12) (r : Fmt.M1.Stage → ℕ) (ch : ℕ) (T : List (Fmt.TreeSource × ℕ)) (t₁ t₂ a : ℕ)
    (more : List LeftT) (key : ℕ → ℕ) (W : Type) (no rd : ℕ → ℕ) : Prop :=
  (pieceAt π r ch T t₁ t₂ a more key W).ior.red.Leads
    (PromAt (frN π ch T t₁ t₂ a more key) π (numAt t₁ t₂ ch) no (baseAt t₁ t₂ ch π))
    (fun x _ => QN π (NTuple (frN π ch T t₁ t₂ a more key) π no (fun s => r s.st) rd) x)
    (pieceAt π r ch T t₁ t₂ a more key W).err

/-- **The law's statement, second arm, at the letters.** -/
def LawOwnAt (π : P12) (r : Fmt.M1.Stage → ℕ) (ch : ℕ) (T : List (Fmt.TreeSource × ℕ)) (t₁ t₂ a : ℕ)
    (more : List LeftT) (key : ℕ → ℕ) (W : Type) (no rd : ℕ → ℕ) : Prop :=
  (pieceAt π r ch T t₁ t₂ a more key W).ior.red.Leads
    (PromOwnAt (frN π ch T t₁ t₂ a more key) π (numAt t₁ t₂ ch) no (baseAt t₁ t₂ ch π))
    (fun x _ => QN π (NTuple (frN π ch T t₁ t₂ a more key) π no (fun s => r s.st) rd) x)
    (pieceAt π r ch T t₁ t₂ a more key W).err

/-- AtPlace at the letters. -/
abbrev AtN (π : P12) (r : Fmt.M1.Stage → ℕ) (ch : ℕ) (T : List (Fmt.TreeSource × ℕ)) (t₁ t₂ a : ℕ)
    (more : List LeftT) (key : ℕ → ℕ) : Prop :=
  AtPlace (frN π ch T t₁ t₂ a more key) π (numAt t₁ t₂ ch) Sg.lstJ Sg.flC Sg.flZ Sg.flZ
    (fun s => r s.st) (baseAt t₁ t₂ ch π) (dBAt (numAt t₁ t₂ ch) π) (dtAt (numAt t₁ t₂ ch) π)
    (εAt (numAt t₁ t₂ ch) π r)

/-- AtPlaceOwn at the letters. -/
abbrev AtOwnN (π : P12) (r : Fmt.M1.Stage → ℕ) (ch : ℕ) (T : List (Fmt.TreeSource × ℕ))
    (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) : Prop :=
  AtPlaceOwn (frN π ch T t₁ t₂ a more key) π (numAt t₁ t₂ ch) Sg.lstJ Sg.flC Sg.flZ Sg.flZ
    (fun s => r s.st) (baseAt t₁ t₂ ch π) (dBAt (numAt t₁ t₂ ch) π) (dtAt (numAt t₁ t₂ ch) π)
    (εAt (numAt t₁ t₂ ch) π r)

section
variable (π : P12) (r : Fmt.M1.Stage → ℕ) (K : Codes) (εs : ℝ≥0∞) (ch b₁ b₂ : ℕ)
  (T : List (Fmt.TreeSource × ℕ)) (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ)
  (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
  (hK : K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) π K εs)
  (hT : placeOk π ch b₁ b₂ T = true) (h₁ : b₁ ≤ t₁) (h₂ : b₂ ≤ t₂)


include hp hT h₁ h₂ in
theorem wants_at : ∀ Rs,
    wantsOf a (⟨a, baseAt t₁ t₂ ch π, allAt (numAt t₁ t₂ ch) π T (baseAt t₁ t₂ ch π) more,
        dBAt (numAt t₁ t₂ ch) π :: dtAt (numAt t₁ t₂ ch) π, key,
        allAt (numAt t₁ t₂ ch) π T (baseAt t₁ t₂ ch π) more⟩ : StageD).depth
      (dBAt (numAt t₁ t₂ ch) π :: dtAt (numAt t₁ t₂ ch) π) Rs =
      wantsDecl (numAt t₁ t₂ ch) (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds Rs := by
  intro Rs
  have hO := (placeOk_parts hT).2.1
  have h := wants_dataOf a
    (stAt (numAt t₁ t₂ ch) π a (baseAt t₁ t₂ ch π)
      (allAt (numAt t₁ t₂ ch) π T (baseAt t₁ t₂ ch π) more) key).depth (numAt t₁ t₂ ch) (wsAt π)
    (rdsAt π) Rs (opensOk_parts hO).2.2.1 (depth_at π ch b₁ b₂ T t₁ t₂ a more key hp hT h₁ h₂)
    (opensOk_parts hO).2.1
  rw [← data_at (numAt t₁ t₂ ch) hp hO] at h
  exact h

include hp hK hT h₁ h₂ in
/-- **AtPlace: all thirteen fields.** -/
theorem atPlace_at (ho : π.nums.ownMask = false) : AtN π r ch T t₁ t₂ a more key :=
  atPlace_of_plan _ π (numAt t₁ t₂ ch) Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) _ _ _ _
    (H2K.JointK.early_of_planOk π hp) (H2K.JointK.answers_of_planOk π hp) hp hK.spend hK.codes
    (like_at π hp (placeOk_parts hT).2.1 _) rfl ho
    (wants_at π ch b₁ b₂ T t₁ t₂ a more key hp hT h₁ h₂)
    (numOwn_numAt t₁ t₂ ch π.nums.free _ rfl)
    (bears_at π r K εs hp hK (placeOk_parts hT).2.1 _)

include hp hK hT h₁ h₂ in
/-- **AtPlaceOwn: all thirteen fields.** -/
theorem atPlaceOwn_at (ho : π.nums.ownMask = true) : AtOwnN π r ch T t₁ t₂ a more key :=
  atPlaceOwn_of_plan _ π (numAt t₁ t₂ ch) Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) _ _ _ _
    (H2K.JointK.early_of_planOk π hp) (H2K.JointK.answers_of_planOk π hp) hp hK.spend hK.codes
    (like_at π hp (placeOk_parts hT).2.1 _) rfl ho
    (wants_at π ch b₁ b₂ T t₁ t₂ a more key hp hT h₁ h₂)
    (numOwn_numAt t₁ t₂ ch π.nums.free _ rfl)
    (bears_at π r K εs hp hK (placeOk_parts hT).2.1 _)

include hp hK hT h₁ h₂ in
/-- **The first arm called.** -/
theorem law_at (ho : π.nums.ownMask = false) (hj : johOk π r = true) (W : Type) (no rd : ℕ → ℕ) :
    LawAt π r ch T t₁ t₂ a more key W no rd := by
  unfold LawAt pieceAt
  exact k12_lawRecFree _ W π (numAt t₁ t₂ ch) no Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) rd
    _ _ _ _ π.nums.free (H2K.JointK.early_of_planOk π hp) hp
    (fun _ => atPlace_at π r K εs ch b₁ b₂ T t₁ t₂ a more key hp hK hT h₁ h₂ ho) r (fun _ => rfl) hj
    (H2K.Made.batOneOk_of_planOk guardedProximityTestParts π hp)

include hp hK hT h₁ h₂ in
/-- **The second arm called.** -/
theorem lawOwn_at (ho : π.nums.ownMask = true) (hj : johOk π r = true) (W : Type)
    (no rd : ℕ → ℕ) : LawOwnAt π r ch T t₁ t₂ a more key W no rd := by
  have hb := H2K.First.batOne_of_ok π (w0At π) (wsAt π).tail (wsAt_cons π hp).1
    (H2K.Made.batOneOk_of_planOk guardedProximityTestParts π hp)
  unfold LawOwnAt pieceAt
  exact k12_lawRecFreeO _ W π (numAt t₁ t₂ ch) no Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) rd
    _ _ _ (batV0 π r) _ π.nums.free (H2K.JointK.early_of_planOk π hp) hp
    (fun _ => atPlaceOwn_at π r K εs ch b₁ b₂ T t₁ t₂ a more key hp hK hT h₁ h₂ ho)
    (H2K.Pub.payPub_of_joh π r (fun s => r s.st) (fun _ => rfl) hj (w0At π) (wsAt π).tail
      (wsAt_cons π hp).1) hb.1 hb.2

end

/-! ## What a caller at a closed place lays -/

/-- Four tests with code, and the condition at 2⁻¹ ^ 128. -/
structure Closed (π : P12) (r : Fmt.M1.Stage → ℕ) (K : Codes) (ch b₁ b₂ : ℕ)
    (T : List (Fmt.TreeSource × ℕ)) : Prop where
  plan : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true
  cond : K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) π K ((2 : ℝ≥0∞)⁻¹ ^ 128)
  place : placeOk π ch b₁ b₂ T = true
  joh : johOk π r = true
  bat : batPriceOk π r 128 = true

namespace Closed
variable {π : P12} {r : Fmt.M1.Stage → ℕ} {K : Codes} {ch b₁ b₂ : ℕ}
  {T : List (Fmt.TreeSource × ℕ)} (h : Closed π r K ch b₁ b₂ T)
include h

theorem atPlace (ho : π.nums.ownMask = false) (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ)
    (h₁ : b₁ ≤ t₁) (h₂ : b₂ ≤ t₂) : AtN π r ch T t₁ t₂ a more key :=
  atPlace_at π r K _ ch b₁ b₂ T t₁ t₂ a more key h.plan h.cond h.place h₁ h₂ ho

theorem atPlaceOwn (ho : π.nums.ownMask = true) (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ)
    (h₁ : b₁ ≤ t₁) (h₂ : b₂ ≤ t₂) : AtOwnN π r ch T t₁ t₂ a more key :=
  atPlaceOwn_at π r K _ ch b₁ b₂ T t₁ t₂ a more key h.plan h.cond h.place h₁ h₂ ho

theorem law (ho : π.nums.ownMask = false) (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ)
    (h₁ : b₁ ≤ t₁) (h₂ : b₂ ≤ t₂) (W : Type) (no rd : ℕ → ℕ) :
    LawAt π r ch T t₁ t₂ a more key W no rd :=
  law_at π r K _ ch b₁ b₂ T t₁ t₂ a more key h.plan h.cond h.place h₁ h₂ ho h.joh W no rd

theorem lawOwn (ho : π.nums.ownMask = true) (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ)
    (h₁ : b₁ ≤ t₁) (h₂ : b₂ ≤ t₂) (W : Type) (no rd : ℕ → ℕ) :
    LawOwnAt π r ch T t₁ t₂ a more key W no rd :=
  lawOwn_at π r K _ ch b₁ b₂ T t₁ t₂ a more key h.plan h.cond h.place h₁ h₂ ho h.joh W no rd

/-- A comparison of numbers alone, at radii that `joh` has tested. -/
theorem small (num : Fmt.TreeSource → ℕ) : Err.Below (εAt num π r) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  small_at π r K _ h.plan h.cond (placeOk_parts h.place).2.1 num

/-- A comparison of numbers alone, at radii that `joh` has tested: `batPriceOk` by itself says yes
at silly radii too. -/
theorem batSmall (num : Fmt.TreeSource → ℕ) :
    RoundBelow (batV0 π r) (OnBytes.Flat.toRD (dBAt num π)) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  bat_small_at π r K _ 128 h.plan h.cond (placeOk_parts h.place).2.1 num h.bat

theorem counts (num : Fmt.TreeSource → ℕ) : CountsAre num π r :=
  counts_at π r K _ h.plan h.cond (placeOk_parts h.place).2.1 num

end Closed

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.atPlace_at
#print axioms VerifiableInference.Desc.K12.Coin.atPlaceOwn_at
#print axioms VerifiableInference.Desc.K12.Coin.law_at
#print axioms VerifiableInference.Desc.K12.Coin.lawOwn_at
#print axioms VerifiableInference.Desc.K12.Coin.small_at
#print axioms VerifiableInference.Desc.K12.Coin.counts_at
#print axioms VerifiableInference.Desc.K12.Coin.bat_small_at
