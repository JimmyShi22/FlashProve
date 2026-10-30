-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GameAt.lean: the game of the proximity test (the kind K12) at every seat
(`k12_gameSeat`, `k12_gameSeatO`, Johnson/Desc/K12/Coin/GameSeat.lean), its public premises paid in
general from `Closed` (Johnson/Desc/K12/Coin/LawAt.lean) and closed at the four places of the proof
file of the full-size stored example proof. Definitions, statements and proofs: each proof is one
call.

Whose is what. The game's form, its law and its proof are GameSeat.lean's and the files' beneath it:
they are called here, once an arm. From LawAt.lean come `AtPlace` | `AtPlaceOwn` with the numbers t₁
and t₂ of the earlier chains' trees as letters, and, beside, that the errors are small.
What it is not, first.
  (1) All six points at the head of Johnson/Desc/K12/Coin/LawAtFull.lean stand here too: the frame
    and the data are made by hand off the plan; at W the letters t₁, t₂ are free in a range; at L
    the frame is not the chain's whole list; small is one round's share.
  (2) It stands over the block's parts with the guard on the batched rows: over parts without that
    guard GameSeat.lean does not compile.
  (3) e is free upwards: at an e that reaches the first round's number of verifier messages the law
    is true for nothing. It is meant at e := "BAT"'s count times the sampler's number, where
    `bat_small_‹X›` stands beside.
  (4) Where the door in refuses, the piece refuses and the law is idle.
  (5) In the conclusion the record t behind the door in is pinned; the record t' is only some record
    that the door out takes to the state behind: it is not said to be the block's own return.
    Nothing on the record behind the seat follows.
  (6) "Every seat" is every `Block.inside enter leave`. What stands in a description's flat lists is
    such a block under wrappers: that a description's piece at a place is this term at these letters
    is shown of no seat.
  (7) No member of the promise is shown at U, W, L. At O `firstOpensOwn_OFull`
    (Johnson/Desc/K12/Coin/MemberPromFull.lean) is one at the bare record: `game_OFull_at`; that
    this record is the one which the verifier reaches on the stored file is no theorem.
Main names.
  `SeatGameAt`, `SeatGameOwnAt`: the conclusions of `K12GameSeat` | `K12GameSeatO` at the letters of
    LawAt.lean, under "BAT"'s count times the sampler's number ≤ e.
  `Closed.game`, `Closed.gameOwn`: from `Closed`, which arm, b₁ ≤ t₁ and b₂ ≤ t₂.
  `At.game_UFull`, `At.game_OFull`, `At.game_WFull`, `At.game_LFull`: the callers.
  `At.game_OFull_at`: at the doors that do nothing, at the record `tOFull`, whatever the oracles.
  `ownLabelsFreeB`, `labelsPub_own`: a test on the plan with code (`ownLabelsB` of
    Johnson/Desc/K12/Coin/FirstBook.lean with one clause more: n < free); it
    gives `LabelsPub` (Johnson/Desc/K12/Coin/GameLabels.lean) at `numAt t₁ t₂ ch` and `nlAt`
    (GameLabelsO.lean) with t₁ and t₂ letters.
  `SeatGameVAt`, `Closed.gameV`, `At.gameV_UFull`, `At.gameV_LFull`: the first arm with nothing
    promised of the record (`k12_gameSeatV`, GameLabels.lean): one call. The conclusion has turned
    with the promise: the tuple stands at the oracles that `nuOf` names: the book's places are
    numbered by the labels of the trees that stand there.
  `At.noLabels_WFull`: at W `LabelsPub` cannot be met, whatever nl, where the first chain sends a
    tree: two of the three opened trees bear one label: so that form has no caller at W (there the
    order of the book's places tells the trees apart, not the label).
  `lawAt_iff`, `lawOwnAt_iff`: `LawAt` | `LawOwnAt` of LawAt.lean are the forms `GameAt` | `GameAtO`
    of Johnson/Desc/K12/Coin/Game.lean at the piece `pieceAt` and the place's «free», by definition:
    one form, two names. `At.refuses_OFull_at`: the law at `tOFull` said the other way.
Limits: those of GameSeat.lean, LawAt.lean and LawAtFull.lean. No soundness is claimed. Nothing on
hiding.

-/
import Johnson.Desc.K12.Coin.GameSeat
import Johnson.Desc.K12.Coin.GameLabelsO
import Johnson.Desc.K12.Coin.LawAtFull
import Johnson.Desc.K12.Law.LabelsClash

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pin (NTuple)
open H2K.Pub (batV0)
open H2K.Member (wsAt w0At dBAt dtAt wsAt_cons numAt_own)
open H2K.First (opensOf)

/-- **The game at every seat, first arm, at the letters.** -/
def SeatGameAt (π : P12) (r : Fmt.M1.Stage → ℕ) (ch : ℕ) (T : List (Fmt.TreeSource × ℕ)) (t₁ t₂ a : ℕ)
    (more : List LeftT) (key : ℕ → ℕ) : Prop :=
  ∀ (S : Type) (enter : S → Except String T12) (leave : S → T12 → Except String S) (W : Type)
    (no rd : ℕ → ℕ)
    (ext : S × (frN π ch T t₁ t₂ a more key).E.Str →
      Iop.Tr (uLT (ckP .two) (dBAt (numAt t₁ t₂ ch) π :: dtAt (numAt t₁ t₂ ch) π)) → W → W)
    (e : ℕ),
    batV0 π r *
      (bsRound .two (dBAt (numAt t₁ t₂ ch) π).entry (dBAt (numAt t₁ t₂ ch) π).kind).w ≤ e →
    (pieceOf (C := ckP .two) (F := frN π ch T t₁ t₂ a more key)
        ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) (baseAt t₁ t₂ ch π)
        (dBAt (numAt t₁ t₂ ch) π :: dtAt (numAt t₁ t₂ ch) π) []
        ⟨ext, (e, εAt (numAt t₁ t₂ ch) π r)⟩).ior.red.Leads
      (fun x => ∀ t, enter x.1 = .ok t → FirstOpens π (numAt t₁ t₂ ch) no (baseAt t₁ t₂ ch π) t)
      (fun x y => ∃ t t', enter x.1 = .ok t ∧ leave x.1 t' = .ok y.1 ∧
        QN π (NTuple (frN π ch T t₁ t₂ a more key) π no (fun s => r s.st) rd) (t, x.2))
      (e, εAt (numAt t₁ t₂ ch) π r)

/-- **The second arm.** -/
def SeatGameOwnAt (π : P12) (r : Fmt.M1.Stage → ℕ) (ch : ℕ) (T : List (Fmt.TreeSource × ℕ))
    (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) : Prop :=
  ∀ (S : Type) (enter : S → Except String T12) (leave : S → T12 → Except String S) (W : Type)
    (no rd : ℕ → ℕ)
    (ext : S × (frN π ch T t₁ t₂ a more key).E.Str →
      Iop.Tr (uLT (ckP .two) (dBAt (numAt t₁ t₂ ch) π :: dtAt (numAt t₁ t₂ ch) π)) → W → W)
    (e : ℕ),
    batV0 π r *
      (bsRound .two (dBAt (numAt t₁ t₂ ch) π).entry (dBAt (numAt t₁ t₂ ch) π).kind).w ≤ e →
    (pieceOf (C := ckP .two) (F := frN π ch T t₁ t₂ a more key)
        ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) (baseAt t₁ t₂ ch π)
        (dBAt (numAt t₁ t₂ ch) π :: dtAt (numAt t₁ t₂ ch) π) []
        ⟨ext, (e, εAt (numAt t₁ t₂ ch) π r)⟩).ior.red.Leads
      (fun x => ∀ t, enter x.1 = .ok t →
        FirstOpensOwn π (numAt t₁ t₂ ch) no (baseAt t₁ t₂ ch π) t)
      (fun x y => ∃ t t', enter x.1 = .ok t ∧ leave x.1 t' = .ok y.1 ∧
        QN π (NTuple (frN π ch T t₁ t₂ a more key) π no (fun s => r s.st) rd) (t, x.2))
      (e, εAt (numAt t₁ t₂ ch) π r)

/-! ## Nothing promised of the record: the first arm -/

/-- A test on the plan: every opening of the first switch is the chain's own tree number n, in front
of the test, and bears the label firstTree + n. -/
def ownLabelsFreeB (π : P12) : Bool :=
  match π.nums.stages with
  | a :: _ => (opensOf π a.k).all fun o =>
      match o.2 with
      | .own n => o.1.tree == π.nums.firstTree + n && decide (n < π.nums.free)
      | .taken _ _ => false
  | [] => false

/-- **`LabelsPub` (GameLabels.lean) with the numbers of the earlier chains' trees as letters.** -/
theorem labelsPub_own (π : P12) (ch t₁ t₂ : ℕ) (h : ownLabelsFreeB π = true) :
    LabelsPub π (numAt t₁ t₂ ch) (nlAt π (numAt t₁ t₂ ch (.own 0))) (baseAt t₁ t₂ ch π) := by
  intro a rest hs o ho
  unfold ownLabelsFreeB at h
  rw [hs] at h
  have h1 := List.all_eq_true.1 h o ho
  obtain ⟨sh, src⟩ := o
  cases src with
  | taken c s => simp at h1
  | own n =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    obtain ⟨e1, e2⟩ := h1
    refine ⟨?_, ?_⟩
    · show numAt t₁ t₂ ch (.own n) = nlAt π (numAt t₁ t₂ ch (.own 0)) sh.tree
      unfold nlAt
      rw [e1, numAt_own, numAt_own]
      omega
    · show numAt t₁ t₂ ch (.own n) < numAt t₁ t₂ ch (.own π.nums.free)
      rw [numAt_own, numAt_own]
      omega

/-- **The game at every seat with nothing promised of the record, first arm, at the letters**: the
book's places are numbered by the labels of the trees that stand there (`nuOf`). -/
def SeatGameVAt (π : P12) (r : Fmt.M1.Stage → ℕ) (ch : ℕ) (T : List (Fmt.TreeSource × ℕ))
    (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) : Prop :=
  ∀ (S : Type) (enter : S → Except String T12) (leave : S → T12 → Except String S) (W : Type)
    (rd : ℕ → ℕ)
    (ext : S × (frN π ch T t₁ t₂ a more key).E.Str →
      Iop.Tr (uLT (ckP .two) (dBAt (numAt t₁ t₂ ch) π :: dtAt (numAt t₁ t₂ ch) π)) → W → W)
    (e : ℕ),
    batV0 π r *
      (bsRound .two (dBAt (numAt t₁ t₂ ch) π).entry (dBAt (numAt t₁ t₂ ch) π).kind).w ≤ e →
    (pieceOf (C := ckP .two) (F := frN π ch T t₁ t₂ a more key)
        ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) (baseAt t₁ t₂ ch π)
        (dBAt (numAt t₁ t₂ ch) π :: dtAt (numAt t₁ t₂ ch) π) []
        ⟨ext, (e, εAt (numAt t₁ t₂ ch) π r)⟩).ior.red.Leads (fun _ => True)
      (fun x y => ∃ t t', enter x.1 = .ok t ∧ leave x.1 t' = .ok y.1 ∧
        QN π (NTuple (frN π ch T t₁ t₂ a more key) π
          (nuOf π (nlAt π (numAt t₁ t₂ ch (.own 0))) t) (fun s => r s.st) rd) (t, x.2))
      (e, εAt (numAt t₁ t₂ ch) π r)

/-! ## One form, two names -/

/-- `LawAt` (LawAt.lean) is the form `GameAt` (Game.lean) at the piece `pieceAt` and the place's
«free»: by definition. -/
theorem lawAt_iff (π : P12) (r : Fmt.M1.Stage → ℕ) (ch : ℕ) (T : List (Fmt.TreeSource × ℕ))
    (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) (W : Type) (no rd : ℕ → ℕ) :
    LawAt π r ch T t₁ t₂ a more key W no rd ↔
      GameAt (frN π ch T t₁ t₂ a more key) π (numAt t₁ t₂ ch) no (fun s => r s.st) rd
        (baseAt t₁ t₂ ch π) π.nums.free (pieceAt π r ch T t₁ t₂ a more key W) :=
  Iff.rfl

/-- The second arm alike. -/
theorem lawOwnAt_iff (π : P12) (r : Fmt.M1.Stage → ℕ) (ch : ℕ) (T : List (Fmt.TreeSource × ℕ))
    (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) (W : Type) (no rd : ℕ → ℕ) :
    LawOwnAt π r ch T t₁ t₂ a more key W no rd ↔
      GameAtO (frN π ch T t₁ t₂ a more key) π (numAt t₁ t₂ ch) no (fun s => r s.st) rd
        (baseAt t₁ t₂ ch π) π.nums.free (pieceAt π r ch T t₁ t₂ a more key W) :=
  Iff.rfl

namespace Closed
variable {π : P12} {r : Fmt.M1.Stage → ℕ} {K : Codes} {ch b₁ b₂ : ℕ}
  {T : List (Fmt.TreeSource × ℕ)} (h : Closed π r K ch b₁ b₂ T)
include h

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

end Closed

namespace At
open H2K.Member

theorem game_UFull (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) :
    SeatGameAt piUFull rUFull 1 TUFull t₁ t₂ a more key :=
  closed_UFull.game rfl t₁ t₂ a more key (Nat.zero_le _) (Nat.zero_le _)

theorem game_OFull (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) :
    SeatGameOwnAt piOFull rOFull 1 TOFull t₁ t₂ a more key :=
  closed_OFull.gameOwn rfl t₁ t₂ a more key (Nat.zero_le _) (Nat.zero_le _)

theorem game_WFull (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) (h₁ : 83 ≤ t₁)
    (h₂ : 2 ≤ t₂) : SeatGameAt piWFull rWFull 2 TWFull t₁ t₂ a more key :=
  closed_WFull.game rfl t₁ t₂ a more key h₁ h₂

theorem game_LFull (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) :
    SeatGameAt piLFull rLFull 0 TLFull t₁ t₂ a more key :=
  closed_LFull.game rfl t₁ t₂ a more key (Nat.zero_le _) (Nat.zero_le _)

theorem gameV_UFull (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) :
    SeatGameVAt piUFull rUFull 1 TUFull t₁ t₂ a more key :=
  closed_UFull.gameV rfl (by decide +kernel) t₁ t₂ a more key (Nat.zero_le _) (Nat.zero_le _)

theorem gameV_LFull (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) :
    SeatGameVAt piLFull rLFull 0 TLFull t₁ t₂ a more key :=
  closed_LFull.gameV rfl (by decide +kernel) t₁ t₂ a more key (Nat.zero_le _) (Nat.zero_le _)

/-- The test can fail: at W the openings are taken over from other chains. -/
theorem ownLabels_WFull : ownLabelsFreeB piWFull = false := by decide +kernel

/-- **At W `LabelsPub` cannot be met, whatever nl**: two of the three opened trees bear one label
(`no_label_numAt`, Johnson/Desc/K12/Law/LabelsClash.lean). -/
theorem noLabels_WFull (t₁ t₂ base : ℕ) (nl : ℕ → ℕ) (h : t₁ ≠ 0) :
    ¬ LabelsPub piWFull (numAt t₁ t₂ 2) nl base :=
  fun hL => h (H2K.First.no_label_numAt t₁ t₂ 2 nl fun o ho => (hL _ _ rfl o ho).1)

/-- **At the doors that do nothing, at the record `tOFull`, whatever the oracles.** -/
theorem game_OFull_at (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) (W : Type) (rd : ℕ → ℕ)
    (ext : T12 × (frN piOFull 1 TOFull t₁ t₂ a more key).E.Str →
      Iop.Tr (uLT (ckP .two)
        (dBAt (numAt t₁ t₂ 1) piOFull :: dtAt (numAt t₁ t₂ 1) piOFull)) → W → W)
    (e : ℕ)
    (hle : batV0 piOFull rOFull * (bsRound .two (dBAt (numAt t₁ t₂ 1) piOFull).entry
      (dBAt (numAt t₁ t₂ 1) piOFull).kind).w ≤ e)
    (y : (frN piOFull 1 TOFull t₁ t₂ a more key).E.Str) :
    Doomed (uLT (ckP .two) (dBAt (numAt t₁ t₂ 1) piOFull :: dtAt (numAt t₁ t₂ 1) piOFull))
      (e, εAt (numAt t₁ t₂ 1) piOFull rOFull)
      (fun τ => ∀ b,
        (pieceOf (C := ckP .two) (F := frN piOFull 1 TOFull t₁ t₂ a more key)
          ((proximityTestKind guardedProximityTestParts piOFull : Block T12 Unit).inside (fun t => .ok t) fun _ t' => .ok t')
          (baseAt t₁ t₂ 1 piOFull)
          (dBAt (numAt t₁ t₂ 1) piOFull :: dtAt (numAt t₁ t₂ 1) piOFull) []
          ⟨ext, (e, εAt (numAt t₁ t₂ 1) piOFull rOFull)⟩).ior.red.out (tOFull, y) τ = some b →
        QN piOFull (NTuple (frN piOFull 1 TOFull t₁ t₂ a more key) piOFull (fun z => t₁ + z)
          (fun s => rOFull s.st) rd) (tOFull, y)) := by
  refine Doomed.mono _ _ (fun τ hτ b hb => ?_)
    (game_OFull t₁ t₂ a more key T12 (fun t => .ok t) (fun _ t' => .ok t') W (fun z => t₁ + z) rd
      ext e hle (tOFull, y) fun t ht => ?_)
  · obtain ⟨t, _, ht, _, hq⟩ := hτ b hb
    obtain rfl : tOFull = t := Except.ok.inj ht
    exact hq
  · obtain rfl : tOFull = t := Except.ok.inj ht
    exact firstOpensOwn_OFull t₁ t₂

/-- **The law at the record `tOFull`, said the other way** (`leads_iff_refuses`, Game.lean): where
there is no near tuple at these oracles, the prover has lost towards a refusal. -/
theorem refuses_OFull_at (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) (W : Type) (rd : ℕ → ℕ)
    (y : (frN piOFull 1 TOFull t₁ t₂ a more key).E.Str)
    (hn : ¬ QN piOFull (NTuple (frN piOFull 1 TOFull t₁ t₂ a more key) piOFull (fun z => t₁ + z)
      (fun s => rOFull s.st) rd) (tOFull, y)) :
    Doomed _ (pieceAt piOFull rOFull 1 TOFull t₁ t₂ a more key W).err
      (fun τ =>
        (pieceAt piOFull rOFull 1 TOFull t₁ t₂ a more key W).ior.red.out (tOFull, y) τ = none) :=
  leads_iff_refuses.1 ((lawOwnAt_iff _ _ _ _ _ _ _ _ _ _ _ _).1
    (law_OFull t₁ t₂ a more key W (fun z => t₁ + z) rd)) (tOFull, y) (promise_OFull t₁ t₂) hn

end At

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.lawAt_iff
#print axioms VerifiableInference.Desc.K12.Coin.lawOwnAt_iff
#print axioms VerifiableInference.Desc.K12.Coin.At.refuses_OFull_at
#print axioms VerifiableInference.Desc.K12.Coin.labelsPub_own
#print axioms VerifiableInference.Desc.K12.Coin.Closed.gameV
#print axioms VerifiableInference.Desc.K12.Coin.At.gameV_UFull
#print axioms VerifiableInference.Desc.K12.Coin.At.gameV_LFull
#print axioms VerifiableInference.Desc.K12.Coin.At.noLabels_WFull
#print axioms VerifiableInference.Desc.K12.Coin.Closed.game
#print axioms VerifiableInference.Desc.K12.Coin.Closed.gameOwn
#print axioms VerifiableInference.Desc.K12.Coin.At.game_UFull
#print axioms VerifiableInference.Desc.K12.Coin.At.game_OFull
#print axioms VerifiableInference.Desc.K12.Coin.At.game_WFull
#print axioms VerifiableInference.Desc.K12.Coin.At.game_LFull
#print axioms VerifiableInference.Desc.K12.Coin.At.game_OFull_at
