-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/LawAtFull.lean: the public premises of the law of the proximity test (the kind
K12) in the plain form, closed at the four places of the proof file of the full-size stored example
proof, and the law called there at public letters. Each caller is a few lines that the kernel
evaluates and one call of Johnson/Desc/K12/Coin/LawAt.lean. Statements and proofs.

What it is not, first.
  (1) Not "the law at these places": `AtPlace` | `AtPlaceOwn` closed, and the law called at public
    letters. Whether any statement meets the promise (the record's count of roots; `FirstOpens`;
    `PayRec`) at U, W and L is shown by nobody: no record lies as a term there. At O the promise has
    a member (`promise_OFull`, Johnson/Desc/K12/Coin/MemberPromFull.lean), and `law_OFull_at` is the
    law at that record; that it is the record which the verifier reaches on the stored file is
    nobody's word.
  (2) A law called, not a law shown to bite: no oracles and transcript with a yes of the piece are
    exhibited.
  (3) The frame and the data are made by hand off the plan: no description's tiling. The frame's
    trees: those in front that some place's plan names, by source; the test's own; then «more», a
    free letter, behind (first match). At L the first chain's other trees stand in no closed plan: T
    holds one tree, and the frame is not the chain's whole list of trees in its order.
  (4) At W the letters t₁ and t₂ are free in a range: 83 ≤ t₁ and 2 ≤ t₂: the chain named sends the
    tree named (the openings are taken 0 1, taken 0 82, taken 1 1). Below the range the field wants
    is false (t₁ = 0: one number, two depths). At a description the two follow from a yes of
    `beforeAt` (`taken_below`, Johnson/Desc/K12/Law/BeforeK12.lean): not
    called here.
  (5) `small_‹X›`, `bat_small_‹X›`: each count is at most 2⁻¹ ^ 128 of its own round's written
    verifier messages, bits of work among them: the rounds "CS" and "BASE" alone bear work, 28 bits
    at U and O, 20 at W and L (`works_‹X›`). One round's
    share: no sum over rounds, no level of security of the whole.
  (6) That the closed places are the places which a description makes of the stored public files is
    a run's word (the head of Johnson/Desc/K12/Law/PlacesFull.lean).
Main names, all in the namespace `VerifiableInference.Desc.K12.Coin.At`; ‹X› is UFull, OFull, WFull,
LFull.
  `T‹X›`: the trees in front of the stretch, by source, with their depths.
  `closed_‹X›`: `Closed` at the place: the test on the plan, the condition, `placeOk`, `johOk`,
    `batPriceOk`.
  `v0_‹X›`, `works_‹X›`, `sent_‹X›`, `base_‹X›`, `all_‹X›`: "BAT"'s count; the written rounds
    that bear bits of work; the depths of the trees that the test
    sends; the base; the frame's trees written out.
  `atPlace_‹X›`: all thirteen fields. `law_‹X›`: the law called. `small_‹X›`, `bat_small_‹X›`,
    `counts_‹X›`.
  `book_OFull`, `law_OFull_at`: O's trees in front are the record's book's; the law at the record.
  `place_…`: six plans of trees at which `placeOk` says no. `front_OFull`: O's trees in front are
    U's and those that U sends.
The letters. Closed: the place; the radii `r‹X›`; the Johnson letters; num := `numAt t₁ t₂ ch` with
ch + 1 the place's chain; the base; the place's «free» as the record's count of roots; "BAT"'s
count; the frame's firstTree; the data; the errors, which are the chain's own counts. Free on
purpose: t₁, t₂ (how many trees the first and the second chain send; idle where the chain does not
read them); a (idle: the kind opens no stored table); key; more; W; rd; no (which place of the book
is which tree is the promise's to say).
Limits: those of LawAt.lean. No soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.LawAt
import Johnson.Desc.K12.Law.CondMembersFull
import Johnson.Desc.K12.Coin.MemberPromFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace VerifiableInference.Desc.K12.Coin.At
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open H2K.Pub
open H2K.Member
open H2K.Pin (NTuple)
open scoped ENNReal

/-! ## UFull -/

/-- The trees in front of the stretch, by source, with their depths. -/
def TUFull : List (Fmt.TreeSource × ℕ) :=
  [(.own 0, 24), (.own 1, 22), (.own 2, 13)]

theorem closed_UFull : Closed piUFull rUFull codesFull 1 0 0 TUFull :=
  ⟨piUFull_planOk, k12Condition_piUFull_r, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

theorem v0_UFull : batV0 piUFull rUFull = 6097 := by decide +kernel

/-- The written rounds that bear bits of work: name and number. -/
theorem works_UFull : ((wsAt piUFull).filter fun w => w.entry.work != 0).map
    (fun w => (w.entry.name, w.entry.work)) =
      [("CS", 28), ("CS", 28), ("CS", 28), ("CS", 28), ("BASE", 28)] := by
  decide +kernel

theorem sent_UFull : ((wsAt piUFull).filterMap (·.tree)).map (·.a) = [21, 17, 13, 14] := by
  decide +kernel

theorem base_UFull (t₁ t₂ : ℕ) : baseAt t₁ t₂ 1 piUFull = t₁ + 3 := rfl

/-- The frame's trees, written out: those in front, the test's own, then more. -/
theorem all_UFull (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) :
    (frN piUFull 1 TUFull t₁ t₂ a more key).all =
      [⟨t₁, 24⟩, ⟨t₁ + 1, 22⟩, ⟨t₁ + 2, 13⟩, ⟨t₁ + 3, 21⟩, ⟨t₁ + 4, 17⟩, ⟨t₁ + 5, 13⟩,
       ⟨t₁ + 6, 14⟩] ++ more := by
  show allAt (numAt t₁ t₂ 1) piUFull TUFull (baseAt t₁ t₂ 1 piUFull) more = _
  unfold allAt H2K.Member.sentAt
  rw [sent_UFull]
  rfl

/-- **All thirteen fields.** -/
theorem atPlace_UFull (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) :
    AtN piUFull rUFull 1 TUFull t₁ t₂ a more key :=
  closed_UFull.atPlace rfl t₁ t₂ a more key (Nat.zero_le _) (Nat.zero_le _)

/-- **The law called.** -/
theorem law_UFull (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) (W : Type)
    (no rd : ℕ → ℕ) : LawAt piUFull rUFull 1 TUFull t₁ t₂ a more key W no rd :=
  closed_UFull.law rfl t₁ t₂ a more key (Nat.zero_le _) (Nat.zero_le _) W no rd

/-- Every count behind "BAT" is at most 2⁻¹ ^ 128 of its own round's verifier messages. -/
theorem small_UFull (num : Fmt.TreeSource → ℕ) :
    Err.Below (εAt num piUFull rUFull) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  closed_UFull.small num

/-- "BAT"'s own count likewise, at the stretch's first round. -/
theorem bat_small_UFull (num : Fmt.TreeSource → ℕ) :
    RoundBelow 6097 (OnBytes.Flat.toRD (dBAt num piUFull)) ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have h := closed_UFull.batSmall num
  rwa [v0_UFull] at h

/-- The chain is there, and the errors' numbers are its own. -/
theorem counts_UFull (num : Fmt.TreeSource → ℕ) : CountsAre num piUFull rUFull :=
  closed_UFull.counts num

/-! ## OFull -/

/-- The trees in front of the stretch, by source, with their depths. -/
def TOFull : List (Fmt.TreeSource × ℕ) :=
  [(.own 0, 24), (.own 1, 22), (.own 2, 13), (.own 3, 21), (.own 4, 17), (.own 5, 13), (.own 6, 14)]

theorem closed_OFull : Closed piOFull rOFull codesFull 1 0 0 TOFull :=
  ⟨piOFull_planOk, k12Condition_piOFull_r, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

theorem v0_OFull : batV0 piOFull rOFull = 474 := by decide +kernel

/-- The written rounds that bear bits of work: name and number. -/
theorem works_OFull : ((wsAt piOFull).filter fun w => w.entry.work != 0).map
    (fun w => (w.entry.name, w.entry.work)) =
      [("CS", 28), ("CS", 28), ("CS", 28), ("BASE", 28)] := by
  decide +kernel

theorem sent_OFull : ((wsAt piOFull).filterMap (·.tree)).map (·.a) = [13, 18, 14, 15] := by
  decide +kernel

theorem base_OFull (t₁ t₂ : ℕ) : baseAt t₁ t₂ 1 piOFull = t₁ + 7 := rfl

/-- The frame's trees, written out: those in front, the test's own, then more. -/
theorem all_OFull (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) :
    (frN piOFull 1 TOFull t₁ t₂ a more key).all =
      [⟨t₁, 24⟩, ⟨t₁ + 1, 22⟩, ⟨t₁ + 2, 13⟩, ⟨t₁ + 3, 21⟩, ⟨t₁ + 4, 17⟩, ⟨t₁ + 5, 13⟩, ⟨t₁ + 6, 14⟩,
       ⟨t₁ + 7, 13⟩, ⟨t₁ + 8, 18⟩, ⟨t₁ + 9, 14⟩, ⟨t₁ + 10, 15⟩] ++ more := by
  show allAt (numAt t₁ t₂ 1) piOFull TOFull (baseAt t₁ t₂ 1 piOFull) more = _
  unfold allAt H2K.Member.sentAt
  rw [sent_OFull]
  rfl

/-- **All thirteen fields.** -/
theorem atPlace_OFull (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) :
    AtOwnN piOFull rOFull 1 TOFull t₁ t₂ a more key :=
  closed_OFull.atPlaceOwn rfl t₁ t₂ a more key (Nat.zero_le _) (Nat.zero_le _)

/-- **The law called.** -/
theorem law_OFull (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) (W : Type)
    (no rd : ℕ → ℕ) : LawOwnAt piOFull rOFull 1 TOFull t₁ t₂ a more key W no rd :=
  closed_OFull.lawOwn rfl t₁ t₂ a more key (Nat.zero_le _) (Nat.zero_le _) W no rd

/-- Every count behind "BAT" is at most 2⁻¹ ^ 128 of its own round's verifier messages. -/
theorem small_OFull (num : Fmt.TreeSource → ℕ) :
    Err.Below (εAt num piOFull rOFull) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  closed_OFull.small num

/-- "BAT"'s own count likewise, at the stretch's first round. -/
theorem bat_small_OFull (num : Fmt.TreeSource → ℕ) :
    RoundBelow 474 (OnBytes.Flat.toRD (dBAt num piOFull)) ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have h := closed_OFull.batSmall num
  rwa [v0_OFull] at h

/-- The chain is there, and the errors' numbers are its own. -/
theorem counts_OFull (num : Fmt.TreeSource → ℕ) : CountsAre num piOFull rOFull :=
  closed_OFull.counts num

/-! ## WFull -/

/-- The trees in front of the stretch, by source, with their depths. -/
def TWFull : List (Fmt.TreeSource × ℕ) :=
  [(.taken 0 1, 13), (.taken 0 82, 22), (.taken 1 1, 22)]

theorem closed_WFull : Closed piWFull rWFull codesFull 2 83 2 TWFull :=
  ⟨piWFull_planOk, k12Condition_piWFull_r, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

theorem v0_WFull : batV0 piWFull rWFull = 948 := by decide +kernel

/-- The written rounds that bear bits of work: name and number. -/
theorem works_WFull : ((wsAt piWFull).filter fun w => w.entry.work != 0).map
    (fun w => (w.entry.name, w.entry.work)) =
      [("CS", 20), ("CS", 20), ("CS", 20), ("CS", 20), ("BASE", 20)] := by
  decide +kernel

theorem sent_WFull : ((wsAt piWFull).filterMap (·.tree)).map (·.a) = [18, 15, 13, 15] := by
  decide +kernel

theorem base_WFull (t₁ t₂ : ℕ) : baseAt t₁ t₂ 2 piWFull = t₁ + t₂ := rfl

/-- The frame's trees, written out: those in front, the test's own, then more. -/
theorem all_WFull (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) :
    (frN piWFull 2 TWFull t₁ t₂ a more key).all =
      [⟨1, 13⟩, ⟨82, 22⟩, ⟨t₁ + 1, 22⟩, ⟨t₁ + t₂, 18⟩, ⟨t₁ + t₂ + 1, 15⟩, ⟨t₁ + t₂ + 2, 13⟩,
       ⟨t₁ + t₂ + 3, 15⟩] ++ more := by
  show allAt (numAt t₁ t₂ 2) piWFull TWFull (baseAt t₁ t₂ 2 piWFull) more = _
  unfold allAt H2K.Member.sentAt
  rw [sent_WFull]
  rfl

/-- **All thirteen fields.** -/
theorem atPlace_WFull (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ)
    (h₁ : 83 ≤ t₁) (h₂ : 2 ≤ t₂) :
    AtN piWFull rWFull 2 TWFull t₁ t₂ a more key :=
  closed_WFull.atPlace rfl t₁ t₂ a more key h₁ h₂

/-- **The law called.** -/
theorem law_WFull (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ)
    (h₁ : 83 ≤ t₁) (h₂ : 2 ≤ t₂) (W : Type)
    (no rd : ℕ → ℕ) : LawAt piWFull rWFull 2 TWFull t₁ t₂ a more key W no rd :=
  closed_WFull.law rfl t₁ t₂ a more key h₁ h₂ W no rd

/-- Every count behind "BAT" is at most 2⁻¹ ^ 128 of its own round's verifier messages. -/
theorem small_WFull (num : Fmt.TreeSource → ℕ) :
    Err.Below (εAt num piWFull rWFull) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  closed_WFull.small num

/-- "BAT"'s own count likewise, at the stretch's first round. -/
theorem bat_small_WFull (num : Fmt.TreeSource → ℕ) :
    RoundBelow 948 (OnBytes.Flat.toRD (dBAt num piWFull)) ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have h := closed_WFull.batSmall num
  rwa [v0_WFull] at h

/-- The chain is there, and the errors' numbers are its own. -/
theorem counts_WFull (num : Fmt.TreeSource → ℕ) : CountsAre num piWFull rWFull :=
  closed_WFull.counts num

/-! ## LFull -/

/-- The trees in front of the stretch, by source, with their depths. -/
def TLFull : List (Fmt.TreeSource × ℕ) :=
  [(.own 76, 23)]

theorem closed_LFull : Closed piLFull rLFull codesFull 0 0 0 TLFull :=
  ⟨piLFull_planOk, k12Condition_piLFull_r, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

theorem v0_LFull : batV0 piLFull rLFull = 35532 := by decide +kernel

/-- The written rounds that bear bits of work: name and number. -/
theorem works_LFull : ((wsAt piLFull).filter fun w => w.entry.work != 0).map
    (fun w => (w.entry.name, w.entry.work)) =
      [("CS", 20), ("CS", 20), ("CS", 20), ("CS", 20), ("CS", 20), ("BASE", 20)] := by
  decide +kernel

theorem sent_LFull : ((wsAt piLFull).filterMap (·.tree)).map (·.a) = [22, 19, 16, 13, 15] := by
  decide +kernel

theorem base_LFull (t₁ t₂ : ℕ) : baseAt t₁ t₂ 0 piLFull = 77 := rfl

/-- The frame's trees, written out: those in front, the test's own, then more. -/
theorem all_LFull (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) :
    (frN piLFull 0 TLFull t₁ t₂ a more key).all =
      [⟨76, 23⟩, ⟨77, 22⟩, ⟨78, 19⟩, ⟨79, 16⟩, ⟨80, 13⟩, ⟨81, 15⟩] ++ more := by
  show allAt (numAt t₁ t₂ 0) piLFull TLFull (baseAt t₁ t₂ 0 piLFull) more = _
  unfold allAt H2K.Member.sentAt
  rw [sent_LFull]
  rfl

/-- **All thirteen fields.** -/
theorem atPlace_LFull (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) :
    AtN piLFull rLFull 0 TLFull t₁ t₂ a more key :=
  closed_LFull.atPlace rfl t₁ t₂ a more key (Nat.zero_le _) (Nat.zero_le _)

/-- **The law called.** -/
theorem law_LFull (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) (W : Type)
    (no rd : ℕ → ℕ) : LawAt piLFull rLFull 0 TLFull t₁ t₂ a more key W no rd :=
  closed_LFull.law rfl t₁ t₂ a more key (Nat.zero_le _) (Nat.zero_le _) W no rd

/-- Every count behind "BAT" is at most 2⁻¹ ^ 128 of its own round's verifier messages. -/
theorem small_LFull (num : Fmt.TreeSource → ℕ) :
    Err.Below (εAt num piLFull rLFull) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  closed_LFull.small num

/-- "BAT"'s own count likewise, at the stretch's first round. -/
theorem bat_small_LFull (num : Fmt.TreeSource → ℕ) :
    RoundBelow 35532 (OnBytes.Flat.toRD (dBAt num piLFull)) ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have h := closed_LFull.batSmall num
  rwa [v0_LFull] at h

/-- The chain is there, and the errors' numbers are its own. -/
theorem counts_LFull (num : Fmt.TreeSource → ℕ) : CountsAre num piLFull rLFull :=
  closed_LFull.counts num

/-! ## Can the test fail? -/

theorem place_WFull_sharp1 : placeOk piWFull 2 82 2 TWFull = false := by decide +kernel
theorem place_WFull_sharp2 : placeOk piWFull 2 83 1 TWFull = false := by decide +kernel
theorem place_UFull_depth :
    placeOk piUFull 1 0 0 [(.own 0, 24), (.own 1, 22), (.own 2, 12)] = false := by decide +kernel
theorem place_UFull_lacks : placeOk piUFull 1 0 0 [(.own 0, 24), (.own 1, 22)] = false := by
  decide +kernel
theorem place_UFull_chain : placeOk piUFull 0 0 0 TUFull = false := by decide +kernel
theorem place_UFull_two : placeOk piUFull 1 0 0 ((.own 2, 14) :: TUFull) = false := by
  decide +kernel
/-- O's trees in front are U's trees in front and the trees that U sends. -/
theorem front_OFull : TOFull.map (·.2) =
    TUFull.map (·.2) ++ ((wsAt piUFull).filterMap (·.tree)).map (·.a) := by
  decide +kernel

/-! ## At O's record -/

/-- O's trees in front, by their depths, are the trees of the record's book. -/
theorem book_OFull : TOFull.map (·.2) = tOFull.book.trees.toList.map (·.shape.logN) := by
  decide +kernel

/-- **The law at the record `tOFull`, whatever the oracles**: by `promise_OFull`
(Johnson/Desc/K12/Coin/MemberPromFull.lean), at no := fun z => t₁ + z. -/
theorem law_OFull_at (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ) (W : Type) (rd : ℕ → ℕ)
    (y : (frN piOFull 1 TOFull t₁ t₂ a more key).E.Str) :
    Doomed _ (pieceAt piOFull rOFull 1 TOFull t₁ t₂ a more key W).err
      (fun τ => ∀ b,
        (pieceAt piOFull rOFull 1 TOFull t₁ t₂ a more key W).ior.red.out (tOFull, y) τ = some b →
        QN piOFull (NTuple (frN piOFull 1 TOFull t₁ t₂ a more key) piOFull (fun z => t₁ + z)
          (fun s => rOFull s.st) rd) (tOFull, y)) :=
  law_OFull t₁ t₂ a more key W (fun z => t₁ + z) rd (tOFull, y) (promise_OFull t₁ t₂)

end VerifiableInference.Desc.K12.Coin.At

#print axioms VerifiableInference.Desc.K12.Coin.At.closed_UFull
#print axioms VerifiableInference.Desc.K12.Coin.At.v0_UFull
#print axioms VerifiableInference.Desc.K12.Coin.At.all_UFull
#print axioms VerifiableInference.Desc.K12.Coin.At.atPlace_UFull
#print axioms VerifiableInference.Desc.K12.Coin.At.law_UFull
#print axioms VerifiableInference.Desc.K12.Coin.At.small_UFull
#print axioms VerifiableInference.Desc.K12.Coin.At.bat_small_UFull
#print axioms VerifiableInference.Desc.K12.Coin.At.counts_UFull
#print axioms VerifiableInference.Desc.K12.Coin.At.closed_OFull
#print axioms VerifiableInference.Desc.K12.Coin.At.v0_OFull
#print axioms VerifiableInference.Desc.K12.Coin.At.all_OFull
#print axioms VerifiableInference.Desc.K12.Coin.At.atPlace_OFull
#print axioms VerifiableInference.Desc.K12.Coin.At.law_OFull
#print axioms VerifiableInference.Desc.K12.Coin.At.small_OFull
#print axioms VerifiableInference.Desc.K12.Coin.At.bat_small_OFull
#print axioms VerifiableInference.Desc.K12.Coin.At.counts_OFull
#print axioms VerifiableInference.Desc.K12.Coin.At.closed_WFull
#print axioms VerifiableInference.Desc.K12.Coin.At.v0_WFull
#print axioms VerifiableInference.Desc.K12.Coin.At.all_WFull
#print axioms VerifiableInference.Desc.K12.Coin.At.atPlace_WFull
#print axioms VerifiableInference.Desc.K12.Coin.At.law_WFull
#print axioms VerifiableInference.Desc.K12.Coin.At.small_WFull
#print axioms VerifiableInference.Desc.K12.Coin.At.bat_small_WFull
#print axioms VerifiableInference.Desc.K12.Coin.At.counts_WFull
#print axioms VerifiableInference.Desc.K12.Coin.At.closed_LFull
#print axioms VerifiableInference.Desc.K12.Coin.At.v0_LFull
#print axioms VerifiableInference.Desc.K12.Coin.At.all_LFull
#print axioms VerifiableInference.Desc.K12.Coin.At.atPlace_LFull
#print axioms VerifiableInference.Desc.K12.Coin.At.law_LFull
#print axioms VerifiableInference.Desc.K12.Coin.At.small_LFull
#print axioms VerifiableInference.Desc.K12.Coin.At.bat_small_LFull
#print axioms VerifiableInference.Desc.K12.Coin.At.counts_LFull
#print axioms VerifiableInference.Desc.K12.Coin.At.book_OFull
#print axioms VerifiableInference.Desc.K12.Coin.At.law_OFull_at
