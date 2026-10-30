-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/MarksHead.lean: the list of the owners' marks at the proof file's
first chain at the full size, as one definition, and the number laid for each mark. The list is the
argument `hm` of `FirstAsks` (Honest/Law/CoverAsks.lean), and the number its argument `qM`. Each
owner of sub-protocols lays its own list in a file of its own and proves its bounds in other files.
This file imports the files that hold the lists' definitions, and none of the owners' bounds. So
each owner's lemma stands here as a hypothesis in that lemma's own form, and what is proved is the
step from the owners' lemmas to the fields `hseat`, `hM` and `hq0` at the whole list.

  1  `marksHead`, `qMHead`   the two definitions
  2  `marksHead_length`   the list's length is the sum of the five lists' lengths
  3  `marksHead_seat`, `marksHead_member`   every mark stands at a mark's seat, and at the place of
     a sub-protocol of the chain, if that holds of each owner's list
  4  `qMHead_k3`, `qMHead_k6`, `qMHead_other`   the number at a place of the kind K3, of the kind
     K6, and at any other place; `part4_kind`: K6's authors' marks stand at a place of the kind K6
  5  `hq0_head`   the field `hq0` at `qMHead`
  6  `marksHead_hM`   the field `hM` at `marksHead` and `qMHead`, from each owner's bounds at its
     own list and number

Limits.
  * All five lists are the owners' own. No argument of `marksHead` is left open.
  * At a place of the kind K3 or K6 the number is the stated share's numerator times a letter
    (`kap₃`, `kap₆`). It is not the share's value, and no share is shown to be held there. The two
    letters are apart, since nothing says that the two owners' factors are one number.
  * No owner's lemma is proved or imported here. The owners' letters say which of their lemmas are
    proved and under which hypotheses. K4's authors have handed theirs in for the wider marks
    (`K4.k4_markWideDebt_table`, Honest/K4/Law/MarkWideDebt.lean, not imported here): at the kit of
    hash blocks, at the share's value, under two hypotheses on the rounds' data. K5's authors have
    handed theirs in, in a file that is not imported here. The lookups' authors' bound
    and K6's authors' bound have hypotheses that are proved at no kit of challenges.
  * K4's marks are its authors' wider ones (`K4.k4MarkWide`), at the places of the narrower ones
    (`K4.k4MarksWide_places`). The two stated shares are one written product, 2 * n * (2 ^ 128 + 1)
    ^ 3 over pGold ^ 3 * (2 ^ 128) ^ 3, at two numbers n of listed rounds: la + 2 * lt at the
    narrower mark (`K4.k4MarkRounds_length`), 13 + muV + 2 * lt and further summands at the wider
    (`K4.k4WideRounds_length`). So the number that `qMHead` lays at these twelve places is another
    than with the narrower marks. No number is evaluated.
  * The list holds the marks that the owners have named. K8's authors say that their bound for
    `k8ShareFall` wants further conditions for which no mark is known.
  * What a mark's silence gives (the field `hPM` and the conditions of the owners' bounds for the
    falls) is not treated here.
  * Most stated shares are written pairs of numbers and no bounds.
  * By K4's authors' word their two files
    (Honest/K4/Law/K4MarksWide.lean, Honest/K4/Law/MarkWide.lean) hold
    lemmas beside the definitions and reach Johnson.Bridge.PlanFiveNat and
    Johnson.Bridge.PlanRulesNat. So this file is a law: no file that defines a part of the
    description may import it.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverMarksJoin
import Johnson.Desc.ProofFile.Honest.Law.CoverSeats
import Johnson.P1K8R.Part1MarksCode
import Johnson.Desc.ProofFile.Honest.K3.Good.MarksList
import Johnson.Desc.ProofFile.Honest.K4.Law.K4MarksWide
import Johnson.Desc.ProofFile.Honest.K5.MarksList
import Johnson.Desc.ProofFile.Honest.K6.K6Marks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT)
open _root_.Run.PQ (CK)

/-- The owners' marks at the proof file's first chain at the full size: the owners' own lists in a
row: K8's and K11's authors' `P1K8.part1Marks` (26 marks under the library's hypothesis), the
lookups' authors' `K3.Good.k3Marks` (100), K4's authors' `K4.k4MarksWide` (12), K5's authors'
`K5.k5Marks` (24) and K6's authors' `K6.part4Marks` (2). Most stated shares are written pairs of
numbers and no bounds: see each list's own file. -/
def marksHead (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) : List Mark :=
  P1K8.part1Marks Zp G₀ ++ K3.Good.k3Marks Zp G₀ ++ K4.k4MarksWide Zp G₀ ++ K5.k5Marks Zp G₀ ++
    K6.part4Marks Zp G₀

/-- The number laid for a mark of `marksHead`. The owners read a mark's stated share in two ways.
The lookups' authors' bound (K3) and K6's authors' bound are the share's numerator times a letter of
the owner's: a bound, at one round, on the share of that round's challenges that show a given
element. The other owners' bounds that we have seen are the share's value. So the number parts by
the kind of the mark's place. There are two letters, `kap₃` for K3 and `kap₆` for K6, since nothing
says that the two owners' factors are one number. At K3 and K6 the number is the numerator times a
letter: it is not a share that is held. -/
noncomputable def qMHead {S Cl : Type} (kap₃ kap₆ : ℝ≥0∞) (_ : Block S Cl) (mk : Mark) : ℝ≥0∞ :=
  if mk.place.kind = KindName.K3 then (mk.share.num : ℝ≥0∞) * kap₃
  else if mk.place.kind = KindName.K6 then (mk.share.num : ℝ≥0∞) * kap₆ else mk.share.val

variable {Zp : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- The list's length. -/
theorem marksHead_length : (marksHead Zp G₀).length =
    (P1K8.part1Marks Zp G₀).length + (K3.Good.k3Marks Zp G₀).length +
      (K4.k4MarksWide Zp G₀).length + (K5.k5Marks Zp G₀).length + (K6.part4Marks Zp G₀).length := by
  unfold marksHead
  simp only [List.length_append]

/-- A statement on marks holds of the whole list if it holds of each owner's list. -/
theorem marksHead_all {p : Mark → Prop} (h₁ : ∀ mk ∈ P1K8.part1Marks Zp G₀, p mk)
    (h₃ : ∀ mk ∈ K3.Good.k3Marks Zp G₀, p mk) (h₄ : ∀ mk ∈ K4.k4MarksWide Zp G₀, p mk)
    (h₅ : ∀ mk ∈ K5.k5Marks Zp G₀, p mk) (h₆ : ∀ mk ∈ K6.part4Marks Zp G₀, p mk) :
    ∀ mk ∈ marksHead Zp G₀, p mk := by
  unfold marksHead
  exact List.forall_mem_append.2 ⟨List.forall_mem_append.2 ⟨List.forall_mem_append.2
    ⟨List.forall_mem_append.2 ⟨h₁, h₃⟩, h₄⟩, h₅⟩, h₆⟩

/-- The field `hseat` at `marksHead`. K6's authors' share of it is their `part4Marks_seat`, which
has no hypothesis and stands in their file of definitions. -/
theorem marksHead_seat (h₁ : ∀ mk ∈ P1K8.part1Marks Zp G₀, markSeat mk.place = true)
    (h₃ : ∀ mk ∈ K3.Good.k3Marks Zp G₀, markSeat mk.place = true)
    (h₄ : ∀ mk ∈ K4.k4MarksWide Zp G₀, markSeat mk.place = true)
    (h₅ : ∀ mk ∈ K5.k5Marks Zp G₀, markSeat mk.place = true) :
    ∀ mk ∈ marksHead Zp G₀, markSeat mk.place = true :=
  marksHead_all h₁ h₃ h₄ h₅ (K6.part4Marks_seat Zp G₀)

variable {S Cl : Type}

/-- Every mark stands at the place of a sub-protocol of the chain. -/
theorem marksHead_member {all : List (Block S Cl)}
    (h₁ : ∀ mk ∈ P1K8.part1Marks Zp G₀, ∃ b ∈ all, b.place = mk.place)
    (h₃ : ∀ mk ∈ K3.Good.k3Marks Zp G₀, ∃ b ∈ all, b.place = mk.place)
    (h₄ : ∀ mk ∈ K4.k4MarksWide Zp G₀, ∃ b ∈ all, b.place = mk.place)
    (h₅ : ∀ mk ∈ K5.k5Marks Zp G₀, ∃ b ∈ all, b.place = mk.place)
    (h₆ : ∀ mk ∈ K6.part4Marks Zp G₀, ∃ b ∈ all, b.place = mk.place) :
    ∀ mk ∈ marksHead Zp G₀, ∃ b ∈ all, b.place = mk.place :=
  marksHead_all h₁ h₃ h₄ h₅ h₆

/-- The number at a place of the kind K3. -/
theorem qMHead_k3 (kap₃ kap₆ : ℝ≥0∞) (b : Block S Cl) {mk : Mark}
    (h : mk.place.kind = KindName.K3) :
    qMHead kap₃ kap₆ b mk = (mk.share.num : ℝ≥0∞) * kap₃ := by
  unfold qMHead
  rw [if_pos h]

/-- The number at a place of the kind K6. -/
theorem qMHead_k6 (kap₃ kap₆ : ℝ≥0∞) (b : Block S Cl) {mk : Mark}
    (h : mk.place.kind = KindName.K6) :
    qMHead kap₃ kap₆ b mk = (mk.share.num : ℝ≥0∞) * kap₆ := by
  have h3 : mk.place.kind ≠ KindName.K3 := by
    rw [h]
    decide
  unfold qMHead
  rw [if_neg h3, if_pos h]

/-- The number at any other place. -/
theorem qMHead_other (kap₃ kap₆ : ℝ≥0∞) (b : Block S Cl) {mk : Mark}
    (h : mk.place.kind ≠ KindName.K3 ∧ mk.place.kind ≠ KindName.K6) :
    qMHead kap₃ kap₆ b mk = mk.share.val := by
  unfold qMHead
  rw [if_neg h.1, if_neg h.2]

/-- K6's authors' marks stand at a place of the kind K6. -/
theorem part4_kind : ∀ mk ∈ K6.part4Marks Zp G₀, mk.place.kind = KindName.K6 := by
  intro mk hmk
  unfold K6.part4Marks at hmk
  rcases List.mem_cons.1 hmk with rfl | h2
  · rfl
  · rcases List.mem_cons.1 h2 with rfl | h3
    · rfl
    · exact absurd h3 List.not_mem_nil

/-- The field `hq0` at `qMHead`. -/
theorem hq0_head (kap₃ kap₆ : ℝ≥0∞) (pre₁ : List (Block S Cl)) :
    ∀ b ∈ pre₁, qMHead kap₃ kap₆ b ⟨b.place,
      fun _ own => if drawsFit b.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ = 0 := by
  intro b hb
  by_cases h : b.place.kind = KindName.K3
  · rw [qMHead_k3 kap₃ kap₆ b h]
    exact hq0_num pre₁ kap₃ b hb
  · by_cases h' : b.place.kind = KindName.K6
    · rw [qMHead_k6 kap₃ kap₆ b h']
      exact hq0_num pre₁ kap₆ b hb
    · rw [qMHead_other kap₃ kap₆ b ⟨h, h'⟩]
      exact hq0_val pre₁ b hb

/-- The field `hM` at `marksHead` and `qMHead`, from each owner's bounds at its own list and number,
and the kinds of the places: K3 at the lookups' marks, K6 at K6's authors' (`part4_kind`), neither
at the others. -/
theorem marksHead_hM (C : CK) (kap₃ kap₆ : ℝ≥0∞) {pre₁ : List (Block S Cl)}
    {PM : Block S Cl → List Fmt.Drawn → Prop}
    (k₁ : ∀ mk ∈ P1K8.part1Marks Zp G₀,
      mk.place.kind ≠ KindName.K3 ∧ mk.place.kind ≠ KindName.K6)
    (h₁ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (P1K8.part1Marks Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (mk.share.val))
    (k₃ : ∀ mk ∈ K3.Good.k3Marks Zp G₀, mk.place.kind = KindName.K3)
    (h₃ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (K3.Good.k3Marks Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) ((mk.share.num : ℝ≥0∞) * kap₃))
    (k₄ : ∀ mk ∈ K4.k4MarksWide Zp G₀,
      mk.place.kind ≠ KindName.K3 ∧ mk.place.kind ≠ KindName.K6)
    (h₄ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (K4.k4MarksWide Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (mk.share.val))
    (k₅ : ∀ mk ∈ K5.k5Marks Zp G₀,
      mk.place.kind ≠ KindName.K3 ∧ mk.place.kind ≠ KindName.K6)
    (h₅ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (K5.k5Marks Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (mk.share.val))
    (h₆ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (K6.part4Marks Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt C mk dsb (PM b) ((mk.share.num : ℝ≥0∞) * kap₆)) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (marksHead Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt C mk dsb (PM b) (qMHead kap₃ kap₆ b mk) := by
  unfold marksHead
  refine hM_append C (hM_append C (hM_append C (hM_append C ?_ ?_) ?_) ?_) ?_
  · exact hM_congr C (q' := fun _ mk => mk.share.val)
      (fun b mk h => qMHead_other kap₃ kap₆ b (k₁ mk h)) h₁
  · exact hM_congr C (q' := fun _ mk => (mk.share.num : ℝ≥0∞) * kap₃)
      (fun b mk h => qMHead_k3 kap₃ kap₆ b (k₃ mk h)) h₃
  · exact hM_congr C (q' := fun _ mk => mk.share.val)
      (fun b mk h => qMHead_other kap₃ kap₆ b (k₄ mk h)) h₄
  · exact hM_congr C (q' := fun _ mk => mk.share.val)
      (fun b mk h => qMHead_other kap₃ kap₆ b (k₅ mk h)) h₅
  · exact hM_congr C (q' := fun _ mk => (mk.share.num : ℝ≥0∞) * kap₆)
      (fun b mk h => qMHead_k6 kap₃ kap₆ b (part4_kind mk h)) h₆

end ProofFile.Honest

#print axioms ProofFile.Honest.marksHead_length
#print axioms ProofFile.Honest.marksHead_all
#print axioms ProofFile.Honest.marksHead_seat
#print axioms ProofFile.Honest.marksHead_member
#print axioms ProofFile.Honest.qMHead_k3
#print axioms ProofFile.Honest.qMHead_k6
#print axioms ProofFile.Honest.qMHead_other
#print axioms ProofFile.Honest.part4_kind
#print axioms ProofFile.Honest.hq0_head
#print axioms ProofFile.Honest.marksHead_hM
