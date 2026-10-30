-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Pay/SidesWhole.lean: WHOLE halved AND rooted, FROM ONE LINE A KIND.
The tests halvedAll and rootedAll (Honest/Law/Run.lean, Honest/Law/PlanGives.lean) ask at each
sub-protocol of each chain a side, or rounds that declare nothing. At WP's plan the kinds that are
not listed here declare nothing (written_quiet, by the kernel), and under PlanAlike that holds at any
description. So what each listed kind owes is SidesWhere: a side at each of its sub-protocols that
declares something.

  quietRound, quietTest      a round that declares nothing but roots and no root; the test
  sendsFirst, sendsShared, sendsSecond   the kinds of the three chains that declare something
  written_quiet              the test at WP, by the kernel
  SidesWhere                 what a kind owes at a chain
  KindsWhole                 what the kinds owe at the three chains
  sidesWhole_of_kinds        **halvedAll and rootedAll from KindsWhole**
  sealPlain_alike            sealPlain, at any description alike to WP

Limits. Implications. SidesWhere is shown here of no kind. The tests read places and declared rounds
alone: that a side is the right one is not said. Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K1.Pay.Written
import Johnson.Desc.ProofFile.Honest.BookAlike
import Johnson.Desc.ProofFile.Honest.Law.Run
import Johnson.Desc.ProofFile.Honest.Law.PlanGives
import Johnson.Desc.ProofFile.Honest.Law.Thread

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1.Pay
open VerifiableInference.Desc (Block FileDescription Place KindName PlanAlike alike₂_rounds)
open P2Law.ProofPlan (WP)

variable {Xi S Cl V W X W₀ Rc Ky Tr X₀ : Type}

/-- A round that declares no item but roots, and no root. -/
def quietRound (d : Fmt.DeclaredRound) : Bool :=
  (d.items.filter (· != .root)).isEmpty && d.entry.roots == 0

/-- **Every sub-protocol of a kind that is not listed has quiet rounds alone.** -/
def quietTest (ks : List KindName) (l : List PlanB) : Bool :=
  l.all fun x => ks.contains x.place.kind || x.rounds.all quietRound

def sendsFirst : List KindName := [.K1, .K2, .K3, .K4, .K5, .K6, .K7, .K10, .K11, .K12, .K13]
def sendsShared : List KindName := [.K1, .K12, .K14]
def sendsSecond : List KindName := [.K12]

set_option maxRecDepth 1000000 in
theorem written_quiet : quietTest sendsFirst (planOf WP.first.blocksInOrder) = true ∧
    quietTest sendsShared (planOf WP.shared.blocksInOrder) = true ∧
    quietTest sendsSecond (planOf WP.second.blocksInOrder) = true := by decide +kernel

/-- **What a kind owes at a chain**: a side at each of its sub-protocols that declares something. -/
def SidesWhere (bs : List (Block S Cl)) (hs : List (Placed V W X)) (κ : KindName) : Prop :=
  ∀ b ∈ bs, b.place.kind = κ → b.rounds.all quietRound = false →
    (hs.any fun h => h.place == b.place) = true

theorem whole_of {bs : List (Block S Cl)} {hs : List (Placed V W X)} {ks : List KindName}
    (ht : quietTest ks (planOf bs) = true) (hk : ∀ κ ∈ ks, SidesWhere bs hs κ) :
    halved bs hs = true ∧ rooted bs hs = true := by
  have key : ∀ b ∈ bs, (hs.any fun h => h.place == b.place) = true ∨
      b.rounds.all quietRound = true := by
    intro b hb
    cases hq : b.rounds.all quietRound with
    | true => exact .inr rfl
    | false =>
      have h1 := List.all_eq_true.1 ht _ (List.mem_map.2 ⟨b, hb, rfl⟩)
      dsimp only at h1
      rw [hq, Bool.or_false] at h1
      exact .inl (hk _ (by simpa using h1) b hb rfl hq)
  constructor
  · unfold halved
    refine List.all_eq_true.2 fun b hb => ?_
    rcases key b hb with h | h
    · rw [h]; rfl
    · refine Bool.or_eq_true_iff.2 (.inr (List.all_eq_true.2 fun d hd => ?_))
      have := List.all_eq_true.1 h d hd
      unfold quietRound at this
      exact (Bool.and_eq_true_iff.1 this).1
  · unfold rooted
    refine List.all_eq_true.2 fun b hb => ?_
    rcases key b hb with h | h
    · rw [h]; rfl
    · refine Bool.or_eq_true_iff.2 (.inr (List.all_eq_true.2 fun d hd => ?_))
      have := List.all_eq_true.1 h d hd
      unfold quietRound at this
      exact (Bool.and_eq_true_iff.1 this).2

/-- **What the kinds owe at the three chains.** -/
structure KindsWhole (F : FileDescription Xi) (H : Prover W₀ Rc Xi Ky Tr X₀ X) : Prop where
  first : ∀ κ ∈ sendsFirst, SidesWhere F.first.blocksInOrder H.first κ
  shared : ∀ κ ∈ sendsShared, SidesWhere F.shared.blocksInOrder H.shared κ
  second : ∀ κ ∈ sendsSecond, SidesWhere F.second.blocksInOrder H.second κ

/-- **halvedAll AND rootedAll, FROM ONE LINE A KIND**, at any description alike to WP. -/
theorem sidesWhole_of_kinds {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    (hF : PlanAlike WP F) (K : KindsWhole F H) :
    halvedAll F H = true ∧ rootedAll F H = true := by
  have e1 := planOf_alike hF.first
  have e2 := planOf_alike hF.shared
  have e3 := planOf_alike hF.second
  obtain ⟨a1, b1⟩ := whole_of (e1 ▸ written_quiet.1) K.first
  obtain ⟨a2, b2⟩ := whole_of (e2 ▸ written_quiet.2.1) K.shared
  obtain ⟨a3, b3⟩ := whole_of (e3 ▸ written_quiet.2.2) K.second
  simp [halvedAll, rootedAll, a1, a2, a3, b1, b2, b3]

/-- **The sealing round is plain**, at any description alike to WP. -/
theorem sealPlain_alike {F : FileDescription Xi} (hF : PlanAlike WP F) : sealPlain F = true := by
  have h : sealPlain WP = true := by decide +kernel
  unfold sealPlain at h ⊢
  have e : F.roundsDeclaredByBlocks.1 = WP.roundsDeclaredByBlocks.1 := (alike₂_rounds _ _ hF.first).symm
  rw [e]
  exact h

end ProofFile.Honest.K1.Pay

#print axioms ProofFile.Honest.K1.Pay.written_quiet
#print axioms ProofFile.Honest.K1.Pay.sidesWhole_of_kinds
#print axioms ProofFile.Honest.K1.Pay.sealPlain_alike
