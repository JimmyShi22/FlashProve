-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/SeatGuardHoldsR.lean: the law of Johnson/Desc/Sound/SeatGuardHolds.lean for a
wider sort of property: one that goes down along `Block.UnderR`
(Johnson/Desc/Sound/SeatGuardChain.lean: b' has b's rounds, and where b' says yes b says the same
yes). Such a property may speak of a block's rounds.

Why. `Block.Under` sees decisions alone, so "the block has one round" does not go down along it.
Every crossing of the walk keeps the rounds: the guard (`guarded_underR`), and the turn of `planOk`
that `Chain.blocksInOrder` lays on first, front, back and last. So the same walk serves.

Main names:
  `DownUnderR Q`: where b' has b's rounds and says yes only where b says the same yes, Q b gives
    Q b'. `downR_of_down`: every property that goes down along `Block.Under` is one.
  `rounds_downR n`, `and_downR`, `laysOne_downR`: "the block has n rounds" goes down; so does the
    conjunction of two that do; so does "lays rd, and has n rounds".
  `Link.HoldsAt.guarded_flatR`, `Chain.HoldsAt.guarded_flatR`: under the debt of
    SeatGuardHolds.lean every block of `(c.guarded same but).blocksInOrder` at a place that `but` names
    has Q.

Silly members: SeatGuardHolds.lean's. Every "there is", walked: no statement has one.
Limits. Rules: shown of no chain of the protocol. Nothing on soundness, on acceptance or on hiding.

-/
import Johnson.Desc.Sound.SeatGuardHolds
import Johnson.Desc.Sound.SeatGuardChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl α : Type}

/-- The property goes down along `Block.UnderR`. -/
def DownUnderR (Q : Block S Cl → Prop) : Prop := ∀ b' b : Block S Cl, b'.UnderR b → Q b → Q b'

theorem downR_of_down {Q : Block S Cl → Prop} (h : DownUnder Q) : DownUnderR Q :=
  fun b' b u => h b' b u.2

theorem rounds_downR (n : Nat) : DownUnderR fun b : Block S Cl => b.rounds.length = n :=
  fun _ _ u H => (congrArg List.length u.1).trans H

theorem and_downR {Q R : Block S Cl → Prop} (hQ : DownUnderR Q) (hR : DownUnderR R) :
    DownUnderR fun b => Q b ∧ R b :=
  fun b' b u H => ⟨hQ b' b u H.1, hR b' b u H.2⟩

theorem laysOne_downR (h : S → α) (rd : List Fmt.RoundView → α) (n : Nat) :
    DownUnderR fun b : Block S Cl => b.Lays h rd ∧ b.rounds.length = n :=
  and_downR (downR_of_down (lays_down h rd)) (rounds_downR n)

section
variable {Q : Block S Cl → Prop} {but : Place → Bool} (same : S → S → Bool)

/-- One block: behind the guard it has the property if it had. -/
theorem guarded_holdsR (hQ : DownUnderR Q) (b : Block S Cl) (h : but b.place = true → Q b)
    (hp : but (b.guarded same but).place = true) : Q (b.guarded same but) :=
  hQ _ _ (guarded_underR same but b) (h hp)

theorem Link.HoldsAt.guarded_flatR (hQ : DownUnderR Q) {L : Link S Cl} (H : L.HoldsAt Q but) :
    ∀ b ∈ (L.guarded same but).blocksInOrder, but b.place = true → Q b := by
  intro b hb hp
  unfold Link.blocksInOrder at hb
  simp only [List.mem_cons, List.mem_append, List.cons_append, List.not_mem_nil,
    or_false] at hb
  rcases hb with rfl | ((hb | rfl | rfl) | hb) | rfl
  · have hp' : but ⟨L.chain, some L.number, 0, .frame⟩ = true := hp
    rw [H.frame] at hp'
    exact nomatch hp'
  · obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hb
    exact guarded_holdsR same hQ b₀ (H.hear b₀ h₀) hp
  · have hp' : but (L.batch _).place = true := hp
    rw [H.batch] at hp'
    exact nomatch hp'
  · have hp' : but ⟨L.chain, some L.number, (L.guarded same but).hear.length + 2, .frame⟩ = true :=
      hp
    rw [H.frame] at hp'
    exact nomatch hp'
  · obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hb
    exact guarded_holdsR same hQ b₀ (H.close b₀ h₀) hp
  · have hp' : but ⟨L.chain, some L.number,
        (L.guarded same but).hear.length + (L.guarded same but).close.length + 3, .frame⟩ = true :=
      hp
    rw [H.frame] at hp'
    exact nomatch hp'

/-- **Behind the guard, every block at a place told apart has the property.** -/
theorem Chain.HoldsAt.guarded_flatR (hQ : DownUnderR Q) {c : Chain S Cl} (H : c.HoldsAt Q but) :
    ∀ b ∈ (c.guarded same but).blocksInOrder, but b.place = true → Q b := by
  intro b hb hp
  unfold Chain.blocksInOrder at hb
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap, List.cons_append,
    List.not_mem_nil, or_false] at hb
  rcases hb with rfl | (((⟨p, hq, rfl⟩ | ⟨L, hL, hb⟩) | ⟨p, hq, rfl⟩) | rfl)
  · exact hQ _ (c.first.guarded same but) ⟨rfl, fun _ _ _ _ D => D⟩
      (guarded_holdsR same hQ c.first H.first hp)
  · obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hq
    exact hQ _ (b₀.guarded same but) ⟨rfl, fun _ _ _ _ D => D⟩
      (guarded_holdsR same hQ b₀ (H.front b₀ h₀) hp)
  · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
    exact (H.links L₀ h₀).guarded_flatR same hQ b hb hp
  · obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hq
    exact hQ _ (b₀.guarded same but) ⟨rfl, fun _ _ _ _ D => D⟩
      (guarded_holdsR same hQ b₀ (H.back b₀ h₀) hp)
  · exact hQ _ (c.last.guarded same but) ⟨rfl, fun _ _ _ _ D => D⟩
      (guarded_holdsR same hQ c.last H.last hp)

end

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.laysOne_downR
#print axioms VerifiableInference.Desc.Chain.HoldsAt.guarded_flatR
