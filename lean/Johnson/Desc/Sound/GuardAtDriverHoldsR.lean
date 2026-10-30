-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/GuardAtDriverHoldsR.lean: the law of Johnson/Desc/Sound/SeatGuardHoldsR.lean at
the driver's own text: where every block that the seat hands at a place of the kind K7 has a
property Q that goes down along `Block.UnderR`, every block of the first chain's flat list at such
a place has Q. Such a property may speak of a block's rounds.

The walk is that of Johnson/Desc/Sound/GuardAtDriverHolds.lean, line for line. The one crossing that
it adds to the guard's is the driver's stamp of a place, which keeps the rounds and the decision.

Main names:
  `blockAt_holdsR`, `linkAt_holdsAtR`, `bare_holdsAtR`, `firstChain_flat_holdsR`.
  `firstChain_flat_laysOne`: at "lays rd, and has n rounds".

Silly members: GuardAtDriverHolds.lean's. Every "there is", walked: no statement has one.
Limits. Rules at the driver's text, general in the seat: nothing is shown of any seat. That a run
goes by this chain is not said here. Nothing on soundness.

-/
import Johnson.Desc.Sound.GuardAtDriverHolds
import Johnson.Desc.Sound.SeatGuardHoldsR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc

variable {S Cl α : Type}

section
variable {H : Blocks S Cl} {links : List ModelPart} {several : Bool} {c c₀ : Chain S Cl}
variable {Q : Block S Cl → Prop}

theorem blockAt_holdsR (hQ : DownUnderR Q) (hK : ∀ a b, H.block a = some b → a.kind = .K7 → Q b)
    {a : Place} {b : Block S Cl} (h : blockAt H a = some b) (hp : hearsReply b.place = true) :
    Q b := by
  unfold blockAt at h
  obtain ⟨b₀, e₀, rfl⟩ := Option.map_eq_some_iff.1 h
  exact hQ _ b₀ ⟨rfl, fun _ _ _ _ D => D⟩ (hK a b₀ e₀ (hearsReply_kind hp))

theorem linkAt_holdsAtR (hQ : DownUnderR Q) (hK : ∀ a b, H.block a = some b → a.kind = .K7 → Q b)
    {l : Nat} {sub : ModelPart} {L : Link S Cl} (h : linkAt H l sub = some L) :
    L.HoldsAt Q hearsReply := by
  unfold linkAt at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨hear, hh, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨batch, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨close, hc, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  refine ⟨fun b hb hp => ?_, fun b hb hp => ?_, fun _ => rfl, fun _ => rfl⟩
  · obtain ⟨a, _, e⟩ := mem_of_mapM (blockAt H) _ _ hh b hb
    exact blockAt_holdsR hQ hK e hp
  · obtain ⟨a, _, e⟩ := mem_of_mapM (blockAt H) _ _ hc b hb
    exact blockAt_holdsR hQ hK e hp

theorem bare_holdsAtR (hQ : DownUnderR Q) (hK : ∀ a b, H.block a = some b → a.kind = .K7 → Q b)
    (h₀ : firstChainWithoutReplyGuard H links several = some c₀) : c₀.HoldsAt Q hearsReply := by
  unfold firstChainWithoutReplyGuard at h₀
  simp only [Option.bind_eq_bind, Option.pure_def] at h₀
  split at h₀
  · cases h₀
  obtain ⟨_, _, h₀⟩ := Option.bind_eq_some_iff.1 h₀
  obtain ⟨ls, hl, h₀⟩ := Option.bind_eq_some_iff.1 h₀
  obtain ⟨back, hb, h₀⟩ := Option.bind_eq_some_iff.1 h₀
  cases h₀
  refine ⟨fun hp => (Bool.false_ne_true hp).elim, (fun b m => nomatch m), fun L hL => ?_,
    fun b m hp => ?_, fun hp => (Bool.false_ne_true hp).elim⟩
  · obtain ⟨x, _, e⟩ := mem_of_mapM (fun x : ModelPart × Nat => linkAt H x.2 x.1) _ _ hl L hL
    exact linkAt_holdsAtR hQ hK e
  · obtain ⟨a, _, e⟩ := mem_of_mapM (blockAt H) _ _ hb b m
    exact blockAt_holdsR hQ hK e hp

/-- **Every block of the first chain's flat list at a place of the kind K7 has the property.** -/
theorem firstChain_flat_holdsR (hQ : DownUnderR Q)
    (hK : ∀ a b, H.block a = some b → a.kind = .K7 → Q b)
    (h : firstChain H links several = some c) :
    ∀ b ∈ c.blocksInOrder, hearsReply b.place = true → Q b := by
  obtain ⟨c₁, h₁, rfl⟩ := firstChain_some h
  exact (bare_holdsAtR hQ hK h₁).guarded_flatR H.same hQ

/-- **At "lays rd, and has n rounds".** -/
theorem firstChain_flat_laysOne {hh : S → α} {rd : List Fmt.RoundView → α} {n : Nat}
    (hK : ∀ a b, H.block a = some b → a.kind = .K7 → b.Lays hh rd ∧ b.rounds.length = n)
    (h : firstChain H links several = some c) :
    ∀ b ∈ c.blocksInOrder, hearsReply b.place = true → b.Lays hh rd ∧ b.rounds.length = n :=
  firstChain_flat_holdsR (laysOne_downR hh rd n) hK h

end

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.firstChain_flat_holdsR
#print axioms VerifiableInference.Desc.First.firstChain_flat_laysOne
