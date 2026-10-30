-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/GuardAtDriverHolds.lean: the law of Johnson/Desc/Sound/SeatGuardHolds.lean at the
driver's own text: where every block that the seat hands at a place of the kind K7 has a property Q
that goes down along `Block.Under`, every block of the first chain's flat list at such a place has
Q.

The walk is that of `blockAt_hears`, `linkAt_hearsAt`, `bare_hearsAt` and `firstChain_flat_hears`
(Johnson/Desc/Sound/GuardAtDriver.lean), line for line, with Q in the place of "hears once".

Main names:
  `blockAt_holds`, `linkAt_holdsAt`, `bare_holdsAt`, `firstChain_flat_holds`.
  `firstChain_flat_lays`: at `Q := Block.Lays h rd`: where every block that the seat hands at a
    place of the kind K7 lays rd of the rounds that it was shown, so does every block of the flat
    list at such a place.

Silly members. A seat that hands, at K7's place, a block that says yes to all and lays nothing: the
premise of `firstChain_flat_lays` fails. A seat that hands no block at such a place: the premise
is met for nothing, and no first chain is made of it (the driver asks a block at every place).
Every "there is", walked: no statement has one.
Limits. Rules at the driver's text, general in the seat: nothing is shown of any seat. A clause on a
block's rounds does not cross by this law (`guarded_rounds`, and the driver's stamp keeps rounds).
That a run goes by this chain is not said here. Nothing on soundness.

-/
import Johnson.Desc.Sound.GuardAtDriver
import Johnson.Desc.Sound.SeatGuardHolds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc

variable {S Cl α : Type}

section
variable {H : Blocks S Cl} {links : List ModelPart} {several : Bool} {c c₀ : Chain S Cl}
variable {Q : Block S Cl → Prop}

theorem blockAt_holds (hQ : DownUnder Q) (hK : ∀ a b, H.block a = some b → a.kind = .K7 → Q b)
    {a : Place} {b : Block S Cl} (h : blockAt H a = some b) (hp : hearsReply b.place = true) :
    Q b := by
  unfold blockAt at h
  obtain ⟨b₀, e₀, rfl⟩ := Option.map_eq_some_iff.1 h
  exact hQ _ b₀ (fun _ _ _ _ D => D) (hK a b₀ e₀ (hearsReply_kind hp))

theorem linkAt_holdsAt (hQ : DownUnder Q) (hK : ∀ a b, H.block a = some b → a.kind = .K7 → Q b)
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
    exact blockAt_holds hQ hK e hp
  · obtain ⟨a, _, e⟩ := mem_of_mapM (blockAt H) _ _ hc b hb
    exact blockAt_holds hQ hK e hp

theorem bare_holdsAt (hQ : DownUnder Q) (hK : ∀ a b, H.block a = some b → a.kind = .K7 → Q b)
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
    exact linkAt_holdsAt hQ hK e
  · obtain ⟨a, _, e⟩ := mem_of_mapM (blockAt H) _ _ hb b m
    exact blockAt_holds hQ hK e hp

/-- **Every block of the first chain's flat list at a place of the kind K7 has the property.** -/
theorem firstChain_flat_holds (hQ : DownUnder Q)
    (hK : ∀ a b, H.block a = some b → a.kind = .K7 → Q b)
    (h : firstChain H links several = some c) :
    ∀ b ∈ c.blocksInOrder, hearsReply b.place = true → Q b := by
  obtain ⟨c₁, h₁, rfl⟩ := firstChain_some h
  exact (bare_holdsAt hQ hK h₁).guarded_flat H.same hQ

/-- **At "lays".** -/
theorem firstChain_flat_lays {hh : S → α} {rd : List Fmt.RoundView → α}
    (hK : ∀ a b, H.block a = some b → a.kind = .K7 → b.Lays hh rd)
    (h : firstChain H links several = some c) :
    ∀ b ∈ c.blocksInOrder, hearsReply b.place = true → b.Lays hh rd :=
  firstChain_flat_holds (lays_down hh rd) hK h

end

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.firstChain_flat_holds
#print axioms VerifiableInference.Desc.First.firstChain_flat_lays
