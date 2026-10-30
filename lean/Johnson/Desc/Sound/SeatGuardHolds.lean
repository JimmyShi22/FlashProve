-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/SeatGuardHolds.lean: behind the guard (Johnson/Desc/SeatGuard.lean), every block
of the guarded chain's flat list that stands at a place told apart has a property Q, from the
unguarded chain's parts: general in every property Q of blocks that goes down along `Block.Under`.

Why. Johnson/Desc/Sound/SeatGuardHears.lean has this law at the one property `Block.HearsOnce r`.
That property does not say what is laid. A caller that needs `Block.Lays h rd` at the place told
apart needs the same walk once more. Here the walk is made once, for every such property.

Main names:
  `DownUnder Q`: where b' says yes only where b says the same yes, Q b gives Q b'.
  `lays_down`, `leaves_down`, `hearsOnce_down`: three properties that go down.
  `Link.HoldsAt Q but`, `Chain.HoldsAt Q but`: the debt: each block of first, front, hear, close,
    back, last at a place that `but` names has Q; the batching's place and the places of the kind
    "frame" are not told apart.
  `Chain.HoldsAt.guarded_flat`: then every block of `(c.guarded same but).blocksInOrder` at a place that
    `but` names has Q.
  `guarded_rounds`: the guarded block's rounds are the block's. A clause on a block's rounds is no
    property that goes down along `Block.Under`, which sees decisions alone; it crosses by this.

Silly members. `Q := fun _ => True`: the law says nothing. `Q := fun _ => False`: it goes down; the
debt then says that no block of the six sorts stands at a place told apart. `but := fun _ => false`:
the debt is met for nothing. `but := fun _ => true`: the debt fails at the first link ("frame").
Every "there is", walked: no statement has one.
Limits. Rules: shown of no chain of the protocol. Nothing on soundness, on acceptance or on hiding.

-/
import Johnson.Desc.Sound.SeatGuardHears

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl α β : Type}

/-- The property goes down along `Block.Under`. -/
def DownUnder (Q : Block S Cl → Prop) : Prop := ∀ b' b : Block S Cl, b'.Under b → Q b → Q b'

theorem lays_down (h : S → α) (rd : List Fmt.RoundView → α) :
    DownUnder fun b : Block S Cl => b.Lays h rd :=
  fun _ _ u H s rs gs s' D => H s rs gs s' (u s rs gs s' D)

theorem leaves_down (h : S → α) : DownUnder fun b : Block S Cl => b.Leaves h :=
  fun _ _ u H => leaves_of_under u H

theorem hearsOnce_down (r : S → Option β) : DownUnder fun b : Block S Cl => b.HearsOnce r :=
  fun _ _ u H => hearsOnce_of_under u H

/-- What a link's parts owe for the places told apart. -/
structure Link.HoldsAt (Q : Block S Cl → Prop) (but : Place → Bool) (L : Link S Cl) : Prop where
  hear : ∀ b ∈ L.hear, but b.place = true → Q b
  close : ∀ b ∈ L.close, but b.place = true → Q b
  batch : ∀ f, but (L.batch f).place = false
  frame : ∀ i, but ⟨L.chain, some L.number, i, .frame⟩ = false

/-- What a chain's parts owe for the places told apart. -/
structure Chain.HoldsAt (Q : Block S Cl → Prop) (but : Place → Bool) (c : Chain S Cl) : Prop where
  first : but c.first.place = true → Q c.first
  front : ∀ b ∈ c.front, but b.place = true → Q b
  links : ∀ L ∈ c.links, L.HoldsAt Q but
  back : ∀ b ∈ c.back, but b.place = true → Q b
  last : but c.last.place = true → Q c.last

/-- The guarded block's rounds are the block's. -/
theorem guarded_rounds (same : S → S → Bool) (but : Place → Bool) (b : Block S Cl) :
    (b.guarded same but).rounds = b.rounds := rfl

section
variable {Q : Block S Cl → Prop} {but : Place → Bool} (same : S → S → Bool)

/-- One block: behind the guard it has the property if it had. -/
theorem guarded_holds (hQ : DownUnder Q) (b : Block S Cl) (h : but b.place = true → Q b)
    (hp : but (b.guarded same but).place = true) : Q (b.guarded same but) :=
  hQ _ _ (guarded_under same but b) (h hp)

theorem Link.HoldsAt.guarded_flat (hQ : DownUnder Q) {L : Link S Cl} (H : L.HoldsAt Q but) :
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
    exact guarded_holds same hQ b₀ (H.hear b₀ h₀) hp
  · have hp' : but (L.batch _).place = true := hp
    rw [H.batch] at hp'
    exact nomatch hp'
  · have hp' : but ⟨L.chain, some L.number, (L.guarded same but).hear.length + 2, .frame⟩ = true :=
      hp
    rw [H.frame] at hp'
    exact nomatch hp'
  · obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hb
    exact guarded_holds same hQ b₀ (H.close b₀ h₀) hp
  · have hp' : but ⟨L.chain, some L.number,
        (L.guarded same but).hear.length + (L.guarded same but).close.length + 3, .frame⟩ = true :=
      hp
    rw [H.frame] at hp'
    exact nomatch hp'

/-- **Behind the guard, every block at a place told apart has the property.** -/
theorem Chain.HoldsAt.guarded_flat (hQ : DownUnder Q) {c : Chain S Cl} (H : c.HoldsAt Q but) :
    ∀ b ∈ (c.guarded same but).blocksInOrder, but b.place = true → Q b := by
  intro b hb hp
  unfold Chain.blocksInOrder at hb
  simp only [List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap, List.cons_append,
    List.not_mem_nil, or_false] at hb
  rcases hb with rfl | (((⟨p, hq, rfl⟩ | ⟨L, hL, hb⟩) | ⟨p, hq, rfl⟩) | rfl)
  · exact hQ _ (c.first.guarded same but) (fun _ _ _ _ D => D)
      (guarded_holds same hQ c.first H.first hp)
  · obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hq
    exact hQ _ (b₀.guarded same but) (fun _ _ _ _ D => D)
      (guarded_holds same hQ b₀ (H.front b₀ h₀) hp)
  · obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
    exact (H.links L₀ h₀).guarded_flat same hQ b hb hp
  · obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hq
    exact hQ _ (b₀.guarded same but) (fun _ _ _ _ D => D)
      (guarded_holds same hQ b₀ (H.back b₀ h₀) hp)
  · exact hQ _ (c.last.guarded same but) (fun _ _ _ _ D => D)
      (guarded_holds same hQ c.last H.last hp)

end

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.lays_down
#print axioms VerifiableInference.Desc.Link.HoldsAt.guarded_flat
#print axioms VerifiableInference.Desc.Chain.HoldsAt.guarded_flat
