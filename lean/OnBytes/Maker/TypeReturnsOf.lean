-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TypeReturnsOf.lean: the typing of a whole file returns where the three chains were
read under descriptions whose rounds have the items of the rounds from which the data were made.

`typeReturns` (OnBytes/Maker/TypeTest.lean) has six parts. This file pays four of them from the
reading's own equations: the first chain's run's value, and the typed plain parts of the three
stretches. The two others, the tables of the openings and the stored table's, stay premises.

Main theorems.
  `itemsAs_of₁`, `itemsAs_of₂`, `itemsAs_of₃`: the data that `WholeD.of a (Whole.of R₁ R₂ R₃)` lays
    have, round by round, the items of R₁ without its last round, of R₂, of R₃.
  `plains_read`: a stretch's plain parts type at a chain as read, if the description's rounds have
    the items of the rounds from which the data were made.
  `typeReturns_of`: the test says yes.

What is asked. Three equations of the shipped reader `readChain`; that the first chain's description
has random bytes; that the three descriptions' rounds have, member by member, the items of R₁, R₂,
R₃ (for the first two chains the descriptions are made of these very rounds; the third chain's
rounds are stated at the file's own roots, the data's at made-up names); that both tables return.


-/
import OnBytes.Maker.TypeTest
import OnBytes.Maker.TypingReturns
import OnBytes.Maker.ReadSpecs
import OnBytes.Maker.ReadTrace

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ OnBytes.Tie

/-- A list made by `zipWith` from l and a list that is as long is related to l member by member. -/
theorem forall₂_zipWith_left {α β γ : Type} {P : γ → α → Prop} (f : α → β → γ)
    (h : ∀ a b, P (f a b) a) : ∀ (l : List α) (m : List β), m.length = l.length →
      List.Forall₂ P (List.zipWith f l m) l
  | [], [], _ => .nil
  | a :: l, b :: m, e => .cons (h a b) (forall₂_zipWith_left f h l m (by simpa using e))

/-- The rounds' data of one chain have the rounds' items. -/
theorem itemsAs_rdsFromL (all : List (Nat × Fmt.Shape × Nat × Nat)) (t₁ t₂ here base first : Nat)
    (R : Params.Rounds) :
    ItemsAs ((Three.rdsFromL all t₁ t₂ here base first R).map rdtOf) (R.map (·.1)) := by
  unfold ItemsAs
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact forall₂_zipWith_left (P := fun d r => (rdtOf d).items = r.1.items)
    (Three.rdOf all t₁ t₂ here base first) (fun _ _ => rfl) R _ (sentBefore_length R)

theorem itemsAs_of₁ (a : ℕ) (R₁ R₂ R₃ : Params.Rounds) :
    ItemsAs (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₁ (R₁.map (·.1)).dropLast := by
  have h : ItemsAs ((Three.Whole.of R₁ R₂ R₃).ds₁.map rdtOf) (R₁.map (·.1)) :=
    itemsAs_rdsFromL _ _ _ _ _ _ R₁
  have h' := itemsAs_dropLast h
  rw [← List.map_dropLast] at h'
  exact h'

theorem itemsAs_of₂ (a : ℕ) (R₁ R₂ R₃ : Params.Rounds) :
    ItemsAs (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₂ (R₂.map (·.1)) :=
  itemsAs_rdsFromL _ _ _ _ _ _ R₂

theorem itemsAs_of₃ (a : ℕ) (R₁ R₂ R₃ : Params.Rounds) :
    ItemsAs (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₃ (R₃.map (·.1)) :=
  itemsAs_rdsFromL _ _ _ _ _ _ R₃

/-- Two lists of rounds have the same items, member by member. -/
def SameItems (rs rs' : List Fmt.Round) : Prop :=
  List.Forall₂ (fun r r' => r.items = r'.items) rs rs'

theorem ItemsAs.trans {ds : List RDT} {rs rs' : List Fmt.Round} (h : ItemsAs ds rs)
    (h' : SameItems rs rs') : ItemsAs ds rs' := by
  induction h generalizing rs' with
  | nil => cases h'; exact .nil
  | cons hd _ ih =>
    cases h' with
    | cons hr ht => exact .cons (hd.trans hr) (ih ht)

theorem sameItems_refl : ∀ rs : List Fmt.Round, SameItems rs rs
  | [] => .nil
  | _ :: rs => .cons rfl (sameItems_refl rs)

/-- **A stretch's plain parts type at a chain as read.** -/
theorem plains_read (C : CK) (ds : List RDT) (rs : List Fmt.Round) (S : Fmt.SpecX)
    (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut) (j : ℕ)
    (e : readChain S seen b i = some (o, j)) (hi : ItemsAs ds rs)
    (hs : SameItems rs S.base.rounds) :
    (plainsT C ds o.rounds.toList).isSome = true := by
  obtain ⟨pl, h⟩ := plainsT_some C S.base.plan.field ds S.base.rounds o.rounds.toList (hi.trans hs)
    (readChain_vals S seen b i o j e)
  rw [h]
  rfl

/-- The same for the first chain without its last round. -/
theorem plains_read_dropLast (C : CK) (ds : List RDT) (rs : List Fmt.Round) (S : Fmt.SpecX)
    (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut) (j : ℕ)
    (e : readChain S seen b i = some (o, j)) (hi : ItemsAs ds rs.dropLast)
    (hs : SameItems rs S.base.rounds) : (plainsT C ds o.rounds.toList.dropLast).isSome = true := by
  obtain ⟨pl, h⟩ := plainsT_some C S.base.plan.field ds S.base.rounds.dropLast
    o.rounds.toList.dropLast (hi.trans (forall₂_dropLast hs))
    (valsAs_dropLast (readChain_vals S seen b i o j e))
  rw [h]
  rfl

/-- **The typing of a whole file returns.** -/
theorem typeReturns_of (C : CK) (a : ℕ) (R₁ R₂ R₃ : Params.Rounds) (saltBytes : ℕ)
    (cfg : ByteArray) (r : Proof.TailRead) (S₁ S₂ S₃ : Fmt.SpecX) (seen₁ seen₂ seen₃ : Fmt.Seen)
    (b : ByteArray) (i₁ i₂ i₃ j₁ j₂ j₃ : ℕ)
    (e₁ : readChain S₁ seen₁ b i₁ = some (r.first.out, j₁))
    (e₂ : readChain S₂ seen₂ b i₂ = some (r.shared.out, j₂))
    (e₃ : readChain S₃ seen₃ b i₃ = some (r.second.out, j₃))
    (hr : S₁.base.rand ≠ .none)
    (h₁ : SameItems (R₁.map (·.1)) S₁.base.rounds) (h₂ : SameItems (R₂.map (·.1)) S₂.base.rounds)
    (h₃ : SameItems (R₃.map (·.1)) S₃.base.rounds)
    (ht : (tabsWFull (Three.Whole.of R₁ R₂ R₃) saltBytes r).isSome = true)
    (hx : (extWFull a cfg (Three.Whole.of R₁ R₂ R₃) r).isSome = true) :
    typeReturns C a (Three.Whole.of R₁ R₂ R₃) saltBytes cfg r = true := by
  obtain ⟨run, hrun⟩ := readChain_run S₁ seen₁ b i₁ r.first.out j₁ e₁ hr
  unfold typeReturns
  rw [ht, hx, hrun,
    plains_read_dropLast C _ _ S₁ seen₁ b i₁ _ j₁ e₁ (itemsAs_of₁ a R₁ R₂ R₃) h₁,
    plains_read C _ _ S₂ seen₂ b i₂ _ j₂ e₂ (itemsAs_of₂ a R₁ R₂ R₃) h₂,
    plains_read C _ _ S₃ seen₃ b i₃ _ j₃ e₃ (itemsAs_of₃ a R₁ R₂ R₃) h₃]
  rfl

end OnBytes.Maker
