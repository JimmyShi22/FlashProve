-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookSharedKit.lean: at which places the owners of the book's entries
stand, maker by maker. Lemmas on the makers of the book of coins (Honest/Book*.lean), for
Honest/BookSharedLaw.lean. No definition.

  1  `ex_bind` … `mapM_all`   where a computation that may reject returns, its parts have returned
  2  `addrOfRound_place`, `addrIn_place`, `planOf_places`   an address that is made off a list of
     sub-protocols stands at a place of that list
  3 `foldEntries_owner`, `sentIn_sender`, `ownerOf_owner` so do the owner of a fold's spending
     entry, the sender of a listed message, and an oracle message's owner
  4  `partWants_msg` … `loneWants_msg`, `linksWants_owner`   a sumcheck's stretch is laid under its
     segment's mask row or under the index-mask message
  5 `carryPair_owner`, `segmentCarries_owner` a carrying entry's owner is the carried message's
       sender
  6  `filter_none`, `carryPair_filter`, `filter_owner_and`   one owner's entries among such lists

Limits. The lemmas are about lists, addresses and places. This file proves nothing about soundness,
completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.BookShared
open VerifiableInference.Desc (Block FileDescription Place)

variable {Xi S Cl : Type}

/-! ## 1 Where a computation returns -/

theorem ex_bind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem ex_bindE {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem ex_map {ε α β : Type} {x : Except ε α} {f : α → β} {b : β}
    (h : (f <$> x) = .ok b) : ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, Except.ok.inj h⟩

theorem ex_mapE {ε α β : Type} {x : Except ε α} {f : α → β} {b : β}
    (h : x.map f = .ok b) : ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, Except.ok.inj h⟩

theorem ex_ite {ε α : Type} {c : Prop} [Decidable c] {x y : Except ε α} {b : α}
    (h : (if c then x else y) = .ok b) : (c ∧ x = .ok b) ∨ (¬c ∧ y = .ok b) := by
  by_cases hc : c
  · rw [if_pos hc] at h
    exact Or.inl ⟨hc, h⟩
  · rw [if_neg hc] at h
    exact Or.inr ⟨hc, h⟩

theorem throw_ne {α : Type} {e : String} {a : α} : (throw e : Except String α) ≠ .ok a := by
  intro h
  cases h

theorem bind_of_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {a : α} {b : β}
    (hx : x = .ok a) (hf : f a = .ok b) : (x >>= f) = .ok b := by
  rw [hx]
  exact hf

theorem opt_bind {α β : Type} {x : Option α} {f : α → Option β} {b : β}
    (h : x.bind f = some b) : ∃ a, x = some a ∧ f a = some b := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

theorem opt_map {α β : Type} {x : Option α} {f : α → β} {b : β}
    (h : x.map f = some b) : ∃ a, x = some a ∧ f a = b := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, Option.some.inj h⟩

/-- Where `mapM` returns, each element of what it returns is what the function returned at an
element of the list. -/
theorem mapM_all {ε α β : Type} {f : α → Except ε β} {P : β → Prop} :
    ∀ (l : List α) (r : List β), (∀ a ∈ l, ∀ b, f a = .ok b → P b) → l.mapM f = .ok r →
      ∀ b ∈ r, P b
  | [], r, _, h => by
    rw [List.mapM_nil] at h
    have e := Except.ok.inj h
    intro b hb
    rw [← e] at hb
    cases hb
  | a :: l, r, hf, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := ex_bind h
    obtain ⟨bs, hbs, h⟩ := ex_bind h
    have e := Except.ok.inj h
    intro y hy
    rw [← e] at hy
    cases hy with
    | head => exact hf a (List.Mem.head _) b hb
    | tail _ hy => exact mapM_all l bs (fun a' ha' => hf a' (List.Mem.tail _ ha')) hbs y hy

/-! ## 2 Addresses -/

theorem addrOfRound_place : ∀ (bs : List (Block S Cl)) (i : Nat) (a : Addr),
    addrOfRound bs i = some a → a.place ∈ bs.map (·.place)
  | [], _, _, h => by
    unfold addrOfRound at h
    cases h
  | b :: bs, i, a, h => by
    unfold addrOfRound at h
    split at h
    · have e := Option.some.inj h
      rw [← e]
      exact List.Mem.head _
    · exact List.Mem.tail _ (addrOfRound_place bs _ a h)

theorem addrIn_place : ∀ (l : List PlanB) (i : Nat) (a : Addr),
    addrIn l i = some a → a.place ∈ l.map (·.place)
  | [], _, _, h => by
    unfold addrIn at h
    cases h
  | b :: l, i, a, h => by
    unfold addrIn at h
    split at h
    · have e := Option.some.inj h
      rw [← e]
      exact List.Mem.head _
    · exact List.Mem.tail _ (addrIn_place l _ a h)

theorem planOf_places (bs : List (Block S Cl)) :
    (planOf bs).map (·.place) = bs.map (·.place) := by
  unfold planOf
  rw [List.map_map]
  rfl

/-! ## 3 Three makers -/

theorem foldEntries_owner {here later : List PlanB} {c : Johnson.G.ChainSends} {l : List Ahead}
    (h : foldEntries here later c = .ok l) : ∀ e ∈ l, e.owner.place ∈ here.map (·.place) := by
  unfold foldEntries at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨ll, hll, e⟩ := ex_map h
    intro a ha
    rw [← e] at ha
    obtain ⟨inner, hin, ha⟩ := List.mem_flatten.1 ha
    refine mapM_all _ ll (P := fun inner => ∀ a ∈ inner, a.owner.place ∈ here.map (·.place)) ?_ hll
      inner hin a ha
    intro x _ r hr
    refine mapM_all _ r ?_ hr
    intro j _ b hb
    try dsimp only at hb
    split at hb
    · cases hb
    · cases hb
    · split at hb
      · have e2 := Except.ok.inj hb
        rw [← e2]
        exact addrIn_place _ _ _ (by assumption)
      · cases hb

theorem sentIn_sender {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {ms : List SentMsg} (h : sentIn bs c later = .ok ms) :
    ∀ m ∈ ms, m.sender.place ∈ bs.map (·.place) := by
  unfold sentIn at h
  split at h
  · cases h
  · obtain ⟨ll, hll, e⟩ := ex_map h
    intro a ha
    rw [← e] at ha
    obtain ⟨inner, hin, ha⟩ := List.mem_flatten.1 ha
    refine mapM_all _ ll (P := fun inner => ∀ a ∈ inner, a.sender.place ∈ bs.map (·.place)) ?_ hll
      inner hin a ha
    intro x _ r hr
    try dsimp only at hr
    refine mapM_all _ r ?_ hr
    intro n _ b hb
    try dsimp only at hb
    split at hb
    · have e2 := Except.ok.inj hb
      rw [← e2]
      exact addrOfRound_place _ _ _ (by assumption)
    · cases hb

theorem ownerOf_owner {name : String} {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {label : String} {pick : OnBytes.OracleNotice → Bool} {m : MsgAt}
    (h : ownerOf name bs c later label pick = some m) : m.owner.place ∈ bs.map (·.place) := by
  unfold ownerOf at h
  obtain ⟨x, -, h⟩ := opt_bind h
  obtain ⟨a, ha, h⟩ := opt_bind h
  obtain ⟨st, -, h⟩ := opt_bind h
  obtain ⟨fr, -, h⟩ := opt_map h
  rw [← h]
  exact addrOfRound_place _ _ _ ha

/-! ## 4 The sumchecks' stretches -/

theorem mem_one {α : Type} {a b : α} (h : a ∈ [b]) : a = b := by
  cases h with
  | head => rfl
  | tail _ h2 => cases h2

theorem mem_two {α : Type} {a b c : α} (h : a ∈ [b, c]) : a = b ∨ a = c := by
  cases h with
  | head => exact Or.inl rfl
  | tail _ h2 => exact Or.inr (mem_one h2)

theorem partWants_msg (row idx : MsgAt) (merge : Bool) (p : PartAt) (j t : Nat) :
    ∀ w ∈ (partWants row idx merge p j t).1, w.msg = row ∨ w.msg = idx := by
  intro w hw
  unfold partWants at hw
  dsimp only at hw
  split at hw
  · cases hw
  · split at hw
    · rw [mem_one hw]
      exact Or.inl rfl
    · split at hw
      · rw [mem_one hw]
        exact Or.inl rfl
      · split at hw
        · rcases mem_two hw with e | e
          · rw [e]
            exact Or.inl rfl
          · rw [e]
            exact Or.inr rfl
        · rcases mem_two hw with e | e
          · rw [e]
            exact Or.inl rfl
          · rw [e]
            exact Or.inl rfl

theorem partsWants_msg (row idx : MsgAt) (merges : List Addr) :
    ∀ (ps : List PartAt) (j t : Nat), ∀ w ∈ (partsWants row idx merges ps j t).1,
      w.msg = row ∨ w.msg = idx
  | [], _, _, w, hw => by
    unfold partsWants at hw
    try dsimp only at hw
    cases hw
  | p :: ps, j, t, w, hw => by
    unfold partsWants at hw
    try dsimp only at hw
    rcases List.mem_append.1 hw with h | h
    · exact partWants_msg _ _ _ _ _ _ w h
    · exact partsWants_msg row idx merges ps _ _ w h

theorem loneWants_msg (idx : MsgAt) (lone : List Addr) :
    ∀ (ps : List PartAt) (t : Nat), ∀ w ∈ (loneWants idx lone ps t).1, w.msg = idx
  | [], _, w, hw => by
    unfold loneWants at hw
    try dsimp only at hw
    cases hw
  | p :: ps, t, w, hw => by
    unfold loneWants at hw
    try dsimp only at hw
    rcases List.mem_append.1 hw with h | h
    · split at h
      · unfold loneSumWants at h
        split at h
        · rw [mem_one h]
        · try dsimp only at h
          cases h
      · try dsimp only at h
        cases h
    · exact loneWants_msg idx lone ps _ w h

theorem linksWants_owner {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {idx : MsgAt} {merges : List Addr}
    (hidx : idx.owner.place ∈ bs.map (·.place)) :
    ∀ (ls : List Nat) (t : Nat) (r : List Want × Nat),
      linksWants bs c later idx merges ls t = .ok r →
      ∀ w ∈ r.1, w.msg.owner.place ∈ bs.map (·.place)
  | [], t, r, h, w, hw => by
    unfold linksWants at h
    have e := Except.ok.inj h
    rw [← e] at hw
    cases hw
  | l :: ls, t, r, h, w, hw => by
    unfold linksWants at h
    split at h
    · cases h
    · rename_i row hrow
      try dsimp only at h
      obtain ⟨y, hy, e⟩ := ex_mapE h
      rw [← e] at hw
      rcases List.mem_append.1 hw with h1 | h1
      · rcases partsWants_msg row idx merges _ 0 t w h1 with e1 | e1
        · rw [e1]
          exact ownerOf_owner hrow
        · rw [e1]
          exact hidx
      · exact linksWants_owner hidx ls _ y hy w h1

/-! ## 5 The carrying entries -/

theorem carryPair_owner {p q : Addr} {reach : List SentMsg} {own : Option SentMsg} :
    ∀ e ∈ carryPair p q reach own, ∃ m, (m ∈ reach ∨ own = some m) ∧ e.owner = m.sender := by
  intro e he
  unfold carryPair at he
  rcases List.mem_append.1 he with h | h
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
    exact ⟨m, Or.inl hm, rfl⟩
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
    rcases List.mem_append.1 hm with h1 | h1
    · exact ⟨m, Or.inl h1, rfl⟩
    · refine ⟨m, Or.inr ?_, rfl⟩
      cases own with
      | none => cases h1
      | some x =>
        cases h1 with
        | head => rfl
        | tail _ h2 => cases h2

theorem segmentCarries_owner {here : List PlanB} {ms : List SentMsg} {l : List Ahead}
    (h : segmentCarries here ms = .ok l) : ∀ e ∈ l, ∃ m ∈ ms, e.owner = m.sender := by
  unfold segmentCarries at h
  obtain ⟨ll, hll, e⟩ := ex_map h
  intro a ha
  rw [← e] at ha
  obtain ⟨inner, hin, ha⟩ := List.mem_flatten.1 ha
  refine mapM_all _ ll (P := fun inner => ∀ a ∈ inner, ∃ m ∈ ms, a.owner = m.sender) ?_ hll
    inner hin a ha
  intro f _ r hr
  try dsimp only at hr
  split at hr
  · have e2 := Except.ok.inj hr
    rw [← e2]
    intro a ha
    rcases List.mem_append.1 ha with h1 | h1
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h1
      exact ⟨m, (List.mem_filter.1 hm).1, rfl⟩
    · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h1
      exact ⟨m, (List.mem_filter.1 hm).1, rfl⟩
  · cases hr

/-! ## 6 One owner's entries -/

theorem filter_none {l : List Ahead} {o : Addr} (h : ∀ e ∈ l, e.owner ≠ o) :
    l.filter (·.owner == o) = [] :=
  List.filter_eq_nil_iff.2 fun e he => by
    have hne := h e he
    simp [hne]

/-- Of a fold's carrying entries, at an owner that sends none of the messages `R₁` and not the
fold's own table: those of the other messages alone. -/
theorem carryPair_filter {p q o : Addr} {R₁ R₂ : List SentMsg} {own : Option SentMsg}
    (h1 : ∀ m ∈ R₁, m.sender ≠ o) (h2 : ∀ m, own = some m → m.sender ≠ o) :
    (carryPair p q (R₁ ++ R₂) own).filter (·.owner == o) =
      (carryPair p q R₂ none).filter (·.owner == o) := by
  have a1 : (R₁.map (·.carry p)).filter (·.owner == o) = [] := filter_none (by
    intro e he
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 he
    exact h1 m hm)
  have a2 : (R₁.map (·.carry q)).filter (·.owner == o) = [] := filter_none (by
    intro e he
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 he
    exact h1 m hm)
  have a3 : (own.toList.map (·.carry q)).filter (·.owner == o) = [] := filter_none (by
    intro e he
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 he
    refine h2 m ?_
    cases own with
    | none => cases hm
    | some x =>
      cases hm with
      | head => rfl
      | tail _ h3 => cases h3)
  have e0 : (none : Option SentMsg).toList = [] := rfl
  unfold carryPair
  simp only [List.map_append, List.filter_append, a1, a2, a3, e0, List.nil_append,
    List.append_nil]

/-- Two lists that have the same entries of an owner have the same entries of that owner that meet a
further test. -/
theorem filter_owner_and {l l' : List Ahead} {o : Addr}
    (h : l.filter (·.owner == o) = l'.filter (·.owner == o)) (q : Ahead → Bool) :
    l.filter (fun e => e.owner == o && q e) = l'.filter (fun e => e.owner == o && q e) := by
  have k : ∀ x : List Ahead,
      x.filter (fun e => e.owner == o && q e) = (x.filter (·.owner == o)).filter q := by
    intro x
    rw [List.filter_filter]
    congr 1
    funext e
    exact Bool.and_comm _ _
  rw [k l, k l', h]

end ProofFile.Honest.BookShared

#print axioms ProofFile.Honest.BookShared.ex_bind
#print axioms ProofFile.Honest.BookShared.ex_bindE
#print axioms ProofFile.Honest.BookShared.ex_map
#print axioms ProofFile.Honest.BookShared.ex_mapE
#print axioms ProofFile.Honest.BookShared.ex_ite
#print axioms ProofFile.Honest.BookShared.throw_ne
#print axioms ProofFile.Honest.BookShared.bind_of_ok
#print axioms ProofFile.Honest.BookShared.opt_bind
#print axioms ProofFile.Honest.BookShared.opt_map
#print axioms ProofFile.Honest.BookShared.mapM_all
#print axioms ProofFile.Honest.BookShared.addrOfRound_place
#print axioms ProofFile.Honest.BookShared.addrIn_place
#print axioms ProofFile.Honest.BookShared.planOf_places
#print axioms ProofFile.Honest.BookShared.foldEntries_owner
#print axioms ProofFile.Honest.BookShared.sentIn_sender
#print axioms ProofFile.Honest.BookShared.ownerOf_owner
#print axioms ProofFile.Honest.BookShared.mem_one
#print axioms ProofFile.Honest.BookShared.mem_two
#print axioms ProofFile.Honest.BookShared.partWants_msg
#print axioms ProofFile.Honest.BookShared.partsWants_msg
#print axioms ProofFile.Honest.BookShared.loneWants_msg
#print axioms ProofFile.Honest.BookShared.linksWants_owner
#print axioms ProofFile.Honest.BookShared.carryPair_owner
#print axioms ProofFile.Honest.BookShared.segmentCarries_owner
#print axioms ProofFile.Honest.BookShared.filter_none
#print axioms ProofFile.Honest.BookShared.carryPair_filter
#print axioms ProofFile.Honest.BookShared.filter_owner_and
