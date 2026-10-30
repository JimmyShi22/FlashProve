-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Order.lean: the order of a session's steps: the stretches of
`theActs` (Honest/Law/Rule/Session.lean) are in the order of their addresses (Honest/Frame.lean:
`Addr.before`, at the description's own order of places). This is `theActs_order`; it holds where
the description passes its test on the places. No coin and no run of a protocol occurs.

  1  `before_places`   two addresses whose places are in two consecutive segments of an order that
     has no place twice
  2  `InOrder`, `cutRow_addr`, `cutRow_order`   a definition; the stretches of a list of parts
  3  `ownOf`, `chainActs_cons`, `ownOf_place`, `chainActs_place`, `chainActs_order`   a chain's
     steps
  4  `theActs_order`   the session's

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Session
import Johnson.Desc.ProofFile.Honest.Law.Rule.Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle)

variable {Xi : Type}

/-! ## 1 Two consecutive segments of an order -/

theorem before_places {ord l₁ l₂ : List Place} (hn : ord.Nodup) (h : ord = l₁ ++ l₂) {a b : Addr}
    (ha : a.place ∈ l₁) (hb : b.place ∈ l₂) : a.before ord b = true := by
  obtain ⟨m₁, m₂, e⟩ := List.append_of_mem hb
  have h' : ord = (l₁ ++ m₁) ++ b.place :: m₂ := by rw [h, e, List.append_assoc]
  rw [h'] at hn ⊢
  refine Addr.before_of_split (List.mem_append.2 (Or.inl ha)) fun hm => ?_
  exact (List.nodup_append.1 hn).2.2 _ hm _ (List.mem_cons.2 (Or.inl rfl)) rfl

/-! ## 2 The stretches of a list of parts -/

/-- Steps whose stretches are in the order of their addresses. -/
def InOrder {F : FileDescription Xi} (ord : List Place) (A : List (Act F)) : Prop :=
  A.Pairwise fun a a' => ∀ s s', a = .lay s → a' = .lay s' → s.addr.before ord s'.addr = true

theorem cutRow_addr (ch : Nat) (tree : Nat → List Nat) (tl : Addr → Option Teller) (a : Place) :
    ∀ (cs : List Nat) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle)) (n : Nat)
      (ds : List Fmt.Drawn), ∀ s ∈ cutRow ch tree tl a j cs rs n ds,
    s.addr.place = a ∧ j ≤ s.addr.part
  | [], _, _, _, _, s, hs => by
    rw [cutRow] at hs
    cases hs
  | c :: cs, j, rs, n, ds, s, hs => by
    rw [cutRow] at hs
    rcases List.mem_cons.1 hs with e | e
    · rw [e]
      exact ⟨rfl, Nat.le_refl j⟩
    · obtain ⟨h1, h2⟩ := cutRow_addr ch tree tl a cs (j + 1) _ _ _ s e
      exact ⟨h1, by omega⟩

theorem cutRow_order (ord : List Place) (ch : Nat) (tree : Nat → List Nat)
    (tl : Addr → Option Teller) (a : Place) :
    ∀ (cs : List Nat) (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle)) (n : Nat)
      (ds : List Fmt.Drawn),
    (cutRow ch tree tl a j cs rs n ds).Pairwise fun s s' => s.addr.before ord s'.addr = true
  | [], _, _, _, _ => by
    rw [cutRow]
    exact List.Pairwise.nil
  | c :: cs, j, rs, n, ds => by
    rw [cutRow]
    refine List.pairwise_cons.2 ⟨fun s' hs' => ?_, cutRow_order ord ch tree tl a cs (j + 1) _ _ _⟩
    obtain ⟨h1, h2⟩ := cutRow_addr ch tree tl a cs (j + 1) _ _ _ s' hs'
    have e : s'.addr = ⟨a, s'.addr.part⟩ := by
      rw [← h1]
    rw [e]
    exact Addr.before_same ord a (by omega)

/-! ## 3 A chain's steps -/

section
variable {F : FileDescription Xi} {S Cl : Type} (Bk : ProverCoinCounts) (ch : Nat) (tree : Nat → List Nat)
  (tl : Addr → Option Teller) (has : Place → Bool) (J : Block S Cl → List Fmt.Drawn → Act F)
  (hJ : ∀ b own s, J b own ≠ .lay s)

/-- A sub-protocol's stretches, as `chainActs` cuts them. -/
def ownOf (b : Block S Cl) (n : Nat) (own : List Fmt.Drawn) : List Stretch :=
  if has b.place then
    cutRow ch tree tl b.place 0 ((Bk.cuts.lookup b.place).getD []) (b.rounds.zip b.oracles) n own
  else [(⟨ch, ⟨b.place, 0⟩, b.rounds.zip b.oracles, own,
    asksFrom tree ((b.rounds.zip b.oracles).map (·.2.length)) n, none⟩ : Stretch)]

theorem chainActs_cons (b : Block S Cl) (bs : List (Block S Cl)) (n : Nat) (ds : List Fmt.Drawn) :
    chainActs F Bk ch tree tl has J (b :: bs) n ds =
      (ownOf Bk ch tree tl has b n (ds.take b.rounds.length)).map Act.lay ++
        J b (ds.take b.rounds.length) :: chainActs F Bk ch tree tl has J bs
          (n + ((b.rounds.zip b.oracles).map (·.2.length)).sum) (ds.drop b.rounds.length) := rfl

theorem ownOf_place (b : Block S Cl) (n : Nat) (own : List Fmt.Drawn) :
    ∀ s ∈ ownOf Bk ch tree tl has b n own, s.addr.place = b.place := by
  intro s hs
  unfold ownOf at hs
  by_cases hh : has b.place = true
  · rw [if_pos hh] at hs
    exact (cutRow_addr ch tree tl b.place _ 0 _ _ _ s hs).1
  · rw [if_neg hh] at hs
    rw [List.mem_singleton.1 hs]

include hJ in
/-- A chain's stretches are at its sub-protocols' places. -/
theorem chainActs_place : ∀ (bs : List (Block S Cl)) (n : Nat) (ds : List Fmt.Drawn) (s : Stretch),
    Act.lay s ∈ chainActs F Bk ch tree tl has J bs n ds → s.addr.place ∈ bs.map (·.place)
  | [], _, _, s, hs => by
    rw [chainActs] at hs
    cases hs
  | b :: bs, n, ds, s, hs => by
    rw [chainActs_cons] at hs
    rcases List.mem_append.1 hs with h | h
    · obtain ⟨s', hs', e⟩ := List.mem_map.1 h
      have e' : s' = s := Act.lay.inj e
      subst e'
      exact List.mem_cons.2 (Or.inl (ownOf_place Bk ch tree tl has b _ _ s' hs'))
    · rcases List.mem_cons.1 h with e | e
      · exact absurd e.symm (hJ _ _ _)
      · exact List.mem_cons_of_mem _ (chainActs_place bs _ _ s e)

include hJ in
/-- **A chain's steps are in order.** `pre`, `post`: the places before and after these
sub-protocols, in an order that has no place twice. -/
theorem chainActs_order {ord : List Place} (hn : ord.Nodup) :
    ∀ (bs : List (Block S Cl)) (pre post : List Place) (n : Nat) (ds : List Fmt.Drawn),
    ord = pre ++ bs.map (·.place) ++ post →
    InOrder ord (chainActs F Bk ch tree tl has J bs n ds)
  | [], _, _, _, _, _ => by
    rw [chainActs]
    exact List.Pairwise.nil
  | b :: bs, pre, post, n, ds, ho => by
    have ho' : ord = (pre ++ [b.place]) ++ bs.map (·.place) ++ post := by
      rw [ho]
      simp
    have ih := chainActs_order hn bs (pre ++ [b.place]) post
      (n + ((b.rounds.zip b.oracles).map (·.2.length)).sum) (ds.drop b.rounds.length) ho'
    have hsplit : ord = (pre ++ [b.place]) ++ (bs.map (·.place) ++ post) := by
      rw [ho', List.append_assoc]
    unfold InOrder
    rw [chainActs_cons]
    refine List.pairwise_append.2 ⟨?_, List.pairwise_cons.2 ⟨fun a' _ s s' e _ =>
      absurd e (hJ _ _ _), ih⟩, ?_⟩
    · -- the sub-protocol's own stretches
      refine (List.pairwise_map).2 ?_
      unfold ownOf
      by_cases hh : has b.place = true
      · rw [if_pos hh]
        exact (cutRow_order ord ch tree tl b.place _ 0 _ _ _).imp fun {x y} hxy s s' e e' => by
          rw [← Act.lay.inj e, ← Act.lay.inj e']
          exact hxy
      · rw [if_neg hh]
        exact List.pairwise_singleton _ _
    · -- compared with the sub-protocols after it
      intro a ha a' ha' s s' e e'
      subst e
      subst e'
      have hp : s.addr.place = b.place := by
        obtain ⟨s₀, hs₀, e₀⟩ := List.mem_map.1 ha
        rw [← Act.lay.inj e₀]
        exact ownOf_place Bk ch tree tl has b _ _ s₀ hs₀
      rcases List.mem_cons.1 ha' with e | e
      · exact absurd e.symm (hJ _ _ _)
      · have hq := chainActs_place Bk ch tree tl has J hJ bs _ _ s' e
        exact before_places hn hsplit
          (List.mem_append.2 (Or.inr (by rw [hp]; exact List.mem_singleton.2 rfl)))
          (List.mem_append.2 (Or.inl hq))

end

/-! ## 4 The session's steps -/

/-- **A session's steps are in the order of their addresses.** -/
theorem theActs_order {Ky : Type} (F : FileDescription Xi) (Bk : ProverCoinCounts) (T : Sims Xi Ky) (key : Xi → Ky)
    (x : Xi) (ρ : Draws) (hp : F.placesOk = true) :
    InOrder (orderOf F) (theActs F Bk T key x ρ) := by
  have hn := orderOf_nodup hp
  have j1 : ∀ (b : Block F.S₁ F.Cl) own s, (Act.judge₁ b own : Act F) ≠ .lay s :=
    fun _ _ _ e => by cases e
  have j2 : ∀ (b : Block F.S₂ F.Cl) own s, (Act.judge₂ b own : Act F) ≠ .lay s :=
    fun _ _ _ e => by cases e
  have j3 : ∀ (b : Block F.S₃ F.Cl) own s, (Act.judge₃ b own : Act F) ≠ .lay s :=
    fun _ _ _ e => by cases e
  unfold theActs InOrder
  refine List.pairwise_append.2 ⟨List.pairwise_append.2 ⟨?_, ?_, ?_⟩,
    List.pairwise_cons.2 ⟨(fun a' _ s s' e _ => by cases e), ?_⟩, ?_⟩
  · exact chainActs_order Bk 0 _ _ _ _ j1 hn F.first.blocksInOrder []
      (F.shared.blocksInOrder.map (·.place) ++ F.second.blocksInOrder.map (·.place)) 0 ρ.first (by
                          unfold orderOf
                          rw [List.nil_append, List.append_assoc])
  · exact chainActs_order Bk 1 _ _ _ _ j2 hn F.shared.blocksInOrder (F.first.blocksInOrder.map (·.place))
      (F.second.blocksInOrder.map (·.place)) 0 ρ.shared rfl
  · intro a ha a' ha' s s' e e'
    subst e
    subst e'
    exact before_places hn (l₁ := F.first.blocksInOrder.map (·.place))
      (l₂ := F.shared.blocksInOrder.map (·.place) ++ F.second.blocksInOrder.map (·.place))
      (by unfold orderOf; rw [List.append_assoc])
      (chainActs_place Bk 0 _ _ _ _ j1 _ _ _ s ha)
      (List.mem_append.2 (Or.inl (chainActs_place Bk 1 _ _ _ _ j2 _ _ _ s' ha')))
  · exact chainActs_order Bk 2 _ _ _ _ j3 hn F.second.blocksInOrder
      (F.first.blocksInOrder.map (·.place) ++ F.shared.blocksInOrder.map (·.place)) [] 0 ρ.second (by
                          unfold orderOf
                          rw [List.append_nil])
  · intro a ha a' ha' s s' e e'
    subst e
    subst e'
    rcases List.mem_cons.1 ha' with e | e
    · cases e
    · refine before_places hn (l₁ := F.first.blocksInOrder.map (·.place) ++ F.shared.blocksInOrder.map (·.place))
        (l₂ := F.second.blocksInOrder.map (·.place)) rfl ?_ (chainActs_place Bk 2 _ _ _ _ j3 _ _ _ s' e)
      rcases List.mem_append.1 ha with h | h
      · exact List.mem_append.2 (Or.inl (chainActs_place Bk 0 _ _ _ _ j1 _ _ _ s h))
      · exact List.mem_append.2 (Or.inr (chainActs_place Bk 1 _ _ _ _ j2 _ _ _ s h))

end ProofFile.Honest

#print axioms ProofFile.Honest.before_places
#print axioms ProofFile.Honest.cutRow_addr
#print axioms ProofFile.Honest.cutRow_order
#print axioms ProofFile.Honest.chainActs_cons
#print axioms ProofFile.Honest.ownOf_place
#print axioms ProofFile.Honest.chainActs_place
#print axioms ProofFile.Honest.chainActs_order
#print axioms ProofFile.Honest.theActs_order
