-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/DriverKeeps.lean: Johnson/Goal/Meaning/KeepsDriver.lean's walk ONCE MORE, IN
ChainKeeps.lean's LETTERS: a property of the verifier's state that the sub-protocols handed to the
first chain's driver keep, each perhaps only on rounds with a property R, is kept by every entry of
the driver's chain's flat list in front of the entries behind the last segment. A law file; no
running text imports it.

THE WALK IS KeepsDriver.lean's, not this file's. Why once more: that file asks FoldKeeps.lean's
`Decides` of a sub-protocol, a law at ALL rounds; the code switch keeps SampleGoodS only on rounds
whose drawn elements are in canonical form, so it has `KeepsD` and no `Decides`.

  `LinkOk R P L`, `link_flat_ok`   ChainKeeps.lean's LinkKeeps | link_flat_keeps with
                    "b.planOk = true →" in front of each sub-protocol's `KeepsD`: a law may lean on
                    the sub-protocol's own test on the plan.
  `guardedFn_keeps`, `linkGuarded_keeps`   the guard on the reply (Johnson/Desc/SeatGuard.lean)
                    hands on the very state that it tests, and turns no test on the plan.
  `hearKinds_open`  no hearing place of a segment is of the kind K9 or K10.
  `BlocksKeep R P H`   what is asked of the driver's structure `Blocks`: at the places INSIDE A
                    SEGMENT ALONE `KeepsD` of every sub-protocol THAT PASSES ITS OWN TEST ON THE
                    PLAN, `KeepsRuns` of those that are not
                    of the kinds K9 and K10 (the closing's three state no run that the segment
                    calls); the batching at every function of claims that keeps P; where a segment
                    starts and ends; the chain's first entry.
  `linkAt_keeps`, `firstChain_links`   `LinkOk R P` of every segment that the driver makes.
  `firstChain_front`   so every entry of `frontOf c` that passes its own test on the plan has
                    `KeepsD R P`.
  `take_front`, `firstChain_take`   and so every such entry of `c.blocksInOrder.take k`, at
                    k ≤ (frontOf c).length.
Limits. Nothing is asked, and nothing is said, of the entries behind the last segment or of the
seal. Nothing on any one property or kind. Nothing on soundness or on hiding.

-/
import Johnson.Top.H0.K2Hands.ChainKeeps
import Johnson.Goal.Meaning.KeepsDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Keeps1
open VerifiableInference.Desc
open VerifiableInference.Desc.First (Blocks ModelPart firstChain firstChainWithoutReplyGuard linkAt blockAt addresses
  closeAddresses mem_of_mapM kindsBeforeBatching kindOfModelPart)
open Meaning.K2 (frontOf backOf flat_eq firstChain_noFront)

variable {S Cl : Type} {R : Fmt.RoundView → Prop} {P : S → Prop}

/-! ## The guard on the reply -/

theorem guardedFn_keeps (same : S → S → Bool) {f : S → Except String S}
    (h : ∀ s s', f s = .ok s' → P s → P s') :
    ∀ s s', (f s).bind (seatSame same s) = .ok s' → P s → P s' := by
  intro s s' hy hs
  obtain ⟨t, h1, h2⟩ := bind_ok hy
  rw [seatSame_ok h2]
  exact h s t h1 hs

/-- What is asked of a segment: ChainKeeps.lean's `LinkKeeps`, each sub-protocol's `KeepsD` under
its own test on the plan. -/
structure LinkOk (R : Fmt.RoundView → Prop) (P : S → Prop) (L : Link S Cl) : Prop where
  lay : ∀ s s', L.lay s = .ok s' → P s → P s'
  hearD : ∀ b ∈ L.hear, b.planOk = true → KeepsD R P b
  hearR : ∀ b ∈ L.hear, KeepsRuns P b
  batch : ∀ f : S → Except String (List Cl × S), (∀ s y, f s = .ok y → P s → P y.2) →
    (L.batch f).planOk = true → KeepsD R P (L.batch f)
  close : ∀ b ∈ L.close, b.planOk = true → KeepsD R P b
  clear : ∀ s s', L.clear s = .ok s' → P s → P s'

/-- Every entry of a segment's flat list that passes its own test on the plan. -/
theorem link_flat_ok {L : Link S Cl} (h : LinkOk R P L) :
    ∀ b ∈ L.blocksInOrder, b.planOk = true → KeepsD R P b := by
  intro b hb
  unfold Link.blocksInOrder at hb
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false] at hb
  rcases hb with rfl | ((hb | rfl | rfl) | hb) | rfl
  · exact fun _ s s' _ _ _ hy => h.lay s s' hy
  · exact h.hearD b hb
  · exact h.batch _ fun s y hy hs => claimsInBy_keeps h.hearR hy hs
  · refine fun _ => keepsD_quiet fun s s' hy hs => ?_
    unfold Link.runBehind at hy
    split at hy
    · exact afterIn_keeps h.hearR hy hs
    · cases hy
  · exact h.close b hb
  · exact fun _ => keepsD_quiet h.clear

theorem linkGuarded_keeps (same : S → S → Bool) (but : Place → Bool) {L : Link S Cl}
    (h : LinkOk R P L) : LinkOk R P (L.guarded same but) where
  lay := guardedFn_keeps same h.lay
  hearD := fun b hb => by
    obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.1 hb
    exact fun hp => keepsD_guarded same but (h.hearD b₀ hb₀ hp)
  hearR := fun b hb => by
    obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.1 hb
    exact keepsRuns_guarded same but (h.hearR b₀ hb₀)
  batch := fun f hf hp => keepsD_guarded same but (h.batch f hf hp)
  close := fun b hb => by
    obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.1 hb
    exact fun hp => keepsD_guarded same but (h.close b₀ hb₀ hp)
  clear := guardedFn_keeps same h.clear

/-! ## The driver -/

theorem fst_mem_zipIdx {α : Type} : ∀ (l : List α) (n : Nat) (x : α × Nat), x ∈ l.zipIdx n → x.1 ∈ l
  | [], _, _, h => by cases h
  | a :: l, n, x, h => by
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (fst_mem_zipIdx l _ x h)

/-- No hearing place of a segment is of the kind K9 or K10. -/
theorem hearKinds_open (sub : ModelPart) (first : Bool) :
    ∀ k ∈ kindsBeforeBatching sub first, k ≠ KindName.K9 ∧ k ≠ KindName.K10 := by
  cases sub <;> cases first <;> decide

/-- What is asked of the driver's structure. -/
structure BlocksKeep (R : Fmt.RoundView → Prop) (P : S → Prop) (H : Blocks S Cl) : Prop where
  blockD : ∀ a b, a.link ≠ none → H.block a = some b → b.planOk = true → KeepsD R P b
  blockR : ∀ a b, a.link ≠ none → a.kind ≠ KindName.K9 → a.kind ≠ KindName.K10 →
    H.block a = some b → KeepsRuns P b
  batch : ∀ a mk, a.link ≠ none → H.batch a = some mk →
    ∀ f : S → Except String (List Cl × S), (∀ s y, f s = .ok y → P s → P y.2) →
      (mk f).planOk = true → KeepsD R P (mk f)
  lay : ∀ l s s', H.lay l s = .ok s' → P s → P s'
  clear : ∀ l s s', H.clear l s = .ok s' → P s → P s'
  first : KeepsD R P H.first

theorem blockAt_keepsD {H : Blocks S Cl} (K : BlocksKeep R P H) {a : Place} {b : Block S Cl}
    (ha : a.link ≠ none) (h : blockAt H a = some b) : b.planOk = true → KeepsD R P b := by
  unfold blockAt at h
  obtain ⟨b₀, e, rfl⟩ := Option.map_eq_some_iff.1 h
  exact fun hp => keepsD_under rfl (K.blockD a b₀ ha e hp)

theorem blockAt_keepsRuns {H : Blocks S Cl} (K : BlocksKeep R P H) {a : Place} {b : Block S Cl}
    (ha : a.link ≠ none) (h9 : a.kind ≠ KindName.K9) (h10 : a.kind ≠ KindName.K10)
    (h : blockAt H a = some b) : KeepsRuns P b := by
  unfold blockAt at h
  obtain ⟨b₀, e, rfl⟩ := Option.map_eq_some_iff.1 h
  exact K.blockR a b₀ ha h9 h10 e

theorem linkAt_keeps {H : Blocks S Cl} (K : BlocksKeep R P H) {l : Nat} {sub : ModelPart}
    {L : Link S Cl} (h : linkAt H l sub = some L) : LinkOk R P L := by
  unfold linkAt at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨hear, hh, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨batch, hb, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨close, hc, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  refine ⟨K.lay l, fun b hb' => ?_, fun b hb' => ?_,
    fun f hf hp => keepsD_under rfl (K.batch _ _ (Option.some_ne_none l) hb f hf hp),
    fun b hb' => ?_, K.clear l⟩
  · obtain ⟨a, ha, e⟩ := mem_of_mapM _ _ _ hh b hb'
    unfold addresses at ha
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
    exact blockAt_keepsD K (Option.some_ne_none l) e
  · obtain ⟨a, ha, e⟩ := mem_of_mapM _ _ _ hh b hb'
    unfold addresses at ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    obtain ⟨h9, h10⟩ := hearKinds_open sub (l == 0) x.1 (fst_mem_zipIdx _ _ x hx)
    exact blockAt_keepsRuns K (Option.some_ne_none l) h9 h10 e
  · obtain ⟨a, ha, e⟩ := mem_of_mapM _ _ _ hc b hb'
    unfold closeAddresses at ha
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
    exact blockAt_keepsD K (Option.some_ne_none l) e

/-- **The driver's chain: its first entry and every segment.** -/
theorem firstChain_links {H : Blocks S Cl} (K : BlocksKeep R P H) {links : List ModelPart}
    {several : Bool} {c : Chain S Cl} (h : firstChain H links several = some c) :
    KeepsD R P c.first ∧ ∀ L ∈ c.links, LinkOk R P L := by
  unfold firstChain at h
  obtain ⟨c₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold firstChainWithoutReplyGuard at h0
  simp only [Option.bind_eq_bind, Option.pure_def] at h0
  split at h0
  · cases h0
  obtain ⟨_, _, h0⟩ := Option.bind_eq_some_iff.1 h0
  obtain ⟨ls, hl, h0⟩ := Option.bind_eq_some_iff.1 h0
  obtain ⟨back, -, h0⟩ := Option.bind_eq_some_iff.1 h0
  cases h0
  refine ⟨keepsD_guarded _ _ (keepsD_under rfl K.first), fun L hL => ?_⟩
  obtain ⟨L₀, hL₀, rfl⟩ := List.mem_map.1 hL
  obtain ⟨x, -, e⟩ := mem_of_mapM _ _ _ hl L₀ hL₀
  exact linkGuarded_keeps _ _ (linkAt_keeps K e)

/-- **Every entry of the flat list in front of the entries behind the last segment**, under its own
test on the plan. -/
theorem firstChain_front {H : Blocks S Cl} (K : BlocksKeep R P H) {links : List ModelPart}
    {several : Bool} {c : Chain S Cl} (h : firstChain H links several = some c) :
    ∀ b ∈ frontOf c, b.planOk = true → KeepsD R P b := by
  obtain ⟨h1, h2⟩ := firstChain_links K h
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact fun _ => keepsD_under rfl h1
  · obtain ⟨L, hL, hb⟩ := List.mem_flatMap.1 hb
    exact link_flat_ok (h2 L hL) b hb

/-- A cut of the flat list that is no longer than `frontOf c` holds entries of `frontOf c` alone. -/
theorem take_front {c : Chain S Cl} (h : c.front = []) {k : Nat} (hk : k ≤ (frontOf c).length) :
    ∀ b ∈ c.blocksInOrder.take k, b ∈ frontOf c := by
  intro b hb
  rw [flat_eq h, List.take_append_of_le_length hk] at hb
  exact List.mem_of_mem_take hb

theorem firstChain_take {H : Blocks S Cl} (K : BlocksKeep R P H) {links : List ModelPart}
    {several : Bool} {c : Chain S Cl} (h : firstChain H links several = some c) {k : Nat}
    (hk : k ≤ (frontOf c).length) : ∀ b ∈ c.blocksInOrder.take k, b.planOk = true → KeepsD R P b :=
  fun b hb => firstChain_front K h b (take_front (firstChain_noFront h) hk b hb)

end VerifiableInference.Desc.Keeps1

#print axioms VerifiableInference.Desc.Keeps1.link_flat_ok
#print axioms VerifiableInference.Desc.Keeps1.linkGuarded_keeps
#print axioms VerifiableInference.Desc.Keeps1.linkAt_keeps
#print axioms VerifiableInference.Desc.Keeps1.firstChain_front
#print axioms VerifiableInference.Desc.Keeps1.firstChain_take
