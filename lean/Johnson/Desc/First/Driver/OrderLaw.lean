-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Driver/OrderLaw.lean: the law on the order of a segment's named lists, at the
driver's own makers: where the test on the plan says yes, every list that the protocol's order names
is stated by the hearing block of its number.

Why. A `linkAt` (Johnson/Desc/First/Driver/Chain.lean) that laid the protocol's two
orders filtered by what the segment's blocks state would cut away without a refusal a list that the
order names and no block states: Block.lean's test `namesOk` would be handed the filtered order, so
its clause "the order names no other" could not fail. linkAt lays the two
orders uncut, and that same clause refuses such a segment on the plan. This file proves that it
does. Definitions, statements and proofs.
What stands beneath. What Block.lean's tests on an order catch, at any order (orderOk_covers,
orderAfterOk_covers), and what that means for `stated` and `cutAway` (cutAway_nil_iff,
stated_eq_iff, orderOk_nothing_cut, orderAfterOk_nothing_cut), is proved in
Johnson/Desc/First/Link/Law/Order.lean and OrderCut.lean. This file holds
only what speaks of linkAt and firstChain.
What it costs. A segment one of whose hearing blocks is a stand-in, or states fewer lists than the
table names, fails its test on the plan.
Main names:
  `whole_of_nothing_cut`: where nothing of the stretches in a row is cut away, every stretch is
    stated whole (so `wholeOrNone` says yes, by its first arm).
  `linkAt_order`: a segment's two orders are `orderOf sub` and `orderAfterOf sub`, uncut.
  `Link.framePlanOk`: the test on the plan of the first block that `Link.blocksInOrder` lays.
  `covered_of_orders`, `link_covered`: where that test says yes at a segment that bears the
    protocol's two orders (one that linkAt has made is such): every entry of orderOf sub and of
    orderAfterOf sub is stated by the hearing block of its number; nothing is cut away; every
    stretch is whole.
  `frame_of_blocksOk`: Block.lean's test `blocksOk` on a chain's flat list holds that test of every
    segment.
  `chain_covered`: where blocksOk says yes of the flat list of the chain that `firstChain` makes,
    every segment of it is one that linkAt has made of a member of the list of parts, behind the
    guard, and is covered.
  `getElem_of_mapM`, `chain_links_at`: the segment number i of that chain is the one that linkAt
    makes, at the number i, of the member number i of the list of parts, behind the guard.
  `chain_covered_at`: so, where blocksOk says yes, the segment number i bears the two orders of the
    sort at the number i, uncut, and is covered; nothing is cut away; every stretch is whole.
Limits. The law speaks of names: that a block has a list of the name, not what the list holds, nor
that two lists do not add the same claims. That `orderOf` and `orderAfterOf` are the protocol's
order is not shown here: they are a table typed in Chain.lean. Block.lean's tests do not know that
table: with two entries of an order swapped orderOk still says yes; linkAt_order alone fixes the
order. Nothing is said of the blocks after the last segment. That a run goes by `Link.order` at all,
and not by a table of a seat's own, is not said here. No soundness is claimed, and nothing is said
on hiding.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.First.Link.Law.OrderCut
import Johnson.Desc.First.Driver.PlacesLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc
open VerifiableInference.Desc.Shape (orderOk_covers orderAfterOk_covers cutAway_nil_iff
  stated_eq_iff orderOk_nothing_cut orderAfterOk_nothing_cut)

/-- Where nothing of the stretches in a row is cut away, every stretch is whole. -/
theorem whole_of_nothing_cut {B : Type} (names : B → List String) (bs : List B)
    (cuts : List (List (Nat × String))) (h : cutAway names bs cuts.flatten = []) :
    ∀ cut ∈ cuts, stated names bs cut = cut ∧ wholeOrNone names bs cut = true := by
  intro cut hc
  have h' : cutAway names bs cut = [] := by
    rw [cutAway_nil_iff] at h ⊢
    exact fun o ho => h o (List.mem_flatten.2 ⟨cut, hc, ho⟩)
  have e := (stated_eq_iff names bs cut).2 h'
  refine ⟨e, ?_⟩
  unfold wholeOrNone
  rw [e]
  simp

variable {S Cl : Type}

/-- A segment's two orders are the protocol's, uncut. -/
theorem linkAt_order (H : Blocks S Cl) (l : Nat) (sub : ModelPart) (L : Link S Cl)
    (h : linkAt H l sub = some L) : L.order = orderOf sub ∧ L.orderAfter = orderAfterOf sub := by
  unfold linkAt at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨hear, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨batch, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨close, _, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  exact ⟨rfl, rfl⟩

/-- The test on the plan of a segment's first block. -/
def Link.framePlanOk (L : Link S Cl) : Bool := (L.blocksInOrder.head?.map (·.planOk)).getD false

/-- **The law at a segment that bears the protocol's two orders.** Where the test on the plan of the
segment's first block says yes, every list that the protocol's order names at this sort of segment
is stated by the hearing block of its number, nothing is cut away, and every stretch is whole. -/
theorem covered_of_orders (sub : ModelPart) (L : Link S Cl) (e1 : L.order = orderOf sub)
    (e2 : L.orderAfter = orderAfterOf sub) (hp : Link.framePlanOk L = true) :
    (∀ o ∈ orderOf sub, ∃ b, L.hear[o.1]? = some b ∧ o.2 ∈ b.claims.map (·.1)) ∧
      (∀ o ∈ orderAfterOf sub, ∃ b, L.hear[o.1]? = some b ∧ o.2 ∈ b.after.map (·.1)) ∧
      cutAway (·.claims.map (·.1)) L.hear (orderOf sub) = [] ∧
      cutAway (·.after.map (·.1)) L.hear (orderAfterOf sub) = [] ∧
      ∀ cut ∈ orderCuts sub, wholeOrNone (·.claims.map (·.1)) L.hear cut = true := by
  have hp' : (orderOk L.hear L.order && orderAfterOk L.hear L.orderAfter &&
      L.close.all Block.hasNoClaimsAndNothingAfter && (L.batch (claimsInBy L.each L.hear L.order)).hasNoClaimsAndNothingAfter) = true := hp
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, e1, e2] at hp'
  have k1 := orderOk_nothing_cut hp'.1.1.1
  exact ⟨orderOk_covers hp'.1.1.1, orderAfterOk_covers hp'.1.1.2, k1,
    orderAfterOk_nothing_cut hp'.1.1.2,
    fun cut hc => (whole_of_nothing_cut _ _ (orderCuts sub) k1 cut hc).2⟩

/-- The law at a segment that linkAt has made. -/
theorem link_covered (H : Blocks S Cl) (l : Nat) (sub : ModelPart) (L : Link S Cl)
    (h : linkAt H l sub = some L) (hp : Link.framePlanOk L = true) :
    (∀ o ∈ orderOf sub, ∃ b, L.hear[o.1]? = some b ∧ o.2 ∈ b.claims.map (·.1)) ∧
      (∀ o ∈ orderAfterOf sub, ∃ b, L.hear[o.1]? = some b ∧ o.2 ∈ b.after.map (·.1)) ∧
      cutAway (·.claims.map (·.1)) L.hear (orderOf sub) = [] ∧
      cutAway (·.after.map (·.1)) L.hear (orderAfterOf sub) = [] ∧
      ∀ cut ∈ orderCuts sub, wholeOrNone (·.claims.map (·.1)) L.hear cut = true :=
  covered_of_orders sub L (linkAt_order H l sub L h).1 (linkAt_order H l sub L h).2 hp

/-- Block.lean's test on the plan of all blocks of a chain's flat list holds the test of every
segment's first block. -/
theorem frame_of_blocksOk (c : Chain S Cl) (h : blocksOk c.blocksInOrder = true) :
    ∀ L ∈ c.links, Link.framePlanOk L = true := by
  intro L hL
  unfold blocksOk at h
  rw [List.all_eq_true] at h
  obtain ⟨b0, t, e⟩ : ∃ b0 t, L.blocksInOrder = b0 :: t := ⟨_, _, rfl⟩
  have hm : b0 ∈ c.blocksInOrder := by
    unfold Chain.blocksInOrder
    refine List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.2 ⟨L, hL, ?_⟩))))
    rw [e]
    exact List.mem_cons_self
  have hb := h b0 hm
  rw [Bool.and_eq_true] at hb
  unfold Link.framePlanOk
  rw [e]
  exact hb.1

/-- **The law at the first chain.** Where Block.lean's test on the plan of all blocks says yes of
the chain that `firstChain` makes, every segment of it is one that `linkAt` has made of a member of
the list of parts, behind the guard, and at every segment every list that the protocol's order names
is stated by the hearing block of its number. -/
theorem chain_covered (H : Blocks S Cl) (links : List ModelPart) (several : Bool) (c : Chain S Cl)
    (h : firstChain H links several = some c) (hp : blocksOk c.blocksInOrder = true) :
    ∀ L ∈ c.links, ∃ x ∈ links.zipIdx, ∃ L0, linkAt H x.2 x.1 = some L0 ∧
      L = L0.guarded H.same hearsReply ∧
      (∀ o ∈ orderOf x.1, ∃ b, L.hear[o.1]? = some b ∧ o.2 ∈ b.claims.map (·.1)) ∧
      (∀ o ∈ orderAfterOf x.1, ∃ b, L.hear[o.1]? = some b ∧ o.2 ∈ b.after.map (·.1)) := by
  intro L hL
  have hf := frame_of_blocksOk c hp L hL
  unfold firstChain at h
  obtain ⟨c0, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨L0, hL0, rfl⟩ := List.mem_map.1 (show L ∈ c0.links.map (Link.guarded H.same hearsReply)
    from hL)
  unfold firstChainWithoutReplyGuard at h0
  simp only [Option.bind_eq_bind, Option.pure_def] at h0
  split at h0
  · cases h0
  obtain ⟨_, _, h0⟩ := Option.bind_eq_some_iff.1 h0
  obtain ⟨ls, hl, h0⟩ := Option.bind_eq_some_iff.1 h0
  obtain ⟨back, _, h0⟩ := Option.bind_eq_some_iff.1 h0
  cases h0
  obtain ⟨x, hx, e⟩ := mem_of_mapM (fun x : ModelPart × Nat => linkAt H x.2 x.1) _ _ hl L0 hL0
  obtain ⟨c1, c2, _⟩ := covered_of_orders x.1 (L0.guarded H.same hearsReply)
    (linkAt_order H x.2 x.1 L0 e).1 (linkAt_order H x.2 x.1 L0 e).2 hf
  exact ⟨x, hx, L0, e, rfl, c1, c2⟩

/-- The value number i comes from the member number i. -/
theorem getElem_of_mapM {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β),
    l.mapM f = some r → ∀ (i : Nat) (b : β), r[i]? = some b → ∃ a, l[i]? = some a ∧ f a = some b
  | [], r, h => by
    rw [List.mapM_nil] at h
    cases h
    intro i b hb
    simp at hb
  | a :: l, r, h => by
    obtain ⟨b0, bs, hb0, hbs, rfl⟩ := mapM_cons_some f a l r h
    intro i b hb
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero] at hb
      cases hb
      exact ⟨a, List.getElem?_cons_zero, hb0⟩
    | succ i =>
      rw [List.getElem?_cons_succ] at hb
      obtain ⟨a', ha', e⟩ := getElem_of_mapM f l bs hbs i b hb
      exact ⟨a', by rw [List.getElem?_cons_succ]; exact ha', e⟩

/-- **The segment number i of the first chain** is the one that `linkAt` makes, at the number i, of
the member number i of the list of parts, behind the guard. -/
theorem chain_links_at (H : Blocks S Cl) (links : List ModelPart) (several : Bool) (c : Chain S Cl)
    (h : firstChain H links several = some c) (i : Nat) (L : Link S Cl)
    (hL : c.links[i]? = some L) :
    ∃ sub L0, links[i]? = some sub ∧ linkAt H i sub = some L0 ∧
      L = L0.guarded H.same hearsReply := by
  unfold firstChain at h
  obtain ⟨c0, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have hL' : (c0.links.map (Link.guarded H.same hearsReply))[i]? = some L := hL
  rw [List.getElem?_map] at hL'
  obtain ⟨L0, hL0, rfl⟩ := Option.map_eq_some_iff.1 hL'
  unfold firstChainWithoutReplyGuard at h0
  simp only [Option.bind_eq_bind, Option.pure_def] at h0
  split at h0
  · cases h0
  obtain ⟨_, _, h0⟩ := Option.bind_eq_some_iff.1 h0
  obtain ⟨ls, hl, h0⟩ := Option.bind_eq_some_iff.1 h0
  obtain ⟨back, _, h0⟩ := Option.bind_eq_some_iff.1 h0
  cases h0
  obtain ⟨x, hx, e⟩ := getElem_of_mapM (fun x : ModelPart × Nat => linkAt H x.2 x.1) _ _ hl i L0 hL0
  rw [List.getElem?_zipIdx] at hx
  obtain ⟨sub, hs, rfl⟩ := Option.map_eq_some_iff.1 hx
  refine ⟨sub, L0, hs, ?_, rfl⟩
  simpa using e

/-- **The law at the segment number i.** Where Block.lean's test on the plan of all blocks says yes
of the chain that `firstChain` makes: the segment number i bears the protocol's two orders, uncut,
of the sort that the list of parts has at the number i; every list that they name is stated by the
hearing block of its number; nothing is cut away; every stretch is whole. -/
theorem chain_covered_at (H : Blocks S Cl) (links : List ModelPart) (several : Bool) (c : Chain S Cl)
    (h : firstChain H links several = some c) (hp : blocksOk c.blocksInOrder = true) (i : Nat)
    (L : Link S Cl) (hL : c.links[i]? = some L) :
    ∃ sub, links[i]? = some sub ∧ L.order = orderOf sub ∧ L.orderAfter = orderAfterOf sub ∧
      (∀ o ∈ orderOf sub, ∃ b, L.hear[o.1]? = some b ∧ o.2 ∈ b.claims.map (·.1)) ∧
      (∀ o ∈ orderAfterOf sub, ∃ b, L.hear[o.1]? = some b ∧ o.2 ∈ b.after.map (·.1)) ∧
      cutAway (·.claims.map (·.1)) L.hear (orderOf sub) = [] ∧
      cutAway (·.after.map (·.1)) L.hear (orderAfterOf sub) = [] ∧
      ∀ cut ∈ orderCuts sub, wholeOrNone (·.claims.map (·.1)) L.hear cut = true := by
  have hf := frame_of_blocksOk c hp L (List.mem_of_getElem? hL)
  obtain ⟨sub, L0, hs, e, rfl⟩ := chain_links_at H links several c h i L hL
  exact ⟨sub, hs, (linkAt_order H i sub L0 e).1, (linkAt_order H i sub L0 e).2,
    covered_of_orders sub (L0.guarded H.same hearsReply) (linkAt_order H i sub L0 e).1
      (linkAt_order H i sub L0 e).2 hf⟩

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.whole_of_nothing_cut
#print axioms VerifiableInference.Desc.First.linkAt_order
#print axioms VerifiableInference.Desc.First.covered_of_orders
#print axioms VerifiableInference.Desc.First.link_covered
#print axioms VerifiableInference.Desc.First.frame_of_blocksOk
#print axioms VerifiableInference.Desc.First.chain_covered
#print axioms VerifiableInference.Desc.First.chain_links_at
#print axioms VerifiableInference.Desc.First.chain_covered_at
