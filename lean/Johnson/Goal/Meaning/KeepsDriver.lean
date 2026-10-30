-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/KeepsDriver.lean: a relation that the blocks handed to the first chain's driver
keep is kept by every link of the chain that the driver makes, and by its first block: GENERAL IN
THE RECORD, THE TYPE OF A CLAIM AND THE RELATION.

The driver (Johnson/Desc/First/Driver/Chain.lean: firstChain) asks its record Blocks for a block at
each address, stamps the address into it, makes the links, and lays the guard of
Johnson/Desc/SeatGuard.lean over the whole.
  mem_of_mapM_ok: a tool: the members of what a List.mapM over Except returns.
  guarded_whole, guarded_decides: the guard keeps what the block keeps: by the library's
    guarded_under, guarded_claims_under, guarded_after_under
    (Johnson/Desc/Sound/SeatGuardLaws.lean).
  linkGuarded_keeps: so LinkKeeps R (Johnson/Desc/FoldKeeps.lean) goes over to the guarded link.
  linkAt_keeps: LinkKeeps R of the link that linkAt makes.
  firstChain_links: firstChain H links several = some c → Decides R c.first ∧
    ∀ L ∈ c.links, LinkKeeps R L.
  frontOf, firstChain_front: so every block of frontOf c := c.first :: c.links.flatMap Link.blocksInOrder is
    Decides R.
  firstChain_back, firstChain_flat: the like of the blocks behind the last link and the seal, for
    whoever pays these too, EACH UNDER ITS OWN TEST ON THE PLAN (b.planOk = true): then every block
    of c.blocksInOrder that passes its test on the plan is Decides R.
  firstChain_noFront, backOf, flat_eq: the driver's chain has c.front = [], and there c.blocksInOrder =
    frontOf c ++ backOf c: so frontOf c is the flat list in front of the blocks behind the last
    link.
WHAT IS ASKED OF H: Whole R of H.block's blocks AT THE ADDRESSES INSIDE A LINK ALONE; of H.batch's
makers there: for every function of claims that keeps R the block keeps R; Fn R of H.lay l and
H.clear l; Decides R of H.first. NOTHING IS ASKED of the blocks behind the last link or of the seal.
OBJECT: firstChain's value, at any H. USER: Johnson/IMR/KeepsSeat.lean (at ProofFile's fill).
-/
import Johnson.Desc.FoldKeeps
import Johnson.Desc.First.Driver.PlacesLaw
import Johnson.Desc.Sound.SeatGuardLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open VerifiableInference.Desc
open VerifiableInference.Desc.First (Blocks ModelPart firstChain firstChainWithoutReplyGuard linkAt blockAt addresses
  closeAddresses mem_of_mapM)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl LinkKeeps)

variable {T Cl : Type} {R : T → T → Prop}

/-- The members of what a List.mapM over Except returns. (The library's laws of this kind are over
Option.) -/
theorem mem_of_mapM_ok {α β : Type} (g : α → Except String β) : ∀ (l : List α) (ys : List β),
    l.mapM g = .ok ys → ∀ y ∈ ys, ∃ x ∈ l, g x = .ok y
  | [], ys, h, y, hy => by
    rw [List.mapM_nil] at h
    cases h
    cases hy
  | a :: l, ys, h, y, hy => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := Keeps.ebind_ok h
    obtain ⟨bs, hbs, h⟩ := Keeps.ebind_ok h
    cases h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨a, List.mem_cons_self, hb⟩
    · obtain ⟨x, hx, e⟩ := mem_of_mapM_ok g l bs hbs y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, e⟩

theorem guarded_decides (same : T → T → Bool) (but : Place → Bool) {b : Block T Cl}
    (W : Decides R b) : Decides R (b.guarded same but) :=
  fun s rs gs s' h => W s rs gs s' (guarded_under same but b s rs gs s' h)

theorem guarded_whole (same : T → T → Bool) (but : Place → Bool) {b : Block T Cl}
    (W : Whole R b) : Whole R (b.guarded same but) := by
  refine ⟨guarded_decides same but W.1, fun c hc n s y h => ?_, fun c hc s s' h => ?_⟩
  · obtain ⟨c₀, h₀, -, k⟩ := guarded_claims_under same but b c hc
    exact W.2.1 c₀ h₀ n s y (k n s y h).1
  · obtain ⟨c₀, h₀, -, k⟩ := guarded_after_under same but b c hc
    exact W.2.2 c₀ h₀ s s' (k s s' h).1

theorem guardedFn (same : T → T → Bool) {f : T → Except String T} (W : Fn R f) :
    Fn R fun t => (f t).bind (seatSame same t) := fun t s' h => by
  obtain ⟨s, hs, e⟩ := Keeps.ebind_ok h
  rw [(seatSame_ok e).1]
  exact W t s hs

theorem linkGuarded_keeps (same : T → T → Bool) (but : Place → Bool) {L : Link T Cl}
    (h : LinkKeeps R L) : LinkKeeps R (L.guarded same but) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨guardedFn same h1, fun b hb => ?_, fun f hf => guarded_decides same but (h3 f hf),
    fun b hb => ?_, guardedFn same h5⟩
  · obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.1 hb
    exact guarded_whole same but (h2 b₀ hb₀)
  · obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.1 hb
    exact guarded_decides same but (h4 b₀ hb₀)

/-- What is asked of the driver's record. -/
structure BlocksKeep (R : T → T → Prop) (H : Blocks T Cl) : Prop where
  block : ∀ a b, a.link ≠ none → H.block a = some b → Whole R b
  batch : ∀ a mk, a.link ≠ none → H.batch a = some mk → ∀ f, FnCl R f → Decides R (mk f)
  lay : ∀ l, Fn R (H.lay l)
  clear : ∀ l, Fn R (H.clear l)
  first : Decides R H.first

theorem blockAt_whole {H : Blocks T Cl} (K : BlocksKeep R H) {a : Place} {b : Block T Cl}
    (ha : a.link ≠ none) (h : blockAt H a = some b) : Whole R b := by
  unfold blockAt at h
  obtain ⟨b₀, e, rfl⟩ := Option.map_eq_some_iff.1 h
  exact K.block a b₀ ha e

theorem linkAt_keeps {H : Blocks T Cl} (K : BlocksKeep R H) {l : Nat} {sub : ModelPart} {L : Link T Cl}
    (h : linkAt H l sub = some L) : LinkKeeps R L := by
  unfold linkAt at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨hear, hh, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨batch, hb, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨close, hc, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  refine ⟨K.lay l, fun b hb' => ?_, fun f hf => K.batch _ _ (Option.some_ne_none l) hb f hf,
    fun b hb' => ?_, K.clear l⟩
  · obtain ⟨a, ha, e⟩ := mem_of_mapM _ _ _ hh b hb'
    unfold addresses at ha
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
    exact blockAt_whole K (Option.some_ne_none l) e
  · obtain ⟨a, ha, e⟩ := mem_of_mapM _ _ _ hc b hb'
    unfold closeAddresses at ha
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
    exact (blockAt_whole K (Option.some_ne_none l) e).1

/-- **The driver's chain: its first block and every link.** -/
theorem firstChain_links {H : Blocks T Cl} (K : BlocksKeep R H) {links : List ModelPart}
    {several : Bool} {c : Chain T Cl} (h : firstChain H links several = some c) :
    Decides R c.first ∧ ∀ L ∈ c.links, LinkKeeps R L := by
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
  refine ⟨guarded_decides _ _ K.first, fun L hL => ?_⟩
  obtain ⟨L₀, hL₀, rfl⟩ := List.mem_map.1 hL
  obtain ⟨x, -, e⟩ := mem_of_mapM _ _ _ hl L₀ hL₀
  exact linkGuarded_keeps _ _ (linkAt_keeps K e)

/-- A chain's first block, as Chain.blocksInOrder lays it, and its links' flat lists. IT LEAVES c.front OUT:
where c.front = [] it is the flat list in front of the blocks behind the last link (flat_eq). -/
def frontOf (c : Chain T Cl) : List (Block T Cl) :=
  { c.first with planOk := c.first.planOk && c.first.hasNoClaimsAndNothingAfter } :: c.links.flatMap Link.blocksInOrder

theorem firstChain_front (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c)
    {H : Blocks T Cl} (K : BlocksKeep R H) {links : List ModelPart} {several : Bool} {c : Chain T Cl}
    (h : firstChain H links several = some c) : ∀ b ∈ frontOf c, Decides R b := by
  obtain ⟨h1, h2⟩ := firstChain_links K h
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact h1
  · obtain ⟨L, hL, hb⟩ := List.mem_flatMap.1 hb
    exact Keeps.link_flat_keeps R hr ht L (h2 L hL) b hb

/-- The driver lays no block between the front and the first link. -/
theorem firstChain_noFront {H : Blocks T Cl} {links : List ModelPart} {several : Bool} {c : Chain T Cl}
    (h : firstChain H links several = some c) : c.front = [] := by
  unfold firstChain at h
  obtain ⟨c₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold firstChainWithoutReplyGuard at h0
  simp only [Option.bind_eq_bind, Option.pure_def] at h0
  split at h0
  · cases h0
  obtain ⟨_, _, h0⟩ := Option.bind_eq_some_iff.1 h0
  obtain ⟨ls, -, h0⟩ := Option.bind_eq_some_iff.1 h0
  obtain ⟨back, -, h0⟩ := Option.bind_eq_some_iff.1 h0
  cases h0
  rfl

/-- The flat list behind the last link: the blocks there, and the seal. -/
def backOf (c : Chain T Cl) : List (Block T Cl) :=
  c.back.map (fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }) ++
    [{ c.last with planOk := c.last.planOk && c.last.hasNoClaimsAndNothingAfter }]

theorem flat_eq {c : Chain T Cl} (h : c.front = []) : c.blocksInOrder = frontOf c ++ backOf c := by
  unfold Chain.blocksInOrder frontOf backOf
  rw [h]
  simp only [List.map_nil, List.nil_append, List.cons_append, List.append_assoc]

/-- **The driver's chain: the blocks behind the last link, and the seal.** -/
theorem firstChain_back {H : Blocks T Cl}
    (hb : ∀ a b, a.link = none → H.block a = some b → b.planOk = true → Decides R b)
    (hl : H.last.planOk = true → Decides R H.last)
    {links : List ModelPart} {several : Bool} {c : Chain T Cl}
    (h : firstChain H links several = some c) :
    ∀ b ∈ backOf c, b.planOk = true → Decides R b := by
  unfold firstChain at h
  obtain ⟨c₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold firstChainWithoutReplyGuard at h0
  simp only [Option.bind_eq_bind, Option.pure_def] at h0
  split at h0
  · cases h0
  obtain ⟨_, _, h0⟩ := Option.bind_eq_some_iff.1 h0
  obtain ⟨ls, -, h0⟩ := Option.bind_eq_some_iff.1 h0
  obtain ⟨back, hk, h0⟩ := Option.bind_eq_some_iff.1 h0
  cases h0
  intro b hb' hp
  rcases List.mem_append.1 hb' with hb' | hb'
  · obtain ⟨b₁, h₁, rfl⟩ := List.mem_map.1 hb'
    obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 h₁
    obtain ⟨a, ha, e⟩ := mem_of_mapM _ _ _ hk b₀ h₀
    unfold addresses at ha
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
    unfold blockAt at e
    obtain ⟨b₂, e₂, rfl⟩ := Option.map_eq_some_iff.1 e
    exact guarded_decides _ _ (hb _ b₂ rfl e₂ (Bool.and_eq_true _ _ ▸ hp).1)
  · obtain rfl := List.mem_singleton.1 hb'
    have hp' : H.last.planOk = true := (Bool.and_eq_true _ _ ▸ hp).1
    exact fun s rs gs s' k => guarded_decides H.same First.hearsReply
      (b := { H.last with place := ⟨1, none, back.length + 1, .frame⟩ })
      (fun s rs gs s' k => hl hp' s rs gs s' k) s rs gs s' k

/-- **The driver's chain, whole.** -/
theorem firstChain_flat (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c)
    {H : Blocks T Cl} (K : BlocksKeep R H)
    (hb : ∀ a b, a.link = none → H.block a = some b → b.planOk = true → Decides R b)
    (hl : H.last.planOk = true → Decides R H.last)
    {links : List ModelPart} {several : Bool} {c : Chain T Cl}
    (h : firstChain H links several = some c) : ∀ b ∈ c.blocksInOrder, b.planOk = true → Decides R b := by
  intro b hb' hp
  rw [flat_eq (firstChain_noFront h)] at hb'
  rcases List.mem_append.1 hb' with k | k
  · exact firstChain_front hr ht K h b k
  · exact firstChain_back hb hl h b k hp

#print axioms guarded_whole
#print axioms linkAt_keeps
#print axioms firstChain_links
#print axioms firstChain_front
#print axioms flat_eq
#print axioms firstChain_flat

end Meaning.K2
