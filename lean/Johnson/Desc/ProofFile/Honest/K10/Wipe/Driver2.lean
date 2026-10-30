-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/Driver2.lean: the closing of a segment (K10): if the blocks that are handed to
the first chain's driver have like outcomes at two states that are one under w, then so has every block that the driver
lays in front of the blocks behind the last link. General in the state's type T, in the type of a claim and in w : T →
T. One structure of type Prop; the rest are theorems.

  seatSame_alike2, decides_guarded2   the guard of Johnson/Desc/SeatGuard.lean over a block of which Decides2 alone is
                     known; its test must give one answer at like states
  linkGuarded_keeps2   LinkKeeps2 w goes over to the guarded link
  BlocksKeep2 w H      what is asked of the driver's record H
  blockAt_whole2, linkAt_keeps2   so of the block and the link that the driver makes
  firstChain_links2    firstChain H links several = some c gives Decides2 w c.first and LinkKeeps2 w of every link of c
  firstChain_front2    so every block of Meaning.K2.frontOf c is Decides2 w

What is proved, by what. It follows Johnson/Goal/Meaning/KeepsDriver.lean, lemma for lemma, over the laws of
Wipe/Alike.lean, Wipe/Wrap2.lean and Wipe/Link2.lean. Three clauses of BlocksKeep2 have no like there: a link's test
behind each run, its tests behind the adding, and the guard's own test. In a law on one state these return no state and
could be dropped; here they decide whether a block returns.

Limits. BlocksKeep2 is shown of no record here. Nothing is asked, and nothing shown, of the blocks behind the last link
or of the seal. No property of the protocol is claimed: nothing is said on its soundness, completeness, binding or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.Alike
import Johnson.Desc.ProofFile.Honest.K10.Wipe.Wrap2
import Johnson.Desc.ProofFile.Honest.K10.Wipe.Link2
import Johnson.Goal.Meaning.KeepsDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10

open VerifiableInference.Desc (Block Link Chain Place seatSame)
open VerifiableInference.Desc.First (Blocks ModelPart firstChain firstChainWithoutReplyGuard linkAt blockAt addresses closeAddresses
  mem_of_mapM)

variable {T Cl : Type} {w : T → T}

/-- The guard's test has like outcomes at like states, where its question has one answer there. -/
theorem seatSame_alike2 {same : T → T → Bool}
    (hr : ∀ t t' s s', w t = w t' → w s = w s' → same t s = same t' s') {t t' s s' : T}
    (ht : w t = w t') (hs : w s = w s') : AlikeE w (seatSame same t s) (seatSame same t' s') := by
  unfold seatSame
  rw [hr t t' s s' ht hs]
  by_cases h : same t' s' = true
  · rw [if_pos h, if_pos h]
    exact AlikeE.ok hs
  · rw [if_neg h, if_neg h]
    exact AlikeE.error _

/-- The guard over a block keeps Decides2. -/
theorem decides_guarded2 (same : T → T → Bool) (but : Place → Bool)
    (hr : ∀ t t' s s', w t = w t' → w s = w s' → same t s = same t' s') {b : Block T Cl}
    (W : Decides2 w b) : Decides2 w (b.guarded same but) := by
  intro s s' rs gs gs' hs hg
  show AlikeE w (if but b.place then b.decide s rs gs else (b.decide s rs gs).bind (seatSame same s))
    (if but b.place then b.decide s' rs gs' else (b.decide s' rs gs').bind (seatSame same s'))
  by_cases h : but b.place = true
  · rw [if_pos h, if_pos h]
    exact W s s' rs gs gs' hs hg
  · rw [if_neg h, if_neg h]
    exact AlikeE.bind (W s s' rs gs gs' hs hg) fun a a' ha => seatSame_alike2 hr hs ha

/-- The guard over a link keeps LinkKeeps2. -/
theorem linkGuarded_keeps2 (same : T → T → Bool) (but : Place → Bool)
    (hr : ∀ t t' s s', w t = w t' → w s = w s' → same t s = same t' s') {L : Link T Cl}
    (h : LinkKeeps2 w L) : LinkKeeps2 w (L.guarded same but) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨guardedFn2 same hr h1, fun b hb => ?_, h3, h4,
    fun f hf => decides_guarded2 same but hr (h5 f hf), fun b hb => ?_, guardedFn2 same hr h7⟩
  · obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.1 hb
    exact guarded_whole2 same but hr (h2 b₀ hb₀)
  · obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.1 hb
    exact decides_guarded2 same but hr (h6 b₀ hb₀)

/-- What is asked of the driver's record. -/
structure BlocksKeep2 (w : T → T) (H : Blocks T Cl) : Prop where
  block : ∀ a b, a.link ≠ none → H.block a = some b → Whole2 w b
  batch : ∀ a mk, a.link ≠ none → H.batch a = some mk → ∀ f, FnCl2 w f → Decides2 w (mk f)
  lay : ∀ l, Fn2 w (H.lay l)
  clear : ∀ l, Fn2 w (H.clear l)
  first : Decides2 w H.first
  /-- a link's test behind each run of claims -/
  each : ∀ l o cl, Test2 w (H.each l o cl)
  /-- a link's tests behind the adding -/
  tests : ∀ l, Test2 w (H.tests l)
  /-- the guard's question has one answer at like states -/
  same : ∀ t t' s s', w t = w t' → w s = w s' → H.same t s = H.same t' s'

/-- The block that the driver lays at an address inside a link. -/
theorem blockAt_whole2 {H : Blocks T Cl} (K : BlocksKeep2 w H) {a : Place} {b : Block T Cl}
    (ha : a.link ≠ none) (h : blockAt H a = some b) : Whole2 w b := by
  unfold blockAt at h
  obtain ⟨b₀, e, rfl⟩ := Option.map_eq_some_iff.1 h
  exact K.block a b₀ ha e

/-- The link that the driver makes. -/
theorem linkAt_keeps2 {H : Blocks T Cl} (K : BlocksKeep2 w H) {l : Nat} {sub : ModelPart} {L : Link T Cl}
    (h : linkAt H l sub = some L) : LinkKeeps2 w L := by
  unfold linkAt at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨hear, hh, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨batch, hb, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨close, hc, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  refine ⟨K.lay l, fun b hb' => ?_, K.each l, K.tests l,
    fun f hf => K.batch _ _ (Option.some_ne_none l) hb f hf, fun b hb' => ?_, K.clear l⟩
  · obtain ⟨a, ha, e⟩ := mem_of_mapM _ _ _ hh b hb'
    unfold addresses at ha
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
    exact blockAt_whole2 K (Option.some_ne_none l) e
  · obtain ⟨a, ha, e⟩ := mem_of_mapM _ _ _ hc b hb'
    unfold closeAddresses at ha
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
    exact (blockAt_whole2 K (Option.some_ne_none l) e).1

/-- **The driver's chain: its first block and every link.** -/
theorem firstChain_links2 {H : Blocks T Cl} (K : BlocksKeep2 w H) {links : List ModelPart} {several : Bool}
    {c : Chain T Cl} (h : firstChain H links several = some c) :
    Decides2 w c.first ∧ ∀ L ∈ c.links, LinkKeeps2 w L := by
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
  refine ⟨decides_guarded2 _ _ K.same K.first, fun L hL => ?_⟩
  obtain ⟨L₀, hL₀, rfl⟩ := List.mem_map.1 hL
  obtain ⟨x, -, e⟩ := mem_of_mapM _ _ _ hl L₀ hL₀
  exact linkGuarded_keeps2 _ _ K.same (linkAt_keeps2 K e)

/-- **The driver's chain: every block in front of the blocks behind the last link.** -/
theorem firstChain_front2 {H : Blocks T Cl} (K : BlocksKeep2 w H) {links : List ModelPart} {several : Bool}
    {c : Chain T Cl} (h : firstChain H links several = some c) :
    ∀ b ∈ Meaning.K2.frontOf c, Decides2 w b := by
  obtain ⟨h1, h2⟩ := firstChain_links2 K h
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact h1
  · obtain ⟨L, hL, hb⟩ := List.mem_flatMap.1 hb
    exact link_flat_keeps2 L (h2 L hL) b hb

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.seatSame_alike2
#print axioms ProofFile.Honest.K10.decides_guarded2
#print axioms ProofFile.Honest.K10.linkGuarded_keeps2
#print axioms ProofFile.Honest.K10.BlocksKeep2
#print axioms ProofFile.Honest.K10.blockAt_whole2
#print axioms ProofFile.Honest.K10.linkAt_keeps2
#print axioms ProofFile.Honest.K10.firstChain_links2
#print axioms ProofFile.Honest.K10.firstChain_front2
