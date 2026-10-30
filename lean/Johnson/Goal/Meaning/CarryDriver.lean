-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/CarryDriver.lean: a PROPERTY OF BLOCKS that the blocks handed to the first
chain's driver have is had by every block of every link of the chain that the driver makes, and by
its first block: GENERAL IN THE RECORD, THE TYPE OF A CLAIM AND THE PROPERTY.

Why. Johnson/Goal/Meaning/KeepsDriver.lean walks the driver's text for ONE RELATION ON RECORDS
that every block's decision keeps (Keeps.Decides R). A sentence that names EACH BLOCK's OWN DECLARED
ROUNDS (RootsStep, Johnson/Desc/K12/Law/RootsFold.lean: a yes adds to the count of roots just what
the block's rounds declare) is no such relation. Here the same walk stands once more, general in a
property Pr of blocks; Decides R is its first instance (carried_decides; wholeP_decides is Iff.rfl).
KeepsDriver.lean IS NO COROLLARY OF THIS FILE: THE WALK STANDS TWICE.

  UnderP c b: c has b's declared rounds and says yes only where b says the same yes
      (Block.UnderR, Johnson/Desc/Sound/SeatGuardChain.lean), and c's test on the plan holds b's;
          ALSO: c tells the oracle messages that b tells (c.oracles =
          b.oracles).
  Carried Pr R₀: WHAT IS ASKED OF THE PROPERTY: it goes along UnderP (under); a block without a
      round, which tells no oracle message, whose decision keeps R₀ has it (quiet); two blocks as
      one have it (andThen); R₀ is
      reflexive and transitive. R₀: a relation on records, for what a link RUNS and does not decide:
      the runs of claims, which the batching is handed, and the runs behind the batching.
  WholeP Pr R₀ b: Pr of b; R₀ of b's runs of claims and of its runs behind the batching.
  guarded_underP, stamp_underP, bare_underP: the guard, the place's stamp and "&& hasNoClaimsAndNothingAfter" are UnderP.
      guarded_wholeP.
  LinkCarry, claims_carry, behind_carry, link_flat_carry: every block of a link's flat list has Pr.
      linkGuarded_carry.
  BlocksCarry, blockAt_wholeP, linkAt_carry, firstChain_frontP: **firstChain H links several = some
      c → ∀ b ∈ frontOf c, Pr b.**
CALLED, NOT TYPED: guarded_underR, claimsTrace, afterSteps (they ask the runs alone) ·
guarded_claims_under, guarded_after_under, claimsIn_of_claimsInBy · frontOf, guardedFn
(KeepsDriver.lean).
OBJECT: firstChain's value, at any H.
USER: Johnson/IMR/CarrySeat.lean.
LETTERS: T, Cl, Pr, R₀, H: free.

Compiled with the whole library.
Limits. Nothing on the blocks behind the last link or on the seal. Nothing on soundness.

-/
import Johnson.Goal.Meaning.KeepsDriver
import Johnson.Desc.Sound.SeatGuardChain
import Johnson.Desc.Sound.FoldStepsProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open VerifiableInference.Desc
open VerifiableInference.Desc.First (Blocks ModelPart firstChain firstChainWithoutReplyGuard linkAt blockAt addresses
  closeAddresses mem_of_mapM)
open VerifiableInference.Desc.Keeps (Decides Fn FnCl)
open Meaning.K2 (frontOf)

variable {T Cl : Type}

/-! ## 1 The letters -/

/-- c has b's declared rounds and says yes only where b says the same yes; and c's test on the plan
holds b's. -/
def UnderP (c b : Block T Cl) : Prop :=
  c.UnderR b ∧ (c.planOk = true → b.planOk = true) ∧ c.oracles = b.oracles

theorem UnderP.refl (b : Block T Cl) : UnderP b b := ⟨⟨rfl, fun _ _ _ _ h => h⟩, id, rfl⟩

theorem UnderP.trans {a b c : Block T Cl} (h₁ : UnderP a b) (h₂ : UnderP b c) : UnderP a c :=
  ⟨h₁.1.trans h₂.1, fun h => h₂.2.1 (h₁.2.1 h), h₁.2.2.trans h₂.2.2⟩

/-- **A property of blocks that a seat's wrappers carry**, with a relation on records for what is
run and not decided. -/
structure Carried (Pr : Block T Cl → Prop) (R₀ : T → T → Prop) : Prop where
  refl : ∀ s, R₀ s s
  trans : ∀ a b c, R₀ a b → R₀ b c → R₀ a c
  under : ∀ {c b : Block T Cl}, UnderP c b → Pr b → Pr c
  quiet : ∀ {b : Block T Cl}, b.rounds = [] → b.oracles.flatten = [] → Decides R₀ b → Pr b
  andThen : ∀ {n : String} {p q : Block T Cl}, Pr p → Pr q → Pr (p.andThen n q)

/-- Pr of the block's decision; R₀ of its runs of claims and of its runs behind the batching. -/
def WholeP (Pr : Block T Cl → Prop) (R₀ : T → T → Prop) (b : Block T Cl) : Prop :=
  Pr b ∧ (∀ c ∈ b.claims, ∀ n, FnCl R₀ (c.2 n)) ∧ ∀ c ∈ b.after, Fn R₀ c.2

variable {Pr : Block T Cl → Prop} {R₀ : T → T → Prop}

theorem Carried.pre (C : Carried Pr R₀) : Pre R₀ := ⟨C.refl, C.trans⟩

/-! ## 2 The wrappers -/

theorem guarded_underP (same : T → T → Bool) (but : Place → Bool) (b : Block T Cl) :
    UnderP (b.guarded same but) b := ⟨guarded_underR same but b, id, rfl⟩

theorem stamp_underP (b : Block T Cl) (a : Place) : UnderP { b with place := a } b :=
  ⟨⟨rfl, fun _ _ _ _ h => h⟩, id, rfl⟩

theorem bare_underP (b : Block T Cl) : UnderP { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } b :=
  ⟨⟨rfl, fun _ _ _ _ h => h⟩, fun h => (Bool.and_eq_true _ _ ▸ h).1, rfl⟩

theorem guarded_wholeP (C : Carried Pr R₀) (same : T → T → Bool) (but : Place → Bool)
    {b : Block T Cl} (W : WholeP Pr R₀ b) : WholeP Pr R₀ (b.guarded same but) := by
  refine ⟨C.under (guarded_underP same but b) W.1, fun c hc n s y h => ?_, fun c hc s s' h => ?_⟩
  · obtain ⟨c₀, h₀, -, k⟩ := guarded_claims_under same but b c hc
    exact W.2.1 c₀ h₀ n s y (k n s y h).1
  · obtain ⟨c₀, h₀, -, k⟩ := guarded_after_under same but b c hc
    exact W.2.2 c₀ h₀ s s' (k s s' h).1

/-! ## 3 A link -/

/-- What is asked of a link. -/
structure LinkCarry (Pr : Block T Cl → Prop) (R₀ : T → T → Prop) (L : Link T Cl) : Prop where
  lay : Fn R₀ L.lay
  hear : ∀ b ∈ L.hear, WholeP Pr R₀ b
  batch : ∀ f, FnCl R₀ f → Pr (L.batch f)
  close : ∀ b ∈ L.close, Pr b
  clear : Fn R₀ L.clear

theorem claims_carry (C : Carried Pr R₀) {bs : List (Block T Cl)}
    (hb : ∀ b ∈ bs, WholeP Pr R₀ b) (each : Nat × String → List Cl → T → Except String Unit)
    (order : List (Nat × String)) : FnCl R₀ (claimsInBy each bs order) := fun s y h =>
  (claimsTrace T Cl R₀ C.pre bs order s y.2 y.1
    (fun b hb' c hc n s cl s' k => (hb b hb').2.1 c hc n s (cl, s') k)
    (claimsIn_of_claimsInBy each bs order s y h)).1

theorem behind_carry (C : Carried Pr R₀) {L : Link T Cl} (hb : ∀ b ∈ L.hear, WholeP Pr R₀ b) :
    Fn R₀ L.runBehind := fun s s' h => by
  unfold Link.runBehind at h
  split at h
  · exact afterSteps T Cl R₀ C.pre L.hear L.orderAfter s s'
      (fun b hb' c hc s s' k => (hb b hb').2.2 c hc s s' k) h
  · cases h

/-- **Every block of a link's flat list has the property.** -/
theorem link_flat_carry (C : Carried Pr R₀) (L : Link T Cl) (h : LinkCarry Pr R₀ L) :
    ∀ b ∈ L.blocksInOrder, Pr b := by
  intro b hb
  unfold Link.blocksInOrder at hb
  rcases List.mem_append.1 hb with hb | hb
  · rcases List.mem_append.1 hb with hb | hb
    · rcases List.mem_append.1 hb with hb | hb
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact C.quiet rfl rfl fun s _ _ s' k => h.lay s s' k
        · exact (h.hear b hb).1
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact h.batch _ (claims_carry C h.hear _ _)
        · obtain rfl := List.mem_singleton.1 hb
          exact C.quiet rfl rfl fun s _ _ s' k => behind_carry C h.hear s s' k
    · exact h.close b hb
  · obtain rfl := List.mem_singleton.1 hb
    exact C.quiet rfl rfl fun s _ _ s' k => h.clear s s' k

theorem linkGuarded_carry (C : Carried Pr R₀) (same : T → T → Bool) (but : Place → Bool)
    {L : Link T Cl} (h : LinkCarry Pr R₀ L) : LinkCarry Pr R₀ (L.guarded same but) where
  lay := Meaning.K2.guardedFn same h.lay
  hear b hb := by
    obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.1 hb
    exact guarded_wholeP C same but (h.hear b₀ hb₀)
  batch f hf := C.under (guarded_underP same but _) (h.batch f hf)
  close b hb := by
    obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.1 hb
    exact C.under (guarded_underP same but _) (h.close b₀ hb₀)
  clear := Meaning.K2.guardedFn same h.clear

/-! ## 4 The driver -/

/-- What is asked of the driver's record. -/
structure BlocksCarry (Pr : Block T Cl → Prop) (R₀ : T → T → Prop) (H : Blocks T Cl) : Prop where
  block : ∀ a b, a.link ≠ none → H.block a = some b → WholeP Pr R₀ b
  batch : ∀ a mk, a.link ≠ none → H.batch a = some mk → ∀ f, FnCl R₀ f → Pr (mk f)
  lay : ∀ l, Fn R₀ (H.lay l)
  clear : ∀ l, Fn R₀ (H.clear l)
  first : Pr H.first

theorem blockAt_wholeP (C : Carried Pr R₀) {H : Blocks T Cl} (K : BlocksCarry Pr R₀ H) {a : Place}
    {b : Block T Cl} (ha : a.link ≠ none) (h : blockAt H a = some b) : WholeP Pr R₀ b := by
  unfold blockAt at h
  obtain ⟨b₀, e, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := K.block a b₀ ha e
  exact ⟨C.under (stamp_underP b₀ a) W.1, W.2.1, W.2.2⟩

theorem linkAt_carry (C : Carried Pr R₀) {H : Blocks T Cl} (K : BlocksCarry Pr R₀ H) {l : Nat}
    {sub : ModelPart} {L : Link T Cl} (h : linkAt H l sub = some L) : LinkCarry Pr R₀ L := by
  unfold linkAt at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨hear, hh, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨batch, hb, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨close, hc, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  refine ⟨K.lay l, fun b hb' => ?_,
    fun f hf => C.under (stamp_underP _ _) (K.batch _ _ (Option.some_ne_none l) hb f hf),
    fun b hb' => ?_, K.clear l⟩
  · obtain ⟨a, ha, e⟩ := mem_of_mapM _ _ _ hh b hb'
    unfold addresses at ha
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
    exact blockAt_wholeP C K (Option.some_ne_none l) e
  · obtain ⟨a, ha, e⟩ := mem_of_mapM _ _ _ hc b hb'
    unfold closeAddresses at ha
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
    exact (blockAt_wholeP C K (Option.some_ne_none l) e).1

/-- **The driver's chain: every block in front of the blocks behind the last link.** -/
theorem firstChain_frontP (C : Carried Pr R₀) {H : Blocks T Cl} (K : BlocksCarry Pr R₀ H)
    {links : List ModelPart} {several : Bool} {c : Chain T Cl}
    (h : firstChain H links several = some c) : ∀ b ∈ frontOf c, Pr b := by
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
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact C.under (((bare_underP _).trans (guarded_underP _ _ _)).trans (stamp_underP _ _)) K.first
  · obtain ⟨L, hL, hb⟩ := List.mem_flatMap.1 hb
    obtain ⟨L₀, hL₀, rfl⟩ := List.mem_map.1 hL
    obtain ⟨x, -, e⟩ := mem_of_mapM _ _ _ hl L₀ hL₀
    exact link_flat_carry C _ (linkGuarded_carry C _ _ (linkAt_carry C K e)) b hb

/-! ## 5 The first instance: a relation that every decision keeps -/

theorem carried_decides {R : T → T → Prop} (hr : ∀ s, R s s)
    (ht : ∀ a b c, R a b → R b c → R a c) : Carried (Cl := Cl) (Decides R) R where
  refl := hr
  trans := ht
  under u W := fun s rs gs s' h => W s rs gs s' (u.1.2 s rs gs s' h)
  quiet _ _ W := W
  andThen W₁ W₂ := fun s rs gs s' h => by
    obtain ⟨m, h1, h2⟩ := Keeps.ebind_ok h
    exact ht _ _ _ (W₁ _ _ _ _ h1) (W₂ _ _ _ _ h2)

theorem wholeP_decides {R : T → T → Prop} (b : Block T Cl) :
    WholeP (Decides R) R b ↔ Keeps.Whole R b := Iff.rfl

#print axioms link_flat_carry
#print axioms firstChain_frontP
#print axioms carried_decides

end Meaning.Carry
