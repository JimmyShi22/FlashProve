-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/Fit/DriverFits.lean: THE DRIVER's CHAIN: every sub-protocol
in front of, and behind, the last link keeps R at rounds that fit, where the driver's sockets'
sub-protocols do.
  guarded_decidesF | guarded_wholeF · linkGuarded_keepsF · BlocksKeepF · blockAt_wholeF ·
  linkAt_keepsF · firstChain_linksF | _frontF | _backF   carried
CARRIED BY PROGRAM out of Johnson/Goal/Meaning/KeepsDriver.lean:
each declaration that is needed for the top and names Decides | Whole is copied under
its own name with a letter behind it (F | W), with Fits | WholeF in that word's place; its
docstrings are struck (they are that file's); where a proof opens the word itself it is turned by
hand. THE ORIGINAL IS IMPORTED AND NOT TURNED: what names neither word is called from it. IF THE
ORIGINAL ITSELF IS WIDENED INSTEAD, THIS FILE FALLS.
What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Meaning.KeepsDriver
import Johnson.Desc.Tidy.Fits
import Johnson.Desc.AtSeats.Fit.FoldFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open VerifiableInference.Desc
open VerifiableInference.Desc.First (Blocks ModelPart firstChain firstChainWithoutReplyGuard linkAt blockAt addresses
  closeAddresses mem_of_mapM)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl LinkKeeps)
open VerifiableInference.Desc.Keeps (WholeF Fits LinkKeepsF wholeF_of_whole fits_of_decides
    andThen_wholeF whole_sameF fits_planOk)

variable {T Cl : Type} {R : T → T → Prop}

theorem guarded_decidesF (same : T → T → Bool) (but : Place → Bool) {b : Block T Cl}
    (W : Fits R b) : Fits R (b.guarded same but) :=
  fun hp s rs gs s' hf h => W hp s rs gs s' hf (guarded_under same but b s _ gs s' h)

theorem guarded_wholeF (same : T → T → Bool) (but : Place → Bool) {b : Block T Cl}
    (W : WholeF R b) : WholeF R (b.guarded same but) := by
  refine ⟨guarded_decidesF same but W.1, fun c hc n s y h => ?_, fun c hc s s' h => ?_⟩
  · obtain ⟨c₀, h₀, -, k⟩ := guarded_claims_under same but b c hc
    exact W.2.1 c₀ h₀ n s y (k n s y h).1
  · obtain ⟨c₀, h₀, -, k⟩ := guarded_after_under same but b c hc
    exact W.2.2 c₀ h₀ s s' (k s s' h).1

theorem linkGuarded_keepsF (same : T → T → Bool) (but : Place → Bool) {L : Link T Cl}
    (h : LinkKeepsF R L) : LinkKeepsF R (L.guarded same but) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨guardedFn same h1, fun b hb => ?_, fun f hf => guarded_decidesF same but (h3 f hf),
    fun b hb => ?_, guardedFn same h5⟩
  · obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.1 hb
    exact guarded_wholeF same but (h2 b₀ hb₀)
  · obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.1 hb
    exact guarded_decidesF same but (h4 b₀ hb₀)

structure BlocksKeepF (R : T → T → Prop) (H : Blocks T Cl) : Prop where
  block : ∀ a b, a.link ≠ none → H.block a = some b → WholeF R b
  batch : ∀ a mk, a.link ≠ none → H.batch a = some mk → ∀ f, FnCl R f → Fits R (mk f)
  lay : ∀ l, Fn R (H.lay l)
  clear : ∀ l, Fn R (H.clear l)
  first : Fits R H.first

theorem blockAt_wholeF {H : Blocks T Cl} (K : BlocksKeepF R H) {a : Place} {b : Block T Cl}
    (ha : a.link ≠ none) (h : blockAt H a = some b) : WholeF R b := by
  unfold blockAt at h
  obtain ⟨b₀, e, rfl⟩ := Option.map_eq_some_iff.1 h
  exact K.block a b₀ ha e

theorem linkAt_keepsF {H : Blocks T Cl} (K : BlocksKeepF R H) {l : Nat} {sub : ModelPart} {L : Link T Cl}
    (h : linkAt H l sub = some L) : LinkKeepsF R L := by
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
    exact blockAt_wholeF K (Option.some_ne_none l) e
  · obtain ⟨a, ha, e⟩ := mem_of_mapM _ _ _ hc b hb'
    unfold closeAddresses at ha
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
    exact (blockAt_wholeF K (Option.some_ne_none l) e).1

theorem firstChain_linksF {H : Blocks T Cl} (K : BlocksKeepF R H) {links : List ModelPart}
    {several : Bool} {c : Chain T Cl} (h : firstChain H links several = some c) :
    Fits R c.first ∧ ∀ L ∈ c.links, LinkKeepsF R L := by
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
  refine ⟨guarded_decidesF _ _ K.first, fun L hL => ?_⟩
  obtain ⟨L₀, hL₀, rfl⟩ := List.mem_map.1 hL
  obtain ⟨x, -, e⟩ := mem_of_mapM _ _ _ hl L₀ hL₀
  exact linkGuarded_keepsF _ _ (linkAt_keepsF K e)

theorem firstChain_frontF (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c)
    {H : Blocks T Cl} (K : BlocksKeepF R H) {links : List ModelPart} {several : Bool} {c : Chain T Cl}
    (h : firstChain H links several = some c) : ∀ b ∈ frontOf c, Fits R b := by
  obtain ⟨h1, h2⟩ := firstChain_linksF K h
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact Keeps.fits_planOk _ h1
  · obtain ⟨L, hL, hb⟩ := List.mem_flatMap.1 hb
    exact Keeps.link_flat_keepsF R hr ht L (h2 L hL) b hb

theorem firstChain_backF {H : Blocks T Cl}
    (hb : ∀ a b, a.link = none → H.block a = some b → b.planOk = true → Fits R b)
    (hl : H.last.planOk = true → Fits R H.last)
    {links : List ModelPart} {several : Bool} {c : Chain T Cl}
    (h : firstChain H links several = some c) :
    ∀ b ∈ backOf c, b.planOk = true → Fits R b := by
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
    exact Keeps.fits_planOk _ (guarded_decidesF _ _ (hb _ b₂ rfl e₂ (Bool.and_eq_true _ _ ▸ hp).1))
  · obtain rfl := List.mem_singleton.1 hb'
    have hp' : H.last.planOk = true := (Bool.and_eq_true _ _ ▸ hp).1
    exact fun hq s rs gs s' hf k => guarded_decidesF H.same First.hearsReply
      (b := { H.last with place := ⟨1, none, back.length + 1, .frame⟩ })
      (fun _ s rs gs s' hf k => hl hp' hp' s rs gs s' hf k) hp' s rs gs s' hf k

end Meaning.K2
