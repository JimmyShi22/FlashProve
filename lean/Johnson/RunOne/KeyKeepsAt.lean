-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyKeepsAt.lean: THEOREMS. **THE KEY FILE's OWN BLOCKS OF ITS FIRST CHAIN WRITE THE STATEMENT THROUGH THE GROUND's PLAIN FUNCTIONS ALONE: so they keep every relation R on statements that these functions keep
(GroundKeeps R: Johnson/Desc/GroundKeeps.lean)**: among them «a statement only grows», «no new mark», «the codes are the same». CARRIED from a frozen KeyKeeps.lean (a file that is not in this library; not the library's Johnson/Desc/Key/KeyKeeps.lean) to the library's names (Johnson/Desc/Key/One | Link | Chain1.lean), by a program and then by hand where a
knob has fallen (the hook · keep · tab · due · strict). NEW: K3's own block is PAID, by the library's blockG_whole (Johnson/Goal/Meaning/RecK3More.lean): the key's seat's two layings leave the statement.
OBJECT. Key.sendingSeat · sendIndexMasks · sendOwnMessage · openRangesGroup · layPile · batchTableRows · sendW · firstChainEnd · caller · layer · layRows · lookupLink · firstChain. USER. KeyCodesStay.lean. LETTERS. R with GroundKeeps R; one · D · told · set · N.
  seat_keeps · openRanges_keeps · layPile_keeps · idx_keeps | msg_keeps | batt_keeps | w_keeps | end_keeps · caller_keeps · layer_keeps · layRows_keeps
  k3_whole         K3's own block at a lookup keeps By R st₁, whole, for every reflexive R
  link_keeps       a lookup's link
  chain1_keeps     **chain 1 keeps R, GIVEN ONE PREMISE: the proximity test's seat at the ranges does (Decides).**
What is not claimed. The premise. That a block ACCEPTS rightly: «keeps R» speaks of what a block writes. NOTHING ON ROWS. Nothing on soundness.

-/
import Johnson.RunOne.KeySendIs
import Johnson.Desc.Key.Chain1
import Johnson.Desc.K1.Keeps
import Johnson.Desc.ChainEndExact
import Johnson.Goal.Meaning.RecK3More

set_option autoImplicit false

namespace Johnson.RunOne.KeyKeeps

open OnBytes OnBytes.Params VerifiableInference.Desc.Key
open VerifiableInference.Desc (Block Chain Link named need)
open VerifiableInference.Desc.Ground (GroundKeeps By)
open VerifiableInference.Desc.Keeps (Decides Fn FnCl Whole LinkKeeps ChainKeeps andThen_decides named_ok emap_ok)
open VerifiableInference.Desc.ChainEnd (bind_ok)

variable {β Cl : Type} {R : Statement → Statement → Prop}

theorem by_trans (H : GroundKeeps R) : ∀ a b c : ChainState β, By R st₁ a b → By R st₁ b c → By R st₁ a c := fun _ _ _ h k => H.trans h k

theorem quietAt_keeps {name : String} {place : VerifiableInference.Desc.Place} {f : ChainState β → Except String (ChainState β)} (hf : Fn (By R st₁) f) :
    Decides (By R st₁) (quietAt (Cl := Cl) name place f) := fun s _ _ s' h => hf s s' h

/-- **K1's seat.** -/
theorem seat_keeps (H : GroundKeeps R) (name : String) (P : VerifiableInference.Desc.K1.Par) : Decides (By R st₁) (sendingSeat (β := β) (Cl := Cl) name P) := by
  intro s rs gs s' h
  obtain ⟨y, hy, he⟩ := emap_ok h
  have := VerifiableInference.Desc.K1.Rel.sendOwn_keeps (Cl := Cl) H P _ rs gs y hy
  rw [← he]
  exact this

theorem openRanges_keeps (H : GroundKeeps R) (one : OneTime) : Fn (By R (st₁ (β := β))) (openRangesGroup one) := by
  intro s s' h
  unfold openRangesGroup at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨g, hg, h⟩ := bind_ok h
  obtain ⟨d, hd, h⟩ := bind_ok h
  rw [← Except.ok.inj h]
  obtain ⟨n, d₀⟩ := g
  exact H.trans (H.newGroup _ _ _ _ _ (named_ok hg)) (H.join _ _ _ _ _ (named_ok hd))

theorem layPile_keeps (H : GroundKeeps R) (keysOf : β → List (List Lkp.Keys)) (one : OneTime) : Fn (By R st₁) (layPile keysOf one) := by
  intro s s' h
  unfold layPile at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  rw [← Except.ok.inj h]
  exact H.refl _

theorem idx_keeps (H : GroundKeeps R) (one : OneTime) (N : Pieces) (groups : List (List Nat)) : Decides (By R st₁) (sendIndexMasks (β := β) (Cl := Cl) one N groups) :=
  andThen_decides _ (by_trans H) _ _ _ (seat_keeps H _ _) (quietAt_keeps fun s s' h => by
    obtain ⟨_, _, h⟩ := bind_ok h
    rw [← Except.ok.inj h]
    exact H.refl _)

theorem msg_keeps (H : GroundKeeps R) (one : OneTime) (N : Pieces) (groups : List (List Nat)) : Decides (By R st₁) (sendOwnMessage (β := β) (Cl := Cl) one N groups) :=
  andThen_decides _ (by_trans H) _ _ _ (seat_keeps H _ _) (quietAt_keeps (openRanges_keeps H one))

theorem batt_keeps (H : GroundKeeps R) (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (N : Pieces) (sent : Nat) :
    Decides (By R st₁) (batchTableRows (Cl := Cl) keysOf one N sent) :=
  andThen_decides _ (by_trans H) _ _ _
    (andThen_decides _ (by_trans H) _ _ _
      (andThen_decides _ (by_trans H) _ _ _ (quietAt_keeps (layPile_keeps H keysOf one)) (VerifiableInference.Desc.K13.frontB_keeps H.quiet _ st₁ lens_lensSt _))
      (VerifiableInference.Desc.K13.battB_keeps H.quiet _ st₁ lens_lensSt _))
    (VerifiableInference.Desc.K13.quietB_keeps H.quiet _ st₁ lens_lensSt _)

theorem w_keeps (H : GroundKeeps R) (one : OneTime) (N : Pieces) (sent : Nat) (groups : List (List Nat)) : ∀ b ∈ (sendW (β := β) (Cl := Cl) one N sent groups).toList, Decides (By R st₁) b := by
  intro b hb
  unfold sendW at hb
  cases hm : linMessageW one.lin with
  | none => rw [hm] at hb; cases hb
  | some msg =>
    rw [hm] at hb
    simp only [Option.map_some, Option.toList_some, List.mem_singleton] at hb
    rw [hb]
    exact andThen_decides _ (by_trans H) _ _ _
      (andThen_decides _ (by_trans H) _ _ _
        (andThen_decides _ (by_trans H) _ _ _
          (quietAt_keeps fun s s' h => by
            obtain ⟨_, _, h⟩ := bind_ok h
            rw [← Except.ok.inj h]
            exact H.refl _)
          (seat_keeps H _ _))
        (quietAt_keeps fun s s' h => by
          rw [← Except.ok.inj h]
          exact H.refl _))
      (VerifiableInference.Desc.K13.rowsB_keeps H.quiet _ st₁ lens_lensSt _)

theorem end_keeps (H : GroundKeeps R) (N : Pieces) (inFront : List Fmt.DeclaredRound) : Decides (By R st₁) (firstChainEnd (β := β) (Cl := Cl) N inFront) := by
  intro s rs gs s' h
  obtain ⟨_, _, he⟩ := emap_ok h
  rw [← he]
  exact H.refl _

/-! ## The links -/

theorem caller_keeps (H : GroundKeeps R) (one : OneTime) (i : Nat) (x : Lookup) : Decides (By R st₁) (caller one i x) :=
  quietAt_keeps fun s s' h => by
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨o, ho, h⟩ := bind_ok h
    obtain ⟨k, hk, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    rw [← Except.ok.inj h]
    obtain ⟨l₁, d₁⟩ := o
    obtain ⟨l₂, d₂⟩ := k
    exact H.trans (H.takeMasks _ _ _ _ _ (named_ok ho)) (H.takeMasks _ _ _ _ _ (named_ok hk))

theorem layer_keeps (one : OneTime) (set : Setting) (i : Nat) (x : Lookup)
    (f : FirstState → Except String (List Claim × FirstState)) (hf : FnCl (By R st₁) f) : Decides (By R st₁) (layer one set i x f) :=
  quietAt_keeps fun s s' h => by
    obtain ⟨y, hy, h⟩ := bind_ok h
    obtain ⟨cls, t⟩ := y
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    rw [← Except.ok.inj h]
    exact hf s _ hy

theorem layRows_keeps (H : GroundKeeps R) (one : OneTime) : Decides (By R st₁) (layRows one) :=
  quietAt_keeps fun s s' h => by
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨d, hd, h⟩ := bind_ok h
    rw [← Except.ok.inj h]
    exact H.addRows _ _ _ _ (named_ok hd)

/-- **K3's own block at a lookup**: the key's seat's two layings turn the lookups' record alone. -/
theorem k3_whole (hr : ∀ T, R T T) (set : Setting) (i : Nat) (x : Lookup) :
    Whole (By R st₁) (VerifiableInference.Desc.K3.lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set i x)) :=
  Meaning.K2.blockG_whole (By R st₁) (fun s => hr _) lookupSeat (fun s _ _ => hr _) (fun s _ => hr _) _ _ _ _

/-- A lookup's link keeps R. -/
theorem link_keeps (H : GroundKeeps R) (one : OneTime) (set : Setting) (i : Nat) (x : Lookup) : LinkKeeps (By R st₁) (lookupLink one set i x) := by
  refine ⟨fun s s' h => ?_, fun b hb => ?_, fun f hf => layer_keeps one set i x f hf, fun b hb => (by cases hb), fun s s' h => ?_⟩
  · obtain ⟨_, _, h⟩ := bind_ok h
    rw [← Except.ok.inj h]
    exact H.refl _
  · rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨caller_keeps H one i x, fun c hc => (by cases hc), fun c hc => (by cases hc)⟩
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact k3_whole H.refl set i x
      · cases hb
  · rw [← Except.ok.inj h]
    exact H.refl _

/-- **Chain 1 keeps R**, given the proximity test's seat at the ranges. -/
theorem chain1_keeps (H : GroundKeeps R) (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root) (set : Setting) (N : H2U.PlaceNums)
    (h12 : Decides (By R st₁) (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim)) : ChainKeeps (By R st₁) (firstChain one D told set N) := by
  refine ⟨idx_keeps H _ _ _, fun b hb => ?_, fun L hL => ?_, fun b hb => ?_, end_keeps H _ _⟩
  · rcases List.mem_cons.1 hb with rfl | hb
    · exact msg_keeps H _ _ _
    · cases hb
  · obtain ⟨x, _, rfl⟩ := List.mem_map.1 hL
    exact link_keeps H one set x.2 x.1
  · rcases List.mem_append.1 hb with hb | hb
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact layRows_keeps H one
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact h12
        · rcases List.mem_cons.1 hb with rfl | hb
          · exact batt_keeps H _ _ _ _
          · cases hb
    · exact w_keeps H _ _ _ _ b hb

end Johnson.RunOne.KeyKeeps

#print axioms Johnson.RunOne.KeyKeeps.seat_keeps
#print axioms Johnson.RunOne.KeyKeeps.batt_keeps
#print axioms Johnson.RunOne.KeyKeeps.w_keeps
#print axioms Johnson.RunOne.KeyKeeps.k3_whole
#print axioms Johnson.RunOne.KeyKeeps.link_keeps
#print axioms Johnson.RunOne.KeyKeeps.chain1_keeps
