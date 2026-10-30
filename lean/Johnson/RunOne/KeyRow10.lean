-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRow10.lean: A TRACER: THE KEY FILE's ROW 1.0 (the first sending: the index masks' message), THE FIRST OF THE ROWS WITH A DRAW, TAKEN FROM THE GENERAL ROW OF A SENDING (Johnson/Desc/Key/KeySendRow.lean: sendRow_keeps_new) TO THE TABLES' OWN LETTERS (on₁ | L₁ at the borders 0 | 1). EVERY UNPAID THING IS A NAMED PREMISE.
OBJECT: on₁ | L₁ at the borders 0 and 1 · USER: The35.r1_0 (Johnson/Top/Fire/Code/Row10.lean calls this file) · LETTERS: F Fr G at_ one R coll; the piece pc.
  open₁_send0     PROVED (by decide): open₁ 2 1 = open₁ 2 0 ++ [.pin 0, .srow 0]; no pin is open in front
  RecStays        A CONDITION ON THE READING G: the stored table's record is read off the instance alone
  back_send0      PROVED: the older items ride BACK across the block: «unmarked» (the first chain marks nothing) · pinT (RecStays; the cells stay) · inRange (it reads the witness alone)
  SendYes₀        A NAMED PREMISE: WHAT THE BLOCK's YES MUST GIVE OF THE RECORD: from the book-keeping and the promise's last letter at border 0, the format's test on the rounds, and New at the strings behind: the book-keeping and the last letter at border 1
  keeps_send0     PROVED FROM: Held · RecStays · hnew · SendYes₀ · good (GoodIn at THIS piece, from the tables' own promise at border 0) · tie (Sl ⟹ hasSmp ∧ NoColl at the seat at_ 0)
Nothing on soundness.
-/
import Johnson.Desc.Key.KeySendRow
import Johnson.RunOne.KeyTenKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Lookup)
open VerifiableInference.Desc.Key (Xi)
open _root_.Run.PQ (CK)
open _root_.Iop (Reduction)

variable {XI Cells M Smp Rec W : Type} {C : CK} (F : FileDescription XI) (Fr : Frame) (G : Reading (Xi × FirstState) Cells M Smp Rec) (at_ : Where)
  (one : OneTime) (R : KRead Cells M) (coll : Strs → Rec → Prop)

theorem open₁_send0 : open₁ 2 1 = open₁ 2 0 ++ [.pin 0, .srow 0] := by decide
theorem pinned_send0 : pinned (open₁ 2 0 ++ [.pin 0, .srow 0]) = pinned (open₁ 2 0) ++ [0] := by decide
theorem pinned_front0 : pinned (open₁ 2 0) = [] := by decide

/-- The stored table's record is read off the instance alone. -/
def RecStays : Prop := ∀ (p : Xi) (s s' : FirstState), G.recOf (p, s') = G.recOf (p, s)

/-- **The older items ride back.** -/
theorem back_send0 (hR : RecStays G) (p : Xi) (s s' : FirstState) (y y' : Strs) (w : Wit Cells Unit M) (Hy : StrsStay F at_ (open₁ 2 0) y y')
    (h : relAt F G at_ (meaning₁At one R) (open₁ 2 0 ++ [.pin 0, .srow 0]) (p, s') y' w) : relAt F G at_ (meaning₁At one R) (open₁ 2 0) (p, s) y w := by
  intro i hi
  have H := h i (List.mem_append_left _ hi)
  have hi' : i = .unmarked ∨ i = .pinT ∨ i = .inRange 0 ∨ i = .inRange 1 := by
    have e : open₁ 2 0 = [.unmarked, .pinT, .inRange 0, .inRange 1] := by decide
    rw [e] at hi
    simpa using hi
  rcases hi' with rfl | rfl | rfl | rfl
  · exact rfl
  · obtain ⟨r, h1, h2⟩ := H
    exact ⟨r, (hR p s s') ▸ h1, Hy.cell ▸ h2⟩
  · exact H
  · exact H

/-- **What the first sending's yes must give of the record.** New: a fact of the piece on the strings behind. -/
def SendYes₀ (New : Strs → Prop) (b : Block FirstState Claim) : Prop :=
  ∀ (p : Xi) (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (y y' : Strs),
    roundsFit b.rounds rs = true → b.decide s (rs.map noDigest) gs = .ok s' → StrsStay F at_ (open₁ 2 0) y y' → New y' →
    shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 0 s = true → free₁ F G at_ one R coll 0 (p, s) y →
    shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 1 s' = true ∧ free₁ F G at_ one R coll 1 (p, s') y'

/-- The row, where the number of lookups is given. -/
theorem keeps_send0_two (pc : Piece C Fr (Xi × FirstState) Claim W) (b : Block FirstState Claim) (hheld : Held Fr pc b) (hrounds : pc.b.rounds = b.rounds) (hn : n₁ one = 2)
    (hR : RecStays G) (New : Strs → Prop)
    (hnew : ∀ a τ a', on₁ F Fr G at_ one R coll 0 a → pc.ior.red.out a τ = some a' → New (strsOf Fr a'.2))
    (yes : SendYes₀ F G at_ one R coll New b)
    (Sl : (Xi × FirstState) × Fr.E.Str → Prop) (Ra Rb : (Xi × FirstState) × Fr.E.Str → W → Prop)
    (good : pc.GoodIn (on₁ F Fr G at_ one R coll 0) Sl Ra Rb)
    (tie : ∀ a', Sl a' → hasSmp G (at_ 0).1 (at_ 0).2 a'.1 = true ∧ NoColl F G (at_ 0).1 (at_ 0).2 a'.1 (strsOf Fr a'.2)) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 0) (on₁ F Fr G at_ one R coll 1) (L₁ F Fr G at_ one R 0) (L₁ F Fr G at_ one R 1) pc.err := by
  have e0 : on₁ F Fr G at_ one R coll 0 = onB F Fr G at_ (meaning₁At one R) (shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 0) (free₁ F G at_ one R coll 0) (open₁ 2 0) := by
    unfold on₁ onB
    rw [hn]
  rw [e0] at hnew good
  have key := sendRow_keeps_new F Fr G at_ (meaning₁At one R) pc (shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 0) (shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 1)
    (free₁ F G at_ one R coll 0) (free₁ F G at_ one R coll 1) (open₁ 2 0) [.pin 0, .srow 0] 0 pinned_send0 (fun j hj => by rw [pinned_front0] at hj; cases hj) New hnew
    (fun a rs gs a' y y' hf hd Hy hN ho => by
      obtain ⟨e, hb⟩ := hheld a _ gs a' hd
      refine ⟨fun _ => rfl, fun hu => ?_⟩
      obtain ⟨h1, -, h3, -⟩ := ho.resolve_left (fun hx => hx hu)
      obtain ⟨p, s⟩ := a
      obtain ⟨p', s'⟩ := a'
      have e' : p' = p := e
      subst e'
      obtain ⟨g1, g2⟩ := yes p' s s' rs gs y y' (hrounds ▸ hf) hb Hy hN h1 h3
      exact ⟨g1, fun j hj => (by rw [pinned_front0] at hj; cases hj), g2⟩)
    (fun a rs gs a' y y' w hf hd Hy _ hw => by
      obtain ⟨e, -⟩ := hheld a _ gs a' hd
      obtain ⟨p, s⟩ := a
      obtain ⟨p', s'⟩ := a'
      have e' : p' = p := e
      subst e'
      exact back_send0 F G at_ one R hR p' s s' y y' w Hy hw)
    Sl Ra Rb good tie
  unfold on₁ L₁ R₁
  rw [hn, open₁_send0]
  exact key

/-- **ROW 1.0.** The number of lookups is no premise: the promise in front holds it (on₁_two). -/
theorem keeps_send0 (pc : Piece C Fr (Xi × FirstState) Claim W) (b : Block FirstState Claim) (hheld : Held Fr pc b) (hrounds : pc.b.rounds = b.rounds)
    (hR : RecStays G) (New : Strs → Prop)
    (hnew : ∀ a τ a', on₁ F Fr G at_ one R coll 0 a → pc.ior.red.out a τ = some a' → New (strsOf Fr a'.2))
    (yes : SendYes₀ F G at_ one R coll New b)
    (Sl : (Xi × FirstState) × Fr.E.Str → Prop) (Ra Rb : (Xi × FirstState) × Fr.E.Str → W → Prop)
    (good : pc.GoodIn (on₁ F Fr G at_ one R coll 0) Sl Ra Rb)
    (tie : ∀ a', Sl a' → hasSmp G (at_ 0).1 (at_ 0).2 a'.1 = true ∧ NoColl F G (at_ 0).1 (at_ 0).2 a'.1 (strsOf Fr a'.2)) :
    pc.ior.red.Keeps (on₁ F Fr G at_ one R coll 0) (on₁ F Fr G at_ one R coll 1) (L₁ F Fr G at_ one R 0) (L₁ F Fr G at_ one R 1) pc.err := by
  intro a ha
  exact keeps_send0_two F Fr G at_ one R coll pc b hheld hrounds (on₁_two F Fr G at_ one R coll 0 a ha) hR New hnew yes Sl Ra Rb good tie a ha

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.back_send0
#print axioms Johnson.RunOne.KeyRows1.keeps_send0
