-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K7HearsOnce.lean: THE NEXT TOKEN's SUB-PROTOCOL HEARS ONCE
(Johnson/Desc/Sound/HearsOnce.lean: Block.HearsOnce), AT THE READER heardV OF THE HEARD REPLY AS A
TOKEN OF THE REFERENCE's VOCABULARY (Johnson/P5J/ReplyAtDriver.lean): where its decision accepts,
the reader answers nothing in front and something behind. Statements and proofs.

  heardV_none, heardV_some   the reader at a state with no reply; with a reply that is a token.
  joined_hearsOnce at "an entry that leaves what was put out, then the next token's": nothing in
                   front by Law/ReplyPins.lean's Came.reply_record; something behind by
                   Law/ReplyHears.lean's joined_hearsTok.
  h1Own_hearsOnce  at the sub-protocol that the lot of the proof file's IOP makes (ProofFile.h1Own: the
                   guarded quiet entry into the head's link, then the next token's): the entry
                   leaves all that was put out (Top/H0/Tw/K2C/FrontGroup.lean: headFrontQ_rest).

WHAT IT IS NOT. UNDER ONE NAMED PREMISE: hV: THE PLAN's VOCABULARY IS NO LARGER THAN THE
REFERENCE's. The sub-protocol tests what it hears to be a token below the plan's V; heardV answers
below the reference's alone: without hV the statement is not to be had. Nothing on which token is
heard. Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K6K7LotLeaves
import Johnson.Desc.Kinds.Law.ReplyHears
import Johnson.Desc.Sound.HearsOnce
import Johnson.P5J.ReplyAtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open Inst.Model (ppref)
open VerifiableInference.Desc (Block roundlessBlock)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (headFrontQ headFrontQ_rest)

/-- No reply: the reader answers nothing. -/
theorem heardV_none {s : S} (h : s.out.reply = none) : P5J.heardV (fun s : S => s) s = none := by
  show (s.out.reply.bind _).bind _ = none
  rw [h]
  rfl

/-- A token's number below the reference's vocabulary is heard: the reader answers. -/
theorem heardV_some {s : S} {y : Nat}
    (h : ((S.heard s).bind fun g =>
      if OnBytes.Model.ofNat g.c0.toNat == g then some g.c0.toNat else none) = some y)
    (hy : y < ppref.V) : (P5J.heardV (fun s : S => s) s).isSome = true := by
  have e : P5J.heardV (fun s : S => s) s =
      (some y).bind fun n => if h : n < ppref.V then some (⟨n, h⟩ : Fin ppref.V) else none := by
    rw [← h]
    rfl
  rw [e]
  show (if h : y < ppref.V then some (⟨y, h⟩ : Fin ppref.V) else none).isSome = true
  rw [dif_pos hy]
  rfl

/-- **At "an entry that leaves what was put out, then the next token's sub-protocol".** -/
theorem joined_hearsOnce (W : OnBytes.Model.Verify.Public) (l : Nat) (name : String)
    (front : Block S Unit) (hV : W.hS.V ≤ ppref.V)
    (hout : ∀ s rs gs s1, front.decide s rs gs = .ok s1 → s1.out = s.out) :
    (front.andThen name (Reply.blockOf W l)).HearsOnce (P5J.heardV fun s : S => s) := by
  intro s rs gs s' H
  obtain ⟨y, h1, h2⟩ := joined_hearsTok W l name front hV s rs gs s' H
  refine ⟨?_, heardV_some h1 h2⟩
  have h' : ((front.decide s (rs.take front.rounds.length) (gs.take front.openings)).bind
      fun s1 => (Reply.blockOf W l).decide s1 (rs.drop front.rounds.length)
        (gs.drop front.openings)) = .ok s' := H
  cases hp : front.decide s (rs.take front.rounds.length) (gs.take front.openings) with
  | error e => rw [hp] at h'; cases h'
  | ok s1 =>
    rw [hp] at h'
    obtain ⟨_, _, _, _, hn, _, _⟩ := Came.reply_record l W.hS.V h'
    refine heardV_none ?_
    rw [← hout _ _ _ _ hp]
    exact hn

/-- **At the sub-protocol that the lot makes.** -/
theorem h1Own_hearsOnce {G : ProofFile.Ground} (hV : G.W.hS.V ≤ ppref.V) {x : Block S Unit}
    (h : x ∈ ProofFile.h1Own G) : x.HearsOnce (P5J.heardV fun s : S => s) := by
  unfold ProofFile.h1Own at h
  obtain rfl := List.mem_singleton.1 h
  exact joined_hearsOnce G.W (G.built.size - 1) "H:1" _ hV fun s rs gs s1 h1 =>
    (headFrontQ_rest (h1Front G.W.H.tl _ _ _ _ _ s rs gs s1 h1)).2.2.2.2.2.1

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.h1Own_hearsOnce
