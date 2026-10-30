-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Honest/Law/K7PubAt.lean: CONDITIONAL: THE PUBLIC ITEMS' TEST BEHIND THE NEXT
TOKEN's ROW (kind K7; border 338 of the full chain), AT THE COMPOSED MEANING, AT TWO STATES OF THE
VERIFIER BETWEEN WHICH THE SEATED CONSTANT SAYS YES. One statement with its proof. Over the library
alone.

  k7_pub_at   CONDITIONAL: the test at the border in front, at the state x ⊢ the test behind the
              row, at the state t

IT IS THE LIBRARY's pub_mgAll (Johnson/Desc/Kinds/Law/K7AtMgAll.lean) WITH ANOTHER FIRST LINE.
pub_mgAll speaks of a piece's accept at a transcript, and its proof's first line turns that accept
into "the seated constant says yes between the two states"; from there on the proof here is its
proof, line for line. A caller that has a member's step and no piece cannot call pub_mgAll. Whoever
keeps that file may state it in this form and derive the other: then this file is to strike.

The premises. hmore: the composed meaning's list of extra public tests is the closed one · hW: the
two public records have one head's shape · hfront: the front's yes is the entry of the head's link ·
hy: the seated constant (the front, then the next token's block) says yes at x and yields t · h: the
test in front.

Called: place_leaves, place_index, tokenSmall_mgAll and three closed facts on the table at that
border, pubFront338, pubStep338, pubTied339, which Lean's kernel has decided by evaluation (all in
K7AtMgAll.lean).

Limits. Conditional. None of the premises is shown here. It speaks of one Bool of the table's
promise. At the full chain's written lists alone. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.Kinds.Law.K7AtMgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace H2K7

open OnBytes.Model (HTailF2)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc (Block Wit)
open VerifiableInference.Desc.First (S Meaning flatPlacesOf openSets start pubHeld pubSets pubStep
  pubRowM stepOpen rowOf)
open VerifiableInference.Desc.K13 (indexIsC indexThereC)
open VerifiableInference.Desc.First.K2 (headFrontQ)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head.Law

variable {Xi P Tok : Type} {rows cols nR : Nat} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT))

/-- **THE PUBLIC ITEMS' TEST BEHIND THE NEXT TOKEN's ROW, AT THE COMPOSED MEANING, AT TWO STATES.**
CONDITIONAL: the list of extra public tests is the closed one; one head's shape; the front's yes is
the entry of the head's link; the seated constant says yes at x and yields t; the test in front. -/
theorem k7_pub_at (hmore : (mgAll D Mg).more = mgMore) (W : OnBytes.Model.Verify.Public)
    (hW : Wp.hS = W.hS) (l : Nat) (name : String) (front : Block S Unit) (tl : HTailF2)
    (hfront : ∀ x rs gs x1, front.decide x rs gs = .ok x1 → headFrontQ tl x = .ok x1) (z : P)
    {x t : S} {rs gs}
    (hy : (front.andThen name (Reply.blockOf W l)).decide x rs gs = .ok t)
    (h : pubHeld (mgAll D Mg)
      ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[338]?.getD [])
      ((pubSets (mgAll D Mg).more linksFull (flatPlacesOf linksFull true))[338]?.getD [])
      (z, x) = true) :
    pubHeld (mgAll D Mg)
      (stepOpen ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[338]?.getD [])
        (rowOf linksFull ⟨1, some 24, 1, .K7⟩))
      (pubStep ((pubSets (mgAll D Mg).more linksFull (flatPlacesOf linksFull true))[338]?.getD [])
        (pubRowM (mgAll D Mg).more linksFull ⟨1, some 24, 1, .K7⟩)) (z, t) = true := by
  have lv := place_leaves W l name front tl hfront _ _ _ _ hy
  have ix := place_index W l name front tl hfront _ _ _ _ hy
  rw [hmore] at h ⊢
  unfold pubHeld at h ⊢
  rw [pubFront338] at h
  rw [pubStep338, pubTied339]
  simp only [List.cons_append, List.nil_append, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true] at h ⊢
  obtain ⟨_, h2, h3⟩ := h
  refine ⟨tokenSmall_mgAll D Mg W hW l name front z _ _ _ _ hy, ?_, ?_⟩
  · have h2' : indexIsC D.N.indexNo x = true := h2
    show indexIsC D.N.indexNo t = true
    unfold indexIsC at h2' ⊢
    rw [ix]
    exact h2'
  · have h3' : indexThereC x = true := h3
    show indexThereC t = true
    unfold indexThereC at h3' ⊢
    rw [ix, lv.2.1]
    exact h3'

end H2K7

#print axioms H2K7.k7_pub_at
