-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ReadsNamed.lean: the head's plan names the array of reads, in every public
part that the verifier's function publicOf returns.

What the file holds.
  Third tl        the record of a smallness test numbers its third vector, U3, as array 0.
  public_third    publicOf pol KL layout = .ok X gives Third X.H.tl, that is
                  X.H.tl.ix.U.getD 2 none = some 0.
  public_block    so the output head's own block is there: Head.blockOf X l is some block, at
                  every l.
  shapeF_third, made_third, planH2_third   the steps: what HTailF2.shapeF returns at the list
                  false, false, true, false; what follows in the plan keeps the numbering.
Why. The output head's own block is made from the number under which the plan lists the array of
reads; where the plan lists none there is no block, and a law on the block speaks of nothing.

On what it rests. OnBytes/Tie/Pv/Lookup/Ends/FoHasU.lean shows that the record has ONE of the four
vectors (TlU; public_H_u). Its proofs see more than that statement keeps: which vector, and its
number. The four proofs here walk the same routines in the same order, and keep it. The two local
tactics are that file's.

What it does not give. Nothing on soundness. Nothing on the array's length or on what it holds. That
publicOf returns is a premise.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoHasU
import Johnson.Stored.HeadSeatAt

set_option autoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.ReadsNamed

open OnBytes OnBytes.Model OnBytes.Model.HTailF2 Fo Fo.Pub Fo.ZPlan
open Fo.BatRows (bindE_ok ite_ok)

set_option hygiene false in
/-- Closes a goal whose hypothesis e says that a routine which throws has returned. -/
local macro "dead" : tactic => `(tactic| first
  | (obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done)
  | (obtain ⟨_, _, e⟩ := bindE_ok e; obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done))

set_option hygiene false in
/-- Takes the branch of a test in which nothing is thrown. -/
local macro "alive" : tactic => `(tactic|
  (rcases ite_ok e with ⟨_, e⟩ | ⟨_, e⟩; (· dead); obtain ⟨_, _, e⟩ := bindE_ok e))

/-- The record numbers its third vector as array 0. -/
def Third (tl : HTailF2) : Prop := tl.ix.U.getD 2 none = some 0

theorem Third.same {a b : HTailF2} (h : Third a) (k : SameP a b) : Third b := by
  have e : b.ix = a.ix := congrArg (·.ix) k.eq
  unfold Third
  rw [e]
  exact h

theorem shapeF_third {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {tau : Nat}
    (e : tl.shapeF m txOf f #[false, false, true, false] tau = .ok tl') : Third tl' := by
  unfold HTailF2.shapeF at e
  dsimp only at e
  alive
  alive
  obtain ⟨_, _, e⟩ := bindE_ok e
  alive
  obtain ⟨r2, h2, e⟩ := bindE_ok e
  obtain rfl := Except.ok.inj h2
  obtain ⟨_, _, e⟩ := bindE_ok e
  alive
  alive
  obtain ⟨_, _, _, hi, _⟩ := Fo.PiecesF.piecesF_pieceOK_walk e
  unfold Third
  rw [hi]
  rfl

theorem made_third {tl₀ tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {tau : Nat}
    (hs : tl₀.shapeF m txOf f #[false, false, true, false] tau = .ok tl) {F G : Fork}
    {T T' : Tail2} {nU aTX : Array Nat} {hb hbLine : Nat}
    (ha : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) {tlc : HTailF2}
    (hr : SameP tl' tlc) : Third tlc :=
  (shapeF_third hs).same ((addTreesF_sameP ha).trans hr)

theorem planH2_third (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) : Third hp.tl := by
  unfold Head.planH2 at e
  repeat obtain ⟨_, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl, hS, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨⟨tl1, Fp, Tp⟩, hA, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl2, hO, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    cases e
    exact made_third hS hA (ownerHeld_sameP hO)
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

/-- **The head's plan names the array of reads, as array 0.** -/
theorem public_third (h : Verify.publicOf pol KL layout = .ok X) : Third X.H.tl := by
  obtain ⟨H0, h0, e⟩ := public_H h
  rw [e]
  exact planH2_third _ _ _ _ _ _ _ H0 h0

/-- **So the output head's own block is there.** -/
theorem public_block (h : Verify.publicOf pol KL layout = .ok X) (l : Nat) :
    (VerifiableInference.Desc.Kinds.Head.blockOf X l).isSome = true := by
  unfold VerifiableInference.Desc.Kinds.Head.blockOf
  rw [show X.H.tl.ix.U.getD 2 none = some 0 from public_third h]
  rfl

end VerifiableInference.Desc.Kinds.Head.Law.ReadsNamed

#print axioms VerifiableInference.Desc.Kinds.Head.Law.ReadsNamed.public_third
#print axioms VerifiableInference.Desc.Kinds.Head.Law.ReadsNamed.public_block
