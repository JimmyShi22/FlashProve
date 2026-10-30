-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/ShutYes.lean
(kind K9's soundness lemma): THEOREM: Law/ShutLaw.lean's shut_goodIn FOR A BLOCK IN WHATEVER DRESS:
the piece holds a block b5 of which only this is asked: a yes of its step is a yes of K9.shut's step
with the same return (a seat's guard only adds refusals; its name, its place and its test on the
plan are free). So the law speaks of the term that a seat calls.
  shut_goodIn_yes   the piece is good, at any errors, between any two relations of which the one
                behind gives the one in front along the block's writing.
  shut_mark_yes a mark stays at such a piece (Law/KeepsField.lean's shut_mark, from a yes).
  top8_topOf    top8 (Law/K8Disc.lean) is the library's topOf, to the letter.

-/
import Johnson.Desc.First.Batch.Law.KeepsField
import Johnson.Desc.First.Batch.Law.K8Disc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)
open _root_.Iop (Doomed)
open VerifiableInference.Desc.K9 (atS Where shut closed)
open VerifiableInference.Desc.First (S)

variable {W Cl : Type} {C : CK} {F : Frame}

/-- **The piece of "shut" in whatever dress is good**, at any errors. -/
theorem shut_goodIn_yes (pw : Where) (piece : Nat) (b₅ : Block S Cl)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Cl) pw piece).step ft s rs cols = .ok x)
    (p : Piece C F S Cl W) (hb : p.b = below b₅) (hext : ∀ a τ w, p.ext a τ w = w)
    (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop)
    (hhands : ∀ a τ b, on a → p.ior.red.out a τ = some b → on' b)
    (hcarry : ∀ a τ b w L, on a → p.ior.red.out a τ = some b → a.1.link? = some L →
      b.1 = a.1.putLink (closed L L.check.frame) → R' b w → R a w) :
    p.GoodIn on on' R R' := by
  intro a ha
  refine Doomed.of_forall _ _ fun τ b hout => ⟨hhands a τ b ha hout, ?_⟩
  intro w hw
  rw [hext]
  obtain ⟨_, _, hfold⟩ := Piece.out_below hb hout
  obtain ⟨k, hstep⟩ := fold_one hfold
  obtain ⟨L, hL, e⟩ := shut_inv pw piece F.ft a.1 _ _ b.1 k (hb₅ _ _ _ _ _ hstep)
  exact hcarry a τ b w L ha hout hL e hw

/-- A mark stays at such a piece. -/
theorem shut_mark_yes (pw : Where) (piece : ℕ) (b₅ : Block S Cl)
    (hb₅ : ∀ ft s rs cols x, b₅.step ft s rs cols = .ok x →
      (shut (Cl := Cl) pw piece).step ft s rs cols = .ok x)
    (ps : Piece C F S Cl W) (hps : ps.b = below b₅) (a b : S × F.E.Str)
    (τ : _root_.Iop.Tr (uLT C ps.ds)) (hout : ps.ior.red.out a τ = some b)
    (hm : a.1.failed ≠ none) : b.1.failed ≠ none := by
  obtain ⟨_, _, hfold⟩ := Piece.out_below hps hout
  obtain ⟨k, hs⟩ := fold_one hfold
  rw [shut_keep (·.failed) failed_putLink pw piece _ _ _ _ _ k (hb₅ _ _ _ _ _ hs)]
  exact hm

/-- top8 is the library's topOf. -/
theorem top8_topOf (tl : HTailF2) (funs : Array HFun) :
    top8 tl funs = OnBytes.Tie.Pv.Tail.Port.topOf tl funs := rfl

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.shut_goodIn_yes
#print axioms VerifiableInference.Desc.K9L.shut_mark_yes
#print axioms VerifiableInference.Desc.K9L.top8_topOf
