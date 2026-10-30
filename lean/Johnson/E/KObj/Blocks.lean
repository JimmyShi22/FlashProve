-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/E/KObj/Blocks.lean: a protocol description as a typed list of bare blocks; if every block is
knowledge sound, so is the list's one reduction.

A bare block is a typed reduction between two joints, with an extractor and a list of errors. No
honest side occurs in its type. Definitions and proofs. No library file turns.
Main names:
  `JK`: a joint, the verifier's side alone: statements, oracles, relaxed witnesses, a condition, the
    relaxed relation.
  `BK A B`: a bare block from the joint A to the joint B.
  `BK.Good`: a block's property: point queries; a local verifier; round-by-round knowledge
    soundness into the next joint's condition (`Reduction.KnowInto`).
  `BK.seq`, `BK.good_seq`: two blocks in a row; the property goes along.
  `LK A B`: a description: a typed list of blocks. `LK.blk`: its one reduction (`IOR.seq` in a row),
    one extractor (`IOR.extSeq`), one list of errors (`Err.app`).
  `LK.Each`, `PG`, `LK.good`: every block has its property ⇒ the list's one block has it.
  `Rd`, `BK.Hands`, `BK.hands_seq`: what is read off a joint (a record, an encoded index) is handed
    on by a block, and by two blocks in a row.
Limits: nothing here says that a block has its property, or that a list describes a protocol that
any program runs. Nothing on an honest prover, on completeness or on zero knowledge.

-/
import Ior.KnowColl
import Ior.SeqProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob

/-- a joint, the verifier's side alone: statements, oracles, relaxed witnesses, the condition, the
relaxed relation -/
structure JK : Type 1 where
  X    : Type
  E    : ExtSpec
  W    : Type
  on   : X × E.Str → Prop
  relR : X × E.Str → W → Prop

/-- a bare block -/
structure BK (A B : JK) : Type 1 where
  R   : IOR A.X A.E B.X B.E
  ext : A.X × A.E.Str → Tr R.shape → B.W → A.W
  err : Err R.shape

/-- A BLOCK's PROPERTY -/
structure BK.Good {A B : JK} (b : BK A B) : Prop where
  point   : Nonempty b.R.shape.IsPoint
  isLocal : b.R.IsLocal
  know    : b.R.red.KnowInto A.on B.on A.relR B.relR b.ext b.err

/-- two blocks in a row; d: the extractor's value where the first verifier rejects -/
noncomputable def BK.seq {A B C : JK} (b : BK A B) (c : BK B C) (d : A.W) : BK A C where
  R := b.R.seq c.R
  ext := IOR.extSeq b.R c.R b.ext c.ext d
  err := Err.app b.err c.err

theorem BK.good_seq {A B C : JK} (b : BK A B) (c : BK B C) (d : A.W) (hb : b.Good) (hc : c.Good) :
    (b.seq c d).Good where
  point := hb.point.elim fun p₁ => hc.point.elim fun p₂ => ⟨Shape.IsPoint.append p₁ p₂⟩
  isLocal := hb.isLocal.seq hc.isLocal
  know := by
    have h := knowInto_seq _ _ _ _ _ _ b.R.red c.R.red A.on B.on C.on A.relR B.relR C.relR b.ext
      c.ext b.err c.err d hb.know hc.know
    intro a ha
    refine Doomed.mono _ _ ?_ (h a ha)
    intro τ hτ x w hx hw
    exact hτ x w ((IOR.red_seq_out b.R c.R a τ).symm.trans hx) hw

/-- A DESCRIPTION: a typed list of blocks -/
inductive LK : JK → JK → Type 1
  | one {A B : JK} (b : BK A B) : LK A B
  | snoc {A B C : JK} (l : LK A B) (b : BK B C) : LK A C

namespace LK

/-- every block has Q -/
def Each (Q : ∀ A B : JK, BK A B → Prop) {A : JK} : {B : JK} → LK A B → Prop
  | _, .one b => Q _ _ b
  | _, .snoc l b => l.Each Q ∧ Q _ _ b

/-- THE ONE BLOCK OF A LIST: one reduction, one extractor, one list of errors -/
noncomputable def blk {A : JK} : {B : JK} → LK A B → A.W → BK A B
  | _, .one b, _ => b
  | _, .snoc l b, d => (l.blk d).seq b d

/-- the number of blocks -/
def len {A : JK} : {B : JK} → LK A B → ℕ
  | _, .one _ => 1
  | _, .snoc l _ => l.len + 1

/-- two lists in a row -/
def app {A B : JK} (l : LK A B) : {C : JK} → LK B C → LK A C
  | _, .one b => .snoc l b
  | _, .snoc m b => .snoc (l.app m) b

theorem each_one (Q : ∀ A B : JK, BK A B → Prop) {A B : JK} (b : BK A B) :
    (LK.one b).Each Q ↔ Q _ _ b := by rw [LK.Each]
theorem each_snoc (Q : ∀ A B : JK, BK A B → Prop) {A B C : JK} (l : LK A B) (b : BK B C) :
    (l.snoc b).Each Q ↔ l.Each Q ∧ Q _ _ b := by rw [LK.Each]
theorem blk_one {A B : JK} (b : BK A B) (d : A.W) : (LK.one b).blk d = b := by rw [LK.blk]
theorem blk_snoc {A B C : JK} (l : LK A B) (b : BK B C) (d : A.W) :
    (l.snoc b).blk d = (l.blk d).seq b d := by rw [LK.blk]
theorem app_one {A B C : JK} (l : LK A B) (b : BK B C) : l.app (.one b) = l.snoc b := by rw [LK.app]
theorem app_snoc {A B C D : JK} (l : LK A B) (m : LK B C) (b : BK C D) :
    l.app (m.snoc b) = (l.app m).snoc b := by rw [LK.app]

/-- `len`'s equations are made here, before the seal. -/
private theorem len_eqs {A B C : JK} (l : LK A B) (b : BK B C) : (l.snoc b).len = l.len + 1 := by
  rw [LK.len]

/- These four are by structural recursion, so they unfold at a written list; they are sealed, so
that no unification unfolds a long list unasked: `unseal KObj.LK.blk in …` opens one. -/
attribute [irreducible] Each blk len app

end LK

/-- the predicate «has its property» -/
def PG : ∀ A B : JK, BK A B → Prop := fun _ _ b => b.Good

/-- (5) EVERY BLOCK HAS ITS PROPERTY ⇒ THE LIST's ONE BLOCK HAS IT -/
theorem LK.good {A B : JK} (l : LK A B) (d : A.W) : l.Each PG → (l.blk d).Good := by
  induction l with
  | one b =>
    intro h
    rw [LK.blk_one]
    exact (LK.each_one _ b).1 h
  | snoc l b ih =>
    intro h
    rw [LK.blk_snoc]
    exact BK.good_seq _ b d (ih ((LK.each_snoc _ l b).1 h).1) ((LK.each_snoc _ l b).1 h).2

theorem LK.each_app (Q : ∀ A B : JK, BK A B → Prop) {A B C : JK} (l : LK A B) (m : LK B C) :
    (l.app m).Each Q ↔ l.Each Q ∧ m.Each Q := by
  induction m with
  | one b => rw [LK.app_one, LK.each_snoc, LK.each_one]
  | snoc m b ih => rw [LK.app_snoc, LK.each_snoc, LK.each_snoc, ih, and_assoc]

/-! ### (6) what is handed on along a list -/

/-- what is read off a joint's statements and oracles: a part of the explicit part (the record), a
part of the oracles (the encoded index) -/
structure Rd (T : Type) (U : Type) (A : JK) where
  rc : A.X → T
  ix : A.E.Str → U

/-- a block hands both on -/
structure BK.Hands {T U : Type} {A B : JK} (b : BK A B) (ρ : Rd T U A) (σ : Rd T U B) : Prop where
  passes : ∀ x y τ x', b.R.out x y τ = some x' → σ.rc x' = ρ.rc x
  copy   : ∀ y τ, σ.ix (b.R.imp y τ) = ρ.ix y

theorem BK.hands_seq {T U : Type} {A B C : JK} (b : BK A B) (c : BK B C) (d : A.W) (ρ : Rd T U A)
    (σ : Rd T U B) (θ : Rd T U C) (hb : b.Hands ρ σ) (hc : c.Hands σ θ) :
    (b.seq c d).Hands ρ θ where
  passes := by
    intro x y τ x' h
    have h' : (b.R.out x y (Tr.fst τ)).bind (fun x₂ =>
        c.R.out x₂ (b.R.imp y (Tr.fst τ)) (Tr.snd (s := b.R.shape) τ)) = some x' := h
    cases e : b.R.out x y (Tr.fst τ) with
    | none => rw [e] at h'; exact absurd h' (by simp)
    | some x₂ =>
      rw [e] at h'
      exact (hc.passes _ _ _ _ h').trans (hb.passes _ _ _ _ e)
  copy := fun y τ => (hc.copy _ _).trans (hb.copy _ _)

#print axioms KObj.BK.good_seq
#print axioms KObj.LK.good
#print axioms KObj.LK.each_app
#print axioms KObj.BK.hands_seq

end KObj
