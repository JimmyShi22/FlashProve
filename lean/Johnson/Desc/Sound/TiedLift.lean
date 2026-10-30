-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/TiedLift.lean: A BLOCK'S TIES TO THE FIRST CHAIN'S TABLE OF JOINTS PASS THE LIFT
OVER THE PUBLIC PART. Two lemmas, two theorems.

Why. A kind's files state its law, and its ties to the table, at a piece over the chain's carried
record S, with what was handed to the chain as a letter z (get := fun s => (z, s)). A description's
piece stands over the pair of the public part and the record, and holds the block lifted
(`OfDesc`, Johnson/Desc/Sound/DescThree.lean); the table is read there at get := the identity. The
lifted block cannot read z, and leaves it.

What is said.
  `out_liftAt`: a yes of the lifted piece is a yes of the piece at the record, with the public part
    laid back.
  **`tiedBy_liftAt`**: `TiedBy` (Johnson/Desc/Sound/TiedBy.lean) at the piece p over S, FOR EVERY
    VALUE z OF THE PUBLIC PART, at words that may name z, gives `TiedBy` at the lifted piece, z read
    off the statement: all eight clauses.
  `withMap_is_liftAt`, **`tiedBy_of_part`**: THE FORM FOR A GIVEN PIECE q of a description's row,
    with a map E that lays nothing as its extractor: if q's block is b₀ lifted, the ties at
    ⟨b₀, q's own stretch, rounds put back and errors, the identity⟩ for every z give the ties at
    `q.withMap E`.

Limits. "For every z": also at public parts that no run reaches. For a row that lays nothing (hE) in
the second form. A carriage: the premises are met by no block here. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TiedBy
import Johnson.Desc.Sound.LiftOwn
import Johnson.Desc.Sound.ReExt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start)

variable {P Cl W : Type} {C : CK} {F : Frame}

/-- The piece over the record, lifted over the public part, with its own extractor. -/
abbrev Piece.overPub (P : Type) (p : Piece C F First.S Cl W) : Piece C F (P × First.S) Cl W :=
  p.liftAt Prod.snd (fun t s => (t.1, s)) Prod.fst fun _ => p.ext

/-- A yes of the lifted piece is a yes of the piece at the record; the public part is laid back. -/
theorem out_liftAt (p : Piece C F First.S Cl W) (a b : (P × First.S) × F.E.Str)
    (τ : Iop.Tr (uLT C p.ds)) (h : (p.overPub P).ior.red.out a τ = some b) :
    ∃ x, p.ior.red.out (a.1.2, a.2) τ = some x ∧ b = ((a.1.1, x.1), x.2) := by
  have e := liftOut (P × First.S) First.S Cl W C F Prod.snd (fun t s => (t.1, s)) p
    (fun _ _ => rfl) (fun _ _ _ => rfl) a τ
  have h' : (p.lift Prod.snd fun t s => (t.1, s)).ior.red.out a τ = some b := h
  rw [e] at h'
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h'
  exact ⟨x, hx, rfl⟩

section
variable (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (ps : List Place) (k : ℕ)

/-- **THE TIES PASS THE LIFT OVER THE PUBLIC PART.** -/
theorem tiedBy_liftAt (p : Piece C F First.S Cl W) (o o' : P → First.S × F.E.Str → Prop)
    (R R' : P → First.S × F.E.Str → W → Prop)
    (H : ∀ z, TiedBy N Mg links ps (fun s => (z, s)) k p (o z) (o' z) (R z) (R' z)) :
    TiedBy N Mg links ps (fun a => a) k (p.overPub P) (fun a => o a.1.1 (a.1.2, a.2))
      (fun a => o' a.1.1 (a.1.2, a.2)) (fun a w => R a.1.1 (a.1.2, a.2) w)
      (fun a w => R' a.1.1 (a.1.2, a.2) w) := by
  refine ⟨liftGoodInExt (P × First.S) First.S P Cl W C F Prod.snd (fun t s => (t.1, s)) Prod.fst p
      (fun _ => p.ext) o o' R R' (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
      (fun z => (H z).1),
    fun a ha hm => (H a.1.1).2.1 (a.1.2, a.2) ha hm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a τ b ha hm hb ho
    obtain ⟨x, hx, rfl⟩ := out_liftAt p a b τ hb
    exact (H a.1.1).2.2.1 (a.1.2, a.2) τ x ha hm hx ho
  · intro a τ b w ha hm hb ho hw
    obtain ⟨x, hx, rfl⟩ := out_liftAt p a b τ hb
    exact (H a.1.1).2.2.2.1 (a.1.2, a.2) τ x w ha hm hx ho hw
  · intro a τ b w ha hm hb ho hw hr
    obtain ⟨x, hx, rfl⟩ := out_liftAt p a b τ hb
    exact (H a.1.1).2.2.2.2.1 (a.1.2, a.2) τ x w ha hm hx ho hw hr
  · intro a τ b w i ha hm hb hon hall hi hin
    obtain ⟨x, hx, rfl⟩ := out_liftAt p a b τ hb
    exact (H a.1.1).2.2.2.2.2.1 (a.1.2, a.2) τ x w i ha hm hx hon hall hi hin
  · intro a τ b hb hm
    obtain ⟨x, hx, rfl⟩ := out_liftAt p a b τ hb
    exact (H a.1.1).2.2.2.2.2.2.1 (a.1.2, a.2) τ x hx hm
  · intro a τ b hb hd
    obtain ⟨x, hx, rfl⟩ := out_liftAt p a b τ hb
    exact (H a.1.1).2.2.2.2.2.2.2 (a.1.2, a.2) τ x hx hd

end

/-- A description's piece whose block is b₀ lifted, with a map that lays nothing as its extractor,
IS the lifted piece. -/
theorem withMap_is_liftAt (q : Piece C F (P × First.S) Cl W) (b₀ : Block First.S Cl)
    (hq : q.b = b₀.lift Prod.snd fun t s => (t.1, s))
    (E : (P × First.S) × F.E.Str → (P × First.S) × F.E.Str → W → W) (hE : ∀ a b w, E a b w = w) :
    q.withMap E = (⟨b₀, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece C F First.S Cl W).overPub P := by
  have he : (q.withMap E).ext = fun _ _ w => w := by
    funext a τ w
    exact withMap_id q E hE a τ w
  obtain ⟨bq, base, ds, back, ext, err⟩ := q
  dsimp only at hq
  subst hq
  show (⟨_, base, ds, back, (Piece.withMap ⟨_, base, ds, back, ext, err⟩ E).ext, err⟩ :
    Piece C F (P × First.S) Cl W) = ⟨_, base, ds, back, fun _ _ w => w, err⟩
  rw [he]
  rfl

/-- **THE FORM FOR A GIVEN PIECE OF A DESCRIPTION's ROW.** -/
theorem tiedBy_of_part (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (ps : List Place)
    (k : ℕ) (q : Piece C F (P × First.S) Cl W) (b₀ : Block First.S Cl)
    (hq : q.b = b₀.lift Prod.snd fun t s => (t.1, s))
    (E : (P × First.S) × F.E.Str → (P × First.S) × F.E.Str → W → W) (hE : ∀ a b w, E a b w = w)
    (o o' : P → First.S × F.E.Str → Prop) (R R' : P → First.S × F.E.Str → W → Prop)
    (H : ∀ z, TiedBy N Mg links ps (fun s => (z, s)) k
      (⟨b₀, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C F First.S Cl W) (o z) (o' z)
      (R z) (R' z)) :
    TiedBy N Mg links ps (fun a => a) k (q.withMap E) (fun a => o a.1.1 (a.1.2, a.2))
      (fun a => o' a.1.1 (a.1.2, a.2)) (fun a w => R a.1.1 (a.1.2, a.2) w)
      (fun a w => R' a.1.1 (a.1.2, a.2) w) := by
  rw [withMap_is_liftAt q b₀ hq E hE]
  exact tiedBy_liftAt N Mg links ps k _ o o' R R' H

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.out_liftAt
#print axioms VerifiableInference.Desc.Sound.tiedBy_liftAt
#print axioms VerifiableInference.Desc.Sound.withMap_is_liftAt
#print axioms VerifiableInference.Desc.Sound.tiedBy_of_part
