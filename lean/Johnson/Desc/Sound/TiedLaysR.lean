-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
lean/Johnson/Desc/Sound/TiedLaysR.lean: THE SEAT'S FRAME WHERE A ROW OF THE TABLE LAYS A PART OF THE
    WITNESS, IN THE SECOND FORM OF THE CHAIN OF PROMISES: TiedLays.lean's three
rules with the condition Rch k in hand in each tie (`TiedByR`, TiedR.lean). The first forms stand
    unturned.
  `tiedByR_liftAtE` · `tiedByR_of_partE`: the ties pass the lift over the public part, the extractor
      reading it; over the
    state alone Rch is read at (z, state).
  **`tiedAtR_of_seatE`**: a sub-protocol at a seat is tied in the second form, whatever its kind,
      also where its row lays:
    from the kind's tie, at ANY words o o' R R' of its own, for every value z of the public part.
Limits. General in Rch. "For every z" : also at public parts that no run reaches. A rule over
    letters: no member.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TiedLays
import Johnson.Desc.Sound.TiedR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start)

variable {P Cl W : Type} {C : CK} {F : Frame}

section
variable (N : Numbers) (Mg : Meaning P W) (links : List ModelPart) (ps : List Place)
  (Rch : ℕ → (P × First.S) × F.E.Str → Prop) (k : ℕ)

/-- **THE TIES OF THE SECOND FORM PASS THE LIFT OVER THE PUBLIC PART, THE EXTRACTOR READING IT.** -/
theorem tiedByR_liftAtE (p : Piece C F First.S Cl W)
    (e : P → First.S × F.E.Str → Iop.Tr (uLT C p.ds) → W → W)
    (o o' : P → First.S × F.E.Str → Prop) (R R' : P → First.S × F.E.Str → W → Prop)
    (H : ∀ z, TiedByR N Mg links ps (fun s => (z, s)) (fun k a => Rch k ((z, a.1), a.2)) k
      (p.withExt (e z)) (o z) (o' z) (R z) (R' z)) :
    TiedByR N Mg links ps (fun a => a) Rch k
      (p.liftAt Prod.snd (fun t s => (t.1, s)) Prod.fst e)
      (fun a => o a.1.1 (a.1.2, a.2)) (fun a => o' a.1.1 (a.1.2, a.2))
      (fun a w => R a.1.1 (a.1.2, a.2) w) (fun a w => R' a.1.1 (a.1.2, a.2) w) := by
  refine ⟨liftGoodInExt (P × First.S) First.S P Cl W C F Prod.snd (fun t s => (t.1, s)) Prod.fst p
      e o o' R R' (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) (fun z => (H z).1),
    fun a ha hr hm => (H a.1.1).2.1 (a.1.2, a.2) ha hr hm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a τ b ha hr hm hb ho
    obtain ⟨x, hx, rfl⟩ := out_liftAtE p e a b τ hb
    exact (H a.1.1).2.2.1 (a.1.2, a.2) τ x ha hr hm hx ho
  · intro a τ b w ha hr hm hb ho hw
    obtain ⟨x, hx, rfl⟩ := out_liftAtE p e a b τ hb
    exact (H a.1.1).2.2.2.1 (a.1.2, a.2) τ x w ha hr hm hx ho hw
  · intro a τ b w ha hr hm hb ho hw hR
    obtain ⟨x, hx, rfl⟩ := out_liftAtE p e a b τ hb
    exact (H a.1.1).2.2.2.2.1 (a.1.2, a.2) τ x w ha hr hm hx ho hw hR
  · intro a τ b w i ha hr hm hb hon hall hi hin
    obtain ⟨x, hx, rfl⟩ := out_liftAtE p e a b τ hb
    exact (H a.1.1).2.2.2.2.2.1 (a.1.2, a.2) τ x w i ha hr hm hx hon hall hi hin
  · intro a τ b hb hm
    obtain ⟨x, hx, rfl⟩ := out_liftAtE p e a b τ hb
    exact (H a.1.1).2.2.2.2.2.2.1 (a.1.2, a.2) τ x hx hm
  · intro a τ b hb hd
    obtain ⟨x, hx, rfl⟩ := out_liftAtE p e a b τ hb
    exact (H a.1.1).2.2.2.2.2.2.2 (a.1.2, a.2) τ x hx hd

/-- The same for a given piece q of the first chain, at any extractor E laid in. -/
theorem tiedByR_of_partE (q : Piece C F (P × First.S) Cl W) (b₀ : Block First.S Cl)
    (hq : q.b = b₀.lift Prod.snd fun t s => (t.1, s))
    (E : (P × First.S) × F.E.Str → (P × First.S) × F.E.Str → W → W)
    (o o' : P → First.S × F.E.Str → Prop) (R R' : P → First.S × F.E.Str → W → Prop)
    (H : ∀ z, TiedByR N Mg links ps (fun s => (z, s)) (fun k a => Rch k ((z, a.1), a.2)) k
      ((⟨b₀, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C F First.S Cl W).withMap
        (atPub E z)) (o z) (o' z) (R z) (R' z)) :
    TiedByR N Mg links ps (fun a => a) Rch k (q.withMap E) (fun a => o a.1.1 (a.1.2, a.2))
      (fun a => o' a.1.1 (a.1.2, a.2)) (fun a w => R a.1.1 (a.1.2, a.2) w)
      (fun a w => R' a.1.1 (a.1.2, a.2) w) := by
  rw [withMap_is_liftAtE q b₀ hq E]
  exact tiedByR_liftAtE N Mg links ps Rch k _ _ o o' R R' H

end

/-- **A SUB-PROTOCOL AT A SEAT IS TIED IN THE SECOND FORM, WHATEVER ITS KIND, ALSO WHERE ITS ROW
    LAYS.** tie: left to the kind's
files, at words o o' R R' of their own choosing. -/
theorem tiedAtR_of_seatE (links : List ModelPart) (ps : List Place) (k : ℕ) (Bst B : Block First.S Cl)
    (q : Piece C F (P × First.S) Cl W) (hS : SeatOf Bst B)
    (hq : q.b = (below B).lift Prod.snd fun t s => (t.1, s)) (N : Numbers) (Mg : Meaning P W)
    (Rch : ℕ → (P × First.S) × F.E.Str → Prop)
    (E : (P × First.S) × F.E.Str → (P × First.S) × F.E.Str → W → W)
    (o o' : P → First.S × F.E.Str → Prop) (R R' : P → First.S × F.E.Str → W → Prop)
    (tie : SeatOf Bst B → ∀ z : P, TiedByR N Mg links ps (fun s => (z, s))
      (fun k a => Rch k ((z, a.1), a.2)) k
      ((⟨below B, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C F First.S Cl W).withMap (atPub E z)) (o z) (o' z) (R z) (R' z)) :
    TiedAtR N Mg links ps (fun a => a) Rch k (q.withMap E) :=
  (tiedByR_of_partE N Mg links ps Rch k q (below B) hq E o o' R R' (tie hS)).tiedAtR

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.tiedByR_liftAtE
#print axioms VerifiableInference.Desc.Sound.tiedByR_of_partE
#print axioms VerifiableInference.Desc.Sound.tiedAtR_of_seatE
