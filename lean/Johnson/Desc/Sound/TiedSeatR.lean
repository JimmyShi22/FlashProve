-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
lean/Johnson/Desc/Sound/TiedSeatR.lean: THE SEAT'S FRAME IN THE SECOND FORM OF THE CHAIN OF
    PROMISES: what a kind's files owe at a seat (`SeatLaws`, TiedSeat.lean), WITH THE
CONDITION Rch k IN HAND wherever the table's promise in front is in hand (meant: "this verifier's
    state is reached from the
state at the start"). TiedLift.lean's and TiedSeat.lean's rules again, one premise more; the first
    forms stand unturned.
  `tiedByR_liftAt`, `tiedByR_of_part`: the ties pass the lift over the public part; over the state
      alone Rch is read at
    (z, state): fun k a => Rch k ((z, a.1), a.2).
  `tiedByR_of_own`: a sub-protocol's own law AT THE PROMISE WITH Rch BESIDE IT, what rides, and the
      two facts on its text.
  **`SeatLawsR`**: the kind's four, second form. **`tiedByR_of_seatLawsR`**: the tie (`TiedAtR`)
      from them, at a row at which the table's extractor lays nothing (hE).
Limits. General in Rch. "For every z" : also at public parts that no run reaches. A rule over
    letters: no member.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TiedR
import Johnson.Desc.Sound.TiedSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

open OnBytes OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start)

section
variable {Cl P W : Type} {C : CK} {F : Frame} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
  (ps : List Place) (Rch : ℕ → (P × First.S) × F.E.Str → Prop) (k : ℕ)

/-- **THE TIES OF THE SECOND FORM PASS THE LIFT OVER THE PUBLIC PART.** -/
theorem tiedByR_liftAt (p : Piece C F First.S Cl W) (o o' : P → First.S × F.E.Str → Prop)
    (R R' : P → First.S × F.E.Str → W → Prop)
    (H : ∀ z, TiedByR N Mg links ps (fun s => (z, s)) (fun k a => Rch k ((z, a.1), a.2)) k p (o z)
      (o' z) (R z) (R' z)) :
    TiedByR N Mg links ps (fun a => a) Rch k (p.overPub P) (fun a => o a.1.1 (a.1.2, a.2))
      (fun a => o' a.1.1 (a.1.2, a.2)) (fun a w => R a.1.1 (a.1.2, a.2) w)
      (fun a w => R' a.1.1 (a.1.2, a.2) w) := by
  refine ⟨liftGoodInExt (P × First.S) First.S P Cl W C F Prod.snd (fun t s => (t.1, s)) Prod.fst p
      (fun _ => p.ext) o o' R R' (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
      (fun z => (H z).1),
    fun a ha hr hm => (H a.1.1).2.1 (a.1.2, a.2) ha hr hm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a τ b ha hr hm hb ho
    obtain ⟨x, hx, rfl⟩ := out_liftAt p a b τ hb
    exact (H a.1.1).2.2.1 (a.1.2, a.2) τ x ha hr hm hx ho
  · intro a τ b w ha hr hm hb ho hw
    obtain ⟨x, hx, rfl⟩ := out_liftAt p a b τ hb
    exact (H a.1.1).2.2.2.1 (a.1.2, a.2) τ x w ha hr hm hx ho hw
  · intro a τ b w ha hr hm hb ho hw hR
    obtain ⟨x, hx, rfl⟩ := out_liftAt p a b τ hb
    exact (H a.1.1).2.2.2.2.1 (a.1.2, a.2) τ x w ha hr hm hx ho hw hR
  · intro a τ b w i ha hr hm hb hon hall hi hin
    obtain ⟨x, hx, rfl⟩ := out_liftAt p a b τ hb
    exact (H a.1.1).2.2.2.2.2.1 (a.1.2, a.2) τ x w i ha hr hm hx hon hall hi hin
  · intro a τ b hb hm
    obtain ⟨x, hx, rfl⟩ := out_liftAt p a b τ hb
    exact (H a.1.1).2.2.2.2.2.2.1 (a.1.2, a.2) τ x hx hm
  · intro a τ b hb hd
    obtain ⟨x, hx, rfl⟩ := out_liftAt p a b τ hb
    exact (H a.1.1).2.2.2.2.2.2.2 (a.1.2, a.2) τ x hx hd

/-- The same for a given piece q of the first chain: one whose sub-protocol is b₀ lifted over the
    public part, with
an extractor E laid in that changes no witness. -/
theorem tiedByR_of_part (q : Piece C F (P × First.S) Cl W) (b₀ : Block First.S Cl)
    (hq : q.b = b₀.lift Prod.snd fun t s => (t.1, s))
    (E : (P × First.S) × F.E.Str → (P × First.S) × F.E.Str → W → W) (hE : ∀ a b w, E a b w = w)
    (o o' : P → First.S × F.E.Str → Prop) (R R' : P → First.S × F.E.Str → W → Prop)
    (H : ∀ z, TiedByR N Mg links ps (fun s => (z, s)) (fun k a => Rch k ((z, a.1), a.2)) k
      (⟨b₀, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C F First.S Cl W) (o z) (o' z)
      (R z) (R' z)) :
    TiedByR N Mg links ps (fun a => a) Rch k (q.withMap E) (fun a => o a.1.1 (a.1.2, a.2))
      (fun a => o' a.1.1 (a.1.2, a.2)) (fun a w => R a.1.1 (a.1.2, a.2) w)
      (fun a w => R' a.1.1 (a.1.2, a.2) w) := by
  rw [withMap_is_liftAt q b₀ hq E hE]
  exact tiedByR_liftAt N Mg links ps Rch k _ o o' R R' H

end

section
variable {A Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
  (links : List ModelPart) (ps : List Place) (get : A → P × First.S) (Rch : ℕ → A × Fr.E.Str → Prop)

/-- A sub-protocol's own law at the promise with Rch beside it, what rides, and the two facts on its
text: a tie of the second form at the table's own words. -/
theorem tiedByR_of_own (k : ℕ) (q : Piece C Fr A Cl W)
    (ho : q.Own (onR N Mg links ps get Rch k) (onQ N Mg links ps get (k + 1)) (meansQ N Mg get)
      (insQ links ps k) (outsQ links ps k))
    (t5 : ∀ a τ b w i, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → onQ N Mg links ps get (k + 1) b →
      relQ N Mg links ps get (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg get i a (q.ext a τ w))
    (hMark : ∀ a τ b, q.ior.red.out a τ = some b → (get a.1).2.failed ≠ none →
      (get b.1).2.failed ≠ none)
    (hDec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes (get a.1) (strsOf Fr a.2) →
      Mg.decodes (get b.1) (strsOf Fr b.2)) :
    TiedByR N Mg links ps get Rch k q (onR N Mg links ps get Rch k)
      (onQ N Mg links ps get (k + 1)) (relAt (meansQ N Mg get) (insQ links ps k))
      (relAt (meansQ N Mg get) (outsQ links ps k)) :=
  ⟨ho, fun _ ha hr _ => ⟨ha, hr⟩, fun _ _ _ _ _ _ _ hb => hb, fun _ _ _ _ _ _ _ _ _ hO => hO,
    fun _ _ _ _ _ _ _ _ _ _ hR => hR, t5, hMark, hDec⟩

end

section
variable {Cl P W : Type} {C : CK} {Fr : Frame} (links : List ModelPart)

/-- **What a kind's files owe at a seat, second form.** -/
def SeatLawsR (ps : List Place) (k : ℕ) (q : Piece C Fr (P × First.S) Cl W) (N : Numbers)
    (Mg : Meaning P W) (Rch : ℕ → (P × First.S) × Fr.E.Str → Prop) (Bst : Block First.S Cl) :
    Prop :=
  (∀ B', SeatOf Bst B' → ∀ z : P,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ : Piece C Fr First.S Cl W).Own
        (onR N Mg links ps (fun s => (z, s)) (fun k a => Rch k ((z, a.1), a.2)) k)
        (onQ N Mg links ps (fun s => (z, s)) (k + 1))
        (meansQ N Mg fun s => (z, s)) (insQ links ps k) (outsQ links ps k)) ∧
  (∀ B', SeatOf Bst B' → ∀ (z : P) a τ b w i,
      onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b →
      onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a w) ∧
  (∀ B', SeatOf Bst B' → ∀ a τ b,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b → a.1.failed ≠ none → b.1.failed ≠ none) ∧
  ∀ B', SeatOf Bst B' → ∀ (z : P) a τ b,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b → Mg.decodes (z, a.1) (strsOf Fr a.2) →
      Mg.decodes (z, b.1) (strsOf Fr b.2)

/-- **The tie of the second form from the kind's four.** -/
theorem tiedByR_of_seatLawsR (ps : List Place) (k : ℕ) (Bst B : Block First.S Cl)
    (q : Piece C Fr (P × First.S) Cl W) (hS : SeatOf Bst B)
    (hq : q.b = (below B).lift Prod.snd fun t s => (t.1, s)) (N : Numbers) (Mg : Meaning P W)
    (Rch : ℕ → (P × First.S) × Fr.E.Str → Prop)
    (E : (P × First.S) × Fr.E.Str → (P × First.S) × Fr.E.Str → W → W) (hE : ∀ a b w, E a b w = w)
    (H : SeatLawsR links ps k q N Mg Rch Bst) :
    TiedAtR N Mg links ps (fun a => a) Rch k (q.withMap E) :=
  (tiedByR_of_part N Mg links ps Rch k q (below B) hq E hE
    (fun z => onR N Mg links ps (fun s => (z, s)) (fun k a => Rch k ((z, a.1), a.2)) k)
    (fun z => onQ N Mg links ps (fun s => (z, s)) (k + 1))
    (fun z => relAt (meansQ N Mg fun s => (z, s)) (insQ links ps k))
    (fun z => relAt (meansQ N Mg fun s => (z, s)) (outsQ links ps k))
    fun z => tiedByR_of_own N Mg links ps (fun s => (z, s)) _ k _ (H.1 B hS z)
      (H.2.1 B hS z) (H.2.2.1 B hS) (H.2.2.2 B hS z)).tiedAtR

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.tiedByR_liftAt
#print axioms VerifiableInference.Desc.Sound.tiedByR_of_part
#print axioms VerifiableInference.Desc.Sound.tiedByR_of_own
#print axioms VerifiableInference.Desc.Sound.tiedByR_of_seatLawsR
