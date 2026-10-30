-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/G4/RoundIsAll.lean: what it means that a typed round of the library is the round of a plan's
entry, for entries of more kinds than OnBytes/G4/RoundIs.lean bears, as far as a typed round can say
it.

A round of the library (Iop.Round, Iop/Shape.lean) holds types. A plan's entry (Fmt.Entry,
Fmt/Plan.lean) is a name and eleven numbers. OnBytes/G4/RoundIs.lean ties three of the eleven (msg,
drawE, drawNZ) for rounds that send and draw elements of the challenge field alone. It cannot bear a
round that draws matrix entries or positions, or that sends a root: of such an entry its EntryIs
holds for a hollow round and fails for the true one. This file ties seven numbers, for all such
rounds. It turns nothing in RoundIs.lean.

`EntryIsAll E F r e`, with E the challenge field and F the base field, says four things.
 - The plain part of the prover's message is, up to a bijection, some elements of E and some of F,
   and msg = 32 roots + 24 (elements of E) + 8 (elements of F). In the format a root is 32 bytes, an
   element of the challenge field or an answer to a sample 24, an element of the base field 8.
 - drawNZ ≤ drawE: the elements that must not be 0 are among the elements drawn.
 - The challenge is, up to a bijection, `DrawSet`: drawE - drawNZ elements of E, drawNZ elements of
   E that are not 0, poss numbers below 2 ^ logN, and trits pairs of bits. A matrix entry is drawn
   as two bits (Fmt/Rules6.lean, tritAt: first bit 0 gives 0; else the second bit gives 1 or -1), so
   that 0 has probability 1/2; it is not an element of a set of three.
 - The round has no oracle position exactly if roots = 0.
`ShapeIsAll E F s ds` says it of a list of rounds and a list of entries, one by one. The statement
to use is `ShapeIsAll Cb.Gl.E Cb.Gl.F shape ds`. For a round with a finite plain part all of it is a
matter of two sizes (`entryIsAll_iff_card`).

What it lets through. It counts: two sizes, equations, and whether there is an oracle position.
 - Which bijection: the order of the parts inside a message or a challenge is tied by nothing here.
 - How many roots, beyond "none or some": a typed round has one oracle part, and its positions do
   not say into how many trees they are cut. Nothing on the oracle part's own size.
 - How many elements of E and how many of F: an element of E has the size of three of F, so only 3
   (elements of E) + (elements of F) is determined, and with it msg once roots is given.
 - The five numbers of a challenge are not determined by its size together: a position below 2 ^ 2
   has the size of a matrix entry. What holds of two entries of one round: if they agree in poss,
   logN and trits, they agree in drawE and drawNZ; if they agree in the four others, they agree in
   trits, in poss (if 0 < logN) and in logN (if 0 < poss). So an entry in which ONE of these five is
   changed is refuted, but for poss at logN = 0 and logN at poss = 0, where nothing is drawn from
   more than one. msg changed is refuted with roots held. roots changed from some to some others is
   NOT refuted.
 - The name, count, work, answers and rows are tied to nothing.
Of which shape. The statement is meant of a shape BEFORE proof of work is laid on it. A round with b
bits of work (Round.grind, Iop/Grind.lean) has another plain part, which holds a nonce too, and
another challenge set. This file has no law on such a round; it is not meant to be EntryIsAll of its
entry.
What it cannot bear. A message with an item "word" (8 bytes, any 64 bits). A round that draws a
seal: that it does is the round's kind, no number of the entry; EntryIsAll asks a one-point
challenge of it.

Main definitions: DrawSet, EntryIsAll, ShapeIsAll, bareRoundAll, rootRoundAll.
Main theorems: card_drawSet, EntryIsAll.card_chal, EntryIsAll.msg_eq, EntryIsAll.draws_eq,
EntryIsAll.poss_eq, EntryIsAll.logN_eq, EntryIsAll.trits_eq, EntryIsAll.roots_zero_iff,
EntryIs.toAll, entryIsAll_iff_card, entryIsAll_bareRoundAll, entryIsAll_rootRoundAll, card_gl_cube,
two_le_card_gl_base.
Not claimed. Nothing on any protocol.
-/
import OnBytes.G4.RoundIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.G4
open Iop

/-- The set from which a round draws: so many elements of E, so many elements of E that are not 0,
so
many positions below 2 ^ logSize, and so many matrix entries, each as two bits. -/
def DrawSet (E : Type) [Zero E] (plain nonzero positions logSize matrixEntries : ℕ) : Type :=
  (Fin plain → E) × (Fin nonzero → {x : E // x ≠ 0}) × (Fin positions → Fin (2 ^ logSize)) ×
    (Fin matrixEntries → Bool × Bool)

/-- The round r sends and draws what the entry e says, in the seven numbers msg, roots, drawE,
drawNZ,
poss, logN, trits, as far as the types of a round can say it. -/
def EntryIsAll (E F : Type) [Zero E] (r : Round) (e : Fmt.Entry) : Prop :=
  (∃ scalars words : ℕ, Nonempty (r.Plain ≃ (Fin scalars → E) × (Fin words → F)) ∧
    e.msg = 32 * e.roots + 24 * scalars + 8 * words) ∧
  e.drawNZ ≤ e.drawE ∧
  Nonempty (r.Chal ≃ DrawSet E (e.drawE - e.drawNZ) e.drawNZ e.poss e.logN e.trits) ∧
  (IsEmpty r.Pos ↔ e.roots = 0)

/-- The rounds of a shape are the rounds of the entries, one by one. -/
def ShapeIsAll (E F : Type) [Zero E] (s : Shape) (ds : List Fmt.Entry) : Prop :=
  List.Forall₂ (EntryIsAll E F) s ds

section
variable {E F : Type} [Zero E] [Finite E]

/-- The size of the set from which a round draws. -/
theorem card_drawSet (plain nonzero positions logSize matrixEntries : ℕ) :
    Nat.card (DrawSet E plain nonzero positions logSize matrixEntries) =
      Nat.card E ^ plain * ((Nat.card E - 1) ^ nonzero *
        ((2 ^ logSize) ^ positions * 4 ^ matrixEntries)) := by
  unfold DrawSet
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod, card_fun, card_fun, card_fun, card_fun, card_nz,
    Nat.card_fin, Nat.card_prod]
  simp

/-- The size of the challenge set, in the entry's own numbers. -/
theorem EntryIsAll.card_chal {r : Round} {e : Fmt.Entry} (h : EntryIsAll E F r e) :
    Nat.card r.Chal =
      Nat.card E ^ (e.drawE - e.drawNZ) * ((Nat.card E - 1) ^ e.drawNZ *
        ((2 ^ e.logN) ^ e.poss * 4 ^ e.trits)) := by
  obtain ⟨f⟩ := h.2.2.1
  rw [Nat.card_congr f, card_drawSet]

/-- q ^ a (q - 1) ^ b determines a and b, for q above 2. -/
theorem pow_mul_pow_inj {q a b a' b' : ℕ} (hq : 2 < q)
    (h : q ^ a * (q - 1) ^ b = q ^ a' * (q - 1) ^ b') : a = a' ∧ b = b' := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h
  have hc : Nat.Coprime (m + 1) m := by simp
  have le : ∀ {a b a' b' : ℕ}, (m + 1) ^ a * m ^ b = (m + 1) ^ a' * m ^ b' → a ≤ a' := by
    intro a b a' b' h
    have hd : (m + 1) ^ a ∣ (m + 1) ^ a' * m ^ b' := ⟨m ^ b, h.symm⟩
    have hd' := (Nat.Coprime.pow a b' hc).dvd_of_dvd_mul_right hd
    exact (Nat.pow_dvd_pow_iff_le_right (by omega)).1 hd'
  have ha : a = a' := le_antisymm (le h) (le h.symm)
  subst ha
  have hb := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega)) h
  exact ⟨rfl, Nat.pow_right_injective (by omega) hb⟩

/-- Two entries of one round give the challenge set one size. -/
theorem EntryIsAll.card_eq {r : Round} {e e' : Fmt.Entry} (h : EntryIsAll E F r e)
    (h' : EntryIsAll E F r e') :
    Nat.card E ^ (e.drawE - e.drawNZ) * ((Nat.card E - 1) ^ e.drawNZ *
        ((2 ^ e.logN) ^ e.poss * 4 ^ e.trits)) =
      Nat.card E ^ (e'.drawE - e'.drawNZ) * ((Nat.card E - 1) ^ e'.drawNZ *
        ((2 ^ e'.logN) ^ e'.poss * 4 ^ e'.trits)) := by
  rw [← h.card_chal, ← h'.card_chal]

/-- Two entries of one round that agree in drawE, drawNZ, poss and logN agree in trits. -/
theorem EntryIsAll.trits_eq (hq : 2 < Nat.card E) {r : Round} {e e' : Fmt.Entry}
    (h : EntryIsAll E F r e) (h' : EntryIsAll E F r e') (h1 : e.drawE = e'.drawE)
    (h2 : e.drawNZ = e'.drawNZ) (h3 : e.poss = e'.poss) (h4 : e.logN = e'.logN) :
    e.trits = e'.trits := by
  have hc := h.card_eq h'
  rw [h1, h2, h3, h4] at hc
  have c1 := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega)) hc
  have c2 := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega)) c1
  have c3 := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (Nat.pow_pos (by omega))) c2
  exact Nat.pow_right_injective (by omega) c3

/-- Two entries of one round that agree in drawE, drawNZ, logN and trits agree in poss, if positions
are drawn from more than one. -/
theorem EntryIsAll.poss_eq (hq : 2 < Nat.card E) {r : Round} {e e' : Fmt.Entry}
    (h : EntryIsAll E F r e) (h' : EntryIsAll E F r e') (h1 : e.drawE = e'.drawE)
    (h2 : e.drawNZ = e'.drawNZ) (h3 : e.logN = e'.logN) (h4 : e.trits = e'.trits)
    (hl : 0 < e.logN) : e.poss = e'.poss := by
  have hc := h.card_eq h'
  rw [h1, h2, ← h3, h4] at hc
  have c1 := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega)) hc
  have c2 := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega)) c1
  have c3 := Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by omega)) c2
  have two : 2 ≤ 2 ^ e.logN := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ e.logN := Nat.pow_le_pow_right (by omega) hl
  exact Nat.pow_right_injective two c3

/-- Two entries of one round that agree in drawE, drawNZ, poss and trits agree in logN, if a
position
is drawn. -/
theorem EntryIsAll.logN_eq (hq : 2 < Nat.card E) {r : Round} {e e' : Fmt.Entry}
    (h : EntryIsAll E F r e) (h' : EntryIsAll E F r e') (h1 : e.drawE = e'.drawE)
    (h2 : e.drawNZ = e'.drawNZ) (h3 : e.poss = e'.poss) (h4 : e.trits = e'.trits)
    (hp : 0 < e.poss) : e.logN = e'.logN := by
  have hc := h.card_eq h'
  rw [h1, h2, ← h3, h4] at hc
  have c1 := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega)) hc
  have c2 := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by omega)) c1
  have c3 := Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by omega)) c2
  rw [← pow_mul, ← pow_mul] at c3
  have c4 := Nat.pow_right_injective (le_refl 2) c3
  exact Nat.eq_of_mul_eq_mul_right hp c4

/-- Two entries of one round that agree in poss, logN and trits agree in drawE and in drawNZ. -/
theorem EntryIsAll.draws_eq (hq : 2 < Nat.card E) {r : Round} {e e' : Fmt.Entry}
    (h : EntryIsAll E F r e) (h' : EntryIsAll E F r e') (h1 : e.poss = e'.poss)
    (h2 : e.logN = e'.logN) (h3 : e.trits = e'.trits) :
    e.drawE = e'.drawE ∧ e.drawNZ = e'.drawNZ := by
  have hc := h.card_eq h'
  rw [h1, h2, h3] at hc
  have hx : 0 < (2 ^ e'.logN) ^ e'.poss * 4 ^ e'.trits :=
    Nat.mul_pos (Nat.pow_pos (Nat.pow_pos Nat.zero_lt_two)) (Nat.pow_pos (by omega))
  have hc' : Nat.card E ^ (e.drawE - e.drawNZ) * (Nat.card E - 1) ^ e.drawNZ *
        ((2 ^ e'.logN) ^ e'.poss * 4 ^ e'.trits) =
      Nat.card E ^ (e'.drawE - e'.drawNZ) * (Nat.card E - 1) ^ e'.drawNZ *
        ((2 ^ e'.logN) ^ e'.poss * 4 ^ e'.trits) := by
    rw [mul_assoc, mul_assoc]
    exact hc
  have c1 := Nat.eq_of_mul_eq_mul_right hx hc'
  obtain ⟨a, b⟩ := pow_mul_pow_inj hq c1
  have l1 := h.2.1
  have l2 := h'.2.1
  exact ⟨by omega, b⟩

omit [Finite E] in
/-- Two entries of one round with the same number of roots have the same number of bytes, if an
element of E has the size of three elements of F. -/
theorem EntryIsAll.msg_eq [Finite F] (hF : 2 ≤ Nat.card F) (hEF : Nat.card E = Nat.card F ^ 3)
    {r : Round} {e e' : Fmt.Entry} (h : EntryIsAll E F r e) (h' : EntryIsAll E F r e')
    (hr : e.roots = e'.roots) : e.msg = e'.msg := by
  obtain ⟨⟨k, w, ⟨f⟩, hk⟩, _⟩ := h
  obtain ⟨⟨k', w', ⟨f'⟩, hk'⟩, _⟩ := h'
  have hc := Nat.card_congr (f.symm.trans f')
  rw [Nat.card_prod, Nat.card_prod, card_fun, card_fun, card_fun, card_fun, hEF, ← pow_mul, ←
      pow_mul,
    ← pow_add, ← pow_add] at hc
  have := Nat.pow_right_injective hF hc
  omega

omit [Finite E] in
/-- Two entries of one round have both no root or both some. -/
theorem EntryIsAll.roots_zero_iff {r : Round} {e e' : Fmt.Entry} (h : EntryIsAll E F r e)
    (h' : EntryIsAll E F r e') : e.roots = 0 ↔ e'.roots = 0 :=
  h.2.2.2.symm.trans h'.2.2.2

end

/-! ## Where the narrow definition speaks, the wide one says the same of the draws -/

section
variable {E : Type} (F : Type) [Zero E] [Finite E]

instance (plain nonzero positions logSize matrixEntries : ℕ) :
    Finite (DrawSet E plain nonzero positions logSize matrixEntries) := by
  unfold DrawSet
  infer_instance

/-- A round that is the round of an entry in the narrow sense (OnBytes/G4/RoundIs.lean) is so in the
wide
sense, if the entry has no root, no position and no matrix entry. -/
theorem EntryIs.toAll {r : Round} {e : Fmt.Entry} (h : EntryIs E r e) (h0 : e.roots = 0)
    (h1 : e.poss = 0) (h2 : e.trits = 0) : EntryIsAll E F r e := by
  obtain ⟨s, ⟨⟨f⟩, ⟨g⟩, hpos⟩, hm, hE, hZ⟩ := h
  have hcard := Nat.card_congr g
  rw [card_drawT] at hcard
  have hposc : 0 < Nat.card r.Chal := Nat.card_pos
  have hcases : s.drawNZ = 0 ∨ (s.drawNZ = 1 ∧ s.drawE = 1) := by
    by_cases a : s.drawNZ = 0
    · exact Or.inl a
    · rw [if_neg a] at hcard
      by_cases b : s.drawNZ = 1 ∧ s.drawE = 1
      · exact Or.inr b
      · rw [if_neg b] at hcard
        omega
  refine ⟨⟨s.scalars, 0, ⟨f.trans (Equiv.prodUnique _ _).symm⟩, by omega⟩, ?_, ?_, ⟨fun _ => h0, fun
      _ => hpos⟩⟩
  · rcases hcases with a | ⟨a, b⟩ <;> omega
  · haveI : Finite r.Chal := Finite.of_fintype _
    rw [← Finite.card_eq, card_drawSet, hcard, hE, hZ, h1, h2]
    rcases hcases with a | ⟨a, b⟩
    · simp [a]
    · simp [a, b]

end

/-! ## It counts -/

section
variable {E F : Type} [Zero E] [Finite E] [Finite F]

/-- For a round with a finite plain part, to be the round of an entry is a matter of two sizes, of
equations between numbers, and of whether there is an oracle position. -/
theorem entryIsAll_iff_card {r : Round} [Finite r.Plain] {e : Fmt.Entry} :
    EntryIsAll E F r e ↔
      (∃ scalars words : ℕ, Nat.card r.Plain = Nat.card E ^ scalars * Nat.card F ^ words ∧
        e.msg = 32 * e.roots + 24 * scalars + 8 * words) ∧
      e.drawNZ ≤ e.drawE ∧
      Nat.card r.Chal = Nat.card E ^ (e.drawE - e.drawNZ) * ((Nat.card E - 1) ^ e.drawNZ *
        ((2 ^ e.logN) ^ e.poss * 4 ^ e.trits)) ∧
      (IsEmpty r.Pos ↔ e.roots = 0) := by
  haveI : Finite r.Chal := Finite.of_fintype _
  unfold EntryIsAll
  simp only [← Finite.card_eq, card_drawSet, Nat.card_prod, card_fun]

end

/-! ## It is met -/

section
variable (E F : Type) [Zero E] [Zero F] [Fintype E]

/-- The round without an oracle part that sends so many elements of E and of F and draws from the
given set. one: an element of E that is not 0. -/
noncomputable def bareRoundAll (scalars words plain nonzero positions logSize matrixEntries : ℕ)
    (one : {x : E // x ≠ 0}) : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ p => p.elim
  Plain := (Fin scalars → E) × (Fin words → F)
  Chal := DrawSet E plain nonzero positions logSize matrixEntries
  dOrc := ()
  dPlain := (fun _ => 0, fun _ => 0)
  finChalT := fun _ => by
    classical
    unfold DrawSet
    exact inferInstance
  neChal := ⟨(fun _ => 0, fun _ => one, fun _ => ⟨0, Nat.pow_pos (by omega)⟩, fun _ => (false,
      false))⟩

/-- That round is the round of every entry with its numbers and without a root. -/
theorem entryIsAll_bareRoundAll (scalars words plain nonzero positions logSize matrixEntries : ℕ)
    (one : {x : E // x ≠ 0}) (e : Fmt.Entry) (h0 : e.roots = 0)
    (h1 : e.msg = 24 * scalars + 8 * words) (h2 : e.drawE = plain + nonzero) (h3 : e.drawNZ =
        nonzero)
    (h4 : e.poss = positions) (h5 : e.logN = logSize) (h6 : e.trits = matrixEntries) :
    EntryIsAll E F
      (bareRoundAll E F scalars words plain nonzero positions logSize matrixEntries one) e := by
  refine ⟨⟨scalars, words, ⟨Equiv.refl _⟩, by omega⟩, by omega, ?_, ?_⟩
  · rw [h2, h3, h4, h5, h6, Nat.add_sub_cancel]
    exact ⟨Equiv.refl _⟩
  · exact ⟨fun _ => h0, fun _ => inferInstanceAs (IsEmpty Empty)⟩

/-- The same round with an oracle part of one position. -/
noncomputable def rootRoundAll (scalars words plain nonzero positions logSize matrixEntries : ℕ)
    (one : {x : E // x ≠ 0}) : Round :=
  { bareRoundAll E F scalars words plain nonzero positions logSize matrixEntries one with
    Orc := E
    Pos := Unit
    Sym := fun _ => E
    rd := fun o _ => o
    dOrc := 0 }

/-- That round is the round of every entry with its numbers and with a root or more. -/
theorem entryIsAll_rootRoundAll (scalars words plain nonzero positions logSize matrixEntries : ℕ)
    (one : {x : E // x ≠ 0}) (e : Fmt.Entry) (h0 : e.roots ≠ 0)
    (h1 : e.msg = 32 * e.roots + 24 * scalars + 8 * words) (h2 : e.drawE = plain + nonzero)
    (h3 : e.drawNZ = nonzero) (h4 : e.poss = positions) (h5 : e.logN = logSize)
    (h6 : e.trits = matrixEntries) :
    EntryIsAll E F
      (rootRoundAll E F scalars words plain nonzero positions logSize matrixEntries one) e := by
  refine ⟨⟨scalars, words, ⟨Equiv.refl _⟩, h1⟩, by omega, ?_, ?_⟩
  · rw [h2, h3, h4, h5, h6, Nat.add_sub_cancel]
    exact ⟨Equiv.refl _⟩
  · exact ⟨fun h => (h.false ()).elim, fun h => absurd h h0⟩

end

/-! ## At the two fields of the protocol -/

/-- An element of the challenge field has the size of three elements of the base field. -/
theorem card_gl_cube : Nat.card Cb.Gl.E = Nat.card Cb.Gl.F ^ 3 := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Cb.Gl.gl_card.2.1, Cb.Gl.gl_card.1]

/-- The base field has two elements or more. -/
theorem two_le_card_gl_base : 2 ≤ Nat.card Cb.Gl.F := by
  have h := two_lt_card_gl
  rw [card_gl_cube] at h
  by_contra hlt
  have h1 : Nat.card Cb.Gl.F ≤ 1 := by omega
  have h2 : Nat.card Cb.Gl.F ^ 3 ≤ 1 ^ 3 := Nat.pow_le_pow_left h1 3
  omega

end OnBytes.G4

#print axioms OnBytes.G4.EntryIsAll.card_chal
#print axioms OnBytes.G4.EntryIsAll.trits_eq
#print axioms OnBytes.G4.EntryIsAll.poss_eq
#print axioms OnBytes.G4.EntryIsAll.logN_eq
#print axioms OnBytes.G4.EntryIsAll.draws_eq
#print axioms OnBytes.G4.EntryIsAll.msg_eq
#print axioms OnBytes.G4.EntryIsAll.roots_zero_iff
#print axioms OnBytes.G4.EntryIs.toAll
#print axioms OnBytes.G4.entryIsAll_iff_card
#print axioms OnBytes.G4.entryIsAll_bareRoundAll
#print axioms OnBytes.G4.entryIsAll_rootRoundAll
#print axioms OnBytes.G4.card_gl_cube
#print axioms OnBytes.G4.two_le_card_gl_base
