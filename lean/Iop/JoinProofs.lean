-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/JoinProofs.lean: lemmas on two consecutive rounds that are merged into one, by (J1) (two prover
messages as one) or (J2) (two challenges as one) of Iop/Join.lean. Iop/RecutProofs.lean uses them.
(Words of this library: lean/GLOSSARY.md.)

As in Iop/SplitProofs.lean. A transcript that begins with a merged round is mapped to a transcript
with the two rounds (`Tr.unMsg`, `Tr.unChal`). Verifier randomness, plain parts and answers of
oracles commute with that map (answers at (J2): for a second round without positions, `noPos`).
Soundness. (J2): a pair (c1, c2) lets a doomed prover escape only if c1 does (at most e1 values,
each with card C2 partners), or c1 does not and c2 does after the one second message (at most e2
values for each of the card C1 values of c1): `Prob.cnt_two_rounds_le`. (J1): the same count over
pairs bounds the count over c2 at the one value u of c1.
Notation: `cnt P : ℕ` (Prob/Cnt.lean): the number of elements of a finite type with the property P;
`Err s : Type` (Iop/Rbr.lean): one number for each round; in `Doomed s ε bad` (there), how many
values of the challenge may lead from a doomed transcript to one that is not doomed;
`Doomed s ε bad : Prop` (there): the empty transcript is doomed with respect to `bad` (a property of
full transcripts, bad for the prover): whatever the prover sends, at most e values of the next
challenge lead to a transcript that is not doomed; at the end, `bad` holds; `Err.Below ε c : Prop`
(Iop/InteractiveOracleProof.lean): every error of the list, as a probability, is at most c, for a round r with the
error e: `(e : ℝ≥0∞) ≤ c * (Fintype.card r.Chal : ℝ≥0∞)`; types of Iop/Shape.lean: `Tr s`: full
transcripts; `Rho s`: the verifier's randomness of a whole execution; `Plains s`: the plain parts of
all prover messages; `OPos s`: positions of all prover oracles; `OSym s p`: the alphabet at a
position; `τ.read p` (`Tr.read`, there): the answer to a query to a prover oracle; e1, e2, C1, C2:
in `Doomed.two`, `e1 e2 : ℕ` are the first two entries of the list of errors `(e1, e2, ε)`, and C1,
C2 are `r1.Chal`, `r2.Chal`; `e1 e2 n1 n2 w d : ℕ`, `c b1 b2 : ℝ≥0∞` in section 3: arguments of
`two_le`, `two_sum`, `two_le'`; what is asked of them: `h1`, `h2`.
-/
import Iop.Join
import Prob.Count

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. One step -/

section OneStep
variable {r1 r2 : Round} {s : Shape}

theorem Tr.rho_unMsg (u : r1.Chal) (z : Tr (r1.joinMsg r2 :: s)) :
    (Tr.unMsg u z).rho = (u, (z.rho : Rho (r1.joinMsg r2 :: s))) := by
  obtain ⟨m, c, t⟩ := z
  rfl

theorem Tr.rho_unChal (z : Tr (r1.joinChal r2 :: s)) :
    (Tr.unChal z).rho =
      ((z.rho : Rho (r1.joinChal r2 :: s)).1.1,
        (z.rho : Rho (r1.joinChal r2 :: s)).1.2,
        (z.rho : Rho (r1.joinChal r2 :: s)).2) := by
  obtain ⟨m, c, t⟩ := z
  rfl

theorem Tr.plains_unMsg (u : r1.Chal) (z : Tr (r1.joinMsg r2 :: s)) :
    (Tr.unMsg u z).plains =
      ((z.plains : Plains (r1.joinMsg r2 :: s)).1.1,
        (z.plains : Plains (r1.joinMsg r2 :: s)).1.2,
        (z.plains : Plains (r1.joinMsg r2 :: s)).2) := by
  obtain ⟨m, c, t⟩ := z
  rfl

theorem Tr.plains_unChal (z : Tr (r1.joinChal r2 :: s)) :
    (Tr.unChal z).plains =
      ((z.plains : Plains (r1.joinChal r2 :: s)).1,
        r2.dPlain,
        (z.plains : Plains (r1.joinChal r2 :: s)).2) := by
  obtain ⟨m, c, t⟩ := z
  rfl

theorem Tr.read_unMsg (u : r1.Chal) (z : Tr (r1.joinMsg r2 :: s)) : ∀ p : OPos (r1.joinMsg r2 :: s),
    (Tr.unMsg u z).read (OPos.unMsg r1 r2 s p) = OSym.unMsg p (z.read p) := by
  obtain ⟨m, c, t⟩ := z
  rintro ((_ | _) | _) <;> rfl

theorem Tr.read_unChal (noPos : r2.Pos → Empty) (z : Tr (r1.joinChal r2 :: s)) :
    ∀ p : OPos (r1.joinChal r2 :: s),
      (Tr.unChal z).read (OPos.unChal r1 r2 s noPos p) = OSym.unChal noPos p (z.read p) := by
  obtain ⟨m, c, t⟩ := z
  rintro (_ | _) <;> rfl

theorem OSym.reMsg_unMsg :
    ∀ (p : OPos (r1.joinMsg r2 :: s)) (a : OSym (r1.joinMsg r2 :: s) p),
      OSym.reMsg p (OSym.unMsg p a) = a
  | .inl (.inl _), _ => rfl
  | .inl (.inr _), _ => rfl
  | .inr _, _ => rfl

theorem OSym.reChal_unChal (noPos : r2.Pos → Empty) :
    ∀ (p : OPos (r1.joinChal r2 :: s)) (a : OSym (r1.joinChal r2 :: s) p),
      OSym.reChal noPos p (OSym.unChal noPos p a) = a
  | .inl _, _ => rfl
  | .inr _, _ => rfl

end OneStep








/-! ## 2. Soundness -/

/-- A count over pairs bounds the count at one value of the first coordinate. -/
theorem cnt_slice_le {C D : Type} [Fintype C] [Fintype D] (P : C × D → Prop) (u : C) :
    cnt (fun d => P (u, d)) ≤ cnt P := by
  rw [cnt_prod_eq_sum P]
  exact Finset.single_le_sum
    (f := fun c => cnt fun d => P (c, d)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)

theorem Doomed.two {r1 r2 : Round} {s : Shape} {e1 e2 : ℕ} {ε : Err s}
    {bad : Tr (r1 :: r2 :: s) → Prop} (h : Doomed (r1 :: r2 :: s) (e1, e2, ε) bad)
    (m1 : r1.Msg) (m2 : r2.Msg) :
    cnt (fun x : r1.Chal × r2.Chal => ¬ Doomed s ε (fun τ => bad (m1, x.1, m2, x.2, τ))) ≤
      e1 * Fintype.card r2.Chal + Fintype.card r1.Chal * e2 :=
  cnt_two_rounds_le _ (fun c1 => ¬ Doomed (r2 :: s) (e2, ε) (fun τ => bad (m1, c1, τ))) e1 e2
    (h m1) fun _ hc => (not_not.1 hc) m2


/-! ## 3. Bounds on the new errors -/

theorem card_eq_one_of_forall {C : Type} [Fintype C] {u : C} (h : ∀ c, c = u) :
    Fintype.card C = 1 :=
  Fintype.card_eq_one_iff.2 ⟨u, h⟩

theorem eq_zero_of_below {e : ℕ} {c : ℝ≥0∞} (hc : c < 1) {n : ℕ}
    (hn : n = 1) (h : (e : ℝ≥0∞) ≤ c * (n : ℝ≥0∞)) : e = 0 := by
  subst hn
  by_contra he
  have h1 : (1 : ℝ≥0∞) ≤ (e : ℝ≥0∞) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 he
  rw [Nat.cast_one, mul_one] at h
  exact absurd (lt_of_le_of_lt (h1.trans h) hc) (lt_irrefl _)

theorem Err.Below.weaken :
    ∀ {s : Shape} {ε : Err s} {c c' : ℝ≥0∞}, c ≤ c' → Err.Below ε c → Err.Below ε c'
  | [], _, _, _, _, _ => trivial
  | _ :: _, (_, _), _, _, hc, h => ⟨h.1.trans (mul_le_mul' hc le_rfl), Err.Below.weaken hc h.2⟩


theorem two_le {e1 e2 n1 n2 w : ℕ} {c : ℝ≥0∞}
    (h1 : (e1 : ℝ≥0∞) ≤ (w * c) * (n1 : ℝ≥0∞)) (h2 : (e2 : ℝ≥0∞) ≤ c * (n2 : ℝ≥0∞)) :
    ((e1 * n2 + n1 * e2 : ℕ) : ℝ≥0∞) ≤ (((w + 1 : ℕ) : ℝ≥0∞) * c) * ((n1 * n2 : ℕ) : ℝ≥0∞) := by
  push_cast
  calc
    (e1 : ℝ≥0∞) * n2 + n1 * e2 ≤ (w * c) * n1 * n2 + n1 * (c * n2) :=
      add_le_add (mul_le_mul' h1 le_rfl) (mul_le_mul' le_rfl h2)
    _ = (w + 1) * c * (n1 * n2) := by ring


/-! ### Two rounds with separate bounds b1 and b2: the merged round has b1 + b2 -/

theorem two_sum {e1 e2 n1 n2 : ℕ} {b1 b2 : ℝ≥0∞}
    (h1 : (e1 : ℝ≥0∞) ≤ b1 * (n1 : ℝ≥0∞)) (h2 : (e2 : ℝ≥0∞) ≤ b2 * (n2 : ℝ≥0∞)) :
    ((e1 * n2 + n1 * e2 : ℕ) : ℝ≥0∞) ≤ (b1 + b2) * ((n1 * n2 : ℕ) : ℝ≥0∞) := by
  push_cast
  calc
    (e1 : ℝ≥0∞) * n2 + n1 * e2 ≤ b1 * n1 * n2 + n1 * (b2 * n2) :=
      add_le_add (mul_le_mul' h1 le_rfl) (mul_le_mul' le_rfl h2)
    _ = (b1 + b2) * (n1 * n2) := by ring


/-! ### For a bound c < 1, only rounds whose challenge has more than one value count -/

theorem head_le {e n : ℕ} {c : ℝ≥0∞} (hc : c < 1) (h : (e : ℝ≥0∞) ≤ c * (n : ℝ≥0∞)) :
    (e : ℝ≥0∞) ≤ (((if n = 1 then 0 else 1 : ℕ) : ℝ≥0∞) * c) * (n : ℝ≥0∞) := by
  split_ifs with hn
  · obtain rfl := eq_zero_of_below hc hn h
    simp
  · simpa using h

theorem two_le' {e1 e2 n1 n2 w d : ℕ} {c : ℝ≥0∞} (h1 : (e1 : ℝ≥0∞) ≤ (w * c) * (n1 : ℝ≥0∞))
    (h2 : (e2 : ℝ≥0∞) ≤ (d * c) * (n2 : ℝ≥0∞)) :
    ((e1 * n2 + n1 * e2 : ℕ) : ℝ≥0∞) ≤ (((w + d : ℕ) : ℝ≥0∞) * c) * ((n1 * n2 : ℕ) : ℝ≥0∞) := by
  push_cast
  calc
    (e1 : ℝ≥0∞) * n2 + n1 * e2 ≤ (w * c) * n1 * n2 + n1 * ((d * c) * n2) :=
      add_le_add (mul_le_mul' h1 le_rfl) (mul_le_mul' le_rfl h2)
    _ = (w + d) * c * (n1 * n2) := by ring

/-! ## 4. Rounds whose oracle is a string -/

/-- Two rounds whose oracles are strings, merged by (J1), give a round whose oracle is a string. -/
def Round.IsPoint.joinMsg {r1 r2 : Round} (h1 : r1.IsPoint) (h2 : r2.IsPoint) :
    (r1.joinMsg r2).IsPoint where
  finPos := letI := h1.finPos; letI := h2.finPos; inferInstanceAs (Fintype (r1.Pos ⊕ r2.Pos))
  decPos := letI := h1.decPos; letI := h2.decPos; inferInstanceAs (DecidableEq (r1.Pos ⊕ r2.Pos))
  ofSyms := fun f => (h1.ofSyms fun p => f (.inl p), h2.ofSyms fun p => f (.inr p))
  rd_ofSyms := fun f p => match p with
    | .inl p => h1.rd_ofSyms (fun p => f (.inl p)) p
    | .inr p => h2.rd_ofSyms (fun p => f (.inr p)) p
  ofSyms_rd := fun o => Prod.ext (h1.ofSyms_rd o.1) (h2.ofSyms_rd o.2)
  zero := fun p => match p with
    | .inl p => h1.zero p
    | .inr p => h2.zero p

/-- A round whose oracle is a string, merged by (J2) with the next round, is again such a round. -/
def Round.IsPoint.joinChal {r1 : Round} (h1 : r1.IsPoint) (r2 : Round) : (r1.joinChal r2).IsPoint :=
  ⟨h1.finPos, h1.decPos, h1.ofSyms, h1.rd_ofSyms, h1.ofSyms_rd, h1.zero⟩





end Iop
