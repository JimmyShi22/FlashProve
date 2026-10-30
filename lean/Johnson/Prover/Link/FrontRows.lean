-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FrontRows.lean: the rows behind the link's five rounds, FORWARD: if seven
clauses hold of a message on the group's tables, every row holds of it, and so does their sum under
the powers of any element. Statements and proofs, in the library's typed terms.

OnBytes/Slice/BatSemRec.lean's rows_back_semR draws, out of "all rows hold of w", the facts that the
library's last joint of the link asks. This file goes the other way, by the same lemmas (val_split,
sum_bool_at, ldForm_push).

  Covers N        every number below N.n is some row's
  FrontTrue x μ   seven clauses: μ is 0 on the rows that no member has · each member's share has the
                  sample's answer · each fold's message part has its OOD sample's folded answers ·
                  each fold's code word has at each drawn location what was read there · the two
                  folds agree, under eq(φ, ·), on the entries that are compared
  rows_fwd_semR   IsRowsR · Covers · FrontTrue ⟹ ∑ j, vs b j * μ j = tg b at every b < N.n
  holds_sumStmR   so (Slf.idf).Holds (sumStmR N t tg vs θ) μ AT EVERY θ
  covers_port     the program's numbering covers, where the answers' numbering is onto

Not shown here. That any prover's message meets FrontTrue. That a program's or a description's
rows meet IsRowsR (OnBytes/Slice/RowsXRec.lean and the files that its head names). Nothing on a
decision, a view, a file or a hash function; nothing on soundness; nothing on what any entry of a
message discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BatSemRec

set_option autoImplicit false

namespace Johnson.Prover.Link
open OnBytes.Slice Cb Cb.Ood Iop Run

variable {S : Sz} {Z : Sample GE S.En}

/-- Every number below N.n is some row's. -/
def Covers (N : RowNo S Z) : Prop :=
  ∀ b, b < N.n → b = N.eq ∨ (∃ a, b = N.sm a) ∨ (∃ i, b = N.c0 i) ∨ (∃ i, b = N.c1 i) ∨
    ∃ a s, b = N.rc a s

/-- **The seven clauses.** -/
structure FrontTrue (t : ℕ) (x : (S.lkR Z).X4) (μ : (S.sg t).cIn.J → GE) : Prop where
  free : FreeZero S t μ
  sm : ∀ a : Bool, ∑ j, (S.fam.om a).Z.mat (x.1.1.2 a).1 () j * μ (atJ S t a j) = (x.1.1.2 a).2 ()
  rc0 : ∀ s : Z.S, ∑ j, Z.mat x.1.1.1.1.1.1 s j * μ (atJ S t false (S.putAt ((S.ixR Z).pl j))) =
    (S.ixR Z).tgt x.1.1.1.1.1 x.1.1.1.2 s
  rc1 : ∀ s : Z.S, ∑ j, Z.mat x.1.1.1.1.2.1 s j * μ (atJ S t true (S.putAt ((S.ixR Z).pl j))) =
    (S.ixR Z).tgt x.1.1.1.1.2 x.1.1.1.2 s
  c0 : ∀ i : Fin S.P.nu0,
    ∑ k, (S.ixR Z).G (x.1.2.1.1 i) k * μ (atJ S t false (S.putAt k)) = x.1.2.1.2 i
  c1 : ∀ i : Fin S.P.nuj,
    ∑ k, (S.ixR Z).G (x.1.2.2.1 i) k * μ (atJ S t true (S.putAt k)) = x.1.2.2.2 i
  eq : ∑ a : S.Lay, Alg.eqk x.2 ((S.lwR Z).pl a) *
    (μ (atJ S t false (S.putAt ((S.ixR Z).pl ((S.lwR Z).lay a)))) -
      μ (atJ S t true (S.putAt ((S.ixR Z).pl ((S.lwR Z).lay a))))) = 0

/-- **Every row holds.** -/
theorem rows_fwd_semR (N : RowNo S Z) (t : ℕ) (x : (S.lkR Z).X4) (tg : ℕ → GE)
    (vs : ℕ → (S.sg t).cIn.J → GE) (hr : IsRowsR S Z t N x tg vs) (hN : Covers N)
    (μ : (S.sg t).cIn.J → GE) (h : FrontTrue t x μ) (b : ℕ) (hb : b < N.n) :
    ∑ j, vs b j * μ j = tg b := by
  have hval : ∀ a : Bool, ∑ j, vs b j * μ j =
      ∑ j : S.MJ, vs b (atJ S t a j) * μ (atJ S t a j) +
        ∑ j : S.MJ, vs b (atJ S t (!a) j) * μ (atJ S t (!a) j) := fun a => by
    rw [← sum_bool_at a fun a => ∑ j : S.MJ, vs b (atJ S t a j) * μ (atJ S t a j),
      ← val_split S t (vs b) μ (hr.mask b) h.free]
  have hpush : ∀ (a : Bool) {St I : Type} [Fintype I] (φ : I → ((S.lkR Z).N.om a).C.J)
      (c : St → I → GE) (st : St),
      ∑ j, Slf.push φ c st j * μ (atJ S t a j) = ∑ i, c st i * μ (atJ S t a (φ i)) :=
    fun a St I _ φ c st =>
      ldForm_push GE St I ((S.lkR Z).N.om a).C.J φ c st fun j => μ (atJ S t a j)
  rcases hN b hb with rfl | ⟨a, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨a, s, rfl⟩
  · -- the equality row
    have e0 : ∑ j : S.MJ, vs N.eq (atJ S t false j) * μ (atJ S t false j) =
        ∑ a : S.Lay, Alg.eqk x.2 ((S.lwR Z).pl a) *
          μ (atJ S t false (S.putAt ((S.ixR Z).pl ((S.lwR Z).lay a)))) :=
      (Finset.sum_congr rfl fun j _ => by rw [hr.eq0 j]; rfl).trans
        (hpush false (fun a => S.putAt ((S.ixR Z).pl ((S.lwR Z).lay a)))
          (fun φ a => Alg.eqk φ ((S.lwR Z).pl a)) x.2)
    have e1 : ∑ j : S.MJ, vs N.eq (atJ S t (!false) j) * μ (atJ S t (!false) j) =
        -∑ a : S.Lay, Alg.eqk x.2 ((S.lwR Z).pl a) *
          μ (atJ S t true (S.putAt ((S.ixR Z).pl ((S.lwR Z).lay a)))) := by
      rw [← hpush true (fun a => S.putAt ((S.ixR Z).pl ((S.lwR Z).lay a)))
        (fun φ a => Alg.eqk φ ((S.lwR Z).pl a)) x.2, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by
        rw [show vs N.eq (atJ S t (!false) j) = _ from hr.eq1 j, neg_mul]; rfl
    rw [hval false, e0, e1, hr.eqT, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
    exact (Finset.sum_congr rfl fun a _ => (mul_sub _ _ _).symm).trans h.eq
  · -- a member's sample row
    have hz : ∑ j : S.MJ, vs (N.sm a) (atJ S t (!a) j) * μ (atJ S t (!a) j) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hr.smO a j, zero_mul]
    rw [hval a, hz, add_zero, hr.smT a]
    exact (Finset.sum_congr rfl fun j _ => by rw [hr.smS a j]).trans (h.sm a)
  · -- the first table's draws
    have hz : ∑ j : S.MJ, vs (N.c0 i) (atJ S t (!false) j) * μ (atJ S t (!false) j) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [show vs (N.c0 i) (atJ S t (!false) j) = 0 from hr.c0O i j, zero_mul]
    rw [hval false, hz, add_zero, hr.c0T i]
    refine Eq.trans ?_ (h.c0 i)
    refine Eq.trans ?_ (hpush false S.putAt (fun x k => (S.ixR Z).G x k) (x.1.2.1.1 i))
    exact Finset.sum_congr rfl fun j _ => by rw [hr.c0S i j]; rfl
  · -- the copy's draws
    have hz : ∑ j : S.MJ, vs (N.c1 i) (atJ S t (!true) j) * μ (atJ S t (!true) j) = 0 :=
      Finset.sum_eq_zero fun j _ => by
        rw [show vs (N.c1 i) (atJ S t (!true) j) = 0 from hr.c1O i j, zero_mul]
    rw [hval true, hz, add_zero, hr.c1T i]
    refine Eq.trans ?_ (h.c1 i)
    refine Eq.trans ?_ (hpush true S.putAt (fun x k => (S.ixR Z).G x k) (x.1.2.2.1 i))
    exact Finset.sum_congr rfl fun j _ => by rw [hr.c1S i j]; rfl
  · -- an OOD sample's row
    cases a
    · have hz : ∑ j : S.MJ, vs (N.rc false s) (atJ S t (!false) j) * μ (atJ S t (!false) j) = 0 :=
        Finset.sum_eq_zero fun j _ => by
          rw [show vs (N.rc false s) (atJ S t (!false) j) = 0 from hr.r0O s j, zero_mul]
      rw [hval false, hz, add_zero, hr.r0T s]
      refine Eq.trans ?_ (h.rc0 s)
      refine Eq.trans ?_ (hpush false (fun j => S.putAt ((S.ixR Z).pl j))
        (fun ρ j => Z.mat ρ s j) x.1.1.1.1.1.1)
      exact Finset.sum_congr rfl fun j _ => by rw [hr.r0S s j]; rfl
    · have hz : ∑ j : S.MJ, vs (N.rc true s) (atJ S t (!true) j) * μ (atJ S t (!true) j) = 0 :=
        Finset.sum_eq_zero fun j _ => by
          rw [show vs (N.rc true s) (atJ S t (!true) j) = 0 from hr.r1O s j, zero_mul]
      rw [hval true, hz, add_zero, hr.r1T s]
      refine Eq.trans ?_ (h.rc1 s)
      refine Eq.trans ?_ (hpush true (fun j => S.putAt ((S.ixR Z).pl j))
        (fun ρ j => Z.mat ρ s j) x.1.1.1.1.2.1)
      exact Finset.sum_congr rfl fun j _ => by rw [hr.r1S s j]; rfl

/-- **The rows' sum under the powers of any element holds.** -/
theorem holds_sumStmR (N : RowNo S Z) (t : ℕ) (x : (S.lkR Z).X4) (tg : ℕ → GE)
    (vs : ℕ → (S.sg t).cIn.J → GE) (hr : IsRowsR S Z t N x tg vs) (hN : Covers N)
    (μ : (S.sg t).cIn.J → GE) (h : FrontTrue t x μ) (θ : GE) :
    (Slf.idf (E := GE) (J := (S.sg t).cIn.J)).Holds (sumStmR N t tg vs θ) μ := by
  show ∑ j, (∑ b : Fin N.n, vs b.val j * θ ^ b.val) * μ j = ∑ b : Fin N.n, θ ^ b.val * tg b.val
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← rows_fwd_semR N t x tg vs hr hN μ h b.val b.isLt, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The program's numbering covers, where the answers' numbering is onto. -/
theorem covers_port (s : ℕ) (num : Z.S → Fin s) (hnum : Function.Surjective num) :
    Covers (RowNo.port S Z s num) := by
  intro b hb
  have hb' : b < 2 * s + 3 + (S.P.nu0 + S.P.nuj) := hb
  by_cases h1 : b < s
  · obtain ⟨σ, hσ⟩ := hnum ⟨b, h1⟩
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨false, σ, ?_⟩)))
    show b = (if false = true then s else 0) + (num σ).val
    rw [hσ]; simp
  by_cases h2 : b < 2 * s
  · obtain ⟨σ, hσ⟩ := hnum ⟨b - s, by omega⟩
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨true, σ, ?_⟩)))
    show b = (if true = true then s else 0) + (num σ).val
    rw [hσ]; simp; omega
  by_cases h3 : b = 2 * s
  · exact Or.inl h3
  by_cases h4 : b = 2 * s + 1
  · exact Or.inr (Or.inl ⟨false, by show b = 2 * s + 1 + false.toNat; simpa using h4⟩)
  by_cases h5 : b = 2 * s + 2
  · exact Or.inr (Or.inl ⟨true, by show b = 2 * s + 1 + true.toNat; simpa using h5⟩)
  by_cases h6 : b < 2 * s + 3 + S.P.nu0
  · exact Or.inr (Or.inr (Or.inl ⟨⟨b - (2 * s + 3), by omega⟩, by
      show b = 2 * s + 3 + (b - (2 * s + 3)); omega⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨b - (2 * s + 3 + S.P.nu0), by omega⟩, by
      show b = 2 * s + 3 + S.P.nu0 + (b - (2 * s + 3 + S.P.nu0)); omega⟩)))

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.Covers
#print axioms Johnson.Prover.Link.FrontTrue
#print axioms Johnson.Prover.Link.rows_fwd_semR
#print axioms Johnson.Prover.Link.holds_sumStmR
#print axioms Johnson.Prover.Link.covers_port
