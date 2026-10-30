--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/LibBack.lean: THE WAY BACK, THE HEAD's OWN HALF: from the clauses on keys and
on the ledger's two lines of the library's field relation of the head with the cost ledger
(Policy/Rel/LedgerHead.lean: RF.keys, RF.jc), at the library's record made of the kind's cells
(cellsOf c X, Law/LibJoin.lean), to the five fields of the kind's relation on cells that speak of
keys and the field lines (HeadNormLaw.lean: CellRelH.top, mid, low, rowA, rowB, lines). Statements
and proofs. NO ACCEPTANCE OF ANY TEXT THAT RUNS IS CLAIMED.

Why. Law/LibJoin.lean's join leads from the kind's relation to the library's clauses: what soundness
spends; its head lists the converse under what it does not say. Whoever wants to show that honest
cells stand in the kind's relation needs the other way. That file's identities between integers
(K1_eq, K2_eq, top_eq, ex_eq, dB4_int, dZ_int) and Law/Values.lean's values of the five keys and the
two lines (rd_key_mid, rd_key_low, rd_key_top, rd_key_tableA, rd_key_tableB, rd_clip, rd_table) are
equations: here they are read backwards. No integer's range is wanted: a key that is read as a
number's image IS that image (Law/TableTie.lean: eq_natCast_of_rd).

Main names.
  mid_back, low_back, top_back, rowA_back, rowB_back   field by field.
  lines_back   at every position the two guests' corner values are 0 (K06Statement.lean's
    CornerGuests says the same).

Limits. ONE WAY: from the library's clauses to the kind's six fields. The field sums of CellRelH is
not spoken of. PREMISES, as in Law/LibJoin.lean's join: the facts on the plan (PlanFacts) · the test
on the request · the next token is a token · Same · Wide (NO PADDING: V = JV = 202048) · More ·
the kind's table is the library's EX on 16 bits. The weights are the kind's own (weightsOf c): that
they are an index's output matrix is not said. That cellsOf c X is what any committed integers spell
is not said. The full size alone. No chance in it.
Not claimed: anything on completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Kinds.Law.LibJoin
import Johnson.Desc.Kinds.Law.TableTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.HeadJoin

open Finset
open VerifiableInference.Desc.Kinds VerifiableInference.Desc.Kinds.Head
open Inst.Model (NormPar)

section Field
variable [Head.Sizes] [Head.Policy] [Head.Request] [Head.Token] {c : Law.Cells}
  {X : ℕ → ℕ → ℤ} {Y : Inst.Model.Head.Req} {np : NormPar}

/-- The middle digit of a margin. -/
theorem mid_back (P : Law.PlanFacts) (S : Same Y) (Wd : Wide)
    (R : Policy.LedgerHead.RF np (weightsOf c) Y (cellsOf c X)) :
    ∀ t, t < Norm.T → ∀ x, x < Head.JV →
      Law.InBits 16 (Law.keyAt c (Law.corner x t) .marginMid) := by
  intro t ht x hx
  have hi : t < 1024 := by rw [← S.T]; exact ht
  have hx' : x < 202048 := by rw [← Wd.JV]; exact hx
  have k := R.keys .HD1 x t hx' hi
  rw [key_cast] at k
  obtain ⟨n, hn, e⟩ := k
  have e0 : ((Inst.Model.Head.K1 (cellsOf c X) Y x t : ℤ) : Law.K) = (((n : ℕ) : ℤ) : Law.K) := e
  rw [K1_eq S Wd hx', Int.cast_natCast] at e0
  refine ⟨n, hn, Law.Came.eq_natCast_of_rd (Law.okE_keyAt _ _ _) ?_⟩
  rw [Law.rd_key_mid P hx ht]
  exact e0

/-- The low digit of a margin. -/
theorem low_back (P : Law.PlanFacts) (S : Same Y) (Wd : Wide)
    (R : Policy.LedgerHead.RF np (weightsOf c) Y (cellsOf c X)) :
    ∀ t, t < Norm.T → ∀ x, x < Head.JV →
      Law.InBits 8 (Law.keyAt c (Law.corner x t) .marginLow) := by
  intro t ht x hx
  have hi : t < 1024 := by rw [← S.T]; exact ht
  have hx' : x < 202048 := by rw [← Wd.JV]; exact hx
  have k := R.keys .HD2 x t hx' hi
  rw [key_cast] at k
  obtain ⟨n, hn, e⟩ := k
  have e0 : ((Inst.Model.Head.K2 (cellsOf c X) Y x t : ℤ) : Law.K) = (((n : ℕ) : ℤ) : Law.K) := e
  rw [K2_eq S Wd hx', Int.cast_natCast] at e0
  refine ⟨n, hn, Law.Came.eq_natCast_of_rd (Law.okE_keyAt _ _ _) ?_⟩
  rw [Law.rd_key_low P hx ht]
  exact e0

/-- What is left of a margin above its two lower digits. -/
theorem top_back (P : Law.PlanFacts) (hreq : Request.ok = true) (hy : Token.y < Head.V)
    (S : Same Y) (Wd : Wide) (M : More Y)
    (R : Policy.LedgerHead.RF np (weightsOf c) Y (cellsOf c X)) :
    ∀ t, t < Norm.T → ∀ x, x < Head.JV →
      Law.InBits 16 (Law.keyAt c (Law.corner x t) .marginTop) := by
  intro t ht x hx
  have hi : t < 1024 := by rw [← S.T]; exact ht
  have hx' : x < 202048 := by rw [← Wd.JV]; exact hx
  have k := R.keys .HD0 x t hx' hi
  rw [key_cast] at k
  obtain ⟨n, hn, e⟩ := k
  have e0 : ((Inst.Model.Head.mg (cellsOf c X) c.Wh Y x t -
      2 ^ 8 * Inst.Model.Head.K1 (cellsOf c X) Y x t -
      Inst.Model.Head.K2 (cellsOf c X) Y x t : ℤ) : Law.K) = ((2 ^ 23 * (n : ℤ) : ℤ) : Law.K) := e
  rw [top_eq S Wd M hx'] at e0
  refine ⟨n, hn, Law.Came.eq_natCast_of_rd (Law.okE_keyAt _ _ _) ?_⟩
  rw [Law.rd_key_top P hreq hy hx ht, e0, M.sh,
    inv_mul_eq_iff_eq_mul₀ (Law.two_pow_ne_zero _)]
  push_cast
  norm_num

/-- The middle digit with the value looked up at it: the table's first half. -/
theorem rowA_back (P : Law.PlanFacts) {tab : ℕ → ℕ} (S : Same Y) (Wd : Wide) (M : More Y)
    (htab : ∀ u, u < 2 ^ 16 → (tab u : ℤ) = Inst.Model.EX u)
    (R : Policy.LedgerHead.RF np (weightsOf c) Y (cellsOf c X)) :
    ∀ t, t < Norm.T → ∀ x, x < Head.len .tableA →
      Law.IsRow tab (Law.keyAt c (Law.corner x t) .tableA) := by
  intro t ht x hx
  have hi : t < 1024 := by rw [← S.T]; exact ht
  have hxa : x < Head.JVa := hx
  have hx0 : x < 131072 := by rw [← M.JVa]; exact hxa
  have hx' : x < 202048 := by omega
  have k := R.keys .HE0 x t hx0 hi
  rw [key_cast] at k
  obtain ⟨u, hu, e⟩ := k
  have hu' : u < 2 ^ 16 := hu
  have e0 : ((Inst.Model.Head.K1 (cellsOf c X) Y x t +
      2 ^ 16 * Inst.Model.Head.ex (cellsOf c X) x t : ℤ) : Law.K) =
      (((u : ℤ) + 2 ^ 16 * Inst.Model.EX u : ℤ) : Law.K) := e
  rw [K1_eq S Wd hx', ex_eq Wd, ← htab u hu'] at e0
  refine ⟨u, hu', Law.Came.eq_natCast_of_rd (Law.okE_keyAt _ _ _) ?_⟩
  rw [Law.rd_key_tableA P hxa ht, e0]
  push_cast
  rfl

/-- The same: the table's second half. -/
theorem rowB_back (P : Law.PlanFacts) {tab : ℕ → ℕ} (S : Same Y) (Wd : Wide) (M : More Y)
    (htab : ∀ u, u < 2 ^ 16 → (tab u : ℤ) = Inst.Model.EX u)
    (R : Policy.LedgerHead.RF np (weightsOf c) Y (cellsOf c X)) :
    ∀ t, t < Norm.T → ∀ x, x < Head.len .tableB →
      Law.IsRow tab (Law.keyAt c (Law.corner x t) .tableB) := by
  intro t ht x hx
  have hi : t < 1024 := by rw [← S.T]; exact ht
  have hxb : x < Head.JV - Head.JVa := hx
  have hx0 : x < 70976 := by
    have h := hxb
    rw [Wd.JV, M.JVa] at h
    omega
  have hx' : 131072 + x < 202048 := by omega
  have k := R.keys .HE1 x t hx0 hi
  rw [key_cast] at k
  obtain ⟨u, hu, e⟩ := k
  have hu' : u < 2 ^ 16 := hu
  have e0 : ((Inst.Model.Head.K1 (cellsOf c X) Y (131072 + x) t +
      2 ^ 16 * Inst.Model.Head.ex (cellsOf c X) (131072 + x) t : ℤ) : Law.K) =
      (((u : ℤ) + 2 ^ 16 * Inst.Model.EX u : ℤ) : Law.K) := e
  rw [K1_eq S Wd hx', ex_eq Wd, ← htab u hu'] at e0
  refine ⟨u, hu', Law.Came.eq_natCast_of_rd (Law.okE_keyAt _ _ _) ?_⟩
  rw [Law.rd_key_tableB P hxb ht, M.JVa, e0]
  push_cast
  rfl

/-- **At every position the two guests' corner values are 0.** -/
theorem lines_back (P : Law.PlanFacts) (S : Same Y) (Wd : Wide)
    (R : Policy.LedgerHead.RF np (weightsOf c) Y (cellsOf c X)) :
    ∀ t, t < Norm.T →
      Law.clipAt c (Law.corner 0 t) = 0 ∧ Law.tableAt c (Law.corner 0 t) = 0 := by
  intro t ht
  have hi : t < 1024 := by rw [← S.T]; exact ht
  obtain ⟨j1, j2⟩ := R.jc t hi
  have e1 : Inst.Model.Head.dB4 ((cellsOf c X).cast Law.K) Y t =
      ((Inst.Model.Head.dB4 (cellsOf c X) Y t : ℤ) : Law.K) :=
    (Inst.Model.Head.map_dB4 (Int.castRingHom Law.K) (cellsOf c X) Y t).symm
  have e2 : Inst.Model.Head.dZ ((cellsOf c X).cast Law.K) Y t =
      ((Inst.Model.Head.dZ (cellsOf c X) Y t : ℤ) : Law.K) :=
    (Inst.Model.Head.map_dZ (Int.castRingHom Law.K) (cellsOf c X) Y t).symm
  rw [e1, dB4_int S] at j1
  rw [e2, dZ_int S Wd] at j2
  refine ⟨Law.eq_of_rd (Law.okE_clipAt _ _) Law.okE_zero ?_,
    Law.eq_of_rd (Law.okE_tableAt _ _) Law.okE_zero ?_⟩
  · rw [Law.rd_clip ht, Law.rd_zero]
    by_cases hk : costed t = true
    · rw [if_pos hk] at j1 ⊢
      exact j1
    · rw [if_neg hk]
  · rw [Law.rd_table P ht, Law.rd_zero]
    by_cases hk : costed t = true
    · rw [if_pos hk] at j2 ⊢
      exact j2
    · rw [if_neg hk]

end Field

end VerifiableInference.Desc.Kinds.HeadJoin

#print axioms VerifiableInference.Desc.Kinds.HeadJoin.mid_back
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.low_back
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.top_back
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.rowA_back
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.rowB_back
#print axioms VerifiableInference.Desc.Kinds.HeadJoin.lines_back
