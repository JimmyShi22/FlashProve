-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/EndRows.lean: the single equations of a smallness test's ties and reads as
one list, each with its exponent; the exponents rise along the list.

Definitions, statements and proofs.
Main names:
  `Gap K`: what an equation lacks, as a function of the arrays' entries A t r c.
  `tieRow`, `readRow`: a single tie, a single equation of a read.
  `rowsTail ρ tl funs pc`: the list: the ties, matrix by matrix, then the reads in the order in
    which objectsF adds them. pc: the number of claims in the sub-proof's plan.
  `batchOf θ A L`: the rows of L added up under the powers of θ.
  `batch_rowsTail`: the batch of the list is the sum of all `tieEnd` and `readEnd`
    (OnBytes/Tie/Pv/Tail/EndAll.lean).
  `Rising`, `rising_rowsTail`, `bounds_rowsTail`: the exponents rise strictly, so no two are equal;
    each is at least pc and below pc plus the number of indices.
Limits: an equation is given as a function of the entries, not by its coefficients; these are in
OnBytes/Tie/Pv/Tail/Ends.lean.
-/
import OnBytes.Tie.Pv.Tail.EndAll
import OnBytes.Tie.Pv.Tail.EndIndex
import OnBytes.Tie.Pv.Tail.EndSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model

open Finset

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- What a single equation lacks, as a function of the arrays' entries A t r c. -/
abbrev Gap (K : Type) : Type := (Nat → Nat → Nat → K) → K

/-- The single tie of matrix mu, row i' of symbols, combination u. -/
def tieRow (tl : HTailF2) (mu : Nat) (i' : Fin (Alg.symRows (tl.shp.getD mu {}).m))
    (u : Fin tl.tau) : Gap K := fun A =>
  tieGap ((2 : ℤ) ^ 20) ((2 : K) ^ 10) ((2 : K) ^ 17) (thOf tl mu (tl.shp.getD mu {}).k)
    (fun i' c => A (tl.gtTree.getD mu 0) i' c)
    (fun u i => A tl.ix.ZZ u ((tl.zzCol mu 0 0).getD 0 + i))
    (fun u i => A tl.ix.ZZ u ((tl.zzCol mu 1 0).getD 0 + i)) u i'

/-- The single equation of the read x, combination u. -/
def readRow (tl : HTailF2) (x : HFun × Nat) (u : Fin tl.tau) : Gap K := fun A =>
  readGap (m := x.1.len) ((2 : K) ^ 10) ((2 : K) ^ 17)
    (thOf tl x.1.mat (tl.mats.getD x.1.mat {}).k)
    (fun j => ρ.val (x.1.phi.getD j zeroE)) (fun d => A (uOf tl x.1) 0 (posOf tl x.1 x.2 d))
    (fun u j => A tl.ix.ZZ u ((tl.zzCol x.1.mat 0 (x.2 * x.1.len)).getD 0 + j))
    (fun u j => A tl.ix.ZZ u ((tl.zzCol x.1.mat 1 (x.2 * x.1.len)).getD 0 + j)) u

/-- The ties of one matrix, each with its exponent. -/
def tieRowsAt (tl : HTailF2) (pc mu : Nat) : List (Nat × Gap K) :=
  (List.finRange (Alg.symRows (tl.shp.getD mu {}).m)).flatMap fun i' =>
    (List.finRange tl.tau).map fun u => (pc + eTie tl mu i'.val u.val, tieRow tl mu i' u)

/-- All ties. -/
def tieRows (tl : HTailF2) (pc : Nat) : List (Nat × Gap K) :=
  (List.range tl.NM).flatMap fun mu => tieRowsAt tl pc mu

/-- Rows for the members of a list, the first of which has the number q: tau rows for each, with
the exponents e and the equations g. -/
def rowsFrom {tau : Nat} (e : Nat → Nat → Nat) (g : HFun × Nat → Fin tau → Gap K) :
    Nat → List (HFun × Nat) → List (Nat × Gap K)
  | _, [] => []
  | q, x :: l => ((List.finRange tau).map fun u => (e q u.val, g x u)) ++ rowsFrom e g (q + 1) l

/-- The equations of the reads of a list, the first of which has the number q. -/
def readRowsFrom (tl : HTailF2) (pc q : Nat) (l : List (HFun × Nat)) : List (Nat × Gap K) :=
  rowsFrom (fun q u => pc + eRead tl q u) (readRow ρ tl) q l

theorem readRowsFrom_cons (tl : HTailF2) (pc q : Nat) (x : HFun × Nat) (l : List (HFun × Nat)) :
    readRowsFrom ρ tl pc q (x :: l) =
      ((List.finRange tl.tau).map fun u => (pc + eRead tl q u.val, readRow ρ tl x u)) ++
        readRowsFrom ρ tl pc (q + 1) l := rfl

/-- All single equations of the ties and reads, each with its exponent. The batching element does
not occur. -/
def rowsTail (tl : HTailF2) (funs : Array HFun) (pc : Nat) : List (Nat × Gap K) :=
  tieRows tl pc ++ readRowsFrom ρ tl pc 0 (readsList tl funs)

/-- The rows added up under the powers of θ. -/
def batchOf (θ : K) (A : Nat → Nat → Nat → K) (L : List (Nat × Gap K)) : K :=
  (L.map fun r => θ ^ r.1 * r.2 A).sum

/-! ## The sum -/

theorem sum_flatMap {α β : Type} (g : β → K) (f : α → List β) : ∀ l : List α,
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum
  | [] => rfl
  | a :: l => by
      rw [List.flatMap_cons, List.map_append, List.sum_append, sum_flatMap g f l, List.map_cons,
        List.sum_cons]

theorem sum_finRange {n : ℕ} (f : Fin n → K) : ((List.finRange n).map f).sum = ∑ i, f i :=
  (Fin.sum_univ_def f).symm

theorem batch_tieRowsAt (θ : K) (A : Nat → Nat → Nat → K) (tl : HTailF2) (pc mu : Nat) :
    batchOf θ A (tieRowsAt tl pc mu) = tieEnd A tl θ (pc + firstOf tl mu) mu := by
  unfold batchOf tieRowsAt tieEnd
  rw [sum_flatMap, sum_finRange]
  refine sum_congr rfl fun i' _ => ?_
  rw [List.map_map, sum_finRange]
  refine sum_congr rfl fun u _ => ?_
  show θ ^ (pc + eTie tl mu i' u) * tieRow tl mu i' u A = _
  rw [show pc + eTie tl mu i' u = pc + firstOf tl mu + (tl.stepF * (i' : ℕ) + (u : ℕ)) by
    unfold eTie; omega]
  rfl

theorem batch_tieRows (θ : K) (A : Nat → Nat → Nat → K) (tl : HTailF2) (pc : Nat) :
    batchOf θ A (tieRows tl pc) =
      ((List.range tl.NM).map fun mu => tieEnd A tl θ (pc + firstOf tl mu) mu).sum := by
  unfold tieRows
  show ((List.flatMap _ _).map _).sum = _
  rw [sum_flatMap]
  exact congrArg List.sum (List.map_congr_left fun mu _ => batch_tieRowsAt θ A tl pc mu)

theorem batch_readRows (θ : K) (A : Nat → Nat → Nat → K) (tl : HTailF2) (pc : Nat) :
    ∀ (l : List (HFun × Nat)) (q : Nat), batchOf θ A (readRowsFrom ρ tl pc q l) =
      sumFrom (fun q x => readEnd ρ A tl θ (pc + (firstOf tl tl.NM + q * tl.stepF)) x) q l
  | [], _ => rfl
  | x :: l, q => by
      have ih := batch_readRows θ A tl pc l (q + 1)
      unfold batchOf at ih ⊢
      rw [readRowsFrom_cons, List.map_append, List.sum_append, ih]
      change _ = readEnd ρ A tl θ (pc + (firstOf tl tl.NM + q * tl.stepF)) x + _
      congr 1
      rw [List.map_map, sum_finRange]
      unfold readEnd
      refine sum_congr rfl fun u _ => ?_
      show θ ^ (pc + eRead tl q u) * readRow ρ tl x u A = _
      rw [show pc + eRead tl q u = pc + (firstOf tl tl.NM + q * tl.stepF) + (u : ℕ) by
        unfold eRead; omega]
      rfl

theorem batch_rowsTail (θ : K) (A : Nat → Nat → Nat → K) (tl : HTailF2) (funs : Array HFun)
    (pc : Nat) :
    batchOf θ A (rowsTail ρ tl funs pc) =
      ((List.range tl.NM).map fun mu => tieEnd A tl θ (pc + firstOf tl mu) mu).sum +
        sumFrom (fun q x => readEnd ρ A tl θ (pc + (firstOf tl tl.NM + q * tl.stepF)) x) 0
          (readsList tl funs) := by
  rw [← batch_tieRows, ← batch_readRows]
  unfold batchOf rowsTail
  rw [List.map_append, List.sum_append]

/-! ## The exponents rise along the list -/

/-- the exponents rise -/
def Rising (L : List (Nat × Gap K)) : Prop := L.Pairwise fun a b => a.1 < b.1

theorem mem_tieRowsAt {tl : HTailF2} {pc mu : Nat} {r : Nat × Gap K}
    (h : r ∈ tieRowsAt tl pc mu) :
    ∃ (i' : Fin (Alg.symRows (tl.shp.getD mu {}).m)) (u : Fin tl.tau),
      r.1 = pc + eTie tl mu i' u := by
  obtain ⟨i', _, h⟩ := List.mem_flatMap.1 h
  obtain ⟨u, _, rfl⟩ := List.mem_map.1 h
  exact ⟨i', u, rfl⟩

theorem rising_tieRowsAt (tl : HTailF2) (pc mu : Nat) :
    Rising (K := K) (tieRowsAt tl pc mu) := by
  unfold Rising tieRowsAt
  rw [List.pairwise_flatMap]
  refine ⟨fun i' _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    refine (List.pairwise_lt_finRange _).imp fun {u v} h => ?_
    have h' : (u : ℕ) < v := h
    show pc + eTie tl mu i' u < pc + eTie tl mu i' v
    unfold eTie
    omega
  · refine (List.pairwise_lt_finRange _).imp fun {i j} h x hx y hy => ?_
    obtain ⟨u, _, rfl⟩ := List.mem_map.1 hx
    obtain ⟨v, _, rfl⟩ := List.mem_map.1 hy
    show pc + eTie tl mu i u < pc + eTie tl mu j v
    have h1 := tau_le_stepF tl
    have hu := u.2
    have hij : (i : ℕ) + 1 ≤ j := h
    have h3 : tl.stepF * ((i : ℕ) + 1) ≤ tl.stepF * j := Nat.mul_le_mul_left _ hij
    have h4 : tl.stepF * ((i : ℕ) + 1) = tl.stepF * i + tl.stepF := by ring
    unfold eTie
    omega

theorem rising_tieRows (tl : HTailF2) (pc : Nat)
    (hmS : ∀ mu, mu < tl.NM → (tl.shp.getD mu {}).mS = Alg.symRows (tl.shp.getD mu {}).m) :
    Rising (K := K) (tieRows tl pc) := by
  unfold Rising tieRows
  rw [List.pairwise_flatMap]
  refine ⟨fun mu _ => rising_tieRowsAt tl pc mu, ?_⟩
  refine List.Pairwise.imp_of_mem (R := fun a b => a < b) ?_ List.pairwise_lt_range
  intro mu nu hmu _ hlt x hx y hy
  obtain ⟨i, u, ex⟩ := mem_tieRowsAt hx
  obtain ⟨j, v, ey⟩ := mem_tieRowsAt hy
  have a := eTie_lt tl mu i u (by rw [hmS mu (List.mem_range.1 hmu)]; exact i.2) u.2
  have b := firstOf_mono tl (show mu + 1 ≤ nu from hlt)
  rw [ex, ey]
  unfold eTie at a ⊢
  omega

theorem le_readRows (tl : HTailF2) (pc : Nat) : ∀ (l : List (HFun × Nat)) (q : Nat),
    ∀ r ∈ readRowsFrom ρ tl pc q l, pc + eRead tl q 0 ≤ r.1 ∧
      r.1 < pc + (firstOf tl tl.NM + (q + l.length) * tl.stepF)
  | [], _, r, h => absurd h (List.not_mem_nil)
  | x :: l, q, r, h => by
      rw [readRowsFrom_cons] at h
      rcases List.mem_append.1 h with h | h
      · obtain ⟨u, _, rfl⟩ := List.mem_map.1 h
        have h2 := eRead_lt tl (q + (x :: l).length) q u
          (by rw [List.length_cons]; omega) u.2
        refine ⟨?_, Nat.add_lt_add_left h2 pc⟩
        show pc + eRead tl q 0 ≤ pc + eRead tl q u
        unfold eRead
        omega
      · obtain ⟨h1, h2⟩ := le_readRows tl pc l (q + 1) r h
        have e : (q + 1) * tl.stepF = q * tl.stepF + tl.stepF := Nat.succ_mul _ _
        refine ⟨?_, ?_⟩
        · unfold eRead at h1 ⊢
          omega
        · rw [List.length_cons, show q + (l.length + 1) = q + 1 + l.length by omega]
          exact h2

theorem rising_readRows (tl : HTailF2) (pc : Nat) : ∀ (l : List (HFun × Nat)) (q : Nat),
    Rising (readRowsFrom ρ tl pc q l)
  | [], _ => List.Pairwise.nil
  | x :: l, q => by
      unfold Rising
      rw [readRowsFrom_cons, List.pairwise_append]
      refine ⟨?_, rising_readRows tl pc l (q + 1), ?_⟩
      · rw [List.pairwise_map]
        refine (List.pairwise_lt_finRange _).imp fun {u v} h => ?_
        have h' : (u : ℕ) < v := h
        show pc + eRead tl q u < pc + eRead tl q v
        unfold eRead
        omega
      · intro a ha b hb
        obtain ⟨u, _, rfl⟩ := List.mem_map.1 ha
        have h1 := (le_readRows ρ tl pc l (q + 1) b hb).1
        have h2 := tau_le_stepF tl
        have hu := u.2
        have e : (q + 1) * tl.stepF = q * tl.stepF + tl.stepF := Nat.succ_mul _ _
        show pc + eRead tl q u < b.1
        unfold eRead at h1 ⊢
        omega

/-- The exponents of all rows rise along the list: so no two are equal. -/
theorem rising_rowsTail (tl : HTailF2) (funs : Array HFun) (pc : Nat)
    (hmS : ∀ mu, mu < tl.NM → (tl.shp.getD mu {}).mS = Alg.symRows (tl.shp.getD mu {}).m) :
    Rising (rowsTail ρ tl funs pc) := by
  unfold Rising rowsTail
  rw [List.pairwise_append]
  refine ⟨rising_tieRows tl pc hmS, rising_readRows ρ tl pc _ 0, ?_⟩
  intro a ha b hb
  obtain ⟨mu, hmu, ha⟩ := List.mem_flatMap.1 ha
  obtain ⟨i, u, ea⟩ := mem_tieRowsAt ha
  have hmu' : mu < tl.NM := List.mem_range.1 hmu
  have h1 := (le_readRows ρ tl pc _ 0 b hb).1
  have h2 := eTie_lt_eRead tl mu i u 0 0 hmu' (by rw [hmS mu hmu']; exact i.2) u.2
  rw [ea]
  omega

/-- Every exponent is at least pc and below pc plus the number of indices. -/
theorem bounds_rowsTail (tl : HTailF2) (funs : Array HFun) (pc : Nat)
    (hmS : ∀ mu, mu < tl.NM → (tl.shp.getD mu {}).mS = Alg.symRows (tl.shp.getD mu {}).m) :
    ∀ r ∈ rowsTail ρ tl funs pc, pc ≤ r.1 ∧
      r.1 < pc + (firstOf tl tl.NM + (readsList tl funs).length * tl.stepF) := by
  intro r hr
  rcases List.mem_append.1 hr with h | h
  · obtain ⟨mu, hmu, h⟩ := List.mem_flatMap.1 h
    obtain ⟨i, u, e⟩ := mem_tieRowsAt h
    have hmu' : mu < tl.NM := List.mem_range.1 hmu
    have h2 := eTie_lt_eRead tl mu i u 0 0 hmu' (by rw [hmS mu hmu']; exact i.2) u.2
    rw [e]
    unfold eRead at h2
    omega
  · obtain ⟨h1, h2⟩ := le_readRows ρ tl pc _ 0 r h
    rw [Nat.zero_add] at h2
    exact ⟨by omega, h2⟩

end OnBytes.Tie.Pv.Tail.Port

#print axioms OnBytes.Tie.Pv.Tail.Port.rising_rowsTail
#print axioms OnBytes.Tie.Pv.Tail.Port.bounds_rowsTail
#print axioms OnBytes.Tie.Pv.Tail.Port.batch_rowsTail
