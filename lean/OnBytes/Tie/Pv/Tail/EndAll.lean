-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndAll.lean: `objectsF` (OnBytes/Model/Tail.lean) is the verifier's routine that
adds the equations of a smallness test to the sub-proof's one equation. This file shows, under the
premises below, that what it adds behind the lookup's claims is the sum of the test's single
equations over the arrays' own entries, each under its own power of the batching element.
States. `objectsF_ends`: from the state behind the lookup's claims to the state that `objectsF`
returns, the total of the one equation grows by the sum of all `tieEnd` (the single equations of a
matrix, each under its power of the batching element) and all `readEnd` (those of a read).
Under, four premises: (1) `objectsF` returns; (2) the shapes fit the matrices; (3) `RawRows`: the
entries of the four kinds of virtual rows in use (a virtual row is a public combination of an
array's rows) are the sums that it names, in terms of the arrays' entries A, a parameter that
`RawRows` alone relates to the rest; (4) all values are read in a commutative ring K through a map ρ
that respects 0, 1, sums, differences and products. The part of the conclusion on the total has a
condition of its own: `F1.LS.size = F1.ns`.
Does not show.
 1. `RawRows` is a premise, proved nowhere in this file.
 2. One more premise: the shapes fit the matrices, which the routine that sets up the arrays tests.
 3. A read's equation runs over the rows of its segment alone.
Notes in full, with every limit at length, stand at the end of this file.

-/
import OnBytes.Tie.Pv.Tail.EndLoopsB
import OnBytes.Tie.Pv.Tail.Ends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model

open Finset

variable {K : Type} [CommRing K]

/-! ## 1. The two brackets, over raw rows, are sums of single equations -/

theorem cast20 : (((2 : ℤ) ^ 20 : ℤ) : K) = (2 : K) ^ 20 := by norm_num

/-- The tie's bracket. -/
theorem tie_closed (θ : K) (st : ℕ) {m k tau : ℕ} (th : Fin tau → Fin k → K)
    (sym : Fin (Alg.symRows m) → Fin k → K) (zl zh : Fin tau → Fin m → K) :
    -((2 : K) ^ 17 * ((∑ u : Fin tau, θ ^ (u : ℕ)) *
          ∑ i : Fin m, ((2 : K) ^ 20) ^ ((i : ℕ) % 3) * θ ^ (st * ((i : ℕ) / 3)))) +
        ∑ i : Fin m, ((2 : K) ^ 20) ^ ((i : ℕ) % 3) * θ ^ (st * ((i : ℕ) / 3)) *
          ∑ u : Fin tau, θ ^ (u : ℕ) * zl u i +
        (2 : K) ^ 10 * ∑ i : Fin m, ((2 : K) ^ 20) ^ ((i : ℕ) % 3) * θ ^ (st * ((i : ℕ) / 3)) *
          ∑ u : Fin tau, θ ^ (u : ℕ) * zh u i -
        ∑ p : Fin k, (∑ u : Fin tau, th u p * θ ^ (u : ℕ)) *
          ∑ i' : Fin (Alg.symRows m), θ ^ (st * (i' : ℕ)) * sym i' p =
      ∑ i' : Fin (Alg.symRows m), ∑ u : Fin tau, θ ^ (st * (i' : ℕ) + (u : ℕ)) *
        tieGap ((2 : ℤ) ^ 20) ((2 : K) ^ 10) ((2 : K) ^ 17) th sym zl zh u i' := by
  refine Eq.trans ?_ (tie_batch ((2 : ℤ) ^ 20) ((2 : K) ^ 10) ((2 : K) ^ 17)
    (fun i' u => θ ^ (st * i' + u)) th sym zl zh).symm
  have t1 : (∑ u : Fin tau, θ ^ (u : ℕ)) *
        ∑ i : Fin m, ((2 : K) ^ 20) ^ ((i : ℕ) % 3) * θ ^ (st * ((i : ℕ) / 3)) =
      ∑ u : Fin tau, ∑ i : Fin m, cTie ((2 : ℤ) ^ 20) (fun i' u => θ ^ (st * i' + u)) u i := by
    rw [sum_mul_sum]
    refine sum_congr rfl fun u _ => sum_congr rfl fun i _ => ?_
    simp only [cTie, cast20]
    rw [pow_add]
    ring
  have t2 : ∀ z : Fin tau → Fin m → K,
      ∑ i : Fin m, ((2 : K) ^ 20) ^ ((i : ℕ) % 3) * θ ^ (st * ((i : ℕ) / 3)) *
          ∑ u : Fin tau, θ ^ (u : ℕ) * z u i =
        ∑ u : Fin tau, ∑ i : Fin m,
          cTie ((2 : ℤ) ^ 20) (fun i' u => θ ^ (st * i' + u)) u i * z u i := by
    intro z
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun u _ => ?_
    simp only [cTie, cast20]
    rw [pow_add]
    ring
  have t3 : ∑ p : Fin k, (∑ u : Fin tau, th u p * θ ^ (u : ℕ)) *
        ∑ i' : Fin (Alg.symRows m), θ ^ (st * (i' : ℕ)) * sym i' p =
      -∑ i' : Fin (Alg.symRows m), ∑ c : Fin k,
        cSym (fun i' u => θ ^ (st * i' + u)) th i' c * sym i' c := by
    rw [sum_comm (s := (univ : Finset (Fin (Alg.symRows m)))), ← sum_neg_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun i' _ => ?_
    simp only [cSym]
    rw [neg_mul, neg_neg, sum_mul, sum_mul]
    refine sum_congr rfl fun u _ => ?_
    rw [pow_add]
    ring
  have t4 : (2 : K) ^ 10 * ∑ u : Fin tau, ∑ i : Fin m,
        cTie ((2 : ℤ) ^ 20) (fun i' u => θ ^ (st * i' + u)) u i * zh u i =
      ∑ u : Fin tau, ∑ i : Fin m,
        (2 : K) ^ 10 * cTie ((2 : ℤ) ^ 20) (fun i' u => θ ^ (st * i' + u)) u i * zh u i := by
    rw [mul_sum]
    refine sum_congr rfl fun u _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
  unfold cTie0
  rw [t1, t2 zl, t2 zh, t3, t4]
  ring

/-- The read's bracket. -/
theorem read_closed (θ : K) {len k tau : ℕ} (th : Fin tau → Fin k → K) (φ : ℕ → K)
    (tab : Fin k → K) (zl zh : Fin tau → Fin len → K) :
    -((2 : K) ^ 17 * ((∑ j : Fin len, φ j) * ∑ u : Fin tau, θ ^ (u : ℕ))) -
        ∑ d : Fin k, (∑ u : Fin tau, th u d * θ ^ (u : ℕ)) * tab d +
        ∑ j : Fin len, φ j * ∑ u : Fin tau, θ ^ (u : ℕ) * zl u j +
        (2 : K) ^ 10 * ∑ j : Fin len, φ j * ∑ u : Fin tau, θ ^ (u : ℕ) * zh u j =
      ∑ u : Fin tau, θ ^ (u : ℕ) * readGap ((2 : K) ^ 10) ((2 : K) ^ 17) th φ tab zl zh u := by
  refine Eq.trans ?_ (read_batch ((2 : K) ^ 10) ((2 : K) ^ 17) (fun u => θ ^ u) th φ tab zl
    zh).symm
  have t1 : (∑ j : Fin len, φ j) * ∑ u : Fin tau, θ ^ (u : ℕ) =
      ∑ u : Fin tau, ∑ i : Fin len, cRead (fun u => θ ^ u) φ u i := by
    rw [mul_comm, sum_mul_sum]
    exact sum_congr rfl fun u _ => sum_congr rfl fun i _ => rfl
  have t2 : ∀ z : Fin tau → Fin len → K,
      ∑ j : Fin len, φ j * ∑ u : Fin tau, θ ^ (u : ℕ) * z u j =
        ∑ u : Fin tau, ∑ i : Fin len, cRead (fun u => θ ^ u) φ u i * z u i := by
    intro z
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun u _ => ?_
    simp only [cRead]
    ring
  have t3 : ∑ d : Fin k, (∑ u : Fin tau, th u d * θ ^ (u : ℕ)) * tab d =
      -∑ c : Fin k, cTab (fun u => θ ^ u) th c * tab c := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun d _ => ?_
    simp only [cTab]
    rw [neg_mul, neg_neg]
    congr 1
    exact sum_congr rfl fun u _ => mul_comm _ _
  have t4 : (2 : K) ^ 10 * ∑ u : Fin tau, ∑ i : Fin len,
        cRead (fun u => θ ^ u) φ u i * zh u i =
      ∑ u : Fin tau, ∑ i : Fin len, (2 : K) ^ 10 * cRead (fun u => θ ^ u) φ u i * zh u i := by
    rw [mul_sum]
    refine sum_congr rfl fun u _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
  unfold cRead0
  rw [t1, t2 zl, t2 zh, t3, t4]
  ring

/-! ## 2. The world of raw rows -/

variable (ρ : Reading K) (W : World K)

/-- The array that holds the table Fn. -/
def uOf (tl : HTailF2) (Fn : HFun) : Nat := (tl.ix.U.getD Fn.tree none).getD 0

/-- What the entries of the four kinds of virtual rows are, in terms of the entries A t r c of the
arrays: ZZ's two last virtual rows have the weight θ ^ u on row u; a symbol array's one virtual row
has θ ^ (stepF i') on row i'; the vector that holds a table is one row with the weight 1. -/
structure RawRows (tl : HTailF2) (G : Fork) (funs : Array HFun) (θ : K)
    (A : Nat → Nat → Nat → K) : Prop where
  ties : ∀ c, W.entry tl.ix.ZZ tl.zzRowTies c = ∑ u ∈ range tl.tau, θ ^ u * A tl.ix.ZZ u c
  reads : ∀ c, W.entry tl.ix.ZZ tl.zzRowReads c = ∑ u ∈ range tl.tau, θ ^ u * A tl.ix.ZZ u c
  syms : ∀ mu, mu < tl.NM → ∀ p, W.entry (tl.gtTree.getD mu 0) 0 p =
    ∑ i' ∈ range (tl.shp.getD mu {}).mS, θ ^ (tl.stepF * i') * A (tl.gtTree.getD mu 0) i' p
  tabs : ∀ x ∈ readsList tl funs, ∀ d, d < (tl.mats.getD x.1.mat {}).k →
    W.entry (uOf tl x.1) (posOf tl x.1 x.2 d / colsU G (uOf tl x.1))
      (posOf tl x.1 x.2 d % colsU G (uOf tl x.1)) = A (uOf tl x.1) 0 (posOf tl x.1 x.2 d)

/-- The drawn entries of matrix mu, by their signs. -/
def thOf (tl : HTailF2) (mu k : Nat) : Fin tl.tau → Fin k → K := fun u p =>
  signOf (K := K) (tl.cfF.getD ((tl.cfFirst.getD mu 0 + p) * tl.tau + u) 0)

/-- The single ties of matrix mu, each under its power of θ. -/
def tieEnd (A : Nat → Nat → Nat → K) (tl : HTailF2) (θ : K) (e0 mu : Nat) : K :=
  ∑ i' : Fin (Alg.symRows (tl.shp.getD mu {}).m), ∑ u : Fin tl.tau,
    θ ^ (e0 + (tl.stepF * (i' : ℕ) + (u : ℕ))) *
      tieGap ((2 : ℤ) ^ 20) ((2 : K) ^ 10) ((2 : K) ^ 17) (thOf tl mu (tl.shp.getD mu {}).k)
        (fun i' c => A (tl.gtTree.getD mu 0) i' c)
        (fun u i => A tl.ix.ZZ u ((tl.zzCol mu 0 0).getD 0 + i))
        (fun u i => A tl.ix.ZZ u ((tl.zzCol mu 1 0).getD 0 + i)) u i'

/-- The single equations of the read x, each under its power of θ. -/
def readEnd (A : Nat → Nat → Nat → K) (tl : HTailF2) (θ : K) (e0 : Nat) (x : HFun × Nat) : K :=
  ∑ u : Fin tl.tau, θ ^ (e0 + (u : ℕ)) *
    readGap (m := x.1.len) ((2 : K) ^ 10) ((2 : K) ^ 17)
      (thOf tl x.1.mat (tl.mats.getD x.1.mat {}).k)
      (fun j => ρ.val (x.1.phi.getD j zeroE)) (fun d => A (uOf tl x.1) 0 (posOf tl x.1 x.2 d))
      (fun u j => A tl.ix.ZZ u ((tl.zzCol x.1.mat 0 (x.2 * x.1.len)).getD 0 + j))
      (fun u j => A tl.ix.ZZ u ((tl.zzCol x.1.mat 1 (x.2 * x.1.len)).getD 0 + j)) u

variable {W}

theorem tieClosed_raw {tl : HTailF2} {G : Fork} {funs : Array HFun} {θ : K}
    {A : Nat → Nat → Nat → K} (hV : RawRows W tl G funs θ A) (e0 mu : Nat) (hmu : mu < tl.NM)
    (hmS : (tl.shp.getD mu {}).mS = Alg.symRows (tl.shp.getD mu {}).m) :
    θ ^ e0 * tieClosed W θ (gamSign θ tl) tl mu = tieEnd A tl θ e0 mu := by
  have e := tie_closed (m := (tl.shp.getD mu {}).m) θ tl.stepF (thOf tl mu (tl.shp.getD mu {}).k)
    (fun i' c => A (tl.gtTree.getD mu 0) i' c)
    (fun u i => A tl.ix.ZZ u ((tl.zzCol mu 0 0).getD 0 + i))
    (fun u i => A tl.ix.ZZ u ((tl.zzCol mu 1 0).getD 0 + i))
  unfold tieClosed tieEnd gamSign
  simp only [hV.ties, hV.syms mu hmu, hmS, Finset.sum_range]
  refine (congrArg (fun t => θ ^ e0 * t) e).trans ?_
  rw [mul_sum]
  refine sum_congr rfl fun i' _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun u _ => ?_
  ring

theorem readClosed_raw {tl : HTailF2} {G : Fork} {funs : Array HFun} {θ : K}
    {A : Nat → Nat → Nat → K} (hV : RawRows W tl G funs θ A) (e0 : Nat) (x : HFun × Nat)
    (hx : x ∈ readsList tl funs) (hphi : x.1.phi.size = x.1.len) :
    θ ^ e0 * readClosed ρ W θ (gamSign θ tl) tl G x = readEnd ρ A tl θ e0 x := by
  have e := read_closed (len := x.1.len) θ (thOf tl x.1.mat (tl.mats.getD x.1.mat {}).k)
    (fun j => ρ.val (x.1.phi.getD j zeroE)) (fun d => A (uOf tl x.1) 0 (posOf tl x.1 x.2 d))
    (fun u j => A tl.ix.ZZ u ((tl.zzCol x.1.mat 0 (x.2 * x.1.len)).getD 0 + j))
    (fun u j => A tl.ix.ZZ u ((tl.zzCol x.1.mat 1 (x.2 * x.1.len)).getD 0 + j))
  have hT : ∑ d ∈ range (tl.mats.getD x.1.mat {}).k, gamSign θ tl x.1.mat d *
        W.entry ((tl.ix.U.getD x.1.tree none).getD 0)
          (posOf tl x.1 x.2 d / colsU G ((tl.ix.U.getD x.1.tree none).getD 0))
          (posOf tl x.1 x.2 d % colsU G ((tl.ix.U.getD x.1.tree none).getD 0)) =
      ∑ d ∈ range (tl.mats.getD x.1.mat {}).k, gamSign θ tl x.1.mat d *
        A (uOf tl x.1) 0 (posOf tl x.1 x.2 d) :=
    sum_congr rfl fun d hd => by rw [← hV.tabs x hx d (mem_range.1 hd)]; rfl
  unfold readClosed readEnd
  rw [hT, hphi]
  unfold gamSign
  simp only [hV.reads, Finset.sum_range]
  refine (congrArg (fun t => θ ^ e0 * t) e).trans ?_
  rw [mul_sum]
  refine sum_congr rfl fun u _ => ?_
  rw [pow_add, mul_assoc]

/-! ## 3. What objectsF adds for its ties and reads -/

variable (W)

/-- If objectsF succeeds, the shapes fit and `RawRows` holds, then, where F1.LS.size = F1.ns, behind
the lookup's claims the one equation grows by the sum of all single ties and all single equations of
reads, each under its own power of the batching element. -/
theorem objectsF_ends (tl tl' : HTailF2) (funs : Array HFun) (F G : Fork) (c c' : Ctx)
    (h : tl.objectsF funs F c = .ok ((tl', G), c'))
    (hfit : ∀ mu, mu < tl'.NM → (tl'.shp.getD mu {}).m = (tl'.mats.getD mu {}).m ∧
      (tl'.shp.getD mu {}).k = (tl'.mats.getD mu {}).k)
    (A : Nat → Nat → Nat → K) (hV : RawRows W tl' G funs (ρ.val G.theta) A) :
    ∃ g Fa ca tla Fb cb tlb Fc cc tl1 F1 c1,
      tl.heard = some g ∧ Forest.objects g F c = .ok (((), Fa), ca) ∧
      tl.linJoin9 Fa ca = .ok ((tla, Fb), cb) ∧ tla.linBits9 Fb cb = .ok ((tlb, Fc), cc) ∧
      tlb.weightsF Fc cc = .ok ((tl1, F1), c1) ∧ F1 = Fc ∧ c1 = cc ∧
      (F1.LS.size = F1.ns → c' = c1 ∧ Kept F1 G ∧
        G.nClaim = F1.nClaim + tl'.NM + tl'.nX4Laid ∧
        G.total ρ W = F1.total ρ W
          + ((List.range tl'.NM).map fun mu =>
              tieEnd A tl' (ρ.val G.theta) (G.planClaimsF + firstOf tl' mu) mu).sum
          + sumFrom (fun q x =>
              readEnd ρ A tl' (ρ.val G.theta)
                (G.planClaimsF + (firstOf tl' tl'.NM + q * tl'.stepF)) x) 0
              (readsList tl' funs)) := by
  have hsh : (∀ mu, mu < tl'.NM →
      (tl'.shp.getD mu {}).mS = ((tl'.mats.getD mu {}).m + 2) / 3) ∧
      ∀ x ∈ readsList tl' funs, x.1.phi.size = x.1.len := by
    obtain ⟨_, _, _, _, _, _, tlb, Fc, cc, tl1, F1, c1, _, _, _, _, hWt, _, etl, _, hp, _⟩ :=
      objectsF_total ρ W tl tl' funs F G c c' h
    obtain ⟨_, _, hP1, _⟩ := weightsF_spec tlb tl1 Fc F1 cc c1 hWt
    rw [etl]
    exact ⟨fun mu hmu => (hP1.shape mu hmu).2.2.2.2, hp⟩
  obtain ⟨hsh, hphi⟩ := hsh
  obtain ⟨g, Fa, ca, tla, Fb, cb, tlb, Fc, cc, tl1, F1, c1, hg, hFo, hJ, hB, hWt, eF, ec, himp⟩ :=
    objectsF_fits_total ρ W tl tl' funs F G c c' h hfit
  refine ⟨g, Fa, ca, tla, Fb, cb, tlb, Fc, cc, tl1, F1, c1, hg, hFo, hJ, hB, hWt, eF, ec,
    fun hs => ?_⟩
  obtain ⟨e1, hk, hn, htot⟩ := himp hs
  refine ⟨e1, hk, hn, ?_⟩
  rw [htot]
  congr 1
  · congr 2
    apply List.map_congr_left
    intro mu hmu
    have hmu' : mu < tl'.NM := List.mem_range.1 hmu
    refine tieClosed_raw hV _ mu hmu' ?_
    rw [hsh mu hmu', (hfit mu hmu').1]
    rfl
  · apply sumFrom_congr
    intro q x hx
    exact readClosed_raw ρ hV _ x hx (hphi x hx)

end OnBytes.Tie.Pv.Tail.Port

#print axioms OnBytes.Tie.Pv.Tail.Port.objectsF_ends
#print axioms OnBytes.Tie.Pv.Tail.Port.tie_closed
#print axioms OnBytes.Tie.Pv.Tail.Port.read_closed
#print axioms OnBytes.Tie.Pv.Tail.Port.tieClosed_raw
#print axioms OnBytes.Tie.Pv.Tail.Port.readClosed_raw

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/Tie/Pv/Tail/EndAll.lean: what objectsF (OnBytes/Model/Tail.lean) adds to the sub-proof's one
equation for its ties and reads is the sum of the smallness test's single equations over the arrays'
own entries, each under its own power of the batching element.

Definitions, statements and proofs. OnBytes/Tie/Pv/Tail/EndLoopsB.lean has the sum in closed form
over
the entries of virtual rows. A virtual row is a public combination of an array's rows. Here the
entries of the four kinds of virtual rows that the ties and reads use are taken to be the
combinations that `RawRows` names, and the closed forms are regrouped by `tie_batch` and
`read_batch`
(OnBytes/Tie/Pv/Tail/Ends.lean).
Main names:
  `tie_closed`, `read_closed`: the two brackets over raw rows are sums of single equations.
  `RawRows W tl G funs θ A`: a premise on the world W: what the entries of ZZ's two last virtual
    rows, of each symbol array's virtual row and of the vector that holds a table are, in terms of
    the arrays' entries A t r c.
  `thOf`: the drawn entries, by sign. `tieEnd`, `readEnd`: the single equations of a matrix and of a
    read, added up.
  `objectsF_ends`: if objectsF returns, the total grows by the sum of all `tieEnd` and `readEnd`.
Limits: `RawRows` is a premise, proved nowhere in this file. One more premise: the shapes fit the
matrices, which the routine that lays the arrays tests. A read's equation runs over the rows of its
segment alone.
-/
