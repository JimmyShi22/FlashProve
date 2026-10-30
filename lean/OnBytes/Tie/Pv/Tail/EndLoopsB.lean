-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndLoopsB.lean: what objectsF (OnBytes/Model/Tail.lean) adds for its ties and
reads, as an expression in the batching element, numbers of the smallness test's state, the drawn
matrix and the entries of virtual rows.

Definitions, statements and proofs.
Main names:
  `pushFold_array`: a fold that pushes running sums. `Powered.eqFirst_val`: the first indices.
  `Powered.tieLeft_some`, `Powered.tieRight_some`: the weights of a tie are there.
  `mem_readsList`: which reads the list has.
  `signOf`, `foldColumn_val`: a column of the drawn matrix, summed under weights: an entry counts
    by its sign. `gamAt`, `weightsF_gam`, `gamAt_val`: what weightsF leaves in gamX and gamV.
  `firstOf`, `gamSign`, `tieClosed`, `readClosed`: the closed forms.
  `objectsF_fits_total`: if objectsF returns and the shapes fit the matrices, the total grows by
    the closed forms, each under theta ^ (planClaims + its first index).
Limits: the entries are those of virtual rows. The drawn matrix is read by sign and at cfFirst, as
foldSums reads it: that its entries are -1, 0, 1 is not used.

-/
import OnBytes.Tie.Pv.Tail.EndClosed
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model

variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

/-! ## A fold that pushes running sums -/

theorem pushFold_spec {α : Type} (w : α → Nat) :
    ∀ (l : List α) (a : Array Nat), 0 < a.size →
      (l.foldl (fun a s => a.push (a.getD (a.size - 1) 0 + w s)) a).size = a.size + l.length ∧
      (∀ i, i < a.size →
        (l.foldl (fun a s => a.push (a.getD (a.size - 1) 0 + w s)) a).getD i 0 = a.getD i 0) ∧
      (∀ j, j ≤ l.length →
        (l.foldl (fun a s => a.push (a.getD (a.size - 1) 0 + w s)) a).getD (a.size - 1 + j) 0
          = a.getD (a.size - 1) 0 + ((l.take j).map w).sum)
  | [], a, _ => ⟨rfl, fun _ _ => rfl, fun j hj => by
      obtain rfl := Nat.le_zero.1 hj
      simp⟩
  | s :: l, a, h => by
    have hp : (a.push (a.getD (a.size - 1) 0 + w s)).size = a.size + 1 := Array.size_push _
    obtain ⟨h1, h2, h3⟩ := pushFold_spec w l (a.push (a.getD (a.size - 1) 0 + w s)) (by omega)
    have old : ∀ i, i < a.size →
        (a.push (a.getD (a.size - 1) 0 + w s)).getD i 0 = a.getD i 0 := by
      intro i hi
      simp [Array.getD, Array.getElem_push, hi, Nat.lt_succ_of_lt hi]
    have last : (a.push (a.getD (a.size - 1) 0 + w s)).getD a.size 0
        = a.getD (a.size - 1) 0 + w s := by
      simp [Array.getD]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.foldl_cons, h1, hp, List.length_cons]; omega
    · intro i hi
      rw [List.foldl_cons, h2 i (by omega), old i hi]
    · intro j hj
      rw [List.foldl_cons]
      cases j with
      | zero =>
        rw [Nat.add_zero, h2 _ (by omega), old _ (by omega)]
        simp
      | succ j =>
        have e : a.size - 1 + (j + 1) = (a.push (a.getD (a.size - 1) 0 + w s)).size - 1 + j := by
          rw [hp]; omega
        rw [e, h3 j (Nat.le_of_succ_le_succ hj), hp, Nat.add_sub_cancel, last, List.take_succ_cons,
          List.map_cons, List.sum_cons]
        omega

theorem sum_take_eq {α : Type} (w : α → Nat) (d : α) : ∀ (l : List α) (n : Nat), n ≤ l.length →
    ((l.take n).map w).sum = ∑ i ∈ Finset.range n, w (l.getD i d)
  | _, 0, _ => by simp
  | [], n + 1, h => absurd h (by simp)
  | a :: l, n + 1, h => by
    rw [List.take_succ_cons, List.map_cons, List.sum_cons, Finset.sum_range_succ',
      sum_take_eq w d l n (Nat.le_of_succ_le_succ h)]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    exact Nat.add_comm _ _

/-- The pushing fold over an array, from #[0]: one entry more than the array, entry n = the sum of
the first n. -/
theorem pushFold_array {α : Type} (w : α → Nat) (d : α) (as : Array α) :
    (as.foldl (fun a s => a.push (a.getD (a.size - 1) 0 + w s)) #[0]).size = as.size + 1 ∧
    ∀ n, n ≤ as.size →
      (as.foldl (fun a s => a.push (a.getD (a.size - 1) 0 + w s)) #[0]).getD n 0
        = ∑ i ∈ Finset.range n, w (as.getD i d) := by
  rw [← Array.foldl_toList]
  obtain ⟨h1, _, h3⟩ := pushFold_spec w as.toList #[0] (by simp)
  refine ⟨by rw [h1]; simp; omega, fun n hn => ?_⟩
  have h := h3 n (by simpa using hn)
  have e0 : (#[0] : Array Nat).size - 1 + n = n := by simp
  have e1 : (#[0] : Array Nat).getD ((#[0] : Array Nat).size - 1) 0 = 0 := rfl
  rw [e0, e1, Nat.zero_add, sum_take_eq w d as.toList n (by simpa using hn)] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

namespace Powered
variable {tl : HTailF2} {theta : E} (hP : Powered tl theta)
include hP

/-! ## There is a shape for each matrix -/

theorem lt_shp (mu : Nat) (hmu : mu < tl.NM) : mu < tl.shp.size := by
  by_contra hge
  have e : tl.shp.getD mu {} = {} := by simp [Array.getD, hge]
  have h1 := (hP.shape mu hmu).1
  rw [e] at h1
  exact absurd h1 (by decide)

theorem NM_le_shp : tl.NM ≤ tl.shp.size :=
  Nat.le_of_not_lt fun hlt => absurd (hP.lt_shp _ hlt) (Nat.lt_irrefl _)

/-! ## The first indices in closed form -/

theorem eqFirst_val (mu : Nat) (h : mu ≤ tl.shp.size) :
    tl.eqFirst.getD mu 0 = ∑ nu ∈ Finset.range mu, tl.stepF * 2 ^ clog2 (tl.shp.getD nu {}).mS := by
  rw [hP.eqFirst]
  exact (pushFold_array (fun s : ShP => tl.stepF * 2 ^ clog2 s.mS) {} tl.shp).2 mu h

/-! ## The weights of a tie are there -/

theorem tieLeft_some (mu : Nat) (hmu : mu < tl.NM) :
    ∃ wl, tieLeft (tl.shp.getD mu {}) (tl.rowX.getD mu #[]) (tl.loX.getD mu #[]) = some wl := by
  have hsz := hP.lt_shp mu hmu
  obtain ⟨hJ, _, _, hRr, _⟩ := hP.shape mu hmu
  have e1 : (tl.rowX.getD mu #[]).size = (tl.shp.getD mu {}).Rr := by
    rw [hP.rowX, getD_map _ _ _ _ {} hsz, powers_size, hRr]
  have e2 : (tl.loX.getD mu #[]).size = (tl.shp.getD mu {}).J := by
    rw [hP.loX, getD_map _ _ _ _ {} hsz, hJ]
    rfl
  unfold tieLeft
  rw [if_neg (by rw [e1, e2]; simp)]
  exact ⟨_, rfl⟩

/-- tieRight is there as soon as gamX[mu] has s.k entries. -/
theorem tieRight_some (mu : Nat) (hmu : mu < tl.NM)
    (hg : (tl.gamX.getD mu #[]).size = (tl.shp.getD mu {}).k) :
    ∃ wr, tieRight (tl.shp.getD mu {}) (tl.loX.getD mu #[]) (tl.gamX.getD mu #[]) = some wr := by
  have hsz := hP.lt_shp mu hmu
  have e2 : (tl.loX.getD mu #[]).size = (tl.shp.getD mu {}).J := by
    rw [hP.loX, getD_map _ _ _ _ {} hsz, (hP.shape mu hmu).1]
    rfl
  unfold tieRight
  rw [if_neg (by rw [e2, hg]; simp)]
  exact ⟨_, rfl⟩

end Powered

/-! ## Which reads the list has -/

theorem mem_readsList (tl : HTailF2) (funs : Array HFun) (Fn : HFun) (sg : Nat) :
    (Fn, sg) ∈ readsList tl funs ↔ Fn ∈ funs.toList ∧ Fn.mat < tl.NM ∧ (Fn.tree = 0 ∨ Fn.tree = 2) ∧
      sg < (tl.mats.getD Fn.mat {}).m / Fn.len := by
  simp only [readsList, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨mu, hmu, un, hun, Fn', hFn', hx⟩
    unfold segsOf at hx
    split at hx
    · rename_i hc
      simp only [List.mem_map, List.mem_range, Prod.mk.injEq] at hx
      obtain ⟨s, hs, rfl, rfl⟩ := hx
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨hFn', hmu, by simpa using hun, hs⟩
    · simp at hx
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨Fn.mat, h2, Fn.tree, by simpa using h3, Fn, h1, ?_⟩
    unfold segsOf
    rw [if_pos (by simp)]
    exact List.mem_map.2 ⟨sg, List.mem_range.2 h4, rfl⟩

/-! ## What weightsF leaves in gamX and gamV -/

/-- An entry of the drawn matrix as foldColumn reads it: by its sign. -/
def signOf (x : Int) : K := if x = 0 then 0 else if x < 0 then -1 else 1

theorem sign_step (x : Int) (s y : E) :
    ρ.val (if x == 0 then s else if x < 0 then subE s y else addE s y)
      = ρ.val s + signOf (K := K) x * ρ.val y := by
  by_cases h0 : x = 0
  · rw [if_pos (beq_iff_eq.2 h0), signOf, if_pos h0, zero_mul, add_zero]
  · rw [if_neg (fun h => h0 (beq_iff_eq.1 h))]
    by_cases h1 : x < 0
    · rw [if_pos h1, ρ.sub, signOf, if_neg h0, if_pos h1]; ring
    · rw [if_neg h1, ρ.add, signOf, if_neg h0, if_neg h1, one_mul]

theorem foldColumn_list (cf : Array Int) (base : Nat) : ∀ (l : List E) (s : E) (n : Nat),
    ρ.val (l.foldl (fun (s : E × Nat) y =>
        let x := cf.getD (base + s.2) 0
        (if x == 0 then s.1 else if x < 0 then subE s.1 y else addE s.1 y, s.2 + 1)) (s, n)).1
      = ρ.val s + ∑ j ∈ Finset.range l.length,
          signOf (K := K) (cf.getD (base + (n + j)) 0) * ρ.val (l.getD j zeroE)
  | [], s, n => by simp
  | y :: l, s, n => by
    rw [List.foldl_cons, foldColumn_list cf base l _ (n + 1), List.length_cons,
      Finset.sum_range_succ']
    have e : ∀ j, n + 1 + j = n + (j + 1) := by intro j; omega
    simp only [e, Nat.add_zero, List.getD_cons_succ, List.getD_cons_zero]
    rw [sign_step]
    ring

theorem foldColumn_val (cf : Array Int) (base tau : Nat) (v : Array E) (hv : v.size = tau) :
    ρ.val (HTailF2.foldColumn cf base tau v)
      = ∑ u ∈ Finset.range tau,
          signOf (K := K) (cf.getD (base + u) 0) * ρ.val (v.getD u zeroE) := by
  have e : v.extract 0 tau = v := by subst hv; simp
  unfold HTailF2.foldColumn
  rw [e, ← Array.foldl_toList, foldColumn_list ρ cf base v.toList zeroE 0, ρ.zero, zero_add]
  simp [hv, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- What foldSums puts at mu, as a function of fields that foldSums leaves alone. -/
def gamAt (x : HTailF2) (mu : Nat) : Array E :=
  (Array.range (x.mats.getD mu {}).k).map fun c =>
    HTailF2.foldColumn x.cfF ((x.cfFirst.getD mu 0 + c) * x.tau) x.tau x.vp

theorem foldSums_gam (x y : HTailF2) (mu : Nat) (hv : x.vt = x.vp) (h : x.foldSums mu = some y) :
    y.gamX = x.gamX.set! mu (gamAt x mu) ∧ y.gamV = x.gamV.set! mu (gamAt x mu) := by
  unfold HTailF2.foldSums at h
  dsimp only at h
  rw [hv] at h
  simp only [ite_self] at h
  split_ifs at h <;> (cases h; exact ⟨rfl, rfl⟩)

theorem gamAt_congr (x t : HTailF2)
    (e : t = { x with foldTakenF := t.foldTakenF, gamX := t.gamX, gamV := t.gamV }) (mu : Nat) :
    gamAt t mu = gamAt x mu :=
  (congrArg (fun z => gamAt z mu) e).trans rfl

theorem getD_set!_same {α : Type} (a : Array α) (i : Nat) (v d : α) (h : i < a.size) :
    (a.set! i v).getD i d = v := by
  simp [Array.getD, Array.set!, h]

theorem getD_set!_other {α : Type} (a : Array α) (i j : Nat) (v d : α) (h : i ≠ j) :
    (a.set! i v).getD j d = a.getD j d := by
  simp [Array.getD_eq_getD_getElem?, Array.set!, h]

/-- Every write at mu writes gamAt x mu, whenever it comes: so no word on the order or on «once
each» is needed. -/
theorem foldSums_fold_gam : ∀ (l : List Nat) (x y : HTailF2), x.vt = x.vp →
    l.foldlM (fun (x : HTailF2) mu => x.foldSums mu) x = some y →
    y.gamX.size = x.gamX.size ∧ y.gamV.size = x.gamV.size ∧
    ∀ mu, mu < x.gamX.size → mu < x.gamV.size →
      ((mu ∈ l ∨ x.gamX.getD mu #[] = gamAt x mu) → y.gamX.getD mu #[] = gamAt x mu) ∧
      ((mu ∈ l ∨ x.gamV.getD mu #[] = gamAt x mu) → y.gamV.getD mu #[] = gamAt x mu)
  | [], x, y, _, h => by
    have e : x = y := by simpa using h
    subst e
    exact ⟨rfl, rfl, fun mu _ _ => ⟨fun q => q.resolve_left (List.not_mem_nil),
      fun q => q.resolve_left (List.not_mem_nil)⟩⟩
  | nu :: l, x, y, hv, h => by
    rw [List.foldlM_cons] at h
    cases hq : x.foldSums nu with
    | none => simp [hq] at h
    | some t =>
      rw [hq] at h
      have h2 : l.foldlM (fun (x : HTailF2) mu => x.foldSums mu) t = some y := by simpa using h
      have e1 := foldSums_spec x t nu hq
      obtain ⟨gx, gv⟩ := foldSums_gam x t nu hv hq
      have hvt : t.vt = t.vp := by rw [e1]; exact hv
      obtain ⟨s1, s2, hall⟩ := foldSums_fold_gam l t y hvt h2
      have sx : t.gamX.size = x.gamX.size := by rw [gx]; simp
      have sv : t.gamV.size = x.gamV.size := by rw [gv]; simp
      refine ⟨s1.trans sx, s2.trans sv, fun mu h1 h3 => ?_⟩
      obtain ⟨ax, av⟩ := hall mu (by omega) (by omega)
      rw [gamAt_congr x t e1 mu] at ax av
      refine ⟨fun q => ax ?_, fun q => av ?_⟩
      · by_cases hn : nu = mu
        · subst hn; right; rw [gx, getD_set!_same _ _ _ _ h1]
        · rcases q with q | q
          · rcases List.mem_cons.1 q with q | q
            · exact absurd q.symm hn
            · exact Or.inl q
          · right; rw [gx, getD_set!_other _ _ _ _ _ hn, q]
      · by_cases hn : nu = mu
        · subst hn; right; rw [gv, getD_set!_same _ _ _ _ h3]
        · rcases q with q | q
          · rcases List.mem_cons.1 q with q | q
            · exact absurd q.symm hn
            · exact Or.inl q
          · right; rw [gv, getD_set!_other _ _ _ _ _ hn, q]

/-- What weightsF leaves in gamX and gamV. -/
theorem weightsF_gam (tl tl1 : HTailF2) (F F1 : Fork) (c c1 : Ctx)
    (h : tl.weightsF F c = .ok ((tl1, F1), c1)) :
    tl1.gamX.size = tl1.NM ∧ tl1.gamV.size = tl1.NM ∧
    ∀ mu, mu < tl1.NM →
      tl1.gamX.getD mu #[] = gamAt tl1 mu ∧ tl1.gamV.getD mu #[] = gamAt tl1 mu := by
  unfold HTailF2.weightsF at h
  simp only [bind_ok, ask_ok, get_ok] at h
  obtain ⟨tl2, F2, c2, ⟨hp, _, _⟩, hf, _, _⟩ := h
  obtain ⟨hP, _⟩ := powersF_spec tl tl2 F hp
  have e1 := foldSums_fold _ _ _ hf
  obtain ⟨s1, s2, hall⟩ := foldSums_fold_gam (List.range tl2.NM)
    { tl2 with gamX := Array.replicate tl2.NM #[], gamV := Array.replicate tl2.NM #[] } tl1
    (hP.vt.trans hP.vp.symm) hf
  have eN : tl1.NM = tl2.NM := by rw [e1]
  have z1 : tl1.gamX.size = tl2.NM := by rw [s1]; simp
  have z2 : tl1.gamV.size = tl2.NM := by rw [s2]; simp
  refine ⟨z1.trans eN.symm, z2.trans eN.symm, fun mu hmu => ?_⟩
  rw [eN] at hmu
  obtain ⟨ax, av⟩ := hall mu
    (by
      show mu < (Array.replicate tl2.NM (#[] : Array E)).size
      rw [Array.size_replicate]
      exact hmu)
    (by
      show mu < (Array.replicate tl2.NM (#[] : Array E)).size
      rw [Array.size_replicate]
      exact hmu)
  rw [gamAt_congr _ tl1 e1 mu]
  exact ⟨ax (Or.inl (List.mem_range.2 hmu)), av (Or.inl (List.mem_range.2 hmu))⟩

/-- gamX[mu][p], read: theta written out. cfFirst[mu] is pushFold_array's sum of the earlier k
(drawMatrixF). -/
theorem gamAt_val {tl : HTailF2} {theta : E} (hP : Powered tl theta) (mu p : Nat)
    (hp : p < (tl.mats.getD mu {}).k) :
    ρ.val ((gamAt tl mu).getD p zeroE) = ∑ u ∈ Finset.range tl.tau,
      signOf (K := K) (tl.cfF.getD ((tl.cfFirst.getD mu 0 + p) * tl.tau + u) 0) *
        ρ.val theta ^ u := by
  rw [gamAt, getD_map_range _ _ _ _ hp, foldColumn_val ρ _ _ _ _ (by rw [hP.vp, powers_size])]
  apply Finset.sum_congr rfl
  intro u hu
  rw [hP.vp, powers_val ρ _ _ _ (Finset.mem_range.1 hu)]

/-! ## The closed forms -/

theorem sumFrom_congr {α : Type} (g g' : Nat → α → K) : ∀ (l : List α) (n : Nat),
    (∀ q x, x ∈ l → g q x = g' q x) → sumFrom g n l = sumFrom g' n l
  | [], _, _ => rfl
  | a :: l, n, h => by
    rw [sumFrom, sumFrom, h n a (by simp),
      sumFrom_congr g g' l (n + 1) (fun q x hx => h q x (List.mem_cons_of_mem _ hx))]

/-- The index of matrix mu's first equation (mu = NM: of the first read's), written out. -/
def firstOf (tl : HTailF2) (mu : Nat) : Nat :=
  ∑ nu ∈ Finset.range mu, tl.stepF * 2 ^ clog2 (tl.shp.getD nu {}).mS

/-- The tie's bracket as an expression in θ, numbers of tl, the drawn matrix, and W's entries of
virtual rows. -/
def tieClosed (θ : K) (gam : Nat → Nat → K) (tl : HTailF2) (mu : Nat) : K :=
  -((2 : K) ^ 17 * ((∑ u ∈ Finset.range tl.tau, θ ^ u)
      * ∑ i ∈ Finset.range (tl.shp.getD mu {}).m,
          ((2 : K) ^ 20) ^ (i % 3) * θ ^ (tl.stepF * (i / 3))))
    + ∑ i ∈ Finset.range (tl.shp.getD mu {}).m, ((2 : K) ^ 20) ^ (i % 3) * θ ^ (tl.stepF * (i / 3))
        * W.entry tl.ix.ZZ tl.zzRowTies ((tl.zzCol mu 0 0).getD 0 + i)
    + (2 : K) ^ 10 * ∑ i ∈ Finset.range (tl.shp.getD mu {}).m,
        ((2 : K) ^ 20) ^ (i % 3) * θ ^ (tl.stepF * (i / 3))
          * W.entry tl.ix.ZZ tl.zzRowTies ((tl.zzCol mu 1 0).getD 0 + i)
    - ∑ p ∈ Finset.range (tl.shp.getD mu {}).k, gam mu p * W.entry (tl.gtTree.getD mu 0) 0 p

/-- The read's bracket likewise. phi stays a letter: it is a field of the list that was closed
before the matrix. -/
def readClosed (θ : K) (gam : Nat → Nat → K) (tl : HTailF2) (F0 : Fork) (x : HFun × Nat) : K :=
  -((2 : K) ^ 17 * ((∑ j ∈ Finset.range x.1.phi.size, ρ.val (x.1.phi.getD j zeroE))
      * ∑ u ∈ Finset.range tl.tau, θ ^ u))
    - ∑ d ∈ Finset.range (tl.mats.getD x.1.mat {}).k, gam x.1.mat d
        * W.entry ((tl.ix.U.getD x.1.tree none).getD 0)
            (posOf tl x.1 x.2 d / colsU F0 ((tl.ix.U.getD x.1.tree none).getD 0))
            (posOf tl x.1 x.2 d % colsU F0 ((tl.ix.U.getD x.1.tree none).getD 0))
    + ∑ j ∈ Finset.range x.1.len, ρ.val (x.1.phi.getD j zeroE)
        * W.entry tl.ix.ZZ tl.zzRowReads ((tl.zzCol x.1.mat 0 (x.2 * x.1.len)).getD 0 + j)
    + (2 : K) ^ 10 * ∑ j ∈ Finset.range x.1.len, ρ.val (x.1.phi.getD j zeroE)
        * W.entry tl.ix.ZZ tl.zzRowReads ((tl.zzCol x.1.mat 1 (x.2 * x.1.len)).getD 0 + j)

/-! ## The statement -/

def gamSign (θ : K) (tl : HTailF2) (mu p : Nat) : K :=
  ∑ u ∈ Finset.range tl.tau,
    signOf (K := K) (tl.cfF.getD ((tl.cfFirst.getD mu 0 + p) * tl.tau + u) 0) * θ ^ u

theorem objectsF_fits_total (tl tl' : HTailF2) (funs : Array HFun) (F G : Fork) (c c' : Ctx)
    (h : tl.objectsF funs F c = .ok ((tl', G), c'))
    (hfit : ∀ mu, mu < tl'.NM → (tl'.shp.getD mu {}).m = (tl'.mats.getD mu {}).m ∧
      (tl'.shp.getD mu {}).k = (tl'.mats.getD mu {}).k) :
    ∃ g Fa ca tla Fb cb tlb Fc cc tl1 F1 c1,
      tl.heard = some g ∧ Forest.objects g F c = .ok (((), Fa), ca) ∧
      tl.linJoin9 Fa ca = .ok ((tla, Fb), cb) ∧ tla.linBits9 Fb cb = .ok ((tlb, Fc), cc) ∧
      tlb.weightsF Fc cc = .ok ((tl1, F1), c1) ∧ F1 = Fc ∧ c1 = cc ∧
      (F1.LS.size = F1.ns → c' = c1 ∧ Kept F1 G ∧
        G.nClaim = F1.nClaim + tl'.NM + tl'.nX4Laid ∧
        G.total ρ W = F1.total ρ W
          + ((List.range tl'.NM).map fun mu =>
              ρ.val G.theta ^ (G.planClaimsF + firstOf tl' mu)
                * tieClosed W (ρ.val G.theta) (gamSign (ρ.val G.theta) tl') tl' mu).sum
          + sumFrom (fun q x =>
              ρ.val G.theta ^ (G.planClaimsF + (firstOf tl' tl'.NM + q * tl'.stepF))
                * readClosed ρ W (ρ.val G.theta) (gamSign (ρ.val G.theta) tl') tl' G x) 0
              (readsList tl' funs)) := by
  obtain ⟨g, Fa, ca, tla, Fb, cb, tlb, Fc, cc, tl1, F1, c1, hg, hFo, hJ, hB, hWt, hlaid, etl, _,
    _, himp⟩ :=
    objectsF_total ρ W tl tl' funs F G c c' h
  obtain ⟨eF, ec, hP1, _⟩ := weightsF_spec tlb tl1 Fc F1 cc c1 hWt
  obtain ⟨_, _, hgam1⟩ := weightsF_gam tlb tl1 Fc F1 cc c1 hWt
  refine ⟨g, Fa, ca, tla, Fb, cb, tlb, Fc, cc, tl1, F1, c1, hg, hFo, hJ, hB, hWt, eF, ec,
    fun hs => ?_⟩
  obtain ⟨e1, hk, hn, htot⟩ := himp hs
  have hP : Powered tl' G.theta := by
    rw [hk.theta, eF, etl]
    exact ⟨hP1.vp, hP1.vt, hP1.rowX, hP1.loX, hP1.eqFirst, hP1.shape⟩
  have hgam : ∀ mu, mu < tl'.NM →
      tl'.gamX.getD mu #[] = gamAt tl' mu ∧ tl'.gamV.getD mu #[] = gamAt tl' mu := by
    rw [etl]
    exact hgam1
  have eNM : tl1.NM = tl'.NM := ((congrArg (fun t => t.NM) etl).trans rfl).symm
  have eL : readsList tl1 funs = readsList tl' funs :=
    ((congrArg (fun t => readsList t funs) etl).trans rfl).symm
  have eT : ∀ mu, tieTerm ρ W tl1 F1 mu = tieTerm ρ W tl' F1 mu := fun mu =>
    ((congrArg (fun t => tieTerm ρ W t F1 mu) etl).trans rfl).symm
  have eR : ∀ q x, readTerm ρ W tl1 F1 q x = readTerm ρ W tl' F1 q x := fun q x =>
    ((congrArg (fun t => readTerm ρ W t F1 q x) etl).trans rfl).symm
  refine ⟨e1, hk, by rw [hn, eNM, hlaid], ?_⟩
  rw [htot, eNM, eL]
  congr 1
  · congr 2
    apply List.map_congr_left
    intro mu hmu
    have hmu' : mu < tl'.NM := List.mem_range.1 hmu
    obtain ⟨fm, fk⟩ := hfit mu hmu'
    have eg : (tl'.gamX.getD mu #[]).size = (tl'.shp.getD mu {}).k := by
      rw [(hgam mu hmu').1, gamAt, Array.size_map, Array.size_range, fk]
    have hm : (tl'.shp.getD mu {}).m ≤ 3 * (tl'.shp.getD mu {}).mS := by
      have := (hP.shape mu hmu').2.2.2.2
      rw [fm]
      omega
    obtain ⟨wl, hwl⟩ := hP.tieLeft_some mu hmu'
    obtain ⟨wr, hwr⟩ := hP.tieRight_some mu hmu' eg
    rw [eT, tieTerm, ← hk.theta, ← hk.plan, hP.eqFirst_val mu (Nat.le_of_lt (hP.lt_shp mu hmu')),
      hP.tieBracket_closed ρ W mu hmu' (hP.lt_shp mu hmu') hm wl wr hwl hwr]
    unfold firstOf tieClosed gamSign
    congr 2
    apply Finset.sum_congr rfl
    intro p hp
    rw [(hgam mu hmu').1, gamAt_val ρ hP mu p (by rw [← fk]; exact Finset.mem_range.1 hp)]
  · apply sumFrom_congr
    intro q x hx
    obtain ⟨Fn, sg⟩ := x
    have hmat : Fn.mat < tl'.NM := ((mem_readsList tl' funs Fn sg).1 hx).2.1
    rw [eR, readTerm, ← hk.theta, ← hk.plan, hP.eqFirst_val tl'.NM hP.NM_le_shp,
      hP.readBracket_closed ρ W F1 (Fn, sg)]
    unfold firstOf readClosed gamSign
    simp only [colsU_frame G F1 hk.frame]
    congr 4
    apply Finset.sum_congr rfl
    intro d hd'
    rw [(hgam Fn.mat hmat).2, gamAt_val ρ hP Fn.mat d (Finset.mem_range.1 hd')]

#print axioms weightsF_gam
#print axioms objectsF_fits_total

end OnBytes.Tie.Pv.Tail.Port
