-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TreesLaws.lean: what a claim on long runs of entries adds to the one equation.

OnBytes/Model/Trees.lean adds a claim that holds long runs of entries by steps of its own (pushRun,
t2Lin). This file states for these steps what OnBytes/Model/HideLaws.lean states for Fork.push and
Fork.lin. The setting is that of HideLaws.lean: a reading of the program's arithmetic in a
commutative ring, and a world that gives every hidden value a value. The program does not import
this file.

A run (Run2) is coef times the sum over i below n of w[w0 + i] times entry first + i of one virtual
row.

Main theorems.
   pushRun_value        adding k times a run adds k times the run's value
   Fork.pushRuns_total  adding k times each of several runs adds k times the sum of their values to
                        Fork.total; of the arrays only the values of the weights L change
   Fork.claim_total     a weight taken by Fork.kap, a form and runs added under it: Fork.total
                        grows by theta^c times the value of the form and the runs
   t2Lin_total          Fork.claim_total for the routine t2Lin, run on a state

What this file does not claim. As in HideLaws.lean: nothing where a step refuses; nothing about
probabilities, about what an acceptance shows, about hiding, or about the chain. The values of the
form and of the runs may themselves depend on theta, and in the smallness test
(OnBytes/Model/Tail.lean) they do.
-/
import OnBytes.Model.Trees
import OnBytes.Model.HideLaws

namespace OnBytes.Model

variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)

/-- The sum of h j for j = i, .., i + count - 1. -/
def runSum (h : Nat → K) : (count i : Nat) → K
  | 0, _ => 0
  | count + 1, i => h i + runSum h count (i + 1)

/-- The value of a run in a world: coef * sum_{i < n} w[w0 + i] * (entry first + i of its virtual
row). -/
def Run2.value (r : Run2) : K :=
  ρ.val r.coef *
    runSum (fun i => ρ.val (r.w.getD (r.w0 + i) zeroE) * W.entry r.tree r.row (r.first + i)) r.n 0

/-- The loop of pushRun, run for j = i, .., i + count - 1, adds
kc * sum_j w[w0 + j] * e(s + first + j) to the sum over all j of L[j] * e(s + j), for any values e.
Hypothesis: the places first + j of the run lie inside L. s: the index of L's first element. -/
theorem runLoop_value (e : Nat → K) (kc : E) (w : Array E) (w0 first s : Nat) :
    ∀ (count i : Nat) (L : Array E), first + i + count ≤ L.size →
      sumFrom (fun j v => ρ.val v * e j) s (runLoop kc w w0 first count i L).toList =
        sumFrom (fun j v => ρ.val v * e j) s L.toList +
          ρ.val kc * runSum (fun j => ρ.val (w.getD (w0 + j) zeroE) * e (s + (first + j))) count i
  | 0, i, L, _ => by simp [runLoop, runSum]
  | count + 1, i, L, h => by
    simp only [runLoop, runSum]
    split_ifs with hz
    · rw [runLoop_value e kc w w0 first s count (i + 1) L (by omega), isZeroE_eq hz, ρ.zero]
      ring
    · have hv : L.toList[first + i]? = some L[first + i] := by
        have : first + i < L.size := by omega
        simp [this]
      rw [runLoop_value e kc w w0 first s count (i + 1) _ (by simp only [Array.size_modify]; omega),
        Array.toList_modify, sumFrom_modify _ _ _ s (first + i) _ hv, ρ.add, ρ.mul]
      ring

/-- The loop of pushRun keeps the number of the weights. -/
theorem size_runLoop (kc : E) (w : Array E) (w0 first : Nat) :
    ∀ (count i : Nat) (L : Array E), (runLoop kc w w0 first count i L).size = L.size
  | 0, _, _ => rfl
  | count + 1, i, L => by
    simp only [runLoop]
    split_ifs
    · exact size_runLoop kc w w0 first count (i + 1) L
    · rw [size_runLoop kc w w0 first count (i + 1) _, Array.size_modify]

/-- Adding a run changes nothing in the arrays except the values of weights L. -/
theorem pushRun_frame (k : E) (trees trees' : Array HTree) (r : Run2)
    (h : pushRun k trees r = some trees') : treesFrame trees' = treesFrame trees := by
  unfold pushRun at h
  split at h
  · have ht := Option.some.inj h
    subst ht
    unfold treesFrame
    apply map_modify_same
    intro X
    simp only [HTree.frame, Prod.mk.injEq, true_and]
    apply map_modify_same
    intro R
    simp [HRow.frame, size_runLoop]
  · simp at h

/-- What runFits finds: the array and the virtual row that a run names, and that the run fits inside
the row's weights. -/
theorem runFits_spec {trees : Array HTree} {r : Run2} (h : runFits trees r = true) :
    ∃ X R, trees.toList[r.tree]? = some X ∧ X.rows.toList[r.row]? = some R ∧ R.L0 ≤ r.first ∧
      r.first - R.L0 + r.n ≤ R.L.size := by
  unfold runFits at h
  split at h
  · simp at h
  · rename_i X hX
    split at h
    · simp at h
    · rename_i R hR
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨_, _⟩, h3⟩, h4⟩, h5⟩ := h
      exact ⟨X, R, by simpa using hX, by simpa using hR, h3, by omega⟩

/-- Adding k times a run adds k times the run's value to treesValue, the arrays' part of
Fork.total. -/
theorem pushRun_value (k : E) (trees trees' : Array HTree) (r : Run2)
    (h : pushRun k trees r = some trees') :
    treesValue ρ W trees' = treesValue ρ W trees + ρ.val k * Run2.value ρ W r := by
  unfold pushRun at h
  split at h
  · rename_i hh
    obtain ⟨X, R, hX, hR, hle, hin⟩ := runFits_spec hh
    have ht := Option.some.inj h
    subst ht
    simp only [treesValue, Array.toList_modify]
    rw [sumFrom_modify _ _ _ 0 r.tree X hX]
    simp only [HTree.value, Array.toList_modify]
    rw [sumFrom_modify _ _ _ 0 r.row R hR]
    simp only [HRow.value]
    rw [runLoop_value ρ _ _ _ _ _ R.L0 r.n 0 R.L (by omega)]
    have hi : ∀ j, R.L0 + (r.first - R.L0 + j) = r.first + j := fun j => by omega
    simp only [hi, ρ.mul, Run2.value, Nat.zero_add]
    ring
  · simp at h

/-- Adding k times each of several runs adds k times the sum of their values. Of the state only the
arrays change, and of the arrays only the values of the weights L. -/
theorem Fork.pushRuns_total (F G : Fork) (k : E) (runs : Array Run2)
    (h : F.pushRuns k runs = some G) :
    G.total ρ W = F.total ρ W + ρ.val k * (runs.toList.map (Run2.value ρ W)).sum ∧
      G = { F with trees := G.trees } ∧ treesFrame G.trees = treesFrame F.trees := by
  unfold Fork.pushRuns at h
  dsimp only at h
  cases hq : Array.foldlM (pushRun k) F.trees runs with
  | none => simp [hq] at h
  | some trees' =>
    rw [hq] at h
    have hG : { F with trees := trees' } = G := by simpa using h
    subst hG
    rw [← Array.foldlM_toList] at hq
    have e1 := foldlM_adds (pushRun k) (fun s => treesFrame s = treesFrame F.trees)
      (treesValue ρ W) (fun x => ρ.val k * Run2.value ρ W x)
      (fun s x s' hi hx => ⟨(pushRun_frame k s s' x hx).trans hi, pushRun_value ρ W k s s' x hx⟩)
      _ _ _ rfl hq
    refine ⟨?_, rfl, e1.1⟩
    simp only [Fork.total]
    rw [e1.2, List.sum_map_mul_left]
    ring

/-- One claim: a weight is taken, and a form and runs are added under it. Fork.total grows by
theta^c times the value of the form and the runs, where c is nClaim. -/
theorem Fork.claim_total (F F1 F2 G : Fork) (k : E) (a : Aff) (runs : Array Run2)
    (hs : F.LS.size = F.ns) (h1 : F.kap = some (k, F1)) (h2 : F1.push k a = some F2)
    (h3 : F2.pushRuns k runs = some G) :
    G.total ρ W = F.total ρ W + ρ.val F.theta ^ F.nClaim *
        (a.value ρ W + (runs.toList.map (Run2.value ρ W)).sum) ∧
      G.nClaim = F.nClaim + 1 ∧ G.theta = F.theta ∧ G.ns = F.ns ∧ G.LS.size = G.ns ∧
      treesFrame G.trees = treesFrame F.trees := by
  obtain ⟨hk, hF1, _, _⟩ := Fork.kap_spec F F1 k h1
  have hs1 : F1.LS.size = F1.ns := by rw [hF1]; exact hs
  obtain ⟨t2, hF2, hs2, fr2⟩ := Fork.push_total ρ W F1 F2 k a hs1 h2
  obtain ⟨t3, hG, fr3⟩ := Fork.pushRuns_total ρ W F2 G k runs h3
  have t1 : F1.total ρ W = F.total ρ W := by rw [hF1]; rfl
  have tr1 : F1.trees = F.trees := by rw [hF1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [t3, t2, t1, hk, ρ.pow]
    ring
  · rw [hG, hF2, hF1]
  · rw [hG, hF2, hF1]
  · rw [hG, hF2, hF1]
  · rw [hG]; exact hs2
  · rw [fr3, fr2, tr1]

/-- The routine t2Lin, run from a state F and a context c of Blk (Ctx, OnBytes/Iop/Ground.lean): if
it succeeds, the context is unchanged, and the new state has grown as Fork.claim_total says. -/
theorem t2Lin_total (a : Aff) (runs : Array Run2) (F G : Fork) (c c' : Ctx)
    (hs : F.LS.size = F.ns) (h : t2Lin a runs F c = .ok (((), G), c')) :
    c' = c ∧ G.total ρ W = F.total ρ W + ρ.val F.theta ^ F.nClaim *
        (a.value ρ W + (runs.toList.map (Run2.value ρ W)).sum) ∧
      G.nClaim = F.nClaim + 1 ∧ G.theta = F.theta ∧ G.ns = F.ns ∧ G.LS.size = G.ns ∧
      treesFrame G.trees = treesFrame F.trees := by
  simp only [t2Lin, SubM.kap, SubM.push, SubM.change, SubM.take, bind, StateT.bind] at h
  cases h1 : F.kap with
  | none => simp [h1, liftOption_none, Except.bind] at h
  | some x =>
    obtain ⟨k, F1⟩ := x
    simp only [h1, Option.map_some, liftOption_some, Except.bind] at h
    cases h2 : F1.push k a with
    | none => simp [h2, liftOption_none] at h
    | some F2 =>
      simp only [h2, Option.map_some, liftOption_some] at h
      cases h3 : F2.pushRuns k runs with
      | none => simp [h3, liftOption_none] at h
      | some G' =>
        simp only [h3, Option.map_some, liftOption_some, Except.ok.injEq, Prod.mk.injEq,
          true_and] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, Fork.claim_total ρ W F F1 F2 G' k a runs hs h1 h2 h3⟩

end OnBytes.Model

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms OnBytes.Model.pushRun_value
#print axioms OnBytes.Model.t2Lin_total
