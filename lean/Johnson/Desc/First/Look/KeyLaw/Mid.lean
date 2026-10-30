-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid.lean: the join of the planes' claims, and the parts' key trees.

Main names:
  eqTab_read: an entry of the kind's table of equality weights, read, is the course's weight.
  join_loop_sim: the planes' claims as one: the kind's form reads as the course's joined claim.
  keysPat, keysShape; keys_sim: keysG against the course's cKey.

Limits. One world W of mask entries; where the flat functions return.

-/
import Johnson.Desc.First.Look.KeyLaw.Levels
import OnBytes.Tie.Pv.Lookup.Port.FoTwins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundName RoundForm Reading World eqTab)
open OnBytes.PscRun (took Later Sized Filled Ran)
open First.Prod (wholeStandIn Whole Carried turn level stepDown layBack)
open Lk6.PortSim (noClaim sProd lineF byVarF joinF joinOneF joinAtF eqW)
open Lk6.Mid (Dt Cs RowF pscC heardF slots eqPairsF cLevels ordFirst ordDown cKey)

/-! ## The join -/

theorem eqW_eqN : ∀ (xs : List GE) (j : ℕ) (r : GE), eqW xs j r = r * TwV.eqN xs j
  | [], _, r => by simp [eqW, TwV.eqN]
  | x :: xs, j, r => by
    show eqW xs (j / 2) (r * (if j % 2 == 1 then x else 1 - x)) = _
    rw [eqW_eqN xs]
    show _ = r * ((if j % 2 = 1 then x else 1 - x) * TwV.eqN xs (j / 2))
    by_cases h : j % 2 = 1 <;> simp [h] <;> ring

/-- An entry of the table of equality weights at the drawn point, turned. -/
theorem eqTab_read (x : Array E) (j : ℕ) (hj : j < 2 ^ x.size) :
    readE ((eqTab x.reverse).getD j zeroE) = eqW (x.toList.map readE) j 1 := by
  have h1 := Fo.eqTab_val rho x.reverse
  have h2 := Fo.eqTabK_get (Fo.rdL rho x.reverse) j
  rw [← h1] at h2
  have e : (Fo.rdL rho (eqTab x.reverse)).getD j 0 = readE ((eqTab x.reverse).getD j zeroE) := by
    show ((eqTab x.reverse).toList.map readE).getD j 0 = _
    rw [read_getD, arr_getD]
  rw [e] at h2
  rw [h2, if_pos (by simpa [Fo.rdL] using hj), eqW_eqN, one_mul]
  congr 1
  simp [Fo.rdL]
  intro a _
  rfl

variable {W : PscF.World} {home : ℕ → Slot} {D : Dt}

/-- The loop that makes the planes' claims one. -/
theorem join_loop_sim {F : Fork} {pl : ℕ} {sG : Array ℕ} {ej : Array E} {r : List GE}
    {planes : ℕ → PscF.PointClaim}
    (hp : ∀ j < pl, RC W home F (Aff.slot (sG.getD j 0)) (planes j)) :
    ∀ (js : List ℕ) (a : Aff) (c : PscF.PointClaim), RC W home F a c →
    (∀ j ∈ js, readE (ej.getD j zeroE) = eqW r j 1) →
    RC W home F
      (js.foldl (fun (c : Aff) j =>
        if j < pl then Aff.addMul c (Aff.slot (sG.getD j 0)) (ej.getD j zeroE)
        else c + Aff.ofConst (ej.getD j zeroE)) a)
      (js.foldl (joinOneF r ((List.range pl).map planes)) c)
  | [], a, c, h, _ => h
  | j :: js, a, c, h, he => by
    rw [List.foldl_cons, List.foldl_cons]
    refine join_loop_sim hp js _ _ ?_ fun i hi => he i (List.mem_cons_of_mem _ hi)
    have hj := he j List.mem_cons_self
    unfold joinOneF
    by_cases hlt : j < pl
    · rw [if_pos hlt]
      have e : ((List.range pl).map planes)[j]? = some (planes j) := by
        simp [hlt]
      rw [e]
      have := Reads.addMul h (hp j hlt) (ej.getD j zeroE)
      rw [hj] at this
      exact this
    · rw [if_neg hlt]
      have e : ((List.range pl).map planes)[j]? = none := by
        simp; omega
      rw [e]
      have := Reads.add h (Reads.const (W := W) (home := home) F (ej.getD j zeroE))
      rw [hj] at this
      exact this.congr (by rw [List.append_nil]; rfl) rfl

/-! ## The key trees -/

def keysPat (vs : List ℕ) : List Bool := vs.flatMap fun v => levelsPat true 0 v 0

def keysShape (vs : List ℕ) : List Shape := vs.flatMap fun v => levelsShape 0 v 0

theorem cKey_succ (D : Dt) (n i : ℕ) (s : Cs) :
    cKey D (n + 1) i s = cKey D n (i + 1)
      { (cLevels D true 0 (D.S.v i) 0 (s.roots i) s).2 with
        leaves := Function.update (cLevels D true 0 (D.S.v i) 0 (s.roots i) s).2.leaves i
          (cLevels D true 0 (D.S.v i) 0 (s.roots i) s).1 } := rfl

/-- **The parts' key trees.** -/
theorem keys_sim (f : Face) : ∀ (vs : List ℕ) (i : ℕ) (Cs' : List Aff) (rows : Array Aff)
    (F G : Fork) (t u : Tape) (res : Array Aff × List (Array E × Aff)) (s : Cs) (pat : List Bool),
    keysG f (vs.zipIdx i) Cs' rows F t = some (res, G, u) → Cs'.length = vs.length →
    (∀ q < vs.length, D.S.v (i + q) = vs.getD q 0 ∧
      OrdIs D true 0 (f.orders (i + q)) (vs.getD q 0) 0) →
    St W home D F t s (keysPat vs ++ pat) rows.toList →
    (∀ q < vs.length, RC W home F (Cs'.getD q {}) (s.roots (i + q)) ∧
      (s.roots (i + q)).point = []) →
    St W home D G u (cKey D vs.length i s) pat res.1.toList ∧ res.2.length = vs.length ∧
      (∀ q < vs.length, RC W home G (res.2.getD q (#[], {})).2 ((cKey D vs.length i s).leaves (i +
          q)) ∧
        ((cKey D vs.length i s).leaves (i + q)).point =
          (res.2.getD q (#[], {})).1.toList.reverse.map readE) ∧
      (∀ q < i, (cKey D vs.length i s).leaves q = s.leaves q) ∧
      (cKey D vs.length i s).alpha = s.alpha ∧ (cKey D vs.length i s).top = s.top ∧ Later F G ∧
      Shp t u (keysShape vs) := by
  intro vs
  induction vs with
  | nil =>
    intro i Cs' rows F G t u res s pat h _ _ hst _
    have h' : (pure (rows, []) : Fl (Array Aff × List (Array E × Aff))) F t = some (res, G, u) := by
      cases Cs' <;> exact h
    cases pure_some h'
    exact ⟨hst, rfl, fun q hq => (by cases hq), fun _ _ => rfl, rfl, rfl, Later.refl _, Shp.refl _⟩
  | cons v vs ih =>
    intro i Cs' rows F G t u res s pat h hl hv hst hC
    cases Cs' with
    | nil => simp at hl
    | cons C Cs' =>
      rw [List.zipIdx_cons] at h
      unfold keysG at h
      replace h := bind_some h
      obtain ⟨k, G1, u1, h1, h⟩ := h
      replace h := bind_some h
      obtain ⟨y, G2, u2, h2, h⟩ := h
      cases pure_some h
      unfold First.Prod.run at h1
      rw [List.range_eq_range'] at h1
      obtain ⟨hv0, ho0⟩ := hv 0 (by simp)
      obtain ⟨hC0, hP0⟩ := hC 0 (by simp)
      rw [Nat.add_zero] at hv0 ho0 hC0 hP0
      have hv0' : D.S.v i = v := hv0
      have ho0' : OrdIs D true 0 (f.orders i) v 0 := ho0
      obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := levels_sim true 0 (f.orders i) v 0 _ k F G1 t u1
        (s.roots i) s (keysPat vs ++ pat) h1 ho0'
        (by
          have : keysPat (v :: vs) ++ pat = levelsPat true 0 v 0 ++ (keysPat vs ++ pat) := by
            show (levelsPat true 0 v 0 ++ keysPat vs) ++ pat = _
            rw [List.append_assoc]
          rw [this] at hst
          exact hst)
        hC0 (by rw [hP0]; rfl) rfl
      rw [List.length_cons, cKey_succ, hv0']
      generalize cLevels D true 0 v 0 (s.roots i) s = r at l1 l2 l3 l5 ⊢
      obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := ih (i + 1) Cs' k.rows G1 _ u1 _ y
        { r.2 with leaves := Function.update r.2.leaves i r.1 } pat h2 (by simpa using hl)
        (fun q hq => by
          have := hv (q + 1) (by simpa using hq)
          rwa [show i + (q + 1) = i + 1 + q by omega, List.getD_cons_succ] at this)
        (l1.congr rfl rfl rfl rfl)
        (fun q hq => by
          have := hC (q + 1) (by simpa using hq)
          rw [show i + (q + 1) = i + 1 + q by omega, List.getD_cons_succ] at this
          show RC W home G1 _ (r.2.roots (i + 1 + q)) ∧ (r.2.roots (i + 1 + q)).point = []
          rw [l5.roots]
          exact ⟨this.1.later l6, this.2⟩)
      refine ⟨r1, by simp [r2], fun q hq => ?_, fun q hq => ?_, r5.trans l5.alpha, r6.trans l5.top,
        l6.trans r7, l7.trans r8⟩
      · cases q with
        | zero =>
          have e := (r4 i (by omega)).trans (Function.update_self i r.1 r.2.leaves)
          exact ⟨(congrArg (RC W home G k.form) e).mpr (l2.later r7),
            (congrArg (·.point) e).trans l3⟩
        | succ q =>
          have := r3 q (by simpa using hq)
          rwa [show i + 1 + q = i + (q + 1) by omega] at this
      · exact (r4 q (by omega)).trans ((Function.update_of_ne (by omega) _ _).trans
          (congrFun l5.leaves q))

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.eqTab_read
#print axioms VerifiableInference.Desc.K3.KeyLaw.join_loop_sim
#print axioms VerifiableInference.Desc.K3.KeyLaw.keys_sim
