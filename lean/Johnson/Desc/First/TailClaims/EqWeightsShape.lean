-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/TailClaims/EqWeightsShape.lean: THE SMALLNESS TEST: WHAT THE WEIGHTS' STEP OF ITS
RUN OF EQUATIONS (eqWeights, Johnson/Desc/First/TailClaims/Equations.lean) DOES TO THE SHAPE OF THE
RECORD (Johnson/Desc/First/Shape/Tail.lean): ONE UPDATE, EXACT. A law from a return: nothing is
evaluated, and nothing is said on whether the step returns.

  powU            the powers' part: two sizes, the rows' sizes, the first exponents; the sums' rows
                  laid empty.
  sumU mu         one matrix's sums: its mark set, two rows' sizes laid.
  weightsU        THE UPDATE: powU, then sumU for each matrix: the step's own fold, on numbers.
  powersF_shape, foldSums_shape, foldAll_shape   part by part.
  **eqWeights_shape**   eqWeights tl front s = .ok (tl', s') gives
                  tailSh tl' = weightsU (tailSh tl), and s' = s.

Limits. From a return alone. Nothing on values. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.TailClaims.EquationsRuns
import Johnson.Desc.First.Shape.Tail
import OnBytes.Tie.Pv.Tail.EndClaimsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First.Shape

/-- The powers' part, and the sums' rows laid empty. -/
def powU (t : TailSh) : TailSh :=
  { t with
    vt := t.tau, vp := t.tau
    eqFirst := t.shp.foldl
      (fun a s => a.push (a.getD (a.size - 1) 0 + 2 ^ clog2 t.tau * 2 ^ clog2 s.mS)) #[0]
    rowX := t.shp.toList.map (·.mS), loX := t.shp.toList.map fun _ => 1
    gamX := List.replicate t.NM 0, gamV := List.replicate t.NM 0 }

/-- One matrix's sums. -/
def sumU (mu : Nat) (t : TailSh) : TailSh :=
  { t with
    foldTakenF :=
      (if t.foldTakenF.size != t.NM then Array.replicate t.NM false else t.foldTakenF).set! mu true
    gamX := t.gamX.set mu (t.mats.getD mu {}).k
    gamV := t.gamV.set mu (t.mats.getD mu {}).k }

/-- **THE UPDATE.** -/
def weightsU (t : TailSh) : TailSh := (List.range t.NM).foldl (fun x mu => sumU mu x) (powU t)

theorem powersF_shape {tl tl1 : HTailF2} {F : Fork} (h : tl.powersF F = some tl1) :
    tailSh { tl1 with gamX := Array.replicate tl1.NM #[], gamV := Array.replicate tl1.NM #[] } =
      powU (tailSh tl) := by
  unfold HTailF2.powersF at h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Option.some.inj h
    unfold tailSh powU
    simp [OnBytes.Tie.Pv.Tail.Port.powers_size, HTailF2.stepF, Function.comp_def]

/-- The sizes of the rows behind a write. -/
theorem sizes_set (a : Array (Array E)) (mu : Nat) (v : Array E) :
    (a.set! mu v).toList.map (·.size) = (a.toList.map (·.size)).set mu v.size := by
  simp [Array.set!, List.map_set]

theorem foldSums_shape {x x' : HTailF2} {mu : Nat} (h : x.foldSums mu = some x') :
    tailSh x' = sumU mu (tailSh x) := by
  unfold HTailF2.foldSums at h
  dsimp only at h
  by_cases hc : (decide (mu ≥ x.NM) || (if x.foldTakenF.size != x.NM then
      Array.replicate x.NM false else x.foldTakenF).getD mu true) = true
  · rw [if_pos hc] at h
    cases h
  · rw [if_neg hc] at h
    obtain rfl := Option.some.inj h
    unfold tailSh sumU
    dsimp only
    rw [sizes_set, sizes_set]
    have e : (if x.vt == x.vp then
        (Array.range (x.mats.getD mu {}).k).map fun c =>
          HTailF2.foldColumn x.cfF ((x.cfFirst.getD mu 0 + c) * x.tau) x.tau x.vp
      else (Array.range (x.mats.getD mu {}).k).map fun c =>
          HTailF2.foldColumn x.cfF ((x.cfFirst.getD mu 0 + c) * x.tau) x.tau x.vt).size =
        (x.mats.getD mu {}).k := by
      split <;> simp
    rw [e]
    simp

theorem foldAll_shape : ∀ (l : List Nat) (x x' : HTailF2),
    l.foldlM (fun (x : HTailF2) mu => x.foldSums mu) x = some x' →
      tailSh x' = l.foldl (fun t mu => sumU mu t) (tailSh x)
  | [], x, x', h => by
    obtain rfl : x = x' := by simpa using h
    rfl
  | mu :: l, x, x', h => by
    rw [List.foldlM_cons] at h
    cases hs : x.foldSums mu with
    | none =>
      rw [hs] at h
      cases h
    | some y =>
      rw [hs] at h
      rw [List.foldl_cons, ← foldSums_shape hs]
      exact foldAll_shape l y x' h

/-- **What the weights' step does to the record's shape**, and that it leaves the state. -/
theorem eqWeights_shape {tl tl' : HTailF2} {front : Nat} {s s' : St}
    (h : eqWeights tl front s = .ok (tl', s')) : tailSh tl' = weightsU (tailSh tl) ∧ s' = s := by
  unfold eqWeights at h
  obtain ⟨tl1, s1, h1, h2⟩ := (eq_bind_ok _ _ _ _ _).1 h
  obtain ⟨hp, rfl⟩ := eq_ask_ok h1
  obtain ⟨hf, rfl⟩ := eq_get_ok h2
  refine ⟨?_, rfl⟩
  have eN : tl1.NM = tl.NM := by
    have := congrArg TailSh.NM (powersF_shape hp)
    exact this
  rw [foldAll_shape _ _ _ hf, powersF_shape hp, eN]
  rfl

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.powersF_shape
#print axioms VerifiableInference.Desc.First.TailClaims.Law.sizes_set
#print axioms VerifiableInference.Desc.First.TailClaims.Law.foldSums_shape
#print axioms VerifiableInference.Desc.First.TailClaims.Law.foldAll_shape
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eqWeights_shape
#print axioms VerifiableInference.Desc.First.TailClaims.Law.powU
#print axioms VerifiableInference.Desc.First.TailClaims.Law.sumU
#print axioms VerifiableInference.Desc.First.TailClaims.Law.weightsU
