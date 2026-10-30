-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/DotLaws.lean: the inner product of a structured vector with a written-out vector.

A tensor is a vector of product form, and a form is a sum of tensors and single entries
(OnBytes/Iop/Tensor.lean). Form.dot computes the inner product of a form with a written-out vector.
A tensor without a written-out factor whose pairs are all (1, 0), (0, h) or (1, h) with h in the
base field goes coordinate by coordinate on machine words (Tensor.dotInF, which returns none for any
other tensor); the other parts are written out (Form.writeOut) and multiplied entry by entry
(Form.dotPlain). The law, for a form whose tensors all have n variables: under any reading of the
program's field elements in a commutative ring (Model.Reading, see OnBytes/Iop/TensorLaws.lean),
Form.dot f n a reads as the sum over the indices j below 2^n of entry j of the form times entry j of
the vector. An entry that the vector lacks counts as 0; its entries from 2^n on do not count.

Main theorems: dotSteps_coords, dotStepsE_val, Tensor.dotInF_val, Form.writeOut_val,
Form.dotPlain_val, Form.dot_val. The definitions of this file serve their proofs.

What is not claimed. That Form.dot and Form.dotPlain return the same words; shown is only that both
read as the same sum. Nothing on a form with a tensor of another number of variables. Nothing on
soundness. The program does not import this file.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import OnBytes.Iop.SpreadLaws
import OnBytes.Iop.RowLaws

namespace OnBytes

open Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- dotSteps, computed on whole elements of the extension field instead of on one coordinate. -/
def dotStepsE (a : Array E) : List FStep → Nat → Nat → E
  | [], _, offset => a.getD offset zeroE
  | .low :: ps, w, offset => dotStepsE a ps (w / 2) offset
  | .high h :: ps, w, offset => scaleE h (dotStepsE a ps (w / 2) (offset + w))
  | .both h :: ps, w, offset =>
    addE (dotStepsE a ps (w / 2) offset) (scaleE h (dotStepsE a ps (w / 2) (offset + w)))

/-- The three coordinates that dotSteps computes are those of dotStepsE. -/
theorem dotSteps_coords (a : Array E) : ∀ (ps : List FStep) (w offset : Nat),
    E.mk3 (dotSteps a 0 ps w offset) (dotSteps a 1 ps w offset) (dotSteps a 2 ps w offset) =
      dotStepsE a ps w offset
  | [], _, offset => by
    simp only [dotSteps, dotStepsE, coordE]
    exact E.mk3_eta _
  | .low :: ps, w, offset => by
    simp only [dotSteps, dotStepsE]
    exact dotSteps_coords a ps _ _
  | .high h :: ps, w, offset => by
    simp only [dotSteps, dotStepsE]
    rw [← dotSteps_coords a ps]
    simp only [scaleE, E.c0_mk3, E.c1_mk3, E.c2_mk3]
  | .both h :: ps, w, offset => by
    simp only [dotSteps, dotStepsE]
    rw [← dotSteps_coords a ps (w / 2) offset, ← dotSteps_coords a ps (w / 2) (offset + w)]
    simp only [scaleE, addE, E.c0_mk3, E.c1_mk3, E.c2_mk3]

/-- What a step's half reads as: the high half if b, else the low half. -/
def stepHalf (s : FStep) (b : Bool) : K :=
  match s with
  | .low => if b then 0 else 1
  | .high h => if b then ρ.val (ofF h) else 0
  | .both h => if b then ρ.val (ofF h) else 1

/-- The product of the steps' halves that the bits of j pick, for steps from the highest variable
down. -/
def stepsVal : List FStep → Nat → K
  | [], _ => 1
  | s :: ps, j => stepHalf ρ s (j / 2 ^ ps.length % 2 == 1) * stepsVal ps (j % 2 ^ ps.length)

/-- A sum over 2^(n+1) indices splits at the highest bit. -/
theorem sum_split (n : Nat) (f : Nat → K) :
    ∑ j ∈ Finset.range (2 ^ (n + 1)), f j =
      ∑ j ∈ Finset.range (2 ^ n), f j + ∑ j ∈ Finset.range (2 ^ n), f (2 ^ n + j) := by
  have e : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
    rw [Nat.pow_succ]
    omega
  rw [e, Finset.sum_range_add]

/-- The weight that a list of steps needs: that of its highest variable's bit. -/
def weightOk : List FStep → Nat → Prop
  | [], _ => True
  | _ :: ps, w => w = 2 ^ ps.length

/-- The list without its first step needs half the weight. -/
theorem weightOk_half (s : FStep) (ps : List FStep) (w : Nat) (h : weightOk (s :: ps) w) :
    weightOk ps (w / 2) := by
  cases ps with
  | nil => trivial
  | cons t qs =>
    show w / 2 = 2 ^ qs.length
    have : w = 2 ^ (qs.length + 1) := h
    rw [this, Nat.pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2)]

/-- If w is the weight of the first step's bit (weightOk), dotStepsE reads as the sum, over j below
2 to the number of steps, of the steps' product at j times entry offset + j. -/
theorem dotStepsE_val (a : Array E) : ∀ (ps : List FStep) (w offset : Nat), weightOk ps w →
    ρ.val (dotStepsE a ps w offset) =
      ∑ j ∈ Finset.range (2 ^ ps.length), stepsVal ρ ps j * ρ.val (a.getD (offset + j) zeroE)
  | [], _, offset, _ => by
    simp [dotStepsE, stepsVal]
  | s :: ps, w, offset, hw => by
    have hw' : w = 2 ^ ps.length := hw
    have ih0 := dotStepsE_val a ps (w / 2) offset (weightOk_half s ps w hw)
    have ih1 := dotStepsE_val a ps (w / 2) (offset + w) (weightOk_half s ps w hw)
    have lo : ∀ j ∈ Finset.range (2 ^ ps.length),
        j / 2 ^ ps.length % 2 = 0 ∧ j % 2 ^ ps.length = j := by
      intro j hj
      have := Finset.mem_range.1 hj
      exact ⟨by rw [Nat.div_eq_of_lt this], Nat.mod_eq_of_lt this⟩
    have hi : ∀ j ∈ Finset.range (2 ^ ps.length),
        (2 ^ ps.length + j) / 2 ^ ps.length % 2 = 1 ∧ (2 ^ ps.length + j) % 2 ^ ps.length = j := by
      intro j hj
      have h := Finset.mem_range.1 hj
      constructor
      · rw [Nat.add_div_left _ (Nat.two_pow_pos _), Nat.div_eq_of_lt h]
      · rw [Nat.add_mod_left, Nat.mod_eq_of_lt h]
    rw [List.length_cons, sum_split]
    have s0 : ∀ (c0 : K), (∀ j ∈ Finset.range (2 ^ ps.length),
        stepsVal ρ (s :: ps) j = c0 * stepsVal ρ ps j) →
        ∑ j ∈ Finset.range (2 ^ ps.length),
          stepsVal ρ (s :: ps) j * ρ.val (a.getD (offset + j) zeroE) =
          c0 * ρ.val (dotStepsE a ps (w / 2) offset) := by
      intro c0 hc
      rw [ih0, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hc j hj]
      ring
    have s1 : ∀ (c1 : K), (∀ j ∈ Finset.range (2 ^ ps.length),
        stepsVal ρ (s :: ps) (2 ^ ps.length + j) = c1 * stepsVal ρ ps j) →
        ∑ j ∈ Finset.range (2 ^ ps.length),
          stepsVal ρ (s :: ps) (2 ^ ps.length + j) *
            ρ.val (a.getD (offset + (2 ^ ps.length + j)) zeroE) =
          c1 * ρ.val (dotStepsE a ps (w / 2) (offset + w)) := by
      intro c1 hc
      rw [ih1, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hc j hj, hw', Nat.add_assoc]
      ring
    cases s with
    | low =>
      rw [s0 1 (fun j hj => by
          show stepHalf ρ .low (j / 2 ^ ps.length % 2 == 1) * _ = _
          rw [(lo j hj).1, (lo j hj).2]
          simp [stepHalf]),
        s1 0 (fun j hj => by
          show stepHalf ρ .low ((2 ^ ps.length + j) / 2 ^ ps.length % 2 == 1) * _ = _
          rw [(hi j hj).1, (hi j hj).2]
          simp [stepHalf])]
      simp [dotStepsE]
    | high h =>
      rw [s0 0 (fun j hj => by
          show stepHalf ρ (.high h) (j / 2 ^ ps.length % 2 == 1) * _ = _
          rw [(lo j hj).1, (lo j hj).2]
          simp [stepHalf]),
        s1 (ρ.val (ofF h)) (fun j hj => by
          show stepHalf ρ (.high h) ((2 ^ ps.length + j) / 2 ^ ps.length % 2 == 1) * _ = _
          rw [(hi j hj).1, (hi j hj).2]
          simp [stepHalf])]
      simp [dotStepsE, scaleE_val]
    | both h =>
      rw [s0 1 (fun j hj => by
          show stepHalf ρ (.both h) (j / 2 ^ ps.length % 2 == 1) * _ = _
          rw [(lo j hj).1, (lo j hj).2]
          simp [stepHalf]),
        s1 (ρ.val (ofF h)) (fun j hj => by
          show stepHalf ρ (.both h) ((2 ^ ps.length + j) / 2 ^ ps.length % 2 == 1) * _ = _
          rw [(hi j hj).1, (hi j hj).2]
          simp [stepHalf])]
      simp [dotStepsE, scaleE_val, ρ.add]

/-- If fStep makes the step s of the pair p, each half of p reads as that half of s (stepHalf). -/
theorem fStep_val (p : E × E) (s : FStep) (h : fStep p = some s) (b : Bool) :
    ρ.val (if b then p.2 else p.1) = stepHalf ρ s b := by
  unfold stepHalf
  unfold fStep at h
  split at h
  · cases h
  · rename_i hz
    simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq] at hz
    obtain ⟨⟨⟨z1, z2⟩, z3⟩, z4⟩ := hz
    have e2 : p.2 = ofF p.2.c0 := E.ext3 rfl z3 z4
    split at h
    · rename_i h1
      have e1 : p.1 = oneE := E.ext3 (beq_iff_eq.1 h1) z1 z2
      split at h
      · rename_i h0
        cases h
        have e3 : p.2 = zeroE := E.ext3 (beq_iff_eq.1 h0) z3 z4
        cases b <;> simp [e1, e3, ρ.one, ρ.zero]
      · cases h
        cases b
        · simp [e1, ρ.one]
        · simp only [if_true]
          rw [← e2]
    · split at h
      · rename_i h0
        cases h
        have e1 : p.1 = zeroE := E.ext3 (beq_iff_eq.1 h0) z1 z2
        cases b
        · simp [e1, ρ.zero]
        · simp only [if_true]
          rw [← e2]
      · cases h

/-- If mapM fStep makes a list of steps of a list of pairs, each step is made of the pair at its
place. -/
theorem mapM_fStep : ∀ (ps : List (E × E)) (steps : List FStep), ps.mapM fStep = some steps →
    List.Forall₂ (fun p s => fStep p = some s) ps steps
  | [], steps, h => by
    have e : steps = [] := by simpa using h.symm
    subst e
    exact List.Forall₂.nil
  | p :: ps, steps, h => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨s, hs, rest, hr, rfl⟩ := h
    exact List.Forall₂.cons hs (mapM_fStep ps rest hr)

/-- For steps made of pairs one by one, the steps' product at j (stepsVal) is the pairs' product at
j (pairsValHigh). -/
theorem stepsVal_eq : ∀ (ps : List (E × E)) (steps : List FStep),
    List.Forall₂ (fun p s => fStep p = some s) ps steps → ∀ j,
    stepsVal ρ steps j = pairsValHigh ρ ps j
  | [], _, h, _ => by
    cases h
    rfl
  | p :: ps, _, h, j => by
    cases h with
    | cons hs hr =>
      rename_i s rest
      have hl : rest.length = ps.length := hr.length_eq.symm
      have e1 : stepsVal ρ (s :: rest) j =
          stepHalf ρ s (j / 2 ^ rest.length % 2 == 1) * stepsVal ρ rest (j % 2 ^ rest.length) := rfl
      rw [e1, pairsValHigh, stepsVal_eq ps rest hr, hl,
        fStep_val ρ p s hs (j / 2 ^ ps.length % 2 == 1)]

/-- If Tensor.dotInF returns a value, the value reads as the sum over the indices j of entry j of
the tensor times entry j of the written-out vector. Entries that the vector lacks count as 0. -/
theorem Tensor.dotInF_val (v : Tensor) (a : Array E) (d : E) (h : v.dotInF a = some d) :
    ρ.val d = ∑ j ∈ Finset.range (2 ^ v.vars), ρ.val (v.entry j) * ρ.val (a.getD j zeroE) := by
  unfold Tensor.dotInF at h
  split at h
  · cases h
  · rename_i he
    simp only [Bool.not_eq_true', Bool.not_eq_false] at he
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨steps, hm, rfl⟩ := h
    have f2 := (mapM_fStep v.pairs steps hm)
    have fr : List.Forall₂ (fun p s => fStep p = some s) v.pairs.reverse steps.reverse :=
      List.rel_reverse f2
    have hl : steps.reverse.length = v.vars := by
      rw [List.length_reverse, ← f2.length_eq]
      rfl
    have hw : weightOk steps.reverse (2 ^ (v.vars - 1)) := by
      cases hs : steps.reverse with
      | nil => trivial
      | cons s ps =>
        show 2 ^ (v.vars - 1) = 2 ^ ps.length
        rw [hs, List.length_cons] at hl
        rw [← hl, Nat.add_sub_cancel]
    rw [ρ.mul, dotSteps_coords, dotStepsE_val ρ a _ _ _ hw, hl, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [stepsVal_eq ρ _ _ fr, pairsValHigh_eq, List.reverse_reverse, Tensor.entry_val,
      Tensor.denseVal, if_pos he, Nat.zero_add]
    ring

/-! ## A form written out, and its inner product -/

/-- Adding tensors of n variables to a vector keeps its length; entry J, for J below 2^n and within
the vector, then reads as the old entry plus the sum of the tensors' entries J. -/
theorem foldl_addTo (n : Nat) : ∀ (l : List Tensor) (out : Array E) (J : Nat),
    (∀ v ∈ l, v.vars = n) → J < 2 ^ n → J < out.size →
    (l.foldl (fun o v => v.addTo o) out).size = out.size ∧
    ρ.val ((l.foldl (fun o v => v.addTo o) out).getD J zeroE) =
      ρ.val (out.getD J zeroE) + (l.map fun v => ρ.val (v.entry J)).sum
  | [], out, J, _, _, _ => by simp
  | v :: l, out, J, hv, hJ, hs => by
    have s1 := Tensor.addTo_size v out
    have e1 := Tensor.addTo_val ρ v out J
    obtain ⟨s2, e2⟩ := foldl_addTo n l (v.addTo out) J (fun u hu => hv u (by simp [hu])) hJ
      (by rw [s1]; exact hs)
    rw [List.foldl_cons]
    refine ⟨s2.trans s1, ?_⟩
    rw [e2, e1, if_pos ⟨by rw [hv v (by simp)]; exact hJ, hs⟩, List.map_cons, List.sum_cons]
    ring

/-- Adding single entries to a vector keeps its length; entry J within the vector then reads as the
old entry plus the sum of the coefficients whose index is J. -/
theorem foldl_modify : ∀ (l : List (Nat × E)) (out : Array E) (J : Nat), J < out.size →
    (l.foldl (fun o e => o.modify e.1 fun y => addE y e.2) out).size = out.size ∧
    ρ.val ((l.foldl (fun o e => o.modify e.1 fun y => addE y e.2) out).getD J zeroE) =
      ρ.val (out.getD J zeroE) + (l.map fun e => if e.1 = J then ρ.val e.2 else 0).sum
  | [], out, J, _ => by simp
  | e :: l, out, J, hs => by
    have s1 : (out.modify e.1 fun y => addE y e.2).size = out.size := by simp
    obtain ⟨s2, e2⟩ := foldl_modify l (out.modify e.1 fun y => addE y e.2) J (by rw [s1]; exact hs)
    rw [List.foldl_cons]
    refine ⟨s2.trans s1, ?_⟩
    rw [e2, getD_modify, List.map_cons, List.sum_cons]
    by_cases h : e.1 = J
    · rw [if_pos ⟨h, hs⟩, if_pos h, ρ.add]
      ring
    · rw [if_neg (fun x => h x.1), if_neg h]
      ring

/-- A form all of whose tensors have n variables, written out: 2^n entries, and entry J, for J below
2^n, reads as the form's entry J. -/
theorem Form.writeOut_val (f : Form) (n : Nat)
    (hv : ∀ v ∈ f.tensors, v.vars = n) (J : Nat) (hJ : J < 2 ^ n) :
    (f.writeOut n).size = 2 ^ n ∧ ρ.val ((f.writeOut n).getD J zeroE) = ρ.val (f.entry J) := by
  unfold Form.writeOut Form.addTo
  have s0 : (Array.replicate (2 ^ n) zeroE).size = 2 ^ n := by simp
  obtain ⟨s1, e1⟩ := foldl_addTo ρ n f.tensors (Array.replicate (2 ^ n) zeroE) J hv hJ
    (by rw [s0]; exact hJ)
  obtain ⟨s2, e2⟩ := foldl_modify ρ f.entries _ J (by rw [s1, s0]; exact hJ)
  refine ⟨by rw [s2, s1, s0], ?_⟩
  rw [e2, e1, Form.entry_val]
  simp [Array.getD, hJ, ρ.zero]

/-- A loop that adds up products reads as the sum of the products. -/
theorem fold_madd (w a : Array E) : ∀ m : Nat,
    ρ.val (Nat.fold m (fun j _ r => maddE r (w.getD j zeroE) (a.getD j zeroE)) zeroE) =
      ∑ j ∈ Finset.range m, ρ.val (w.getD j zeroE) * ρ.val (a.getD j zeroE)
  | 0 => by simp [ρ.zero]
  | m + 1 => by
    rw [Nat.fold_succ, maddE_val, fold_madd w a m, Finset.sum_range_succ]

/-- The plain inner product of a form with a written-out vector reads as the sum over the indices j
of the form's entry j times the vector's entry j. Entries that the vector lacks count as 0. Every
tensor of the form must have n variables. -/
theorem Form.dotPlain_val (f : Form) (n : Nat)
    (hv : ∀ v ∈ f.tensors, v.vars = n) (a : Array E) :
    ρ.val (f.dotPlain n a) =
      ∑ j ∈ Finset.range (2 ^ n), ρ.val (f.entry j) * ρ.val (a.getD j zeroE) := by
  unfold Form.dotPlain
  dsimp only
  rw [fold_madd, (Form.writeOut_val ρ f n hv 0 (Nat.two_pow_pos n)).1]
  rw [Finset.sum_subset (Finset.range_subset_range.2 (Nat.min_le_left (2 ^ n) a.size))]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [(Form.writeOut_val ρ f n hv j (Finset.mem_range.1 hj)).2]
  · intro j hj hn
    have h1 := Finset.mem_range.1 hj
    have h2 : ¬ j < min (2 ^ n) a.size := fun x => hn (Finset.mem_range.2 x)
    have h3 : ¬ j < a.size := by omega
    simp [Array.getD, h3, ρ.zero]

/-- The sum over the indices j of (the sum of the tensors' entries j) times the vector's entry j. -/
def tensorsDot (n : Nat) (a : Array E) (l : List Tensor) : K :=
  ∑ j ∈ Finset.range (2 ^ n), (l.map fun v => ρ.val (v.entry j)).sum * ρ.val (a.getD j zeroE)

/-- One tensor more adds its own inner product. -/
theorem tensorsDot_cons (n : Nat) (a : Array E) (v : Tensor) (l : List Tensor) :
    tensorsDot ρ n a (v :: l) =
      ∑ j ∈ Finset.range (2 ^ n), ρ.val (v.entry j) * ρ.val (a.getD j zeroE) +
        tensorsDot ρ n a l := by
  unfold tensorsDot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [List.map_cons, List.sum_cons]
  ring

/-- One step of the loop of Form.dot. -/
def dotStep (n : Nat) (a : Array E) (s : E × List Tensor) (v : Tensor) : E × List Tensor :=
  if isZeroE v.scalar then s
  else if a.size ≤ 2 ^ n && v.vars == n then
    match v.dotInF a with
    | some d => (addE s.1 d, s.2)
    | none => (s.1, v :: s.2)
  else (s.1, v :: s.2)

/-- Form.dot, with its loop's step under a name. -/
theorem Form.dot_eq (f : Form) (n : Nat) (a : Array E) :
    f.dot n a = addE (f.tensors.foldl (dotStep n a) (zeroE, [])).1
      (Form.dotPlain { tensors := (f.tensors.foldl (dotStep n a) (zeroE, [])).2,
                       entries := f.entries } n a) := rfl

/-- The loop of Form.dot: what it has added up and what it has put aside make, together, the inner
product of the tensors that it has seen. -/
theorem dot_fold (n : Nat) (a : Array E) : ∀ (l : List Tensor) (s : E × List Tensor),
    (∀ v ∈ l, v.vars = n) → (∀ v ∈ s.2, v.vars = n) →
    (∀ v ∈ (l.foldl (dotStep n a) s).2, v.vars = n) ∧
    ρ.val (l.foldl (dotStep n a) s).1 +
      tensorsDot ρ n a (l.foldl (dotStep n a) s).2 =
      ρ.val s.1 + tensorsDot ρ n a s.2 + tensorsDot ρ n a l
  | [], s, _, hs => by
    simp only [List.foldl_nil]
    exact ⟨hs, by simp [tensorsDot]⟩
  | v :: l, s, hl, hs => by
    rw [List.foldl_cons]
    have hvn := hl v (by simp)
    have hl' : ∀ u ∈ l, u.vars = n := fun u hu => hl u (by simp [hu])
    have push := dot_fold n a l (s.1, v :: s.2) hl' (by
      intro u hu
      rcases List.mem_cons.1 hu with rfl | hu
      · exact hvn
      · exact hs u hu)
    by_cases z : isZeroE v.scalar = true
    · have h1 : dotStep n a s v = s := by
        unfold dotStep
        simp only [z, if_true]
      rw [h1]
      obtain ⟨p, e⟩ := dot_fold n a l s hl' hs
      refine ⟨p, ?_⟩
      rw [e, tensorsDot_cons]
      have : ∑ j ∈ Finset.range (2 ^ n), ρ.val (v.entry j) * ρ.val (a.getD j zeroE) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        rw [Tensor.entry_val, val_of_isZeroE ρ _ z]
        ring
      rw [this]
      ring
    · by_cases c : (decide (a.size ≤ 2 ^ n) && v.vars == n) = true
      · cases hd : v.dotInF a with
        | some d =>
          have h1 : dotStep n a s v = (addE s.1 d, s.2) := by
            unfold dotStep
            simp only [z, c, hd, if_true, Bool.false_eq_true, if_false]
          rw [h1]
          obtain ⟨p, e⟩ := dot_fold n a l (addE s.1 d, s.2) hl' hs
          refine ⟨p, ?_⟩
          rw [e, tensorsDot_cons, ρ.add, Tensor.dotInF_val ρ v a d hd, hvn]
          ring
        | none =>
          have h1 : dotStep n a s v = (s.1, v :: s.2) := by
            unfold dotStep
            simp only [z, c, hd, if_true, Bool.false_eq_true, if_false]
          rw [h1]
          refine ⟨push.1, ?_⟩
          rw [push.2, tensorsDot_cons, tensorsDot_cons]
          ring
      · have h1 : dotStep n a s v = (s.1, v :: s.2) := by
          unfold dotStep
          simp only [z, c, Bool.false_eq_true, if_false]
        rw [h1]
        refine ⟨push.1, ?_⟩
        rw [push.2, tensorsDot_cons, tensorsDot_cons]
        ring

/-- Every tensor of a form that passes Form.fits n has n variables. -/
theorem Form.vars_of_fits (f : Form) (n : Nat) (h : f.fits n = true) :
    ∀ v ∈ f.tensors, v.vars = n := by
  unfold Form.fits at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact fun v hv => (h.1 v hv).1

/-- The inner product of a form with a written-out vector reads as the sum over the indices j below
2^n of the form's entry j times the vector's entry j. Entries that the vector lacks count as 0.
Every tensor of the form must have n variables (Form.fits tests this). -/
theorem Form.dot_val (f : Form) (n : Nat) (hv : ∀ v ∈ f.tensors, v.vars = n) (a : Array E) :
    ρ.val (f.dot n a) =
      ∑ j ∈ Finset.range (2 ^ n), ρ.val (f.entry j) * ρ.val (a.getD j zeroE) := by
  rw [Form.dot_eq]
  obtain ⟨p, e⟩ := dot_fold ρ n a f.tensors (zeroE, []) hv (by simp)
  rw [ρ.add, Form.dotPlain_val ρ _ n p a]
  have split : ∀ (l : List Tensor),
      ∑ j ∈ Finset.range (2 ^ n),
        ρ.val (({ tensors := l, entries := f.entries } : Form).entry j) *
          ρ.val (a.getD j zeroE) =
      tensorsDot ρ n a l + ∑ j ∈ Finset.range (2 ^ n),
        (f.entries.map fun e => if e.1 = j then ρ.val e.2 else 0).sum *
          ρ.val (a.getD j zeroE) := by
    intro l
    unfold tensorsDot
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [Form.entry_val]
    ring
  have whole : ∑ j ∈ Finset.range (2 ^ n), ρ.val (f.entry j) * ρ.val (a.getD j zeroE) =
      tensorsDot ρ n a f.tensors + ∑ j ∈ Finset.range (2 ^ n),
        (f.entries.map fun e => if e.1 = j then ρ.val e.2 else 0).sum *
          ρ.val (a.getD j zeroE) := split f.tensors
  have z1 : ρ.val zeroE = 0 := ρ.zero
  have z2 : tensorsDot ρ n a [] = 0 := by simp [tensorsDot]
  dsimp only at e
  rw [split, whole]
  linear_combination e + z1 + z2

end OnBytes

#print axioms OnBytes.Tensor.dotInF_val
#print axioms OnBytes.Form.dot_val
