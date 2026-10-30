-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/HalveLaw.lean: `halved` (Halve.lean) equals `FoldOwn.honest`
(Fmt/M1Fold.lean) at `Fld.two`, for all arguments, without hypothesis.

  `Spec.halved_eq`   the statement: `halved .two T g = FoldOwn.honest .two T [] g` for every trial T
                 and every list g of sampled elements. The tables may have any lengths, the words
                 need not be below the prime. (Beyond k elements `halved` calls `honest`.)
  `halved_eq`    its proof
  `halved_of_le`   up to k elements `halved` is `halvedFrom`, not the call of `honest`
  `halving_rounds`   so `Seams.halving = Seams.lib` (Run.lean), as structures
  `dRR`, `fold1R`, `foldR`   the inner product and the fold over the field, for the proof

How. Every operation of `Fld.two` reads its words modulo the prime and returns reduced words. So two
results of an addition are equal if they decode to the same field element (`toE`, `toE_inj`,
OnBytes/Slice/Field.lean). Over the field: folding a table at 0 keeps the even entries, at 1 the odd
ones (`dRR_split`). So the inner product of the two tables folded at a vertex, summed over all
vertices of the cube of the later variables, is the inner product of the tables (`cube_sum`). The
hiding polynomial's and the mask tables' shares are the same words in both definitions.

Limits. At `Fld.one` `Seams.halving` calls `FoldOwn.honest` itself. Two definitions give the same
words. Nothing follows on what a verifier decides.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Halve
import OnBytes.Slice.Field
import Fmt.M1CsEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt (Fld)
open Fmt.M1 (E dot dotL fold1 fold1L fold1A foldLow)
open Fmt.M1.CsEq (okE_addE)
open Fmt.M1.FoldOwn (Trial cube coeffs honest roundAt sumPoly)
open OnBytes.Slice (toE toE_addE toE_subE toE_mulE toE_zeroE toE_oneE toE_inj)

/-- `halved` equals `FoldOwn.honest` at `Fld.two`. -/
def Spec.halved_eq : Prop :=
  ∀ (T : Trial) (g : List E), halved .two T g = honest .two T [] g

/-! ## 1 Over the field -/

/-- The inner product of two lists, up to the length of the shorter. -/
def dRR : List Cb.Gl.E → List Cb.Gl.E → Cb.Gl.E
  | a :: u, b :: w => a * b + dRR u w
  | _, _ => 0

theorem dRR_nil (u : List Cb.Gl.E) : dRR u [] = 0 := by cases u <;> rfl

/-- One variable folded at x. -/
def fold1R (x : Cb.Gl.E) : List Cb.Gl.E → List Cb.Gl.E
  | a :: b :: T => (a + x * (b - a)) :: fold1R x T
  | [a] => [a + x * (0 - a)]
  | [] => []

/-- Variables folded one after the other. -/
def foldR (g T : List Cb.Gl.E) : List Cb.Gl.E := g.foldl (fun T x => fold1R x T) T

theorem mulEF_two (a b : E) : Fld.two.mulEF a b = Fld.two.mulE a b := Fmt.mulEF_eq .two a b

theorem val_dotL : ∀ (u w : List E) (acc : E),
    toE (dotL .two u w acc) = toE acc + dRR (u.map toE) (w.map toE)
  | [], _, acc => by simp [dotL, dRR]
  | _ :: _, [], acc => by simp [dotL, dRR]
  | a :: u, b :: w, acc => by
    rw [dotL, val_dotL u w, toE_addE, Fmt.mulEF_eq, toE_mulE]
    simp only [List.map_cons, dRR]
    ring

theorem val_fold1A (g : E) : ∀ (T acc : List E),
    (fold1A .two g T acc).map toE = (acc.map toE).reverse ++ fold1R (toE g) (T.map toE)
  | a :: b :: T, acc => by
    rw [fold1A, val_fold1A g T]
    simp [fold1R, toE_addE, mulEF_two, toE_mulE, toE_subE]
  | [a], acc => by
    simp [fold1A, fold1R, toE_addE, mulEF_two, toE_mulE, toE_subE, toE_zeroE]
  | [], acc => by simp [fold1A, fold1R]

theorem val_fold1L (g : E) (T : List E) :
    (fold1L .two g T).map toE = fold1R (toE g) (T.map toE) := by
  simp [fold1L, val_fold1A]

theorem val_foldl : ∀ (g T : List E),
    (g.foldl (fun T x => fold1L .two x T) T).map toE = foldR (g.map toE) (T.map toE)
  | [], _ => rfl
  | x :: g, T => by
    rw [List.foldl_cons, val_foldl g, val_fold1L]
    rfl

theorem val_foldLow (g : List E) (A : Array E) :
    (foldLow .two g A).toList.map toE = foldR (g.map toE) (A.toList.map toE) := by
  simp [foldLow, val_foldl]

theorem val_dot (A B : Array E) :
    toE (dot .two A B) = dRR (A.toList.map toE) (B.toList.map toE) := by
  simp [dot, val_dotL, toE_zeroE]

theorem val_fold1 (X : E) (A : Array E) :
    (fold1 .two X A).toList.map toE = fold1R (toE X) (A.toList.map toE) := by
  simp [fold1, val_fold1L]

/-! ## 2 The sum over the cube -/

/-- The inner products of the two lists folded at 0 and folded at 1 add up to the inner product of
the lists. (Folding at 0 keeps the even entries, at 1 the odd ones.) -/
theorem dRR_split : ∀ (C M : List Cb.Gl.E),
    dRR (fold1R 0 C) (fold1R 0 M) + dRR (fold1R 1 C) (fold1R 1 M) = dRR C M
  | a :: b :: C, x :: y :: M => by
    have h := dRR_split C M
    simp only [fold1R, dRR]
    rw [← h]
    ring
  | a :: b :: C, [x] => by
    simp only [fold1R, dRR, dRR_nil]
    ring
  | _ :: _ :: _, [] => by simp only [fold1R, dRR, dRR_nil, add_zero]
  | [a], x :: y :: M => by
    simp only [fold1R, dRR]
    ring
  | [a], [x] => by
    simp only [fold1R, dRR]
    ring
  | [_], [] => by simp only [fold1R, dRR, add_zero]
  | [], _ => by simp only [fold1R, dRR, add_zero]

theorem sum_add {α : Type} (F G : α → Cb.Gl.E) : ∀ L : List α,
    (L.map fun p => F p + G p).sum = (L.map F).sum + (L.map G).sum
  | [] => by simp
  | p :: L => by
    simp only [List.map_cons, List.sum_cons, sum_add F G L]
    ring

theorem sum_mul {α : Type} (e : Cb.Gl.E) (F : α → Cb.Gl.E) : ∀ L : List α,
    (L.map fun p => e * F p).sum = e * (L.map F).sum
  | [] => by simp
  | p :: L => by
    simp only [List.map_cons, List.sum_cons, sum_mul e F L]
    ring

theorem sum_pairs (F : List E → Cb.Gl.E) : ∀ L : List (List E),
    ((L.flatMap fun p => [Fld.zeroE :: p, Fld.oneE :: p]).map F).sum =
      (L.map fun p => F (Fld.zeroE :: p) + F (Fld.oneE :: p)).sum
  | [] => by simp
  | p :: L => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, sum_pairs F L]
    ring

/-- Summed over all vertices of the cube, the inner product of the two folded lists is the inner
product of the lists. -/
theorem cube_sum : ∀ (n : Nat) (C M : List Cb.Gl.E),
    ((cube n).map fun p => dRR (foldR (p.map toE) C) (foldR (p.map toE) M)).sum = dRR C M
  | 0, C, M => by simp [cube, foldR]
  | n + 1, C, M => by
    rw [cube, sum_pairs, sum_add]
    have a := cube_sum n (fold1R 0 C) (fold1R 0 M)
    have b := cube_sum n (fold1R 1 C) (fold1R 1 M)
    simp only [List.map_cons, foldR, List.foldl_cons, toE_zeroE, toE_oneE] at a b ⊢
    rw [a, b, dRR_split]

theorem cube_length : ∀ (n : Nat) (p : List E), p ∈ cube n → p.length = n
  | 0, p, h => by
    simp [cube] at h
    simp [h]
  | n + 1, p, h => by
    rw [cube, List.mem_flatMap] at h
    obtain ⟨q, hq, hp⟩ := h
    have := cube_length n q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [this]

/-! ## 3 A round -/

theorem val_foldl_add (F : List E → E) : ∀ (L : List (List E)) (s : E),
    toE (L.foldl (fun s p => Fld.two.addE s (F p)) s) = toE s + (L.map fun p => toE (F p)).sum
  | [], s => by simp
  | p :: L, s => by
    rw [List.foldl_cons, val_foldl_add F L, toE_addE]
    simp only [List.map_cons, List.sum_cons]
    ring

theorem ok_foldl_add (F : List E → E) : ∀ (L : List (List E)) (s : E),
    Fld.two.okE s = true → Fld.two.okE (L.foldl (fun s p => Fld.two.addE s (F p)) s) = true
  | [], _, h => h
  | p :: L, s, _ => by
    rw [List.foldl_cons]
    exact ok_foldl_add F L _ (okE_addE _ _ _)

/-- At a vertex of the later variables `sumPoly` decodes to `lightTerm` plus the main tables' share.
-/
theorem val_sumPoly (T : Trial) (before : List E) (X : E) (p : List E)
    (h : (before ++ X :: p).length = T.k) :
    toE (sumPoly .two T (before ++ X :: p)) =
      toE (lightTerm .two T (before ++ X :: p)) +
        toE T.eps *
          dRR (foldR (p.map toE) (fold1R (toE X) ((foldLow .two before T.G.c).toList.map toE)))
            (foldR (p.map toE) (fold1R (toE X) ((foldLow .two before T.m).toList.map toE))) := by
  have ht : (before ++ X :: p).take T.k = before ++ X :: p := List.take_of_length_le (by omega)
  have hf : ∀ A : Array E, (foldLow .two (before ++ X :: p) A).toList.map toE =
      foldR (p.map toE) (fold1R (toE X) ((foldLow .two before A).toList.map toE)) := by
    intro A
    rw [val_foldLow, val_foldLow]
    simp [foldR, List.foldl_append]
  unfold sumPoly lightTerm
  rw [ht]
  simp only [toE_addE, toE_mulE, val_dot, hf]
  ring

/-- A round polynomial's value at X is the same three words in both definitions. -/
theorem round_eq (T : Trial) (before : List E) (X : E) (h : before.length + 1 ≤ T.k) :
    Fld.two.addE (lightAt .two T before X)
        (Fld.two.mulE T.eps (dot .two (fold1 .two X (foldLow .two before T.G.c))
          (fold1 .two X (foldLow .two before T.m)))) =
      roundAt .two T before X := by
  refine toE_inj _ _ (okE_addE _ _ _) (ok_foldl_add _ _ _ (by decide)) ?_
  rw [toE_addE, toE_mulE, val_dot, val_fold1, val_fold1]
  unfold lightAt roundAt
  rw [val_foldl_add, val_foldl_add]
  have key : ∀ p ∈ cube (T.k - before.length - 1),
      toE (sumPoly .two T (before ++ X :: p)) =
        toE (lightTerm .two T (before ++ X :: p)) +
          toE T.eps *
            dRR (foldR (p.map toE) (fold1R (toE X) ((foldLow .two before T.G.c).toList.map toE)))
              (foldR (p.map toE)
                (fold1R (toE X) ((foldLow .two before T.m).toList.map toE))) := by
    intro p hp
    refine val_sumPoly T before X p ?_
    have := cube_length _ p hp
    simp only [List.length_append, List.length_cons]
    omega
  rw [List.map_congr_left key, sum_add, sum_mul, cube_sum]
  ring

/-! ## 4 All rounds -/

theorem foldLow_snoc (g : E) (before : List E) (A : Array E) :
    fold1 .two g (foldLow .two before A) = foldLow .two (before ++ [g]) A := by
  simp [fold1, foldLow, List.foldl_append]

theorem halvedFrom_eq (T : Trial) : ∀ (gs before : List E), before.length + gs.length ≤ T.k →
    halvedFrom .two T before (foldLow .two before T.G.c) (foldLow .two before T.m) gs =
      honest .two T before gs
  | [], _, _ => by simp [halvedFrom, honest]
  | g :: gs, before, h => by
    have h1 : before.length + 1 ≤ T.k := by
      simp only [List.length_cons] at h
      omega
    have h2 : (before ++ [g]).length + gs.length ≤ T.k := by
      simp only [List.length_cons, List.length_append, List.length_nil] at h ⊢
      omega
    simp only [halvedFrom, honest]
    simp only [round_eq T before _ h1]
    rw [foldLow_snoc, foldLow_snoc, halvedFrom_eq T gs (before ++ [g]) h2]

theorem halved_eq : Spec.halved_eq := by
  intro T g
  unfold halved
  split
  · rename_i h
    have e := halvedFrom_eq T g [] (by simpa using h)
    simpa [foldLow] using e
  · rfl

/-- With at most as many sampled elements as the fold has variables, `halved` is `halvedFrom`. -/
theorem halved_of_le (f : Fld) (T : Trial) (g : List E) (h : g.length ≤ T.k) :
    halved f T g = halvedFrom f T [] T.G.c T.m g := if_pos h

/-- `Seams.halving` and `Seams.lib` are equal in all five fields (their definitions differ in
`rounds` alone). -/
theorem halving_rounds : Seams.halving = Seams.lib := by
  unfold Seams.halving Seams.lib
  congr 1
  funext f T g
  cases f
  · rfl
  · exact halved_eq T g

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.dRR_nil
#print axioms ProofFile.Honest.K12.Light.mulEF_two
#print axioms ProofFile.Honest.K12.Light.val_dotL
#print axioms ProofFile.Honest.K12.Light.val_fold1A
#print axioms ProofFile.Honest.K12.Light.val_fold1L
#print axioms ProofFile.Honest.K12.Light.val_foldl
#print axioms ProofFile.Honest.K12.Light.val_foldLow
#print axioms ProofFile.Honest.K12.Light.val_dot
#print axioms ProofFile.Honest.K12.Light.val_fold1
#print axioms ProofFile.Honest.K12.Light.dRR_split
#print axioms ProofFile.Honest.K12.Light.sum_add
#print axioms ProofFile.Honest.K12.Light.sum_mul
#print axioms ProofFile.Honest.K12.Light.sum_pairs
#print axioms ProofFile.Honest.K12.Light.cube_sum
#print axioms ProofFile.Honest.K12.Light.cube_length
#print axioms ProofFile.Honest.K12.Light.val_foldl_add
#print axioms ProofFile.Honest.K12.Light.ok_foldl_add
#print axioms ProofFile.Honest.K12.Light.val_sumPoly
#print axioms ProofFile.Honest.K12.Light.round_eq
#print axioms ProofFile.Honest.K12.Light.foldLow_snoc
#print axioms ProofFile.Honest.K12.Light.halvedFrom_eq
#print axioms ProofFile.Honest.K12.Light.halved_eq
#print axioms ProofFile.Honest.K12.Light.halved_of_le
#print axioms ProofFile.Honest.K12.Light.halving_rounds
#print axioms ProofFile.Honest.K12.Light.Spec.halved_eq
#print axioms ProofFile.Honest.K12.Light.dRR
#print axioms ProofFile.Honest.K12.Light.fold1R
#print axioms ProofFile.Honest.K12.Light.foldR
