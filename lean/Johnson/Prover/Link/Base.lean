-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/Base.lean: the last step of a proximity test (the base case,
Johnson/Desc/Prox/BaseCase.lean) says yes to an honest prover's two messages: the values' half.
General in the two codes, the claim, the drawn element and the drawn positions. No stage, no chain,
no strategy, no record of an honest side.

The letters, as in Johnson/Desc/Prox/BaseChecks.lean. The last message holds a word under the main
code C, of the message m0 with the tail r0, and a word under the mask code Z, of m1 with r1. The
masking message holds the words of h0 with s0 and of h1 with s1. c, d, tau: the claim that is left.
All eight are functions ℕ → GE, read below the codes' lengths alone.

Main names (namespace `Johnson.Prover.Link`).
  `formG n c m`, `symG C x m r`   a vector of coefficients on a message; the code word's symbol at
      the position x: `symV` (OnBytes/Slice/SimBase.lean) with functions in the place of lists
  `symG_line`, `symG_congr`, `formG_line`   both are linear, and read their arguments below the
      lengths alone
  `baseChecks_of_field`   the claim is true at (m0, m1) · tauS reads as the claim's left side at
      (h0, h1) · the four shown lists have the codes' lengths and read as h + lam * m, entry by
      entry · each listed position has a column whose four symbols read as the four code words'
      symbols there: then `baseChecks` = true
  `wr n f`, `length_wr`, `lst_wr`, `okE_wr`   a function's first n values written as triples of
      words below the prime; read back they are the values
  `tauSW`, `baseColW`, `baseChecks_written`   the honest prover's element, four lists and columns,
      written; `baseChecks` at them = true, at every list of positions
  `words12`, `shownAll`, `baseDecide_written`   so `baseDecide` returns the claim, at two rounds and
      one group of columns that hold these

By: `baseOK_iff_parts`, `baseB1_iff`, `baseB2At_iff` (OnBytes/Slice/SimBase.lean: each of the
format's three functions returns true exactly if the field's equations hold), `baseChecks_eq`
(Johnson/Desc/K12/Law/BaseChecksIs.lean).

Limits. That the claim that is left is true at the last message is a premise. Nothing on the guards
of the part that calls `baseDecide` (`baseJ5`, Johnson/Desc/K12/JoinGuarded.lean), on `Block.step`'s
tests of form, on trees, paths or hashes. Nothing on how h0, s0, h1, s1 are chosen. Nothing on
soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.SimBase
import Johnson.Desc.K12.Law.BaseChecksIs
import Johnson.Desc.Prox.BaseCase

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes.Slice Cb
open Fmt.M1 (E Code point)
open VerifiableInference.Desc.Prox

/-! ## The form and the symbol, on functions -/

/-- A vector of coefficients on the first n entries of a message. -/
def formG (n : ℕ) (c : Array E) (m : ℕ → GE) : GE := ∑ i ∈ Finset.range n, vec c i * m i

/-- The code word's symbol at the position x: the value, at x's point, of the polynomial whose
coefficients are the r entries of the tail and then the l entries of the message. At C.r = 0 the
first sum is empty: no entry of the tail is read; nothing refuses. -/
def symG (C : Code) (x : ℕ) (m r : ℕ → GE) : GE :=
  (∑ q ∈ Finset.range C.r, algebraMap GF GE (toF (point C.a x) ^ q) * r q) +
    ∑ j ∈ Finset.range C.l, algebraMap GF GE (toF (point C.a x) ^ (C.r + j)) * m j

theorem symV_eq (C : Code) (x : ℕ) (M R : List E) : symV C x M R = symG C x (lst M) (lst R) := rfl

theorem formG_congr (n : ℕ) (c : Array E) (m m' : ℕ → GE) (h : ∀ i, i < n → m i = m' i) :
    formG n c m = formG n c m' :=
  Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]

theorem formG_line (n : ℕ) (c : Array E) (h m : ℕ → GE) (μ : GE) :
    formG n c (fun i => h i + μ * m i) = formG n c h + μ * formG n c m := by
  unfold formG
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem symG_congr (C : Code) (x : ℕ) (m m' r r' : ℕ → GE) (hm : ∀ j, j < C.l → m j = m' j)
    (hr : ∀ q, q < C.r → r q = r' q) : symG C x m r = symG C x m' r' := by
  unfold symG
  exact congrArg₂ (· + ·)
    (Finset.sum_congr rfl fun q hq => by rw [hr q (Finset.mem_range.1 hq)])
    (Finset.sum_congr rfl fun j hj => by rw [hm j (Finset.mem_range.1 hj)])

theorem symG_line (C : Code) (x : ℕ) (h m s r : ℕ → GE) (μ : GE) :
    symG C x (fun j => h j + μ * m j) (fun q => s q + μ * r q) =
      symG C x h s + μ * symG C x m r := by
  unfold symG
  rw [mul_add, Finset.mul_sum, Finset.mul_sum,
    show (∑ q ∈ Finset.range C.r, algebraMap GF GE (toF (point C.a x) ^ q) * (s q + μ * r q)) =
      (∑ q ∈ Finset.range C.r, algebraMap GF GE (toF (point C.a x) ^ q) * s q) +
        ∑ q ∈ Finset.range C.r, μ * (algebraMap GF GE (toF (point C.a x) ^ q) * r q) by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun q _ => by ring,
    show (∑ j ∈ Finset.range C.l,
        algebraMap GF GE (toF (point C.a x) ^ (C.r + j)) * (h j + μ * m j)) =
      (∑ j ∈ Finset.range C.l, algebraMap GF GE (toF (point C.a x) ^ (C.r + j)) * h j) +
        ∑ j ∈ Finset.range C.l, μ * (algebraMap GF GE (toF (point C.a x) ^ (C.r + j)) * m j) by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring]
  ring

/-! ## The checks, from equations in the field -/

/-- **The base case's checks say yes** where the claim is true at the last message and what is sent
and opened reads, in the field, as an honest prover's. -/
theorem baseChecks_of_field (C Z : Code) (c d : Array E) (tau tauS lam : E)
    (M0 M1 R0 R1 : List E) (xs : List ℕ) (col : ℕ → Option (E × E × E × E))
    (m0 r0 m1 r1 h0 s0 h1 s1 : ℕ → GE)
    (hlen : M0.length = C.l ∧ M1.length = Z.l ∧ R0.length = C.r ∧ R1.length = Z.r)
    (hcl : formG C.l c m0 + formG Z.l d m1 = toE tau)
    (hS : toE tauS = formG C.l c h0 + formG Z.l d h1)
    (hM0 : ∀ j, j < C.l → lst M0 j = h0 j + toE lam * m0 j)
    (hM1 : ∀ j, j < Z.l → lst M1 j = h1 j + toE lam * m1 j)
    (hR0 : ∀ q, q < C.r → lst R0 q = s0 q + toE lam * r0 q)
    (hR1 : ∀ q, q < Z.r → lst R1 q = s1 q + toE lam * r1 q)
    (hcol : ∀ x ∈ xs, ∃ o, col x = some o ∧ toE o.1 = symG C x m0 r0 ∧
      toE o.2.1 = symG C x h0 s0 ∧ toE o.2.2.1 = symG Z (x % 2 ^ Z.a) m1 r1 ∧
      toE o.2.2.2 = symG Z (x % 2 ^ Z.a) h1 s1) :
    baseChecks C Z c d tau tauS lam M0 M1 R0 R1 xs col = true := by
  rw [baseChecks_eq, baseOK_iff_parts]
  refine ⟨hlen, (baseB1_iff c d tau tauS lam M0 M1 C.l Z.l (le_of_eq hlen.1)
    (le_of_eq hlen.2.1)).2 ?_, fun x hx => ?_⟩
  · show formG C.l c (lst M0) + formG Z.l d (lst M1) = _
    rw [formG_congr C.l c _ _ hM0, formG_congr Z.l d _ _ hM1, formG_line, formG_line, hS, ← hcl]
    ring
  · obtain ⟨o, ho, e1, e2, e3, e4⟩ := hcol x hx
    refine ⟨o, ho, (baseB2At_iff C Z lam M0 M1 R0 R1 x o).2 ⟨?_, ?_⟩⟩
    · rw [symV_eq, symG_congr C x _ _ _ _ hM0 hR0, symG_line, e1, e2]
    · rw [symV_eq, symG_congr Z _ _ _ _ _ hM1 hR1, symG_line, e3, e4]

/-! ## The writing, and the reading back -/

/-- A function's first n values, written as triples of words below the prime. -/
def wr (n : ℕ) (f : ℕ → GE) : List E := (List.range n).map fun j => ofE (f j)

theorem length_wr (n : ℕ) (f : ℕ → GE) : (wr n f).length = n := by
  unfold wr
  rw [List.length_map, List.length_range]

/-- Read back they are the values. -/
theorem lst_wr (n : ℕ) (f : ℕ → GE) (j : ℕ) (h : j < n) : lst (wr n f) j = f j := by
  unfold lst wr
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact h),
    List.getElem_map, List.getElem_range, toE_ofE]

theorem okE_ofE (x : GE) : Fmt.Fld.two.okE (ofE x) = true := by
  simp only [Fmt.Fld.okE, ofE, ok_ofF, Bool.and_self]

/-- Every written triple has words below the prime. -/
theorem okE_wr (n : ℕ) (f : ℕ → GE) : ∀ e ∈ wr n f, Fmt.Fld.two.okE e = true := by
  intro e he
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 he
  exact okE_ofE _

/-- The element of the first round: the claim's left side at the masking message. -/
def tauSW (C Z : Code) (c d : Array E) (h0 h1 : ℕ → GE) : E :=
  ofE (formG C.l c h0 + formG Z.l d h1)

/-- A column's four symbols at the position x: the last message's main symbol, the masking
message's, the last message's mask symbol, the masking message's. -/
def baseColW (C Z : Code) (m0 r0 m1 r1 h0 s0 h1 s1 : ℕ → GE) (x : ℕ) : E × E × E × E :=
  (ofE (symG C x m0 r0), ofE (symG C x h0 s0), ofE (symG Z (x % 2 ^ Z.a) m1 r1),
    ofE (symG Z (x % 2 ^ Z.a) h1 s1))

/-- **The checks say yes to what an honest prover writes**, at every drawn element and every list
of positions. -/
theorem baseChecks_written (C Z : Code) (c d : Array E) (tau lam : E) (xs : List ℕ)
    (m0 r0 m1 r1 h0 s0 h1 s1 : ℕ → GE) (hcl : formG C.l c m0 + formG Z.l d m1 = toE tau) :
    baseChecks C Z c d tau (tauSW C Z c d h0 h1) lam
      (wr C.l fun j => h0 j + toE lam * m0 j) (wr Z.l fun j => h1 j + toE lam * m1 j)
      (wr C.r fun q => s0 q + toE lam * r0 q) (wr Z.r fun q => s1 q + toE lam * r1 q) xs
      (fun x => some (baseColW C Z m0 r0 m1 r1 h0 s0 h1 s1 x)) = true :=
  baseChecks_of_field C Z c d tau _ lam _ _ _ _ xs _ m0 r0 m1 r1 h0 s0 h1 s1
    ⟨length_wr _ _, length_wr _ _, length_wr _ _, length_wr _ _⟩ hcl (toE_ofE _)
    (fun j hj => lst_wr _ _ j hj) (fun j hj => lst_wr _ _ j hj) (fun q hq => lst_wr _ _ q hq)
    (fun q hq => lst_wr _ _ q hq)
    fun _ _ => ⟨_, rfl, toE_ofE _, toE_ofE _, toE_ofE _, toE_ofE _⟩

/-! ## The decision on two rounds and one group of columns -/

/-- A column's twelve words. -/
def words12 (o : E × E × E × E) : List UInt64 :=
  [o.1.1, o.1.2.1, o.1.2.2, o.2.1.1, o.2.1.2.1, o.2.1.2.2, o.2.2.1.1, o.2.2.1.2.1, o.2.2.1.2.2,
    o.2.2.2.1, o.2.2.2.2.1, o.2.2.2.2.2]

theorem four_words12 (o : E × E × E × E) : four (words12 o) = some o := rfl

theorem elems_map : ∀ l : List E, elems (l.map Fmt.ItemValue.e) = some l
  | [] => rfl
  | x :: l => by
    show (elems (l.map Fmt.ItemValue.e)).map (x :: ·) = _
    rw [elems_map l]
    rfl

/-- Four lists in a row, cut again at their lengths. -/
theorem cut4 {α : Type} (A B G D : List α) (a b g : ℕ) (ha : A.length = a) (hb : B.length = b)
    (hg : G.length = g) :
    (A ++ (B ++ (G ++ D))).take a = A ∧ ((A ++ (B ++ (G ++ D))).drop a).take b = B ∧
      ((A ++ (B ++ (G ++ D))).drop (a + b)).take g = G ∧
      (A ++ (B ++ (G ++ D))).drop (a + b + g) = D := by
  have e1 : (A ++ (B ++ (G ++ D))).drop a = B ++ (G ++ D) := List.drop_left' ha
  have e2 : (A ++ (B ++ (G ++ D))).drop (a + b) = G ++ D := by
    rw [← List.append_assoc]
    exact List.drop_left' (by rw [List.length_append, ha, hb])
  have e3 : (A ++ (B ++ (G ++ D))).drop (a + b + g) = D := by
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.drop_left' (by rw [List.length_append, List.length_append, ha, hb, hg])
  exact ⟨List.take_left' ha, by rw [e1]; exact List.take_left' hb,
    by rw [e2]; exact List.take_left' hg, e3⟩

/-- What the second round shows: the two messages, then the two tails, of h + lam * m. -/
def shownAll (C Z : Code) (lam : E) (m0 r0 m1 r1 h0 s0 h1 s1 : ℕ → GE) : List E :=
  (wr C.l fun j => h0 j + toE lam * m0 j) ++ ((wr Z.l fun j => h1 j + toE lam * m1 j) ++
    ((wr C.r fun q => s0 q + toE lam * r0 q) ++ wr Z.r fun q => s1 q + toE lam * r1 q))

/-- **The base case's decision returns the claim**, at two rounds and one group of columns that
hold what an honest prover writes. -/
theorem baseDecide_written (P : BasePar) (s : BaseClaim) (rL rB : Fmt.RoundView)
    (g : List (ℕ × List UInt64)) (lam : E) (m0 r0 m1 r1 h0 s0 h1 s1 : ℕ → GE)
    (hc : s.c.size = P.C.l) (hd : s.d.size = P.Z.l)
    (hcl : formG P.C.l s.c m0 + formG P.Z.l s.d m1 = toE s.tau)
    (hL : rL.vals = [Fmt.ItemValue.e (tauSW P.C P.Z s.c s.d h0 h1)]) (hlam : rL.drawn.elems = [lam])
    (hB : rB.vals = (shownAll P.C P.Z lam m0 r0 m1 r1 h0 s0 h1 s1).map Fmt.ItemValue.e)
    (hg : ∀ x ∈ rB.drawn.poss, ∃ y, g.find? (·.1 == x) = some y ∧
      y.2 = words12 (baseColW P.C P.Z m0 r0 m1 r1 h0 s0 h1 s1 x)) :
    baseDecide P s [rL, rB] [g] = .ok s := by
  obtain ⟨t1, t2, t3, t4⟩ := cut4 (wr P.C.l fun j => h0 j + toE lam * m0 j)
    (wr P.Z.l fun j => h1 j + toE lam * m1 j) (wr P.C.r fun q => s0 q + toE lam * r0 q)
    (wr P.Z.r fun q => s1 q + toE lam * r1 q) P.C.l P.Z.l P.C.r (length_wr _ _) (length_wr _ _)
    (length_wr _ _)
  have hk : baseChecks P.C P.Z s.c s.d s.tau (tauSW P.C P.Z s.c s.d h0 h1) lam
      ((shownAll P.C P.Z lam m0 r0 m1 r1 h0 s0 h1 s1).take P.C.l)
      (((shownAll P.C P.Z lam m0 r0 m1 r1 h0 s0 h1 s1).drop P.C.l).take P.Z.l)
      (((shownAll P.C P.Z lam m0 r0 m1 r1 h0 s0 h1 s1).drop (P.C.l + P.Z.l)).take P.C.r)
      ((shownAll P.C P.Z lam m0 r0 m1 r1 h0 s0 h1 s1).drop (P.C.l + P.Z.l + P.C.r))
      rB.drawn.poss (fun x => (g.find? (·.1 == x)).bind fun y => four y.2) = true := by
    unfold shownAll
    rw [t1, t2, t3, t4]
    exact baseChecks_of_field P.C P.Z s.c s.d s.tau _ lam _ _ _ _ _ _ m0 r0 m1 r1 h0 s0 h1 s1
      ⟨length_wr _ _, length_wr _ _, length_wr _ _, length_wr _ _⟩ hcl (toE_ofE _)
      (fun j hj => lst_wr _ _ j hj) (fun j hj => lst_wr _ _ j hj) (fun q hq => lst_wr _ _ q hq)
      (fun q hq => lst_wr _ _ q hq) fun x hx => by
        obtain ⟨y, hy, e⟩ := hg x hx
        refine ⟨baseColW P.C P.Z m0 r0 m1 r1 h0 s0 h1 s1 x, ?_, toE_ofE _, toE_ofE _, toE_ofE _,
          toE_ofE _⟩
        rw [hy]
        show four y.2 = _
        rw [e, four_words12]
  unfold baseDecide
  simp only [hL, hlam, hB, elems_map, hc, hd, beq_self_eq_true, Bool.and_self, if_true, hk]

end Johnson.Prover.Link
