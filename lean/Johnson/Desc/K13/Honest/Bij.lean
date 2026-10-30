--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/Bij.lean: the masked sumcheck's honest scalars (plain weights, degree 2, no
value shown at the end; Johnson/Desc/K13/Honest/Moves.lean): FROM THE 2 n + 1 COEFFICIENTS OF THE
HIDING POLYNOMIAL TO THE 2 n + 1 SCALARS THAT ARE SENT IS A BIJECTION, whatever the summand, the
joining element and the challenges are. Over any commutative ring. Definitions with code; statements
with their proofs.

How. The map is triangular. A round's quadratic coefficient holds the hiding polynomial's quadratic
coefficient of that variable, plus a share of the summand. The last round's constant coefficient
holds the hiding polynomial's constant. An earlier round's constant coefficient holds the sum of the
hiding polynomial's part in the later variables. The scalar that is sent first holds the sum of the
whole. So the coefficients come back one variable at a time, the linear one last in each.

WHAT IS HELD FIXED, AND WHAT VARIES. Fixed, and arbitrary: the parameter q, which gives the
summand's round polynomials; the joining element eps; the challenges seen and gs. At kind K13 q is
made of the matrix, of the weights and column points of the rows on the pile, and of the first
sampled element, and of nothing else. What varies: the function v on 2 n + 1 numbers, the
coefficients. No state of a verifier and no statement stands in a theorem of this file.

WHOSE HALF THIS IS. In the protocol the coefficients are mask entries of an oracle message that was
sent earlier. These statements belong to the sub-protocol that SPENDS the entries. What the message
itself shows of them (its OOD answers; the columns that are opened) belongs to the sub-protocol that
SENDS it. The paragraph of that name in Johnson/Desc/K13/Honest/BijLaw.lean holds of this file too:
NO STATEMENT OF THIS FILE IS TO BE QUOTED WITHOUT THE SENDER's SENTENCE BESIDE IT.
Main names:
  `uBack eps q n m l seen gs`: the coefficients, by their numbers, from what was sent: m first, then
    the pairs l. 0 from the number 2 n + 1 on.
  `tailU_shift`, `sentL_shift`: the coefficients' numbers moved by 2.
  `view_uBack`: what is sent at these coefficients is m and l.
  `uBack_view`: from what is sent at u come u's first 2 n + 1 values.
  `flatL`, `flatV m l`: a scalar and pairs as a row of scalars; `tell_flat`, `flat_tell`: that and
    `tellL` (Johnson/Desc/K13/Honest/Tell.lean) undo each other.
  `viewL eps q n seen gs v`: what is sent at the coefficients v. `rowL`: the same in a row.
  `coefL`: the coefficients from such a row.
  `viewEquiv`: **the bijection** of the functions on 2 n + 1 numbers, for n at least 1.
  `viewL_eq_tell`: what is sent at v is the row `viewEquiv v`, cut into a scalar and pairs.
  `viewT_eq_tell`: the same where the summand is given by tables (`sent`).

What is not claimed. Nothing is said here of a distribution: Johnson/Desc/K13/Honest/BijLaw.lean.
The bijection cuts both ways: with q, eps and the challenges, the 2 n + 1 sent scalars fix all
2 n + 1 coefficients, and so every other value that is computed from the coefficients. That the
linear part of the map is one matrix at all lists of challenges is stated nowhere: `viewEquiv` is a
bijection at each fixed list. Nothing on what else a run shows of the coefficients. Nothing on
soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.SumLaw
import Johnson.Desc.K13.Honest.Tell
import Mathlib.Logic.Equiv.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest

variable {K : Type} [CommRing K]

/-! ## Back from what was sent -/

/-- **The coefficients of the hiding polynomial's part in n variables, from what was sent.** m: the
sum of that part. l: the rounds' pairs. seen: the challenges heard in front. gs: those to come. The
last argument is the coefficient's number, from 0. -/
def uBack (eps : K) (q : List K → K × K × K) :
    ℕ → K → List (K × K) → List K → List K → ℕ → K
  | 0, _, _, _, _, _ => 0
  | 1, _, l, seen, _, 0 => (l.headD (0, 0)).1 - eps * (q seen).1
  | 1, m, l, seen, _, 1 =>
    m - 2 * ((l.headD (0, 0)).1 - eps * (q seen).1) - ((l.headD (0, 0)).2 - eps * (q seen).2.2)
  | 1, _, l, seen, _, 2 => (l.headD (0, 0)).2 - eps * (q seen).2.2
  | 1, _, _, _, _, _ + 3 => 0
  | _ + 2, m, l, seen, _, 0 =>
    m - ((l.headD (0, 0)).2 - eps * (q seen).2.2) - 2 * ((l.headD (0, 0)).1 - eps * (q seen).1)
  | _ + 2, _, l, seen, _, 1 => (l.headD (0, 0)).2 - eps * (q seen).2.2
  | n + 2, _, l, seen, gs, j + 2 =>
    uBack eps q (n + 1) ((l.headD (0, 0)).1 - eps * (q seen).1) l.tail (seen ++ [gs.headD 0])
      gs.tail j

/-- From the number 2 n + 1 on it is 0. -/
theorem uBack_zero (eps : K) (q : List K → K × K × K) : ∀ (n : ℕ) (m : K) (l : List (K × K))
    (seen gs : List K) (j : ℕ), 2 * n + 1 ≤ j → uBack eps q n m l seen gs j = 0
  | 0, _, _, _, _, _, _ => rfl
  | 1, _, _, _, _, 0, h => by omega
  | 1, _, _, _, _, 1, h => by omega
  | 1, _, _, _, _, 2, h => by omega
  | 1, _, _, _, _, _ + 3, _ => rfl
  | _ + 2, _, _, _, _, 0, h => by omega
  | _ + 2, _, _, _, _, 1, h => by omega
  | n + 2, _, l, seen, gs, j + 2, h =>
    uBack_zero eps q (n + 1) _ l.tail (seen ++ [gs.headD 0]) gs.tail j (by omega)

/-! ## The coefficients' numbers moved by 2 -/

/-- The coefficients' numbers moved by 2, in the sum. -/
theorem tailU_shift (u : ℕ → K) : ∀ n i : ℕ, tailU u n (i + 2) = tailU (fun j => u (j + 2)) n i
  | 0, _ => rfl
  | 1, i => by
    show 2 * u (i + 2) + u (i + 2 + 1) + u (i + 2 + 2) =
      2 * u (i + 2) + u (i + 1 + 2) + u (i + 2 + 2)
    rw [Nat.add_right_comm i 2 1]
  | n + 2, i => by
    show u (i + 2) + u (i + 2 + 1) + 2 * tailU u (n + 1) (i + 2 + 2) =
      u (i + 2) + u (i + 1 + 2) + 2 * tailU (fun j => u (j + 2)) (n + 1) (i + 2)
    rw [Nat.add_right_comm i 2 1, tailU_shift u (n + 1) (i + 2)]

/-- The coefficients' numbers moved by 2, in what is sent. -/
theorem sentL_shift (u : ℕ → K) (eps : K) (q : List K → K × K × K) : ∀ (n i : ℕ)
    (seen gs : List K),
    sentL u eps q n (i + 2) seen gs = sentL (fun j => u (j + 2)) eps q n i seen gs
  | 0, _, _, _ => rfl
  | 1, _, _, _ => rfl
  | n + 2, i, seen, gs => by
    show (tailU u (n + 1) (i + 2 + 2) + eps * (q seen).1, u (i + 2 + 1) + eps * (q seen).2.2) ::
        sentL u eps q (n + 1) (i + 2 + 2) (seen ++ [gs.headD 0]) gs.tail =
      (tailU (fun j => u (j + 2)) (n + 1) (i + 2) + eps * (q seen).1,
          u (i + 1 + 2) + eps * (q seen).2.2) ::
        sentL (fun j => u (j + 2)) eps q (n + 1) (i + 2) (seen ++ [gs.headD 0]) gs.tail
    rw [Nat.add_right_comm i 2 1, tailU_shift u (n + 1) (i + 2),
      sentL_shift u eps q (n + 1) (i + 2) (seen ++ [gs.headD 0]) gs.tail]

/-- As many pairs are sent as there are variables. -/
theorem sentL_length (u : ℕ → K) (eps : K) (q : List K → K × K × K) : ∀ (n i : ℕ)
    (seen gs : List K), (sentL u eps q n i seen gs).length = n
  | 0, _, _, _ => rfl
  | 1, _, _, _ => rfl
  | n + 2, i, seen, gs =>
    congrArg (· + 1) (sentL_length u eps q (n + 1) (i + 2) (seen ++ [gs.headD 0]) gs.tail)

/-! ## The two maps undo each other -/

/-- **What is sent at the coefficients that come back is what they came back from.** -/
theorem view_uBack (eps : K) (q : List K → K × K × K) : ∀ (n : ℕ) (m : K) (l : List (K × K))
    (seen gs : List K), l.length = n → 1 ≤ n →
    tailU (uBack eps q n m l seen gs) n 0 = m ∧
      sentL (uBack eps q n m l seen gs) eps q n 0 seen gs = l
  | 1, m, [p], seen, gs, _, _ => by
    refine ⟨?_, ?_⟩
    · show 2 * (p.1 - eps * (q seen).1) +
          (m - 2 * (p.1 - eps * (q seen).1) - (p.2 - eps * (q seen).2.2)) +
          (p.2 - eps * (q seen).2.2) = m
      ring
    · show [(p.1 - eps * (q seen).1 + eps * (q seen).1,
          p.2 - eps * (q seen).2.2 + eps * (q seen).2.2)] = [p]
      rw [sub_add_cancel, sub_add_cancel]
  | n + 2, m, p :: l, seen, gs, hl, _ => by
    have ih := view_uBack eps q (n + 1) (p.1 - eps * (q seen).1) l (seen ++ [gs.headD 0]) gs.tail
      (by simp only [List.length_cons] at hl; omega) (by omega)
    have hs : (fun j => uBack eps q (n + 2) m (p :: l) seen gs (j + 2)) =
        uBack eps q (n + 1) (p.1 - eps * (q seen).1) l (seen ++ [gs.headD 0]) gs.tail := rfl
    refine ⟨?_, ?_⟩
    · show (m - (p.2 - eps * (q seen).2.2) - 2 * (p.1 - eps * (q seen).1)) +
          (p.2 - eps * (q seen).2.2) +
          2 * tailU (uBack eps q (n + 2) m (p :: l) seen gs) (n + 1) (0 + 2) = m
      rw [tailU_shift, hs, ih.1]
      ring
    · show (tailU (uBack eps q (n + 2) m (p :: l) seen gs) (n + 1) (0 + 2) + eps * (q seen).1,
          p.2 - eps * (q seen).2.2 + eps * (q seen).2.2) ::
          sentL (uBack eps q (n + 2) m (p :: l) seen gs) eps q (n + 1) (0 + 2)
            (seen ++ [gs.headD 0]) gs.tail = p :: l
      rw [tailU_shift, sentL_shift, hs, ih.1, ih.2, sub_add_cancel, sub_add_cancel]
  | 0, _, _, _, _, _, h => by omega
  | 1, _, [], _, _, hl, _ => by simp only [List.length_nil] at hl; omega
  | 1, _, _ :: _ :: _, _, _, hl, _ => by simp only [List.length_cons] at hl; omega
  | _ + 2, _, [], _, _, hl, _ => by simp only [List.length_nil] at hl; omega

/-- **From what is sent at u come back u's values**, at the 2 n + 1 numbers from i on. -/
theorem uBack_view (u : ℕ → K) (eps : K) (q : List K → K × K × K) : ∀ (n i : ℕ)
    (seen gs : List K) (j : ℕ), 1 ≤ n → j < 2 * n + 1 →
    uBack eps q n (tailU u n i) (sentL u eps q n i seen gs) seen gs j = u (i + j)
  | 1, i, seen, gs, 0, _, _ => by
    show u i + eps * (q seen).1 - eps * (q seen).1 = u i
    ring
  | 1, i, seen, gs, 1, _, _ => by
    show 2 * u i + u (i + 1) + u (i + 2) - 2 * (u i + eps * (q seen).1 - eps * (q seen).1) -
      (u (i + 2) + eps * (q seen).2.2 - eps * (q seen).2.2) = u (i + 1)
    ring
  | 1, i, seen, gs, 2, _, _ => by
    show u (i + 2) + eps * (q seen).2.2 - eps * (q seen).2.2 = u (i + 2)
    ring
  | n + 2, i, seen, gs, 0, _, _ => by
    show u i + u (i + 1) + 2 * tailU u (n + 1) (i + 2) -
        (u (i + 1) + eps * (q seen).2.2 - eps * (q seen).2.2) -
        2 * (tailU u (n + 1) (i + 2) + eps * (q seen).1 - eps * (q seen).1) = u i
    ring
  | n + 2, i, seen, gs, 1, _, _ => by
    show u (i + 1) + eps * (q seen).2.2 - eps * (q seen).2.2 = u (i + 1)
    ring
  | n + 2, i, seen, gs, j + 2, _, h => by
    have ih := uBack_view u eps q (n + 1) (i + 2) (seen ++ [gs.headD 0]) gs.tail j (by omega)
      (by omega)
    show uBack eps q (n + 1) (tailU u (n + 1) (i + 2) + eps * (q seen).1 - eps * (q seen).1)
        (sentL u eps q (n + 1) (i + 2) (seen ++ [gs.headD 0]) gs.tail) (seen ++ [gs.headD 0])
        gs.tail j = u (i + (j + 2))
    rw [add_sub_cancel_right, ih]
    congr 1
    omega
  | 0, _, _, _, _, h, _ => by omega
  | 1, _, _, _, _ + 3, _, h => by omega

/-! ## Rows of scalars -/

/-- Below N it is the value. -/
theorem onNat_of_lt {N : ℕ} (v : Fin N → K) (j : ℕ) (h : j < N) : onNat v j = v ⟨j, h⟩ :=
  dif_pos h

/-- The same at a number of the type. -/
theorem onNat_fin {N : ℕ} (v : Fin N → K) (j : Fin N) : onNat v j = v j := dif_pos j.2

/-- A function that is 0 from N on is made of its first N values. -/
theorem onNat_of_zero {N : ℕ} (w : ℕ → K) (h : ∀ j, N ≤ j → w j = 0) :
    onNat (fun j : Fin N => w j) = w := by
  funext j
  by_cases hj : j < N
  · exact onNat_of_lt _ j hj
  · rw [h j (by omega)]
    exact dif_neg hj

/-- Pairs as a row of scalars; 0 beyond them. -/
def flatL : List (K × K) → ℕ → K
  | [], _ => 0
  | p :: _, 0 => p.1
  | p :: _, 1 => p.2
  | _ :: l, j + 2 => flatL l j

/-- A scalar and pairs as a row of scalars. -/
def flatV (m : K) (l : List (K × K)) : ℕ → K
  | 0 => m
  | j + 1 => flatL l j

/-- Pairs, written in a row and cut again. -/
theorem pairsOf_flatL : ∀ l : List (K × K), pairsOf (flatL l) l.length = l
  | [] => rfl
  | p :: l => by
    show (p.1, p.2) :: pairsOf (flatL l) l.length = p :: l
    rw [pairsOf_flatL l]

/-- A row, cut into pairs and written in a row again. -/
theorem flatL_pairsOf : ∀ (n : ℕ) (w : ℕ → K) (j : ℕ), j < 2 * n → flatL (pairsOf w n) j = w j
  | 0, _, _, h => by omega
  | _ + 1, _, 0, _ => rfl
  | _ + 1, _, 1, _ => rfl
  | n + 1, w, j + 2, h => flatL_pairsOf n (fun j => w (j + 2)) j (by omega)

omit [CommRing K] in
/-- The cut reads the first 2 n scalars alone. -/
theorem pairsOf_congr : ∀ (n : ℕ) (w w' : ℕ → K), (∀ j, j < 2 * n → w j = w' j) →
    pairsOf w n = pairsOf w' n
  | 0, _, _, _ => rfl
  | n + 1, w, w', h => by
    show (w 0, w 1) :: pairsOf (fun j => w (j + 2)) n =
      (w' 0, w' 1) :: pairsOf (fun j => w' (j + 2)) n
    rw [h 0 (by omega), h 1 (by omega),
      pairsOf_congr n (fun j => w (j + 2)) (fun j => w' (j + 2)) fun j hj => h (j + 2) (by omega)]

omit [CommRing K] in
/-- n pairs are cut. -/
theorem pairsOf_length : ∀ (n : ℕ) (w : ℕ → K), (pairsOf w n).length = n
  | 0, _ => rfl
  | n + 1, w => congrArg (· + 1) (pairsOf_length n fun j => w (j + 2))

/-- A scalar and n pairs, written in a row and cut again. -/
theorem tell_flat (m : K) (l : List (K × K)) (n : ℕ) (hl : l.length = n) :
    tellL (onNat fun j : Fin (2 * n + 1) => flatV m l j) n = (m, l) := by
  have e0 : onNat (fun j : Fin (2 * n + 1) => flatV m l j) 0 = m :=
    onNat_of_lt _ 0 (by omega)
  have e1 : pairsOf (fun i => onNat (fun j : Fin (2 * n + 1) => flatV m l j) (i + 1)) n = l := by
    have e2 := pairsOf_flatL l
    rw [hl] at e2
    refine Eq.trans (pairsOf_congr n _ (flatL l) fun i hi => ?_) e2
    exact onNat_of_lt _ (i + 1) (by omega)
  exact Prod.ext e0 e1

/-- A row, cut and written in a row again. -/
theorem flat_tell {n : ℕ} (c : Fin (2 * n + 1) → K) (j : Fin (2 * n + 1)) :
    flatV (tellL (onNat c) n).1 (tellL (onNat c) n).2 j = c j := by
  obtain ⟨j, hj⟩ := j
  cases j with
  | zero => exact onNat_of_lt c 0 hj
  | succ i =>
    show flatL (pairsOf (fun j => onNat c (j + 1)) n) i = c ⟨i + 1, hj⟩
    rw [flatL_pairsOf n _ i (by omega)]
    exact onNat_of_lt c (i + 1) hj

/-! ## The bijection -/

/-- **What is sent** at the coefficients v: the sum of the hiding polynomial, then the rounds'
pairs. seen: the challenges heard in front of the sumcheck's variables. gs: the sumcheck's
challenges. -/
def viewL (eps : K) (q : List K → K × K × K) (n : ℕ) (seen gs : List K)
    (v : Fin (2 * n + 1) → K) : K × List (K × K) :=
  (sumU (onNat v) n, sentL (onNat v) eps q n 0 seen gs)

/-- The coefficients from a row of scalars in the shape of what is sent. -/
def coefL (eps : K) (q : List K → K × K × K) (n : ℕ) (seen gs : List K)
    (c : Fin (2 * n + 1) → K) : Fin (2 * n + 1) → K :=
  fun j => uBack eps q n (tellL (onNat c) n).1 (tellL (onNat c) n).2 seen gs j

/-- What is sent, in a row. -/
def rowL (eps : K) (q : List K → K × K × K) (n : ℕ) (seen gs : List K)
    (v : Fin (2 * n + 1) → K) : Fin (2 * n + 1) → K :=
  fun j => flatV (viewL eps q n seen gs v).1 (viewL eps q n seen gs v).2 j

/-- What is sent at v is its row, cut. -/
theorem tell_rowL (eps : K) (q : List K → K × K × K) (n : ℕ) (seen gs : List K)
    (v : Fin (2 * n + 1) → K) :
    tellL (onNat (rowL eps q n seen gs v)) n = viewL eps q n seen gs v :=
  tell_flat _ _ n (sentL_length _ eps q n 0 seen gs)

/-- From the row of what is sent at v comes v. -/
theorem coefL_rowL (eps : K) (q : List K → K × K × K) (n : ℕ) (hn : 1 ≤ n) (seen gs : List K)
    (v : Fin (2 * n + 1) → K) : coefL eps q n seen gs (rowL eps q n seen gs v) = v := by
  funext j
  show uBack eps q n (tellL (onNat (rowL eps q n seen gs v)) n).1
    (tellL (onNat (rowL eps q n seen gs v)) n).2 seen gs j = v j
  rw [tell_rowL]
  show uBack eps q n (tailU (onNat v) n 0) (sentL (onNat v) eps q n 0 seen gs) seen gs j = v j
  rw [uBack_view (onNat v) eps q n 0 seen gs j hn j.2, Nat.zero_add, onNat_fin]

/-- What is sent at the coefficients of a row is that row, cut. -/
theorem viewL_coefL (eps : K) (q : List K → K × K × K) (n : ℕ) (hn : 1 ≤ n) (seen gs : List K)
    (c : Fin (2 * n + 1) → K) :
    viewL eps q n seen gs (coefL eps q n seen gs c) = tellL (onNat c) n := by
  have hz : onNat (coefL eps q n seen gs c) =
      uBack eps q n (tellL (onNat c) n).1 (tellL (onNat c) n).2 seen gs :=
    onNat_of_zero _ fun i hi => uBack_zero eps q n _ _ seen gs i hi
  obtain ⟨h1, h2⟩ := view_uBack eps q n (tellL (onNat c) n).1 (tellL (onNat c) n).2 seen gs
    (pairsOf_length n _) hn
  show (tailU (onNat (coefL eps q n seen gs c)) n 0,
    sentL (onNat (coefL eps q n seen gs c)) eps q n 0 seen gs) = tellL (onNat c) n
  rw [hz, h1, h2]

/-- The row of what is sent at the coefficients of a row is that row. -/
theorem rowL_coefL (eps : K) (q : List K → K × K × K) (n : ℕ) (hn : 1 ≤ n) (seen gs : List K)
    (c : Fin (2 * n + 1) → K) : rowL eps q n seen gs (coefL eps q n seen gs c) = c := by
  funext j
  show flatV (viewL eps q n seen gs (coefL eps q n seen gs c)).1
    (viewL eps q n seen gs (coefL eps q n seen gs c)).2 j = c j
  rw [viewL_coefL eps q n hn]
  exact flat_tell c j

/-- **The bijection**: from the coefficients to the scalars that are sent, in a row. eps, q, seen
and gs are fixed. THE SPENDER's HALF: see the head; not to be quoted without the sender's sentence.
-/
def viewEquiv (eps : K) (q : List K → K × K × K) (n : ℕ) (hn : 1 ≤ n) (seen gs : List K) :
    (Fin (2 * n + 1) → K) ≃ (Fin (2 * n + 1) → K) where
  toFun := rowL eps q n seen gs
  invFun := coefL eps q n seen gs
  left_inv := coefL_rowL eps q n hn seen gs
  right_inv := rowL_coefL eps q n hn seen gs

/-- **What is sent at v is the row `viewEquiv v`, in the shape of what is sent.** BY ITSELF A FACT
OF SHAPE (it holds of any function that yields n pairs): NEVER TO BE QUOTED WITHOUT `viewEquiv`. THE
SPENDER's HALF: see the head; not to be quoted without the sender's sentence. -/
theorem viewL_eq_tell (eps : K) (q : List K → K × K × K) (n : ℕ) (hn : 1 ≤ n) (seen gs : List K)
    (v : Fin (2 * n + 1) → K) :
    viewL eps q n seen gs v = tellL (onNat (viewEquiv eps q n hn seen gs v)) n :=
  (tell_rowL eps q n seen gs v).symm

/-- What is sent where the summand is given by tables (`sent`, Johnson/Desc/K13/Honest/Moves.lean).
-/
def viewT (eps : K) (S : List (List K × List K)) (n : ℕ) (gs : List K)
    (v : Fin (2 * n + 1) → K) : K × List (K × K) :=
  (sumU (onNat v) n, sent (onNat v) eps n 0 S gs)

/-- At tables it is the same function. -/
theorem viewT_eq_viewL (eps : K) (S : List (List K × List K)) (n : ℕ) (gs : List K)
    (v : Fin (2 * n + 1) → K) :
    viewT eps S n gs v = viewL eps (fun seen => quadAll (foldsAll seen S)) n [] gs v :=
  congrArg (fun l => (sumU (onNat v) n, l)) (sent_eq (onNat v) eps S n 0 [] gs)

/-- The same where the summand is given by tables. THE SPENDER's HALF: see the head. -/
theorem viewT_eq_tell (eps : K) (S : List (List K × List K)) (n : ℕ) (hn : 1 ≤ n) (gs : List K)
    (v : Fin (2 * n + 1) → K) :
    viewT eps S n gs v =
      tellL (onNat (viewEquiv eps (fun seen => quadAll (foldsAll seen S)) n hn [] gs v)) n :=
  (viewT_eq_viewL eps S n gs v).trans (viewL_eq_tell _ _ n hn [] gs v)

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.uBack_zero
#print axioms VerifiableInference.Desc.K13.Honest.tailU_shift
#print axioms VerifiableInference.Desc.K13.Honest.sentL_shift
#print axioms VerifiableInference.Desc.K13.Honest.sentL_length
#print axioms VerifiableInference.Desc.K13.Honest.onNat_of_lt
#print axioms VerifiableInference.Desc.K13.Honest.onNat_fin
#print axioms VerifiableInference.Desc.K13.Honest.onNat_of_zero
#print axioms VerifiableInference.Desc.K13.Honest.pairsOf_flatL
#print axioms VerifiableInference.Desc.K13.Honest.flatL_pairsOf
#print axioms VerifiableInference.Desc.K13.Honest.pairsOf_congr
#print axioms VerifiableInference.Desc.K13.Honest.pairsOf_length
#print axioms VerifiableInference.Desc.K13.Honest.tell_flat
#print axioms VerifiableInference.Desc.K13.Honest.flat_tell
#print axioms VerifiableInference.Desc.K13.Honest.tell_rowL
#print axioms VerifiableInference.Desc.K13.Honest.viewL_coefL
#print axioms VerifiableInference.Desc.K13.Honest.viewT_eq_viewL
#print axioms VerifiableInference.Desc.K13.Honest.view_uBack
#print axioms VerifiableInference.Desc.K13.Honest.uBack_view
#print axioms VerifiableInference.Desc.K13.Honest.coefL_rowL
#print axioms VerifiableInference.Desc.K13.Honest.rowL_coefL
#print axioms VerifiableInference.Desc.K13.Honest.viewEquiv
#print axioms VerifiableInference.Desc.K13.Honest.viewL_eq_tell
#print axioms VerifiableInference.Desc.K13.Honest.viewT_eq_tell
