-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysSig.lean: the early panels' shares make up the matrix products in the keys:
the library with itself.

A key of a feed-forward segment is the sum of an affine part, of products of two values at one
position, and of a matrix product (key_eq in Inst/Model/FF/Objects.lean). The library's quantity KF
of a lookup call holds the matrix products as the sums ACC. The same file defines the panels of the
batched inner-product sumcheck, a panel's share in the sum, and Sig0, the sum of the shares of the
early panels G, U, O, D, V, LR. This file shows that Sig0, at the true contractions of the cells,
is the sum of all ACC under the calls' and the layers' weights.

Every statement here compares objects of the library with objects of the library. No theorem names
the verifier in OnBytes/. The file imports Johnson/Road/FormsKeysV.lean and
Johnson/Road/FormsKeysW.lean, which do, for six lemmas that do not (acc_V, acc_O, acc_LR, acc_G,
acc_U, acc_D) and for wsum.

Main definitions: six, sixIn. Main theorems: sig0_acc; share_G, share_U, share_V, share_O, share_D,
share_LR (the share of one panel); early_pans; famsIn_six, sum_ACC_six, ACC_zero; ACC_G, ACC_U.

The cuts. The family G has f entries; on a layer with routed experts the entries from fe on belong
to the routed expert, whose products are no matrix product of the key (mat is 0 there), and the
panel G sums over the fSh l shared hidden units. The same for U. The panel D has f columns, and
both its sides are 0 from fSh l on; the matrix product in the key of D runs over fSh l hidden
units. The panel LR has a row for each layer with routed experts; the family LR is present in these
layers alone.

The hypotheses, and that they can be met.
 - D.fe ≤ D.f: without it the panels G, U and D would run past the family's entries or the panel's
   columns. Met by the reference sizes and by all sizes with the library's Dim.OK (ref_fe, fe_of_ok
   in Johnson/Road/FormsKeysTn.lean).
 - H1 l j = hhU D t l j (zpos D z) for l < nl and j < fSh l: the vector that the panel D reads is
   the honest vector of the gated products. Met by taking that for H1. Nothing is asked of the
   second point u', of H2, tb, L0, zh or w.

What is not claimed. Nothing is said of the late panels and of the products in the keys (Sig1, TS),
of the places of the panels in the two long vectors, or of how a prover's vector H1 is shown to be
the honest one. Nothing is a statement on what a verifier's acceptance shows. The program does not
import this file.
-/
import Johnson.Road.FormsKeysV
import Johnson.Road.FormsKeysW

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam LW Pan Rd rdTrue pans Sig0 ACC mat len call fams famsIn present
  isExp isExpL fSh routed ew el wc zpos valU hhU)

variable {K : Type} [Field K]

/-! ## Tools -/

/-- A weighted sum of extensions whose terms vanish from m on stops at m. -/
theorem wsum_cut (g : ℕ → K) (lt : ℕ) (u : ℕ → K) {m n : ℕ} (h : m ≤ n) {F : ℕ → ℕ → K}
    (h0 : ∀ x, m ≤ x → x < n → ∀ i, F x i = 0) : wsum g lt u n F = wsum g lt u m F := by
  unfold wsum
  symm
  refine sum_subset (range_subset_range.mpr h) fun x hx hn => ?_
  have e : F x = fun _ => 0 :=
    funext (h0 x (Nat.not_lt.mp fun hc => hn (mem_range.mpr hc)) (mem_range.mp hx))
  rw [e, Blocks.ext_const, mul_zero]

/-- A sum of products of two factors that both vanish from m on stops at m. -/
theorem sum_cut_both {m n : ℕ} (h : m ≤ n) (a b : ℕ → K) :
    ∑ j ∈ range n, (if j < m then a j else 0) * (if j < m then b j else 0) =
      ∑ j ∈ range m, a j * b j := by
  rw [← sum_subset (range_subset_range.mpr h)]
  · exact sum_congr rfl fun j hj => by rw [if_pos (mem_range.mp hj), if_pos (mem_range.mp hj)]
  · intro j _ hj
    rw [if_neg fun hc => hj (mem_range.mpr hc), zero_mul]

/-- A weight under the factor of a shift, times a number: the weight times the number under the
factor. -/
theorem scl_swap (k : ℕ) (a b : K) :
    Inst.Model.Site.scl k a * b = a * Inst.Model.Site.scl k b := by
  rw [Inst.Model.Site.scl_mul, Inst.Model.Site.mul_scl]

/-- A sum over the odd numbers below n. -/
theorem sum_odd (f : ℕ → K) : ∀ n : ℕ,
    ∑ l ∈ range n, (if l % 2 = 1 then f l else 0) = ∑ l' ∈ range (n / 2), f (2 * l' + 1)
  | 0 => by simp
  | n + 1 => by
    rw [sum_range_succ, sum_odd f n]
    by_cases h : n % 2 = 1
    · have e : (n + 1) / 2 = n / 2 + 1 := by omega
      have e2 : 2 * (n / 2) + 1 = n := by omega
      rw [if_pos h, e, sum_range_succ, e2]
    · have e : (n + 1) / 2 = n / 2 := by omega
      rw [if_neg h, e, add_zero]

/-- From the shared hidden units on, a hidden unit of a layer belongs to the routed expert. -/
theorem routed_true (D : Dim) {l x : ℕ} (h1 : fSh D l ≤ x) (h2 : x < D.f) :
    routed D l x = true := by
  unfold fSh at h1
  unfold routed
  cases h : isExpL l with
  | false =>
    rw [h] at h1
    have h1' : D.f ≤ x := h1
    omega
  | true =>
    rw [h] at h1
    have h1' : D.fe ≤ x := h1
    simpa using h1'

/-- The shared hidden units of a layer are at most its hidden units, if an expert has no more. -/
theorem fSh_le (D : Dim) (hfe : D.fe ≤ D.f) (l : ℕ) : fSh D l ≤ D.f := by
  unfold fSh
  split_ifs
  · exact hfe
  · exact Nat.le_refl _

/-! ## The families with a matrix product -/

/-- The six families whose keys hold a matrix product. -/
def six : List Fam := [.G, .U, .V, .O, .D, .LR]

/-- Those of them that call c holds in a layer; b: the layer has routed experts. -/
def sixIn : Fin 8 → Bool → List Fam
  | 0, _ => [.G, .U]
  | 1, _ => [.O, .D, .V]
  | 2, true => [.LR]
  | _, _ => []

/-- The families of call c that are present in layer l and hold a matrix product. -/
theorem famsIn_six (c : Fin 8) (l : ℕ) :
    (famsIn c l).filter (fun s => decide (s ∈ six)) = sixIn c (isExpL l) := by
  have h : ∀ (b : Bool) (c : Fin 8),
      ((fams c).filter fun s => !isExp s || b).filter (fun s => decide (s ∈ six)) =
        sixIn c b := by decide
  exact h (isExpL l) c

section Acc

variable [scl : Scl] (D : Dim) (t : Cell → K) (w : ℕ → LW K) (z : ℕ → K)

/-- The keys of the other families hold no matrix product. -/
theorem mat_zero {s : Fam} (hs : s ∉ six) (l x i : ℕ) : mat D t w s l x i = 0 := by
  cases s <;> first
    | rfl
    | exact absurd (by simp [six]) hs

/-- So their sum ACC is 0. -/
theorem ACC_zero {s : Fam} (hs : s ∉ six) (l : ℕ) : ACC D t w z s l = 0 := by
  unfold ACC
  refine sum_eq_zero fun x _ => ?_
  have e : (fun i => mat D t w s l x i) = fun _ => 0 := funext (mat_zero D t w hs l x)
  rw [e, Blocks.ext_const, mul_zero]

/-- In a sum of ACC over a list of families only the six count. -/
theorem sum_ACC_six (l : ℕ) : ∀ L : List Fam,
    (L.map fun s => ACC D t w z s l).sum =
      ((L.filter fun s => decide (s ∈ six)).map fun s => ACC D t w z s l).sum
  | [] => rfl
  | s :: L => by
    by_cases hs : s ∈ six
    · rw [List.filter_cons_of_pos (by simpa using hs), List.map_cons, List.map_cons, List.sum_cons,
        List.sum_cons, sum_ACC_six l L]
    · rw [List.filter_cons_of_neg (by simpa using hs), List.map_cons, List.sum_cons,
        ACC_zero D t w z hs l, zero_add, sum_ACC_six l L]

/-- ACC of the gate: the sum stops at the shared hidden units. -/
theorem ACC_G (hfe : D.fe ≤ D.f) (l : ℕ) : ACC D t w z .G l =
    wsum (ew D z .G) D.lT (zpos D z) (fSh D l) (fun x i => mat D t w .G l x i) := by
  show wsum (ew D z .G) D.lT (zpos D z) D.f (fun x i => mat D t w .G l x i) = _
  refine wsum_cut (ew D z .G) D.lT (zpos D z) (fSh_le D hfe l) fun x h1 h2 i => ?_
  simp [mat, routed_true D h1 h2]

/-- The same for the up projection. -/
theorem ACC_U (hfe : D.fe ≤ D.f) (l : ℕ) : ACC D t w z .U l =
    wsum (ew D z .U) D.lT (zpos D z) (fSh D l) (fun x i => mat D t w .U l x i) := by
  show wsum (ew D z .U) D.lT (zpos D z) D.f (fun x i => mat D t w .U l x i) = _
  refine wsum_cut (ew D z .U) D.lT (zpos D z) (fSh_le D hfe l) fun x h1 h2 i => ?_
  simp [mat, routed_true D h1 h2]

end Acc

/-! ## The share of each early panel -/

section Shares

variable [scl : Scl] (D : Dim) (t : Cell → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
  (z zh u' : ℕ → K) (H1 H2 : ℕ → ℕ → K)

/-- Panel G. -/
theorem share_G (hfe : D.fe ≤ D.f) :
    Pan.G.share D (rdTrue D t z u' H1 H2) tb L0 w z zh =
      wc D z 0 * ∑ l ∈ range D.nl, el D z 0 l * ACC D t w z .G l := by
  show wc D z 0 * ∑ l ∈ range D.nl, Inst.Model.Site.scl (D.Pl l).kg (el D z 0 l) *
    ∑ j ∈ range D.d, valU D t .m l j (zpos D z) *
      ∑ x ∈ range (fSh D l), ew D z .G x * (w l).Wg j x = _
  congr 1
  refine sum_congr rfl fun l _ => ?_
  rw [scl_swap, ACC_G D t w z hfe l, acc_G D t w (ew D z .G) (zpos D z) l]

/-- Panel U. -/
theorem share_U (hfe : D.fe ≤ D.f) :
    Pan.U.share D (rdTrue D t z u' H1 H2) tb L0 w z zh =
      wc D z 0 * ∑ l ∈ range D.nl, el D z 0 l * ACC D t w z .U l := by
  show wc D z 0 * ∑ l ∈ range D.nl, Inst.Model.Site.scl (D.Pl l).ku (el D z 0 l) *
    ∑ j ∈ range D.d, valU D t .m l j (zpos D z) *
      ∑ x ∈ range (fSh D l), ew D z .U x * (w l).Wu j x = _
  congr 1
  refine sum_congr rfl fun l _ => ?_
  rw [scl_swap, ACC_U D t w z hfe l, acc_U D t w (ew D z .U) (zpos D z) l]

/-- Panel V. -/
theorem share_V :
    Pan.V.share D (rdTrue D t z u' H1 H2) tb L0 w z zh =
      wc D z 1 * ∑ l ∈ range D.nl, el D z 1 l * ACC D t w z .V l := by
  show wc D z 1 * ∑ l ∈ range D.nl, Inst.Model.Site.scl (D.Pl l).kv (el D z 1 l) *
    ∑ j ∈ range D.d, valU D t .a l j (zpos D z) *
      ∑ x ∈ range D.dkv, ew D z .V x * (w l).Wv j x = _
  congr 1
  refine sum_congr rfl fun l _ => ?_
  rw [scl_swap, ← acc_V D t w (ew D z .V) (zpos D z) l]
  rfl

/-- Panel O. -/
theorem share_O :
    Pan.O.share D (rdTrue D t z u' H1 H2) tb L0 w z zh =
      wc D z 1 * ∑ l ∈ range D.nl, el D z 1 l * ACC D t w z .O l := by
  show wc D z 1 * ∑ l ∈ range D.nl, Inst.Model.Site.scl (D.Pl l).ko (el D z 1 l) *
    ∑ j ∈ range D.dq, valU D t .o l j (zpos D z) *
      ∑ x ∈ range D.d, ew D z .O x * (w l).Wo j x = _
  congr 1
  refine sum_congr rfl fun l _ => ?_
  rw [scl_swap, ← acc_O D t w (ew D z .O) (zpos D z) l]
  rfl

/-- Panel D. The panel has f columns and both its sides are 0 from the shared hidden units on. H1
is asked to be the honest vector of the gated products at the lookup's token point, on the layers of
the segment and their shared hidden units. -/
theorem share_D (hfe : D.fe ≤ D.f)
    (hH : ∀ l, l < D.nl → ∀ j, j < fSh D l → H1 l j = hhU D t l j (zpos D z)) :
    Pan.D.share D (rdTrue D t z u' H1 H2) tb L0 w z zh =
      wc D z 1 * ∑ l ∈ range D.nl, el D z 1 l * ACC D t w z .D l := by
  show wc D z 1 * ∑ l ∈ range D.nl, Inst.Model.Site.scl (D.Pl l).kd (el D z 1 l) *
    ∑ j ∈ range D.f, (if j < fSh D l then H1 l j else 0) *
      (if j < fSh D l then ∑ x ∈ range D.d, ew D z .D x * (w l).Wd j x else 0) = _
  congr 1
  refine sum_congr rfl fun l hl => ?_
  rw [scl_swap, sum_cut_both (fSh_le D hfe l)]
  have e : ∑ j ∈ range (fSh D l), H1 l j * ∑ x ∈ range D.d, ew D z .D x * (w l).Wd j x =
      ∑ j ∈ range (fSh D l), hhU D t l j (zpos D z) *
        ∑ x ∈ range D.d, ew D z .D x * (w l).Wd j x :=
    sum_congr rfl fun j hj => by rw [hH l (mem_range.mp hl) j (mem_range.mp hj)]
  rw [e, ← acc_D D t w (ew D z .D) (zpos D z) l]
  rfl

/-- Panel LR: row l' is layer 2 l' + 1. -/
theorem share_LR :
    Pan.LR.share D (rdTrue D t z u' H1 H2) tb L0 w z zh =
      wc D z 2 * ∑ l' ∈ range D.ne, el D z 2 (2 * l' + 1) * ACC D t w z .LR (2 * l' + 1) := by
  show wc D z 2 * ∑ l' ∈ range D.ne,
    Inst.Model.Site.scl (D.Pl (2 * l' + 1)).kr (el D z 2 (2 * l' + 1)) *
    ∑ j ∈ range D.d, valU D t .m (2 * l' + 1) j (zpos D z) *
      ∑ x ∈ range D.nx, ew D z .LR x * (w (2 * l' + 1)).Wr j x = _
  congr 1
  refine sum_congr rfl fun l' _ => ?_
  rw [scl_swap, ← acc_LR D t w (ew D z .LR) (zpos D z) (2 * l' + 1)]
  rfl

/-! ## All early panels -/

omit scl in
/-- The early panels. -/
theorem early_pans : (pans D).filter (fun p => !p.late) = [.G, .U, .O, .D, .V, .LR] := by
  have hm : ∀ f : ℕ → Pan, (∀ n, (f n).late = true) → ∀ l : List ℕ,
      (l.map f).filter (fun p => !p.late) = [] := by
    intro f hf l
    rw [List.filter_eq_nil_iff]
    intro a ha
    obtain ⟨n, -, rfl⟩ := List.mem_map.mp ha
    simp [hf n]
  unfold pans
  simp only [List.filter_append]
  rw [hm Pan.Gr (fun _ => rfl), hm Pan.Ur (fun _ => rfl), hm Pan.Dr (fun _ => rfl)]
  rfl

/-- The early panels' shares make up the matrix products in the keys. At the true contractions of
the cells at the lookup's token point, with the honest vector of the gated products: the sum of the
shares of the panels G, U, O, D, V, LR is the sum over the calls, under the calls' weights, over the
layers, under the layers' weights, and over the families of the call that are present in the layer,
of ACC: the matrix products in the family's keys, summed under the entries' weights and extended at
the token point. For every second point u', every H2, tb, L0 and zh: the early panels read none of
them. -/
theorem sig0_acc (hfe : D.fe ≤ D.f)
    (hH : ∀ l, l < D.nl → ∀ j, j < fSh D l → H1 l j = hhU D t l j (zpos D z)) :
    Sig0 D (rdTrue D t z u' H1 H2) tb L0 w z zh =
      ∑ c, wc D z c * ∑ l ∈ range D.nl, el D z c l *
        ((famsIn c l).map fun s => ACC D t w z s l).sum := by
  have hs : ∀ (c : Fin 8) (l : ℕ), ((famsIn c l).map fun s => ACC D t w z s l).sum =
      ((sixIn c (isExpL l)).map fun s => ACC D t w z s l).sum := by
    intro c l
    rw [sum_ACC_six D t w z l, famsIn_six]
  have hLR : ∑ l ∈ range D.nl, el D z 2 l *
      ((sixIn 2 (isExpL l)).map fun s => ACC D t w z s l).sum =
      ∑ l' ∈ range D.ne, el D z 2 (2 * l' + 1) * ACC D t w z .LR (2 * l' + 1) := by
    have e : ∑ l ∈ range D.nl, (if l % 2 = 1 then el D z 2 l * ACC D t w z .LR l else 0) =
        ∑ l' ∈ range D.ne, el D z 2 (2 * l' + 1) * ACC D t w z .LR (2 * l' + 1) :=
      sum_odd (fun l => el D z 2 l * ACC D t w z .LR l) D.nl
    rw [← e]
    refine sum_congr rfl fun l _ => ?_
    by_cases h : l % 2 = 1
    · have hb : isExpL l = true := by simp [isExpL, h]
      rw [hb, if_pos h]
      show el D z 2 l * (ACC D t w z .LR l + 0) = _
      rw [add_zero]
    · have hb : isExpL l = false := by simp [isExpL, h]
      rw [hb, if_neg h]
      show el D z 2 l * 0 = _
      rw [mul_zero]
  have h0 : ∀ l, ((sixIn 0 (isExpL l)).map fun s => ACC D t w z s l).sum =
      ACC D t w z .G l + ACC D t w z .U l := fun l => by
    show ACC D t w z .G l + (ACC D t w z .U l + 0) = _
    rw [add_zero]
  have h1 : ∀ l, ((sixIn 1 (isExpL l)).map fun s => ACC D t w z s l).sum =
      ACC D t w z .O l + ACC D t w z .D l + ACC D t w z .V l := fun l => by
    show ACC D t w z .O l + (ACC D t w z .D l + (ACC D t w z .V l + 0)) = _
    ring
  have hz : ∀ c : Fin 8, 2 < c.val → ∀ l,
      ((sixIn c (isExpL l)).map fun s => ACC D t w z s l).sum = 0 := by
    intro c hc l
    have e : ∀ b, sixIn c b = [] := by
      revert c
      decide
    rw [e]
    rfl
  unfold Sig0
  rw [early_pans D]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hs]
  rw [share_G D t tb L0 w z zh u' H1 H2 hfe, share_U D t tb L0 w z zh u' H1 H2 hfe,
    share_O D t tb L0 w z zh u' H1 H2, share_D D t tb L0 w z zh u' H1 H2 hfe hH,
    share_V D t tb L0 w z zh u' H1 H2, share_LR D t tb L0 w z zh u' H1 H2, Fin.sum_univ_eight,
    hLR]
  simp only [h0, h1, hz 3 (by decide), hz 4 (by decide), hz 5 (by decide), hz 6 (by decide),
    hz 7 (by decide), mul_zero, sum_const_zero, mul_add, sum_add_distrib]
  ring

end Shares

#print axioms early_pans
#print axioms famsIn_six
#print axioms share_G
#print axioms share_D
#print axioms share_LR
#print axioms sig0_acc

end OnBytes.Road
