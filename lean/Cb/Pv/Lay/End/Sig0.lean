-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/Sig0.lean: the shares of the early panels of a group of layers make up the matrix
products in the keys.

The batched sumcheck of a layers' sub-proof sums the products of two long vectors, panel by panel
(Inst/Model/FF/Objects.lean). The early panels G, U, O, D, V, LR hold the matrix products of the
keys at the lookup's token point.

Main names:
  `wsum`: a weighted sum of extensions. `wsum_scl_matrix`: products of a vector with the columns of
  a matrix, under the factor of a shift.
  `acc_O`, `acc_LR`, `acc_G`, `acc_U`, `acc_D`, `acc_V`: the matrix products of a family at one
  layer.
  `share_G`, `share_U`, `share_V`, `share_O`, `share_D`, `share_LR`: the share of each early panel.
  `sig0_acc`: at the true contractions of the cells at the lookup's token point, with the honest
  vector of the gated products, Sig0 is the sum over calls, layers and families of ACC.
Limits: identities in a field alone. Nothing on a sumcheck, on a distribution of a challenge or on
soundness.


-/
import Inst.Model.FF.Objects

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End.Sig

open Finset
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam LW Pan Rd rdTrue pans Sig0 ACC mat len call fams famsIn present
  isExp isExpL fSh routed ew el wc zpos valU hhU)

variable {K : Type} [Field K]

/-! ## Weighted sums of extensions -/

/-- The sum over x below n of g x times the extension of F x over the 2^lt positions at u. -/
def wsum (g : ℕ → K) (lt : ℕ) (u : ℕ → K) (n : ℕ) (F : ℕ → ℕ → K) : K :=
  ∑ x ∈ range n, g x * Blocks.ext lt (F x) u

/-- A weighted sum reads F at the indices below n alone. -/
theorem wsum_congr (g : ℕ → K) (lt : ℕ) (u : ℕ → K) (n : ℕ) {F G : ℕ → ℕ → K}
    (h : ∀ x, x < n → ∀ i, F x i = G x i) : wsum g lt u n F = wsum g lt u n G := by
  unfold wsum
  refine sum_congr rfl fun x hx => ?_
  have e : F x = G x := funext (h x (mem_range.mp hx))
  rw [e]

/-- Products of a vector a with the columns of a matrix M, each under the factor of the shift k,
summed under weights g: the factor times the sum over j of the extension of a j times the sum of row
j of M under g. -/
theorem wsum_scl_matrix (g : ℕ → K) (lt : ℕ) (u : ℕ → K) (n m k : ℕ) (a M : ℕ → ℕ → K) :
    wsum g lt u n (fun x i => Inst.Model.Site.scl k (∑ j ∈ range m, a j i * M j x)) =
      Inst.Model.Site.scl k
        (∑ j ∈ range m, Blocks.ext lt (a j) u * ∑ x ∈ range n, g x * M j x) := by
  have e : ∀ x, Blocks.ext lt
      (fun i => (2 : K) ^ Inst.Model.Site.dn k * ∑ j ∈ range m, a j i * M j x) u =
      (2 : K) ^ Inst.Model.Site.dn k * ∑ j ∈ range m, Blocks.ext lt (a j) u * M j x := by
    intro x
    rw [Blocks.ext_smul, Blocks.ext_sum]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    have c : (fun i => a j i * M j x) = fun i => M j x * a j i := by
      funext i
      ring
    rw [c, Blocks.ext_smul]
    ring
  unfold wsum
  simp only [Inst.Model.Site.scl_eq]
  simp only [e]
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  refine sum_congr rfl fun x _ => ?_
  ring

/-- A shared hidden unit does not belong to the routed expert. -/
theorem routed_false (D : Dim) {l x : ℕ} (hx : x < fSh D l) : routed D l x = false := by
  unfold fSh at hx
  unfold routed
  cases h : isExpL l with
  | false => rfl
  | true =>
    rw [h] at hx
    have hx' : x < D.fe := hx
    simpa using hx'

/-! ## The matrix products of a family at one layer, under free weights -/

section Acc0

variable [scl : Scl] (D : Dim) (t : Cell → K) (w : ℕ → LW K) (g u : ℕ → K)

/-- O: the attention output o[l] with the matrix Wo. -/
theorem acc_O (l : ℕ) :
    wsum g D.lT u D.d (fun x i => mat D t w .O l x i) =
      Inst.Model.Site.scl (D.Pl l).ko
        (∑ j ∈ range D.dq, valU D t .o l j u * ∑ x ∈ range D.d, g x * (w l).Wo j x) :=
  wsum_scl_matrix g D.lT u D.d D.dq (D.Pl l).ko (fun j i => Inst.Model.FFSeg.val t .o l j i)
    (fun j x => (w l).Wo j x)

/-- LR: the array m[l] with the router's matrix Wr. -/
theorem acc_LR (l : ℕ) :
    wsum g D.lT u D.nx (fun x i => mat D t w .LR l x i) =
      Inst.Model.Site.scl (D.Pl l).kr
        (∑ j ∈ range D.d, valU D t .m l j u * ∑ x ∈ range D.nx, g x * (w l).Wr j x) :=
  wsum_scl_matrix g D.lT u D.nx D.d (D.Pl l).kr (fun j i => Inst.Model.FFSeg.val t .m l j i)
    (fun j x => (w l).Wr j x)

/-- G: the array m[l] with the gate's matrix Wg, over the shared hidden units. -/
theorem acc_G (l : ℕ) :
    wsum g D.lT u (fSh D l) (fun x i => mat D t w .G l x i) =
      Inst.Model.Site.scl (D.Pl l).kg
        (∑ j ∈ range D.d, valU D t .m l j u * ∑ x ∈ range (fSh D l), g x * (w l).Wg j x) := by
  have e : ∀ x, x < fSh D l → ∀ i, mat D t w .G l x i = Inst.Model.Site.scl (D.Pl l).kg
      (∑ j ∈ range D.d, Inst.Model.FFSeg.val t .m l j i * (w l).Wg j x) := by
    intro x hx i
    simp only [mat, Inst.Model.FFSeg.Ag, routed_false D hx, Bool.false_eq_true, if_false]
  rw [wsum_congr _ _ _ _ e]
  exact wsum_scl_matrix g D.lT u (fSh D l) D.d (D.Pl l).kg
    (fun j i => Inst.Model.FFSeg.val t .m l j i) (fun j x => (w l).Wg j x)

/-- U: the array m[l] with the matrix Wu, over the shared hidden units. -/
theorem acc_U (l : ℕ) :
    wsum g D.lT u (fSh D l) (fun x i => mat D t w .U l x i) =
      Inst.Model.Site.scl (D.Pl l).ku
        (∑ j ∈ range D.d, valU D t .m l j u * ∑ x ∈ range (fSh D l), g x * (w l).Wu j x) := by
  have e : ∀ x, x < fSh D l → ∀ i, mat D t w .U l x i = Inst.Model.Site.scl (D.Pl l).ku
      (∑ j ∈ range D.d, Inst.Model.FFSeg.val t .m l j i * (w l).Wu j x) := by
    intro x hx i
    simp only [mat, Inst.Model.FFSeg.Au, routed_false D hx, Bool.false_eq_true, if_false]
  rw [wsum_congr _ _ _ _ e]
  exact wsum_scl_matrix g D.lT u (fSh D l) D.d (D.Pl l).ku
    (fun j i => Inst.Model.FFSeg.val t .m l j i) (fun j x => (w l).Wu j x)

/-- D: the gated products of the shared hidden units, as one vector, with the matrix Wd. -/
theorem acc_D (l : ℕ) :
    wsum g D.lT u D.d (fun x i => mat D t w .D l x i) =
      Inst.Model.Site.scl (D.Pl l).kd
        (∑ j ∈ range (fSh D l), hhU D t l j u * ∑ x ∈ range D.d, g x * (w l).Wd j x) :=
  wsum_scl_matrix g D.lT u D.d (fSh D l) (D.Pl l).kd (fun j i => Inst.Model.FFSeg.hh t l j i)
    (fun j x => (w l).Wd j x)

end Acc0

section AccV

variable [scl : Scl]

/-- The matrix products in the keys of the family V at layer l, summed under weights g: the factor
2^max(0, 16 - kv) times the sum over the channels j of the extension of a[l, j] times the column
sums of Wv under g. -/
theorem acc_V (D : Dim) (t : Cell → K) (w : ℕ → LW K) (g : ℕ → K) (u : ℕ → K) (l : ℕ) :
    wsum g D.lT u D.dkv (fun x i => mat D t w .V l x i) =
      Inst.Model.Site.scl (D.Pl l).kv
        (∑ j ∈ range D.d, valU D t .a l j u * ∑ x ∈ range D.dkv, g x * (w l).Wv j x) := by
  have e : ∀ x, Blocks.ext D.lT (fun i => mat D t w .V l x i) u =
      (2 : K) ^ Inst.Model.Site.dn (D.Pl l).kv *
        ∑ j ∈ range D.d, valU D t .a l j u * (w l).Wv j x := by
    intro x
    simp only [mat, Inst.Model.Site.scl_eq, Inst.Model.FFSeg.Av]
    rw [Blocks.ext_smul, Blocks.ext_sum]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    have c : (fun i => Inst.Model.FFSeg.val t .a l j i * (w l).Wv j x) =
        fun i => (w l).Wv j x * Inst.Model.FFSeg.val t .a l j i := by
      funext i
      ring
    rw [c, Blocks.ext_smul]
    unfold valU
    ring
  unfold wsum
  simp only [e, Inst.Model.Site.scl_eq, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  refine sum_congr rfl fun x _ => ?_
  ring

end AccV

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

end Cb.Pv.Lay.End.Sig
