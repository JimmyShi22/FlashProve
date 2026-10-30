-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/LookupRel.lean: the lookup argument's parameters, relations and counts of bad challenges.

The lookup argument shows that committed looked-up values (keys in Lean names) are entries of public
tables. This file has the part that needs no protocol; Blocks/LookupBlock.lean builds the protocol.

The keys come in NT ≤ 2^σ batches (trees) of nblk = 2^D keys, together the forest. Tree θ has the
table `tb θ` of 2^r entries. The key side is the forest of product trees over the leaves α - key;
its tree products are Z_θ (`LkPar.Zt`). On the table side B[i, θ, π] is bit π of the multiplicity of
table entry i, a leaf is 1 + B[i, θ, π] (α - 1 - `tb θ i`), and the tree products are Y_(θ,π)
(`LkPar.Yt`).

 * Relations on true vectors: `LkPar.InTable` (R_lkp: every key is a value of its table),
   `LkPar.Bits`, `LkPar.DegE` (the degree check), `LkPar.Ident` (the identity between the Z_θ and
   the Y_(θ,π)).
 * Bad challenges: `LkPar.BadAl` (α; at most nblk - 1 values), `BadPt`, `BadPtFam`, `LkPar.BadXi`
   (the root test: the sent tree products satisfy Ident).
 * Honest multiplicities: `LkPar.HonB`.

Choices made here. (1) The parameters are given tree by tree (`tb θ`, `t0 θ`, `φ θ`), and D, r, lp
are free numbers. Calls do not occur here; they are in Blocks/LookupCalls.lean. (2) `LkPar.WF` has
the condition D ≤ r + 2^lp, which makes nblk - ϕ_θ smaller than the characteristic. (3)
`LkPar.BadAl` reads any B through `LkPar.bitOf` and does not ask that all B are bits, and it asks
that the degrees fit (padding positions and multiplicities add up to nblk) only for the first tree
with a key outside its table. (4) A point is one verifier message, so the number of bad points is
bounded by g |E|^(g-1).

Notation:
 * D, σ, r, lp, NT: natural numbers, fields of `LkPar`: 2^D keys in a tree, NT trees, tables with
   2^r entries, 2^lp bits for a multiplicity; σ: the number of bits of a tree's index (the head of
   Blocks/LookupWhole.lean).
 * τ, τ⁰, ϕ_θ (also ϕ): `tb` θ, `tb` θ (`t0` θ), `φ` θ; TL: `LkPar.leafT`.
 * `ext` g v pt, written ~v(pt): the multilinear extension of the vector v of length 2^g at the
   point pt (Blocks/Ext.lean).
 * lev_l: `lvl` s n A l: level l of a forest.
 * `cnt` P: the number of elements of a finite type with the property P (Prob/Cnt.lean).
 * `nat` v: a vector as a function on ℕ, 0 beyond its end (Blocks/Basic.lean).
-/
import Blocks.Ext
import Alg.Lookup
import Alg.Count
import Alg.SumCheck
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks

open Finset Prob

/-! ## 1. The levels of a forest of product trees -/

section Levels

variable {E : Type} [CommMonoid E]

private theorem prod_range_mul_add (A B : ℕ) (f : ℕ → E) :
    ∏ i ∈ range (A * B), f i = ∏ a ∈ range A, ∏ b ∈ range B, f (a * B + b) := by
  induction A with
  | zero => simp
  | succ A ih => rw [Nat.succ_mul, prod_range_add, ih, prod_range_succ]

/-- Level l of a forest. The leaves A have the index (j|X₀) = j 2^s + X₀ with n high bits j. Level l
has the index X of l + s bits, and its entry is the product of the leaves below it. Level n is A,
and level 0 holds the products of the trees. -/
def lvl (s n : ℕ) (A : ℕ → E) (l : ℕ) (X : ℕ) : E :=
  ∏ j ∈ range (2 ^ (n - l)), A (j * 2 ^ (l + s) + X)

theorem lvl_top (s n : ℕ) (A : ℕ → E) : lvl s n A n = A := by
  funext X
  simp [lvl]

/-- For l < n (h): lev_l[X] = lev_(l+1)[(0|X)] lev_(l+1)[(1|X)]. -/
theorem lvl_step (s n : ℕ) (A : ℕ → E) {l : ℕ} (h : l < n) (X : ℕ) :
    lvl s n A l X = lvl s n A (l + 1) X * lvl s n A (l + 1) (X + 2 ^ (l + s)) := by
  unfold lvl
  have h1 : 2 ^ (n - l) = 2 ^ (n - (l + 1)) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h1, prod_range_mul_add, ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  rw [prod_range_succ, prod_range_one]
  congr 2
  · rw [show l + 1 + s = (l + s) + 1 by omega, pow_succ]
    ring
  · rw [show l + 1 + s = (l + s) + 1 by omega, pow_succ]
    ring

theorem lvl_zero (s n : ℕ) (A : ℕ → E) (X : ℕ) :
    lvl s n A 0 X = ∏ j ∈ range (2 ^ n), A (j * 2 ^ s + X) := by
  simp [lvl]

end Levels

/-! ## 2. Parameters, hidden data, and the challenge α -/

/-- The public parameters of a lookup argument, tree by tree: 2^D keys in a tree, NT ≤ 2^σ trees,
tables with 2^r entries (a shorter table is repeated), 2^lp bits for a multiplicity. Tree θ has the
table tb θ, the padding value tb θ (t0 θ) and φ θ padding positions. -/
structure LkPar (E : Type) where
  D : ℕ
  σ : ℕ
  r : ℕ
  lp : ℕ
  NT : ℕ
  tb : ℕ → ℕ → E
  t0 : ℕ → ℕ
  φ : ℕ → ℕ
  /-- the order in which the rounds of the last layer of the key side bind its D - 1 + σ variables
  (variable t belongs to coordinate t of the layer's point; coordinate 0 belongs to the top bit of
  the index). All other layers bind coordinate 0 first. The order changes the order of the rounds
  and of the challenges, and nothing else: every coordinate of the end point keeps its place. -/
  ordK : List ℕ := PL.vars (D - 1 + σ)
  /-- which coordinates of the end point z of the key side the verifier rejects at 0: those by which
  the caller's later blocks divide -/
  zf : ℕ → Bool := fun _ => true

namespace LkPar

/-- The order of the last layer of the key side names each of its variables once. -/
def OrdOK {E : Type} (P : LkPar E) : Prop := P.ordK.Perm (PL.vars (P.D - 1 + P.σ))

/-- The order of the rounds of layer l of the key side. -/
def kOrd {E : Type} (P : LkPar E) (l : ℕ) : List ℕ :=
  if l + 1 = P.D then P.ordK else PL.vars (l + P.σ)

/-- Is coordinate t of the point at level l of the key side rejected at 0? Below level D all are:
the next layer divides by them. At level D the point is the end point z. -/
def kf {E : Type} (P : LkPar E) (l t : ℕ) : Bool := decide (l < P.D) || P.zf t

theorem kf_of_lt {E : Type} (P : LkPar E) {l : ℕ} (h : l < P.D) (t : ℕ) : P.kf l t = true := by
  simp [kf, h]

theorem kf_top {E : Type} (P : LkPar E) (t : ℕ) : P.kf P.D t = P.zf t := by simp [kf]

theorem OrdOK.kOrd {E : Type} {P : LkPar E} (h : P.OrdOK) (l : ℕ) :
    (P.kOrd l).Perm (PL.vars (l + P.σ)) := by
  unfold LkPar.kOrd
  split_ifs with hl
  · have e : P.D - 1 = l := by omega
    rw [← e]
    exact h
  · exact List.Perm.refl _

variable {E : Type} [Field E] (P : LkPar E)

/-- The sizes fit, and the order of the last layer of the key side is an order of its variables (for
the default order this field has a default proof); p is the characteristic. The condition `char` is
2^(r+32) < p for lp = 5, where a multiplicity has 32 bits: the sum of the multiplicities of a tree
is below p. With `dle` also nblk - ϕ_θ is below p, so that the degree check is an equation of
integers. -/
structure WF (p : ℕ) : Prop where
  nt : P.NT ≤ 2 ^ P.σ
  t0 : ∀ θ, P.t0 θ < 2 ^ P.r
  φ : ∀ θ, P.φ θ ≤ 2 ^ P.D
  dle : P.D ≤ P.r + 2 ^ P.lp
  char : 2 ^ (P.r + 2 ^ P.lp) < p
  ord : P.OrdOK := by exact List.Perm.refl _

/-- R_lkp: every key of every tree is a value of the table of that tree. key θ i is key number i of
tree θ. -/
def InTable (key : ℕ → ℕ → E) : Prop := ∀ θ < P.NT, ∀ i < 2 ^ P.D, ∃ t < 2 ^ P.r, key θ i = P.tb θ t

/-- The B[i, θ, π] are bits. -/
def Bits (B : ℕ → ℕ → ℕ → E) : Prop :=
  ∀ i < 2 ^ P.r, ∀ θ < P.NT, ∀ π < 2 ^ P.lp, B i θ π * (B i θ π - 1) = 0

/-- The degree check, in E: ∑_i mult_θ(i) = nblk - ϕ_θ for every tree. -/
def DegE (B : ℕ → ℕ → ℕ → E) : Prop :=
  ∀ θ < P.NT, ∑ i ∈ range (2 ^ P.r), ∑ π ∈ range (2 ^ P.lp), (2 : E) ^ π * B i θ π =
    ((2 ^ P.D - P.φ θ : ℕ) : E)

/-- The true tree product Z_θ of the key side. -/
def Zt (key : ℕ → ℕ → E) (al : E) (θ : ℕ) : E := ∏ i ∈ range (2 ^ P.D), (al - key θ i)

/-- The true tree product Y_(θ,π) of the table side. -/
def Yt (B : ℕ → ℕ → ℕ → E) (al : E) (θ π : ℕ) : E :=
  ∏ i ∈ range (2 ^ P.r), (1 + B i θ π * (al - 1 - P.tb θ i))

/-- The identity between the tree products of the two sides, for numbers Z_θ, Y_(θ,π): Z_θ = (α - tb
θ (t0 θ))^(φ θ) ∏_π Y_(θ,π)^(2^π) for every tree θ < NT. -/
def Ident (al : E) (Z : ℕ → E) (Y : ℕ → ℕ → E) : Prop :=
  ∀ θ < P.NT, Z θ = (al - P.tb θ (P.t0 θ)) ^ P.φ θ * ∏ π ∈ range (2 ^ P.lp), Y θ π ^ 2 ^ π

/-- Tree θ has a key that is not a value of its table. -/
def OffTable (key : ℕ → ℕ → E) (θ : ℕ) : Prop :=
  θ < P.NT ∧ ∃ i < 2 ^ P.D, ∀ t < 2 ^ P.r, key θ i ≠ P.tb θ t

open Classical in
/-- The bit that B[i, θ, π] represents. -/
def bitOf (B : ℕ → ℕ → ℕ → E) (θ : ℕ) (i : Fin (2 ^ P.r)) (π : ℕ) : Bool :=
  decide (B i θ π = 1)

/-- The index of the padding value, as an index of the table. -/
def t0F (θ : ℕ) : Fin (2 ^ P.r) :=
  ⟨P.t0 θ % 2 ^ P.r, Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity))⟩

/-- The bad values of α: the zeros of F_θ - H_θ (`keySide`, `tableSide`, Alg/Lookup.lean) for the
first tree θ with a key outside its table, if the degrees fit. -/
def BadAl (key : ℕ → ℕ → E) (B : ℕ → ℕ → ℕ → E) (al : E) : Prop :=
  ∃ θ,
    Alg.IsFirst (P.OffTable key) θ ∧
    Alg.Lookup.BadAlpha (fun i : Fin (2 ^ P.D) => key θ i) (fun t : Fin (2 ^ P.r) => P.tb θ t)
      (P.t0F θ) (P.φ θ) (Alg.Lookup.mult (2 ^ P.lp) (P.bitOf B θ)) al

/-- At most nblk - 1 values of α are bad. -/
theorem cnt_badAl_le [Finite E] (key : ℕ → ℕ → E) (B : ℕ → ℕ → ℕ → E) :
    cnt (P.BadAl key B) ≤ 2 ^ P.D - 1 := by
  refine Alg.count_first_le (P.OffTable key) _ _ fun θ _ => ?_
  have h := Alg.Lookup.count_badAlpha_le (fun i : Fin (2 ^ P.D) => key θ i)
    (fun t : Fin (2 ^ P.r) => P.tb θ t) (P.t0F θ) (P.φ θ) (Alg.Lookup.mult (2 ^ P.lp) (P.bitOf B θ))
  rwa [Fintype.card_fin] at h

theorem exists_isFirst_nat {Q : ℕ → Prop} (h : ∃ m, Q m) : ∃ m, Alg.IsFirst Q m := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun m' hm' => Nat.find_min h hm'⟩

variable {P}

theorem bit_eq {B : ℕ → ℕ → ℕ → E} (hb : P.Bits B) {θ : ℕ} (hθ : θ < P.NT) (i : Fin (2 ^ P.r))
    {π : ℕ} (hπ : π < 2 ^ P.lp) :
    B i θ π = if P.bitOf B θ i π then 1 else 0 := by
  unfold bitOf
  obtain ⟨β, hβ⟩ := Alg.Lookup.exists_bit (hb i i.2 θ hθ π hπ)
  cases β with
  | false =>
    have h0 : B i θ π = 0 := by simpa using hβ
    simp [h0]
  | true =>
    have h1 : B i θ π = 1 := by simpa using hβ
    simp [h1]

/-- For a tree with a key outside its table, under `WF` at the characteristic p of E: with bits and
the degree check, Ident for the true products says F_θ(α) = H_θ(α) (`keySide`, `tableSide`,
Alg/Lookup.lean), and the degrees fit. -/
theorem badAlpha_of_ident {p : ℕ} [CharP E p] (hW : P.WF p) {key : ℕ → ℕ → E}
    {B : ℕ → ℕ → ℕ → E} {al : E} (hb : P.Bits B) (hd : P.DegE B)
    (hi : P.Ident al (P.Zt key al) (P.Yt B al)) {θ : ℕ} (hoff : P.OffTable key θ) :
    Alg.Lookup.BadAlpha (fun i : Fin (2 ^ P.D) => key θ i) (fun t : Fin (2 ^ P.r) => P.tb θ t)
      (P.t0F θ) (P.φ θ) (Alg.Lookup.mult (2 ^ P.lp) (P.bitOf B θ)) al := by
  obtain ⟨hθ, i0, hi0, hne⟩ := hoff
  refine ⟨?_, ⟨⟨i0, hi0⟩, fun t => hne t t.2⟩, ?_⟩
  · -- the degrees
    have hS : ∑ t : Fin (2 ^ P.r),
          ∑ j ∈ range (2 ^ P.lp), (2 : E) ^ j * (if P.bitOf B θ t j then (1 : E) else 0) =
        ((2 ^ P.D - P.φ θ : ℕ) : E) := by
      rw [← hd θ hθ,
        ← Fin.sum_univ_eq_sum_range (fun i => ∑ π ∈ range (2 ^ P.lp), (2 : E) ^ π * B i θ π)]
      exact sum_congr rfl fun t _ =>
        sum_congr rfl fun j hj => by rw [← bit_eq hb hθ t (mem_range.mp hj)]
    haveI : Nonempty (Fin (2 ^ P.r)) := ⟨P.t0F θ⟩
    have h1 : ∑ t, Alg.Lookup.mult (2 ^ P.lp) (P.bitOf B θ) t < p := by
      refine lt_trans (Alg.Lookup.sum_mult_lt _ _) ?_
      rw [Fintype.card_fin, ← pow_add]
      exact hW.char
    have h2 : 2 ^ P.D - P.φ θ < p :=
      lt_of_le_of_lt ((Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by norm_num) hW.dle)) hW.char
    rw [Alg.Lookup.sum_mult_eq p _ _ _ hS h1 h2, Fintype.card_fin]
    have := hW.φ θ
    omega
  · -- the identity
    have h1 := hi θ hθ
    unfold Zt Yt at h1
    rw [Fin.prod_univ_eq_prod_range (fun i => al - key θ i), h1, ← Alg.Lookup.planes_eq]
    have h0 : ((P.t0F θ : Fin (2 ^ P.r)) : ℕ) = P.t0 θ := Nat.mod_eq_of_lt (hW.t0 θ)
    beta_reduce
    rw [h0]
    congr 1
    refine prod_congr rfl fun π hπ => ?_
    rw [← Fin.prod_univ_eq_prod_range (fun i => 1 + B i θ π * (al - 1 - P.tb θ i))]
    congr 1
    exact prod_congr rfl fun t _ => by rw [← bit_eq hb hθ t (mem_range.mp hπ)]

/-- The backward step at α, under `WF` at the characteristic p of E. If the B are bits, the degree
check holds, Ident holds for the true products, and α is not bad, then every key is a value of its
table. -/
theorem inTable_of_ident {p : ℕ} [CharP E p] (hW : P.WF p) {key : ℕ → ℕ → E}
    {B : ℕ → ℕ → ℕ → E} {al : E} (hb : P.Bits B) (hd : P.DegE B)
    (hi : P.Ident al (P.Zt key al) (P.Yt B al)) (hbad : ¬ P.BadAl key B al) : P.InTable key := by
  by_contra hn
  have hex : ∃ θ, P.OffTable key θ := by
    unfold InTable at hn
    push Not at hn
    obtain ⟨θ, hθ, i, hi', h⟩ := hn
    exact ⟨θ, hθ, i, hi', h⟩
  obtain ⟨θ, hθ⟩ := exists_isFirst_nat hex
  exact hbad ⟨θ, hθ, badAlpha_of_ident hW hb hd hi hθ.1⟩

end LkPar

/-! ## 3. An identity at a point: the point is one verifier message -/

section Point

variable {E : Type} [Field E]

/-- The point p is bad for the vector d of length 2^g: d is not zero and its extension vanishes at
p. -/
def BadPt (g : ℕ) (d : ℕ → E) (p : Fin g → E) : Prop := (∃ X < 2 ^ g, d X ≠ 0) ∧ ext g d (nat p) = 0

theorem cnt_badPt_le [Fintype E] (g : ℕ) (d : ℕ → E) :
    cnt (BadPt g d) ≤ g * Fintype.card E ^ (g - 1) := by
  by_cases h : ∃ X < 2 ^ g, d X ≠ 0
  · exact (cnt_mono fun p hp => hp.2).trans (cnt_ext_zero_le g d h)
  · rw [cnt_false fun p hp => h hp.1]
    exact Nat.zero_le _

theorem eq_zero_of_not_badPt
    {g : ℕ} {d : ℕ → E} {p : Fin g → E} (h : ¬ BadPt g d p) (h0 : ext g d (nat p) = 0) :
    ∀ X < 2 ^ g, d X = 0 := by
  intro X hX
  by_contra hne
  exact h ⟨⟨X, hX, hne⟩, h0⟩

/-- The point p is bad for a family of vectors that share it: it is bad for the first member that is
not zero. -/
def BadPtFam {M : Type} [LT M] (g : ℕ) (d : M → ℕ → E) (p : Fin g → E) : Prop :=
  ∃ m, Alg.IsFirst (fun m => ∃ X < 2 ^ g, d m X ≠ 0) m ∧ ext g (d m) (nat p) = 0

theorem cnt_badPtFam_le [Fintype E] {M : Type} [LinearOrder M] (g : ℕ) (d : M → ℕ → E) :
    cnt (BadPtFam g d) ≤ g * Fintype.card E ^ (g - 1) :=
  Alg.count_first_le (fun m => ∃ X < 2 ^ g, d m X ≠ 0) (fun m p => ext g (d m) (nat p) = 0)
    _ fun m hm => cnt_ext_zero_le g (d m) hm

theorem eq_zero_of_not_badPtFam {M : Type} [LinearOrder M] [Finite M] {g : ℕ} {d : M → ℕ → E}
    {p : Fin g → E} (h : ¬ BadPtFam g d p) (h0 : ∀ m, ext g (d m) (nat p) = 0) :
    ∀ m, ∀ X < 2 ^ g, d m X = 0 := by
  intro m X hX
  by_contra hne
  obtain ⟨m', hm'⟩ := Alg.exists_isFirst (P := fun m => ∃ X < 2 ^ g, d m X ≠ 0) ⟨m, X, hX, hne⟩
  exact h ⟨m', hm', h0 m'⟩

end Point

/-! ## 4. The true vectors of the two sides -/

namespace LkPar

variable {E : Type} [Field E] (P : LkPar E)

/-! ### The key side. The index of a leaf is (i|θ) = i 2^σ + θ. -/

/-- Leaf[(i|θ)] = α - key_θ[i], and 0 for an unused θ. -/
def leafK (key : ℕ → ℕ → E) (al : E) (x : ℕ) : E :=
  if x % 2 ^ P.σ < P.NT then al - key (x % 2 ^ P.σ) (x / 2 ^ P.σ) else 0

/-- Level l of the key side. -/
def kLev (key : ℕ → ℕ → E) (al : E) (l : ℕ) : ℕ → E := lvl P.σ P.D (P.leafK key al) l

theorem kLev_top (key : ℕ → ℕ → E) (al : E) : P.kLev key al P.D = P.leafK key al := lvl_top _ _ _

private theorem split_idx (s j u : ℕ) (hu : u < 2 ^ s) :
    (j * 2 ^ s + u) % 2 ^ s = u ∧ (j * 2 ^ s + u) / 2 ^ s = j := by
  have hpos : 0 < 2 ^ s := Nat.pos_of_ne_zero (by positivity)
  constructor
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hu, Nat.zero_add]

/-- Under hθ: lev_0[θ] = Z_θ, and 0 for an unused θ. -/
theorem kLev_zero (key : ℕ → ℕ → E) (al : E) {θ : ℕ} (hθ : θ < 2 ^ P.σ) :
    P.kLev key al 0 θ = if θ < P.NT then P.Zt key al θ else 0 := by
  unfold kLev
  rw [lvl_zero]
  have h : ∀ j, P.leafK key al (j * 2 ^ P.σ + θ) = if θ < P.NT then al - key θ j else 0 := by
    intro j
    unfold leafK
    rw [(split_idx P.σ j θ hθ).1, (split_idx P.σ j θ hθ).2]
  simp only [h]
  split_ifs with hN
  · rfl
  · exact prod_eq_zero (mem_range.mpr (Nat.pos_of_ne_zero (by positivity) : 0 < 2 ^ P.D)) rfl

/-- For l < D (h): the extension of level l is that of the products of the two halves of level l + 1
(`lvl_step`). So the claim from which a layer of the key side starts is a claim on the level above
its vector. -/
theorem ext_kLev (key : ℕ → ℕ → E) (al : E) {l : ℕ} (h : l < P.D) (pt : ℕ → E) :
    ext (l + P.σ) (P.kLev key al l) pt =
        ext (l + P.σ)
          (fun X => P.kLev key al (l + 1) X * P.kLev key al (l + 1) (X + 2 ^ (l + P.σ))) pt :=
  ext_congr (fun X _ => lvl_step _ _ _ h X) pt

/-- The difference of sent and true tree products of the key side. -/
def dZ (key : ℕ → ℕ → E) (al : E) (Zv : ℕ → E) (θ : ℕ) : E :=
  (if θ < P.NT then Zv θ else 0) - P.kLev key al 0 θ

theorem dZ_eq_zero_iff (hnt : P.NT ≤ 2 ^ P.σ) (key : ℕ → ℕ → E) (al : E) (Zv : ℕ → E) :
    (∀ θ < 2 ^ P.σ, P.dZ key al Zv θ = 0) ↔ ∀ θ < P.NT, Zv θ = P.Zt key al θ := by
  constructor
  · intro h θ hθ
    have h1 := h θ (lt_of_lt_of_le hθ hnt)
    unfold dZ at h1
    rw [P.kLev_zero key al (lt_of_lt_of_le hθ hnt), if_pos hθ, if_pos hθ] at h1
    exact sub_eq_zero.mp h1
  · intro h θ hθ
    unfold dZ
    rw [P.kLev_zero key al hθ]
    split_ifs with hN
    · exact sub_eq_zero.mpr (h θ hN)
    · exact sub_self 0

/-! ### The table side. The index of a leaf is (i|θ|π) = i 2^(σ+lp) + θ 2^lp + π. -/

/-- θ, π and i of an index (i|θ|π). -/
def thOf (x : ℕ) : ℕ := (x / 2 ^ P.lp) % 2 ^ P.σ
def piOf (x : ℕ) : ℕ := x % 2 ^ P.lp
def iOf (x : ℕ) : ℕ := x / 2 ^ (P.σ + P.lp)

/-- The vector B, 0 for an unused θ. -/
def vB (B : ℕ → ℕ → ℕ → E) (x : ℕ) : E :=
  if P.thOf x < P.NT then B (P.iOf x) (P.thOf x) (P.piOf x) else 0
/-- The vector α - 1 - τ, 0 for an unused θ. -/
def vA (al : E) (x : ℕ) : E := if P.thOf x < P.NT then al - 1 - P.tb (P.thOf x) (P.iOf x) else 0
/-- The indicator of θ < NT. -/
def vI (x : ℕ) : E := if P.thOf x < P.NT then 1 else 0

/-- TL = 1 + B (α - 1 - τ) on trees, and 0 for an unused θ. -/
def leafT (B : ℕ → ℕ → ℕ → E) (al : E) (x : ℕ) : E := P.vI x + P.vB B x * P.vA al x

/-- Level l of the table side. -/
def tLev (B : ℕ → ℕ → ℕ → E) (al : E) (l : ℕ) : ℕ → E := lvl (P.σ + P.lp) P.r (P.leafT B al) l

theorem tLev_top (B : ℕ → ℕ → ℕ → E) (al : E) : P.tLev B al P.r = P.leafT B al := lvl_top _ _ _

omit [Field E] in
theorem decode (i : ℕ) {θ π : ℕ} (hθ : θ < 2 ^ P.σ) (hπ : π < 2 ^ P.lp) :
    P.iOf (i * 2 ^ (P.σ + P.lp) + (θ * 2 ^ P.lp + π)) = i ∧
    P.thOf (i * 2 ^ (P.σ + P.lp) + (θ * 2 ^ P.lp + π)) = θ ∧
    P.piOf (i * 2 ^ (P.σ + P.lp) + (θ * 2 ^ P.lp + π)) = π := by
  have hu : θ * 2 ^ P.lp + π < 2 ^ (P.σ + P.lp) := by
    rw [pow_add]
    calc θ * 2 ^ P.lp + π < θ * 2 ^ P.lp + 2 ^ P.lp := by omega
      _ = (θ + 1) * 2 ^ P.lp := by ring
      _ ≤ 2 ^ P.σ * 2 ^ P.lp := Nat.mul_le_mul_right _ hθ
  have e : i * 2 ^ (P.σ + P.lp) + (θ * 2 ^ P.lp + π) = (i * 2 ^ P.σ + θ) * 2 ^ P.lp + π := by
    rw [pow_add]
    ring
  refine ⟨(split_idx _ i _ hu).2, ?_, ?_⟩
  · unfold thOf
    rw [e, (split_idx P.lp _ π hπ).2, (split_idx P.σ i θ hθ).1]
  · unfold piOf
    rw [e, (split_idx P.lp _ π hπ).1]

/-- Under hθ, hπ: lev_0[(θ|π)] = Y_(θ,π), and 0 for an unused θ. -/
theorem tLev_zero (B : ℕ → ℕ → ℕ → E) (al : E) {θ π : ℕ} (hθ : θ < 2 ^ P.σ) (hπ : π < 2 ^ P.lp) :
    P.tLev B al 0 (θ * 2 ^ P.lp + π) = if θ < P.NT then P.Yt B al θ π else 0 := by
  unfold tLev
  rw [lvl_zero]
  have h : ∀ j, P.leafT B al (j * 2 ^ (P.σ + P.lp) + (θ * 2 ^ P.lp + π)) =
      if θ < P.NT then 1 + B j θ π * (al - 1 - P.tb θ j) else 0 := by
    intro j
    obtain ⟨h1, h2, h3⟩ := P.decode j hθ hπ
    unfold leafT vI vB vA
    rw [h1, h2, h3]
    split_ifs <;> simp
  simp only [h]
  split_ifs with hN
  · rfl
  · exact prod_eq_zero (mem_range.mpr (Nat.pos_of_ne_zero (by positivity) : 0 < 2 ^ P.r)) rfl

theorem ext_tLev (B : ℕ → ℕ → ℕ → E) (al : E) {l : ℕ} (h : l < P.r) (pt : ℕ → E) :
    ext (l + (P.σ + P.lp)) (P.tLev B al l) pt =
        ext (l + (P.σ + P.lp))
          (fun X => P.tLev B al (l + 1) X * P.tLev B al (l + 1) (X + 2 ^ (l + (P.σ + P.lp)))) pt :=
  ext_congr (fun X _ => lvl_step _ _ _ h X) pt

/-- The difference of sent and true tree products of the table side, at the index (θ|π). -/
def dY (B : ℕ → ℕ → ℕ → E) (al : E) (Yv : ℕ → ℕ → E) (u : ℕ) : E :=
  (if u / 2 ^ P.lp < P.NT then Yv (u / 2 ^ P.lp) (u % 2 ^ P.lp) else 0) - P.tLev B al 0 u

omit [Field E] in
private theorem pair_idx (u : ℕ) (hu : u < 2 ^ (P.σ + P.lp)) :
    u / 2 ^ P.lp < 2 ^ P.σ ∧
    u % 2 ^ P.lp < 2 ^ P.lp ∧
    u / 2 ^ P.lp * 2 ^ P.lp + u % 2 ^ P.lp = u := by
  have hpos : 0 < 2 ^ P.lp := Nat.pos_of_ne_zero (by positivity)
  refine ⟨?_, Nat.mod_lt _ hpos, Nat.div_add_mod' u _⟩
  rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add]
  exact hu

theorem dY_eq_zero_iff (hnt : P.NT ≤ 2 ^ P.σ) (B : ℕ → ℕ → ℕ → E) (al : E) (Yv : ℕ → ℕ → E) :
    (∀ u < 2 ^ (P.σ + P.lp), P.dY B al Yv u = 0) ↔
    ∀ θ < P.NT, ∀ π < 2 ^ P.lp, Yv θ π = P.Yt B al θ π := by
  constructor
  · intro h θ hθ π hπ
    have hθ' := lt_of_lt_of_le hθ hnt
    have hu : θ * 2 ^ P.lp + π < 2 ^ (P.σ + P.lp) := by
      rw [pow_add]
      calc θ * 2 ^ P.lp + π < θ * 2 ^ P.lp + 2 ^ P.lp := by omega
        _ = (θ + 1) * 2 ^ P.lp := by ring
        _ ≤ 2 ^ P.σ * 2 ^ P.lp := Nat.mul_le_mul_right _ hθ'
    have h1 := h _ hu
    unfold dY at h1
    rw [P.tLev_zero B al hθ' hπ, (split_idx P.lp θ π hπ).1, (split_idx P.lp θ π hπ).2,
      if_pos hθ, if_pos hθ] at h1
    exact sub_eq_zero.mp h1
  · intro h u hu
    obtain ⟨h1, h2, h3⟩ := P.pair_idx u hu
    unfold dY
    rw [← h3, P.tLev_zero B al h1 h2, h3]
    split_ifs with hN
    · exact sub_eq_zero.mpr (h _ hN _ h2)
    · exact sub_self 0

/-- The number of variables of the leaves of the table side. -/
def gT : ℕ := P.r + (P.σ + P.lp)

/-- After the subtraction of the indicator, the claim on TL is the start claim of the leaf layer. -/
theorem ext_leafT (B : ℕ → ℕ → ℕ → E) (al : E) (pt : ℕ → E) :
    ext P.gT (P.leafT B al) pt - ext P.gT P.vI pt =
        ext P.gT (fun X => P.vB B X * P.vA al X) pt := by
  unfold leafT
  rw [ext_add]
  ring

omit [Field E] in
private theorem triple_idx (x : ℕ) (hx : x < 2 ^ P.gT) :
    P.iOf x < 2 ^ P.r ∧ P.thOf x < 2 ^ P.σ ∧ P.piOf x < 2 ^ P.lp := by
  have h1 : 0 < 2 ^ P.lp := Nat.pos_of_ne_zero (by positivity)
  have h2 : 0 < 2 ^ P.σ := Nat.pos_of_ne_zero (by positivity)
  have h3 : 0 < 2 ^ (P.σ + P.lp) := Nat.pos_of_ne_zero (by positivity)
  refine ⟨?_, Nat.mod_lt _ h2, Nat.mod_lt _ h1⟩
  unfold iOf
  rw [Nat.div_lt_iff_lt_mul h3, ← pow_add]
  exact hx

/-- Under hnt: B (B - 1) = 0 as a vector says that the B[i, θ, π] are bits. -/
theorem bits_iff (hnt : P.NT ≤ 2 ^ P.σ) (B : ℕ → ℕ → ℕ → E) :
    (∀ x < 2 ^ P.gT, P.vB B x * (P.vB B x - 1) = 0) ↔ P.Bits B := by
  constructor
  · intro h i hi θ hθ π hπ
    have hθ' := lt_of_lt_of_le hθ hnt
    obtain ⟨h1, h2, h3⟩ := P.decode i hθ' hπ
    have hx : i * 2 ^ (P.σ + P.lp) + (θ * 2 ^ P.lp + π) < 2 ^ P.gT := by
      have hu : θ * 2 ^ P.lp + π < 2 ^ (P.σ + P.lp) := by
        rw [pow_add]
        calc θ * 2 ^ P.lp + π < θ * 2 ^ P.lp + 2 ^ P.lp := by omega
          _ = (θ + 1) * 2 ^ P.lp := by ring
          _ ≤ 2 ^ P.σ * 2 ^ P.lp := Nat.mul_le_mul_right _ hθ'
      unfold gT
      calc
        i * 2 ^ (P.σ + P.lp) + (θ * 2 ^ P.lp + π) < i * 2 ^ (P.σ + P.lp) + 2 ^ (P.σ + P.lp) := by
          omega
        _ = (i + 1) * 2 ^ (P.σ + P.lp) := by ring
        _ ≤ 2 ^ P.r * 2 ^ (P.σ + P.lp) := Nat.mul_le_mul_right _ hi
        _ = 2 ^ (P.r + (P.σ + P.lp)) := (pow_add _ _ _).symm
    have h4 := h _ hx
    unfold vB at h4
    rwa [h1, h2, h3, if_pos hθ] at h4
  · intro h x hx
    obtain ⟨h1, _, h3⟩ := P.triple_idx x hx
    unfold vB
    split_ifs with hN
    · exact h _ h1 _ hN _ h3
    · simp

theorem ext_vB_sub_one (B : ℕ → ℕ → ℕ → E) (pt : ℕ → E) :
    ext P.gT (fun X => P.vB B X - 1) pt = ext P.gT (P.vB B) pt - 1 := by
  rw [ext_sub, ext_const]

/-! ### The degree check -/

/-- d[θ] = ∑_i mult_θ(i) - nblk + ϕ_θ, and 0 for an unused θ. -/
def dDeg (B : ℕ → ℕ → ℕ → E) (θ : ℕ) : E :=
  if θ < P.NT then
    ∑ i ∈ range (2 ^ P.r), ∑ π ∈ range (2 ^ P.lp), (2 : E) ^ π * B i θ π -
      ((2 ^ P.D - P.φ θ : ℕ) : E)
  else 0

theorem dDeg_eq_zero_iff (hnt : P.NT ≤ 2 ^ P.σ) (B : ℕ → ℕ → ℕ → E) :
    (∀ θ < 2 ^ P.σ, P.dDeg B θ = 0) ↔ P.DegE B := by
  constructor
  · intro h θ hθ
    have h1 := h θ (lt_of_lt_of_le hθ hnt)
    unfold dDeg at h1
    rw [if_pos hθ] at h1
    exact sub_eq_zero.mp h1
  · intro h θ _
    unfold dDeg
    split_ifs with hN
    · exact sub_eq_zero.mpr (h θ hN)
    · rfl

end LkPar

/-! ## 5. The root test -/

namespace LkPar

variable {E : Type} [Field E] (P : LkPar E)

/-- The number of the highest plane, that is bit position π of a multiplicity (31 for lp = 5). -/
def Pm : ℕ := 2 ^ P.lp - 1

omit [Field E] in
theorem Pm_succ : P.Pm + 1 = 2 ^ P.lp := Nat.sub_add_cancel (Nat.one_le_two_pow)

/-- An array over the trees, 0 for an unused θ. -/
def msk {M : Type} [Zero M] (A : ℕ → M) (θ : ℕ) : M := if θ < P.NT then A θ else 0

/-- U_π, where the highest one is not sent: U_Pm = Y_(·,Pm). -/
def uArr {M : Type} (Y : ℕ → ℕ → M) (U : ℕ → ℕ → M) (π θ : ℕ) : M :=
  if π = P.Pm then Y θ P.Pm else U π θ

/-- d⋆ = Z - (α - τ⁰)^ϕ U_0. -/
def dStar (al : E) (Zv : ℕ → E) (Yv Uv : ℕ → ℕ → E) : ℕ → E :=
  P.msk fun θ => Zv θ - (al - P.tb θ (P.t0 θ)) ^ P.φ θ * P.uArr Yv Uv 0 θ
/-- d_π = V_π - U_(π+1)². -/
def dV (Yv Uv Vv : ℕ → ℕ → E) (π : ℕ) : ℕ → E := P.msk fun θ => Vv π θ - P.uArr Yv Uv (π + 1) θ ^ 2
/-- d'_π = U_π - V_π Y_(·,π). -/
def dU (Yv Uv Vv : ℕ → ℕ → E) (π : ℕ) : ℕ → E := P.msk fun θ => P.uArr Yv Uv π θ - Vv π θ * Yv θ π

/-- The 2 Pm functions d_π, d'_π in one list: number j < Pm is d_j, number Pm + j is d'_j. -/
def dPair (Yv Uv Vv : ℕ → ℕ → E) (j : ℕ) : ℕ → E :=
  if j < P.Pm then P.dV Yv Uv Vv j else P.dU Yv Uv Vv (j - P.Pm)

/-- The family of 2 Pm + 1 functions that share the point ϱ' (63 for lp = 5): d⋆ first. -/
def dFam (al : E) (Zv : ℕ → E) (Yv Uv Vv : ℕ → ℕ → E) (m : Fin (2 * P.Pm + 1)) : ℕ → E :=
  if m.val = 0 then P.dStar al Zv Yv Uv else P.dPair Yv Uv Vv (m.val - 1)

/-- Under hnt: if all functions of the family vanish, Ident holds for the sent tree products. -/
theorem ident_of_dFam (hnt : P.NT ≤ 2 ^ P.σ) {al : E} {Zv : ℕ → E} {Yv Uv Vv : ℕ → ℕ → E}
    (h : ∀ m, ∀ θ < 2 ^ P.σ, P.dFam al Zv Yv Uv Vv m θ = 0) : P.Ident al Zv Yv := by
  intro θ hθ
  have hθ' := lt_of_lt_of_le hθ hnt
  have h0 : Zv θ = (al - P.tb θ (P.t0 θ)) ^ P.φ θ * P.uArr Yv Uv 0 θ := by
    have h1 := h ⟨0, by omega⟩ θ hθ'
    simp only [dFam, if_true, dStar, msk, if_pos hθ] at h1
    exact sub_eq_zero.mp h1
  have hV : ∀ π < P.Pm, Vv π θ = P.uArr Yv Uv (π + 1) θ ^ 2 := by
    intro π hπ
    have h1 := h ⟨π + 1, by omega⟩ θ hθ'
    simp only [dFam, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel,
      dPair, if_pos hπ, dV, msk, if_pos hθ] at h1
    exact sub_eq_zero.mp h1
  have hU : ∀ π < P.Pm, P.uArr Yv Uv π θ = Vv π θ * Yv θ π := by
    intro π hπ
    have h1 := h ⟨P.Pm + π + 1, by omega⟩ θ hθ'
    have e1 : ¬ P.Pm + π < P.Pm := by omega
    have e2 : P.Pm + π - P.Pm = π := by omega
    simp only [dFam, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel,
      dPair, if_neg e1, e2, dU, msk, if_pos hθ] at h1
    exact sub_eq_zero.mp h1
  have hc : P.uArr Yv Uv 0 θ = ∏ π ∈ range (P.Pm + 1), Yv θ π ^ 2 ^ π :=
    Alg.Lookup.chain_of_rel P.Pm
      (fun π => Yv θ π) (fun π => P.uArr Yv Uv π θ) (fun π => Vv π θ) (by simp [uArr]) hV hU
  rw [h0, hc, P.Pm_succ]

/-- The tuple c of coefficients (ξ, ξ') is bad at the point ϱ': some ~d_π(ϱ') or ~d'_π(ϱ') is not 0,
and their combination vanishes. -/
def BadXi (Yv Uv Vv : ℕ → ℕ → E) (pt : ℕ → E) (c : Fin (2 * P.Pm) → E) : Prop :=
  (fun j : Fin (2 * P.Pm) => ext P.σ (P.dPair Yv Uv Vv j) pt) ≠ 0 ∧
  ∑ j, c j * ext P.σ (P.dPair Yv Uv Vv j) pt = 0

/-- A bound on the number of bad values of (ξ, ξ'), for a field of q elements: q^(2 Pm - 1) of q^(2
Pm). For Pm = 0 (multiplicities of one bit) the message is empty and no value is bad. -/
def eXi (q : ℕ) : ℕ := if P.Pm = 0 then 0 else q ^ (2 * P.Pm - 1)

theorem cnt_badXi_le [Fintype E] (Yv Uv Vv : ℕ → ℕ → E) (pt : ℕ → E) :
    cnt (P.BadXi Yv Uv Vv pt) ≤ P.eXi (Fintype.card E) := by
  unfold eXi
  by_cases h0 : P.Pm = 0
  · rw [if_pos h0, cnt_false fun c hc => hc.1 (funext fun j => absurd j.2 (by omega))]
  rw [if_neg h0]
  by_cases h : (fun j : Fin (2 * P.Pm) => ext P.σ (P.dPair Yv Uv Vv j) pt) ≠ 0
  · have h1 := Alg.count_affine_form_le_pow
      (0 : E) (fun j : Fin (2 * P.Pm) => ext P.σ (P.dPair Yv Uv Vv j) pt) (Or.inr h)
    rw [Fintype.card_fin] at h1
    refine le_trans (cnt_mono fun c hc => ?_) h1
    rw [zero_add]
    exact hc.2
  · rw [cnt_false fun c hc => h hc.1]
    exact Nat.zero_le _

/-- The extensions of the arrays at a point w of σ coordinates. -/
def eV (Vv : ℕ → ℕ → E) (π : ℕ) (w : ℕ → E) : E := ext P.σ (P.msk (Vv π)) w
def eU (Yv Uv : ℕ → ℕ → E) (π : ℕ) (w : ℕ → E) : E := ext P.σ (P.msk (P.uArr Yv Uv π)) w
def eY (Yv : ℕ → ℕ → E) (π : ℕ) (w : ℕ → E) : E := ext P.σ (P.msk fun θ => Yv θ π) w

/-- The polynomial of the sumcheck of the root test. -/
def rootPhi (Yv Uv Vv : ℕ → ℕ → E) (c : ℕ → E) (w : ℕ → E) : E :=
  ∑ π ∈ range P.Pm, (c π * (P.eV Vv π w - P.eU Yv Uv (π + 1) w * P.eU Yv Uv (π + 1) w)
    + c (P.Pm + π) * (P.eU Yv Uv π w - P.eV Vv π w * P.eY Yv π w))

/-- The honest arrays: U_π by squaring and multiplying from the highest plane down, V_π =
U_(π+1)². -/
def hU (Yv : ℕ → ℕ → E) (π θ : ℕ) : E := Alg.Lookup.chainFrom (fun π => Yv θ π) (P.Pm - π) π
def hV (Yv : ℕ → ℕ → E) (π θ : ℕ) : E := P.hU Yv (π + 1) θ ^ 2

theorem uArr_hU (Yv : ℕ → ℕ → E) {π : ℕ} (θ : ℕ) : P.uArr Yv (P.hU Yv) π θ = P.hU Yv π θ := by
  unfold uArr
  split_ifs with h
  · subst h
    simp [hU, Alg.Lookup.chainFrom]
  · rfl

/-- With the honest arrays all functions of the family vanish, if Ident holds for Z, Y. -/
theorem dFam_honest {al : E} {Zv : ℕ → E} {Yv : ℕ → ℕ → E} (hi : P.Ident al Zv Yv)
    (m : Fin (2 * P.Pm + 1)) (θ : ℕ) :
    P.dFam al Zv Yv (P.hU Yv) (P.hV Yv) m θ = 0 := by
  unfold dFam
  split_ifs with h0
  · unfold dStar msk
    split_ifs with hθ
    · beta_reduce
      rw [P.uArr_hU, hi θ hθ]
      unfold hU
      rw [Alg.Lookup.chainFrom_eq_prod, Nat.sub_zero, P.Pm_succ]
      simp
    · rfl
  · unfold dPair
    split_ifs with h1
    · unfold dV msk
      split_ifs
      · beta_reduce
        rw [P.uArr_hU]
        exact sub_self _
      · rfl
    · unfold dU msk
      split_ifs
      · have hπ : m.val - 1 - P.Pm < P.Pm := by have := m.2; omega
        beta_reduce
        rw [P.uArr_hU]
        unfold hV hU
        have e : P.Pm - (m.val - 1 - P.Pm) = (P.Pm - (m.val - 1 - P.Pm + 1)) + 1 := by omega
        rw [e, Alg.Lookup.chainFrom]
        exact sub_self _
      · rfl

end LkPar

/-! ## 6. The sumcheck of the root test -/

section CubeSum

variable {E : Type} [Field E]

/-- The variables 0, .., g - 1, in this order. -/
def lkVars (g : ℕ) : List ℕ := (List.finRange g).map fun t : Fin g => (t : ℕ)

/-- The vertex number X of the hypercube of g variables, with coordinates indexed by ℕ. -/
def cubePt (g X : ℕ) : ℕ → E := nat (Alg.corner (Alg.bits g X) : Fin g → E)

private theorem ext_eq_mleN' (g : ℕ) (f z : ℕ → E) :
    ext g f z = Alg.mleN f fun t : Fin g => z t := by
  unfold ext Alg.mleN
  refine sum_congr rfl fun X _ => ?_
  rw [eqN_eq]
  simp only [Nat.zero_add]

theorem ext_congr_point {g : ℕ} {z z' : ℕ → E} (h : ∀ t < g, z t = z' t) (f : ℕ → E) :
    ext g f z = ext g f z' := by
  rw [ext_eq_mleN', ext_eq_mleN',
    show (fun t : Fin g => z t) = fun t : Fin g => z' t from funext fun t => h t t.2]

/-- The extension agrees with the vector on the hypercube. -/
theorem ext_cubePt (g : ℕ) (f : ℕ → E) {X : ℕ} (hX : X < 2 ^ g) : ext g f (cubePt g X) = f X := by
  rw [ext_eq_mleN', Alg.mleN_eq_mle]
  have h : (fun t : Fin g => (cubePt g X : ℕ → E) t) = Alg.corner (Alg.bits g X) := by
    funext t
    simp [cubePt, nat, t.2]
  rw [h, Alg.mle_corner, Alg.num_bits hX]

/-- The start claim of a sumcheck with an equality factor, for a function Φ of the first g
coordinates: summing Φ out over the g variables with the weights of eq(ϱ, ·) gives the extension at
ϱ of the values of Φ on the hypercube. -/
theorem sumOutL_eqW_lkVars (g : ℕ) (ϱ z : ℕ → E) (Φ : (ℕ → E) → E)
    (hΦ : ∀ w w' : ℕ → E, (∀ t < g, w t = w' t) → Φ w = Φ w') :
    Alg.sumOutL (Alg.eqW ϱ) (lkVars g) Φ z = ext g (fun X => Φ (cubePt g X)) ϱ := by
  have hfun : Φ = fun y : ℕ → E => (fun v : Fin g → E => Φ (nat v)) fun t : Fin g => y t := by
    funext y
    exact hΦ _ _ fun t ht => by simp [nat, ht]
  have h1 := Alg.sumOutL_comp (fun t : Fin g => (t : ℕ)) Fin.val_injective (Alg.eqW ϱ)
    (fun v : Fin g → E => Φ (nat v)) (List.finRange g) z
  have h2 := Alg.sumOutL_eq_mle (fun t : Fin g => ϱ t) (List.finRange g) (List.nodup_finRange g)
    (List.mem_finRange) (fun v : Fin g → E => Φ (nat v)) (fun t : Fin g => z t)
  have e : Alg.sumOutL (Alg.eqW ϱ) (lkVars g) Φ z =
      Alg.mle (fun b => Φ (nat (Alg.corner b : Fin g → E))) fun t : Fin g => ϱ t := by
    unfold lkVars
    conv_lhs => rw [hfun]
    exact h1.trans h2
  rw [e, ext_eq_mleN', Alg.mleN_eq_mle]
  simp only [cubePt, Alg.bits_num]

theorem degLE_ext' (g : ℕ) (f : ℕ → E) : Alg.DegLE (fun _ => 1) (ext g f) := by
  have h1 : Alg.DegLE (fun _ => 1) (fun x : Fin g → E => Alg.mleN f x) := by
    simp only [Alg.mleN_eq_mle]
    exact Alg.DegLE.mle _
  have h2 := h1.comp (fun t : Fin g => (t : ℕ)) Fin.val_injective (fun _ => 1) fun _ => le_rfl
  rwa [show (fun z : ℕ → E => Alg.mleN f fun t : Fin g => z t) = ext g f
      from funext fun z => (ext_eq_mleN' g f z).symm] at h2

end CubeSum

namespace LkPar

variable {E : Type} [Field E] (P : LkPar E)

theorem degLE_rootPhi (Yv Uv Vv : ℕ → ℕ → E) (c : ℕ → E) :
    Alg.DegLE (fun _ => 2) (P.rootPhi Yv Uv Vv c) := by
  have one : ∀ A : ℕ → E, Alg.DegLE (fun _ => 2) (ext P.σ A) := fun A =>
    (degLE_ext' P.σ A).mono fun _ => by norm_num
  have two : ∀ A A' : ℕ → E,
      Alg.DegLE (fun _ => 2) (fun w => ext P.σ A w * ext P.σ A' w) := fun A A' =>
    (degLE_ext' P.σ A).mul (degLE_ext' P.σ A')
  show Alg.DegLE (fun _ => 2) (fun w =>
    ∑ π ∈ range P.Pm, (c π * (P.eV Vv π w - P.eU Yv Uv (π + 1) w * P.eU Yv Uv (π + 1) w) +
      c (P.Pm + π) * (P.eU Yv Uv π w - P.eV Vv π w * P.eY Yv π w)))
  refine Alg.DegLE.sum _ fun π _ => ?_
  exact (((one _).sub (two _ _)).const_mul _).add (((one _).sub (two _ _)).const_mul _)

/-- On the hypercube the polynomial of the root test is the combination of the functions d_π,
d'_π. -/
theorem rootPhi_cubePt (Yv Uv Vv : ℕ → ℕ → E) (c : ℕ → E) {θ : ℕ} (hθ : θ < 2 ^ P.σ) :
    P.rootPhi Yv Uv Vv c (cubePt P.σ θ) =
      ∑ π ∈ range P.Pm, (c π * P.dV Yv Uv Vv π θ + c (P.Pm + π) * P.dU Yv Uv Vv π θ) := by
  unfold rootPhi eV eU eY
  refine sum_congr rfl fun π _ => ?_
  simp only [ext_cubePt _ _ hθ]
  unfold dV dU msk
  split_ifs <;> ring

/-- The start claim of the sumcheck of the root test: ∑_θ eq(ϱ', θ) Φ(θ) = ∑_j c_j ~d_j(ϱ') over
the 2 Pm functions d_π, d'_π. -/
theorem sumOutL_rootPhi (Yv Uv Vv : ℕ → ℕ → E) (c : ℕ → E) (ϱ z : ℕ → E) :
    Alg.sumOutL (Alg.eqW ϱ) (lkVars P.σ) (P.rootPhi Yv Uv Vv c) z =
      ∑ j ∈ range (2 * P.Pm), c j * ext P.σ (P.dPair Yv Uv Vv j) ϱ := by
  rw [sumOutL_eqW_lkVars P.σ ϱ z (P.rootPhi Yv Uv Vv c) fun w w' h => by
    unfold rootPhi eV eU eY
    simp only [ext_congr_point h]]
  rw [ext_congr (fun θ hθ => P.rootPhi_cubePt Yv Uv Vv c hθ), ext_sum, two_mul,
    sum_range_add, ← sum_add_distrib]
  refine sum_congr rfl fun π hπ => ?_
  have h1 : P.dPair Yv Uv Vv π = P.dV Yv Uv Vv π := by
    unfold dPair
    rw [if_pos (mem_range.mp hπ)]
  have h2 : P.dPair Yv Uv Vv (P.Pm + π) = P.dU Yv Uv Vv π := by
    unfold dPair
    rw [if_neg (by omega), Nat.add_sub_cancel_left]
  rw [h1, h2, ext_add, ext_smul, ext_smul]

/-- What the REL (Blocks/Form.lean) of the root test says: the form at the end of its sumcheck, less
the terms that are linear in V_π and U_π, is the sum of the products under the coefficients -ξ_π,
-ξ'_π. -/
theorem rootPhi_eq_iff (Yv Uv Vv : ℕ → ℕ → E) (c : ℕ → E) (w : ℕ → E) (v : E) :
    v = P.rootPhi Yv Uv Vv c w ↔
    v - ∑ π ∈ range P.Pm, (c π * P.eV Vv π w + c (P.Pm + π) * P.eU Yv Uv π w) =
      ∑ π ∈ range P.Pm, (-c π * P.eU Yv Uv (π + 1) w * P.eU Yv Uv (π + 1) w +
        -c (P.Pm + π) * P.eV Vv π w * P.eY Yv π w) := by
  have h : P.rootPhi Yv Uv Vv c w =
      ∑ π ∈ range P.Pm, (c π * P.eV Vv π w + c (P.Pm + π) * P.eU Yv Uv π w) +
        ∑ π ∈ range P.Pm, (-c π * P.eU Yv Uv (π + 1) w * P.eU Yv Uv (π + 1) w +
          -c (P.Pm + π) * P.eV Vv π w * P.eY Yv π w) := by
    unfold rootPhi
    rw [← sum_add_distrib]
    exact sum_congr rfl fun π _ => by ring
  rw [h]
  constructor
  · intro hv
    rw [hv]
    ring
  · intro hv
    rw [← hv]
    ring

/-- For a full forest (every θ is used) the vector of the end claim is α minus the keys. -/
theorem ext_leafK_full (hfull : P.NT = 2 ^ P.σ) (key : ℕ → ℕ → E) (al : E) (z : ℕ → E) :
    ext (P.D + P.σ) (P.leafK key al) z =
        al - ext (P.D + P.σ) (fun x => key (x % 2 ^ P.σ) (x / 2 ^ P.σ)) z := by
  have h : ∀ x, P.leafK key al x = al - key (x % 2 ^ P.σ) (x / 2 ^ P.σ) := by
    intro x
    unfold leafK
    rw [if_pos]
    rw [hfull]
    exact Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity))
  rw [ext_congr (fun x _ => h x), ext_sub, ext_const]

end LkPar

/-! ## 7. The honest multiplicities -/

namespace LkPar

variable {E : Type} [Field E] (P : LkPar E)

/-- The true multiplicity of the table index t in tree θ: the number of keys outside padding
positions that are counted at t. -/
def trueMult (pad : ℕ → ℕ → Bool) (row : ℕ → ℕ → ℕ) (θ t : ℕ) : ℕ :=
  ((range (2 ^ P.D)).filter fun i => pad θ i = false ∧ row θ i = t).card

/-- The honest B. pad marks the padding positions, where the key is the padding value; every other
key i of tree θ is the table value number row θ i; ϕ_θ is the number of padding positions; B holds
the bits of the true multiplicities. -/
structure HonB (key : ℕ → ℕ → E) (B : ℕ → ℕ → ℕ → E) (pad : ℕ → ℕ → Bool) (row : ℕ → ℕ → ℕ) :
    Prop where
  padKey : ∀ θ < P.NT, ∀ i < 2 ^ P.D, pad θ i = true → key θ i = P.tb θ (P.t0 θ)
  rowKey : ∀ θ < P.NT,
    ∀ i < 2 ^ P.D, pad θ i = false → row θ i < 2 ^ P.r ∧ key θ i = P.tb θ (row θ i)
  phi : ∀ θ < P.NT, P.φ θ = ((range (2 ^ P.D)).filter fun i => pad θ i = true).card
  bits : ∀ t < 2 ^ P.r,
    ∀ θ < P.NT, ∀ π < 2 ^ P.lp, B t θ π = if (P.trueMult pad row θ t).testBit π then 1 else 0

variable {P} {key : ℕ → ℕ → E} {B : ℕ → ℕ → ℕ → E} {pad : ℕ → ℕ → Bool} {row : ℕ → ℕ → ℕ}

theorem HonB.isBits (h : P.HonB key B pad row) : P.Bits B := by
  intro i hi θ hθ π hπ
  rw [h.bits i hi θ hθ π hπ]
  split_ifs <;> simp

omit [Field E] in
theorem trueMult_lt (hD : P.D < 2 ^ P.lp) (θ t : ℕ) : P.trueMult pad row θ t < 2 ^ 2 ^ P.lp := by
  refine lt_of_le_of_lt ((card_filter_le _ _).trans (le_of_eq (card_range _))) ?_
  exact Nat.pow_lt_pow_right (by norm_num) hD

omit [Field E] in
/-- If `row` is below 2^r outside padding positions, the multiplicities add up to the number of keys
outside padding positions. -/
theorem sum_trueMult {θ : ℕ} (hrow : ∀ i < 2 ^ P.D, pad θ i = false → row θ i < 2 ^ P.r) :
    ∑ t ∈ range (2 ^ P.r), P.trueMult pad row θ t =
      ((range (2 ^ P.D)).filter fun i => pad θ i = false).card := by
  unfold trueMult
  have h := card_eq_sum_card_fiberwise (s := (range (2 ^ P.D)).filter fun i => pad θ i = false)
    (t := range (2 ^ P.r)) (f := row θ) (fun i hi =>
      mem_coe.mpr
        (mem_range.mpr
          (hrow i (mem_range.mp (mem_filter.mp (mem_coe.mp hi)).1)
            (mem_filter.mp (mem_coe.mp hi)).2)))
  rw [h]
  refine sum_congr rfl fun t _ => ?_
  rw [filter_filter]

theorem HonB.degE (h : P.HonB key B pad row) (hD : P.D < 2 ^ P.lp) : P.DegE B := by
  intro θ hθ
  have h1 : ∀ t ∈ range (2 ^ P.r),
      ∑ π ∈ range (2 ^ P.lp), (2 : E) ^ π * B t θ π = ((P.trueMult pad row θ t : ℕ) : E) := by
    intro t ht
    have h2 : P.trueMult pad row θ t =
        ∑ π ∈ range (2 ^ P.lp), if (P.trueMult pad row θ t).testBit π then 2 ^ π else 0 := by
      rw [Alg.Lookup.sum_testBit, Nat.mod_eq_of_lt (trueMult_lt hD θ t)]
    conv_rhs => rw [h2]
    push_cast
    refine sum_congr rfl fun π hπ => ?_
    rw [h.bits t (mem_range.mp ht) θ hθ π (mem_range.mp hπ)]
    split_ifs <;> simp
  rw [sum_congr rfl h1, ← Nat.cast_sum,
    sum_trueMult (fun i hi hp => (h.rowKey θ hθ i hi hp).1), h.phi θ hθ]
  congr 1
  have h3 := card_filter_add_card_filter_not (s := range (2 ^ P.D)) (fun i => pad θ i = true)
  rw [card_range] at h3
  have h4 : ((range (2 ^ P.D)).filter fun i => ¬ pad θ i = true) =
      (range (2 ^ P.D)).filter fun i => pad θ i = false :=
    filter_congr fun i _ => by simp
  rw [h4] at h3
  omega

/-- Under hD, Ident holds for the true products at every α, for the honest B. -/
theorem HonB.ident (h : P.HonB key B pad row) (hD : P.D < 2 ^ P.lp) (al : E) :
    P.Ident al (P.Zt key al) (P.Yt B al) := by
  intro θ hθ
  -- the key side, sorted by padding and by table index
  have hZ : P.Zt key al θ =
      (al - P.tb θ (P.t0 θ)) ^ P.φ θ *
        ∏ t ∈ range (2 ^ P.r), (al - P.tb θ t) ^ P.trueMult pad row θ t := by
    unfold Zt
    rw [← prod_filter_mul_prod_filter_not (range (2 ^ P.D)) (fun i => pad θ i = true)]
    congr 1
    · rw [prod_congr rfl fun i hi => by
        rw [h.padKey θ hθ i (mem_range.mp (mem_filter.mp hi).1) (mem_filter.mp hi).2],
          prod_const, h.phi θ hθ]
    · have h4 : ((range (2 ^ P.D)).filter fun i => ¬ pad θ i = true) =
          (range (2 ^ P.D)).filter fun i => pad θ i = false :=
        filter_congr fun i _ => by simp
      rw [h4,
        ← prod_fiberwise_of_maps_to (s := (range (2 ^ P.D)).filter fun i => pad θ i = false)
          (t := range (2 ^ P.r)) (g := row θ) fun i hi =>
            mem_range.mpr
              (h.rowKey θ hθ i (mem_range.mp (mem_filter.mp hi).1) (mem_filter.mp hi).2).1]
      refine prod_congr rfl fun t _ => ?_
      rw [prod_congr rfl fun i hi => by
        rw [(h.rowKey θ hθ i (mem_range.mp (mem_filter.mp (mem_filter.mp hi).1).1)
          (mem_filter.mp (mem_filter.mp hi).1).2).2,
          (mem_filter.mp hi).2], prod_const, filter_filter]
      rfl
  -- the table side, by planes
  have hY := Alg.Lookup.planes_eq (2 ^ P.lp)
    (fun (t : Fin (2 ^ P.r)) j => (P.trueMult pad row θ t).testBit j)
    (fun t : Fin (2 ^ P.r) => P.tb θ t) al
  rw [hZ]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (fun t => (al - P.tb θ t) ^ P.trueMult pad row θ t)]
  have hm : ∀ t : Fin (2 ^ P.r),
      Alg.Lookup.mult (2 ^ P.lp)
          (fun (t : Fin (2 ^ P.r)) j => (P.trueMult pad row θ t).testBit j) t =
        P.trueMult pad row θ t := fun t =>
    Alg.Lookup.mult_testBit (2 ^ P.lp)
      (fun t : Fin (2 ^ P.r) => P.trueMult pad row θ t) t (trueMult_lt hD θ t)
  simp only [hm] at hY
  rw [← hY]
  refine prod_congr rfl fun π hπ => ?_
  unfold Yt
  rw [← Fin.prod_univ_eq_prod_range (fun t => 1 + B t θ π * (al - 1 - P.tb θ t))]
  congr 1
  exact prod_congr rfl fun t _ => by rw [h.bits t t.2 θ hθ π (mem_range.mp hπ)]

end LkPar

/-! ## 8. The first table index at which a key occurs -/

namespace LkPar

variable {E : Type} [Field E] [DecidableEq E] (P : LkPar E)

/-- The first index of the table of tree θ at which key number i of that tree occurs; 0 if there is
none. -/
def firstRow (key : ℕ → ℕ → E) (θ i : ℕ) : ℕ :=
  ((List.range (2 ^ P.r)).find? fun t => decide (key θ i = P.tb θ t)).getD 0

omit [Field E] in
theorem firstRow_spec {key : ℕ → ℕ → E} {θ i : ℕ} (h : ∃ t < 2 ^ P.r, key θ i = P.tb θ t) :
    P.firstRow key θ i < 2 ^ P.r ∧ key θ i = P.tb θ (P.firstRow key θ i) := by
  unfold firstRow
  cases hf : (List.range (2 ^ P.r)).find? fun t => decide (key θ i = P.tb θ t) with
  | none =>
    obtain ⟨t, ht, he⟩ := h
    have h1 := List.find?_eq_none.mp hf t (List.mem_range.mpr ht)
    exact absurd he (by simpa using h1)
  | some t =>
    have h1 := List.find?_some hf
    have h2 := List.mem_of_find?_eq_some hf
    exact ⟨List.mem_range.mp h2, by simpa using h1⟩



end LkPar

end Blocks
