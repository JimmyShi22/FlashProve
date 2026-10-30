-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/RngForest.lean: a lookup plan as one forest of the lookup argument; no protocol.

The lookup argument of Blocks/LookupRel.lean treats a forest: NT trees of keys, each tree with its
own table. All calls f and all classes b of a plan (Blocks/RngPlan.lean) are taken as the trees θ =
f 2^B + b of one forest.

 * `Plan.lk`: the parameters of the forest.
 * `Plan.keyT`: its keys: key number i of the tree (f, b) is key number i 2^B + b of call f.
 * `Plan.inTable_iff`: every key of the forest is in its table if and only if every key of every
   call is in its table (for B ≤ D and d_f ≤ r).
 * `Plan.lk_wf`: the sizes fit (`LkPar.WF`), for a valid plan with nc ≤ 2^lf and 2^(r + 2^lp) < p.
 * `Plan.ext_leafK`: the vector with which the key side of the lookup argument ends, evaluated at a
   point z, is a public number minus an index form (for k ≤ D, B ≤ D, nc ≤ 2^lf): α ∑_f eq(z_f, f) -
   ∑_f eq(z_f, f) ~o_f(z_row) - ⟨G(z) ⊗ eq(ψ(z), ·), W⟩ with G(z) = ∑_f eq(z_f, f) g_f(z_row).
 * `Plan.rowT`, `Plan.bitT`, `Plan.honB`: the honest vector bit: the bits of the multiplicities,
   computed by search and without choice. For B ≤ D, d_f ≤ r and a matrix all of whose keys are in
   their tables it is the honest B of the lookup argument (`LkPar.HonB`; for bits, degrees and
   `LkPar.Ident` see `LkPar.HonB.isBits`, `degE`, `ident`).

Choices made here.
 (1) One forest, one α and one descent on each side for all calls, where the implementation
     treats the nc calls in turn (Blocks/RngCallsPlan.lean). So there is one output index claim, and
     no merging of claims is needed after it.
 (2) Padding keys are counted like all other keys (ϕ = 0): a padding key is 0, which is in every
     table, and by (Pl2) (`Plan.Valid.pl2'`, Blocks/RngPlan.lean) a multiplicity has room for all
     2^(D-B) keys of a tree.
 (3) All tables have 2^r entries, r ≥ d_f; a shorter table is repeated.
Notation: the fields of a plan (`Plan`, Blocks/RngPlan.lean), natural numbers unless a type is
given: `h`, `k`: the matrix W has h rows and 2^k columns; `nc`: number of calls; `D`, `B`: the key
hypercube has D coordinates, the last B of which are the class; `lp`: a multiplicity has 2^lp bits;
`d : ℕ → ℕ`, `off : ℕ → ℕ → F`, `Γ : ℕ → ℕ → ℕ → F`: call f has the table {0, .., 2^(d f) - 1},
offsets off f and the matrix Γ f. `p`: ℕ; in `Plan.Valid p WFp` (Blocks/RngPlan.lean), the
characteristic. `lf`, `r`: lf is the number of coordinates for the number of a call, r the number of
coordinates of a table (`Plan.lk`). z: a point of the forest; z_f: its coordinates of f; z_row,
ψ(z): the row part (the first D - k coordinates) and the column part of `Plan.zKey`, the key's
coordinates in z; ~o_f: `Plan.offExt`; g_f(a) = ∑_i' eq(a, i') Γ_f[i'] (`Plan.gOf`; both:
Blocks/RngPlan.lean). α: `al : E`; in Blocks/LookupRel.lean, the challenge of the lookup argument.

Terms: lean/GLOSSARY.md.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Blocks.RngPlan
import Blocks.LookupRel

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks.Rng

open Finset

section Tools

variable {E : Type} [Field E]

/-- `eqN` depends only on the coordinates that it reads. -/
theorem eqN_shift (m off off' : ℕ) {a a' : ℕ → E}
    (h : ∀ t, t < m → a (off + t) = a' (off' + t)) (x : ℕ) :
    eqN m off a x = eqN m off' a' x := by
  unfold eqN
  exact prod_congr rfl fun t ht => by rw [h t (mem_range.mp ht)]

/-- The point z without its coordinates Dt, .., Dt + lf - 1. -/
def skip (Dt lf : ℕ) (z : ℕ → E) : ℕ → E := fun t => if t < Dt then z t else z (t + lf)

theorem split_idx (s j u : ℕ) (hu : u < 2 ^ s) :
    (j * 2 ^ s + u) % 2 ^ s = u ∧ (j * 2 ^ s + u) / 2 ^ s = j := by
  have hpos : 0 < 2 ^ s := by positivity
  constructor
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu]
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hu, Nat.zero_add]

/-- The middle coordinates taken out. An index of Dt + lf + B bits is (i | f | b). The extension at
z is the eq(z_f, f)-combination of the extensions, at z without z_f, of the vectors on the indices
(i | b). -/
theorem ext_forest (Dt lf B : ℕ) (v : ℕ → E) (z : ℕ → E) :
    ext (Dt + (lf + B)) v z = ∑ f ∈ range (2 ^ lf), eqN lf Dt z f *
      ext (Dt + B) (fun idx => v (idx / 2 ^ B * 2 ^ (lf + B) + (f * 2 ^ B + idx % 2 ^ B)))
          (skip Dt lf z) := by
  unfold ext
  have hL : ∑ X ∈ range (2 ^ (Dt + (lf + B))), eqN (Dt + (lf + B)) 0 z X * v X =
      ∑ f ∈ range (2 ^ lf), ∑ i ∈ range (2 ^ Dt), ∑ b ∈ range (2 ^ B),
        eqN (Dt + (lf + B)) 0 z (i * 2 ^ (lf + B) + (f * 2 ^ B + b)) *
          v (i * 2 ^ (lf + B) + (f * 2 ^ B + b)) := by
    have hs : ∀ g : ℕ → E, ∑ θ ∈ range (2 ^ (lf + B)), g θ =
        ∑ f ∈ range (2 ^ lf), ∑ b ∈ range (2 ^ B), g (f * 2 ^ B + b) :=
      fun g => by rw [pow_add 2 lf B, Alg.sum_range_mul_add]
    rw [pow_add 2 Dt (lf + B), Alg.sum_range_mul_add,
      sum_congr rfl fun i _ =>
        hs fun θ => eqN (Dt + (lf + B)) 0 z (i * 2 ^ (lf + B) + θ) * v (i * 2 ^ (lf + B) + θ),
      sum_comm]
  have hR : ∀ f, eqN lf Dt z f *
        ∑ X ∈ range (2 ^ (Dt + B)),
          eqN (Dt + B) 0 (skip Dt lf z) X * v (X / 2 ^ B * 2 ^ (lf + B) + (f * 2 ^ B + X % 2 ^ B)) =
      ∑ i ∈ range (2 ^ Dt), ∑ b ∈ range (2 ^ B), eqN lf Dt z f *
        (eqN (Dt + B) 0 (skip Dt lf z) (i * 2 ^ B + b) *
          v ((i * 2 ^ B + b) / 2 ^ B * 2 ^ (lf + B) + (f * 2 ^ B + (i * 2 ^ B + b) % 2 ^ B))) := by
    intro f
    rw [pow_add 2 Dt B, Alg.sum_range_mul_add, mul_sum]
    exact sum_congr rfl fun i _ => mul_sum _ _ _
  rw [hL]
  simp only [hR]
  refine sum_congr rfl fun f hf => sum_congr rfl fun i _ => sum_congr rfl fun b hb => ?_
  have hb' := mem_range.mp hb
  have hf' := mem_range.mp hf
  have hθ : f * 2 ^ B + b < 2 ^ (lf + B) := by
    calc f * 2 ^ B + b < f * 2 ^ B + 2 ^ B := by omega
      _ = (f + 1) * 2 ^ B := by ring
      _ ≤ 2 ^ lf * 2 ^ B := Nat.mul_le_mul_right _ hf'
      _ = 2 ^ (lf + B) := (pow_add 2 lf B).symm
  obtain ⟨e1, e2⟩ := split_idx B i b hb'
  rw [e1, e2, eqN_append' Dt (lf + B) 0 z i hθ, Nat.zero_add, eqN_append' lf B Dt z f hb',
    eqN_append' Dt B 0 (skip Dt lf z) i hb', Nat.zero_add,
    eqN_shift Dt 0 0 (a := skip Dt lf z) (a' := z) (fun t ht => by
      show (if 0 + t < Dt then z (0 + t) else z (0 + t + lf)) = z (0 + t)
      rw [if_pos (by omega)]),
    eqN_shift B Dt (Dt + lf) (a := skip Dt lf z) (a' := z) (fun t _ => by
      show (if Dt + t < Dt then z (Dt + t) else z (Dt + t + lf)) = z (Dt + lf + t)
      rw [if_neg (by omega)]
      congr 1
      omega)]
  ring

end Tools

namespace Plan

variable {F : Type} [Field F] (P : Plan F) (E : Type) [Field E] [Algebra F E]

/-- The forest of a plan. lf is the number of coordinates for the number of a call, r the number of
coordinates of a table. -/
def lk (lf r : ℕ) : LkPar E where
  D := P.D - P.B
  σ := lf + P.B
  r := r
  lp := P.lp
  NT := P.nc * 2 ^ P.B
  tb := fun θ t => ((t % 2 ^ P.d (θ / 2 ^ P.B) : ℕ) : E)
  t0 := fun _ => 0
  φ := fun _ => 0

variable {E}

/-- The keys of the forest. -/
def keyT (W : ℕ → ℕ → F) (θ i : ℕ) : E :=
  algebraMap F E (P.key (θ / 2 ^ P.B) W (i * 2 ^ P.B + θ % 2 ^ P.B))

theorem lk_wf {p : ℕ} {WFp : (ℕ → ℕ → F) → Prop} (hV : P.Valid p WFp) {lf r : ℕ}
    (hlf : P.nc ≤ 2 ^ lf) (hr : 2 ^ (r + 2 ^ P.lp) < p) : (P.lk E lf r).WF p where
  nt := by
    show P.nc * 2 ^ P.B ≤ 2 ^ (lf + P.B)
    rw [pow_add]
    exact Nat.mul_le_mul_right _ hlf
  t0 := fun _ => by
    show 0 < 2 ^ r
    positivity
  φ := fun _ => Nat.zero_le _
  dle := by
    show P.D - P.B ≤ r + 2 ^ P.lp
    have h := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hV.pl2'
    omega
  char := hr

/-- Under `hB`, `hr`: every key of the forest is in the table of its tree if and only if every key
of every call is in its table. -/
theorem inTable_iff (hB : P.B ≤ P.D) {lf r : ℕ} (hr : ∀ f, f < P.nc → P.d f ≤ r) (W : ℕ → ℕ → F) :
    (P.lk E lf r).InTable (P.keyT W) ↔ P.KeysAll W := by
  have hpos : 0 < 2 ^ P.B := by positivity
  have hD : 2 ^ P.D = 2 ^ (P.D - P.B) * 2 ^ P.B := by rw [← pow_add, Nat.sub_add_cancel hB]
  constructor
  · intro h f hf idx hidx
    have hb : idx % 2 ^ P.B < 2 ^ P.B := Nat.mod_lt _ hpos
    obtain ⟨e1, e2⟩ := split_idx P.B f (idx % 2 ^ P.B) hb
    have hθ : f * 2 ^ P.B + idx % 2 ^ P.B < P.nc * 2 ^ P.B := by
      calc f * 2 ^ P.B + idx % 2 ^ P.B < f * 2 ^ P.B + 2 ^ P.B := by omega
        _ = (f + 1) * 2 ^ P.B := by ring
        _ ≤ P.nc * 2 ^ P.B := Nat.mul_le_mul_right _ hf
    have hi : idx / 2 ^ P.B < 2 ^ (P.D - P.B) :=
      (Nat.div_lt_iff_lt_mul hpos).2 (by rw [← hD]; exact hidx)
    obtain ⟨t, _, ht⟩ := h _ hθ _ hi
    have ht' : algebraMap F E (P.key ((f * 2 ^ P.B + idx % 2 ^ P.B) / 2 ^ P.B) W
        (idx / 2 ^ P.B * 2 ^ P.B + (f * 2 ^ P.B + idx % 2 ^ P.B) % 2 ^ P.B))
        = ((t % 2 ^ P.d ((f * 2 ^ P.B + idx % 2 ^ P.B) / 2 ^ P.B) : ℕ) : E) := ht
    rw [e1, e2, Nat.div_add_mod' idx, ← map_natCast (algebraMap F E)] at ht'
    exact ⟨t % 2 ^ P.d f, Nat.mod_lt _ (by positivity), (algebraMap F E).injective ht'⟩
  · intro h θ hθ i hi
    have hf : θ / 2 ^ P.B < P.nc := (Nat.div_lt_iff_lt_mul hpos).2 hθ
    have hb : θ % 2 ^ P.B < 2 ^ P.B := Nat.mod_lt _ hpos
    have hidx : i * 2 ^ P.B + θ % 2 ^ P.B < 2 ^ P.D := by
      calc i * 2 ^ P.B + θ % 2 ^ P.B < i * 2 ^ P.B + 2 ^ P.B := by omega
        _ = (i + 1) * 2 ^ P.B := by ring
        _ ≤ 2 ^ (P.D - P.B) * 2 ^ P.B := Nat.mul_le_mul_right _ hi
        _ = 2 ^ P.D := hD.symm
    obtain ⟨t, ht, hk⟩ := h _ hf _ hidx
    refine ⟨t, lt_of_lt_of_le ht (Nat.pow_le_pow_right (by norm_num) (hr _ hf)), ?_⟩
    show algebraMap F E (P.key (θ / 2 ^ P.B) W (i * 2 ^ P.B + θ % 2 ^ P.B)) =
      ((t % 2 ^ P.d (θ / 2 ^ P.B) : ℕ) : E)
    rw [hk, Nat.mod_eq_of_lt ht, map_natCast]

/-! ## The end of the key side -/

/-- the key's coordinates in a point z of the forest: z without the coordinates of f -/
def zKey (lf : ℕ) (z : ℕ → E) : ℕ → E := skip (P.D - P.B) lf z

/-- ∑_(f < nc) eq(z_f, f) -/
def pubN (lf : ℕ) (z : ℕ → E) : E := ∑ f ∈ range P.nc, eqN lf (P.D - P.B) z f

/-- ∑_f eq(z_f, f) ~o_f(z_row) -/
def offAll (lf : ℕ) (z : ℕ → E) : E :=
  ∑ f ∈ range P.nc, eqN lf (P.D - P.B) z f * P.offExt f (P.zKey lf z)

/-- G(z) = ∑_f eq(z_f, f) g_f(z_row) -/
def gAll (lf : ℕ) (z : ℕ → E) (y : ℕ) : E :=
  ∑ f ∈ range P.nc, eqN lf (P.D - P.B) z f * P.gOf f (P.zKey lf z) y

/-- ψ(z): the column part of `zKey` -/
def psi (lf : ℕ) (z : ℕ → E) : ℕ → E := fun t => P.zKey lf z (P.D - P.k + t)

/-- The end of the key side, under `hk`, `hB`, `hlf`: the extension of `leafK` at z is a public
number minus an index form. -/
theorem ext_leafK (hk : P.k ≤ P.D) (hB : P.B ≤ P.D) {lf r : ℕ} (hlf : P.nc ≤ 2 ^ lf)
    (W : ℕ → ℕ → F) (al : E) (z : ℕ → E) :
    ext ((P.lk E lf r).D + (P.lk E lf r).σ) ((P.lk E lf r).leafK (P.keyT W) al) z =
        al * P.pubN lf z - P.offAll lf z -
          ∑ y ∈ range P.h, ∑ c ∈ range (2 ^ P.k),
            P.gAll lf z y * eqN P.k 0 (P.psi lf z) c * algebraMap F E (W y c) := by
  have hpos : 0 < 2 ^ P.B := by positivity
  have hDB : P.D - P.B + P.B = P.D := Nat.sub_add_cancel hB
  show ext (P.D - P.B + (lf + P.B)) ((P.lk E lf r).leafK (P.keyT W) al) z = _
  rw [ext_forest]
  -- the vector of one call
  have hv : ∀ f ∈ range (2 ^ lf),
      ext (P.D - P.B + P.B)
          (fun idx =>
            (P.lk E lf r).leafK (P.keyT W) al
              (idx / 2 ^ P.B * 2 ^ (lf + P.B) + (f * 2 ^ P.B + idx % 2 ^ P.B)))
          (skip (P.D - P.B) lf z) =
        if f < P.nc then al - ext P.D (fun idx => algebraMap F E (P.key f W idx)) (P.zKey lf z)
        else 0 := by
    intro f hf
    have hf' := mem_range.mp hf
    have hvec : (fun idx =>
          (P.lk E lf r).leafK (P.keyT W) al
            (idx / 2 ^ P.B * 2 ^ (lf + P.B) + (f * 2 ^ P.B + idx % 2 ^ P.B))) =
        fun idx => if f < P.nc then al - algebraMap F E (P.key f W idx) else 0 := by
      funext idx
      have hb : idx % 2 ^ P.B < 2 ^ P.B := Nat.mod_lt _ hpos
      have hθ : f * 2 ^ P.B + idx % 2 ^ P.B < 2 ^ (lf + P.B) := by
        calc f * 2 ^ P.B + idx % 2 ^ P.B < f * 2 ^ P.B + 2 ^ P.B := by omega
          _ = (f + 1) * 2 ^ P.B := by ring
          _ ≤ 2 ^ lf * 2 ^ P.B := Nat.mul_le_mul_right _ hf'
          _ = 2 ^ (lf + P.B) := (pow_add 2 lf P.B).symm
      obtain ⟨e1, e2⟩ := split_idx (lf + P.B) (idx / 2 ^ P.B) _ hθ
      obtain ⟨e3, e4⟩ := split_idx P.B f _ hb
      show (if (idx / 2 ^ P.B * 2 ^ (lf + P.B) + (f * 2 ^ P.B + idx % 2 ^ P.B)) % 2 ^ (lf + P.B) <
              P.nc * 2 ^ P.B then
            al - P.keyT W
                ((idx / 2 ^ P.B * 2 ^ (lf + P.B) + (f * 2 ^ P.B + idx % 2 ^ P.B)) % 2 ^ (lf + P.B))
                ((idx / 2 ^ P.B * 2 ^ (lf + P.B) + (f * 2 ^ P.B + idx % 2 ^ P.B)) / 2 ^ (lf + P.B))
          else 0) = _
      rw [e1, e2]
      have hiff : f * 2 ^ P.B + idx % 2 ^ P.B < P.nc * 2 ^ P.B ↔ f < P.nc := by
        rw [← Nat.div_lt_iff_lt_mul hpos, e4]
      by_cases hfn : f < P.nc
      · rw [if_pos (hiff.2 hfn), if_pos hfn]
        unfold keyT
        rw [e3, e4, Nat.div_add_mod' idx]
      · rw [if_neg (fun h => hfn (hiff.1 h)), if_neg hfn]
    rw [hvec, hDB]
    by_cases hfn : f < P.nc
    · simp only [if_pos hfn]
      rw [ext_sub, ext_const]
      rfl
    · simp only [if_neg hfn]
      exact ext_zero_of_forall (fun _ _ => rfl) _
  rw [sum_congr rfl fun f hf => by rw [hv f hf]]
  -- only the calls f < nc count
  have hsub : ∑ f ∈ range (2 ^ lf), eqN lf (P.D - P.B) z f *
        (if f < P.nc then al - ext P.D (fun idx => algebraMap F E (P.key f W idx)) (P.zKey lf z)
          else 0) =
      ∑ f ∈ range P.nc, eqN lf (P.D - P.B) z f *
        (al - ext P.D (fun idx => algebraMap F E (P.key f W idx)) (P.zKey lf z)) := by
    rw [← sum_subset (range_subset_range.mpr hlf)]
    · exact sum_congr rfl fun f hf => by rw [if_pos (mem_range.mp hf)]
    · intro f _ hf
      rw [if_neg (fun h => hf (mem_range.mpr h)), mul_zero]
  rw [hsub]
  simp only [P.ext_key hk]
  unfold pubN offAll gAll
  have hψ : ∀ c, eqN P.k (P.D - P.k) (P.zKey lf z) c = eqN P.k 0 (P.psi lf z) c := fun c =>
    eqN_shift P.k (P.D - P.k) 0 (fun t _ => by
      show P.zKey lf z (P.D - P.k + t) = P.zKey lf z (P.D - P.k + (0 + t))
      rw [Nat.zero_add]) c
  simp only [hψ, mul_sub, mul_add, sum_sub_distrib, sum_add_distrib, mul_sum, sum_mul]
  have h3 : ∑ f ∈ range P.nc, ∑ y ∈ range P.h, ∑ c ∈ range (2 ^ P.k), eqN lf (P.D - P.B) z f *
        (P.gOf f (P.zKey lf z) y * eqN P.k 0 (P.psi lf z) c * algebraMap F E (W y c)) =
      ∑ y ∈ range P.h, ∑ c ∈ range (2 ^ P.k), ∑ f ∈ range P.nc, eqN lf (P.D - P.B) z f *
        P.gOf f (P.zKey lf z) y * eqN P.k 0 (P.psi lf z) c * algebraMap F E (W y c) := by
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun c _ => sum_congr rfl fun f _ => by ring
  rw [h3]
  have h4 : ∑ f ∈ range P.nc, eqN lf (P.D - P.B) z f * al =
      ∑ f ∈ range P.nc, al * eqN lf (P.D - P.B) z f :=
    sum_congr rfl fun f _ => mul_comm _ _
  rw [h4]
  ring

/-! ## The honest multiplicities -/

end Plan

section IdxOf

variable {F : Type} [Field F] [DecidableEq F]

/-- The first number t < 2^d whose image is a (0 if there is none): found by search, without
choice. -/
def idxOf (d : ℕ) (a : F) : ℕ :=
  ((List.range (2 ^ d)).find? fun t : ℕ => decide (a = (t : F))).getD 0

theorem idxOf_spec {d : ℕ} {a : F} (h : InTab d a) : idxOf d a < 2 ^ d ∧ a = (idxOf d a : F) := by
  unfold idxOf
  cases hf : (List.range (2 ^ d)).find? fun t : ℕ => decide (a = (t : F)) with
  | none =>
    obtain ⟨t, ht, ha⟩ := h
    have := List.find?_eq_none.1 hf t (List.mem_range.2 ht)
    exact absurd (decide_eq_true ha) this
  | some t =>
    have h1 : decide (a = (t : F)) = true :=
      List.find?_some (p := fun t : ℕ => decide (a = (t : F))) hf
    exact ⟨List.mem_range.1 (List.mem_of_find?_eq_some hf), of_decide_eq_true h1⟩

end IdxOf

namespace Plan

variable {F : Type} [Field F] [DecidableEq F] (P : Plan F) {E : Type} [Field E] [Algebra F E]

/-- the table index of key number i of the tree θ -/
def rowT (W : ℕ → ℕ → F) (θ i : ℕ) : ℕ :=
  idxOf (P.d (θ / 2 ^ P.B)) (P.key (θ / 2 ^ P.B) W (i * 2 ^ P.B + θ % 2 ^ P.B))

variable (E) in
/-- The honest vector bit: the bits of the multiplicities; bitT t θ π is bit π of the number of keys
of the tree θ whose table index (`rowT`) is t. -/
def bitT (lf r : ℕ) (W : ℕ → ℕ → F) (t θ π : ℕ) : E :=
  if ((P.lk E lf r).trueMult (fun _ _ => false) (P.rowT W) θ t).testBit π then 1 else 0

/-- Under `hB`, `hr`, `hK` (all keys are in their tables), bitT is the honest B of the lookup
argument. -/
theorem honB (hB : P.B ≤ P.D) {lf r : ℕ} (hr : ∀ f, f < P.nc → P.d f ≤ r)
    {W : ℕ → ℕ → F} (hK : P.KeysAll W) :
    (P.lk E lf r).HonB (P.keyT W) (P.bitT E lf r W) (fun _ _ => false) (P.rowT W) where
  padKey := fun _ _ _ _ h => absurd h (by simp)
  rowKey := fun θ hθ i hi _ => by
    have hpos : 0 < 2 ^ P.B := by positivity
    have hD : 2 ^ P.D = 2 ^ (P.D - P.B) * 2 ^ P.B := by rw [← pow_add, Nat.sub_add_cancel hB]
    have hf : θ / 2 ^ P.B < P.nc := (Nat.div_lt_iff_lt_mul hpos).2 hθ
    have hb : θ % 2 ^ P.B < 2 ^ P.B := Nat.mod_lt _ hpos
    have hidx : i * 2 ^ P.B + θ % 2 ^ P.B < 2 ^ P.D := by
      calc i * 2 ^ P.B + θ % 2 ^ P.B < i * 2 ^ P.B + 2 ^ P.B := by omega
        _ = (i + 1) * 2 ^ P.B := by ring
        _ ≤ 2 ^ (P.D - P.B) * 2 ^ P.B := Nat.mul_le_mul_right _ hi
        _ = 2 ^ P.D := hD.symm
    obtain ⟨h1, h2⟩ := idxOf_spec (hK _ hf _ hidx)
    refine ⟨lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (hr _ hf)), ?_⟩
    show algebraMap F E (P.key (θ / 2 ^ P.B) W (i * 2 ^ P.B + θ % 2 ^ P.B)) =
      ((P.rowT W θ i % 2 ^ P.d (θ / 2 ^ P.B) : ℕ) : E)
    have h3 : P.rowT W θ i % 2 ^ P.d (θ / 2 ^ P.B) = P.rowT W θ i := Nat.mod_eq_of_lt h1
    rw [h3]
    conv_lhs => rw [h2]
    exact map_natCast _ _
  phi := fun _ _ => by
    show 0 = _
    simp
  bits := fun _ _ _ _ _ _ => rfl

end Plan

end Blocks.Rng
