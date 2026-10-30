-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ReadSD.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: the summand "the key at the index" (sSD, Johnson/Desc/K5/Honest/Index.lean),
READ IN A FIELD. It is the one summand of these rounds that is no sum of weighted products of two
maps: the term of a pair of layer and query head has one factor for the layer's keys and one for
each bit of the index. Names for pieces of the summand's text, and statements with their proofs. The
Greek letter ρ is any reading (OnBytes/Model/HideLaws.lean); the name rho in Latin letters is an
array: it stands for the challenges of the score at the index. The library is Inst/Model/Att
(Sums.lean: Phi18, the summand of step 18; KeyForms.lean: rvKC, rvIBP, Ebk, the rule values of its
end values).

Main names:
  kcTab, kcAt, ibpAt, sdCoef, sdBit, sdOf
                  the summand's text on plain letters: any sizes, any cells, any array in the place
                  of the challenges of the score at the index and of the batching powers
  rhoOf, om4Of, sSD_eq   the prover's summand is that text at its own two arrays
  sd_termAt .. sd_endAt_ib   a term, an end value, by number
  sd_below, named_sdOf   every factor names one of the end values
  kcF, ibF, coF, bitF   the letters as functions of the read point, in the library's equality
                  weights
  aff_kcF .. free_bitF   each function is of degree at most 1 in every coordinate; which
                  coordinates it does not read
  ptL_eq          a list read as a point is its array's point
  read_kcAt, read_ibpAt, read_sdCoef, read_fac_kc, read_fac_bit
                  each letter reads as its function: unconditional but for the point's length
  KeyPub, rhoOf_eq, keyPub_of
                  the premise on the two arrays: read, they are the library's challenges; it holds
                  at the prover's own arrays where the verifier's function of the points returns
  kc_reads, ibp_reads, coef_reads, fac_zero_reads, fac_succ_reads
                  the letters read as the library's
  sd_at           **the summand at ANY point of the sumcheck's length reads as Phi18**
  sd_total        its sum over the cube reads as the sum of Phi18 over the library's vertices
  sd_start, sSD_start
                  **that sum is the batch of the second maps of the score at the index, at that
                  sumcheck's challenges** (by keyMean, Cb/Pv/Att/Mean/Key.lean): algebra at every
                  cell; no cell is asked to be a bit, no identity of the model is spent

The statements from kc_reads on are CONDITIONAL. The premises, and who is meant to show each:
  Sized (Johnson/Desc/K5/Honest/Law/Cells.lean): public, on the planner's shape: the caller's.
  KeyPub: on public letters. By keyPub_of it follows from two public facts with code: the verifier's
  function of the points returns at the challenges so far, and the planner's number of variables of
  the score at the index is the library's (a field of Planned,
  Johnson/Desc/K5/Honest/Law/Weights.lean): the caller's.
In sd_start the challenges c at which the score's summand is taken are free: its hidden maps read no
challenge (sSF_endAt, Johnson/Desc/K5/Honest/Law/ReadSF.lean).
Limits. No theorem of this file says that a premise holds at any place (under the head `Sized` and
`Planned`: `public_at_head`, Johnson/Desc/K5/Honest/Law/PublicAtHead.lean).
Nothing ties the cells to a commitment.
A challenge that has not been heard reads as 0. No property is claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.Degrees
import Johnson.Desc.K5.Honest.Law.ReadSF
import Cb.Pv.Att.Mean.KeyMaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open OnBytes.Road (pt)
open VerifiableInference.Desc.First.Att.P (Geo geoOf eqTab eqPts chal pointsOf)
open Inst.Model.AttSeg
open Finset

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## 1 The summand's text, in named pieces -/

/-- The keys of layer lam on the cube (j, hk), with the channel at the last coordinates of rho: the
entry j 2^lgk + hk. -/
def kcTab (g : Geo) (w : K5In) (rho : Array E) (lam : ℕ) : Array E :=
  (Array.range (2 ^ g.lt * 2 ^ g.lgk)).map fun n =>
    under (eqTab (rho.extract (g.lt + g.lgk) rho.size)) fun ch =>
      w.kx lam (n % 2 ^ g.lgk) (n / 2 ^ g.lgk) ch

/-- A table on the cube (j, hk), at the first two cuts of the point x. -/
def kcAt (g : Geo) (x t : Array E) : E :=
  under (eqTab (x.extract 0 g.lt)) fun j =>
    under (eqTab (x.extract g.lt (g.lt + g.lgk))) fun hk => t.getD (j * 2 ^ g.lgk + hk) zeroE

/-- Cell k of the index of pair b, at the last two cuts of the point x. -/
def ibpAt (g : Geo) (w : K5In) (x : Array E) (k b : ℕ) : E :=
  under (eqTab (x.extract g.lt (g.lt + g.lgk))) fun hk =>
    under (eqTab (x.extract (g.lt + g.lgk) (2 * g.lt + g.lgk))) fun i => w.ibit k b hk i

/-- The coefficient of pair b's term. -/
def sdCoef (g : Geo) (rho om' x : Array E) (b : ℕ) : E :=
  mulE (mulE (eqPts (rho.extract 0 g.lt) (x.extract (g.lt + g.lgk) (2 * g.lt + g.lgk)))
    (eqPts (rho.extract g.lt (g.lt + g.lgk)) (x.extract g.lt (g.lt + g.lgk)))) (om'.getD b zeroE)

/-- The factor of cell k in pair b's term. -/
def sdBit (g : Geo) (x : Array E) (b k : ℕ) : Factor :=
  ⟨subE (addE ((x.extract 0 g.lt).getD (g.lt - 1 - k) zeroE)
      ((x.extract 0 g.lt).getD (g.lt - 1 - k) zeroE)) oneE,
    g.Lam + b * g.lt + k, subE oneE ((x.extract 0 g.lt).getD (g.lt - 1 - k) zeroE)⟩

/-- **The summand "the key at the index" on plain letters**: rho stands for the challenges of the
score at the index, om' for the batching element's powers. -/
def sdOf (g : Geo) (w : K5In) (rho om' : Array E) : Summand where
  vars := 2 * g.lt + g.lgk
  ends := g.Lam + g.NP * g.lt
  endAt := fun x n =>
    if n < g.Lam then kcAt g x.toArray (((Array.range g.Lam).map (kcTab g w rho)).getD n #[])
    else ibpAt g w x.toArray ((n - g.Lam) % g.lt) ((n - g.Lam) / g.lt)
  terms := fun x => (List.range g.NP).map fun b =>
    ⟨sdCoef g rho om' x.toArray b,
      ⟨oneE, b / g.HA, zeroE⟩ :: (List.range g.lt).map (sdBit g x.toArray b)⟩

/-- The challenges of the score at the index, as the prover's summand reads them. -/
def rhoOf (P : Pub5) (c : Chal) : Array E := (maxOf P c).scF.r

/-- The powers that batch the pairs in this sumcheck. -/
def om4Of (P : Pub5) (c : Chal) : Array E := (heardAt P c fun _ => none).om'

/-- The prover's summand is that text at the place's letters. -/
theorem sSD_eq (P : Pub5) (w : K5In) (c : Chal) :
    sSD P w c = sdOf P.g w (rhoOf P c) (om4Of P c) := rfl

/-! ## 2 Terms and end values by number -/

namespace SD

theorem getD_map_range {α : Type} (n : ℕ) (f : ℕ → α) (d : α) (i : ℕ) :
    ((List.range n).map f).getD i d = if i < n then f i else d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < n
  · rw [List.getElem?_range h, if_pos h]
    rfl
  · rw [List.getElem?_eq_none (by rw [List.length_range]; omega), if_neg h]
    rfl

end SD

section Text
variable (g : Geo) (w : K5In) (rho om' : Array E)

theorem sd_termAt (x : List E) {b : ℕ} (hb : b < g.NP) : (sdOf g w rho om').termAt x b =
    ⟨sdCoef g rho om' x.toArray b,
      ⟨oneE, b / g.HA, zeroE⟩ :: (List.range g.lt).map (sdBit g x.toArray b)⟩ := by
  show ((List.range g.NP).map _).getD b _ = _
  rw [SD.getD_map_range, if_pos hb]

theorem sd_termAt_beyond (x : List E) {b : ℕ} (hb : ¬ b < g.NP) :
    (sdOf g w rho om').termAt x b = ⟨zeroE, []⟩ := by
  show ((List.range g.NP).map _).getD b _ = _
  rw [SD.getD_map_range, if_neg hb]

/-- An end value below Lam is a layer's keys. -/
theorem sd_endAt_kc (x : List E) {n : ℕ} (hn : n < g.Lam) :
    (sdOf g w rho om').endAt x n = kcAt g x.toArray (kcTab g w rho n) := by
  show (if n < g.Lam then kcAt g x.toArray (((Array.range g.Lam).map (kcTab g w rho)).getD n #[])
    else _) = _
  rw [if_pos hn, getD_range_map _ _ _ hn]

/-- The end value number Lam + b lt + k is cell k of the index of pair b. -/
theorem sd_endAt_ib (x : List E) (b : ℕ) {k : ℕ} (hk : k < g.lt) :
    (sdOf g w rho om').endAt x (g.Lam + b * g.lt + k) = ibpAt g w x.toArray k b := by
  have e : g.Lam + b * g.lt + k - g.Lam = b * g.lt + k := by omega
  have d := Dim.div_step (a := b) (Nat.lt_of_le_of_lt (Nat.zero_le k) hk) hk
  show (if g.Lam + b * g.lt + k < g.Lam then _ else ibpAt g w x.toArray
    ((g.Lam + b * g.lt + k - g.Lam) % g.lt) ((g.Lam + b * g.lt + k - g.Lam) / g.lt)) = _
  rw [if_neg (by omega), e, d.1, d.2]

/-- A pair's layer is one of the layers. -/
theorem sd_layer {b : ℕ} (hb : b < g.NP) : b / g.HA < g.Lam :=
  Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hb)

/-- Every factor's number lies below the number of end values, at any point. -/
theorem sd_below (x : List E) : ∀ t ∈ (sdOf g w rho om').terms x, ∀ f ∈ t.fs,
    f.n < g.Lam + g.NP * g.lt := by
  intro t ht f hf
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ht
  have hb' : b < g.NP := List.mem_range.1 hb
  rcases List.mem_cons.1 hf with rfl | hf
  · exact Nat.lt_of_lt_of_le (sd_layer g hb') (Nat.le_add_right _ _)
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hf
    have hk' : k < g.lt := List.mem_range.1 hk
    show g.Lam + b * g.lt + k < g.Lam + g.NP * g.lt
    have : (b + 1) * g.lt ≤ g.NP * g.lt := Nat.mul_le_mul_right _ hb'
    rw [Nat.add_mul, Nat.one_mul] at this
    omega

/-- **Every factor names one of the end values.** -/
theorem named_sdOf : (sdOf g w rho om').Named (g.Lam + g.NP * g.lt) :=
  ⟨rfl, fun x _ => sd_below g w rho om' x⟩

end Text

/-! ## 3 The letters as functions of the read point -/

/-- A table T on the cube (j, hk), at the point's first lt and next lgk coordinates. -/
def kcF (lt lgk : ℕ) (T : ℕ → K) : (ℕ → K) → K := fun ξ =>
  ∑ j ∈ range (2 ^ lt), Blocks.eqN lt 0 ξ j *
    ∑ hk ∈ range (2 ^ lgk), Blocks.eqN lgk lt ξ hk * T (j * 2 ^ lgk + hk)

/-- An array A on (hk, i), at the point's coordinates from lt on. -/
def ibF (lt lgk : ℕ) (A : ℕ → ℕ → K) : (ℕ → K) → K := fun ξ =>
  ∑ hk ∈ range (2 ^ lgk), Blocks.eqN lgk lt ξ hk *
    ∑ i ∈ range (2 ^ lt), Blocks.eqN lt (lt + lgk) ξ i * A hk i

/-- A coefficient: two equality polynomials and a constant. -/
def coF (lt lgk n1 n2 : ℕ) (u1 u2 : ℕ → K) (o : K) : (ℕ → K) → K := fun ξ =>
  eqPt n1 u1 (sh ξ (lt + lgk)) * eqPt n2 u2 (sh ξ lt) * o

/-- The factor of bit k: (2 y - 1) times the cell's map, plus 1 - y, y the coordinate lt - 1 - k. -/
def bitF (lt lgk k : ℕ) (A : ℕ → ℕ → K) : (ℕ → K) → K := fun ξ =>
  (ξ (lt - 1 - k) + ξ (lt - 1 - k) - 1) * ibF lt lgk A ξ + (1 - ξ (lt - 1 - k))

section Calc
open Deg
variable (lt lgk : ℕ) {v : ℕ}

theorem aff_kcF (T : ℕ → K) : Aff v (kcF lt lgk T) := by
  unfold kcF
  by_cases h : v < lt
  · exact Aff.sum _ fun j _ => (aff_eqN lt 0 j).mul_free
      (Free.sum _ fun hk _ => (free_eqN lgk lt hk (Or.inl h)).mul (free_const _))
  · exact Aff.sum _ fun j _ => (free_eqN lt 0 j (Or.inr (by omega))).mul_aff
      (Aff.sum _ fun hk _ => (aff_eqN lgk lt hk).mul_free (free_const _))

/-- The keys' map does not read the coordinates of i. -/
theorem free_kcF (T : ℕ → K) (h : lt + lgk ≤ v) : Free v (kcF lt lgk T) := by
  unfold kcF
  exact Free.sum _ fun j _ => (free_eqN lt 0 j (Or.inr (by omega))).mul
    (Free.sum _ fun hk _ => (free_eqN lgk lt hk (Or.inr h)).mul (free_const _))

theorem aff_ibF (A : ℕ → ℕ → K) : Aff v (ibF lt lgk A) := by
  unfold ibF
  by_cases h : v < lt + lgk
  · exact Aff.sum _ fun hk _ => (aff_eqN lgk lt hk).mul_free
      (Free.sum _ fun i _ => (free_eqN lt (lt + lgk) i (Or.inl h)).mul (free_const _))
  · exact Aff.sum _ fun hk _ => (free_eqN lgk lt hk (Or.inr (by omega))).mul_aff
      (Aff.sum _ fun i _ => (aff_eqN lt (lt + lgk) i).mul_free (free_const _))

/-- A cell's map does not read the coordinates of j. -/
theorem free_ibF (A : ℕ → ℕ → K) (h : v < lt) : Free v (ibF lt lgk A) := by
  unfold ibF
  exact Free.sum _ fun hk _ => (free_eqN lgk lt hk (Or.inl h)).mul
    (Free.sum _ fun i _ => (free_eqN lt (lt + lgk) i (Or.inl (by omega))).mul (free_const _))

theorem aff_coF (n1 : ℕ) {n2 : ℕ} (h2 : n2 ≤ lgk) (u1 u2 : ℕ → K) (o : K) :
    Aff v (coF lt lgk n1 n2 u1 u2 o) := by
  unfold coF
  by_cases h : v < lt + lgk
  · exact ((free_eqPt n1 (lt + lgk) u1 (Or.inl h)).mul_aff (aff_eqPt n2 lt u2)).mul_free
      (free_const o)
  · exact ((aff_eqPt n1 (lt + lgk) u1).mul_free (free_eqPt n2 lt u2 (Or.inr (by omega)))).mul_free
      (free_const o)

/-- A coefficient does not read the coordinates of j. -/
theorem free_coF (n1 n2 : ℕ) (u1 u2 : ℕ → K) (o : K) (h : v < lt) :
    Free v (coF lt lgk n1 n2 u1 u2 o) := by
  unfold coF
  exact ((free_eqPt n1 (lt + lgk) u1 (Or.inl (by omega))).mul
    (free_eqPt n2 lt u2 (Or.inl h))).mul (free_const o)

theorem aff_bitF {k : ℕ} (hk : k < lt) (A : ℕ → ℕ → K) : Aff v (bitF lt lgk k A) := by
  unfold bitF
  by_cases h : v < lt
  · exact ((((aff_coord _).add (aff_coord _)).sub (free_const (1 : K)).aff).mul_free
      (free_ibF lt lgk A h)).add ((free_const (1 : K)).aff.sub (aff_coord _))
  · have hc : Free v fun ξ : ℕ → K => ξ (lt - 1 - k) := free_coord (by omega)
    exact (((hc.add hc).sub (free_const (1 : K))).mul_aff (aff_ibF lt lgk A)).add
      ((free_const (1 : K)).sub hc).aff

/-- The factor of bit k reads, of the coordinates of j, that bit's alone. -/
theorem free_bitF (k : ℕ) (A : ℕ → ℕ → K) (h : v < lt) (hne : lt - 1 - k ≠ v) :
    Free v (bitF lt lgk k A) := by
  unfold bitF
  have hc : Free v fun ξ : ℕ → K => ξ (lt - 1 - k) := free_coord hne
  exact (((hc.add hc).sub (free_const (1 : K))).mul (free_ibF lt lgk A h)).add
    ((free_const (1 : K)).sub hc)

end Calc

/-! ## 4 Each letter reads as its function -/

/-- A list, read as a point, is its array's point. -/
theorem ptL_eq (x : List E) : ptL ρ x = pt ρ x.toArray :=
  funext fun j => (pt_toArray ρ x j).symm

/-- The verifier's equality polynomial of two points reads as the library's. -/
theorem read_eqPts (x y : Array E) : ρ.val (eqPts x y) = eqPt x.size (pt ρ x) (pt ρ y) :=
  OnBytes.Road.Rows.eqPts_value ρ x y

section Reads
variable (g : Geo) (w : K5In) (rho om' : Array E) {x : Array E}
  (hx : x.size = 2 * g.lt + g.lgk)
include hx

private theorem z1 : (x.extract 0 g.lt).size = g.lt := by
  rw [size_extract_le x (by omega)]
  omega

private theorem z2 : (x.extract g.lt (g.lt + g.lgk)).size = g.lgk := by
  rw [size_extract_le x (by omega)]
  omega

private theorem z3 : (x.extract (g.lt + g.lgk) (2 * g.lt + g.lgk)).size = g.lt := by
  rw [size_extract_le x (by omega)]
  omega

theorem read_kcAt (t : Array E) :
    ρ.val (kcAt g x t) = kcF g.lt g.lgk (fun n => ρ.val (t.getD n zeroE)) (pt ρ x) := by
  unfold kcAt kcF
  rw [read_under_eq ρ (z1 g hx) (v := pt ρ x) fun j hj => by
    rw [pt_extract ρ x 0 g.lt j (by omega), Nat.zero_add]]
  refine sum_congr rfl fun j _ => ?_
  rw [read_under_eq ρ (z2 g hx) (v := sh (pt ρ x) g.lt) fun k hk =>
    pt_extract ρ x g.lt (g.lt + g.lgk) k (by omega)]
  simp only [Cb.Pv.Att.eqN_sh]

theorem read_ibpAt (k b : ℕ) :
    ρ.val (ibpAt g w x k b) = ibF g.lt g.lgk (fun hk i => ρ.val (w.ibit k b hk i)) (pt ρ x) := by
  unfold ibpAt ibF
  rw [read_under_eq ρ (z2 g hx) (v := sh (pt ρ x) g.lt) fun k hk =>
    pt_extract ρ x g.lt (g.lt + g.lgk) k (by omega)]
  refine sum_congr rfl fun hk _ => ?_
  rw [read_under_eq ρ (z3 g hx) (v := sh (pt ρ x) (g.lt + g.lgk)) fun k hk =>
    pt_extract ρ x (g.lt + g.lgk) (2 * g.lt + g.lgk) k (by omega)]
  simp only [Cb.Pv.Att.eqN_sh]

omit hx in
theorem read_sdCoef (b : ℕ) : ρ.val (sdCoef g rho om' x b) =
    coF g.lt g.lgk (rho.extract 0 g.lt).size (rho.extract g.lt (g.lt + g.lgk)).size
      (pt ρ (rho.extract 0 g.lt)) (pt ρ (rho.extract g.lt (g.lt + g.lgk)))
      (ρ.val (om'.getD b zeroE)) (pt ρ x) := by
  have s1 : (rho.extract 0 g.lt).size ≤ g.lt := by
    rw [Array.size_extract]
    omega
  have s2 : (rho.extract g.lt (g.lt + g.lgk)).size ≤ g.lgk := by
    rw [Array.size_extract]
    omega
  unfold sdCoef coF
  rw [ρ.mul, ρ.mul, read_eqPts, read_eqPts,
    OnBytes.Road.Rows.eqPt_agree (v' := sh (pt ρ x) (g.lt + g.lgk)) (fun _ _ => rfl) fun k hk =>
      pt_extract ρ x (g.lt + g.lgk) (2 * g.lt + g.lgk) k (by omega),
    OnBytes.Road.Rows.eqPt_agree (v' := sh (pt ρ x) g.lt) (fun _ _ => rfl) fun k hk =>
      pt_extract ρ x g.lt (g.lt + g.lgk) k (by omega)]

omit hx in
/-- The cut of rho that stands against the coordinates of hk is not longer than these. -/
theorem size_rg_le : (rho.extract g.lt (g.lt + g.lgk)).size ≤ g.lgk := by
  rw [Array.size_extract]
  omega

end Reads

section Facs
variable (g : Geo) (w : K5In) (rho om' : Array E) {x : List E}
  (hx : x.length = 2 * g.lt + g.lgk)
include hx

/-- The first factor of pair b's term: the keys of the pair's layer. -/
theorem read_fac_kc {b : ℕ} (hb : b < g.NP) :
    ρ.val ((sdOf g w rho om').factorAt x ⟨oneE, b / g.HA, zeroE⟩) =
      kcF g.lt g.lgk (fun n => ρ.val ((kcTab g w rho (b / g.HA)).getD n zeroE)) (ptL ρ x) := by
  rw [read_bare, sd_endAt_kc g w rho om' x (sd_layer g hb),
    read_kcAt ρ g (by rw [List.size_toArray]; exact hx), ptL_eq ρ x]

/-- The factor of bit k in pair b's term. -/
theorem read_fac_bit (b : ℕ) {k : ℕ} (hk : k < g.lt) :
    ρ.val ((sdOf g w rho om').factorAt x (sdBit g x.toArray b k)) =
      bitF g.lt g.lgk k (fun hk i => ρ.val (w.ibit k b hk i)) (ptL ρ x) := by
  have e : ρ.val ((x.toArray.extract 0 g.lt).getD (g.lt - 1 - k) zeroE) =
      ptL ρ x (g.lt - 1 - k) := by
    have := pt_extract ρ x.toArray 0 g.lt (g.lt - 1 - k) (by omega)
    rw [Nat.zero_add, ← ptL_eq ρ x] at this
    exact this
  rw [read_factorAt]
  show ρ.val (subE (addE _ _) oneE) * ρ.val ((sdOf g w rho om').endAt x (g.Lam + b * g.lt + k)) +
    ρ.val (subE oneE _) = _
  rw [sd_endAt_ib g w rho om' x b hk, ρ.sub, ρ.add, ρ.sub, ρ.one, e,
    read_ibpAt ρ g w (by rw [List.size_toArray]; exact hx), ptL_eq ρ x]
  rfl

end Facs

/-! ## 5 The library's letters -/

/-- **The premise on the public letters**: rho and om', read, are the library's challenges: the end
point of the score at the index, and the powers that batch the pairs. -/
structure KeyPub (P : Pub5) (rho om' : Array E) (p : Pub K) : Prop where
  size : rho.size = P.D.lT + P.D.lg + P.D.ln
  fi : ∀ k < P.D.lT, pt ρ rho k = p.fi k
  fg : ∀ k < P.D.lg, pt ρ rho (P.D.lT + k) = p.fg k
  fn : ∀ k < P.D.ln, pt ρ rho (P.D.lT + P.D.lg + k) = p.fn k
  o' : ∀ b < P.D.nb, pt ρ om' b = p.o' b

/-- Where the verifier's function of the points returns, the prover's summand reads the challenges
of the score at the index. -/
theorem rhoOf_eq {P : Pub5} {c : Chal} (hp : (ptsOf P c).isSome = true) :
    rhoOf P c = c.r P.x (iSF P.x) := by
  obtain ⟨pts, hp⟩ := Option.isSome_iff_exists.1 hp
  obtain ⟨uW, hc⟩ := pts_cut (show pointsOf _ _ _ _ = some pts from hp)
  have e : rhoOf P c = pts.x.scF.r := by
    unfold rhoOf maxOf
    rw [hp]
    rfl
  rw [e, hc.scF]
  exact chal_sumAt _

/-- **The premise holds at the prover's own letters** and the library's challenges made of them,
CONDITIONAL on: the verifier's function of the points returns at the challenges so far; the
planner's number of variables of the score at the index is the library's. Both are public and have
code. -/
theorem keyPub_of {P : Pub5} {c : Chal} (z : ℕ → K) (hp : (ptsOf P c).isSome = true)
    (hv : (cut P.x).getD (iSF P.x) 3 - 3 = Step.s16.g P.D) :
    KeyPub ρ P (rhoOf P c) (om4Of P c) (pubOf ρ P c z) := by
  have e : rhoOf P c = chal (heardAt P c fun _ => none).atIndex :=
    (rhoOf_eq hp).trans (chal_sumAt _).symm
  refine ⟨?_, fun k _ => ?_, fun k _ => ?_, fun k _ => ?_, fun b _ => rfl⟩
  · rw [rhoOf_eq hp]
    unfold Chal.r
    rw [Array.size_map, Array.size_range]
    exact hv
  · rw [e]
    rfl
  · rw [e]
    rfl
  · rw [e]
    rfl

section Lib
variable {P : Pub5} (H : Sized P) (w : K5In) {rho om' : Array E} {p : Pub K}
  (Q : KeyPub ρ P rho om' p)

omit ρ in
include H in
/-- The sumcheck's length in the place's numbers. -/
theorem sd_len {x : List E} (hx : x.length = g18 P.D) : x.length = 2 * P.g.lt + P.g.lgk := by
  rw [hx, H.lt]
  show P.D.lT + P.D.lg + P.D.lT = 2 * P.D.lT + P.D.lg
  omega

include H Q in
/-- An entry of the keys' table. -/
theorem read_kcTab (lam : ℕ) {j hk : ℕ} (hj : j < 2 ^ P.D.lT) (hh : hk < 2 ^ P.D.lg) :
    ρ.val ((kcTab P.g w rho lam).getD (j * 2 ^ P.g.lgk + hk) zeroE) =
      conN P.D p.fn fun n => keyV (tOf ρ w) lam hk j n := by
  have d := Dim.div_step (a := j) (Nat.two_pow_pos P.D.lg) hh
  have hlt : j * 2 ^ P.g.lgk + hk < 2 ^ P.g.lt * 2 ^ P.g.lgk := by
    rw [H.lt]
    calc j * 2 ^ P.D.lg + hk < j * 2 ^ P.D.lg + 2 ^ P.D.lg := by omega
      _ = (j + 1) * 2 ^ P.D.lg := by ring
      _ ≤ 2 ^ P.D.lT * 2 ^ P.D.lg := Nat.mul_le_mul_right _ hj
  have hz : (rho.extract (P.g.lt + P.g.lgk) rho.size).size = P.D.ln := by
    rw [size_extract_le rho (le_refl _), Q.size, H.lt]
    show P.D.lT + P.D.lg + P.D.ln - (P.D.lT + P.D.lg) = P.D.ln
    omega
  unfold kcTab
  rw [getD_range_map _ _ _ hlt]
  show ρ.val (under _ fun ch => w.kx lam ((j * 2 ^ P.D.lg + hk) % 2 ^ P.D.lg)
    ((j * 2 ^ P.D.lg + hk) / 2 ^ P.D.lg) ch) = _
  rw [d.1, d.2, read_under_eq ρ hz (v := p.fn) fun k hk' => by
    rw [pt_extract ρ rho _ _ k (by
      rw [Q.size, H.lt]
      show P.D.lT + P.D.lg + k < P.D.lT + P.D.lg + P.D.ln
      omega), H.lt]
    exact Q.fn k hk']
  unfold conN
  exact sum_congr rfl fun n _ => by rw [read_kx]

include H Q in
/-- **KC of layer lam, at ANY point of the sumcheck's length, reads as the library's rule value.**
CONDITIONAL on Sized and KeyPub. -/
theorem kc_reads {x : List E} (hx : x.length = g18 P.D) {lam : ℕ} (hl : lam < P.D.nl) :
    ρ.val ((sdOf P.g w rho om').endAt x lam) = rvKC P.D p (tOf ρ w) (ptL ρ x) lam := by
  rw [sd_endAt_kc P.g w rho om' x hl,
    read_kcAt ρ P.g (by rw [List.size_toArray]; exact sd_len H hx), ← ptL_eq ρ x]
  unfold kcF rvKC rd3 eqT
  rw [H.lt, P.D.T_eq, sum_comm]
  refine sum_congr rfl fun j hj => ?_
  rw [mul_sum]
  refine sum_congr rfl fun hk hh => ?_
  show Blocks.eqN P.D.lT 0 _ j * (Blocks.eqN P.D.lg P.D.lT _ hk *
    ρ.val ((kcTab P.g w rho lam).getD (j * 2 ^ P.g.lgk + hk) zeroE)) = _
  rw [read_kcTab ρ H w Q lam (mem_range.mp hj) (mem_range.mp hh)]
  unfold conN
  rw [Cb.Pv.Att.eqN_sh, mul_sum, mul_sum]
  exact sum_congr rfl fun n _ => by ring

include H in
/-- **IBP of pair b and cell k, at any such point, reads as the library's rule value.** No bound is
asked of b: the summand's text reads any pair's cells. CONDITIONAL on Sized. -/
theorem ibp_reads {x : List E} (hx : x.length = g18 P.D) (b : ℕ) {k : ℕ} (hk : k < P.D.lT) :
    ρ.val ((sdOf P.g w rho om').endAt x (P.g.Lam + b * P.g.lt + k)) =
      rvIBP P.D (tOf ρ w) (ptL ρ x) b k := by
  rw [sd_endAt_ib P.g w rho om' x b (by rw [H.lt]; exact hk),
    read_ibpAt ρ P.g w (by rw [List.size_toArray]; exact sd_len H hx), ← ptL_eq ρ x]
  unfold ibF rvIBP rd2 eqT
  rw [H.lt, P.D.T_eq]
  refine sum_congr rfl fun hk _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [Cb.Pv.Att.eqN_sh, Cb.Pv.Att.eqN_sh]
  show Blocks.eqN P.D.lg P.D.lT _ hk * (Blocks.eqN P.D.lT (P.D.lT + P.D.lg) _ i *
    ρ.val (w.ibit k b hk i)) = _
  rw [read_ibit]
  ring

include H Q in
/-- The coefficient's text, at a point of any length. -/
theorem sdCoef_reads {x : List E} {b : ℕ} (hb : b < P.D.nb) :
    ρ.val (sdCoef P.g rho om' x.toArray b) =
      eqPt P.D.lT p.fi (sh (ptL ρ x) (P.D.lT + P.D.lg)) * eqPt P.D.lg p.fg (sh (ptL ρ x) P.D.lT) *
        p.o' b := by
  have s1 : (rho.extract 0 P.g.lt).size = P.D.lT := by
    rw [size_extract_le rho (by rw [Q.size, H.lt]; omega), H.lt]
    omega
  have s2 : (rho.extract P.g.lt (P.g.lt + P.g.lgk)).size = P.D.lg := by
    rw [size_extract_le rho (by
      rw [Q.size, H.lt]
      show P.D.lT + P.D.lg ≤ _
      omega)]
    show P.g.lt + P.D.lg - P.g.lt = P.D.lg
    omega
  rw [read_sdCoef ρ P.g rho om', ← ptL_eq ρ x]
  unfold coF
  rw [s1, s2, show ρ.val (om'.getD b zeroE) = p.o' b from Q.o' b hb, H.lt,
    OnBytes.Road.Rows.eqPt_agree (u' := p.fi) (fun k hk => by
      rw [pt_extract ρ rho 0 _ k (by omega), Nat.zero_add]
      exact Q.fi k hk) fun _ _ => rfl,
    OnBytes.Road.Rows.eqPt_agree (n := P.D.lg) (u' := p.fg) (fun k hk => by
      rw [pt_extract ρ rho _ _ k (by
        show P.D.lT + k < P.D.lT + P.D.lg
        omega)]
      exact Q.fg k hk) fun _ _ => rfl]
  rfl

include H Q in
/-- The coefficient of pair b, at a point of any length. -/
theorem coef_reads {x : List E} {b : ℕ} (hb : b < P.D.nb) :
    ρ.val ((sdOf P.g w rho om').coefAt b x) =
      eqPt P.D.lT p.fi (sh (ptL ρ x) (P.D.lT + P.D.lg)) * eqPt P.D.lg p.fg (sh (ptL ρ x) P.D.lT) *
        p.o' b := by
  unfold Summand.coefAt
  rw [sd_termAt P.g w rho om' x hb]
  exact sdCoef_reads ρ H Q hb

include H Q in
/-- The first factor's text. -/
theorem facKc_reads {x : List E} (hx : x.length = g18 P.D) {b : ℕ} (hb : b < P.D.nb) :
    ρ.val ((sdOf P.g w rho om').factorAt x ⟨oneE, b / P.g.HA, zeroE⟩) =
      rvKC P.D p (tOf ρ w) (ptL ρ x) (P.D.lamOf b) := by
  rw [read_bare]
  exact kc_reads ρ H w Q hx (sd_layer P.g hb)

include H in
/-- A bit's factor's text. -/
theorem facBit_reads {x : List E} (hx : x.length = g18 P.D) (b : ℕ) {k : ℕ} (hk : k < P.D.lT) :
    ρ.val ((sdOf P.g w rho om').factorAt x (sdBit P.g x.toArray b k)) =
      Ebk P.D (ptL ρ x) (rvIBP P.D (tOf ρ w) (ptL ρ x) b k) k := by
  have hk' : k < P.g.lt := by rw [H.lt]; exact hk
  have e : ρ.val ((x.toArray.extract 0 P.g.lt).getD (P.g.lt - 1 - k) zeroE) =
      ptL ρ x (P.D.lT - 1 - k) := by
    have := pt_extract ρ x.toArray 0 P.g.lt (P.g.lt - 1 - k) (by omega)
    rw [Nat.zero_add, ← ptL_eq ρ x] at this
    rw [← H.lt]
    exact this
  rw [read_factorAt]
  show ρ.val (subE (addE _ _) oneE) *
    ρ.val ((sdOf P.g w rho om').endAt x (P.g.Lam + b * P.g.lt + k)) + ρ.val (subE oneE _) = _
  rw [ibp_reads ρ H w hx b hk, ρ.sub, ρ.add, ρ.sub, ρ.one, e]
  unfold Ebk
  ring

include H Q in
/-- The first factor of pair b's term is KC of the pair's layer. -/
theorem fac_zero_reads {x : List E} (hx : x.length = g18 P.D) {b : ℕ} (hb : b < P.D.nb) :
    ρ.val ((sdOf P.g w rho om').facAt b 0 x) =
      rvKC P.D p (tOf ρ w) (ptL ρ x) (P.D.lamOf b) := by
  unfold Summand.facAt
  rw [sd_termAt P.g w rho om' x hb]
  exact facKc_reads ρ H w Q hx hb

include H in
/-- Factor k + 1 of pair b's term is the library's E_(b,k) on IBP_(b,k). -/
theorem fac_succ_reads {x : List E} (hx : x.length = g18 P.D) {b : ℕ} (hb : b < P.D.nb) {k : ℕ}
    (hk : k < P.D.lT) :
    ρ.val ((sdOf P.g w rho om').facAt b (k + 1) x) =
      Ebk P.D (ptL ρ x) (rvIBP P.D (tOf ρ w) (ptL ρ x) b k) k := by
  unfold Summand.facAt
  rw [sd_termAt P.g w rho om' x hb]
  show ρ.val ((sdOf P.g w rho om').factorAt x
    (((List.range P.g.lt).map (sdBit P.g x.toArray b)).getD k _)) = _
  rw [SD.getD_map_range, if_pos (by rw [H.lt]; exact hk)]
  exact facBit_reads ρ H w hx b hk

include H Q in
/-- **The summand at ANY point of the sumcheck's length reads as the library's summand of step 18.**
CONDITIONAL on Sized and KeyPub. -/
theorem sd_at {x : List E} (hx : x.length = g18 P.D) :
    ρ.val ((sdOf P.g w rho om').at x) = Phi18 P.D p (tOf ρ w) (ptL ρ x) := by
  rw [Summand.read_at]
  show (((List.range P.D.nb).map fun b => (⟨sdCoef P.g rho om' x.toArray b,
    ⟨oneE, b / P.g.HA, zeroE⟩ :: (List.range P.g.lt).map (sdBit P.g x.toArray b)⟩ : Term)).map
      _).sum = _
  rw [List.map_map, sum_list_range]
  unfold Phi18
  rw [mul_sum]
  refine sum_congr rfl fun b hb => ?_
  have hb' := mem_range.mp hb
  show ρ.val (sdCoef P.g rho om' x.toArray b) *
    ((⟨oneE, b / P.g.HA, zeroE⟩ :: (List.range P.g.lt).map (sdBit P.g x.toArray b)).map
      fun f => ρ.val ((sdOf P.g w rho om').factorAt x f)).prod = _
  have e1 : ∏ k ∈ range P.D.lT, ((fun f => ρ.val ((sdOf P.g w rho om').factorAt x f)) ∘
      sdBit P.g x.toArray b) k =
      ∏ k ∈ range P.D.lT, Ebk P.D (ptL ρ x) (rvIBP P.D (tOf ρ w) (ptL ρ x) b k) k :=
    prod_congr rfl fun k hk => facBit_reads ρ H w hx b (mem_range.mp hk)
  have e2 : ∏ k ∈ range P.D.lT, eq1 (Blocks.ext (P.D.lg + P.D.lT)
      (fun X => ibV (tOf ρ w) k b (X / P.D.T) (X % P.D.T)) (sh (ptL ρ x) P.D.lT))
      (ptL ρ x (P.D.lT - 1 - k)) =
      ∏ k ∈ range P.D.lT, Ebk P.D (ptL ρ x) (rvIBP P.D (tOf ρ w) (ptL ρ x) b k) k :=
    prod_congr rfl fun k _ => by
      rw [← Cb.Pv.Att.rvIBP_ext]
      unfold eq1 Ebk
      ring
  rw [List.map_cons, List.prod_cons, List.map_map, prod_list_range, sdCoef_reads ρ H Q hb',
    facKc_reads ρ H w Q hx hb', H.lt, ← Cb.Pv.Att.rvKC_ext, e1, e2]
  ring

include H Q in
/-- **The sum over the cube reads as the sum of the library's summand over its vertices.**
CONDITIONAL on Sized and KeyPub. -/
theorem sd_total : ρ.val (sdOf P.g w rho om').total =
    ∑ X ∈ range (2 ^ g18 P.D), Phi18 P.D p (tOf ρ w) (Blocks.cubePt (g18 P.D) X) := by
  have hv : (sdOf P.g w rho om').vars = g18 P.D := by
    show 2 * P.g.lt + P.g.lgk = P.D.lT + P.D.lg + P.D.lT
    rw [H.lt]
    show 2 * P.D.lT + P.D.lg = _
    omega
  rw [Summand.read_total, hv, sum_cube]
  refine sum_congr rfl fun X _ => ?_
  rw [sd_at ρ H w Q (vertex_length _ X), ptL_eq ρ (vertex _ X), pt_vertex_eq]

include H Q in
/-- **The sum is the batch of the second maps of the score at the index, at rho.** Algebra at every
cell: no cell is asked to be a bit. CONDITIONAL on Sized and KeyPub. -/
theorem sd_start (c : Chal) : ρ.val (sdOf P.g w rho om').total =
    ∑ b ∈ range P.g.NP, ρ.val (om'.getD b zeroE) *
      ρ.val ((sSF P w c).endAt rho.toList (2 * b + 1)) := by
  rw [sd_total ρ H w Q]
  refine (Cb.Pv.Att.keyMean K P.D ⟨fun _ => 0, 0, 0⟩ p (tOf ρ w)).trans ?_
  refine sum_congr rfl fun b hb => ?_
  have hb' : b < P.g.NP := mem_range.mp hb
  rw [sSF_endAt P w c rho.toList (by omega), Array.toArray_toList,
    sfB_reads ρ H w ⟨fun _ => 0, 0, 0⟩ p Q.size b, ← Q.o' b hb']
  refine congrArg (pt ρ om' b * ·) ?_
  unfold Bext
  refine Blocks.ext_congr_point (fun t ht => ?_) _
  have ht' : t < P.D.lT + P.D.lg + P.D.ln := ht
  unfold cat
  by_cases h1 : t < P.D.lT
  · rw [if_pos h1, Q.fi t h1]
  · rw [if_neg h1]
    by_cases h2 : t - P.D.lT < P.D.lg
    · rw [if_pos h2, ← Q.fg _ h2]
      congr 1
      omega
    · rw [if_neg h2, ← Q.fn _ (by omega)]
      congr 1
      omega

end Lib

/-- **The same of the prover's own summand**, CONDITIONAL on: Sized; the verifier's function of the
points returns at the challenges so far; the planner's number of variables of the score at the index
is the library's. -/
theorem sSD_start {P : Pub5} (H : Sized P) (w : K5In) {c : Chal} (hp : (ptsOf P c).isSome = true)
    (hv : (cut P.x).getD (iSF P.x) 3 - 3 = Step.s16.g P.D) :
    ρ.val (sSD P w c).total = ∑ b ∈ range P.g.NP, ρ.val ((om4Of P c).getD b zeroE) *
      ρ.val ((sSF P w c).endAt (rhoOf P c).toList (2 * b + 1)) := by
  rw [sSD_eq]
  exact sd_start ρ H w (keyPub_of ρ (fun _ => 0) hp hv) c

end H2K5.Honest

#print axioms H2K5.Honest.sSD_eq
#print axioms H2K5.Honest.SD.getD_map_range
#print axioms H2K5.Honest.sd_termAt
#print axioms H2K5.Honest.sd_termAt_beyond
#print axioms H2K5.Honest.sd_endAt_kc
#print axioms H2K5.Honest.sd_endAt_ib
#print axioms H2K5.Honest.sd_layer
#print axioms H2K5.Honest.sd_below
#print axioms H2K5.Honest.named_sdOf
#print axioms H2K5.Honest.aff_kcF
#print axioms H2K5.Honest.free_kcF
#print axioms H2K5.Honest.aff_ibF
#print axioms H2K5.Honest.free_ibF
#print axioms H2K5.Honest.aff_coF
#print axioms H2K5.Honest.free_coF
#print axioms H2K5.Honest.aff_bitF
#print axioms H2K5.Honest.free_bitF
#print axioms H2K5.Honest.ptL_eq
#print axioms H2K5.Honest.read_eqPts
#print axioms H2K5.Honest.read_kcAt
#print axioms H2K5.Honest.read_ibpAt
#print axioms H2K5.Honest.read_sdCoef
#print axioms H2K5.Honest.size_rg_le
#print axioms H2K5.Honest.read_fac_kc
#print axioms H2K5.Honest.read_fac_bit
#print axioms H2K5.Honest.rhoOf_eq
#print axioms H2K5.Honest.keyPub_of
#print axioms H2K5.Honest.sd_len
#print axioms H2K5.Honest.read_kcTab
#print axioms H2K5.Honest.kc_reads
#print axioms H2K5.Honest.ibp_reads
#print axioms H2K5.Honest.sdCoef_reads
#print axioms H2K5.Honest.coef_reads
#print axioms H2K5.Honest.facKc_reads
#print axioms H2K5.Honest.facBit_reads
#print axioms H2K5.Honest.fac_zero_reads
#print axioms H2K5.Honest.fac_succ_reads
#print axioms H2K5.Honest.sd_at
#print axioms H2K5.Honest.sd_total
#print axioms H2K5.Honest.sd_start
#print axioms H2K5.Honest.sSD_start
