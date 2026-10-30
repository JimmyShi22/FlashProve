-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lookup/Rider/ForBCalls.lean: the riders of the lookup of a sub-proof, stated in the
arrays that a caller holds: the first part of the key point (zx) and a call's key point (zk).

Definitions, statements and proofs. No protocol of its own. The term, its joints and the rule are
those of OnBytes/Tie/Pv/Lookup/Rider/ForB.lean. A caller need not know how the output statement
numbers its point.

Main names:
  `outRho h b`: the v' + 1 places of the point of the claim on the keys in forB's output statement
    b, as a list; place 0 belongs to the top bit, as `Blocks.ext` reads its point.
  `outZx h b`: its first dT places. `outZy h b`: the rK places behind them. `outZk h iota b`: the
    last iota places of outZy, then outZx: the key point of a call whose trees' numbers have iota
    bits. All three are made by `List.take`, `List.drop` and `++` alone.
  `outRho_at`, `outZx_at`, `outZy_at`, `outZk_at`: their places as places of pt.
  `forB_rider_zk`: as `forB_rider`, each member i of the family with its own iota i ≤ rK and its own
    choice of different places sel i t < iota i + dT of outZk h (iota i) b.
  `forB_rider_zx`: each member with its own choice of different places sel i t < dT of outZx h b.
  `oneHot_zx`: nE maps sum to 1 at every vertex; tested at the last lt places of outZx.
  `two_lines_zx`: two conditions with a public indicator; tested at the same places.
  `denom_zk`: a denominator equals a row sum over tiles; tested at the places callIx nb t of outZk:
    the first nb + lgk + lt + 1 places of a call's key point but place nb.
  `forB_rider_zk_in`, `forB_rider_zx_in`, `oneHot_zx_in`, `two_lines_zx_in`, `denom_zk_in`: the same
    with the source laid inside R0 at the input alone (`forIn_in`): the form that meets a joint
    before the block whose R0 carries the source.
In each, forB's own `KnowAt` at R0 without the source is a premise hK, used as a black box;
reduction, extractor and counts are hK's.

These are statements of form. Every map is a free letter: any function of the caller's state and the
tuple of messages. None has an inhabitant or a test against emptiness of its own here.

Limits: R0 is free in every statement and comes out as it went in. If R0, or the in-joint's own
claim, gives the source, the statement follows from hK alone and says nothing (`forB_hollow`). The
two sentences named in ForB.lean's head are owed for each use: neither is proved at this term for
any value. The forms with _in guard against the source coming out again inside R0, and against
nothing else. Nothing on whether the programs' tests are these targets, on which caller uses which
pick, on whether a later stage takes a target up, or on an honest prover.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.Tie.Pv.Lookup.Rider.ForBUses

set_option autoImplicit false

namespace Cb.Rider
open Iop Prob Cb Blocks Cb.LdLkp Cb.LdLkp.Kn TWhole Cb.Fo Finset

/-! ## 1. Lists -/

section Lists
variable {α : Type} (d : α)

theorem take_at (dT : ℕ) (ρ : List α) {j : ℕ} (hj : j < dT) :
    (ρ.take dT).getD j d = ρ.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hj]

theorem drop_at (dT : ℕ) (ρ : List α) (u : ℕ) : (ρ.drop dT).getD u d = ρ.getD (dT + u) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- The last iota of the places behind the first dT, then the first dT, read through keyIx. -/
theorem call_at (dT rK iota : ℕ) (hi : iota ≤ rK) (ρ : List α) (hρ : ρ.length = dT + rK) {j : ℕ}
    (hj : j < iota + dT) :
    (((ρ.drop dT).drop (rK - iota)) ++ ρ.take dT).getD j d = ρ.getD (keyIx dT rK iota j) d := by
  have hl : ((ρ.drop dT).drop (rK - iota)).length = iota := by
    rw [List.length_drop, List.length_drop, hρ]
    omega
  unfold keyIx
  split
  · next h1 =>
    rw [List.getD_append _ _ _ _ (by rw [hl]; exact h1)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    congr 2
    omega
  · next h1 =>
    rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl]
    exact take_at d dT ρ (by omega)

end Lists

theorem keyIx_lt {dT rK iota j : ℕ} (hi : iota ≤ rK) (hj : j < iota + dT) :
    keyIx dT rK iota j < dT + rK := by
  unfold keyIx
  split <;> omega

theorem keyIx_inj {dT rK iota j j' : ℕ} (hi : iota ≤ rK) (hj : j < iota + dT)
    (hj' : j' < iota + dT) (e : keyIx dT rK iota j = keyIx dT rK iota j') : j = j' := by
  unfold keyIx at e
  split_ifs at e <;> omega

/-! ## 2. The arrays off the output statement -/

section Arrays
variable {E St J : Type} [Field E]

/-- The point of the claim on the keys, as a list of v' + 1 places. -/
def outRho (h : Sh) (b : TX St E J) : List E :=
  List.ofFn fun i : Fin (FoNums.v' h + 1) => b.2.1.pt i
/-- Its first dT places. -/
def outZx (h : Sh) (b : TX St E J) : List E := (outRho h b).take h.dT
/-- The places behind them. -/
def outZy (h : Sh) (b : TX St E J) : List E := (outRho h b).drop h.dT
/-- The key point of a call whose trees' numbers have iota bits: the last iota places of outZy, then
outZx. -/
def outZk (h : Sh) (iota : ℕ) (b : TX St E J) : List E :=
  (outZy h b).drop (h.rK - iota) ++ outZx h b

omit [Field E] in
theorem outRho_len (h : Sh) (b : TX St E J) : (outRho h b).length = FoNums.v' h + 1 :=
  List.length_ofFn

theorem outRho_at (h : Sh) (b : TX St E J) {i : ℕ} (hi : i ≤ FoNums.v' h) :
    (outRho h b).getD i 0 = b.2.1.pt i := by
  unfold outRho
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; omega), List.getElem_ofFn]

theorem outZx_at (h : Sh) (b : TX St E J) {j : ℕ} (hj : j < h.dT) :
    (outZx h b).getD j 0 = b.2.1.pt j := by
  have h1 := sh_dT_le h
  rw [← outRho_at h b (i := j) (by omega)]
  exact take_at 0 h.dT _ hj

theorem outZy_at (h : Sh) (hv : 1 ≤ h.v) (b : TX St E J) {u : ℕ} (hu : u < h.rK) :
    (outZy h b).getD u 0 = b.2.1.pt (h.dT + u) := by
  have h2 := sh_v_eq hv
  rw [← outRho_at h b (i := h.dT + u) (by omega)]
  exact drop_at 0 h.dT _ u

theorem outZk_at (h : Sh) (hv : 1 ≤ h.v) (b : TX St E J) {iota j : ℕ} (hi : iota ≤ h.rK)
    (hj : j < iota + h.dT) :
    (outZk h iota b).getD j 0 = b.2.1.pt (keyIx h.dT h.rK iota j) := by
  have h1 := keyIx_lt hi hj
  have h2 := sh_v_eq hv
  rw [← outRho_at h b (i := keyIx h.dT h.rK iota j) (by omega)]
  exact call_at 0 h.dT h.rK iota hi _ (by rw [outRho_len, h2]) hj

end Arrays

section Rule
variable {E : Type} [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]
  {h : Sh} {L : Lay E St₀ J₀} {Ex : ExtSpec} {Kc M Wp : Type} {R0 : IOR.Rels Kc St₀ Ex (M × Wp)}
  {msg₀ : M → J₀ → E}

/-! ## 3. The rule in a caller's arrays -/

/-- The rule, at calls' key points. Member i of the family is tested at its own choice of different
places sel i t < iota i + dT of the key point of a call with iota i ≤ rK. Source: each array f i,
read off the caller's state and the tuple of messages, is 0 at every vertex of its cube of dimension
g i. Target: its multilinear extension is 0 at those places. Asked of h: the point has at least one
place. Warning: R0 is free and comes out as it went in (forB_hollow). -/
theorem forB_rider_zk
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e)
    (hv : 1 ≤ h.v) {ι : Type} (g : ι → ℕ) (iota : ι → ℕ) (hio : ∀ i, iota i ≤ h.rK)
    (sel : ι → ℕ → ℕ)
    (hsel : ∀ i, (∀ t < g i, ∀ t' < g i, sel i t = sel i t' → t = t') ∧
      ∀ t < g i, sel i t < iota i + h.dT)
    (f : ι → St₀ → M → ℕ → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (withRider (forIn E h L R0 msg₀) fun m a => OnCubes g f a.1 m)
      (withRider (forOut E h L R0 msg₀) fun m b =>
        ∀ i, ext (g i) (f i b.1.1.1 m) (fun t => (outZk h (iota i) b.1).getD (sel i t) 0) = 0)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e := by
  have G := forB_rider hK g (fun i t => keyIx h.dT h.rK (iota i) (sel i t))
    (fun i => ⟨fun t ht t' ht' e => (hsel i).1 t ht t' ht'
        (keyIx_inj (hio i) ((hsel i).2 t ht) ((hsel i).2 t' ht') e),
      fun t ht => by
        have h1 := keyIx_lt (hio i) ((hsel i).2 t ht)
        have h2 := sh_v_eq hv
        show keyIx h.dT h.rK (iota i) (sel i t) ≤ FoNums.v' h
        omega⟩) f
  refine knowAt_congr_rider (fun _ _ => Iff.rfl) (fun m b => forall_congr' fun i => ?_) G
  exact Eq.congr_left (ext_congr_point (g := g i)
    (z := fun t => b.1.2.1.pt (keyIx h.dT h.rK (iota i) (sel i t)))
    (z' := fun t => (outZk h (iota i) b.1).getD (sel i t) 0)
    (fun t ht => (outZk_at h hv b.1 (hio i) ((hsel i).2 t ht)).symm) (f i b.1.1.1 m))

/-- The rule, at the first part of the key point. Member i is tested at its own choice of different
places sel i t < dT of outZx. No premise on h. Warning: R0 is free and comes out as it went in
(forB_hollow). -/
theorem forB_rider_zx
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e)
    {ι : Type} (g : ι → ℕ) (sel : ι → ℕ → ℕ)
    (hsel : ∀ i, (∀ t < g i, ∀ t' < g i, sel i t = sel i t' → t = t') ∧ ∀ t < g i, sel i t < h.dT)
    (f : ι → St₀ → M → ℕ → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (withRider (forIn E h L R0 msg₀) fun m a => OnCubes g f a.1 m)
      (withRider (forOut E h L R0 msg₀) fun m b =>
        ∀ i, ext (g i) (f i b.1.1.1 m) (fun t => (outZx h b.1).getD (sel i t) 0) = 0)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e := by
  have G := forB_rider hK g sel
    (fun i => ⟨(hsel i).1, fun t ht => by
      have h1 := (hsel i).2 t ht
      have h2 := sh_dT_le h
      omega⟩) f
  refine knowAt_congr_rider (fun _ _ => Iff.rfl) (fun m b => forall_congr' fun i => ?_) G
  exact Eq.congr_left (ext_congr_point (g := g i) (z := fun t => b.1.2.1.pt (sel i t))
    (z' := fun t => (outZx h b.1).getD (sel i t) 0)
    (fun t ht => (outZx_at h b.1 ((hsel i).2 t ht)).symm) (f i b.1.1.1 m))

/-! ## 4. The three shapes in a caller's arrays -/

/-- "The entries sum to 1 at every vertex", for each member of a family, tested at the last lt
places of outZx. Warning: R0 is free (forB_hollow). -/
theorem oneHot_zx
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e)
    {Lm : Type} (lt nE : ℕ) (hlt : lt ≤ h.dT) (sl : Lm → St₀ → M → Fin nE → ℕ → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (withRider (forIn E h L R0 msg₀) fun m a => ∀ lm, ∀ X < 2 ^ lt, ∑ k, sl lm a.1 m k X = 1)
      (withRider (forOut E h L R0 msg₀) fun m b =>
        ∀ lm, ∑ k, ext lt (sl lm b.1.1.1 m k)
          (fun t => (outZx h b.1).getD (h.dT - lt + t) 0) = 1)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e := by
  refine knowAt_congr_rider (fun _ _ => Iff.rfl) (fun m b => forall_congr' fun lm => ?_)
    (oneHot_forB hK lt nE hlt sl)
  refine Eq.congr_left (Finset.sum_congr rfl fun k _ => ?_)
  exact ext_congr_point (fun t ht => (outZx_at h b.1 (j := h.dT - lt + t) (by omega)).symm) _

/-- Two conditions with a public indicator, tested at the last lt places of outZx. These are the
last lt places of every call's key point outZk too. A test that reads lt places of a call's key
point from place lJ on reads these places if and only if that point has lJ + lt places; otherwise
forB_rider_zk serves. [An argument in words; no theorem here.] Warning: R0 is free (forB_hollow). If
no vertex counts the rider says nothing (two_lines_none). -/
theorem two_lines_zx
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e)
    (lt : ℕ) (hlt : lt ≤ h.dT) (cost : St₀ → ℕ → Bool) (l3 l4 : St₀ → M → ℕ → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (withRider (forIn E h L R0 msg₀) fun m a =>
        ∀ X < 2 ^ lt, cost a.1 X = true → l3 a.1 m X = 0 ∧ l4 a.1 m X = 0)
      (withRider (forOut E h L R0 msg₀) fun m b =>
        ext lt (fun X => if cost b.1.1.1 X = true then l3 b.1.1.1 m X else 0)
            (fun t => (outZx h b.1).getD (h.dT - lt + t) 0) = 0 ∧
          ext lt (fun X => if cost b.1.1.1 X = true then l4 b.1.1.1 m X else 0)
            (fun t => (outZx h b.1).getD (h.dT - lt + t) 0) = 0)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e := by
  refine knowAt_congr_rider (fun _ _ => Iff.rfl) (fun m b => ?_)
    (two_lines_forB hK lt hlt cost l3 l4)
  have e : ∀ v : ℕ → E, ext lt v (fun t => b.1.2.1.pt (h.dT - lt + t)) =
      ext lt v (fun t => (outZx h b.1).getD (h.dT - lt + t) 0) := fun v =>
    ext_congr_point (fun t ht => (outZx_at h b.1 (j := h.dT - lt + t) (by omega)).symm) v
  rw [e, e]

/-- "The denominator is the row sum at every block, head and position", tested at the places callIx
nb t, t < nb + lgk + lt, of the key point of a call with iota ≤ rK: place nb is skipped. The
indicator marks the blocks 0, .., NP - 1, numbered by the cube's top nb bits: it is on a use that
its pieces stand at these numbers; otherwise forB_rider_zk, whose arrays are free, serves. Warning:
R0 is free (forB_hollow). -/
theorem denom_zk
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e)
    (hv : 1 ≤ h.v) (iota nb lgk lt ldh nS nT B NP : ℕ) (h1 : iota ≤ h.rK)
    (hb : nb + 1 + lgk + lt + ldh = h.dT + iota) (hN : NP ≤ 2 ^ nb)
    (rowOf : ℕ → ℕ → ℕ) (den : St₀ → M → ℕ → ℕ → ℕ → E)
    (wtM : St₀ → M → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E) (wtD : St₀ → M → ℕ → ℕ → ℕ → ℕ → ℕ → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (withRider (forIn E h L R0 msg₀) fun m a =>
        ∀ P < NP, ∀ g < 2 ^ lgk, ∀ i < 2 ^ lt,
          den a.1 m P g i = rowSumA nS nT B rowOf wtM wtD a.1 m P g i)
      (withRider (forOut E h L R0 msg₀) fun m b =>
        ext (nb + lgk + lt) (onPieces lgk lt NP (den b.1.1.1 m))
            (fun t => (outZk h iota b.1).getD (callIx nb t) 0) =
          ext (nb + lgk + lt) (onPieces lgk lt NP (rowSumA nS nT B rowOf wtM wtD b.1.1.1 m))
            (fun t => (outZk h iota b.1).getD (callIx nb t) 0))
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e := by
  refine knowAt_congr_rider (fun _ _ => Iff.rfl) (fun m b => ?_)
    (denom_forB hK hv iota nb lgk lt ldh nS nT B NP h1 hb hN rowOf den wtM wtD)
  have e : ∀ v : ℕ → E, ext (nb + lgk + lt) v (fun t => b.1.2.1.pt (selAtt h.dT h.rK iota nb t)) =
      ext (nb + lgk + lt) v (fun t => (outZk h iota b.1).getD (callIx nb t) 0) := fun v =>
    ext_congr_point (fun t ht => (outZk_at h hv b.1 h1 (by
      unfold callIx
      split <;> omega)).symm) v
  rw [e, e]

/-! ## 5. The same, the source laid inside R0 at the input alone -/

/-- forB_rider_zk with the source inside R0 at the input alone. -/
theorem forB_rider_zk_in
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e)
    (hv : 1 ≤ h.v) {ι : Type} (g : ι → ℕ) (iota : ι → ℕ) (hio : ∀ i, iota i ≤ h.rK)
    (sel : ι → ℕ → ℕ)
    (hsel : ∀ i, (∀ t < g i, ∀ t' < g i, sel i t = sel i t' → t = t') ∧
      ∀ t < g i, sel i t < iota i + h.dT)
    (f : ι → St₀ → M → ℕ → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (forIn E h L (withRider R0 fun m a => OnCubes g f a.1 m) msg₀)
      (withRider (forOut E h L R0 msg₀) fun m b =>
        ∀ i, ext (g i) (f i b.1.1.1 m) (fun t => (outZk h (iota i) b.1).getD (sel i t) 0) = 0)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e :=
  forIn_in (forB_rider_zk hK hv g iota hio sel hsel f)

/-- forB_rider_zx with the source inside R0 at the input alone. -/
theorem forB_rider_zx_in
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e)
    {ι : Type} (g : ι → ℕ) (sel : ι → ℕ → ℕ)
    (hsel : ∀ i, (∀ t < g i, ∀ t' < g i, sel i t = sel i t' → t = t') ∧ ∀ t < g i, sel i t < h.dT)
    (f : ι → St₀ → M → ℕ → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (forIn E h L (withRider R0 fun m a => OnCubes g f a.1 m) msg₀)
      (withRider (forOut E h L R0 msg₀) fun m b =>
        ∀ i, ext (g i) (f i b.1.1.1 m) (fun t => (outZx h b.1).getD (sel i t) 0) = 0)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e :=
  forIn_in (forB_rider_zx hK g sel hsel f)

/-- oneHot_zx with the source inside R0 at the input alone. -/
theorem oneHot_zx_in
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e)
    {Lm : Type} (lt nE : ℕ) (hlt : lt ≤ h.dT) (sl : Lm → St₀ → M → Fin nE → ℕ → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (forIn E h L (withRider R0 fun m a => ∀ lm, ∀ X < 2 ^ lt, ∑ k, sl lm a.1 m k X = 1) msg₀)
      (withRider (forOut E h L R0 msg₀) fun m b =>
        ∀ lm, ∑ k, ext lt (sl lm b.1.1.1 m k)
          (fun t => (outZx h b.1).getD (h.dT - lt + t) 0) = 1)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e :=
  forIn_in (oneHot_zx hK lt nE hlt sl)

/-- two_lines_zx with the source inside R0 at the input alone. -/
theorem two_lines_zx_in
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e)
    (lt : ℕ) (hlt : lt ≤ h.dT) (cost : St₀ → ℕ → Bool) (l3 l4 : St₀ → M → ℕ → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (forIn E h L (withRider R0 fun m a =>
        ∀ X < 2 ^ lt, cost a.1 X = true → l3 a.1 m X = 0 ∧ l4 a.1 m X = 0) msg₀)
      (withRider (forOut E h L R0 msg₀) fun m b =>
        ext lt (fun X => if cost b.1.1.1 X = true then l3 b.1.1.1 m X else 0)
            (fun t => (outZx h b.1).getD (h.dT - lt + t) 0) = 0 ∧
          ext lt (fun X => if cost b.1.1.1 X = true then l4 b.1.1.1 m X else 0)
            (fun t => (outZx h b.1).getD (h.dT - lt + t) 0) = 0)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e :=
  forIn_in (two_lines_zx hK lt hlt cost l3 l4)

/-- denom_zk with the source inside R0 at the input alone. -/
theorem denom_zk_in
    (hK : KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R (forIn E h L R0 msg₀) (forOut E h L R0 msg₀)
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e)
    (hv : 1 ≤ h.v) (iota nb lgk lt ldh nS nT B NP : ℕ) (h1 : iota ≤ h.rK)
    (hb : nb + 1 + lgk + lt + ldh = h.dT + iota) (hN : NP ≤ 2 ^ nb)
    (rowOf : ℕ → ℕ → ℕ) (den : St₀ → M → ℕ → ℕ → ℕ → E)
    (wtM : St₀ → M → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E) (wtD : St₀ → M → ℕ → ℕ → ℕ → ℕ → ℕ → E) :
    KnowAt (forB E h L V₀ V₀C (Ex := Ex)).R
      (forIn E h L (withRider R0 fun m a =>
        ∀ P < NP, ∀ g < 2 ^ lgk, ∀ i < 2 ^ lt,
          den a.1 m P g i = rowSumA nS nT B rowOf wtM wtD a.1 m P g i) msg₀)
      (withRider (forOut E h L R0 msg₀) fun m b =>
        ext (nb + lgk + lt) (onPieces lgk lt NP (den b.1.1.1 m))
            (fun t => (outZk h iota b.1).getD (callIx nb t) 0) =
          ext (nb + lgk + lt) (onPieces lgk lt NP (rowSumA nS nT B rowOf wtM wtD b.1.1.1 m))
            (fun t => (outZk h iota b.1).getD (callIx nb t) 0))
      (fun _ _ _ wp => wp) (forB E h L V₀ V₀C (Ex := Ex)).e :=
  forIn_in (denom_zk hK hv iota nb lgk lt ldh nS nT B NP h1 hb hN rowOf den wtM wtD)

end Rule

end Cb.Rider

#print axioms Cb.Rider.call_at
#print axioms Cb.Rider.forB_rider_zk
#print axioms Cb.Rider.forB_rider_zx
#print axioms Cb.Rider.oneHot_zx
#print axioms Cb.Rider.two_lines_zx
#print axioms Cb.Rider.denom_zk
#print axioms Cb.Rider.forB_rider_zk_in
#print axioms Cb.Rider.forB_rider_zx_in
#print axioms Cb.Rider.oneHot_zx_in
#print axioms Cb.Rider.two_lines_zx_in
#print axioms Cb.Rider.denom_zk_in
