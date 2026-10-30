-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttInj.lean

FOR EVERY SHAPE that the verifier's function shape returns, with at least one part of "as": the rule
of addresses "addrA" (Johnson/Road/Lane5AttDef.lean) is one-to-one on the names that are valid at
the sizes dimOf S: no two cells of the attention segment have one triple (number in the list, row,
column). That the triple lies inside the matrix of that number in the verifier's list is
`addr_inside` (Johnson/Desc/K5/Honest/Law/AddrIn.lean), at a shape that `shapeHid` returns, under
public premises: MatsFit, ColsFit, a part of "as", a feature column in ah. The condition
"at least one part" is no test of shape: the verifier makes it in config
(OnBytes/Model/AttentionConfig.lean); with no part all cells of "as" would have the list number of
ah.

* "asCell_inj", "featCell_inj": the last step of the rule (rows in a column) loses nothing.
* "Laid S": what the proof reads of a shape: Norm S (Johnson/Road/Lane5AttNum.lean); the library's
  number of positions is the shape's T; all cells of places fit into the parts of "as".
* "laid_of_shape": shape cf = .ok S and 0 < cf.NAs give it.
* "addrA_inj_laid", "addrA_inj": one-to-one.

Over the library's adr_inj and phi_inj (Inst/Model/Att/AddrFacts.lean), which hold at all sizes.
Who reads it: whoever carries a trace on valid names into a list of matrices
(Johnson/Road/Lane5AttList.lean).

Not here: the same for the record that shapeHid returns, which a plan of the verifier holds. It is
shape's record with two other fields set (kbA, calls), which addrA and dimOf do not read; "Laid" of
it follows from shaped_of_hid and the two tests as in laid_of_shape, but no theorem here says so.
-/
import Johnson.Road.Lane5AttNum

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model
open Inst.Model.AttSeg (Raw Mx)
open Inst.Model.AttSeg.AddrFacts (adr phi pos mat IsC SM SD)

/-- Two cell numbers of "as" with one place are one. -/
theorem asCell_inj (S : Attention.Shape) {n n' : ℕ} (h : asCell S n = asCell S n') : n = n' := by
  unfold asCell at h
  obtain ⟨h1, h⟩ := Prod.mk.inj h
  obtain ⟨h2, h3⟩ := Prod.mk.inj h
  have e : n / 2 ^ S.cf.lmS = n' / 2 ^ S.cf.lmS := by
    rw [← Nat.div_add_mod (n / 2 ^ S.cf.lmS) (S.kAs / S.cf.NAs),
      ← Nat.div_add_mod (n' / 2 ^ S.cf.lmS) (S.kAs / S.cf.NAs), h1, h3]
  rw [← Nat.div_add_mod n (2 ^ S.cf.lmS), ← Nat.div_add_mod n' (2 ^ S.cf.lmS), e, h2]

/-- Two features at positions below T with one place are one, and so are the positions. -/
theorem featCell_inj (S : Attention.Shape) {a a' wc φ φ' i i' : ℕ} (hi : i < S.T) (hi' : i' < S.T)
    (h : featCell S a wc φ i = featCell S a' wc φ' i') : φ = φ' ∧ i = i' := by
  unfold featCell at h
  obtain ⟨-, h⟩ := Prod.mk.inj h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  rw [Nat.mul_comm _ S.T, Nat.mul_comm _ S.T] at h1
  obtain ⟨h3, h4⟩ := AttSeg.AddrFacts.mr_inj hi hi' h1
  refine ⟨?_, h4⟩
  rw [← Nat.div_add_mod φ wc, ← Nat.div_add_mod φ' wc, h2, h3]

/-- The number in the list, and the features in a column, of a matrix of features. -/
def noOf (S : Attention.Shape) : Mx → ℕ
  | .ah => S.cf.NAs
  | .ao => S.cf.NAs + 1
  | _ => S.cf.NAs + 3

def wcOf (S : Attention.Shape) : Mx → ℕ
  | .ah => S.cf.wcH
  | .ao => S.cf.wcO
  | _ => S.cf.wcQ

theorem addrL_feat (S : Attention.Shape) (c : Raw) (hc : ¬ IsC c) :
    addrL S c = featCell S (noOf S (mat c)) (wcOf S (mat c)) (phi (dimOf S) c) (pos c) := by
  cases c <;> first | exact absurd trivial hc | rfl

theorem noOf_inj (S : Attention.Shape) {μ μ' : Mx} (h : μ = .ah ∨ μ = .ao ∨ μ = .qa)
    (h' : μ' = .ah ∨ μ' = .ao ∨ μ' = .qa) (e : noOf S μ = noOf S μ') : μ = μ' := by
  rcases h with rfl | rfl | rfl <;> rcases h' with rfl | rfl | rfl <;>
    first
    | rfl
    | (exfalso
       simp only [noOf] at e
       omega)

theorem noOf_ge (S : Attention.Shape) (μ : Mx) : S.cf.NAs ≤ noOf S μ := by
  cases μ <;> simp only [noOf] <;> omega

/-- What the proof reads of a shape. -/
structure Laid (S : Attention.Shape) : Prop where
  norm : Norm S
  T : (dimOf S).T = S.T
  wide : SM (dimOf S) + SD (dimOf S) ≤ 2 ^ S.cf.lmS * (S.kAs / S.cf.NAs * S.cf.NAs)

/-- A cell number below the room of the parts of "as" lies in one of the parts. -/
theorem asCell_no (S : Attention.Shape) {n : ℕ}
    (hn : n < 2 ^ S.cf.lmS * (S.kAs / S.cf.NAs * S.cf.NAs)) : (asCell S n).1 < S.cf.NAs :=
  Nat.div_lt_of_lt_mul (Nat.div_lt_of_lt_mul hn)

/-- **One-to-one on the valid names.** -/
theorem addrA_inj_laid {S : Attention.Shape} (L : Laid S) {c c' : Raw}
    (hv : c.Valid (dimOf S)) (hv' : c'.Valid (dimOf S)) (e : addrA S c = addrA S c') :
    c = c' := by
  rw [addrA_norm L.norm, addrA_norm L.norm] at e
  by_cases hc : IsC c <;> by_cases hc' : IsC c'
  · cases c with
    | c ρ jj b x =>
      cases c' with
      | c ρ' jj' b' x' =>
        exact AttSeg.AddrFacts.adr_inj (dimOf S) hv hv' (asCell_inj S e)
      | _ => exact absurd hc' (fun h => h)
    | _ => exact absurd hc (fun h => h)
  · cases c with
    | c ρ jj b x =>
      exfalso
      rw [addrL_feat S c' hc'] at e
      have h1 : (asCell S (adr (dimOf S) ρ jj b x)).1 < S.cf.NAs :=
        asCell_no S (lt_of_lt_of_le (AttSeg.AddrFacts.adr_lt (dimOf S) hv) L.wide)
      have h2 : (asCell S (adr (dimOf S) ρ jj b x)).1 = noOf S (mat c') := (Prod.mk.inj e).1
      have h3 := noOf_ge S (mat c')
      omega
    | _ => exact absurd hc (fun h => h)
  · cases c' with
    | c ρ jj b x =>
      exfalso
      rw [addrL_feat S c hc] at e
      have h1 : (asCell S (adr (dimOf S) ρ jj b x)).1 < S.cf.NAs :=
        asCell_no S (lt_of_lt_of_le (AttSeg.AddrFacts.adr_lt (dimOf S) hv') L.wide)
      have h2 : noOf S (mat c) = (asCell S (adr (dimOf S) ρ jj b x)).1 := (Prod.mk.inj e).1
      have h3 := noOf_ge S (mat c)
      omega
    | _ => exact absurd hc' (fun h => h)
  · rw [addrL_feat S c hc, addrL_feat S c' hc'] at e
    have hm : mat c = mat c' :=
      noOf_inj S (AttSeg.AddrFacts.mat_feat c hc) (AttSeg.AddrFacts.mat_feat c' hc')
        (Prod.mk.inj e).1
    rw [← hm] at e
    have p1 := (AttSeg.AddrFacts.phi_lt (dimOf S) c hv hc).2
    have p2 := (AttSeg.AddrFacts.phi_lt (dimOf S) c' hv' hc').2
    rw [L.T] at p1 p2
    obtain ⟨h1, h2⟩ := featCell_inj S p1 p2 e
    exact AttSeg.AddrFacts.phi_inj (dimOf S) c c' hv hv' hc hc' hm h1 h2

/-- A number is at most the least multiple of u that holds it. -/
theorem ceil_le (c u : ℕ) (hu : 0 < u) : c ≤ (c + u - 1) / u * u := by
  have h1 := Nat.div_add_mod (c + u - 1) u
  have h2 := Nat.mod_lt (c + u - 1) hu
  rw [Nat.mul_comm]
  generalize (c + u - 1) % u = r at h1 h2
  generalize u * ((c + u - 1) / u) = t at h1 ⊢
  omega

/-- **The shapes that the verifier's function shape returns are laid so**, with at least one part of
"as". -/
theorem laid_of_shape {cf : Attention.Cfg} {S : Attention.Shape}
    (h : Attention.shape cf = Except.ok S) (hN : 0 < cf.NAs) : Laid S := by
  have P := shaped_of_shape h
  have N := norm_of_shaped P (tested_of_shape h).1 (tested_of_shape h).2
  refine ⟨N, ?_, ?_⟩
  · rw [AttSeg.Dim.T_eq]
    show 2 ^ (S.lnT - 1 + 1 + S.cf.lB) = S.T
    rw [← N.lt, P.T, P.cfg]
  · have hu : 0 < cf.NAs * 2 ^ cf.lmS := Nat.mul_pos hN (Nat.two_pow_pos _)
    have k := ceil_le (5 * 2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) *
      (2 ^ Attention.nMOf cf + 2 ^ Attention.nDOf cf)) (cf.NAs * 2 ^ cf.lmS) hu
    show 2 ^ (S.cf.lgk + (S.lnT - 1) + (S.lnT - 1 + 1) + S.cf.lB + S.cf.lB) * (S.Lam * S.HA * 5) +
        2 ^ (S.cf.lgk + (S.lnT - 1 + 1) + S.cf.lB + S.cf.lB) * (S.Lam * S.HA * 5) ≤ _
    rw [← N.nM, ← N.nD, P.nM, P.nD, P.Lam, P.HA, P.kAs, P.cfg, Nat.mul_div_cancel _ hN]
    calc 2 ^ Attention.nMOf cf * (2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 5) +
          2 ^ Attention.nDOf cf * (2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) * 5)
        = 5 * 2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) *
          (2 ^ Attention.nMOf cf + 2 ^ Attention.nDOf cf) := by ring
      _ ≤ _ := k
      _ = _ := by ring

/-- **For every shape that the verifier's function shape returns.** -/
theorem addrA_inj {cf : Attention.Cfg} {S : Attention.Shape}
    (h : Attention.shape cf = Except.ok S) (hN : 0 < cf.NAs) {c c' : Raw}
    (hv : c.Valid (dimOf S)) (hv' : c'.Valid (dimOf S)) (e : addrA S c = addrA S c') : c = c' :=
  addrA_inj_laid (laid_of_shape h hN) hv hv' e

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.addrA_inj_laid
#print axioms OnBytes.Road.L5.laid_of_shape
#print axioms OnBytes.Road.L5.addrA_inj
