--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/GposSum.lean: THE SUMMAND OF THE SECOND TOKEN SUMCHECK IS A SUM OF PRODUCTS OF TWO
EXTENSIONS, AND IT IS SUMMED TO THE HONEST VALUE OF THE MASKED SCALAR. The library's `Gpos`
(Inst/Model/FF/Objects.lean:243) against what a caller of the sumcheck owes (`IsSum`,
OnBytes/Desc/First/P1/SumCore.lean). Algebra over a field. Statements and proofs.

`lin_ext`: on lists of g challenges the library's extension `Blocks.ext g v` is the multilinear
extension of a table (`Lin`, OnBytes/Desc/First/P1/SumClosure.lean): by `mle_ext_at`
(OnBytes/Desc/First/P1/MleExt.lean) at the order g - 1, .., 0, in which round j has coordinate j.
`quad_termHat`: each of the bodies of `termHat` is a finite sum, under constants, of products of two
extensions (`Quad`): so it has degree at most 2 in each coordinate.
`quad_Gpos`: so is `Gpos`.
`tot_Gpos`: the sum of `Gpos` over the cube, under the equality weights of a point pt in the order
of its coordinates, is `Blocks.ext lT (fun i => Gpos at vertex i) pt`.
`isSum_Gpos`: under the token sumcheck's own weights at the coordinates zs (`tscWs`,
OnBytes/Desc/First/P1/TscKit.lean), if zs has lT members that read as the first lT coordinates of
the lookup's token point, `Gpos` IS SUMMED TO `ClT`: by `Quad.isSum`, `tot_Gpos` and the landed
`clT_gpos` (Johnson/Road/FormsKeysSigT.lean:216).

The hypothesis D.f = 2 * D.fe is `clT_gpos`'s. Limits: nothing is said of the sumcheck's rounds, of
what a verifier's yes shows, or of probabilities.
-/
import OnBytes.Desc.First.P1.SumClosure
import OnBytes.Desc.First.P1.MleExt
import OnBytes.Desc.First.P1.TscKit
import Johnson.Road.FormsKeysSigT

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4

open Finset
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Arr Fam LW termHat ClT Gpos famsIn ew sw el wc
  zpos valU xU hhU AYU Ct St kQK isExpL)
open OnBytes.Desc.First.P1

variable {K : Type} [Field K]

/-! ### The library's extension on lists of challenges -/

/-- The order g - 1, .., 0: round j has coordinate j. -/
theorem rev_range_ofList (rs : List K) :
    ((List.range rs.length).reverse.map fun v => Blocks.ofList rs (rs.length - 1 - v)) = rs := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have e : rs.length - 1 - (rs.length - 1 - i) = i := by omega
    simp [Blocks.ofList, e, h2]

theorem ext_ofList (g : ℕ) (v : ℕ → K) (rs : List K) (h : rs.length = g) :
    Blocks.ext g v (Blocks.ofList rs) =
      mle g (fun b => v (idxOf (List.range g).reverse b)) rs := by
  subst h
  have e := mle_ext_at rs.length (List.reverse_perm (List.range rs.length)) (Blocks.ofList rs) v
  rw [rev_range_ofList] at e
  exact e.symm

/-- **The library's extension is an extension.** -/
theorem lin_ext (g : ℕ) (v : ℕ → K) : Lin g fun rs => Blocks.ext g v (Blocks.ofList rs) :=
  ⟨_, fun rs h => ext_ofList g v rs h⟩

theorem lin_mulc {n : ℕ} {f : List K → K} (c : K) (hf : Lin n f) : Lin n fun rs => f rs * c :=
  (hf.smul c).congr fun _ _ => mul_comm _ _

theorem quad_scl {n : ℕ} {f : List K → K} (k : ℕ) (hf : Quad n f) :
    Quad n fun rs => Inst.Model.Site.scl k (f rs) :=
  (hf.smul (2 ^ Inst.Model.Site.dn k)).congr fun _ _ => Inst.Model.Site.scl_eq k _

/-! ### The bodies -/

section Hat

variable [scl : Scl] (D : Dim) (t : Cell → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (z : ℕ → K)

omit scl in
theorem lin_valU (X : Arr) (inst j : ℕ) :
    Lin D.lT fun rs => valU D t X inst j (Blocks.ofList rs) := lin_ext _ _

omit scl in
theorem lin_xU (s j : ℕ) : Lin D.lT fun rs => xU D t s j (Blocks.ofList rs) := lin_ext _ _

omit scl in
theorem lin_hhU (l j : ℕ) : Lin D.lT fun rs => hhU D t l j (Blocks.ofList rs) := lin_ext _ _

omit scl in
theorem lin_Ct (l jj : ℕ) : Lin D.lT fun rs => (Ct D tb L0 l jj (Blocks.ofList rs) : K) :=
  lin_ext _ _

omit scl in
theorem lin_St (l jj : ℕ) : Lin D.lT fun rs => (St D tb L0 l jj (Blocks.ofList rs) : K) :=
  lin_ext _ _

omit scl in
theorem lin_AYU (l x : ℕ) : Lin D.lT fun rs => AYU D t w l x (Blocks.ofList rs) := by
  unfold AYU
  by_cases h : x < D.dq
  · simp only [if_pos h]
    exact Lin.sum _ _ fun j _ => lin_mulc _ (lin_valU D t .a l j)
  · simp only [if_neg h]
    exact Lin.sum _ _ fun j _ => lin_mulc _ (lin_valU D t .a l j)

/-- **Each body is a sum of products of two extensions.** -/
theorem quad_termHat (s : Fam) (l : ℕ) :
    Quad D.lT fun rs => termHat D t tb L0 w z s l (Blocks.ofList rs) := by
  cases s <;> simp only [termHat]
  case N1 => exact Lin.mul (lin_ext _ _) (Lin.sum _ _ fun x _ => (lin_xU D t _ x).smul _)
  case N2 => exact Lin.mul (lin_ext _ _) (Lin.sum _ _ fun x _ => (lin_xU D t _ x).smul _)
  case QK =>
    refine Quad.sum _ _ fun x _ => Quad.smul _ (quad_scl _ (Quad.ite _ ?_ ?_))
    · exact ((lin_Ct D tb L0 _ _).mul (lin_AYU D t w _ _)).sub
        ((lin_St D tb L0 _ _).mul (lin_AYU D t w _ _))
    · exact ((lin_St D tb L0 _ _).mul (lin_AYU D t w _ _)).add
        ((lin_Ct D tb L0 _ _).mul (lin_AYU D t w _ _))
  case XR =>
    exact Lin.mul (lin_valU D t _ _ _) (Lin.sum _ _ fun x _ => (lin_valU D t _ _ x).smul _)
  case DD =>
    exact Quad.smul _ (Quad.sum _ _ fun e _ => (lin_valU D t _ _ e).mul (lin_valU D t _ _ e))
  case MR =>
    exact Quad.smul _ (Quad.sum _ _ fun e _ => (lin_valU D t _ _ e).mul (lin_valU D t _ _ e))
  case G =>
    exact Quad.ite _ (quad_scl _ (Quad.sum _ _ fun e _ => Lin.mul (lin_valU D t _ _ e)
      (Lin.sum _ _ fun j _ => lin_mulc _ (lin_valU D t _ _ j)))) (Quad.zero _)
  case U =>
    exact Quad.ite _ (quad_scl _ (Quad.sum _ _ fun e _ => Lin.mul (lin_valU D t _ _ e)
      (Lin.sum _ _ fun j _ => lin_mulc _ (lin_valU D t _ _ j)))) (Quad.zero _)
  case D =>
    exact Quad.ite _ (quad_scl _ (Quad.sum _ _ fun e _ => Lin.mul (lin_valU D t _ _ e)
      (Lin.sum _ _ fun j _ => lin_mulc _ (lin_hhU D t _ _)))) (Quad.zero _)
  all_goals exact Quad.zero _

/-- **The summand is a sum of products of two extensions.** -/
theorem quad_Gpos : Quad D.lT fun rs => Gpos D t tb L0 w z (Blocks.ofList rs) := by
  unfold Gpos
  exact Quad.sum _ _ fun c _ => Quad.smul _ (Quad.sum _ _ fun l _ => Quad.smul _
    (Quad.listSum _ _ fun s _ => quad_termHat D t tb L0 w z s l))

/-! ### The sum over the cube -/

omit scl in
/-- The summand reads its point through extensions over lT variables alone. -/
theorem termHat_congr [Scl] {X X' : ℕ → K}
    (h : ∀ v : ℕ → K, Blocks.ext D.lT v X = Blocks.ext D.lT v X') (s : Fam) (l : ℕ) :
    termHat D t tb L0 w z s l X = termHat D t tb L0 w z s l X' := by
  cases s <;> simp only [termHat, valU, xU, hhU, Ct, St, AYU, h]

omit scl in
theorem Gpos_congr [Scl] {X X' : ℕ → K}
    (h : ∀ v : ℕ → K, Blocks.ext D.lT v X = Blocks.ext D.lT v X') :
    Gpos D t tb L0 w z X = Gpos D t tb L0 w z X' := by
  unfold Gpos
  simp only [termHat_congr D t tb L0 w z h]

end Hat

/-- The library's extension reads the first g coordinates of its point alone. -/
theorem ext_pt {g : ℕ} {u u' : ℕ → K} (h : ∀ k, k < g → u k = u' k) (f : ℕ → K) :
    Blocks.ext g f u = Blocks.ext g f u' := by
  unfold Blocks.ext Blocks.eqN
  refine sum_congr rfl fun X _ => ?_
  congr 1
  exact prod_congr rfl fun k hk => by rw [Nat.zero_add, h k (mem_range.mp hk)]

theorem rev_succ (g : ℕ) : (List.range (g + 1)).reverse = g :: (List.range g).reverse := by
  simp [List.range_succ]

/-- In the order g - 1, .., 0 a list of bits spells a number below 2 ^ g. -/
theorem idxOf_rev_lt : ∀ (g : ℕ) (b : List Bool), idxOf (List.range g).reverse b < 2 ^ g
  | 0, b => by
    cases b <;> simp [idxOf]
  | g + 1, [] => by
    rw [rev_succ]
    show 0 < 2 ^ (g + 1)
    positivity
  | g + 1, x :: b => by
    rw [rev_succ, idxOf_cons]
    have h1 := idxOf_rev_lt g b
    have h2 : 2 ^ (g + 1) = 2 ^ g + 2 ^ g := by rw [pow_succ, Nat.mul_two]
    split <;> omega

/-- At a corner the library's extension is the vector's entry, as at the library's own vertex. -/
theorem ext_corner (g : ℕ) (v : ℕ → K) (b : List Bool) (h : b.length = g) :
    Blocks.ext g v (Blocks.ofList (bitsK b)) =
      Blocks.ext g v (Blocks.cubePt g (idxOf (List.range g).reverse b)) := by
  rw [ext_ofList g v _ (by rw [bitsK_length, h]), mle_bits g _ b h,
    Blocks.ext_cubePt g v (idxOf_rev_lt g b)]

section Sum

variable [scl : Scl] (D : Dim) (t : Cell → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (z : ℕ → K)

/-- **The sum over the cube**, under the equality weights of the point's coordinates in their
order. -/
theorem tot_Gpos (cs : List K) (h : cs.length = D.lT) :
    tot (cs.map fun c => (1 - c, c)) (fun b => Gpos D t tb L0 w z (Blocks.ofList (bitsK b))) =
      Blocks.ext D.lT (fun i => Gpos D t tb L0 w z (Blocks.cubePt D.lT i)) (Blocks.ofList cs) := by
  have e := tot_eqN D.lT (List.reverse_perm (List.range D.lT)) (Blocks.ofList cs)
    (fun i => Gpos D t tb L0 w z (Blocks.cubePt D.lT i))
  have hc := rev_range_ofList cs
  rw [h] at hc
  have hm : ((List.range D.lT).reverse.map fun v =>
      ((1 : K) - Blocks.ofList cs (D.lT - 1 - v), Blocks.ofList cs (D.lT - 1 - v))) =
      cs.map fun c => (1 - c, c) := by
    conv_rhs => rw [← hc]
    rw [List.map_map]
    rfl
  rw [hm] at e
  unfold Blocks.ext
  rw [← e]
  refine tot_congr_len _ _ _ fun b hb => ?_
  have hb' : b.length = D.lT := by rw [hb, List.length_map, h]
  exact Gpos_congr D t tb L0 w z fun v => ext_corner D.lT v b hb'

variable (ρ : OnBytes.Model.Reading K)

/-- **THE SUMMAND IS SUMMED TO THE HONEST VALUE OF THE MASKED SCALAR.** zs: the coordinates under
which the token sumcheck runs. -/
theorem isSum_Gpos (hf : D.f = 2 * D.fe) (zs : List OnBytes.E) (hl : zs.length = D.lT)
    (hz : ∀ k, k < D.lT → Blocks.ofList (zs.map ρ.val) k = zpos D z k) :
    IsSum ((tscWs zs).map (wtOf ρ)) (fun rs => Gpos D t tb L0 w z (Blocks.ofList rs))
      (ClT D t tb L0 w z) := by
  have hlen : ((tscWs zs).map (wtOf ρ)).length = D.lT := by
    rw [List.length_map, tscWs, List.length_map, hl]
  have hq : Quad ((tscWs zs).map (wtOf ρ)).length
      fun rs => Gpos D t tb L0 w z (Blocks.ofList rs) := by
    rw [hlen]
    exact quad_Gpos D t tb L0 w z
  have hs := Quad.isSum (twos_tsc ρ zs) hq
  have hx : tscXs ρ zs = (zs.map ρ.val).map fun c => (1 - c, c) := by
    unfold tscXs
    rw [List.map_map]
    rfl
  rw [hx, tot_Gpos D t tb L0 w z (zs.map ρ.val) (by rw [List.length_map, hl]),
    ext_pt hz, ← OnBytes.Road.clT_gpos D t tb L0 w z hf] at hs
  exact hs

end Sum

end OnBytes.Road.K4
