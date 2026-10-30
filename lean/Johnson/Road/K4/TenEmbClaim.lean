-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/TenEmbClaim.lean: the library's pair of the claim on the embedding (tenEmb,
Cb/Pv/Lay/At/TnEmb.lean) and the embedding's weight claim as the verifier makes it
(ClaimEnv.claimE, OnBytes/Model/LayerPanels.lean), the last claim of the first group's merge, say
the same of every matrix W.

Both are worth, on W, one sum over blocks, features and positions of the library's reading embR of
the embedding's table: the pair by tenEmb_val, the claim by the law embWeight
(Johnson/Meaning/EmbWeightProof.lean). What is done here is the fit of the letters: the pair's two
points read the verifier's two arrays, and its tokens are the array's.

  `tenEmb_claim`: tval (tenEmb ppref kRef h lt ls gB pa pb tok) (matOf W) = claimVal ρ lay W cl.
No new argument.
Limits. AT THE LIBRARY's REFERENCE PARAMETERS ALONE (ppref, kRef): so is embWeight. Premises: the
layout of the weights is what wsLayOf returns on a shape with the library's numbers; EmbNums (seven
public numbers of the layers' layout); the lengths of the two arrays; claimE has returned cl at the
library's vocabulary; pa reads ZE on its ls + lt coordinates, pb reads tkh on its gB = lPd - ls
coordinates, tok reads the array of tokens on the 2 ^ lt positions; the matrix has room for all
units. An identity on public data and any matrix W: nothing on which matrix is committed, on whose
tokens the array holds, on a draw, on soundness or on hiding.


-/
import Johnson.Meaning.EmbWeightProof
import Cb.Pv.Lay.At.TnEmb
import Blocks.RngForest

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open Finset
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (ClaimEnv)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef units off)
open Inst.Model.Layout.Tensor (matOf)
open Inst.Model.FFSeg (embR)
open Cb.Pv.Lay.At (tval tenEmb tenEmb_val)
open Blocks (eqN)
open Meaning.Emb (EmbNums embWeight)

variable {K : Type} [Field K]

/-- **The pair of the claim on the embedding and the verifier's claim say the same of every W.** -/
theorem tenEmb_claim (ρ : Reading K) (c : ClaimEnv) (s : WsShape) (Z : SizedW s ppref)
    (hl : wsLayOf s true kRef = .ok c.wsLay) (N : EmbNums c.v.y) {ZE tkh : Array E}
    {tokv : Array ℕ} {cl : WsClaim} (hZ : ZE.size = c.v.y.ls + c.v.y.h.lt)
    (hk : tkh.size = c.v.y.lPd - c.v.y.ls) (h : c.claimE ZE tkh ppref.V tokv = some cl)
    {hh gB : ℕ} {pa pb : ℕ → K} {tok : ℕ → ℕ} (hgB : gB = c.v.y.lPd - c.v.y.ls)
    (hpa : ∀ j, j < c.v.y.ls + c.v.y.h.lt → pa j = pt ρ ZE j)
    (hpb : ∀ j, j < gB → pb j = pt ρ tkh j)
    (htok : ∀ p, p < 2 ^ c.v.y.h.lt → tok p = tokv.getD p 0)
    (hH : off kRef (units ppref) (units ppref).length ≤ hh) (W : ℕ → ℕ → K) :
    tval (tenEmb ppref kRef hh c.v.y.h.lt c.v.y.ls gB pa pb tok) (matOf W) =
      claimVal ρ c.wsLay W cl := by
  have hd : ppref.d = c.v.y.h.d / c.v.y.S2 * 2 ^ c.v.y.ls := by
    rw [N.blocks]
    exact N.d.symm
  have hnb : c.v.y.h.d / c.v.y.S2 ≤ 2 ^ gB := by
    rw [hgB]
    exact N.blocks_le
  have e : claimVal ρ c.wsLay W cl =
      Rows.embSide (fun kh => ρ.val ((eqTab tkh).getD kh zeroE)) (c.v.y.h.d / c.v.y.S2) c.v.y.ls
        c.v.y.h.lt (pt ρ ZE) (fun j => pt ρ ZE (c.v.y.ls + j))
        (fun j p => embR ppref kRef W (tokv.getD p 0) j) :=
    embWeight K ρ c s Z hl N ZE tkh tokv cl hZ hk h W
  rw [tenEmb_val ppref kRef hh c.v.y.h.lt c.v.y.ls gB _ hd hnb pa pb tok hH W, e]
  unfold Rows.embSide
  refine sum_congr rfl fun kh hkh => ?_
  have w1 : ρ.val ((eqTab tkh).getD kh zeroE) = eqN gB 0 pb kh := by
    rw [eqTab_value ρ tkh kh (by
      rw [hk, ← hgB]
      exact Nat.lt_of_lt_of_le (mem_range.mp hkh) hnb), hk, ← hgB]
    exact Blocks.Rng.eqN_shift gB 0 0 (fun t ht => by
      rw [Nat.zero_add]
      exact (hpb t ht).symm) kh
  beta_reduce
  rw [w1]
  refine congrArg (eqN gB 0 pb kh * ·) (sum_congr rfl fun r _ => ?_)
  have w2 : eqN c.v.y.ls 0 pa r = eqN c.v.y.ls 0 (pt ρ ZE) r :=
    Blocks.Rng.eqN_shift c.v.y.ls 0 0 (fun t ht => by
      rw [Nat.zero_add]
      exact hpa t (Nat.lt_of_lt_of_le ht (Nat.le_add_right _ _))) r
  rw [w2]
  refine congrArg (eqN c.v.y.ls 0 (pt ρ ZE) r * ·) ?_
  unfold Blocks.ext
  refine sum_congr rfl fun p hp => ?_
  beta_reduce
  have w3 : eqN c.v.y.h.lt c.v.y.ls pa p =
      eqN c.v.y.h.lt 0 (fun j => pt ρ ZE (c.v.y.ls + j)) p :=
    Blocks.Rng.eqN_shift c.v.y.h.lt c.v.y.ls 0 (fun t ht => by
      rw [Nat.zero_add]
      exact hpa (c.v.y.ls + t) (Nat.add_lt_add_left ht _)) p
  rw [w3, htok p (mem_range.mp hp)]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.tenEmb_claim
