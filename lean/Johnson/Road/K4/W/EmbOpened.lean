-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/EmbOpened.lean: CONDITIONAL.

Not shown here. AT THE LIBRARY's OWN NUMBERS ALONE: SizedW at ppref, the return of wsLayOf at kRef,
EmbNums and the vocabulary ppref.V are premises: NO SMALL PLAN MEETS THEM, and no example is known.
(J11) is a premise, at the embedding that the library reads in the matrix M and at the array's
tokens: who hands it over is not shown. That M is the committed matrix, and that the array holds
the request's tokens, is not shown. No property is claimed.

THE SUM THAT THE EMBEDDING's WEIGHT CLAIM SPEAKS OF IS THE LIBRARY's SUM OVER THE STREAM THAT COMES
IN, where the library's identity (J11) holds at every feature and position. So one hidden value
serves both the embedding's claim of the sub-protocol K4 (the format's group 12) and the merge. A
call of embWeight (Johnson/Meaning/EmbWeightProof.lean), then (J11) position by position.

  EmbCube      (J11) at every feature below d and every position below 2 ^ D.lT.
  emb_opened   the claim's sum is the library's sum at the cells.
  emb_slot     a slot that holds the claim's sum holds what embedding_zero (HotEmb.lean) asks.
-/
import Johnson.Meaning.EmbWeightProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (ClaimEnv)
open Inst.Model (Scl ppref)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim Cell idnVal xS embR)
open Meaning.Emb (EmbNums embWeight)
open Blocks (ext)

variable {K : Type} [Field K] [scl : Scl]

/-- **(J11) at every feature and every position**: the stream that comes in is the embedding of the
tokens. d: the number of features. This defines a hypothesis; the definition claims nothing. -/
def EmbCube (D : Dim) (t : Cell → K) (emb : ℕ → ℕ → K) (tok : ℕ → ℕ) (d : ℕ) : Prop :=
  ∀ j, j < d → ∀ p, p < 2 ^ D.lT → idnVal D t emb tok (.j11 j p) = 0

/-- **The claim's sum is the library's sum at the cells.** cl: what claimE returns. -/
theorem emb_opened (ρ : Reading K) (c : ClaimEnv) (s : WsShape) (Z : SizedW s ppref)
    (hl : wsLayOf s true kRef = .ok c.wsLay) (N : EmbNums c.v.y) {ZE tkh : Array E}
    {tokv : Array ℕ} {cl : WsClaim} (hZ : ZE.size = c.v.y.ls + c.v.y.h.lt)
    (hk : tkh.size = c.v.y.lPd - c.v.y.ls) (h : c.claimE ZE tkh ppref.V tokv = some cl)
    (M : Wm K) {D : Dim} {t : Cell → K} (hlT : D.lT = c.v.y.h.lt)
    (hJ : EmbCube D t (embR ppref kRef M) (fun p => tokv.getD p 0) c.v.y.h.d) :
    claimVal ρ c.wsLay M cl =
      ∑ kh ∈ range (c.v.y.h.d / c.v.y.S2), ρ.val ((eqTab tkh).getD kh zeroE) *
        ∑ r ∈ range (2 ^ c.v.y.ls), Blocks.eqN c.v.y.ls 0 (pt ρ ZE) r *
          ext D.lT (fun p => xS D t 0 (kh * 2 ^ c.v.y.ls + r) p)
            (fun j => pt ρ ZE (c.v.y.ls + j)) := by
  have e : claimVal ρ c.wsLay M cl = Rows.embSide (fun kh => ρ.val ((eqTab tkh).getD kh zeroE))
      (c.v.y.h.d / c.v.y.S2) c.v.y.ls c.v.y.h.lt (pt ρ ZE) (fun j => pt ρ ZE (c.v.y.ls + j))
      (fun j p => embR ppref kRef M (tokv.getD p 0) j) :=
    embWeight K ρ c s Z hl N ZE tkh tokv cl hZ hk h M
  rw [e, ← hlT]
  unfold Rows.embSide
  refine sum_congr rfl fun kh hkh => ?_
  congr 1
  refine sum_congr rfl fun r hr => ?_
  congr 1
  refine Blocks.ext_congr (fun p hp => ?_) _
  have hj : kh * 2 ^ c.v.y.ls + r < c.v.y.h.d := by
    have h1 := mem_range.mp hkh
    have h2 := mem_range.mp hr
    calc kh * 2 ^ c.v.y.ls + r < (kh + 1) * 2 ^ c.v.y.ls := by rw [Nat.succ_mul]; omega
      _ ≤ c.v.y.h.d / c.v.y.S2 * 2 ^ c.v.y.ls := Nat.mul_le_mul_right _ h1
      _ = c.v.y.h.d := N.blocks
  have d0 : xS D t 0 (kh * 2 ^ c.v.y.ls + r) p -
      embR ppref kRef M (tokv.getD p 0) (kh * 2 ^ c.v.y.ls + r) = 0 := hJ _ hj p hp
  exact (sub_eq_zero.mp d0).symm

/-- A slot that holds the claim's sum holds what the embedding's claim asks of it. -/
theorem emb_slot (ρ : Reading K) (W : World K) (c : ClaimEnv) (s : WsShape) (Z : SizedW s ppref)
    (hl : wsLayOf s true kRef = .ok c.wsLay) (N : EmbNums c.v.y) {ZE tkh : Array E}
    {tokv : Array ℕ} {cl : WsClaim} (hZ : ZE.size = c.v.y.ls + c.v.y.h.lt)
    (hk : tkh.size = c.v.y.lPd - c.v.y.ls) (h : c.claimE ZE tkh ppref.V tokv = some cl)
    (M : Wm K) {D : Dim} {t : Cell → K} (hlT : D.lT = c.v.y.h.lt)
    (hJ : EmbCube D t (embR ppref kRef M) (fun p => tokv.getD p 0) c.v.y.h.d) {sVE : ℕ}
    (hS : W.slot sVE = claimVal ρ c.wsLay M cl) :
    W.slot sVE =
      ∑ kh ∈ range (c.v.y.h.d / c.v.y.S2), ρ.val ((eqTab tkh).getD kh zeroE) *
        ∑ r ∈ range (2 ^ c.v.y.ls), Blocks.eqN c.v.y.ls 0 (pt ρ ZE) r *
          ext D.lT (fun p => xS D t 0 (kh * 2 ^ c.v.y.ls + r) p)
            (fun j => pt ρ ZE (c.v.y.ls + j)) :=
  hS.trans (emb_opened ρ c s Z hl N hZ hk h M hlT hJ)

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.emb_opened
#print axioms OnBytes.Road.K4.W.emb_slot
