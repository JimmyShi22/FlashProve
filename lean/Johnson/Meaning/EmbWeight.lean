-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/EmbWeight.lean: the embedding's weight claim says the model's embedding of the
request's tokens: the hypothesis EmbWeight of Johnson/Road/Rows/EmbEnds.lean:79, as a law.

In the first group of layers the last of the merged weight claims is what the plain function
ClaimEnv.claimE (OnBytes/Model/LayerPanels.lean:494) returns. emb_side and emb_field
(Johnson/Road/Rows/EmbEnds.lean:96, :120) take two premises on it: hV, that the hidden value under
the slot sVE is the sum claimVal that the claim speaks of (not shown in this file), and hE, the
named hypothesis EmbWeight: that this sum is embSide of the library's embedding of the tokens. This
file states hE, in EmbEnds.lean's letters, of every record that claimE returns.

Which table of the committed matrix is the embedding's: the unit that the claim names is the unit
with the library's number first ppref ppref.layers (384), it has four digits to the base 256, and
its cell for digit q of entry (token t, feature j) is the library's place of the unit uEmb
(Inst/Model/Layout.lean:146): the cells in which embR (Inst/Model/FF/Trace.lean:155) reads.

Main definitions: EmbNums (seven public numbers of the layer sub-proof's layout), Spec.embTable,
Spec.embWeight.
What is compared with what: claimVal (Johnson/Road/FormsKeysWm.lean:88: the Road's own writing, on
the verifier's records, of the sum that a claim speaks of) with the library's embR.
Not claimed here: that the hidden value under the slot is claimVal (hV); that the matrix M is the
committed one; that the array tokv holds the request's tokens as the library's record has them
(Cm.Seg.tokX x); that EmbNums, SizedW and the return of wsLayOf hold at the files in scope; EmbStep
(the random step). claimE is a plain function: the law speaks of whatever text calls it.
-/
import Johnson.Road.Rows.EmbEnds
import Johnson.Road.HeadWeight

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning.Emb

open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (ClaimEnv Lay)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef units uEmb first place)
open Inst.Model.FFSeg (embR)

/-- The public numbers of the layer sub-proof's layout that the law reads. -/
structure EmbNums (y : Lay) : Prop where
  /-- the model's layers are the library's -/
  L : y.h.L = ppref.layers
  /-- the width of the residual stream is the library's -/
  d : y.h.d = ppref.d
  /-- a block has 2^ls features -/
  S2 : y.S2 = 2 ^ y.ls
  /-- the stream is a whole number of blocks -/
  blocks : y.h.d / y.S2 * 2 ^ y.ls = y.h.d
  /-- there are 2^lt positions -/
  T : y.T = 2 ^ y.h.lt
  /-- a feature's number has lPd bits, of which the lowest ls count inside a block -/
  ls : y.ls ≤ y.lPd
  /-- every feature's number has at most lPd bits -/
  cap : y.h.d ≤ 2 ^ y.lPd

/-- WHICH TABLE IS THE EMBEDDING's. The claim that claimE returns names the unit with the library's
number of the embedding; that unit has four digits; its cells are the library's places of uEmb. -/
def Spec.embTable : Prop :=
  ∀ (c : ClaimEnv) (s : WsShape), SizedW s ppref → wsLayOf s true kRef = .ok c.wsLay →
    c.v.y.h.L = ppref.layers →
    ∀ (ZE tkh : Array E) (V : ℕ) (tokv : Array ℕ) (cl : WsClaim),
      c.claimE ZE tkh V tokv = some cl →
      cl.ui = first ppref ppref.layers ∧ (units ppref)[cl.ui]? = some (uEmb ppref) ∧
        ∃ u, c.wsLay.U[cl.ui]? = some u ∧ u.nlw = 4 ∧
          ∀ q idx, cellOf u q idx = place kRef (units ppref) cl.ui (uEmb ppref) q idx

/-- THE LAW: hE of emb_side | emb_field. For every reading, every environment of claims whose layout
of the weights is what wsLayOf returns on a shape with the library's nine numbers, a point ZE of
ls + lt coordinates, lPd - ls further coordinates tkh, the library's vocabulary and any array of
tokens: the sum that the returned claim speaks of, in ANY matrix M, is embSide of the embedding
that the library reads in the same M, at the tokens of the array. The letters are those of
trueAt3_of_holds (Johnson/Road/FormsKeysTrue3.lean:271): lowE = pt ρ ZE, uE = the coordinates of ZE
from ls on. -/
def Spec.embWeight : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (c : ClaimEnv) (s : WsShape), SizedW s ppref →
    wsLayOf s true kRef = .ok c.wsLay → EmbNums c.v.y →
    ∀ (ZE tkh : Array E) (tokv : Array ℕ) (cl : WsClaim),
      ZE.size = c.v.y.ls + c.v.y.h.lt → tkh.size = c.v.y.lPd - c.v.y.ls →
      c.claimE ZE tkh ppref.V tokv = some cl →
      ∀ M : Wm K,
        Rows.EmbWeight ρ c.wsLay M cl (fun kh => ρ.val ((eqTab tkh).getD kh zeroE))
          (c.v.y.h.d / c.v.y.S2) c.v.y.ls c.v.y.h.lt (pt ρ ZE) (fun j => pt ρ ZE (c.v.y.ls + j))
          (embR ppref kRef M) (fun p => tokv.getD p 0)

end Meaning.Emb
