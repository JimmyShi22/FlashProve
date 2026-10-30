-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/GatedEnds.lean: what the two ends of the product layers of the gated products say
about the cells. Statements only.

A layer sub-proof (OnBytes/Model/Layer.lean) has one or two product layers for the gated products:
hearGated runs them, claimsGated adds their claims. Each is a sumcheck of a sum
  sum over X of eq(point, X) f0(X) f1(X).
It starts from a form in hidden values that the batched sumcheck has shown, and it ends in two
hidden values, of which claimsEnds claims that they are the negatives of the tensors s and u at the
layer's own point. This file states what these forms are worth in a world in which the tables that
they read are true, in the library's words (Inst/Model/FF/Objects.lean: slV, upV, slV', upV', hhU,
Hh1t).

A sumcheck's soundness is not the matter of this file. Its statement would say: if the sum is not
what the start form is worth, then, but for an error, the layer's claim or one of "the hidden end
value is the map's value at the layer's point" is false. The statements here stand at the two ends
of that one.
 - Out (GatedFirstOut, GatedSecondOut): each of the two claims of claimsEnds is worth the slot of
   the end value less the extension of the library's map at the layer's point. So the claim holds
   exactly if the hidden end value is the map's value there.
 - In (GatedFirstIn, GatedSecondIn): the sum on which the layer runs is the extension of the honest
   never-sent vector at the batched sumcheck's coordinates. For the first layer that is the right
   side of EndsTrue.allH (Johnson/Road/FormsKeysEnd.lean) at the honest vector. The second layer
   starts from one combination of the routed layers' values: the start form less the sum is the
   combination, under the equality weights of the fresh point, of "hidden value less the right side
   of EndsTrue.colH".

Main definitions: endForm, start2 (the verifier's forms, in its own letters), hvOf (the honest
never-sent vectors), EndGround (what is asked of the world and the layout), GatedFirstOut,
GatedFirstIn, GatedSecondOut, GatedSecondIn, GatedFirstEnd, GatedSecondEnd.

What is not claimed. These are statements: none of them is proved in this file, and this file does
not say which of them are proved elsewhere. All are identities in a world; no challenge's
distribution occurs. That the tables at
the layers' points are true (EndGround.trueS, trueU) is the smallness test's matter. The first
layer's end claims are read only where a layer's number of hidden units is a power of two. Every
shape with routed experts is such. A shape without them and with another number is not covered:
there the identity would be false. Nothing is said about hiding. The program does not import this
file.


-/
import Johnson.Road.FormsKeysEnd
import OnBytes.Model.Layer

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff Level tenCell eqTab hiTab)
open OnBytes.Model.Layer (Env Ten SBlk sumForms aff0 downFrom)
open Inst.Model.FFSeg (Dim Cell Arr hhU Hh1t slV upV slV' upV' lF lFe)
open Blocks (ext)

/-! ## The verifier's forms, in its own letters -/

/-- One sum of claimsEnds (OnBytes/Model/Layer.lean). t: the first entry of the tables of af at the
layer's point; X: the tensor; the other arguments are those of claimsEnds. -/
def endForm (v : Env) (t : ℕ) (X : Ten) (e : Array E) (rows blocks stride : ℕ) (lamOf : ℕ → ℕ)
    (first : ℕ) : Option Aff :=
  sumForms (rows * blocks) fun x =>
    (v.longA t X (lamOf (x / blocks)) (first + x % blocks)).map fun a =>
      (a, e.getD (x / blocks * stride + x % blocks) zeroE)

/-- The start form of the second product layer (hearGated): the hidden values of the routed layers'
never-sent vectors, under the equality weights of the fresh point rhoM. -/
def start2 (LamM sH1 : ℕ) (rhoM : Array E) : Aff :=
  (List.range LamM).foldl
    (fun (C : Aff) lm => C.addMul (Aff.slot (sH1 + 1 + lm)) ((eqTab rhoM).getD lm zeroE)) aff0

/-! ## The honest never-sent vectors -/

/-- The honest never-sent vectors of the cells t. u: the lookup's token point; u': the end point of
the second token sumcheck. Vector 0 is the library's Hh1t at u: the gated products of all layers and
hidden units. Vector k + 1 holds the gated products of the routed hidden units of layer 2 k + 1 at
u'. It reads the cells and two token points, and no later challenge. -/
def hvOf {K : Type} [Field K] (D : Dim) (t : Cell → K) (u u' : ℕ → K) : ℕ → ℕ → K
  | 0, Y => Hh1t D t u Y
  | k + 1, j => hhU D t (2 * k + 1) (D.fe + j) u'

/-! ## What is asked of the world and the layout -/

/-- The ground on which the two end claims of a product layer are read. r: the layer's point, of
g + ls + lT coordinates: g for the blocks of features of all layers, ls for a feature in its block,
lT for the position. tb: the first entry of the tables of af at the last ls + lT coordinates of r.
ts, tu: the verifier's tensors s and u. -/
structure EndGround {K : Type} [Field K] (ρ : Reading K) (W : World K) (v : Env) (D : Dim)
    (c : Cells K) (t : Cell → K) (r : Array E) (g tb : ℕ) (ts tu : Ten) : Prop where
  /-- the reading takes numerals to numbers -/
  num : Numerals ρ
  /-- a block has 2^ls features -/
  S2 : v.y.S2 = 2 ^ v.y.ls
  /-- the point has one coordinate for each variable -/
  size : r.size = g + v.y.ls + D.lT
  /-- the library's names of the cells of sl are the cells of the tensor s -/
  tiedS : Tied c t .sl ts.mat ts.place
  /-- and those of up the cells of the tensor u -/
  tiedU : Tied c t .up tu.mat tu.place
  /-- every run of s begins at a whole block -/
  wholeS : ∀ i l, v.y.S2 ∣ tenCell ts.place l i 0
  /-- every run of u begins at a whole block -/
  wholeU : ∀ i l, v.y.S2 ∣ tenCell tu.place l i 0
  /-- the tables at the layer's point are true of the matrix that holds s -/
  trueS : LongTrue ρ W v tb ts.mat v.y.ls D.lT c (fun j => pt ρ r (g + j))
    (fun j => pt ρ r (g + v.y.ls + j))
  /-- and of the matrix that holds u -/
  trueU : LongTrue ρ W v tb tu.mat v.y.ls D.lT c (fun j => pt ρ r (g + j))
    (fun j => pt ρ r (g + v.y.ls + j))

/-! ## The first product layer -/

/-- The two end claims of the first product layer. o: the layer as it was heard; e: the weights of
the blocks, as claimsGated makes them; aS, aU: the two sums of claimsEnds. Each claim's form is
worth the slot of the end value less the extension of the library's map at the layer's point. -/
def GatedFirstOut : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (W : World K) (v : Env) (D : Dim) (c : Cells K)
    (t : Cell → K) (o : Level) (tb : ℕ) (ts tu : Ten) (e : Array E) (aS aU : Aff),
    EndGround ρ W v D c t o.r (D.lL + lF D - v.y.ls) tb ts tu →
    v.y.h.la = v.y.ls + D.lT → v.y.ls ≤ lF D →
    v.y.Lam = 2 ^ D.lL → v.y.h.f = 2 ^ lF D → v.y.Pf = 2 ^ lF D →
    hiTab o.r v.y.h.la (v.y.h.ll + v.y.lPf - v.y.ls) = .ok e →
    endForm v tb ts e v.y.Lam (v.y.h.f / v.y.S2) (v.y.Pf / v.y.S2) id 0 = some aS →
    endForm v tb tu e v.y.Lam (v.y.h.f / v.y.S2) (v.y.Pf / v.y.S2) id 0 = some aU →
    (Aff.slot o.sL + aS).value ρ W =
        W.slot o.sL - ext (D.lL + lF D + D.lT) (slV D t) (pt ρ o.r) ∧
      (Aff.slot o.sR + aU).value ρ W =
        W.slot o.sR - ext (D.lL + lF D + D.lT) (upV D t) (pt ρ o.r)

/-- The sum on which the first product layer runs, at the point from which hearGated starts it, is
the extension of the honest never-sent vector 0 at the coordinates of the panel of the down product:
the right side of EndsTrue.allH at hvOf. rs: the batched sumcheck's challenges; ztF: the lookup's
token point; b: the panel. -/
def GatedFirstIn : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (D : Dim) (t : Cell → K) (rs ztF : Array E) (b : SBlk)
    (u' : ℕ → K),
    b.wy = lF D → b.w = D.lL + lF D → b.w ≤ rs.size →
    ext (D.lL + lF D + D.lT) (fun X => slV D t X * upV D t X)
        (pt ρ (downFrom rs b.w ++ ztF)) =
      gsum ρ rs b (fun i yv => hvOf D t (pt ρ ztF) u' 0 (i * 2 ^ b.wy + yv))

/-- The two ends of the first product layer of the gated products. -/
structure GatedFirstEnd : Prop where
  /-- the end claims -/
  out : GatedFirstOut
  /-- the start -/
  start : GatedFirstIn

/-! ## The second product layer -/

/-- The two end claims of the second product layer, that of the routed experts' hidden units. -/
def GatedSecondOut : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (W : World K) (v : Env) (D : Dim) (c : Cells K)
    (t : Cell → K) (o : Level) (tb : ℕ) (ts tu : Ten) (e : Array E) (aS aU : Aff),
    EndGround ρ W v D c t o.r (D.lL - 1 + lFe D - v.y.ls) tb ts tu →
    v.y.h.la = v.y.ls + D.lT → v.y.ls ≤ lFe D →
    v.y.LamM = 2 ^ (D.lL - 1) → v.y.h.fe = 2 ^ lFe D → D.fe = 2 ^ lFe D →
    hiTab o.r v.y.h.la (v.y.h.ll - 1 + v.y.lfe - v.y.ls) = .ok e →
    endForm v tb ts e v.y.LamM (v.y.h.fe / v.y.S2) (v.y.h.fe / v.y.S2) (fun lm => 2 * lm + 1)
      (v.y.h.fe / v.y.S2) = some aS →
    endForm v tb tu e v.y.LamM (v.y.h.fe / v.y.S2) (v.y.h.fe / v.y.S2) (fun lm => 2 * lm + 1)
      (v.y.h.fe / v.y.S2) = some aU →
    (Aff.slot o.sL + aS).value ρ W =
        W.slot o.sL - ext (D.lL - 1 + lFe D + D.lT) (slV' D t) (pt ρ o.r) ∧
      (Aff.slot o.sR + aU).value ρ W =
        W.slot o.sR - ext (D.lL - 1 + lFe D + D.lT) (upV' D t) (pt ρ o.r)

/-- The start form of the second product layer, less the sum on which the layer runs, is the
combination, under the equality weights of the fresh point rhoM, of "the hidden value of the routed
layer lm's never-sent vector, less the extension of the honest vector at the batched sumcheck's
coordinates": of the two sides of EndsTrue.colH at hvOf. rt: the end point of the second token
sumcheck. -/
def GatedSecondIn : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (W : World K) (D : Dim) (t : Cell → K)
    (rs rt rhoM : Array E) (u : ℕ → K) (sH1 LamM lfe : ℕ),
    lfe = lFe D → lfe ≤ rs.size → rhoM.size = D.lL - 1 → LamM = 2 ^ (D.lL - 1) →
    (start2 LamM sH1 rhoM).value ρ W -
        ext (D.lL - 1 + lFe D + D.lT) (fun X => slV' D t X * upV' D t X)
          (pt ρ (rhoM ++ downFrom rs lfe ++ rt)) =
      ∑ lm ∈ range LamM, Blocks.eqN (D.lL - 1) 0 (pt ρ rhoM) lm *
        (W.slot (sH1 + 1 + lm) -
          ∑ yv ∈ range (2 ^ lfe), eqR ρ rs 0 lfe yv * hvOf D t u (pt ρ rt) (1 + lm) yv)

/-- The two ends of the second product layer of the gated products. -/
structure GatedSecondEnd : Prop where
  /-- the end claims -/
  out : GatedSecondOut
  /-- the start -/
  start : GatedSecondIn

end OnBytes.Road.Rows
