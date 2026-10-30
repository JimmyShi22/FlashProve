-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysQKF.lean: the verifier's weight claims of the segment QK, against the rows of
the library's panel QK.

For each layer of a group the verifier makes one claim on the unit of the layer's query and key
matrices (claimsT, OnBytes/Model/LayerPanels.lean). claimVal (Johnson/Road/FormsKeysWm.lean) writes
the sum that such a claim speaks of in a matrix W of weights: over the unit's index tuples, the
product of what the factors weigh the indices with, times the weight at the verifier's cells. The
library has, for row l of its panel QK, the value of the row's tensor claim (Pan.TnRow,
Inst/Model/FF/Objects.lean), at weights w. This file shows that the two are one number, at the
weights that the library's layout reads in the same W: w l := layerR D.P lk W (L0 + l).

What is compared with what: claimVal, a definition of these files on the verifier's records, at the
verifier's own claim, with the library's Pan.QK.TnRow.

The parts: the claim's unit and its groups, and the step from factors to a tensor claim
(Johnson/Road/FormsKeysClaim.lean, over FormsKeysWLay.lean and FormsKeysTnP.lean); the factors on
the heads and on the channels (Johnson/Road/FormsKeysQK.lean); the factor on the input features
(Ec_at of FormsKeysClaim.lean, over FormsKeysFacRs.lean); the library's row as a tensor claim
(TnRow_QK of Johnson/Road/FormsKeysTn.lean); which claim stands at which number of the segment's
list (claimsT_QK_at of Johnson/Road/FormsKeysFold.lean).

Main definitions: facQK; dimQ, metQKF. Main theorems: claim_QK, claims_QK; zc_met.

The hypotheses, and whether they can be met.
 - ClaimFits: see Johnson/Road/FormsKeysClaim.lean. QKFits, hrt, RopeFits: see
   Johnson/Road/FormsKeysQK.lean.
 - hz, that the point of the verifier's call reads as the library's point zc D z (call .QK) on the
   call's coordinates: for every point there is a z for which it holds (zc_met): one call. That one
   z serves all calls of a lookup is shown in Johnson/Road/FormsKeysLookT.lean (look_fits); see
   there for what it asks.
 - hzh, that zh agrees with the reading of rt on the coordinates of a position: met by that reading
   itself.
 - That they hold together: no theorem. The run metQKF at the end of this file finds true together,
   at a made-up shape, in both groups of layers: the equations and bounds of numbers in ClaimFits,
   the hypotheses of qkFits_of_layout, hrt, and that claimsT returns its claims. The switches hold
   at that shape by switchesR8 (Johnson/Road/FormsKeysRun8.lean), the sizes agree by sized_dimQ.
   What says which points and tables are meant (zeta, hz, hzh, RopeFits) is not evaluated: each can
   be met by a choice of ζ, z, zh and tb (zc_met; ropeFits_met). A run speaks of these numbers
   alone.

What is not claimed: that claimVal is what the verifier's settling of a claim on the matrix of
weights comes to; that the hidden value under a claim's slot is claimVal; anything on the panel's A
side or its weight. Nothing here is a statement on what a verifier's acceptance shows. The program
does not import this file.
-/
import Johnson.Road.FormsKeysClaim
import Johnson.Road.FormsKeysQK
import Johnson.Road.FormsKeysTn

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading eqTab Seg CallD WsGrp WsFac WsClaim WsShape)
open OnBytes.Model.Layer (ClaimEnv)
open Inst.Model (Tables TClaim)
open Inst.Model.Layout (Coord first units uQK)
open Inst.Model.FFSeg (Dim Pan Rd layerR call aC Dk sg eC zc pans AH kp)

/-! ## The three factors, by the group's name -/

/-- The factor that claimsT makes for a group of the unit of queries and keys of layer lam of the
group. ah, lfc: the two arrays of headWeights. -/
def facQK (c : ClaimEnv) (ah lfc : Array E) (lam : ℕ) (G : WsGrp) : Option WsFac :=
  if G.name == "hd" then some { AV := ah }
  else if G.name == "cd" then some { AV := c.ropeFactor (eqTab c.rt) lfc lam }
  else c.facRs G 0 (ceilLog2 c.v.y.h.d)

/-- For the group of the name hd. -/
theorem facQK_hd (c : ClaimEnv) (ah lfc : Array E) (lam : ℕ) {G : WsGrp} (hn : G.name = "hd") :
    facQK c ah lfc lam G = some { AV := ah } := by
  unfold facQK
  rw [hn]
  rfl

/-- For the group of the name cd. -/
theorem facQK_cd (c : ClaimEnv) (ah lfc : Array E) (lam : ℕ) {G : WsGrp} (hn : G.name = "cd") :
    facQK c ah lfc lam G = some { AV := c.ropeFactor (eqTab c.rt) lfc lam } := by
  unfold facQK
  rw [hn]
  rfl

/-- For the group of the name kk. -/
theorem facQK_kk (c : ClaimEnv) (ah lfc : Array E) (lam : ℕ) {G : WsGrp} (hn : G.name = "kk") :
    facQK c ah lfc lam G = c.facRs G 0 (ceilLog2 c.v.y.h.d) := by
  unfold facQK
  rw [hn]
  rfl

section Claim

variable {K : Type} [Field K]

/-! ## The library's point of one call -/

omit [Field K] in
/-- Every point is, on the coordinates of call c, the library's point of that call for some point z
of the whole lookup. For one call alone. -/
theorem zc_met (D : Dim) (c : Fin 8) (p : ℕ → K) : ∃ z : ℕ → K, ∀ j < aC D c, p j = zc D z c j := by
  refine ⟨fun t => if t < Dk D then p (t + eC D c) else p (t - (Dk D + (sg D - eC D c))),
    fun j hj => ?_⟩
  have h1 := Inst.Model.FFSeg.IndexFacts.Dk_le D c
  have e : eC D c = aC D c - Dk D := rfl
  simp only [zc]
  generalize eC D c = ec at *
  generalize Dk D = k at *
  generalize aC D c = a at *
  generalize sg D = σ at *
  by_cases hlt : j < ec
  · rw [if_pos hlt, if_neg (by omega)]
    exact congrArg p (by omega)
  · rw [if_neg hlt, if_pos (by omega)]
    exact congrArg p (by omega)

/-! ## One claim -/

variable (ρ : Reading K)

/-- The verifier's claim of the segment QK for layer lam of the group speaks, in any matrix W, of
the value that the library's panel QK has for the tensor claim of its row lam, at the weights that
the library's layout reads in W from layer L0 on. hcl: cl is the claim that claimsT makes for lam
(claimsT_QK_at of Johnson/Road/FormsKeysFold.lean). Asked: ClaimFits (the two layouts of the
weights, L0, the point ζ of the batched sumcheck); QKFits and that headWeights has returned; hrt and
RopeFits (the rotary tables); hz (the point of the call that holds QK reads as the library's); hzh
(zh agrees with the reading of rt). For every r: the row's tensor claim does not read it. -/
theorem claim_QK {c : ClaimEnv} {sW : WsShape} {D : Dim} {lk L0 : ℕ} {ζ : ℕ → K}
    (C : ClaimFits ρ c sW D lk L0 ζ) {q : ℕ} {cd : CallD} {sg : Seg} (F : QKFits c D q cd sg)
    {ah lfc : Array E} (h : c.headWeights = some (ah, lfc)) (hrt : c.rt.size = D.lT)
    {tb : Tables} {lam : ℕ} (hlam : lam < c.v.y.Lam) (R : RopeFits ρ c D tb L0 lam)
    {z zh : ℕ → K}
    (hz : ∀ j < aC D (call .QK), pt ρ (c.v.zk.getD q #[]) j = zc D z (call .QK) j)
    (hzh : ∀ j < D.lT, zh j = pt ρ c.rt j) (r : Rd K) (W : Wm K) {cl : WsClaim}
    (hcl : c.claim 0 lam (fun G =>
      if G.name == "hd" then some { AV := ah }
      else if G.name == "cd" then some { AV := c.ropeFactor (eqTab c.rt) lfc lam }
      else c.facRs G 0 (ceilLog2 c.v.y.h.d)) = some cl) :
    claimVal ρ c.wsLay W cl =
      Pan.QK.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ lam := by
  have hh : D.P.nq + D.P.nkv ≤ 64 := by
    rw [F.sized.nq, F.sized.nkv]
    exact F.heads
  have hX : (kindsOf (L0 + lam))[0]? = some 0 := by
    unfold kindsOf
    split <;> rfl
  have hU : (units D.P)[first D.P (L0 + lam) + 0]? = some (uQK D.P) :=
    tnOf_unit D tb C.even z zh ζ .QK rfl lam (C.layers lam hlam)
  have hcl' : c.claim 0 lam (facQK c ah lfc lam) = some cl := hcl
  rw [TnRow_QK D r tb L0 lk W z zh ζ hh lam]
  refine claim_Tn C W hcl' hlam hX hU
    (fs := [fun hd => if hd < D.P.nq + D.P.nkv then AH D z hd else 0, kp D tb L0 z zh lam,
      Pan.QK.Ec D ζ]) ?_
  intro u hOK hco hnm Fs hFs
  have hnm' : u.g.map (fun y => (y.name, y.cls)) = [("hd", 'A'), ("cd", 'A'), ("kk", 'E')] := hnm
  obtain ⟨g1, g2, g3, hg, n1, n2, n3⟩ := map_three hnm'
  have m3 : g3 ∈ u.g := by
    rw [hg]
    simp
  rw [hg] at hco hFs ⊢
  have a1 : g1.name = "hd" := congrArg Prod.fst n1
  have a2 : g2.name = "cd" := congrArg Prod.fst n2
  have a3 : g3.name = "kk" := congrArg Prod.fst n3
  have b1 : g1.cls = 'A' := congrArg Prod.snd n1
  have b2 : g2.cls = 'A' := congrArg Prod.snd n2
  have b3 : g3.cls = 'E' := congrArg Prod.snd n3
  have hco' : [coordOf g1, coordOf g2, coordOf g3] =
      [⟨64, .whole⟩, ⟨D.P.ch, .whole⟩, ⟨D.P.d, .low⟩] := hco
  have r2 : g2.R = D.P.ch := congrArg Coord.R (List.cons.inj (List.cons.inj hco').2).1
  have c1 : (g1.cls == 'E') = false := by
    rw [b1]
    rfl
  have c2 : (g2.cls == 'E') = false := by
    rw [b2]
    rfl
  have hp : Pan.QK ∈ pans D := by
    unfold pans
    simp
  have hwy : ceilLog2 c.v.y.h.d = Pan.QK.wcol D := by
    rw [ceilLog2_eq_clog, C.d]
    rfl
  have hcol := (F.chOK h).col
  refine facs_three hFs ?_ ?_ ?_
  · intro X hX v _
    rw [facQK_hd c ah lfc lam a1] at hX
    cases hX
    rw [fac_hd ρ F h g1 c1 v, AHP_eq_AH D hz v]
  · intro X hX v hv
    have hv' : v < c.v.y.h.dh := by
      rw [← F.sized.ch, ← r2]
      exact hv
    rw [facQK_cd c ah lfc lam a2] at hX
    cases hX
    rw [fac_cd ρ F h hrt R g2 c2 hv', ← kpP_zh D tb L0 _ hzh lam v,
      kpP_eq_kp D hcol tb L0 hz zh lam v]
  · intro X hX
    rw [facQK_kk c ah lfc lam a3] at hX
    exact Ec_at C hp b3 (size_of_ok hOK m3 b3) hwy hX

/-! ## All claims of the segment -/

/-- The list of claims that claimsT returns for the segment QK has one claim for each layer of the
group, and claim number lam speaks of the value of the tensor claim of row lam of the library's
panel QK. The hypotheses are those of claim_QK, with RopeFits for every layer of the group. -/
theorem claims_QK {c : ClaimEnv} {sW : WsShape} {D : Dim} {lk L0 : ℕ} {ζ : ℕ → K}
    (C : ClaimFits ρ c sW D lk L0 ζ) {q : ℕ} {cd : CallD} {sg : Seg} (F : QKFits c D q cd sg)
    (hrt : c.rt.size = D.lT) {tb : Tables}
    (R : ∀ lam, lam < c.v.y.Lam → RopeFits ρ c D tb L0 lam) {z zh : ℕ → K}
    (hz : ∀ j < aC D (call .QK), pt ρ (c.v.zk.getD q #[]) j = zc D z (call .QK) j)
    (hzh : ∀ j < D.lT, zh j = pt ρ c.rt j) (r : Rd K) (W : Wm K) {l : List WsClaim}
    (hl : c.claimsT "QK" = some l) :
    l.length = c.v.y.Lam ∧ ∀ lam (hlam : lam < l.length), claimVal ρ c.wsLay W l[lam] =
      Pan.QK.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ lam := by
  obtain ⟨hlen, ah, lfc, hw, hat⟩ := claimsT_QK_at c hl
  refine ⟨hlen, fun lam hlam => ?_⟩
  have e := hat lam hlam
  rw [List.getElem?_eq_getElem hlam] at e
  have hlam' : lam < c.v.y.Lam := by
    rw [← hlen]
    exact hlam
  exact claim_QK ρ C F hw hrt hlam' (R lam hlam') hz hzh r W e.symm

end Claim

/-! ## A run: the hypotheses that can be evaluated hold together -/

/-- The library's sizes for the made-up shape hR8 (Johnson/Road/FormsKeysRun8.lean), with the
vocabulary of 16 that the made-up shape of the weights has (wsShapeR,
Johnson/Road/FormsKeysRun.lean). -/
def dimQ : Dim := { dimOf hR8 with P := { (dimOf hR8).P with V := 16 } }

/-- These sizes agree with the shape. -/
theorem sized_dimQ : Sized hR8 dimQ := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- At the shape hR8 with the library's eight lines of calls, a layout of the weights with 6 column
bits and made-up points, for each group of layers: whether the nine equations of SizedW hold; the
fields of ClaimFits that are equations or bounds of numbers hold, with L0 the number of the group's
first layer; the hypotheses hn, hfl, hsz of qkFits_of_layout and hrt hold; and claimsT returns one
claim for each layer of the group. The field zeta of ClaimFits and the hypotheses hz and hzh say
what ζ, z and zh are, and RopeFits what the tables are: they are not evaluated. -/
def metQKF : Except String (List Bool) := do
  let y ← Model.Layer.layout hR8 pcR8
  let sc ← Model.Layer.scalesOf hR8 klR
  let rd ← Model.Layer.readsOf y
  let rope ← Model.Layer.ropeOf y.h
  let s := wsShapeR y
  let wsLay ← Model.wsLayOf s true 6
  let P := dimQ.P
  (List.range y.NGr).mapM fun g =>
    match envR y sc rd g with
    | none => throw "no tables"
    | some v =>
      let c : ClaimEnv := { v, wsLay, rope, rs := elemsR 400 10, rt := elemsR 900 y.h.lt }
      let L0 := g * y.Lam
      let sized := s.L == P.layers && s.d == P.d && s.dh == P.ch && s.dq == P.nq * P.ch &&
        s.dkv == P.nkv * P.ch && s.f == P.f && s.fe == P.fe && s.NE == P.nexp && s.V == P.V
      let fits := L0 % 2 == 0 && y.h.p3 && decide (L0 + y.Lam ≤ P.layers) && y.h.d == dimQ.d &&
        y.h.f == dimQ.f && y.h.fe == dimQ.fe && y.h.NE == dimQ.nx && y.dq == dimQ.dq &&
        y.Lam == dimQ.nl && y.LamM == dimQ.ne
      let call' := match v.callOf "QK" with
        | none => false
        | some (q, cd, _) =>
          (cd.segs.map (·.name)) == (Inst.Model.FFSeg.fams (call .QK)).map segName &&
            decide (hR8.nmin - hR8.ll - hR8.lt ≤
              Nat.clog 2 (Inst.Model.FFSeg.used dimQ (call .QK))) &&
            decide (y.h.ll + cd.lJ ≤ (v.zk.getD q #[]).size)
      let claims := match c.claimsT "QK" with
        | none => false
        | some l => l.length == y.Lam
      pure (sized && fits && call' && c.rt.size == dimQ.lT && claims)

#guard (match metQKF with
  | .ok r => r == [true, true]
  | .error _ => false)

#print axioms zc_met
#print axioms claim_QK
#print axioms claims_QK

end OnBytes.Road
