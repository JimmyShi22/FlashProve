-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysIdnL.lean: the two claims of a layer sub-proof's identities that read long
tables, in a world; and the text of three routines of the verifier, with names for their forms.

Johnson/Road/FormsKeysIdnW.lean treats the lines of the norms' ledgers and the selectors' sums. Two
more claims belong to the identities of a feed-forward segment. The third claim of claimsNorms
(OnBytes/Model/Layer.lean) ties the end value of the product layer of the squares to the limbs of
the residual stream: through it the slots of the nine sums W_s of each norm hang on the cells.
claimEmbedding, in the first group, ties the slot of the embedding's value to the stream that comes
in. Both read long tables: at the point Z_V, and at the point Z_E.

What is compared with what: the verifier's own forms with the library's bS and xS
(Inst/Model/FF/Trace.lean): limb l, and the value, of the stream at a place, a feature and a
position.

Main definitions: normsSum, embSum, hotSum: the three sums of forms, in the verifier's own letters.
Main theorems.
 - claimsNorms_eq, claimEmbedding_eq, claimsOneHot_eq: the verifier's three routines are written
   with these sums: each by rfl. So a theorem on normsSum, embSum or hotSum speaks of the form that
   the routine claims.
 - block_cell, entry_long: one entry of a true long table.
 - Fits.normsEnd (T-end): the third claim of claimsNorms.
 - Fits.embedding (T-emb): claimEmbedding's form.
 - Fits.hot: oneHot_value of FormsKeysIdnW.lean, on hotSum.

The hypotheses, and what shows that they can be met: Fits and TrueAt3, as in FormsKeysIdnW.lean;
that the tables are found and the sums return: lines of the verifier, evaluated in
Johnson/Road/FormsKeysIdnLRun.lean at a made-up shape, with the conclusions.

What is not claimed. All statements are identities in a world. The right sides are sums over blocks
and limbs, under the verifier's weights read in the field; that these weights are the equality
weights of one point over (norm | feature | position) is not stated here. The other side of (J11),
the weight claim on the embedding's matrix, is not treated. The routines' equations say how the text
reads, not what a run of it leaves. The program does not import this file.
-/
import Johnson.Road.FormsKeysIdnW

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff tenCell eqTab hiTab mustAs layerObject ledNS)
open OnBytes.Model.Layer (Env Lay Heard Pub Ten aff0 sumForms form claimsNorms claimEmbedding
  claimsOneHot)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell Arr idnVal bS xS)
open Blocks (ext)

variable {K : Type} [Field K]

/-! ## The verifier's three sums of forms, and its three routines -/

/-- The sum in the third claim of claimsNorms, in the verifier's letters. tI, tA: the first entries
of the tables of the stream that comes in and of af at Z_V; txs: the tensor xs; e: the weights of
the blocks; gp: the powers that batch the limbs. -/
def normsSum (y : Lay) (v : Env) (tI tA : ℕ) (txs : Ten) (e gp : Array E) : Option Aff :=
  sumForms (y.NI * (y.h.d / y.S2) * y.xb.nl) fun x =>
    let l := x % y.xb.nl
    let kh := x / y.xb.nl % (y.h.d / y.S2)
    let i := x / y.xb.nl / (y.h.d / y.S2)
    (if i == 0 then v.U3at tI (tenCell y.xb l 0 0 / y.S2 + kh)
     else v.U3at tA (tenCell txs.place l (i - 1) 0 / y.S2 + kh)).map fun a =>
      (a, negE (mulE (e.getD (i * y.Pd / y.S2 + kh) zeroE) (gp.getD l zeroE)))

/-- claimsNorms, with normsSum. -/
theorem claimsNorms_eq (P : Pub) (v : Env) (H : Heard) :
    claimsNorms P v H = (do
      layerObject H.wpl
      Model.SubM.lin (Aff.slot H.wpl.sL - Aff.slot H.wpl.sR)
      let txs ← form (P.y.T_ "xs")
      mustAs "plan-tensor-layout"
        (txs.nl == P.y.xb.nl && P.y.xb.nl == P.y.h.xl && ledNS P.y.h.xl == 2 * P.y.xb.nl - 1)
      let tI ← form (v.tabAt "xbI@Z_V")
      let tA ← form (v.tabAt "af@Z_V")
      let e ← form (hiTab H.wpl.r P.y.h.la (P.rd.lNI + P.y.lPd - P.y.ls)).toOption
      let sum ← form (normsSum P.y v tI tA txs e H.gp)
      Model.SubM.lin (Aff.slot H.wpl.sL + sum)) := rfl

/-- The sum in claimEmbedding's claim. t: the first entry of the table of the stream that comes in
at Z_E; tkh: the further coordinates of the embedding's feature. -/
def embSum (v : Env) (t : ℕ) (tkh : Array E) : Option Aff :=
  sumForms (v.y.h.d / v.y.S2) fun kh => (v.xbA t kh).map fun a => (a, (eqTab tkh).getD kh zeroE)

/-- claimEmbedding, with embSum. -/
theorem claimEmbedding_eq (v : Env) (H : Heard) (sVE : ℕ) :
    claimEmbedding v H sVE = (do
      let t ← form (v.tabAt "xbI@Z_E")
      let s ← form (embSum v t H.tkh)
      Model.SubM.lin ((Aff.slot sVE).scale (negE oneE) + s)) := rfl

/-- The sum of the selector's entries of the routed layer lm at the lookup's token point. -/
def hotSum (v : Env) (lm : ℕ) : Option Aff :=
  sumForms v.y.h.NE fun e => (v.shA "sel" "zt" lm e).map fun a => (a, oneE)

/-- claimsOneHot, with hotSum. -/
theorem claimsOneHot_eq (v : Env) :
    claimsOneHot v = (do
      if v.y.h.p3 then
        for lm in List.range v.y.LamM do
          let s ← form (hotSum v lm)
          Model.SubM.lin (Aff.ofConst (negE oneE) + s)) := rfl

/-! ## One entry of a true long table -/

/-- The feature of a block's member: block jh of layer i of a tensor whose layers begin at whole
blocks, member r. -/
theorem block_cell {S2 ls : ℕ} (hS2 : S2 = 2 ^ ls) (pl : Model.TenAt) (l i jh r : ℕ)
    (hal : S2 ∣ tenCell pl l i 0) :
    (tenCell pl l i 0 / S2 + jh) * 2 ^ ls + r = tenCell pl l i (jh * 2 ^ ls + r) := by
  obtain ⟨q, hq⟩ := hal
  have hpos : 0 < S2 := by rw [hS2]; positivity
  have e : tenCell pl l i (jh * 2 ^ ls + r) = tenCell pl l i 0 + (jh * 2 ^ ls + r) := rfl
  rw [e, hq, Nat.mul_div_cancel_left q hpos, ← hS2]
  ring

section Long

variable {ρ : Reading K} {W : World K} {v : Env} {c : Cells K} {t : Cell → K}

/-- One entry of a true long table: limb l of block jh of layer i of a tied array. -/
theorem entry_long {tb mat lt : ℕ} {A : Arr} {pl : Model.TenAt} {lo uu : ℕ → K}
    (T : Tied c t A mat pl) (R : LongTrue ρ W v tb mat v.y.ls lt c lo uu)
    (hS2 : v.y.S2 = 2 ^ v.y.ls) {l i jh : ℕ} (hal : v.y.S2 ∣ tenCell pl l i 0) {a : Aff}
    (h : v.U3at tb (tenCell pl l i 0 / v.y.S2 + jh) = some a) :
    a.value ρ W = ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lo r *
      ext lt (fun p => t ⟨A, l, i, jh * 2 ^ v.y.ls + r, p⟩) uu := by
  rw [R _ _ h]
  refine sum_congr rfl fun r _ => ?_
  rw [block_cell hS2 pl l i jh r hal]
  congr 2
  funext p
  exact (T.2 l i _ p).symm

variable [scl : Scl] {D : Dim} {low u lowV uV uP uR lowE uE : ℕ → K}
  (F : Fits ρ W v D c t low u) (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE)
include F

/-- (T-hot) on hotSum. -/
theorem Fits.hot (lm : ℕ) {s : Aff} (hs : hotSum v lm = some s) (emb : ℕ → ℕ → K)
    (tok : ℕ → ℕ) :
    (Aff.ofConst (negE oneE) + s).value ρ W =
      ext D.lT (fun i => idnVal D t emb tok (.j10 lm i)) u :=
  oneHot_value F lm hs emb tok

include T3

/-- (T-end) The form of the third claim of claimsNorms is worth the slot of the product layer's end
value, less the sum over the norms ν, the blocks kh of features and the limbs l, under the weight e
of (ν, kh) and the power gp of l, of limb l of the library's stream at place ν, extended over the
block's features and the positions at the point Z_V. x runs over (ν | kh | l), as in the
verifier. -/
theorem Fits.normsEnd {tI tA : ℕ} {txs : Ten} (hI : v.tabAt ("xbI" ++ "@" ++ "Z_V") = some tI)
    (hA : v.tabAt ("af" ++ "@" ++ "Z_V") = some tA) (hxs : v.y.T_ "xs" = some txs)
    (hNI : v.y.NI = D.nNu) (e gp : Array E) (sL : ℕ) {sum : Aff}
    (hs : normsSum v.y v tI tA txs e gp = some sum) :
    (Aff.slot sL + sum).value ρ W = W.slot sL -
      ∑ x ∈ range (v.y.NI * (v.y.h.d / v.y.S2) * v.y.xb.nl),
        ρ.val (e.getD (x / v.y.xb.nl / (v.y.h.d / v.y.S2) * v.y.Pd / v.y.S2 +
          x / v.y.xb.nl % (v.y.h.d / v.y.S2)) zeroE) * ρ.val (gp.getD (x % v.y.xb.nl) zeroE) *
        ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lowV r *
          ext D.lT (fun p => bS D t (x / v.y.xb.nl / (v.y.h.d / v.y.S2)) (x % v.y.xb.nl)
            (x / v.y.xb.nl % (v.y.h.d / v.y.S2) * 2 ^ v.y.ls + r) p) uV := by
  obtain ⟨_, _, _, txs', _, _, _, hxs', hm, T0, _, Ts, _, _, _, halb, hals⟩ := F.stream
  have et : txs' = txs := Option.some.inj (hxs'.symm.trans hxs)
  subst et
  -- the cell that the verifier's branch reads
  have h1 : sum.value ρ W = ∑ x ∈ range (v.y.NI * (v.y.h.d / v.y.S2) * v.y.xb.nl),
      -(ρ.val (e.getD (x / v.y.xb.nl / (v.y.h.d / v.y.S2) * v.y.Pd / v.y.S2 +
          x / v.y.xb.nl % (v.y.h.d / v.y.S2)) zeroE) * ρ.val (gp.getD (x % v.y.xb.nl) zeroE) *
        ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lowV r *
          ext D.lT (fun p =>
            if x / v.y.xb.nl / (v.y.h.d / v.y.S2) = 0 then
              t ⟨.x0, x % v.y.xb.nl, 0, x / v.y.xb.nl % (v.y.h.d / v.y.S2) * 2 ^ v.y.ls + r, p⟩
            else t ⟨.xs, x % v.y.xb.nl, x / v.y.xb.nl / (v.y.h.d / v.y.S2) - 1,
              x / v.y.xb.nl % (v.y.h.d / v.y.S2) * 2 ^ v.y.ls + r, p⟩) uV) := by
    refine sumForms_value ρ W _ _ _ ?_ hs
    intro x b k hx
    obtain ⟨a, ha, ek⟩ := map_some hx
    cases ek
    rw [F.num.neg, ρ.mul]
    by_cases h0 : x / v.y.xb.nl / (v.y.h.d / v.y.S2) = 0
    · rw [if_pos (by rw [h0]; rfl)] at ha
      rw [entry_long T0 (T3.xiV tI hI) F.S2 (halb _) ha]
      simp only [if_pos h0]
      ring
    · rw [if_neg (by simpa using h0)] at ha
      rw [entry_long Ts (by rw [hm]; exact T3.afV tA hA) F.S2 (hals _ _) ha]
      simp only [if_neg h0]
      ring
  rw [Aff.value_add, Aff.value_slot, h1, Finset.sum_neg_distrib, sub_eq_add_neg]
  congr 2
  refine sum_congr rfl fun x hx => ?_
  have hi : x / v.y.xb.nl / (v.y.h.d / v.y.S2) < 2 * D.nl := by
    have hx' := mem_range.mp hx
    rw [hNI] at hx'
    have e1 : D.nNu = 2 * D.nl := rfl
    rw [e1] at hx'
    exact Nat.div_lt_of_lt_mul (by
      rw [Nat.mul_comm]
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx'))
  congr 1
  refine sum_congr rfl fun r _ => ?_
  congr 2
  funext p
  unfold Inst.Model.FFSeg.bS Inst.Model.FFSeg.streamAt
  by_cases h0 : x / v.y.xb.nl / (v.y.h.d / v.y.S2) = 0
  · simp only [if_pos h0]
  · simp only [if_neg h0, if_neg (Nat.ne_of_lt hi)]

/-- (T-emb) The form of claimEmbedding's claim, in the first group, is worth the sum over the blocks
kh of features, under the equality weights of tkh, of the library's stream at place 0, extended over
the block's features and the positions at the point Z_E, less the slot of the embedding's value. -/
theorem Fits.embedding (h0 : v.g = 0) {tb : ℕ} (hb : v.tabAt ("xbI" ++ "@" ++ "Z_E") = some tb)
    (tkh : Array E) (sVE : ℕ) {s : Aff} (hs : embSum v tb tkh = some s) :
    ((Aff.slot sVE).scale (negE oneE) + s).value ρ W =
      ∑ kh ∈ range (v.y.h.d / v.y.S2), ρ.val ((eqTab tkh).getD kh zeroE) *
        ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lowE r *
          ext D.lT (fun p => xS D t 0 (kh * 2 ^ v.y.ls + r) p) uE - W.slot sVE := by
  obtain ⟨_, _, _, _, _, _, _, _, _, T0, _, _, _, _, _, halb, _⟩ := F.stream
  have h1 : s.value ρ W = ∑ kh ∈ range (v.y.h.d / v.y.S2), ρ.val ((eqTab tkh).getD kh zeroE) *
      ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lowE r *
        ext D.lT (fun p => xS D t 0 (kh * 2 ^ v.y.ls + r) p) uE := by
    refine sumForms_value ρ W _ _ _ ?_ hs
    intro kh b k hx
    obtain ⟨a, ha, ek⟩ := map_some hx
    cases ek
    rw [long_true F.num T0 (T3.xiE h0 tb hb) F.S2 halb ha]
    congr 1
    refine sum_congr rfl fun r _ => ?_
    congr 2
    funext p
    exact (xS_first D t _ p).symm
  rw [Aff.value_add, Aff.value_scale, Aff.value_slot, F.num.neg, ρ.one, h1]
  ring

end Long

#print axioms claimsNorms_eq
#print axioms claimEmbedding_eq
#print axioms claimsOneHot_eq
#print axioms entry_long
#print axioms Fits.hot
#print axioms Fits.normsEnd
#print axioms Fits.embedding

end OnBytes.Road
