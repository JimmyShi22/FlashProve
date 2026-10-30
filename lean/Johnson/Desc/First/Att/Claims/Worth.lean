-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/Worth.lean: kind K5: what the readers' written forms are worth in the
entries of the array of tables: each reader's form is worth a written weighted sum of entries of
array number h.iU3, read at K columns. It is the first half of the road from the equations "slot =
reader's form" (Johnson/Desc/First/Att/Claims/Say.lean, Johnson/Desc/First/Att/Claims/Say58.lean) to
"slot = the typed map at the point". The second half, what an entry of a table means (a sum over a
block of a committed matrix's rows under the table's weight vector), is what the smallness test is
meant to give, and is not touched here.

Main names:
  `ent W h K x`: the worth of entry number x of the array of tables: W.entry h.iU3 (x / K) (x % K).
  `weightedF_value`, `lessF_value`: a weighted sum, and a start less the pieces' weighted sum, as
    sums in the ring.
  `planeF_value`, `shVF_value`, `overGF_value`, `readMaximumF_value`, `readDenominatorF_value`,
    `readIndexBitF_value`, `xlT_value` (where the cut and the head's features are lawful),
    `readHeadT_value`, `readGroupT_value`.
Used of OnBytes: plain records, pure functions and lemmas on them alone; no routine in a context and
no theorem on a run: the written forms Fo.…F and Fo.…T; Aff.value and its lemmas; Reading; World;
the pure functions Model.eqTab, cutLast, headFeat, tenCell, Attention.limbWeights.
Not claimed: what an entry means.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.Say58

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention

variable {Kf : Type} [CommRing Kf] (ρ : Reading Kf) (W : World Kf)

/-- The worth of entry number x of the array of tables, read at K columns. -/
def ent (h : Attention.Heard) (K x : ℕ) : Kf := W.entry h.iU3 (x / K) (x % K)

theorem u3Form_value (h : Attention.Heard) (K x : ℕ) : (Fo.u3Form h.iU3 K x).value ρ W = ent W h K x := by
  unfold Fo.u3Form ent
  rw [Aff.value_ent]

theorem foldl_pos {α : Type} (fv : α → Aff) (c : α → E) : ∀ (l : List α) (s : Aff),
    (l.foldl (fun s a => Aff.addMul s (fv a) (c a)) s).value ρ W =
      s.value ρ W + (l.map fun a => ρ.val (c a) * (fv a).value ρ W).sum
  | [], s => by simp
  | a :: l, s => by
    rw [List.foldl_cons, foldl_pos fv c l, Aff.value_addMul, List.map_cons, List.sum_cons]
    ring

theorem weightedF_value (n : ℕ) (w : Array E) (fv : ℕ → Aff) :
    (Fo.weightedF n w fv).value ρ W =
      ((List.range n).map fun i => ρ.val (w.getD i zeroE) * (fv i).value ρ W).sum := by
  unfold Fo.weightedF
  rw [foldl_pos ρ W fv (fun i => w.getD i zeroE), Aff.value_ofConst, ρ.zero, zero_add]

theorem lessF_value (start : Aff) (pw : Array PW) (fv : PW → Aff) :
    (Fo.lessF start pw fv).value ρ W =
      start.value ρ W - (pw.toList.map fun w => ρ.val w.wp * (fv w).value ρ W).sum := by
  unfold Fo.lessF
  rw [foldl_neg ρ W fv (fun w : PW => w.wp) _ _ (Aff.ofConst zeroE),
    foldl_pos ρ W fv (fun w : PW => w.wp)]
  ring

variable (h : Attention.Heard) (K : ℕ)

theorem planeF_value (t x lam a : ℕ) (z : Array E) (isD : Bool) :
    (Fo.planeF h K t x lam a z isD).value ρ W =
      ((List.range (eqTab (z.extract 0 ((if isD = true then h.S.nD else h.S.nM) - h.S.cf.lmS))).size).map
        fun hi => ρ.val ((eqTab (z.extract 0 ((if isD = true then h.S.nD else h.S.nM) - h.S.cf.lmS))).getD hi
            zeroE) *
          ent W h K (t + (((if isD = true then (5 * h.S.Lam * h.S.HA) <<< h.S.nM else 0) +
            ((x * h.S.Lam + lam) * h.S.HA + a) <<< if isD = true then h.S.nD else h.S.nM) >>>
              h.S.cf.lmS + hi))).sum := by
  unfold Fo.planeF
  rw [weightedF_value]
  simp only [u3Form_value]

theorem shVF_value (t off nl J lam j : ℕ) :
    (Fo.shVF h K t off nl J lam j).value ρ W =
      ((List.range nl).map fun l => ρ.val ((limbWeights nl).getD l zeroE) *
        ent W h K (t + (off + (l * h.S.Lam + lam) * J + j))).sum := by
  unfold Fo.shVF
  rw [weightedF_value]
  simp only [u3Form_value]

theorem overGF_value (zg : Array E) (fv : ℕ → Aff) :
    (Fo.overGF h zg fv).value ρ W =
      ((List.range h.S.G).map fun g => ρ.val ((eqTab (zg.extract 0 h.S.cf.lgk)).getD g zeroE) *
        (fv g).value ρ W).sum := by
  unfold Fo.overGF
  rw [weightedF_value]

theorem readMaximumF_value (t : ℕ) (zg : Array E) (lam a : ℕ) :
    (Fo.readMaximumF h K t zg lam a).value ρ W =
      ((List.range h.S.G).map fun g => ρ.val ((eqTab (zg.extract 0 h.S.cf.lgk)).getD g zeroE) *
        ((List.range 4).map fun l => ρ.val ((limbWeights 4).getD l zeroE) *
          ent W h K (t + (h.S.oMr + (l * h.S.Lam + lam) * h.S.cf.H + (g * h.S.HA + a)))).sum).sum := by
  unfold Fo.readMaximumF
  rw [overGF_value]
  simp only [shVF_value]

theorem readDenominatorF_value (t : ℕ) (zg : Array E) (lam a : ℕ) :
    (Fo.readDenominatorF h K t zg lam a).value ρ W =
      ((List.range h.S.G).map fun g => ρ.val ((eqTab (zg.extract 0 h.S.cf.lgk)).getD g zeroE) *
        ((List.range 4).map fun l => ρ.val ((limbWeights 4).getD l zeroE) *
          ent W h K (t + (h.S.oZr + (l * h.S.Lam + lam) * h.S.cf.H + (g * h.S.HA + a)))).sum).sum := by
  unfold Fo.readDenominatorF
  rw [overGF_value]
  simp only [shVF_value]

theorem readIndexBitF_value (t : ℕ) (zg : Array E) (lam a b : ℕ) :
    (Fo.readIndexBitF h K t zg lam a b).value ρ W =
      ((List.range h.S.G).map fun g => ρ.val ((eqTab (zg.extract 0 h.S.cf.lgk)).getD g zeroE) *
        ((List.range 1).map fun l => ρ.val ((limbWeights 1).getD l zeroE) *
          ent W h K (t + (h.S.oIb + (l * h.S.Lam + lam) * (h.S.cf.lt * h.S.cf.H) +
            (b * h.S.cf.H + g * h.S.HA + a)))).sum).sum := by
  unfold Fo.readIndexBitF
  rw [overGF_value]
  simp only [shVF_value]

/-- A tensor's head at a point of features, where the cut and the head's features are lawful. -/
theorem xlT_value (t : ℕ) (X : TenAt) (lam hd : ℕ) (zc : Array E) (cut : Array E × Array E) (j0 : ℕ)
    (hc : cutLast (zc.extract 0 h.S.cf.ldh) h.S.ls = .ok cut) (hj : headFeat X hd h.S.dh = .ok j0) :
    (Fo.xlT h K t X lam hd zc).value ρ W =
      ((List.range (eqTab cut.1).size).map fun ch => ρ.val ((eqTab cut.1).getD ch zeroE) *
        ((List.range X.nl).map fun l => ρ.val ((limbWeights X.nl).getD l zeroE) *
          ent W h K (t + (tenCell X l lam j0 / 2 ^ h.S.ls + ch))).sum).sum := by
  unfold Fo.xlT Fo.xlF
  rw [hc, hj]
  show (Fo.weightedF _ _ _).value ρ W = _
  rw [weightedF_value]
  simp only [weightedF_value, u3Form_value]

theorem readHeadT_value (t : ℕ) (X : TenAt) (zg zc : Array E) (lam a : ℕ) :
    (Fo.readHeadT h K t X zg zc lam a).value ρ W =
      ((List.range h.S.G).map fun g => ρ.val ((eqTab (zg.extract 0 h.S.cf.lgk)).getD g zeroE) *
        (Fo.xlT h K t X lam (g * h.S.HA + a) zc).value ρ W).sum := by
  unfold Fo.readHeadT
  rw [overGF_value]

theorem readGroupT_value (t : ℕ) (X : TenAt) (zg zc : Array E) (lam : ℕ) :
    (Fo.readGroupT h K t X zg zc lam).value ρ W =
      ((List.range h.S.G).map fun g => ρ.val ((eqTab (zg.extract 0 h.S.cf.lgk)).getD g zeroE) *
        (Fo.xlT h K t X lam g zc).value ρ W).sum := by
  unfold Fo.readGroupT
  rw [overGF_value]

end K5Law
