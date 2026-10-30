-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ReadsThere.lean: where the verifier's lists of claims return, the verifier can name
every entry of the reads that the dictionaries of the ports speak of; so on true reads these entries
are worth the library's cells, extended.

Johnson/Road/K4/ReadsMeet.lean and ReadsMeetLong.lean say what an entry of the reads is worth on
true reads, for an entry that the verifier can name (U3at, rowCells or shA returns). Here that
premise is paid from the sums and lists of the verifier's claims, in the letters of
Johnson/Road/FormsKeysIdnL.lean (normsSum, hotSum), Johnson/Road/Rows/GatedEnds.lean (endForm) and
Johnson/Road/Rows/LayerEnds3S.lean (termsL): where a sum of forms returns, each of its terms is
there (foldForms_there in Johnson/Road/Rows/LayerHotPort.lean).

Main names:
  `norms_there`, `longA_there`, `endForm_there`: U3at returns at the places that normsSum, longA and
    endForm read.
  `sqI_clause`, `sqA_clause`: the stream's limbs at the squares' point, where normsSum returns.
  `gS_clause`, `gU_clause`: the tensors s and u at a product layer's point, where endForm returns.
  `termsRow_clause`, `termsSc_clause`, `termsSel_clause`: the rows, the scores and the selectors at
    rt, where termsL returns.
  `hotSel_clause`: the selectors at zt, where hotSum returns.
Limits. As ReadsMeet.lean and ReadsMeetLong.lean: Fits, PortFits, TrueAt2, TrueAt3 are premises, and
for s and u the truth of the table is a premise of its own (R), at any first entry tb. The ranges
are in the verifier's own numbers (v.y.NI, v.y.xb.nl, X.nl and so on), not in the library's sizes.
No library-side entry occurs. Nothing on soundness.


-/
import Johnson.Road.K4.ReadsMeet
import Johnson.Road.K4.ReadsMeetLong
import Johnson.Road.Rows.GatedEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open Finset
open OnBytes.Model (Reading World Aff tenCell)
open OnBytes.Model.Layer (Env Lay Ten)
open OnBytes.Road.Rows (readAtW foldForms_there endForm termsL)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell Arr)
open Cb.Pv.Lay.End (div_mod_at)

/-! ## The verifier can name the entries -/

/-- A pair of numbers as one. -/
theorem pair_lt' {a n i k : ℕ} (hi : i < a) (hk : k < n) : i * n + k < a * n := by
  calc i * n + k < i * n + n := by omega
    _ = (i + 1) * n := by ring
    _ ≤ a * n := Nat.mul_le_mul_right _ hi

/-- Where normsSum returns, the read of limb l of block kh of the stream at norm i is there. -/
theorem norms_there {y : Lay} {v : Env} {tI tA : ℕ} {txs : Ten} {e gp : Array E} {s : Aff}
    (h : normsSum y v tI tA txs e gp = some s) {i kh l : ℕ} (hi : i < y.NI)
    (hk : kh < y.h.d / y.S2) (hl : l < y.xb.nl) :
    ∃ a, (if (i == 0) = true then v.U3at tI (tenCell y.xb l 0 0 / y.S2 + kh)
      else v.U3at tA (tenCell txs.place l (i - 1) 0 / y.S2 + kh)) = some a := by
  unfold normsSum at h
  obtain ⟨t, ht⟩ := foldForms_there _ (List.range _) _ _ h
    ((i * (y.h.d / y.S2) + kh) * y.xb.nl + l)
    (List.mem_range.mpr (pair_lt' (pair_lt' hi hk) hl))
  obtain ⟨a, ha, _⟩ := map_some ht
  obtain ⟨d1, d2⟩ := div_mod_at (i * (y.h.d / y.S2) + kh) l y.xb.nl hl
  obtain ⟨d3, d4⟩ := div_mod_at i kh (y.h.d / y.S2) hk
  rw [d1, d2, d3, d4] at ha
  exact ⟨a, ha⟩

/-- Where longA returns, each limb's read is there. -/
theorem longA_there {v : Env} {t : ℕ} {X : Ten} {i jh : ℕ} {a : Aff}
    (h : v.longA t X i jh = some a) {l : ℕ} (hl : l < X.nl) :
    ∃ a', v.U3at t (tenCell X.place l i 0 / v.y.S2 + jh) = some a' := by
  unfold Env.longA Env.limbs at h
  obtain ⟨x, hx⟩ := foldForms_there _ (List.range X.nl) _ _ h l (List.mem_range.mpr hl)
  obtain ⟨a', ha', _⟩ := map_some hx
  exact ⟨a', ha'⟩

/-- Where endForm returns, each limb's read of each of its blocks is there. -/
theorem endForm_there {v : Env} {t : ℕ} {X : Ten} {e : Array E} {rows blocks stride : ℕ}
    {lamOf : ℕ → ℕ} {first : ℕ} {a : Aff}
    (h : endForm v t X e rows blocks stride lamOf first = some a) {x : ℕ}
    (hx : x < rows * blocks) {l : ℕ} (hl : l < X.nl) :
    ∃ a', v.U3at t (tenCell X.place l (lamOf (x / blocks)) 0 / v.y.S2 + (first + x % blocks)) =
      some a' := by
  unfold endForm at h
  obtain ⟨z, hz⟩ := foldForms_there _ (List.range _) _ _ h x (List.mem_range.mpr hx)
  obtain ⟨b, hb, _⟩ := map_some hz
  exact longA_there hb hl

/-! ## The clauses -/

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} {v : Env} {c : Cells K}
  {t : Cell → K} [scl : Scl] {D : Dim} {low u lowV uV uP uR lowE uE low' u' z zh : ℕ → K}

/-- The stream that comes in, at the squares' point: all limbs and blocks that normsSum reads. -/
theorem sqI_clause (F : Fits ρ W v D c t low u) (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE)
    {tI tA : ℕ} {txs : Ten} {e gp : Array E} {s : Aff} (hI : v.tabAt "xbI@Z_V" = some tI)
    (h : normsSum v.y v tI tA txs e gp = some s) (h0 : 0 < v.y.NI) :
    ∀ l kh, l < v.y.xb.nl → kh < v.y.h.d / v.y.S2 →
      readAtW W v tI (tenCell v.y.xb l 0 0 / v.y.S2 + kh) =
        ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lowV r *
          Blocks.ext D.lT (fun p => t ⟨.x0, l, 0, kh * 2 ^ v.y.ls + r, p⟩) uV := by
  intro l kh hl hk
  obtain ⟨a, ha⟩ := norms_there h h0 hk hl
  exact sqI_meet F T3 tI hI l kh a ha

/-- The stream after write number i of the group, 0 < i, at the squares' point. -/
theorem sqA_clause (F : Fits ρ W v D c t low u) (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE)
    {tI tA : ℕ} {txs : Ten} {e gp : Array E} {s : Aff} (hA : v.tabAt "af@Z_V" = some tA)
    (hxs : v.y.T_ "xs" = some txs) (h : normsSum v.y v tI tA txs e gp = some s) :
    ∀ i l kh, 0 < i → i < v.y.NI → l < v.y.xb.nl → kh < v.y.h.d / v.y.S2 →
      readAtW W v tA (tenCell txs.place l (i - 1) 0 / v.y.S2 + kh) =
        ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lowV r *
          Blocks.ext D.lT (fun p => t ⟨.xs, l, i - 1, kh * 2 ^ v.y.ls + r, p⟩) uV := by
  intro i l kh h0 hi hl hk
  obtain ⟨a, ha⟩ := norms_there h hi hk hl
  have hn : ¬ (i == 0) = true := by
    simp
    omega
  rw [if_neg hn] at ha
  exact sqA_meet F T3 tA txs hA hxs (i - 1) l kh a ha

/-- The tensor s at a product layer's point: all limbs and blocks that endForm reads. R: the table
that begins at tb is true of the tensor's matrix at lo, uu. -/
theorem gS_clause (F : Fits ρ W v D c t low u) {X : Ten} (hX : v.y.T_ "s" = some X) {tb : ℕ}
    {lo uu : ℕ → K} (R : LongTrue ρ W v tb X.mat v.y.ls D.lT c lo uu) {e : Array E}
    {rows blocks stride : ℕ} {lamOf : ℕ → ℕ} {first : ℕ} {a : Aff}
    (h : endForm v tb X e rows blocks stride lamOf first = some a) :
    ∀ x, x < rows * blocks → ∀ l, l < X.nl →
      readAtW W v tb (tenCell X.place l (lamOf (x / blocks)) 0 / v.y.S2 + (first + x % blocks)) =
        ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lo r * Blocks.ext D.lT (fun p =>
          t ⟨.sl, l, lamOf (x / blocks), (first + x % blocks) * 2 ^ v.y.ls + r, p⟩) uu := by
  intro x hx l hl
  obtain ⟨a', ha'⟩ := endForm_there h hx hl
  exact gS_meet F hX R ha'

/-- The tensor u: as gS_clause. -/
theorem gU_clause (F : Fits ρ W v D c t low u) {X : Ten} (hX : v.y.T_ "u" = some X) {tb : ℕ}
    {lo uu : ℕ → K} (R : LongTrue ρ W v tb X.mat v.y.ls D.lT c lo uu) {e : Array E}
    {rows blocks stride : ℕ} {lamOf : ℕ → ℕ} {first : ℕ} {a : Aff}
    (h : endForm v tb X e rows blocks stride lamOf first = some a) :
    ∀ x, x < rows * blocks → ∀ l, l < X.nl →
      readAtW W v tb (tenCell X.place l (lamOf (x / blocks)) 0 / v.y.S2 + (first + x % blocks)) =
        ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lo r * Blocks.ext D.lT (fun p =>
          t ⟨.up, l, lamOf (x / blocks), (first + x % blocks) * 2 ^ v.y.ls + r, p⟩) uu := by
  intro x hx l hl
  obtain ⟨a', ha'⟩ := endForm_there h hx hl
  exact gU_meet F hX R ha'

/-- The norms' rows at rt, in the binders of TermsDict.row, where termsL returns and a row has five
limbs. -/
theorem termsRow_clause (F : Fits ρ W v D c t low u) (T2 : TrueAt2 ρ W v D.lT c low' u')
    (h5 : v.y.h.xl = 5) {sEnd : ℕ} {l : List Aff} (h : termsL v sEnd = some l) :
    ∀ tb tr, v.tabAt ("ar@" ++ "rt") = some tb → v.y.T_ "row" = some tr →
      ∀ ν n, ν < v.y.NN * v.y.Lam → n < 99 → readAtW W v tb (tr.OFF + ν * 99 + n) =
        Blocks.ext D.lT (fun p => t ⟨.D, 0, ν, n, p⟩) u' := by
  intro tb tr hb htr ν n hν hn
  unfold termsL at h
  obtain ⟨la, _, ha, _, _⟩ := appL_some h
  obtain ⟨x, hx, _⟩ := mem_flat ha (List.mem_range.mpr hν)
  obtain ⟨g, hg, _⟩ := bind_some hx
  unfold Env.rowR at hg
  have hb5 : (v.y.h.xl == 5) = true := by rw [h5]; rfl
  rw [if_pos hb5] at hg
  obtain ⟨row, hr, _⟩ := map_some hg
  unfold Env.row5At at hr
  obtain ⟨cells, hc, _⟩ := bind_some hr
  exact row_meet_T F T2 hc tb tr hb htr n hn

/-- The scores at rt, in the binders of TermsDict.sc, where termsL returns, with routed experts. -/
theorem termsSc_clause (P : PortFits ρ W v D c t low z zh) {sEnd : ℕ} {l : List Aff}
    (h : termsL v sEnd = some l) :
    ∀ X tb, v.tensorAt "sc" "rt" = some (X, tb) → ∀ lm k, lm < v.y.LamM → k < X.nl →
      readAtW W v tb (tenCell X.place k lm 0) =
        Blocks.ext D.lT (fun p => t ⟨.sc, k, lm, 0, p⟩) zh := by
  intro X tb hX lm k hlm hk
  unfold termsL at h
  obtain ⟨_, lb, _, hb, _⟩ := appL_some h
  rw [if_pos P.fits.p3] at hb
  obtain ⟨lc, _, hc, _, _⟩ := appL_some hb
  obtain ⟨x, hx, _⟩ := mem_flat hc (List.mem_range.mpr hlm)
  obtain ⟨g, hg, _⟩ := bind_some hx
  exact sc_meet_T P hg X tb hX k hk

/-- The selectors at rt, in the binders of TermsDict.sel, where termsL returns. -/
theorem termsSel_clause (P : PortFits ρ W v D c t low z zh) {sEnd : ℕ} {l : List Aff}
    (h : termsL v sEnd = some l) :
    ∀ X tb, v.tensorAt "sel" "rt" = some (X, tb) → ∀ lm x k, lm < v.y.LamM → x < v.y.h.NE →
      k < X.nl → readAtW W v tb (tenCell X.place k lm x) =
        Blocks.ext D.lT (fun p => t ⟨.sel, k, lm, x, p⟩) zh := by
  intro X tb hX lm x k hlm hx hk
  unfold termsL at h
  obtain ⟨_, lb, _, hb, _⟩ := appL_some h
  rw [if_pos P.fits.p3] at hb
  obtain ⟨_, ld, _, hd, _⟩ := appL_some hb
  obtain ⟨q, hq, _⟩ := mem_flat hd (List.mem_range.mpr (pair_lt' hlm hx))
  obtain ⟨g, hg, _⟩ := bind_some hq
  obtain ⟨d1, d2⟩ := div_mod_at lm x v.y.h.NE hx
  rw [d1, d2] at hg
  exact sel_meet_T P hg X tb hX k hk

/-- The selectors at zt, in the binders of HotDict.sel, where hotSum returns for the layer. -/
theorem hotSel_clause (F : Fits ρ W v D c t low u) {lm : ℕ} {s : Aff} (h : hotSum v lm = some s) :
    ∀ X tb, v.tensorAt "sel" "zt" = some (X, tb) → ∀ x k, x < v.y.h.NE → k < X.nl →
      readAtW W v tb (tenCell X.place k lm x) =
        Blocks.ext D.lT (fun p => t ⟨.sel, k, lm, x, p⟩) u := by
  intro X tb hX x k hx hk
  unfold hotSum at h
  obtain ⟨q, hq⟩ := foldForms_there _ (List.range _) _ _ h x (List.mem_range.mpr hx)
  obtain ⟨a, ha, _⟩ := map_some hq
  exact sel_meet_Z F ha X tb hX k hk

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.norms_there
#print axioms OnBytes.Road.K4.endForm_there
#print axioms OnBytes.Road.K4.sqI_clause
#print axioms OnBytes.Road.K4.sqA_clause
#print axioms OnBytes.Road.K4.gS_clause
#print axioms OnBytes.Road.K4.gU_clause
#print axioms OnBytes.Road.K4.termsRow_clause
#print axioms OnBytes.Road.K4.termsSc_clause
#print axioms OnBytes.Road.K4.termsSel_clause
#print axioms OnBytes.Road.K4.hotSel_clause
