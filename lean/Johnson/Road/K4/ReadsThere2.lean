-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ReadsThere2.lean: the clauses of Johnson/Road/K4/ReadsThere.lean once more, in the
binders and ranges of the ports' dictionaries; and in which matrix, with how many limbs, a tensor of
an admitted layout lies.

The dictionaries FrontDict (Johnson/Road/K4/ValuesOfClaims.lean), TermsDict
(Johnson/Road/Rows/LayerTermsPort.lean) and HotDict (Johnson/Road/Rows/LayerHotPort.lean) speak in
the library's sizes and of every first entry and tensor that the verifier finds under a name.
ReadsThere.lean speaks in the verifier's own numbers, of one first entry. Here the two are joined,
under equations between the sizes as premises.

Main names:
  `ten_facts`: the tensor that an admitted layout has under an array's name lies in the array's
    matrix and has the library's number of cells (from ten_of,
    Johnson/Road/FormsKeysFits.lean). So the tensors s and u lie in matrix 0 and have two limbs.
  `tensorAt_T`: what tensorAt finds is the layout's tensor of that name.
  `sqI_dict`, `sqA_dict`, `gS_dict`, `gU_dict`, `termsRow_dict`, `termsSc_dict`, `termsSel_dict`,
    `hotSel_dict`: the clauses.
Limits. As ReadsThere.lean. The right sides are extensions of cells: no library-side entry occurs.
Laid, Switches, Fits, PortFits, TrueAt2, TrueAt3 and the equations between the sizes are premises.
For s and u the truth of the table at matrix 0 is a premise (R0), at a first entry tb that nothing
here ties to a name. One environment v: a layout under another letter is not spoken of. Nothing on
soundness.


-/
import Johnson.Road.K4.ReadsThere

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open Finset
open OnBytes.Model (Reading World Aff tenCell)
open OnBytes.Model.Layer (Env Lay Ten)
open OnBytes.Road.Rows (readAtW endForm termsL)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell Arr)

/-! ## Where a tensor lies -/

/-- The tensor that an admitted layout has under the name of a listed array lies in the array's
matrix and has the library's number of cells for limbs. -/
theorem ten_facts {y : Lay} (L : Laid y) (S : Switches y.h) (A : Arr) (hA : listed A = true)
    {X : Ten} (hX : y.T_ (arrName A) = some X) : X.mat = matNo A ∧ X.nl = A.nCell := by
  obtain ⟨ten, h1, h2, h3, _⟩ := ten_of L S A (Or.inl hA)
  obtain rfl : ten = X := Option.some.inj (h1.symm.trans hX)
  exact ⟨h2, h3⟩

/-- What tensorAt finds under a name is the layout's tensor of that name. -/
theorem tensorAt_T {v : Env} {Xn Z : String} {X : Ten} {tb : ℕ}
    (h : v.tensorAt Xn Z = some (X, tb)) : v.y.T_ Xn = some X := by
  unfold Env.tensorAt at h
  obtain ⟨tn, htn, h2⟩ := bind_some h
  obtain ⟨tb', _, h3⟩ := bind_some h2
  obtain rfl : tn = X := (Prod.mk.inj (Option.some.inj h3)).1
  exact htn

/-! ## The clauses in the dictionaries' binders -/

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} {v : Env} {c : Cells K}
  {t : Cell → K} [scl : Scl] {D : Dim} {low u lowV uV uP uR lowE uE low' u' z zh : ℕ → K}

/-- FrontDict.sqI. B: the blocks of the stream's width. -/
theorem sqI_dict (F : Fits ρ W v D c t low u) (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE)
    {tI tA : ℕ} {txs : Ten} {e gp : Array E} {s : Aff} (hI : v.tabAt "xbI@Z_V" = some tI)
    (h : normsSum v.y v tI tA txs e gp = some s) {B : ℕ} (hNI : v.y.NI = D.nNu)
    (h0 : 0 < D.nNu) (nl5 : v.y.xb.nl = 5) (hB : v.y.h.d / v.y.S2 = B) :
    ∀ tI', v.tabAt "xbI@Z_V" = some tI' → ∀ l kh, l < 5 → kh < B →
      readAtW W v tI' (tenCell v.y.xb l 0 0 / v.y.S2 + kh) =
        ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lowV r *
          Blocks.ext D.lT (fun p => t ⟨.x0, l, 0, kh * 2 ^ v.y.ls + r, p⟩) uV := by
  intro tI' hI' l kh hl hk
  obtain rfl : tI = tI' := Option.some.inj (hI.symm.trans hI')
  exact sqI_clause F T3 hI h (by rw [hNI]; exact h0) l kh (by rw [nl5]; exact hl)
    (by rw [hB]; exact hk)

/-- FrontDict.sqA. -/
theorem sqA_dict (F : Fits ρ W v D c t low u) (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE)
    {tI tA : ℕ} {txs : Ten} {e gp : Array E} {s : Aff} (hA : v.tabAt "af@Z_V" = some tA)
    (hxs : v.y.T_ "xs" = some txs) (h : normsSum v.y v tI tA txs e gp = some s) {B : ℕ}
    (hNI : v.y.NI = D.nNu) (nl5 : v.y.xb.nl = 5) (hB : v.y.h.d / v.y.S2 = B) :
    ∀ tA' txs', v.tabAt "af@Z_V" = some tA' → v.y.T_ "xs" = some txs' →
      ∀ i l kh, 0 < i → i < D.nNu → l < 5 → kh < B →
        readAtW W v tA' (tenCell txs'.place l (i - 1) 0 / v.y.S2 + kh) =
          ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lowV r *
            Blocks.ext D.lT (fun p => t ⟨.xs, l, i - 1, kh * 2 ^ v.y.ls + r, p⟩) uV := by
  intro tA' txs' hA' hxs' i l kh h0 hi hl hk
  obtain rfl : tA = tA' := Option.some.inj (hA.symm.trans hA')
  obtain rfl : txs = txs' := Option.some.inj (hxs.symm.trans hxs')
  exact sqA_clause F T3 hA hxs h i l kh h0 (by rw [hNI]; exact hi) (by rw [nl5]; exact hl)
    (by rw [hB]; exact hk)

/-- FrontDict.g5S and g6S, behind their first two binders: the tensor s has two limbs, and its reads
at all places that endForm names. R0: the table that begins at tb is true of matrix 0. -/
theorem gS_dict (F : Fits ρ W v D c t low u) (L : Laid v.y) (S : Switches v.y.h) {X : Ten}
    (hX : v.y.T_ "s" = some X) {tb : ℕ} {lo uu : ℕ → K}
    (R0 : LongTrue ρ W v tb 0 v.y.ls D.lT c lo uu) {e : Array E} {rows blocks stride : ℕ}
    {lamOf : ℕ → ℕ} {first : ℕ} {a : Aff}
    (h : endForm v tb X e rows blocks stride lamOf first = some a) :
    X.nl = 2 ∧ ∀ x, x < rows * blocks → ∀ l, l < 2 →
      readAtW W v tb (tenCell X.place l (lamOf (x / blocks)) 0 / v.y.S2 + (first + x % blocks)) =
        ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lo r * Blocks.ext D.lT (fun p =>
          t ⟨.sl, l, lamOf (x / blocks), (first + x % blocks) * 2 ^ v.y.ls + r, p⟩) uu := by
  obtain ⟨hm, hn⟩ := ten_facts L S .sl rfl hX
  have hm0 : X.mat = 0 := hm
  have hn2 : X.nl = 2 := hn
  exact ⟨hn2, fun x hx l hl => gS_clause F hX (by rw [hm0]; exact R0) h x hx l
    (by rw [hn2]; exact hl)⟩

/-- FrontDict.g5U and g6U: as gS_dict, for the tensor u. -/
theorem gU_dict (F : Fits ρ W v D c t low u) (L : Laid v.y) (S : Switches v.y.h) {X : Ten}
    (hX : v.y.T_ "u" = some X) {tb : ℕ} {lo uu : ℕ → K}
    (R0 : LongTrue ρ W v tb 0 v.y.ls D.lT c lo uu) {e : Array E} {rows blocks stride : ℕ}
    {lamOf : ℕ → ℕ} {first : ℕ} {a : Aff}
    (h : endForm v tb X e rows blocks stride lamOf first = some a) :
    X.nl = 2 ∧ ∀ x, x < rows * blocks → ∀ l, l < 2 →
      readAtW W v tb (tenCell X.place l (lamOf (x / blocks)) 0 / v.y.S2 + (first + x % blocks)) =
        ∑ r ∈ range (2 ^ v.y.ls), Blocks.eqN v.y.ls 0 lo r * Blocks.ext D.lT (fun p =>
          t ⟨.up, l, lamOf (x / blocks), (first + x % blocks) * 2 ^ v.y.ls + r, p⟩) uu := by
  obtain ⟨hm, hn⟩ := ten_facts L S .up rfl hX
  have hm0 : X.mat = 0 := hm
  have hn2 : X.nl = 2 := hn
  exact ⟨hn2, fun x hx l hl => gU_clause F hX (by rw [hm0]; exact R0) h x hx l
    (by rw [hn2]; exact hl)⟩

/-- TermsDict.row. -/
theorem termsRow_dict (F : Fits ρ W v D c t low u) (T2 : TrueAt2 ρ W v D.lT c low' u')
    (hN : v.y.NN * v.y.Lam = D.nNu) {sEnd : ℕ} {l : List Aff} (h : termsL v sEnd = some l) :
    ∀ tb tr, v.tabAt ("ar@" ++ "rt") = some tb → v.y.T_ "row" = some tr →
      ∀ ν n, ν < D.nNu → n < 99 → readAtW W v tb (tr.OFF + ν * 99 + n) =
        Blocks.ext D.lT (fun p => t ⟨.D, 0, ν, n, p⟩) u' :=
  fun tb tr hb htr ν n hν hn =>
    termsRow_clause F T2 F.xl h tb tr hb htr ν n (by rw [hN]; exact hν) hn

/-- TermsDict.sc. -/
theorem termsSc_dict (P : PortFits ρ W v D c t low z zh) (L : Laid v.y) (S : Switches v.y.h)
    {sEnd : ℕ} {l : List Aff} (h : termsL v sEnd = some l) :
    ∀ X tb, v.tensorAt "sc" "rt" = some (X, tb) → X.nl = 3 ∧
      ∀ lm k, lm < D.ne → k < 3 → readAtW W v tb (tenCell X.place k lm 0) =
        Blocks.ext D.lT (fun p => t ⟨.sc, k, lm, 0, p⟩) zh := by
  intro X tb hX
  have hn : X.nl = 3 := (ten_facts L S .sc rfl (tensorAt_T hX)).2
  exact ⟨hn, fun lm k hlm hk => termsSc_clause P h X tb hX lm k
    (by rw [P.fits.LamM]; exact hlm) (by rw [hn]; exact hk)⟩

/-- TermsDict.sel. -/
theorem termsSel_dict (P : PortFits ρ W v D c t low z zh) (L : Laid v.y) (S : Switches v.y.h)
    {sEnd : ℕ} {l : List Aff} (h : termsL v sEnd = some l) :
    ∀ X tb, v.tensorAt "sel" "rt" = some (X, tb) → X.nl = 1 ∧
      ∀ lm x k, lm < D.ne → x < D.nx → k < 1 → readAtW W v tb (tenCell X.place k lm x) =
        Blocks.ext D.lT (fun p => t ⟨.sel, k, lm, x, p⟩) zh := by
  intro X tb hX
  have hn : X.nl = 1 := (ten_facts L S .sel rfl (tensorAt_T hX)).2
  exact ⟨hn, fun lm x k hlm hx hk => termsSel_clause P h X tb hX lm x k
    (by rw [P.fits.LamM]; exact hlm) (by rw [P.fits.NE]; exact hx) (by rw [hn]; exact hk)⟩

/-- HotDict.sel, where oneHotL returns. -/
theorem hotSel_dict (F : Fits ρ W v D c t low u) (L : Laid v.y) (S : Switches v.y.h)
    {l : List Aff} (h : oneHotL v = some l) :
    ∀ X tb, v.tensorAt "sel" "zt" = some (X, tb) → X.nl = 1 ∧
      ∀ lm x, lm < D.ne → x < D.nx → readAtW W v tb (tenCell X.place 0 lm x) =
        Blocks.ext D.lT (fun p => t ⟨.sel, 0, lm, x, p⟩) u := by
  intro X tb hX
  have hn : X.nl = 1 := (ten_facts L S .sel rfl (tensorAt_T hX)).2
  refine ⟨hn, fun lm x hlm hx => ?_⟩
  unfold oneHotL at h
  rw [if_pos F.p3] at h
  obtain ⟨q, hq, _⟩ := mem_flat h (List.mem_range.mpr (by rw [F.LamM]; exact hlm))
  obtain ⟨s, hs, _⟩ := bind_some hq
  exact hotSel_clause F hs X tb hX x 0 (by rw [F.NE]; exact hx) (by rw [hn]; exact Nat.one_pos)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.ten_facts
#print axioms OnBytes.Road.K4.sqI_dict
#print axioms OnBytes.Road.K4.sqA_dict
#print axioms OnBytes.Road.K4.gS_dict
#print axioms OnBytes.Road.K4.gU_dict
#print axioms OnBytes.Road.K4.termsRow_dict
#print axioms OnBytes.Road.K4.termsSc_dict
#print axioms OnBytes.Road.K4.termsSel_dict
#print axioms OnBytes.Road.K4.hotSel_dict
