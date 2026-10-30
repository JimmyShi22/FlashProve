-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysIdnW.lean: the identities of a feed-forward segment, in a world.

Beside its keys, a feed-forward segment of the library's model has identities (Idn and idnVal in
Inst/Model/FF/Trace.lean): seventeen for each norm and position, (J1) to (J9), on the bytes of the
norm's ledger; one for each routed layer and position, (J10): the selector's entries sum to 1; and,
in the first segment, (J11), on the embedding. The library asks each at every position. The verifier
(OnBytes/Model/Layer.lean) claims, once for each norm, seventeen affine forms in hidden values: the
ledger's digits read at one drawn token point, with slots for nine sums and seven products; and one
form for each routed layer, at the lookup's token point. This file says what these forms are worth
in a world in which the tables of the reads are true: the extension of the library's identity over
the positions, at that point, plus an exact remainder in the slots.

What is compared with what: the verifier's own forms (row5At, ledCarry5, ledLines5, epsOf, twoM,
shA, normsStart, claimRowBatch) with the library's own idnVal, Wsum and prods.

What is reused. The worth of each of the seventeen lines on a row of any cells is
not shown here: it is ledCarry5_value, ledLines5_list and ledRoots_value of
Johnson/Road/HeadLedgerLin.lean; so are slack, idnP_slack, slack_zero and row5_a to
row5_Rhi. That an affine expression passes through an extension over the positions is the library's
ext_idn and ext_sa to ext_Rhi (Inst/Model/Common/LedgerForms.lean).

Main definitions: ledAt, wHat, pHat, idnAt (the bytes, the sums, the products and the identities of
a norm, extended over the positions, at a point); NormWords; rowBatchForm.
Main theorems.
 - rowCells_value: the cells of a row at a token point, from true short tables.
 - normWords_sclOf: the verifier's eps and M of each norm are the library's, under sclOf.
 - ledger_carry (T-carry), ledger_line (T-line), ledger_shown (T-shown): at any point's name;
   Fits.carry, Fits.line8, Fits.shown4: at the verifier's names P_V and r_tV.
 - Fits.idn_zero: if the seventeen forms of a norm are worth 0 and the sixteen slots hold the
   extensions of the sums and the products, the extension of each of (J1) to (J9) vanishes at P_V.
 - oneHot_value (T-hot): (J10), under the tables at the lookup's point alone.
 - rowBatch_value (T-batch), normsStart_value (T-start): two forms that are sums of slots.

The hypotheses, and what shows that they can be met.
 - Fits: concluded by fits_of_layout_true (Johnson/Road/FormsKeysAdmit.lean) from the verifier's
   lines and the tables at the lookup's point, under sclOf. TrueAt3: concluded by trueAt3_of_holds
   (Johnson/Road/FormsKeysTrue3.lean) from the same hypothesis on the reads. NormWords: concluded
   here.
 - "row5At returns", "sumForms returns": lines of the verifier.
   Johnson/Road/FormsKeysIdnWRun.lean evaluates them, and the conclusions with
   them, at a made-up shape.
 - In Fits.idn_zero: that the forms are worth 0 and that the slots hold the extensions. Each stands
   for random steps (the element that batches the claims; two sumchecks; three draws) and is shown
   by nothing here.

What is not claimed. All statements are identities in a world: no distribution of a challenge is
used, and nothing is said on soundness. From "the extension vanishes at the drawn point" to "the
identity holds at every position" lies a random step. The claims on the end values of the product
layer of the squares, the embedding's claim (J11) and the lookup's three claims on the planes are
not treated. That the verifier's check adds these forms as claims is read off its text and stated
only for claimRowBatch. The program does not import this file.
-/
import Johnson.Road.FormsKeysCaller
import Johnson.Road.FormsKeysTrue3
import Johnson.Road.HeadLedgerLin

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff LedK Row5 row5 ledCarry5 ledLines5 tenCell)
open OnBytes.Model.Layer (Env Lay Heard Ten aff0 sumForms twoM epsOf LM1 LM2 claimRowBatch
  normsStart)
open Inst.Model (Scl NormPar)
open Inst.Model.FFSeg (Dim Cell Arr Idn idnVal led bS npOf)
open Blocks (ext)

variable {K : Type} [Field K]

/-! ## What the lines of a norm are compared with -/

section Hats

variable [scl : Scl] (D : Dim) (t : Cell → K) (ν : ℕ) (u : ℕ → K)

/-- The bytes of the ledger of norm ν, each extended over the positions, at the point u. -/
def ledAt (n : ℕ) : K := ext D.lT (fun i => led t ν i n) u

/-- The convolution sum W_s of norm ν, extended over the positions, at the point u. -/
def wHat (s : ℕ) : K :=
  ext D.lT (fun i => Inst.Model.Ledger.Wsum D.d (fun l j => bS D t ν l j i) s) u

/-- Product number j of the ledger of norm ν, extended over the positions, at the point u. -/
def pHat (j : ℕ) : K := ext D.lT (fun i => Inst.Model.Ledger.prods (led t ν i) j) u

/-- The library's identity number k of norm ν, (J1) to (J9), extended over the positions, at the
point u. The identity reads neither the embedding nor the tokens. -/
def idnAt (k : ℕ) : K := ext D.lT (fun i => idnVal D t (fun _ _ => 0) (fun _ => 0) (.jn k ν i)) u

/-- It is the library's identity with letters for the products, at the extensions of the sums, the
bytes and the products: the library's own ext_idn (Inst/Model/Common/LedgerForms.lean). -/
theorem idnAt_eq (k : ℕ) :
    idnAt D t ν u k =
      Inst.Model.Ledger.idnP (npOf D ν) (wHat D t ν u) (ledAt D t ν u) (pHat D t ν u) k :=
  Inst.Model.Ledger.ext_idn D.lT (fun m i => led t ν i m) u (npOf D ν)
    (fun s i => Inst.Model.Ledger.Wsum D.d (fun l j => bS D t ν l j i) s) k

end Hats

/-! ## The cells of a row at a token point -/

section Cells

variable {ρ : Reading K} {W : World K} {v : Env} {c : Cells K} {t : Cell → K} {u : ℕ → K}
  {lT : ℕ}

/-- The cells of row ν of the tensor of rows, read from true short tables of the matrix ar at a
token point named P: cell n plus 128 is worth byte n of the library's ledger of norm ν, extended
over the positions, at that point. -/
theorem rowCells_value {P : String} {b : ℕ} {trow : Ten} (hb : v.tabAt ("ar@" ++ P) = some b)
    (hrow : v.y.T_ "row" = some trow) (hJ : trow.J = 99) (T : Tied c t .D trow.mat trow.place)
    (R : ShortTrue ρ W v b trow.mat lT c u) {ν : ℕ} {cells : Array Aff}
    (hc : v.rowCells P ν 99 = some cells) :
    ∀ n, n < 99 → (cells.getD n aff0).value ρ W + 128 = ext lT (fun i => led t ν i n) u := by
  intro n hn
  unfold Env.rowCells at hc
  obtain ⟨b', hb', hc⟩ := bind_some hc
  obtain ⟨tr', hr', hc⟩ := bind_some hc
  have e1 : b' = b := Option.some.inj (hb'.symm.trans hb)
  have e2 : tr' = trow := Option.some.inj (hr'.symm.trans hrow)
  subst e1
  subst e2
  have h1 := range_mapM_get aff0 hc hn
  have hcell : tr'.OFF + ν * 99 + n = tenCell tr'.place 0 ν n := by
    show _ = tr'.OFF + (0 * tr'.cnt + ν) * tr'.J + n
    rw [hJ, Nat.zero_mul, Nat.zero_add]
  have hk : (fun i => led t ν i n) = fun i => c tr'.mat (tenCell tr'.place 0 ν n) i + 128 := by
    funext i
    simp [Inst.Model.FFSeg.led, Inst.Model.FFSeg.val, Arr.nCell, Arr.off, T.2]
  rw [hk, Blocks.ext_add, Blocks.ext_const, R _ _ h1, hcell]

end Cells

/-! ## The public numbers of a norm -/

/-- The verifier's two public numbers of each norm of the group are the library's: the word M of the
scale file, and eps. -/
structure NormWords [scl : Scl] (v : Env) (D : Dim) : Prop where
  /-- the word M -/
  M : ∀ ν, ν < D.nNu →
    v.sc.kl (v.lay (ν / v.y.NN)) (if ν % 2 == 1 then LM2 else LM1) = (npOf D ν).M
  /-- eps -/
  eps : ∀ ν, ν < D.nNu →
    (((if ν % 2 == 1 then v.y.h.eps2 else v.y.h.eps1 : ℕ) : ℤ)) = (npOf D ν).eps

/-- They are, under the table of scales that sclOf makes of the verifier's scale file, if a layer
has two norms and the group has the library's number of layers. -/
theorem normWords_sclOf (v : Env) (D : Dim) (hNN : v.y.NN = 2) (hL : v.y.Lam = D.nl) :
    NormWords (scl := sclOf v.y.h v.sc v.g v.y.Lam) v D := by
  letI : Scl := sclOf v.y.h v.sc v.g v.y.Lam
  have md : ∀ ν, ν < D.nNu → v.g * v.y.Lam + ν / 2 % v.y.Lam = v.lay (ν / 2) := by
    intro ν hν
    have h2 : ν / 2 < v.y.Lam := by
      rw [hL]
      have : D.nNu = 2 * D.nl := rfl
      omega
    rw [Nat.mod_eq_of_lt h2]
    rfl
  constructor
  · intro ν hν
    rw [hNN, ← md ν hν]
    unfold Inst.Model.FFSeg.npOf
    rcases Nat.mod_two_eq_zero_or_one ν with e | e
    · have h1 : ¬ (ν % 2 == 1) = true := by rw [e]; decide
      rw [if_pos e, if_neg h1]
      rfl
    · have h1 : (ν % 2 == 1) = true := by rw [e]; rfl
      have h0 : ¬ ν % 2 = 0 := by omega
      rw [if_neg h0, if_pos h1]
      rfl
  · intro ν hν
    unfold Inst.Model.FFSeg.npOf
    rcases Nat.mod_two_eq_zero_or_one ν with e | e
    · have h1 : ¬ (ν % 2 == 1) = true := by rw [e]; decide
      rw [if_pos e, if_neg h1]
      rfl
    · have h1 : (ν % 2 == 1) = true := by rw [e]; rfl
      have h0 : ¬ ν % 2 = 0 := by omega
      rw [if_neg h0, if_pos h1]
      rfl

/-! ## (J1) to (J9): the seventeen lines of a norm -/

section Lines

variable {ρ : Reading K} {W : World K} [scl : Scl] {v : Env} {D : Dim} {c : Cells K}
  {t : Cell → K} {u : ℕ → K} {P : String} {b : ℕ} {trow : Ten}
  (hρ : Numerals ρ) (hb : v.tabAt ("ar@" ++ P) = some b) (hrow : v.y.T_ "row" = some trow)
  (hJ : trow.J = 99) (T : Tied c t .D trow.mat trow.place)
  (R : ShortTrue ρ W v b trow.mat D.lT c u) {ν : ℕ} {r : Row5 Aff}
  (hr : v.row5At P ν = some r)

omit scl in
include hb hrow hJ T R hr in
/-- The row that the verifier makes at the point named P is row5 of cells whose values, plus 128,
are the library's bytes at the point. -/
theorem row5At_cells : ∃ cell : ℕ → Aff, r = row5 cell ∧
    ∀ n, n < 99 → (cell n).value ρ W + 128 = ledAt D t ν u n := by
  unfold Env.row5At at hr
  obtain ⟨cells, hc, e⟩ := bind_some hr
  exact ⟨fun j => cells.getD j aff0, (Option.some.inj e).symm,
    rowCells_value hb hrow hJ T R hc⟩

include hρ hb hrow hJ T R hr

/-- (T-carry) The nine carries' lines. The verifier's line s of the carries of norm ν, on the row at
the point u and the slot j, is worth the library's identity (J1) number s of that norm, extended
over the positions, at u, plus what the slot holds more than the extension of the sum W_s. -/
theorem ledger_carry {s : ℕ} (hs : s < 9) (j : ℕ) :
    (ledCarry5 r s (Aff.slot j)).value ρ W =
      idnAt D t ν u s + (W.slot j - wHat D t ν u s) := by
  obtain ⟨cell, rfl, hD⟩ := row5At_cells hb hrow hJ T R hr
  rw [Hd.ledCarry5_value hρ hD hs (Aff.slot j) (npOf D ν) (fun _ => W.slot j) (pHat D t ν u)
      (Aff.value_slot ρ W j),
    idnAt_eq, Inst.Model.Ledger.idnP_j1 _ _ _ _ hs, Inst.Model.Ledger.idnP_j1 _ _ _ _ hs]
  ring

/-- (T-line) The eight lines. The verifier's line number k of norm ν after the carries, on the row
at the point u and the seven slots from j on, is worth the library's identity number 9 + k of that
norm, (J2) to (J9), extended over the positions, at u, plus what the identity gains (Hd.slack in
Johnson/Road/HeadLedgerLin.lean) by what the slots hold more than the extensions of the seven
products. -/
theorem ledger_line (N : NormWords v D) (hν : ν < D.nNu) (j : ℕ) {k : ℕ} (hk : k < 8) :
    ((ledLines5 r ((Array.range 7).map fun x => Aff.slot (j + x)) (epsOf v.y ν)
        (twoM v ν)).toList.getD k {}).value ρ W =
      idnAt D t ν u (9 + k) +
        Hd.slack (fun _ => 0) (fun x => W.slot (j + x) - pHat D t ν u x) (9 + k) := by
  obtain ⟨cell, rfl, hD⟩ := row5At_cells hb hrow hJ T R hr
  have heps : ρ.val (epsOf v.y ν) = ((npOf D ν).eps : K) := by
    unfold epsOf
    rw [hρ.ofNat, ← N.eps ν hν]
    norm_cast
  have htwo : (twoM v ν).value ρ W = 2 ^ ((npOf D ν).M + 1) := by
    unfold twoM
    rw [Aff.value_ofConst, hρ.pw, N.M ν hν]
  have hpv : ∀ x, x < 7 →
      (((Array.range 7).map fun x => Aff.slot (j + x)).getD x (LedK.c zeroE)).value ρ W =
        W.slot (j + x) := by
    intro x hx
    rw [range_map_getD' 7 _ _ hx, Aff.value_slot]
  rw [Hd.ledLines5_list _ _ (by simp) _ _,
    Hd.ledRoots_value hρ hD _ _ _ (npOf D ν) (wHat D t ν u) (fun x => W.slot (j + x)) heps htwo hpv
      hk,
    Hd.idnP_slack (npOf D ν) (wHat D t ν u) (wHat D t ν u) (ledAt D t ν u)
      (fun x => W.slot (j + x)) (pHat D t ν u) (9 + k), idnAt_eq]
  simp only [sub_self]

omit scl in
/-- (T-shown) The four numbers of the row whose values the token sumcheck of the row products shows:
each form is worth the extension over the positions of the library's number, at the point u. -/
theorem ledger_shown :
    r.a.value ρ W = ext D.lT (fun i => Inst.Model.Ledger.sa (led t ν i)) u ∧
      r.b.value ρ W = ext D.lT (fun i => Inst.Model.Ledger.sb (led t ν i)) u ∧
      r.Rlo.value ρ W = ext D.lT (fun i => Inst.Model.Ledger.Rlo (led t ν i)) u ∧
      r.Rhi.value ρ W = ext D.lT (fun i => Inst.Model.Ledger.Rhi (led t ν i)) u := by
  obtain ⟨cell, rfl, hD⟩ := row5At_cells hb hrow hJ T R hr
  exact ⟨(Hd.row5_a hρ hD).trans
      (Inst.Model.Ledger.ext_sa D.lT (fun m i => led t ν i m) u).symm,
    (Hd.row5_b hρ hD).trans (Inst.Model.Ledger.ext_sb D.lT (fun m i => led t ν i m) u).symm,
    (Hd.row5_Rlo hρ hD).trans (Inst.Model.Ledger.ext_Rlo D.lT (fun m i => led t ν i m) u).symm,
    (Hd.row5_Rhi hρ hD).trans (Inst.Model.Ledger.ext_Rhi D.lT (fun m i => led t ν i m) u).symm⟩

end Lines

/-! ## (J10): the selectors' entries of a layer sum to 1 -/

section Hot

variable {ρ : Reading K} {W : World K} [scl : Scl] {v : Env} {D : Dim} {c : Cells K}
  {t : Cell → K} {low u : ℕ → K}

/-- (T-hot) The form of the verifier's claim that the selector's entries of the routed layer lm sum
to 1 (claimsOneHot in OnBytes/Model/Layer.lean) is worth the extension over the positions, at the
lookup's token point, of the library's identity (J10) of that layer. Under the record Fits, which
holds the tables at the lookup's point. -/
theorem oneHot_value (F : Fits ρ W v D c t low u) (lm : ℕ) {s : Aff}
    (hs : sumForms v.y.h.NE (fun e => (v.shA "sel" "zt" lm e).map fun a => (a, oneE)) = some s)
    (emb : ℕ → ℕ → K) (tok : ℕ → ℕ) :
    (Aff.ofConst (negE oneE) + s).value ρ W =
      ext D.lT (fun i => idnVal D t emb tok (.j10 lm i)) u := by
  have h1 : s.value ρ W = ∑ e ∈ range v.y.h.NE, ext D.lT (raw t .sel lm e) u := by
    refine sumForms_value ρ W _ _ _ ?_ hs
    intro x b k hx
    obtain ⟨a, ha, e⟩ := map_some hx
    cases e
    rw [ρ.one, one_mul]
    exact F.shA .sel rfl ha
  have h2 : (fun i => idnVal D t emb tok (.j10 lm i)) =
      fun i => (∑ e ∈ range D.nx, raw t .sel lm e i) - 1 := by
    funext i
    show ∑ e ∈ range D.nx, Inst.Model.FFSeg.val t .sel lm e i - 1 = _
    congr 1
    refine sum_congr rfl fun e _ => ?_
    unfold raw
    simp [Arr.off]
  rw [Aff.value_add, Aff.value_ofConst, F.num.neg, ρ.one, h1, h2, Blocks.ext_sub, Blocks.ext_sum,
    Blocks.ext_const, F.NE]
  ring

end Hot

/-! ## At the verifier's own names: the norms' token point and the end point of the row products -/

section AtNames

variable {ρ : Reading K} {W : World K} [scl : Scl] {v : Env} {D : Dim} {c : Cells K}
  {t : Cell → K} {low u lowV uV uP uR lowE uE : ℕ → K}

omit scl in
/-- If the verifier makes a row at the point named P, it has found the tables of ar at that
point. -/
theorem row5At_found {P : String} {ν : ℕ} {r : Row5 Aff} (hr : v.row5At P ν = some r) :
    ∃ b, v.tabAt ("ar@" ++ P) = some b := by
  unfold Env.row5At at hr
  obtain ⟨cells, hc, -⟩ := bind_some hr
  unfold Env.rowCells at hc
  obtain ⟨b, hb, -⟩ := bind_some hc
  exact ⟨b, hb⟩

variable (F : Fits ρ W v D c t low u) (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE)
include F T3

/-- (T-carry) at the verifier's names: the row at the norms' token point P_V. -/
theorem Fits.carry {ν : ℕ} {r : Row5 Aff} (hr : v.row5At "P_V" ν = some r) {s : ℕ} (hs : s < 9)
    (j : ℕ) :
    (ledCarry5 r s (Aff.slot j)).value ρ W =
      idnAt D t ν uP s + (W.slot j - wHat D t ν uP s) := by
  obtain ⟨trow, _, _, hrow, hm, T, hJ, _⟩ := F.rowTab
  obtain ⟨b, hb⟩ := row5At_found hr
  exact ledger_carry F.num hb hrow hJ T (by rw [hm]; exact T3.arP b hb) hr hs j

/-- (T-line) at the verifier's names. -/
theorem Fits.line8 (N : NormWords v D) {ν : ℕ} (hν : ν < D.nNu) {r : Row5 Aff}
    (hr : v.row5At "P_V" ν = some r) (j : ℕ) {k : ℕ} (hk : k < 8) :
    ((ledLines5 r ((Array.range 7).map fun x => Aff.slot (j + x)) (epsOf v.y ν)
        (twoM v ν)).toList.getD k {}).value ρ W =
      idnAt D t ν uP (9 + k) +
        Hd.slack (fun _ => 0) (fun x => W.slot (j + x) - pHat D t ν uP x) (9 + k) := by
  obtain ⟨trow, _, _, hrow, hm, T, hJ, _⟩ := F.rowTab
  obtain ⟨b, hb⟩ := row5At_found hr
  exact ledger_line F.num hb hrow hJ T (by rw [hm]; exact T3.arP b hb) hr N hν j hk

/-- (T-shown) at the verifier's names: the row at the end point r_tV of the token sumcheck of the
row products. -/
theorem Fits.shown4 {ν : ℕ} {r : Row5 Aff} (hr : v.row5At "r_tV" ν = some r) :
    r.a.value ρ W = ext D.lT (fun i => Inst.Model.Ledger.sa (led t ν i)) uR ∧
      r.b.value ρ W = ext D.lT (fun i => Inst.Model.Ledger.sb (led t ν i)) uR ∧
      r.Rlo.value ρ W = ext D.lT (fun i => Inst.Model.Ledger.Rlo (led t ν i)) uR ∧
      r.Rhi.value ρ W = ext D.lT (fun i => Inst.Model.Ledger.Rhi (led t ν i)) uR := by
  obtain ⟨trow, _, _, hrow, hm, T, hJ, _⟩ := F.rowTab
  obtain ⟨b, hb⟩ := row5At_found hr
  exact ledger_shown F.num hb hrow hJ T (by rw [hm]; exact T3.arR b hb) hr

/-- What the seventeen claims of a norm give. If the nine slots from jW on hold the extensions of
the nine sums, the seven slots from jP on those of the seven products, and the verifier's seventeen
forms of norm ν are worth 0, then each of the library's identities (J1) to (J9) of that norm,
extended over the positions, vanishes at the norms' token point. -/
theorem Fits.idn_zero (N : NormWords v D) {ν : ℕ} (hν : ν < D.nNu) {r : Row5 Aff}
    (hr : v.row5At "P_V" ν = some r) (jW jP : ℕ)
    (hW : ∀ s, s < 9 → W.slot (jW + s) = wHat D t ν uP s)
    (hP : ∀ x, x < 7 → W.slot (jP + x) = pHat D t ν uP x)
    (c9 : ∀ s, s < 9 → (ledCarry5 r s (Aff.slot (jW + s))).value ρ W = 0)
    (c8 : ∀ k, k < 8 →
      ((ledLines5 r ((Array.range 7).map fun x => Aff.slot (jP + x)) (epsOf v.y ν)
        (twoM v ν)).toList.getD k {}).value ρ W = 0) :
    ∀ k, k < 17 → idnAt D t ν uP k = 0 := by
  intro k hk
  by_cases h9 : k < 9
  · have e := F.carry T3 hr h9 (jW + k)
    rw [c9 k h9, hW k h9, sub_self, add_zero] at e
    exact e.symm
  · obtain ⟨m, rfl⟩ : ∃ m, k = 9 + m := ⟨k - 9, by omega⟩
    have e := F.line8 T3 N hν hr jP (k := m) (by omega)
    rw [c8 m (by omega), Hd.slack_zero (fun _ _ => rfl)
      (fun x hx => by rw [hP x hx, sub_self])] at e
    rw [add_zero] at e
    exact e.symm

end AtNames

/-! ## The two forms that are sums of slots -/

section Slots

variable (ρ : Reading K) (W : World K)

/-- A fold in which each step adds g i to the form's worth adds the sum. -/
theorem foldAdds_value (Fn : Aff → ℕ → Aff) (g : ℕ → K)
    (hF : ∀ a i, (Fn a i).value ρ W = a.value ρ W + g i) : ∀ (l : List ℕ) (a : Aff),
    (l.foldl Fn a).value ρ W = a.value ρ W + (l.map g).sum
  | [], a => by simp
  | i :: l, a => by
    rw [List.foldl_cons, foldAdds_value Fn g hF l, hF, List.map_cons, List.sum_cons, add_assoc]

/-- The form of the verifier's claim that the token sumcheck of the row products starts from their
batch. -/
def rowBatchForm (y : Lay) (H : Heard) : Aff :=
  (List.range (Model.ledNP y.h.xl * y.NI)).foldl
    (fun (a : Aff) i => a.addMul (Aff.slot (H.sPv + i)) (negE (H.omV.getD i zeroE)))
    (Aff.slot H.tV.sCl)

/-- It is the verifier's. -/
theorem claimRowBatch_eq (y : Lay) (H : Heard) :
    claimRowBatch y H = Model.SubM.lin (rowBatchForm y H) := rfl

/-- (T-batch) It is worth the hidden sum that the token sumcheck claims, less the row products'
slots under the powers omV. -/
theorem rowBatch_value (hρ : Numerals ρ) (y : Lay) (H : Heard) :
    (rowBatchForm y H).value ρ W = W.slot H.tV.sCl -
      ∑ i ∈ range (Model.ledNP y.h.xl * y.NI),
        ρ.val (H.omV.getD i zeroE) * W.slot (H.sPv + i) := by
  unfold rowBatchForm
  rw [foldAdds_value ρ W _ (fun i => -(ρ.val (H.omV.getD i zeroE) * W.slot (H.sPv + i)))
      (fun a i => by rw [Aff.value_addMul, Aff.value_slot, hρ.neg]; ring),
    Aff.value_slot, list_range_sumM, Finset.sum_neg_distrib]
  ring

/-- (T-start) The start form of the product layer of the squares is worth the scale (1/2)^lPd, as
the verifier computes it, times the sum over the norms, under the equality weights of rhoI, of the
sums' slots under the powers gp. -/
theorem normsStart_value (y : Lay) (sW : ℕ) (gp rhoI PV : Array E) :
    (normsStart y sW gp rhoI PV).1.value ρ W =
      ∑ i ∈ range y.NI, ∑ s ∈ range (Model.ledNS y.h.xl),
        ρ.val (powE (invE (Model.ofNat 2)) y.lPd) * ρ.val ((Model.eqTab rhoI).getD i zeroE) *
          ρ.val (gp.getD s zeroE) * W.slot (sW + Model.ledNS y.h.xl * i + s) := by
  show ((List.range y.NI).foldl (fun C i =>
    (List.range (Model.ledNS y.h.xl)).foldl (fun (C : Aff) s =>
      C.addMul (Aff.slot (sW + Model.ledNS y.h.xl * i + s))
        (mulE (mulE (powE (invE (Model.ofNat 2)) y.lPd) ((Model.eqTab rhoI).getD i zeroE))
          (gp.getD s zeroE))) C) aff0).value ρ W = _
  rw [foldAdds_value ρ W _ (fun i => ∑ s ∈ range (Model.ledNS y.h.xl),
      ρ.val (powE (invE (Model.ofNat 2)) y.lPd) * ρ.val ((Model.eqTab rhoI).getD i zeroE) *
        ρ.val (gp.getD s zeroE) * W.slot (sW + Model.ledNS y.h.xl * i + s))
      (fun a i => by
        rw [foldAdds_value ρ W _ (fun s =>
          ρ.val (powE (invE (Model.ofNat 2)) y.lPd) * ρ.val ((Model.eqTab rhoI).getD i zeroE) *
            ρ.val (gp.getD s zeroE) * W.slot (sW + Model.ledNS y.h.xl * i + s))
          (fun a s => by rw [Aff.value_addMul, Aff.value_slot, ρ.mul, ρ.mul]), list_range_sumM]),
    aff0_value, zero_add, list_range_sumM]

end Slots

#print axioms idnAt_eq
#print axioms rowCells_value
#print axioms normWords_sclOf
#print axioms ledger_carry
#print axioms ledger_line
#print axioms ledger_shown
#print axioms oneHot_value
#print axioms Fits.carry
#print axioms Fits.line8
#print axioms Fits.shown4
#print axioms Fits.idn_zero
#print axioms rowBatch_value
#print axioms normsStart_value

end OnBytes.Road
