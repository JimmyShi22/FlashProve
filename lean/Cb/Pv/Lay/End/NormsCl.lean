-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/NormsCl.lean: the verifier's claims on the norms of a group of layers, as forms on
committed entries, and what they say on cells.

The check of a layers' sub-proof ends in linear claims. This file writes those that belong to the
norms as forms (Blocks/Form.lean) on entries of two kinds: entries of the mask row, which hide what
was shown, and entries of the tables of reads, which are sent late. The forms are
functions of what the verifier has heard and drawn (the record NormsE) and of names for the entries
(the record NormsNames). No state of a program occurs.

Definitions.
 - NormsE: the letters that the claims read: four points (pV: the norms' token point; r1: the
   challenges of the product layer of the squares; r2: those of the token sumcheck of the row
   products; zt: the tail of the lookup's point), the elements γ and ω whose powers batch, the
   factors β1 and β2 of the masks of the end values, and what was shown.
 - NormsNames J: the entries' names in a type J.
 - hW, hP, hCl, hL, hR, h2: the hidden values as forms: what was shown less the factor times the
   mask entry.
 - cSame, cEnd, cBatch, cShown, cIdn, cHot: the claims. clNorms, clLedger, clHot: three lists of
   them, each in the order in which one routine of the programs is meant to add its claims; the two
   claims that the sumchecks themselves leave are letters u1, u2 at their places. normsCl: the
   lists one after the other.
 - TablesTrue: what the entries of the tables of reads are meant to be, on cells t.
 - NormsLast: what the claims say on cells.

Main theorem: norms_last: on entries y with true tables, if every form of normsCl is worth 0, then
NormsLast. hot_last: its last clause from the claims on the selectors' entries alone. at_point: with
NormsLast, if the hidden values under the slots of the sums W_s and of the row products are the
honest values Wt and pvt, the extension of each defect dJ vanishes at pV.
NormsLast.rowB, NormsLast.rowLed: the lines as rows on the hidden sums and as one claim on the
vector of a norm's hidden products.

Limits. TablesTrue is a premise here; Cb/Pv/Lay/End/NormsA.lean shows it of late entries that are at
the values of their forms. The two claims that the sumchecks themselves leave (rows on the hiding
coefficients) are letters. That the lists are a program's, in content or in order, is not said
here. Five limbs; sizes are letters with hypotheses. Identities alone: nothing on a distribution of
a challenge and nothing on soundness.


-/
import Inst.Model.Common.LedgerForms
import Cb.Pv.Lay.End.Vec

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Finset
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell led bS val npOf Pv Wt pvt dJ d10 lDd)
open Inst.Model.Ledger (idnForm idnP saF sbF RloF RhiF)
open Blocks (ext eqN Form)

/-- What the claims on the norms read of what the verifier has heard and drawn. -/
structure NormsE (E : Type) where
  pV : ℕ → E
  r1 : ℕ → E
  r2 : ℕ → E
  zt : ℕ → E
  γ : E
  ω : E
  β1 : E
  β2 : E
  /-- shown for the sums W_s, for the row products, for the sum of the token sumcheck -/
  shW : ℕ → E
  shP : ℕ → E
  shCl : E
  /-- shown for the two end values of the product layer and for those of the token sumcheck -/
  shL : E
  shR : E
  sh2 : ℕ → E

/-- The names of the entries that the claims on the norms read. -/
structure NormsNames (J : Type) where
  /-- the mask entries -/
  mW : ℕ → J
  mP : ℕ → J
  mCl : J
  mL : J
  mR : J
  m2 : ℕ → J
  /-- the reads: limb l of block kh of the stream at place ν; cell n of the ledger of norm ν at the
  two token points; the selector's entry e of routed layer l -/
  uXi : ℕ → ℕ → ℕ → J
  uP : ℕ → ℕ → J
  uR : ℕ → ℕ → J
  uSel : ℕ → ℕ → J

section Forms

variable {E J : Type} [Field E] [DecidableEq J] (N : NormsNames J) (e : NormsE E)

/-- The hidden value under the slot of sum number x. -/
def hW (x : ℕ) : Form J E := Form.masked (e.shW x) (N.mW x)
/-- The hidden value under the slot of product number x. -/
def hP (x : ℕ) : Form J E := Form.masked (e.shP x) (N.mP x)
/-- The hidden sum from which the token sumcheck starts. -/
def hCl : Form J E := Form.masked e.shCl N.mCl
/-- The two hidden end values of the product layer. -/
def hL : Form J E := Form.const e.shL - e.β1 • Form.ent N.mL
def hR : Form J E := Form.const e.shR - e.β1 • Form.ent N.mR
/-- Hidden end value number x of the token sumcheck. -/
def h2 (x : ℕ) : Form J E := Form.const (e.sh2 x) - e.β2 • Form.ent (N.m2 x)

/-- Byte n of the ledger of norm ν at a token point, from the cell's read. -/
def byteF (u : ℕ → ℕ → J) (ν n : ℕ) : Form J E := Form.ent (u ν n) + Form.const 128

/-- The two end values of the product layer are one. -/
def cSame : Form J E := hL N e - hR N e

/-- The end value of the product layer against the reads of the stream's limbs. lNI, b: the bits of
a norm's number and of a block's; B: the blocks in use; n: the norms. -/
def cEnd (lNI b B n : ℕ) : Form J E :=
  hL N e - ∑ i ∈ range (n * B * 5),
    (eqN (lNI + b) 0 e.r1 (i / 5 / B * 2 ^ b + i / 5 % B) * e.γ ^ (i % 5)) •
      Form.ent (N.uXi (i / 5 / B) (i % 5) (i / 5 % B))

/-- The hidden sum of the token sumcheck is the batch of the hidden products. -/
def cBatch (n : ℕ) : Form J E := hCl N e - ∑ x ∈ range (7 * n), e.ω ^ x • hP N e x

/-- The four numbers of a ledger that the token sumcheck shows, by their number, as forms. -/
def rowsMapF (k : ℕ) (DF : ℕ → Form J E) : Form J E :=
  match k with
  | 0 => saF DF
  | 1 => sbF DF
  | 2 => RloF DF
  | _ => RhiF DF

/-- End value number x of the token sumcheck against the reads of the ledger at its end point. -/
def cShown (x : ℕ) : Form J E := h2 N e x - rowsMapF (x % 4) (byteF N.uR (x / 4))

/-- Identity number k of norm ν with the hidden sums and products in the places of W_s and of the
products, on the reads of the ledger at the norms' token point. -/
def cIdn [Scl] (D : Dim) (ν k : ℕ) : Form J E :=
  idnForm (byteF N.uP ν) (npOf D ν) (fun s => hW N e (9 * ν + s)) (fun j => hP N e (7 * ν + j)) k

/-- The selector's entries of routed layer l sum to 1. -/
def cHot (nx l : ℕ) : Form J E := ∑ x ∈ range nx, Form.ent (N.uSel l x) - Form.const 1

/-- The three claims behind the product layer of the squares. u1: the claim that the layer itself
leaves. -/
def clNorms (u1 : Form J E) (lNI b B n : ℕ) : List (Form J E) :=
  [u1, cSame N e, cEnd N e lNI b B n]

/-- The claims behind the token sumcheck of the row products: the claim u2 that the sumcheck itself
leaves; its end values, norm by norm; the identities (J1), norm by norm; the identities (J2) to
(J9), norm by norm. -/
def clLedger [Scl] (u2 : Form J E) (D : Dim) : List (Form J E) :=
  u2 :: ((List.range (4 * D.nNu)).map (cShown N e) ++
    ((List.range (9 * D.nNu)).map (fun x => cIdn N e D (x / 9) (x % 9)) ++
      (List.range (8 * D.nNu)).map fun x => cIdn N e D (x / 8) (9 + x % 8)))

/-- The claims on the selectors' entries. -/
def clHot (D : Dim) : List (Form J E) := (List.range D.ne).map (cHot N D.nx)

/-- The claims on the norms, one list after the other. -/
def normsCl [Scl] (u1 u2 : Form J E) (D : Dim) (lNI b B : ℕ) : List (Form J E) :=
  clNorms N e u1 lNI b B D.nNu ++ cBatch N e D.nNu :: (clLedger N e u2 D ++ clHot (E := E) N D)

end Forms

section Means

variable {E J : Type} [Field E] [Fintype J] [DecidableEq J] (N : NormsNames J) (e : NormsE E)

/-- What the entries of the tables of reads are meant to be, on the cells t. s: the bits of a
feature in its block; B: the blocks in use. Only the entries that the claims read are spoken of. -/
structure TablesTrue (D : Dim) (t : Cell → E) (lNI b s B : ℕ) (y : J → E) : Prop where
  xi : ∀ ν l kh, ν < D.nNu → l < 5 → kh < B →
    y (N.uXi ν l kh) = ∑ r ∈ range (2 ^ s), eqN s (lNI + b) e.r1 r *
      ext D.lT (fun p => bS D t ν l (kh * 2 ^ s + r) p) (fun j => e.r1 (lNI + (b + s) + j))
  atP : ∀ ν n, ν < D.nNu → n < 99 → y (N.uP ν n) + 128 = ext D.lT (fun i => led t ν i n) e.pV
  atR : ∀ ν n, ν < D.nNu → n < 99 → y (N.uR ν n) + 128 = ext D.lT (fun i => led t ν i n) e.r2
  sel : ∀ l x, l < D.ne → x < D.nx → y (N.uSel l x) = ext D.lT (fun i => val t .sel l x i) e.zt

/-- What the claims on the norms say on cells. The hidden values under the slots of the sums W_s and
of the row products stand as what was shown less the mask entry. -/
structure NormsLast [Scl] (D : Dim) (t : Cell → E) (lNI b s : ℕ) (y : J → E) : Prop where
  endL : e.shL - e.β1 * y N.mL = ext (lNI + ((b + s) + D.lT)) (Pv D t e.γ) e.r1
  endR : e.shR - e.β1 * y N.mR = e.shL - e.β1 * y N.mL
  batch : e.shCl - y N.mCl = ∑ x ∈ range (7 * D.nNu), e.ω ^ x * (e.shP x - y (N.mP x))
  shown : ∀ x, x < 4 * D.nNu → e.sh2 x - e.β2 * y (N.m2 x) =
    ext D.lT (fun i => (match x % 4 with
      | 0 => Inst.Model.Ledger.sa
      | 1 => Inst.Model.Ledger.sb
      | 2 => Inst.Model.Ledger.Rlo
      | _ => Inst.Model.Ledger.Rhi) (led t (x / 4) i)) e.r2
  lines : ∀ ν, ν < D.nNu → ∀ k, k < 17 →
    idnP (npOf D ν) (fun s => e.shW (9 * ν + s) - y (N.mW (9 * ν + s)))
      (fun n => ext D.lT (fun i => led t ν i n) e.pV)
      (fun j => e.shP (7 * ν + j) - y (N.mP (7 * ν + j))) k = 0
  hot : ∀ l, l < D.ne → ext D.lT (d10 D t l) e.zt = 0

theorem val_hW (y : J → E) (x : ℕ) : Form.val y (hW N e x) = e.shW x - y (N.mW x) :=
  Form.val_masked y _ _

theorem val_hP (y : J → E) (x : ℕ) : Form.val y (hP N e x) = e.shP x - y (N.mP x) :=
  Form.val_masked y _ _

theorem val_hL (y : J → E) : Form.val y (hL N e) = e.shL - e.β1 * y N.mL := by
  unfold hL
  rw [map_sub, map_smul, Form.val_const, Form.val_ent, smul_eq_mul]

theorem val_hR (y : J → E) : Form.val y (hR N e) = e.shR - e.β1 * y N.mR := by
  unfold hR
  rw [map_sub, map_smul, Form.val_const, Form.val_ent, smul_eq_mul]

theorem val_h2 (y : J → E) (x : ℕ) : Form.val y (h2 N e x) = e.sh2 x - e.β2 * y (N.m2 x) := by
  unfold h2
  rw [map_sub, map_smul, Form.val_const, Form.val_ent, smul_eq_mul]

theorem val_byteF (y : J → E) (u : ℕ → ℕ → J) (ν n : ℕ) :
    Form.val y (byteF (E := E) u ν n) = y (u ν n) + 128 := by
  unfold byteF
  rw [map_add, Form.val_ent, Form.val_const]

omit [Fintype J] [DecidableEq J] in
/-- A number written in n bytes from byte a on reads these bytes alone. -/
theorem b256_congr {Dg Dg' : ℕ → E} (h : ∀ n, n < 99 → Dg n = Dg' n) (a n : ℕ) (ha : a + n ≤ 99) :
    Inst.Model.Ledger.b256 Dg a n = Inst.Model.Ledger.b256 Dg' a n := by
  unfold Inst.Model.Ledger.b256
  exact sum_congr rfl fun l hl => by rw [h (a + l) (by have := mem_range.mp hl; omega)]

omit [Fintype J] [DecidableEq J] in
/-- The four numbers that the token sumcheck shows read the first 99 bytes alone. -/
theorem rows_congr {Dg Dg' : ℕ → E} (h : ∀ n, n < 99 → Dg n = Dg' n) :
    Inst.Model.Ledger.sa Dg = Inst.Model.Ledger.sa Dg' ∧
      Inst.Model.Ledger.sb Dg = Inst.Model.Ledger.sb Dg' ∧
      Inst.Model.Ledger.Rlo Dg = Inst.Model.Ledger.Rlo Dg' ∧
      Inst.Model.Ledger.Rhi Dg = Inst.Model.Ledger.Rhi Dg' := by
  refine ⟨?_, ?_, b256_congr h 80 3 (by norm_num), b256_congr h 83 3 (by norm_num)⟩
  · unfold Inst.Model.Ledger.sa
    rw [h 58 (by norm_num), h 59 (by norm_num), h 60 (by norm_num), h 61 (by norm_num)]
  · unfold Inst.Model.Ledger.sb
    rw [h 62 (by norm_num), h 63 (by norm_num)]

omit [Fintype J] [DecidableEq J] in
/-- A carry up to number 9 reads the first 99 bytes alone. -/
theorem cs_congr {Dg Dg' : ℕ → E} (h : ∀ n, n < 99 → Dg n = Dg' n) (x : ℕ) (hx : x ≤ 9) :
    Inst.Model.Ledger.cs Dg x = Inst.Model.Ledger.cs Dg' x := by
  unfold Inst.Model.Ledger.cs
  by_cases h0 : x = 0
  · rw [if_pos h0, if_pos h0]
  · by_cases h9 : x = 9
    · rw [if_neg h0, if_neg h0, if_pos h9, if_pos h9, h 9 (by norm_num)]
    · rw [if_neg h0, if_neg h0, if_neg h9, if_neg h9,
        b256_congr h (10 + 6 * (x - 1)) 6 (by omega)]

omit [Fintype J] [DecidableEq J] in
/-- An identity reads the first 99 bytes alone. -/
theorem idnP_congr_D (np : Inst.Model.NormPar) (Ws pv : ℕ → E) {Dg Dg' : ℕ → E}
    (h : ∀ n, n < 99 → Dg' n = Dg n) (k : ℕ) : idnP np Ws Dg pv k = idnP np Ws Dg' pv k := by
  have h' : ∀ n, n < 99 → Dg n = Dg' n := fun n hn => (h n hn).symm
  by_cases hk : k < 9
  · rw [Inst.Model.Ledger.idnP_j1 np _ _ _ hk, Inst.Model.Ledger.idnP_j1 np _ _ _ hk,
      cs_congr h' k (by omega), cs_congr h' (k + 1) (by omega), h' k (by omega)]
  · have e1 : Inst.Model.Ledger.Vlo Dg = Inst.Model.Ledger.Vlo Dg' :=
      b256_congr h' 0 6 (by norm_num)
    have e2 : Inst.Model.Ledger.Vhi Dg = Inst.Model.Ledger.Vhi Dg' :=
      b256_congr h' 6 4 (by norm_num)
    have e3 : Inst.Model.Ledger.l1 Dg = Inst.Model.Ledger.l1 Dg' :=
      b256_congr h' 64 5 (by norm_num)
    have e4 : Inst.Model.Ledger.h1 Dg = Inst.Model.Ledger.h1 Dg' :=
      b256_congr h' 69 5 (by norm_num)
    have e5 : Inst.Model.Ledger.Blo Dg = Inst.Model.Ledger.Blo Dg' :=
      b256_congr h' 74 3 (by norm_num)
    have e6 : Inst.Model.Ledger.Bhi Dg = Inst.Model.Ledger.Bhi Dg' :=
      b256_congr h' 77 2 (by norm_num)
    have e7 : Inst.Model.Ledger.q1 Dg = Inst.Model.Ledger.q1 Dg' :=
      b256_congr h' 86 3 (by norm_num)
    have e8 : Inst.Model.Ledger.rr Dg = Inst.Model.Ledger.rr Dg' :=
      b256_congr h' 89 5 (by norm_num)
    have e9 : Inst.Model.Ledger.rq Dg = Inst.Model.Ledger.rq Dg' :=
      b256_congr h' 94 5 (by norm_num)
    have e10 : Inst.Model.Ledger.kc Dg = Inst.Model.Ledger.kc Dg' := by
      unfold Inst.Model.Ledger.kc
      rw [h' 79 (by norm_num)]
    have e11 : Inst.Model.Ledger.s0 Dg = Inst.Model.Ledger.s0 Dg' := h' 59 (by norm_num)
    have e12 : Inst.Model.Ledger.sig Dg = Inst.Model.Ledger.sig Dg' := by
      unfold Inst.Model.Ledger.sig
      rw [(rows_congr h').1, (rows_congr h').2.1]
    unfold Inst.Model.Ledger.idnP
    rw [if_neg hk, if_neg hk, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12]

/-- The claims on the selectors' entries alone: on entries at which the selectors' reads are true,
the extension of each defect d10 vanishes at zt. -/
theorem hot_last (D : Dim) (t : Cell → E) (y : J → E)
    (hsel : ∀ l x, l < D.ne → x < D.nx →
      y (N.uSel l x) = ext D.lT (fun i => val t .sel l x i) e.zt)
    (h : ∀ f ∈ clHot (E := E) N D, Form.val y f = 0) :
    ∀ l, l < D.ne → ext D.lT (d10 D t l) e.zt = 0 := by
  intro l hl'
  have k6 : Form.val y (cHot (E := E) N D.nx l) = 0 :=
    h _ (List.mem_map.2 ⟨l, List.mem_range.2 hl', rfl⟩)
  unfold cHot at k6
  rw [map_sub, map_sum, Form.val_const] at k6
  unfold Inst.Model.FFSeg.d10
  rw [Blocks.ext_sub, Blocks.ext_sum, Blocks.ext_const]
  rw [← k6]
  congr 1
  exact sum_congr rfl fun x hx => by rw [Form.val_ent, hsel _ _ hl' (mem_range.mp hx)]

/-- On entries with true tables, the claims say NormsLast. -/
theorem norms_last [Scl] (u1 u2 : Form J E) (D : Dim) (t : Cell → E) (lNI b s B : ℕ) (y : J → E)
    (hn : D.nNu = 2 ^ lNI) (hl : lDd D = b + s) (hd : D.d = B * 2 ^ s) (hB : B ≤ 2 ^ b)
    (T : TablesTrue N e D t lNI b s B y)
    (h : ∀ f ∈ normsCl N e u1 u2 D lNI b B, Form.val y f = 0) : NormsLast N e D t lNI b s y := by
  have m1 : Form.val y (cSame N e) = 0 := h _ (by simp [normsCl, clNorms])
  have m2 : Form.val y (cEnd N e lNI b B D.nNu) = 0 := h _ (by simp [normsCl, clNorms])
  have m3 : Form.val y (cBatch N e D.nNu) = 0 := h _ (by simp [normsCl])
  have hLed : ∀ f ∈ clLedger N e u2 D, Form.val y f = 0 := fun f hf =>
    h f (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_left _ hf)))
  have m4 : ∀ x, x < 4 * D.nNu → Form.val y (cShown N e x) = 0 := fun x hx =>
    hLed _ (List.mem_cons_of_mem _ (List.mem_append_left _
      (List.mem_map.2 ⟨x, List.mem_range.2 hx, rfl⟩)))
  have m5 : ∀ x, x < 9 * D.nNu → Form.val y (cIdn N e D (x / 9) (x % 9)) = 0 := fun x hx =>
    hLed _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_left _
      (List.mem_map.2 ⟨x, List.mem_range.2 hx, rfl⟩))))
  have m5' : ∀ x, x < 8 * D.nNu → Form.val y (cIdn N e D (x / 8) (9 + x % 8)) = 0 := fun x hx =>
    hLed _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_map.2 ⟨x, List.mem_range.2 hx, rfl⟩))))
  have eL : e.shL - e.β1 * y N.mL = ext (lNI + ((b + s) + D.lT)) (Pv D t e.γ) e.r1 := by
    unfold cEnd at m2
    rw [map_sub, val_hL, map_sum] at m2
    rw [sub_eq_zero.mp m2, ext_Pv_point D t e.γ e.r1 lNI b s B hl hd hB, hn]
    refine sum_congr rfl fun i hi => ?_
    have h5 : i / 5 < 2 ^ lNI * B :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact mem_range.mp hi)
    have hν : i / 5 / B < D.nNu := by
      rw [hn]
      exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h5)
    have hB0 : 0 < B := by
      rcases Nat.eq_zero_or_pos B with h0 | h0
      · rw [h0, Nat.mul_zero] at h5
        exact absurd h5 (Nat.not_lt_zero _)
      · exact h0
    rw [map_smul, Form.val_ent, smul_eq_mul,
      T.xi _ _ _ hν (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ hB0)]
  refine ⟨eL, ?_, ?_, fun x hx => ?_, fun ν hν k hk => ?_, fun l hl' => ?_⟩
  · unfold cSame at m1
    rw [map_sub, val_hL, val_hR] at m1
    exact (sub_eq_zero.mp m1).symm
  · unfold cBatch hCl at m3
    rw [map_sub, Form.val_masked, map_sum] at m3
    rw [sub_eq_zero.mp m3]
    exact sum_congr rfl fun x _ => by rw [map_smul, val_hP, smul_eq_mul]
  · have k4 := m4 x hx
    unfold cShown at k4
    rw [map_sub, val_h2] at k4
    rw [sub_eq_zero.mp k4]
    have hb : ∀ n, n < 99 → Form.val y (byteF (E := E) N.uR (x / 4) n) =
        ext D.lT (fun i => led t (x / 4) i n) e.r2 := fun n hn' => by
      rw [val_byteF, T.atR _ _ (Nat.div_lt_of_lt_mul hx) hn']
    rcases (by omega : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3) with q | q | q | q
    · rw [q]
      show Form.val y (saF _) = ext D.lT (fun i => Inst.Model.Ledger.sa (led t (x / 4) i)) e.r2
      rw [Inst.Model.Ledger.val_saF, (rows_congr hb).1]
      exact (Inst.Model.Ledger.ext_sa D.lT (fun m i => led t (x / 4) i m) e.r2).symm
    · rw [q]
      show Form.val y (sbF _) = ext D.lT (fun i => Inst.Model.Ledger.sb (led t (x / 4) i)) e.r2
      rw [Inst.Model.Ledger.val_sbF, (rows_congr hb).2.1]
      exact (Inst.Model.Ledger.ext_sb D.lT (fun m i => led t (x / 4) i m) e.r2).symm
    · rw [q]
      show Form.val y (RloF _) = ext D.lT (fun i => Inst.Model.Ledger.Rlo (led t (x / 4) i)) e.r2
      rw [Inst.Model.Ledger.val_RloF, (rows_congr hb).2.2.1]
      exact (Inst.Model.Ledger.ext_Rlo D.lT (fun m i => led t (x / 4) i m) e.r2).symm
    · rw [q]
      show Form.val y (RhiF _) = ext D.lT (fun i => Inst.Model.Ledger.Rhi (led t (x / 4) i)) e.r2
      rw [Inst.Model.Ledger.val_RhiF, (rows_congr hb).2.2.2]
      exact (Inst.Model.Ledger.ext_Rhi D.lT (fun m i => led t (x / 4) i m) e.r2).symm
  · have k5 : Form.val y (cIdn N e D ν k) = 0 := by
      by_cases h9 : k < 9
      · have q := m5 (ν * 9 + k) (by omega)
        rw [(div_mod_at ν k 9 h9).1, (div_mod_at ν k 9 h9).2] at q
        exact q
      · have q := m5' (ν * 8 + (k - 9)) (by omega)
        rw [(div_mod_at ν (k - 9) 8 (by omega)).1, (div_mod_at ν (k - 9) 8 (by omega)).2,
          (by omega : 9 + (k - 9) = k)] at q
        exact q
    unfold cIdn at k5
    rw [Inst.Model.Ledger.val_idnForm] at k5
    simp only [val_hW, val_hP] at k5
    rw [← k5]
    exact idnP_congr_D (npOf D ν) _ _ (fun n hn' => by rw [val_byteF, T.atP _ _ hν hn']) k
  · exact hot_last N e D t y T.sel (fun f hf => h f (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_append_right _ hf)))) l hl'

/-- The two claims that the sumchecks leave are members of the list. -/
theorem norms_rows [Scl] (u1 u2 : Form J E) (D : Dim) (lNI b B : ℕ) (y : J → E)
    (h : ∀ f ∈ normsCl N e u1 u2 D lNI b B, Form.val y f = 0) :
    Form.val y u1 = 0 ∧ Form.val y u2 = 0 :=
  ⟨h _ (by simp [normsCl, clNorms]), h _ (by simp [normsCl, clLedger])⟩

omit [Fintype J] [DecidableEq J] in
/-- An identity reads the sums at the numbers below 9 and the products at the numbers below 7
alone. -/
theorem idnP_congr (np : Inst.Model.NormPar) (Dd : ℕ → E) {Ws Ws' pv pv' : ℕ → E}
    (hW' : ∀ x, x < 9 → Ws x = Ws' x) (hP' : ∀ j, j < 7 → pv j = pv' j) (k : ℕ) :
    idnP np Ws Dd pv k = idnP np Ws' Dd pv' k := by
  by_cases hk : k < 9
  · rw [Inst.Model.Ledger.idnP_j1 np _ _ _ hk, Inst.Model.Ledger.idnP_j1 np _ _ _ hk, hW' k hk]
  · unfold Inst.Model.Ledger.idnP
    rw [if_neg hk, if_neg hk, hP' 0 (by norm_num), hP' 1 (by norm_num), hP' 2 (by norm_num),
      hP' 3 (by norm_num), hP' 4 (by norm_num), hP' 5 (by norm_num), hP' 6 (by norm_num)]

omit [Fintype J] [DecidableEq J] in
/-- From number 9 on an identity does not read the sums. -/
theorem idnP_congr_hi (np : Inst.Model.NormPar) (Dd Ws Ws' : ℕ → E) {pv pv' : ℕ → E}
    (hP' : ∀ j, j < 7 → pv j = pv' j) {k : ℕ} (hk : 9 ≤ k) :
    idnP np Ws Dd pv k = idnP np Ws' Dd pv' k := by
  unfold Inst.Model.Ledger.idnP
  rw [if_neg (by omega), if_neg (by omega), hP' 0 (by norm_num), hP' 1 (by norm_num),
    hP' 2 (by norm_num), hP' 3 (by norm_num), hP' 4 (by norm_num), hP' 5 (by norm_num),
    hP' 6 (by norm_num)]

omit [Fintype J] [DecidableEq J] in
/-- The lines (J1), as rows on the hidden sums: the hidden value under the slot of W_x is the digit
row's side of the identity. -/
theorem NormsLast.rowB [Scl] {D : Dim} {t : Cell → E} {lNI b s : ℕ} {y : J → E}
    (L : NormsLast N e D t lNI b s y) {ν : ℕ} (hν : ν < D.nNu) {x : ℕ} (hx : x < 9) :
    e.shW (9 * ν + x) - y (N.mW (9 * ν + x)) =
      ext D.lT (fun i => led t ν i x) e.pV +
        256 * Inst.Model.Ledger.cs (fun n => ext D.lT (fun i => led t ν i n) e.pV) (x + 1) -
        Inst.Model.Ledger.cs (fun n => ext D.lT (fun i => led t ν i n) e.pV) x := by
  have h := L.lines ν hν x (by omega)
  rw [Inst.Model.Ledger.idnP_j1 _ _ _ _ hx] at h
  linear_combination h

omit [Fintype J] [DecidableEq J] in
/-- The lines (J2) to (J9), as one claim on a vector pv that holds the hidden products of norm ν. -/
theorem NormsLast.rowLed [Scl] {D : Dim} {t : Cell → E} {lNI b s : ℕ} {y : J → E}
    (L : NormsLast N e D t lNI b s y) {ν : ℕ} (hν : ν < D.nNu) (pv : ℕ → E)
    (hpv : ∀ j, j < 7 → pv j = e.shP (7 * ν + j) - y (N.mP (7 * ν + j))) {k : ℕ} (hk : 9 ≤ k) :
    idnP (npOf D ν) (fun _ => 0) (fun n => ext D.lT (fun i => led t ν i n) e.pV) pv k = 0 := by
  by_cases h17 : k < 17
  · exact (idnP_congr_hi (npOf D ν) _ _ _ hpv hk).trans (L.lines ν hν k h17)
  · exact Inst.Model.Ledger.idnP_of_le _ _ _ _ (by omega)

omit [Fintype J] [DecidableEq J] in
/-- With NormsLast: if the hidden values under the slots of the sums W_s and of the row products are
the honest values, the extension of each defect of (J1) to (J9) vanishes at the norms' token
point. -/
theorem at_point [Scl] {D : Dim} {t : Cell → E} {lNI b s : ℕ} {y : J → E}
    (L : NormsLast N e D t lNI b s y)
    (hW' : ∀ ν, ν < D.nNu → ∀ x, x < 9 → e.shW (9 * ν + x) - y (N.mW (9 * ν + x)) = Wt D t e.pV ν x)
    (hP' : ∀ ν, ν < D.nNu → ∀ j, j < 7 →
      e.shP (7 * ν + j) - y (N.mP (7 * ν + j)) = pvt D t e.pV ν j) :
    ∀ ν, ν < D.nNu → ∀ k, k < 17 → ext D.lT (dJ D t k ν) e.pV = 0 := by
  intro ν hν k hk
  have e1 : ext D.lT (dJ D t k ν) e.pV =
      idnP (npOf D ν) (fun x => Wt D t e.pV ν x) (fun n => ext D.lT (fun i => led t ν i n) e.pV)
        (fun j => pvt D t e.pV ν j) k :=
    Inst.Model.Ledger.ext_idn D.lT (fun m i => led t ν i m) e.pV (npOf D ν)
      (fun x i => Inst.Model.Ledger.Wsum D.d (fun l j => bS D t ν l j i) x) k
  rw [e1]
  exact (idnP_congr (npOf D ν) _ (fun x hx => (hW' ν hν x hx).symm)
    (fun j hj => (hP' ν hν j hj).symm) k).trans (L.lines ν hν k hk)

end Means

end Cb.Pv.Lay.End
