-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadSumMet.lean: the hypotheses of next_token_of_calls (Johnson/Road/HeadSum.lean) can
be met together.

That theorem starts from functions on the columns of the output head's lookup calls: every value of
each function is a row of the call's table; 17 identities are 0; the cells are small; the layers
give what the head borrows. This file shows that these statements hold together for honest cells of
a true request for the next token, so the theorem is not empty.

The steps.
 1. marks_listed: a column that bears a mark after the verifier's marking is listed by a segment.
    rows_of_keys: so, if the padding key and all keys of all segments have a property, every value
    of a call's function has it. This is the converse of keys_of_fn (Johnson/Road/HeadFn.lean).
 2. calls_of_plainRF: from the field relation of the library's plain head, over any field: functions
    exist, and all their values are rows. The relation speaks of seven families, and of 99 ledger
    bytes. The verifier's calls hold more keys: two more segments, and 120 bytes. That these other
    keys are rows is a hypothesis of this step (RestRows).
 3. met_plain: the step at the library's honest cells of the plain head. RestRows stays a
    hypothesis. On these cells the keys that the head with the cost ledger has under the names HE0
    and HE1 are NOT rows of their table, since the cells of the looked-up values are all 0 there. So
    this witness needs other keys under these two names than the verifier's forms stand for.
 4. met_ledger: the same at the honest cells of the head with the cost ledger, with that head's own
    keys under HE0 and HE1 (kvL), the library's table for the kind of each call (tabL) and that
    table's padding value (padL). Nothing is assumed on keys.
 5. met_fits: next_token_of_calls applies to what met_ledger gives.

What stays a hypothesis in met_ledger, all of it on the verifier's record R alone: the marking of
each call's columns returns (hw); every segment of every call has a family's name, at most the
family's number of entries, and stands in a call of the family's kind (SegsFit); every family of
the plain head has such a segment with at least its number of entries (HasAll).
Johnson/Road/HeadCallsLaid.lean shows the three of every record whose layout the verifier's
function has returned, the last two at the library's sizes.

What is not claimed. Nothing on what a verifier's acceptance shows. The honest cells are the
library's; no prover's cells are looked at. The program does not import this file.
-/
import Johnson.Road.HeadSum
import Johnson.Road.HeadTabs

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model Inst.Model.Head

/-! ## 1. A column with a mark is listed -/

/-- An array of zeros reads 0 everywhere. -/
theorem getD_replicate_zero (J j : ℕ) : (Array.replicate J 0).getD j 0 = 0 := by
  by_cases h : j < J
  · simp [Array.getD, h]
  · simp [Array.getD, h]

/-- Marking the columns pos 0, ..., pos (n - 1): a column that bears a mark afterwards bore one
before or is one of these. -/
theorem fold_listed (pos mk : ℕ → ℕ) :
    ∀ (n : ℕ) (w w' : Array ℕ),
      (List.range n).foldlM (fun w x =>
        if pos x < w.size && w.getD (pos x) 1 == 0 then some (w.set! (pos x) (mk x)) else none)
        w = some w' →
      ∀ j, w'.getD j 0 ≠ 0 → w.getD j 0 ≠ 0 ∨ ∃ x, x < n ∧ j = pos x
  | 0, w, w', h, j, hj => by
    have e : w = w' := by simpa using h
    subst e
    exact Or.inl hj
  | n + 1, w, w', h, j, hj => by
    rw [List.range_succ, List.foldlM_append] at h
    obtain ⟨w1, h1, h2⟩ := bind_some h
    rw [List.foldlM_cons] at h2
    obtain ⟨w2, h3, h4⟩ := bind_some h2
    have e2 : w2 = w' := by simpa using h4
    subst e2
    by_cases hc : (pos n < w1.size && w1.getD (pos n) 1 == 0) = true
    · rw [if_pos hc] at h3
      have e3 := Option.some.inj h3
      subst e3
      by_cases hjp : j = pos n
      · exact Or.inr ⟨n, Nat.lt_succ_self n, hjp⟩
      · rw [Array.set!_eq_setIfInBounds, getD_set_ne w1 (fun e => hjp e.symm) (mk n)] at hj
        rcases fold_listed pos mk n w w1 h1 j hj with h5 | ⟨x, hx, hxj⟩
        · exact Or.inl h5
        · exact Or.inr ⟨x, Nat.lt_succ_of_lt hx, hxj⟩
    · rw [if_neg hc] at h3
      cases h3

/-- The same for the segments of a list. -/
theorem marks_listed {R : Model.Head.Run} :
    ∀ (l : List Model.Seg) (w w' : Array ℕ),
      l.foldlM (fun w g => Model.Head.markColumns R w g) w = some w' →
      ∀ j, w'.getD j 0 ≠ 0 →
        w.getD j 0 ≠ 0 ∨ ∃ g ∈ l, ∃ x, x < g.n ∧ j = g.pos.getD x 0
  | [], w, w', h, j, hj => by
    have e : w = w' := by simpa using h
    subst e
    exact Or.inl hj
  | g :: l, w, w', h, j, hj => by
    rw [List.foldlM_cons] at h
    obtain ⟨w1, h1, h2⟩ := bind_some h
    rcases marks_listed l w1 w' h2 j hj with h3 | ⟨g', hg', x, hx, hxj⟩
    · rcases fold_listed (fun x => g.pos.getD x 0)
        (fun x => if Model.Head.perEntry g.name && Model.Head.firstEntry R.L g.name + x ≥ R.h.V
          then 2 else 1) g.n w w1 h1 j h3 with h4 | ⟨x, hx, hxj⟩
      · exact Or.inl h4
      · exact Or.inr ⟨g, List.mem_cons.mpr (Or.inl rfl), x, hx, hxj⟩
    · exact Or.inr ⟨g', List.mem_cons.mpr (Or.inr hg'), x, hx, hxj⟩

/-- What holds of the padding key and of every key of every segment holds of all values of a call's
function. -/
theorem rows_of_keys {K : Type} [Field K] {R : Model.Head.Run} {J : ℕ} {l : List Model.Seg}
    {w : Array ℕ}
    (h : l.foldlM (fun w g => Model.Head.markColumns R w g) (Array.replicate J 0) = some w)
    {kv : String → ℕ → ℕ → K} {pad : K} {f : ℕ → ℕ → K} (Kf : KeyFn l w J kv pad f)
    (P : K → Prop) (n : ℕ) (hpad : P pad)
    (hseg : ∀ g ∈ l, ∀ x, x < g.n → ∀ i, i < n → P (kv g.name x i)) :
    ∀ j, j < J → ∀ i, i < n → P (f j i) := by
  intro j hj i hi
  by_cases h0 : w.getD j 0 = 0
  · have e := congrFun (Kf.pad j hj h0) i
    rw [e]
    exact hpad
  · rcases marks_listed l _ w h j h0 with h1 | ⟨g, hg, x, hx, hxj⟩
    · exact absurd (getD_replicate_zero J j) h1
    · have e := congrFun (Kf.seg g hg x hx) i
      rw [hxj, e]
      exact hseg g hg x hx i hi

/-! ## 2. From the plain head's relation to the calls' functions -/

section Step

variable {K : Type} [Field K]

/-- What is asked of the keys of which the plain head's relation does not speak: a key of a segment
of call q is a row of T q, unless it is a key of a family of the plain head, below the family's
number of entries, in a call with the family's table. -/
def RestRows (R : Model.Head.Run) (kv : String → ℕ → ℕ → K) (T : ℕ → Lut) : Prop :=
  ∀ q, ∀ g ∈ (R.L.calls.getD q default).segs, ∀ a, a < g.n →
    (¬ ∃ f : Cm.Plain.Fam, g.name = segName f ∧ T q = lutOf f ∧ a < Cm.Plain.len f) →
    ∀ i, i < nT → InLut (T q) (kv g.name a i)

/-- From the field relation of the plain head: the calls' functions exist, and every value of each
is a row of the call's table. -/
theorem calls_of_plainRF {R : Model.Head.Run} {kv : String → ℕ → ℕ → K} {T : ℕ → Lut} {c : K}
    (hc : c * 2 ^ 23 = 1) {np : NormPar} {tz : Head.Cells ℤ} {H : ℕ → ℕ → K} {y : Req}
    (A : CallsFit R kv T c np (tz.cast K) H y) {w : ℕ → Array ℕ} {pad : ℕ → K}
    (hw : ∀ q, (R.L.calls.getD q default).segs.foldlM
      (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some (w q))
    (hpad : ∀ q, InLut (T q) (pad q)) (hrest : RestRows R kv T)
    (h : Cm.Plain.TP.RF (F := K) np H y tz) :
    ∃ fn : ℕ → ℕ → ℕ → K,
      (∀ q, KeyFn (R.L.calls.getD q default).segs (w q) (R.L.calls.getD q default).J kv
        (pad q) (fn q)) ∧
      ∀ q j, j < (R.L.calls.getD q default).J → ∀ i, i < nT → InLut (T q) (fn q j i) := by
  choose fn hfn using fun q => exists_keyFn (hw q) kv (pad q)
  refine ⟨fn, hfn, fun q =>
    rows_of_keys (hw q) (hfn q) (fun v => InLut (T q) v) nT (hpad q) ?_⟩
  intro g hg a ha i hi
  show InLut (T q) (kv g.name a i)
  by_cases hf : ∃ f : Cm.Plain.Fam, g.name = segName f ∧ T q = lutOf f ∧ a < Cm.Plain.len f
  · obtain ⟨f, hname, hT, hlen⟩ := hf
    obtain ⟨_, _, _, _, _, _, hkv⟩ := A f
    rw [hname, hkv, hT]
    have hk := h.keys f a i hlen hi
    cases f with
    | HD0 => exact (Down.hd0_plain hc np (tz.cast K) H y a i).1 hk
    | _ => exact hk
  · exact hrest q g hg a ha hf i hi

end Step

/-! ## 3. At the honest cells of the plain head -/

/-- At every lawful table there are an index and a true request for the next token such that, at the
honest cells of the plain head: the final normalisation is lawful, the layers give what the head
borrows, the cells are small, the identities are 0 in the challenge field, and for every record R,
keys kv, tables T and padding keys with CallsFit, a marking that returns, padding keys that are rows
and RestRows, the calls' functions exist and all their values are rows. -/
theorem met_plain {s : Cm.Scales} (hs : s.Lawful) :
    ∃ (i : Cm.Idx) (x : Instance ppref), x.r = 1023 ∧ x.e = 1024 ∧ s.nf.OK ∧
      Top.LayersGive s.kap (fun _ => tbRef) i.index.val x.prompt (Cm.trace2 s i x).vHead ∧
      Cm.Plain.Small (2 ^ 18) (Cm.trace2 s i x).vHead ∧
      (∀ a < nT, ∀ k < 17,
        Cm.Plain.idn s.nf ((Cm.trace2 s i x).vHead.cast Cb.Gl.E) a k = 0) ∧
      ∀ (R : Model.Head.Run) (kv : String → ℕ → ℕ → Cb.Gl.E) (T : ℕ → Lut) (c : Cb.Gl.E)
        (w : ℕ → Array ℕ) (pad : ℕ → Cb.Gl.E), c * 2 ^ 23 = 1 →
        CallsFit R kv T c s.nf ((Cm.trace2 s i x).vHead.cast Cb.Gl.E)
          (fun j v => ((i.index.val.H j v : ℤ) : Cb.Gl.E)) (Cm.reqOf x) →
        (∀ q, (R.L.calls.getD q default).segs.foldlM
          (fun w g => Model.Head.markColumns R w g)
          (Array.replicate (R.L.calls.getD q default).J 0) = some (w q)) →
        (∀ q, InLut (T q) (pad q)) → RestRows R kv T →
        ∃ fn : ℕ → ℕ → ℕ → Cb.Gl.E,
          (∀ q, KeyFn (R.L.calls.getD q default).segs (w q) (R.L.calls.getD q default).J kv
            (pad q) (fn q)) ∧
          ∀ q j, j < (R.L.calls.getD q default).J → ∀ a, a < nT → InLut (T q) (fn q j a) := by
  obtain ⟨i, x, hr, he, hn, hl, h⟩ := Top.next_hyps_met hs
  have hE := Down.plainRF_gl.2 h
  exact ⟨i, x, hr, he, hn, hl, hE.small, hE.idns,
    fun R kv T c w pad hc A hw hpad hrest => calls_of_plainRF hc A hw hpad hrest hE⟩

/-- At the honest cells of the plain head the ledger's bytes from 99 on have the cell 0. -/
theorem hr_high (s : Cm.Scales) (i : Cm.Idx) (x : Instance ppref) {n : ℕ} (hn : 99 ≤ n) (a : ℕ) :
    (Cm.trace2 s i x).vHead.hr n a = 0 := by
  show (if n < Cm.Plain.nHr then _ else (0 : ℤ)) = 0
  rw [if_neg (by unfold Cm.Plain.nHr; omega)]

/-- The multiplier of a byte from 99 on is 1. -/
theorem mu_high {n : ℕ} (hn : 99 ≤ n) : Ledger.mu n = 1 := by
  unfold Ledger.mu
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

/-- So there the key of ROW at an entry from 99 on is 128, a row of the table of the bytes. -/
theorem row_high {K : Type} [Field K] (s : Cm.Scales) (i : Cm.Idx) (x : Instance ppref)
    (np : NormPar) (H : ℕ → ℕ → K) (y : Req) {n : ℕ} (hn : 99 ≤ n) (a : ℕ) :
    InLut R8 (Cm.Plain.TP.key np ((Cm.trace2 s i x).vHead.cast K) H y .ROW n a) := by
  refine ⟨128, by show 128 < 2 ^ 8; norm_num, ?_⟩
  show ((Ledger.mu n : ℤ) : K) * (128 + (((Cm.trace2 s i x).vHead.hr n a : ℤ) : K)) =
    (((128 : ℕ) : ℤ) : K)
  rw [mu_high hn, hr_high s i x hn a]
  norm_num

/-! ## 4. At the honest cells of the head with the cost ledger -/

/-- The kind of the call in which the verifier looks a family's keys up. -/
def famKind : Head.Fam → String
  | .NF => "R16" | .NFH => "R16" | .HD0 => "R16" | .HD1 => "R16" | .ROW => "R8" | .HD2 => "R8"
  | .HE0 => "FE" | .HE1 => "FE" | .CNF => "FC"

/-- The same for a family of the plain head. -/
def plainKind : Cm.Plain.Fam → String
  | .NF => "R16" | .NFH => "R16" | .HD0 => "R16" | .HD1 => "R16" | .ROW => "R8" | .HD2 => "R8"
  | .CNF => "FC"

/-- Every segment of every call has a family's name, at most the family's number of entries, and
stands in a call of the family's kind. -/
def SegsFit (R : Model.Head.Run) : Prop :=
  ∀ q, ∀ g ∈ (R.L.calls.getD q default).segs, ∃ s : Head.Fam,
    g.name = nameH s ∧ g.n ≤ Head.len s ∧ (R.L.calls.getD q default).kind = famKind s

/-- Every family of the plain head has a segment with at least its number of entries, in a call of
its kind. -/
def HasAll (R : Model.Head.Run) : Prop :=
  ∀ f : Cm.Plain.Fam, ∃ q g, g ∈ (R.L.calls.getD q default).segs ∧ g.name = segName f ∧
    Cm.Plain.len f ≤ g.n ∧ (R.L.calls.getD q default).kind = plainKind f

/-- The library's table for the kind of call number q. -/
def tabL (R : Model.Head.Run) (q : ℕ) : Lut := lutOfKind (R.L.calls.getD q default).kind

/-- The table of the kind "R16" is the library's R16. -/
theorem lut_R16 : lutOfKind "R16" = R16 := by simp [lutOfKind]
/-- The table of the kind "R8" is the library's R8. -/
theorem lut_R8 : lutOfKind "R8" = R8 := by simp [lutOfKind]
/-- The table of the kind "FE" is the library's FE. -/
theorem lut_FE : lutOfKind "FE" = FE := by simp [lutOfKind]
/-- The table of the kind "FC" is the library's FC. -/
theorem lut_FC : lutOfKind "FC" = FC := by simp [lutOfKind]

/-- The padding value of the clamp's table is its row 2^15. -/
theorem FC_pad : FC.pad = FC.row 32768 := by
  rw [← rowFC_eq 32768]
  have e : Model.Layer.rowFC 32768 = 549755846656 := by decide
  rw [e]
  show (2 : ℤ) ^ 15 + 2 ^ 39 = ((549755846656 : ℕ) : ℤ)
  norm_num

/-- The padding value of the table of exponentials is its row 0. -/
theorem FE_pad : FE.pad = FE.row 0 := by
  rw [← rowFE_eq 0]
  have e : rowFE 0 = 1099511627776 := by decide
  rw [e]
  show (2 : ℤ) ^ 40 = ((1099511627776 : ℕ) : ℤ)
  norm_num

section Ledger

variable {K : Type} [Field K]

/-- The padding value of the table of a kind is a row of it. -/
theorem pad_inLut (k : String) : InLut (lutOfKind k) (((lutOfKind k).pad : ℤ) : K) := by
  unfold lutOfKind
  split_ifs
  · exact ⟨32768, by show 32768 < 2 ^ 16; norm_num, by rw [FC_pad]⟩
  · exact ⟨0, by show 0 < 2 ^ 16; norm_num, by rw [FE_pad]⟩
  · exact ⟨0, by show 0 < 2 ^ 8; norm_num, by simp [R8]⟩
  · exact ⟨0, by show 0 < 2 ^ 16; norm_num, by simp [R16]⟩

/-- The keys under the verifier's nine names: the seven families of the plain head as the verifier
looks them up, at the request y; under HE0 and HE1 the keys of the head with the cost ledger, at the
request y'. Under any other name: those of HE1. -/
def kvL (c : K) (np : NormPar) (t : Head.Cells K) (H : ℕ → ℕ → K) (y y' : Req) (n : String) :
    ℕ → ℕ → K :=
  if n = "NF" then keyOf c np t H y .NF
  else if n = "NFH" then keyOf c np t H y .NFH
  else if n = "HD0" then keyOf c np t H y .HD0
  else if n = "HD1" then keyOf c np t H y .HD1
  else if n = "ROW" then keyOf c np t H y .ROW
  else if n = "HD2" then keyOf c np t H y .HD2
  else if n = "CNF" then keyOf c np t H y .CNF
  else if n = "HE0" then Policy.LedgerHead.key np t H y' .HE0
  else Policy.LedgerHead.key np t H y' .HE1

/-- At the name of a family of the plain head the keys kvL are the plain head's keys. -/
theorem kvL_plain (c : K) (np : NormPar) (t : Head.Cells K) (H : ℕ → ℕ → K) (y y' : Req)
    (f : Cm.Plain.Fam) : kvL c np t H y y' (segName f) = keyOf c np t H y f := by
  cases f <;> simp [kvL, segName]

/-- The table of the kind of a family of the plain head is the library's table of that family. -/
theorem lutOf_kindP (f : Cm.Plain.Fam) : lutOfKind (plainKind f) = lutOf f := by
  cases f <;> simp [plainKind, lutOfKind, lutOf, Cm.Plain.TP.tableOf]

/-- With HasAll, these keys and tables have CallsFit. -/
theorem callsFit_kvL {R : Model.Head.Run} (Hs : HasAll R) (c : K) (np : NormPar)
    (t : Head.Cells K) (H : ℕ → ℕ → K) (y y' : Req) :
    CallsFit R (kvL c np t H y y') (tabL R) c np t H y := by
  intro f
  obtain ⟨q, g, hg, hname, hn, hk⟩ := Hs f
  refine ⟨q, g, hg, hname, hn, ?_, kvL_plain c np t H y y' f⟩
  unfold tabL
  rw [hk, lutOf_kindP]

/-- Every key under a family's name, below the family's number of entries, is a row of the table of
the family's kind, given the two field relations. -/
theorem rows_kvL {c : K} (hc : c * 2 ^ 23 = 1) {np : NormPar} {tz : Head.Cells ℤ}
    {H : ℕ → ℕ → K} {y y' : Req} (hP : Cm.Plain.TP.RF (F := K) np H y tz)
    (hL : Policy.LedgerHead.RF (F := K) np H y' tz) (s : Head.Fam) {a i : ℕ}
    (ha : a < Head.len s) (hi : i < nT) :
    InLut (lutOfKind (famKind s)) (kvL c np (tz.cast K) H y y' (nameH s) a i) := by
  cases s
  case NF =>
    have e : kvL c np (tz.cast K) H y y' "NF" = keyOf c np (tz.cast K) H y .NF := by simp [kvL]
    show InLut (lutOfKind "R16") (kvL c np (tz.cast K) H y y' "NF" a i)
    rw [e, lut_R16]
    exact hP.keys .NF a i ha hi
  case NFH =>
    have e : kvL c np (tz.cast K) H y y' "NFH" = keyOf c np (tz.cast K) H y .NFH := by simp [kvL]
    show InLut (lutOfKind "R16") (kvL c np (tz.cast K) H y y' "NFH" a i)
    rw [e, lut_R16]
    exact hP.keys .NFH a i ha hi
  case HD0 =>
    have e : kvL c np (tz.cast K) H y y' "HD0" = keyOf c np (tz.cast K) H y .HD0 := by simp [kvL]
    show InLut (lutOfKind "R16") (kvL c np (tz.cast K) H y y' "HD0" a i)
    rw [e, lut_R16]
    exact (Down.hd0_plain hc np (tz.cast K) H y a i).1 (hP.keys .HD0 a i ha hi)
  case HD1 =>
    have e : kvL c np (tz.cast K) H y y' "HD1" = keyOf c np (tz.cast K) H y .HD1 := by simp [kvL]
    show InLut (lutOfKind "R16") (kvL c np (tz.cast K) H y y' "HD1" a i)
    rw [e, lut_R16]
    exact hP.keys .HD1 a i ha hi
  case ROW =>
    have e : kvL c np (tz.cast K) H y y' "ROW" = keyOf c np (tz.cast K) H y .ROW := by simp [kvL]
    show InLut (lutOfKind "R8") (kvL c np (tz.cast K) H y y' "ROW" a i)
    rw [e, lut_R8]
    exact hL.keys .ROW a i ha hi
  case HD2 =>
    have e : kvL c np (tz.cast K) H y y' "HD2" = keyOf c np (tz.cast K) H y .HD2 := by simp [kvL]
    show InLut (lutOfKind "R8") (kvL c np (tz.cast K) H y y' "HD2" a i)
    rw [e, lut_R8]
    exact hP.keys .HD2 a i ha hi
  case HE0 =>
    have e : kvL c np (tz.cast K) H y y' "HE0" =
        Policy.LedgerHead.key np (tz.cast K) H y' .HE0 := by simp [kvL]
    show InLut (lutOfKind "FE") (kvL c np (tz.cast K) H y y' "HE0" a i)
    rw [e, lut_FE]
    exact hL.keys .HE0 a i ha hi
  case HE1 =>
    have e : kvL c np (tz.cast K) H y y' "HE1" =
        Policy.LedgerHead.key np (tz.cast K) H y' .HE1 := by simp [kvL]
    show InLut (lutOfKind "FE") (kvL c np (tz.cast K) H y y' "HE1" a i)
    rw [e, lut_FE]
    exact hL.keys .HE1 a i ha hi
  case CNF =>
    have e : kvL c np (tz.cast K) H y y' "CNF" = keyOf c np (tz.cast K) H y .CNF := by simp [kvL]
    show InLut (lutOfKind "FC") (kvL c np (tz.cast K) H y y' "CNF" a i)
    rw [e, lut_FC]
    exact hP.keys .CNF a i ha hi

/-- From the two field relations, for a record R with SegsFit whose marking returns: the calls'
functions exist for the keys kvL and the tables' padding values, and all their values are rows. -/
theorem calls_of_ledgerRF {R : Model.Head.Run} (S : SegsFit R) {c : K} (hc : c * 2 ^ 23 = 1)
    {np : NormPar} {tz : Head.Cells ℤ} {H : ℕ → ℕ → K} {y y' : Req} {w : ℕ → Array ℕ}
    (hw : ∀ q, (R.L.calls.getD q default).segs.foldlM
      (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some (w q))
    (hP : Cm.Plain.TP.RF (F := K) np H y tz) (hL : Policy.LedgerHead.RF (F := K) np H y' tz) :
    ∃ fn : ℕ → ℕ → ℕ → K,
      (∀ q, KeyFn (R.L.calls.getD q default).segs (w q) (R.L.calls.getD q default).J
        (kvL c np (tz.cast K) H y y') (((tabL R q).pad : ℤ) : K) (fn q)) ∧
      ∀ q j, j < (R.L.calls.getD q default).J → ∀ i, i < nT → InLut (tabL R q) (fn q j i) := by
  choose fn hfn using fun q =>
    exists_keyFn (hw q) (kvL c np (tz.cast K) H y y') (((tabL R q).pad : ℤ) : K)
  refine ⟨fn, hfn, fun q =>
    rows_of_keys (hw q) (hfn q) (fun v => InLut (tabL R q) v) nT (pad_inLut _) ?_⟩
  intro g hg a ha i hi
  obtain ⟨s, hname, hn, hk⟩ := S q g hg
  show InLut (tabL R q) (kvL c np (tz.cast K) H y y' g.name a i)
  unfold tabL
  rw [hk, hname]
  exact rows_kvL hc hP hL s (lt_of_lt_of_le ha hn) hi

end Ledger

/-- **The hypotheses of next_token_of_calls are met together.** At every lawful table and for every
policy with AcceptancePolicy.OK there are an index, a true request for the next token and integer cells such
that: the final normalisation is lawful; the layers give what the head borrows; the cells are small;
the identities are 0 in the challenge field; and for every record R with SegsFit and HasAll whose
marking returns, and every inverse c of 2^23: the keys kvL and the tables tabL have CallsFit, the
calls' functions exist, and every value of each is a row of the call's table. -/
theorem met_ledger {s : Cm.Scales} (hs : s.Lawful) {pol : AcceptancePolicy} (hpol : pol.OK) :
    ∃ (i : Index ppref) (x : Instance ppref) (tz : Head.Cells ℤ),
      x.r = 1023 ∧ x.e = 1024 ∧ s.nf.OK ∧
      Top.LayersGive s.kap (fun _ => tbRef) i.val x.prompt tz ∧
      Cm.Plain.Small (2 ^ 18) tz ∧
      (∀ a < nT, ∀ k < 17, Cm.Plain.idn s.nf (tz.cast Cb.Gl.E) a k = 0) ∧
      ∀ (R : Model.Head.Run) (c : Cb.Gl.E) (w : ℕ → Array ℕ), c * 2 ^ 23 = 1 →
        SegsFit R → HasAll R →
        (∀ q, (R.L.calls.getD q default).segs.foldlM
          (fun w g => Model.Head.markColumns R w g)
          (Array.replicate (R.L.calls.getD q default).J 0) = some (w q)) →
        CallsFit R
          (kvL c s.nf (tz.cast Cb.Gl.E) (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Cm.reqOf x)
            (Req.of pol x))
          (tabL R) c s.nf (tz.cast Cb.Gl.E) (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E))
          (Cm.reqOf x) ∧
        ∃ fn : ℕ → ℕ → ℕ → Cb.Gl.E,
          (∀ q, KeyFn (R.L.calls.getD q default).segs (w q) (R.L.calls.getD q default).J
            (kvL c s.nf (tz.cast Cb.Gl.E) (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E))
              (Cm.reqOf x) (Req.of pol x))
            (((tabL R q).pad : ℤ) : Cb.Gl.E) (fn q)) ∧
          ∀ q j, j < (R.L.calls.getD q default).J → ∀ a, a < nT →
            InLut (tabL R q) (fn q j a) := by
  obtain ⟨i, x, tz, hr, he, _, hn, hl, h⟩ :=
    Top.ledger_next_hyps_met (p := Cb.Gl.p) hs hpol
  have hL := Down.ledgerRF_gl.2 h
  have h0 : ∀ a < nT, (Req.of pol x).rhoC a = 0 := fun a _ =>
    HeadReq.rhoC_of_le (y := Req.of pol x) (le_of_eq hr.symm) a
  have hP := (HeadReq.plainRF_req (HeadReq.alike_reqOf_of pol x)).2
    (HeadReq.plain_of_ledger h0 hL)
  exact ⟨i, x, tz, hr, he, hn, hl, hP.small, hP.idns, fun R c w hc S Hs hw =>
    ⟨callsFit_kvL Hs c s.nf _ _ _ _, calls_of_ledgerRF S hc hw hP hL⟩⟩

/-- next_token_of_calls applies to what met_ledger gives: for a record R with SegsFit and HasAll
whose marking returns. The conclusion is known beforehand, since the request is a true one: what is
shown is only that the statements fit each other letter by letter. -/
theorem met_fits {s : Cm.Scales} (hs : s.Lawful) {pol : AcceptancePolicy} (hpol : pol.OK)
    {R : Model.Head.Run} {c : Cb.Gl.E} (hc : c * 2 ^ 23 = 1) (S : SegsFit R) (Hs : HasAll R)
    {w : ℕ → Array ℕ}
    (hw : ∀ q, (R.L.calls.getD q default).segs.foldlM
      (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some (w q)) :
    ∃ (i : Index ppref) (x : Instance ppref), x.r = 1023 ∧ x.e = 1024 ∧
      RinfR ppref s.kap s.nf (fun _ => tbRef) pol i x := by
  obtain ⟨i, x, tz, hr, he, hn, hl, hsm, hid, hR⟩ := met_ledger hs hpol
  obtain ⟨A, fn, Kf, keys⟩ := hR R c w hc S Hs hw
  exact ⟨i, x, hr, he, next_token_of_calls hc hn i x hr he A hw Kf hsm keys hid hl pol⟩

#print axioms marks_listed
#print axioms rows_of_keys
#print axioms calls_of_plainRF
#print axioms met_plain
#print axioms row_high
#print axioms calls_of_ledgerRF
#print axioms met_ledger
#print axioms met_fits

end OnBytes.Road.Hd
