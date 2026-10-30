-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadReads.lean: if every table of the output head's reads holds what it says of its
matrix, each entry that the head's forms can name is a sum of cells under the table's own weights.

The claims of the head's sub-proof read entries of a vector of reads. The vector is made of fifteen
tables, which the verifier's routine tablesOf lists (OnBytes/Model/HeadTables.lean). The forms name
an entry as "entry e of the table with this name". The smallness test names it as "column c, run sg
of the rows of the record Fn" (HTailF2.tabAt, OnBytes/Model/Tail.lean). This file shows where the
two meet, for the twelve tables on hf, the residual stream, hd and hr, and reads the outcome on the
cells cellsH of Johnson/Road/HeadPlace.lean.

What is compared with what: texts of the verifier with each other: addFun and tablesOf with tabAt,
and planH2 and matsH (OnBytes/Model/HeadPlan.lean) for the sizes of the matrices. cellsH is a
definition of Johnson/Road/HeadPlace.lean, Holds one of Johnson/Road/FormsKeysMat.lean. The library
is mentioned only through the type of cellsH.

Main definitions.
 - Ask, addAsk, recOf, Uni: one line of the list in tablesOf; the record of a part of its table;
   "all parts have m rows and k columns".
 - WfT: no table is empty, each ends inside the vector, no two begin at one entry.
 - asksH: the list of tablesOf, with what the routine computes on the way as letters.
 - SumShort, SumLong, TrueH: what the reads hold.
 - MadeH: the parts of a run are the verifier's own results.
Main theorems.
 - planH2_mats, matsH_at: the list of matrices in the plan that planH2 returns, and its sizes.
 - parts_fold, addAsk_spec, fold_spec: what adding tables does to the list.
 - find_of_nodup, table_entry: the forms' name of an entry against the smallness test's.
 - short_read, long_read: one table.
 - tables_of_ok: what tablesOf returns is the fold of addFun over asksH.
 - trueH_of_holds, trueH_of_made: the twelve tables.
 - longAt_of_sum, shortAt_of_sum: a table whose weights are made from a point is true at that point
   in the sense of Johnson/Road/HeadLines.lean. xZV_point, xYN_point: the stream's two tables.
 - lentH_same: the hypothesis LentH is not empty.

The hypotheses of trueH_of_holds, and where they are met. planH2, tablesOf return: at the full-size
example by a run (Johnson/Road/HeadPlaceRun.lean), tablesOf there with made-up points. NumH, BorderH
and h.la = 16: theorems from the verifier's layouts at the sizes of that example
(Johnson/Road/HeadPlace.lean). Holds for every record of the list: no theorem concludes it, and the
verifier never tests it: for each record and each run of rows it adds one claim, a random
combination over the columns. It can be met at any matrices (holdsH_met,
Johnson/Road/HeadMet.lean).

At which sizes. table_entry, short_read and long_read have the sizes as letters. trueH_of_holds and
trueH_of_made compare texts of the verifier with each other and yet stand at the sizes of the
full-size example alone: FullH, NumH and BorderH are among their hypotheses.

What is not claimed. Nothing on the three tables of bH. Nothing on the number of columns under which
the smallness test's own claims name an entry. Holds and TrueH speak of an entry of a virtual row of
the array of reads (World.entry); that this array has one row, which is its virtual row, is not
shown. Which feature a limb of a value is, is not the matter of this file: see the head of
Johnson/Road/HeadPlace.lean. Nothing is a statement on what a verifier's acceptance shows. The
program does not import this file.
-/
import Johnson.Road.HeadPlace
import Johnson.Road.HeadLines
import Johnson.Road.FormsKeysTab
import Johnson.Road.FormsKeysPlan
import OnBytes.Model.HeadTables

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open OnBytes.Model (Reading World HFun HTailF2 TMat Fork Tail2 Settings)
open OnBytes.Model.Head (HL Border Owner HPlanH2 Tables addFun matsH planH2 ownerHeld)

/-! ## The matrices of the plan -/

/-- ownerHeld keeps the list of matrices and its length. -/
theorem ownerHeld_keeps {O : Owner} {NGr : ℕ} {tl tl' : HTailF2} {Fp : Fork} {Tp : Tail2}
    (h : ownerHeld O NGr tl Fp Tp = .ok tl') : tl'.mats = tl.mats ∧ tl'.NM = tl.NM := by
  unfold Model.Head.ownerHeld at h
  cases hb : O.tl.ix.TX.back? with
  | none =>
    simp only [hb] at h
    have h' : (Except.error "internal-h-owner-TX" : Except String HTailF2) = .ok tl' := h
    cases h'
  | some t =>
    simp only [hb] at h
    obtain ⟨last, -, h⟩ := ok_of_bind (x := (pure t : Except String ℕ)) h
    obtain ⟨-, -, h⟩ := ok_of_bind h
    obtain ⟨-, -, h⟩ := ok_of_bind h
    obtain ⟨t3, h3, h⟩ := ok_of_bind h
    obtain ⟨pe, -, h⟩ := ok_of_bind h
    obtain ⟨-, -, h⟩ := ok_of_bind h
    have e := (Except.ok.inj h).symm
    subst e
    exact borderMeans_keeps h3

/-- The record of the smallness test in the plan that planH2 returns has the list matsH, and NM is
the list's length. -/
theorem planH2_mats {g : Settings} {h : Model.Head.Shape} {L : HL} {b : Border} {O : Owner}
    {NGr lkW : ℕ} {hp : HPlanH2} (hpl : planH2 g h L b O NGr lkW = .ok hp) :
    ∃ sid, hp.tl.mats = matsH h L b (1 + NGr) sid ∧
      hp.tl.NM = (matsH h L b (1 + NGr) sid).size := by
  unfold Model.Head.planH2 at hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨pc, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  cases hs : O.tl.mats[O.iXO]? with
  | none =>
    simp only [hs] at hpl
    have h' : (Except.error "internal-h-owner-TX" : Except String HPlanH2) = .ok hp := hpl
    cases h'
  | some M0 =>
    simp only [hs] at hpl
    obtain ⟨stream, -, hpl⟩ := ok_of_bind (x := (pure M0 : Except String TMat)) hpl
    obtain ⟨t1, h1, hpl⟩ := ok_of_bind hpl
    obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
    obtain ⟨r, hr, hpl⟩ := ok_of_bind hpl
    obtain ⟨t2, Fp, Tp⟩ := r
    obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
    obtain ⟨Tp2, -, hpl⟩ := ok_of_bind hpl
    obtain ⟨t3, h3, hpl⟩ := ok_of_bind hpl
    obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
    have e := (Except.ok.inj hpl).symm
    subst e
    obtain ⟨s1, s2⟩ := shape_mats h1
    obtain ⟨a1, a2⟩ := addTrees_keeps hr
    obtain ⟨o1, o2⟩ := ownerHeld_keeps h3
    exact ⟨stream.aId, o1.trans (a1.trans s1), o2.trans (a2.trans s2)⟩

/-- The list matsH for hf in four parts: eight matrices; the rows and columns of the parts of hf, of
hd, of hr and of the stream. -/
theorem matsH_at {h : Model.Head.Shape} (L : HL) (b : Border) (gid sid : ℕ) (hN : h.NHf = 4) :
    (matsH h L b gid sid).size = 8 ∧
    (∀ q < 4, ((matsH h L b gid sid).getD q {}).m = L.m ∧
      ((matsH h L b gid sid).getD q {}).k = L.k) ∧
    ((matsH h L b gid sid).getD 4 {}).m = L.mD ∧ ((matsH h L b gid sid).getD 4 {}).k = L.kD ∧
    ((matsH h L b gid sid).getD 5 {}).m = L.mR ∧ ((matsH h L b gid sid).getD 5 {}).k = L.kR ∧
    ((matsH h L b gid sid).getD 7 {}).m = b.mxb ∧ ((matsH h L b gid sid).getD 7 {}).k = b.kxb := by
  unfold Model.Head.matsH
  rw [hN]
  refine ⟨rfl, fun q hq => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  interval_cases q <;> exact ⟨rfl, rfl⟩

/-! ## Adding a table -/

/-- One line of the list in tablesOf: the number of the matrix's first part, the number of parts,
the rows of a run, the weights, the table's name. -/
abbrev Ask := ℕ × ℕ × ℕ × Array E × String

/-- addFun on a line of the list. -/
def addAsk (mats : Array TMat) (t : Tables) (a : Ask) : Option Tables :=
  addFun mats t a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2

/-- The record of part q of the table of the line a, if the table begins at entry tb and each part
has w entries. -/
def recOf (a : Ask) (tb w q : ℕ) : HFun :=
  { mat := a.1 + q, len := a.2.2.1, phi := a.2.2.2.1, tree := 2, start := tb + q * w }

/-- All parts of the matrix of the line a have m rows and k columns. -/
def Uni (mats : Array TMat) (a : Ask) (m k : ℕ) : Prop :=
  ∀ q < a.2.1, (mats.getD (a.1 + q) {}).m = m ∧ (mats.getD (a.1 + q) {}).k = k

/-- The step of addFun for one part. -/
def partStep (mats : Array TMat) (M0 Lf : ℕ) (phi : Array E) (s : Array HFun × ℕ) (q : ℕ) :
    Array HFun × ℕ :=
  (s.1.push { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 },
    s.2 + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf))

/-- addFun, written with partStep. -/
theorem addFun_eq (mats : Array TMat) (t : Tables) (M0 parts Lf : ℕ) (phi : Array E)
    (nm : String) :
    addFun mats t M0 parts Lf phi nm =
      if ((List.range parts).foldl (partStep mats M0 Lf phi) (t.funs, t.p)).2 == t.p then none
      else some {
        funs := ((List.range parts).foldl (partStep mats M0 Lf phi) (t.funs, t.p)).1
        p := ((List.range parts).foldl (partStep mats M0 Lf phi) (t.funs, t.p)).2
        tab := t.tab ++ [(nm, t.p,
          ((List.range parts).foldl (partStep mats M0 Lf phi) (t.funs, t.p)).2 - t.p)] } :=
  rfl

/-- The records after n parts of one size: the old records are kept, part q has its record, which
begins q (k (m / Lf)) entries behind the table's first entry, and the vector has grown by n such
parts. -/
theorem parts_fold (mats : Array TMat) (M0 Lf : ℕ) (phi : Array E) (m k : ℕ)
    (funs : Array HFun) (p : ℕ) : ∀ n : ℕ,
    (∀ q < n, (mats.getD (M0 + q) {}).m = m ∧ (mats.getD (M0 + q) {}).k = k) →
    (∀ Fn ∈ funs, Fn ∈ ((List.range n).foldl (partStep mats M0 Lf phi) (funs, p)).1) ∧
    (∀ q < n, recOf (M0, n, Lf, phi, "") p (k * (m / Lf)) q ∈
      ((List.range n).foldl (partStep mats M0 Lf phi) (funs, p)).1) ∧
    ((List.range n).foldl (partStep mats M0 Lf phi) (funs, p)).2 = p + n * (k * (m / Lf))
  | 0, _ => ⟨fun _ h => h, fun q hq => absurd hq (Nat.not_lt_zero q), by
      show p = p + 0 * (k * (m / Lf))
      rw [Nat.zero_mul, Nat.add_zero]⟩
  | n + 1, hU => by
    obtain ⟨i1, i2, i3⟩ := parts_fold mats M0 Lf phi m k funs p n
      fun q hq => hU q (Nat.lt_succ_of_lt hq)
    rw [List.range_succ, List.foldl_append]
    generalize (List.range n).foldl (partStep mats M0 Lf phi) (funs, p) = r at i1 i2 i3 ⊢
    show (∀ Fn ∈ funs, Fn ∈ (partStep mats M0 Lf phi r n).1) ∧
      (∀ q < n + 1, recOf (M0, n + 1, Lf, phi, "") p (k * (m / Lf)) q ∈
        (partStep mats M0 Lf phi r n).1) ∧
      (partStep mats M0 Lf phi r n).2 = _
    unfold partStep
    refine ⟨fun Fn h => Array.mem_push.mpr (Or.inl (i1 Fn h)), fun q hq => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h1 | h1
      · exact Array.mem_push.mpr (Or.inl (i2 q h1))
      · subst h1
        rw [i3]
        exact Array.mem_push.mpr (Or.inr rfl)
    · show r.2 + (mats.getD (M0 + n) {}).k * ((mats.getD (M0 + n) {}).m / Lf) = _
      rw [(hU n (Nat.lt_succ_self n)).1, (hU n (Nat.lt_succ_self n)).2, i3]
      ring

/-- What adding a table does: the old records are kept; each part has its record; the vector grows
by the table's length, which is not 0; the table is added at the end of the list, with the vector's
old length as its first entry. -/
theorem addAsk_spec {mats : Array TMat} {t t' : Tables} {a : Ask} {m k : ℕ}
    (hU : Uni mats a m k) (h : addAsk mats t a = some t') :
    (∀ Fn ∈ t.funs, Fn ∈ t'.funs) ∧
    (∀ q < a.2.1, recOf a t.p (k * (m / a.2.2.1)) q ∈ t'.funs) ∧
    t'.p = t.p + a.2.1 * (k * (m / a.2.2.1)) ∧ 0 < a.2.1 * (k * (m / a.2.2.1)) ∧
    t'.tab = t.tab ++ [(a.2.2.2.2, t.p, a.2.1 * (k * (m / a.2.2.1)))] := by
  obtain ⟨i1, i2, i3⟩ := parts_fold mats a.1 a.2.2.1 a.2.2.2.1 m k t.funs t.p a.2.1 hU
  unfold addAsk at h
  rw [addFun_eq] at h
  generalize (List.range a.2.1).foldl (partStep mats a.1 a.2.2.1 a.2.2.2.1) (t.funs, t.p) = r
    at i1 i2 i3 h
  by_cases hz : (r.2 == t.p) = true
  · rw [if_pos hz] at h
    cases h
  · rw [if_neg hz] at h
    have e := (Option.some.inj h).symm
    subst e
    have hne : r.2 ≠ t.p := fun e => hz (by rw [e]; exact beq_self_eq_true _)
    have hpos : 0 < a.2.1 * (k * (m / a.2.2.1)) := by omega
    refine ⟨i1, i2, i3, hpos, ?_⟩
    show t.tab ++ [(a.2.2.2.2, t.p, r.2 - t.p)] = _
    rw [i3, Nat.add_sub_cancel_left]

/-- No table is empty, each ends inside the vector, and no two begin at one entry. -/
structure WfT (t : Tables) : Prop where
  ends : ∀ e ∈ t.tab, 0 < e.2.2 ∧ e.2.1 + e.2.2 ≤ t.p
  uniq : ∀ e ∈ t.tab, ∀ e' ∈ t.tab, e.2.1 = e'.2.1 → e = e'

/-- The empty list of tables. -/
theorem wfT_empty : WfT {} :=
  ⟨fun _ h => absurd h (List.not_mem_nil), fun _ h => absurd h (List.not_mem_nil)⟩

/-- Adding a table keeps WfT. -/
theorem wfT_add {t t' : Tables} {nm : String} {len : ℕ} (hW : WfT t) (hp : t'.p = t.p + len)
    (hl : 0 < len) (ht : t'.tab = t.tab ++ [(nm, t.p, len)]) : WfT t' := by
  have mem : ∀ e, e ∈ t'.tab → e ∈ t.tab ∨ e = (nm, t.p, len) := by
    intro e he
    rw [ht, List.mem_append, List.mem_singleton] at he
    exact he
  refine ⟨fun e he => ?_, fun e he e' he' hs => ?_⟩
  · rcases mem e he with h1 | h1
    · have := hW.ends e h1
      omega
    · subst h1
      exact ⟨hl, by rw [hp]⟩
  · rcases mem e he with h1 | h1 <;> rcases mem e' he' with h2 | h2
    · exact hW.uniq e h1 e' h2 hs
    · subst h2
      have := hW.ends e h1
      have hs' : e.2.1 = t.p := hs
      omega
    · subst h1
      have := hW.ends e' h2
      have hs' : t.p = e'.2.1 := hs
      omega
    · rw [h1, h2]

/-- What adding a list of tables does. If every line's matrix has parts of one size: WfT is kept, so
are the old records and tables, the names are added in the list's order, and every line has its
table and the records of its parts. -/
theorem fold_spec (mats : Array TMat) : ∀ (asks : List Ask) (t t' : Tables),
    (∀ a ∈ asks, ∃ m k, Uni mats a m k) → WfT t → asks.foldlM (addAsk mats) t = some t' →
    WfT t' ∧ (∀ Fn ∈ t.funs, Fn ∈ t'.funs) ∧ (∀ e ∈ t.tab, e ∈ t'.tab) ∧
    t'.tab.map (·.1) = t.tab.map (·.1) ++ asks.map (·.2.2.2.2) ∧
    ∀ a ∈ asks, ∀ m k, Uni mats a m k → ∃ tb,
      (a.2.2.2.2, tb, a.2.1 * (k * (m / a.2.2.1))) ∈ t'.tab ∧
      ∀ q < a.2.1, recOf a tb (k * (m / a.2.2.1)) q ∈ t'.funs
  | [], t, t', _, hW, h => by
    have e : t' = t := (Option.some.inj h).symm
    subst e
    exact ⟨hW, fun _ h => h, fun _ h => h, by simp, fun a ha => absurd ha (List.not_mem_nil)⟩
  | a0 :: rest, t, t', hU, hW, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨t1, h1, h2⟩ := bind_some h
    obtain ⟨m0, k0, hU0⟩ := hU a0 List.mem_cons_self
    obtain ⟨s1, s2, s3, s4, s5⟩ := addAsk_spec hU0 h1
    obtain ⟨r1, r2, r3, r4, r5⟩ := fold_spec mats rest t1 t'
      (fun a ha => hU a (List.mem_cons_of_mem _ ha)) (wfT_add hW s3 s4 s5) h2
    refine ⟨r1, fun Fn hF => r2 Fn (s1 Fn hF), fun e he => r3 e ?_, ?_, fun a ha m k hUa => ?_⟩
    · rw [s5]
      exact List.mem_append_left _ he
    · rw [r4, s5]
      simp
    · rcases List.mem_cons.mp ha with e | ha'
      · subst e
        obtain ⟨u1, u2, -, -, u5⟩ := addAsk_spec hUa h1
        refine ⟨t.p, r3 _ ?_, fun q hq => r2 _ (u2 q hq)⟩
        rw [u5]
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      · exact r5 a ha' m k hUa

/-! ## The forms' name of an entry against the smallness test's -/

/-- In a list of tables with different names, a table is the first with its name. -/
theorem find_of_nodup : ∀ (tab : List (String × ℕ × ℕ)), (tab.map (·.1)).Nodup →
    ∀ e ∈ tab, tab.find? (fun x => x.1 == e.1) = some e
  | [], _, _, he => absurd he (List.not_mem_nil)
  | x :: xs, hn, e, he => by
    rw [List.map_cons, List.nodup_cons] at hn
    by_cases hx : x.1 = e.1
    · have hxe : e = x := by
        rcases List.mem_cons.mp he with h1 | h1
        · exact h1
        · exact absurd (hx ▸ List.mem_map_of_mem h1) hn.1
      subst hxe
      exact List.find?_cons_of_pos (by simp)
    · have he' : e ∈ xs := by
        rcases List.mem_cons.mp he with h1 | h1
        · exact absurd (by rw [h1]) hx
        · exact h1
      rw [List.find?_cons_of_neg (by simpa using hx)]
      exact find_of_nodup xs hn.2 e he'

/-- The two numberings of the entries of one table meet. t: the tables that the list asks leaves,
over the matrices of the smallness test's record tl. a: a line of the list whose parts have m rows
and k columns and are matrices of tl. If the first table with the line's name begins at tb, and some
table that begins at tb has more than e entries, then e is below the length of the line's table; the
record of the part e / n / k, n = m / Lf, is in the list of records; and the smallness test has the
place tb + e for that record's column e / n mod k and run e mod n. -/
theorem table_entry {tl : HTailF2} {asks : List Ask} {t : Tables}
    (hU : ∀ a ∈ asks, ∃ m k, Uni tl.mats a m k) (hn : (asks.map (·.2.2.2.2)).Nodup)
    (hf : asks.foldlM (addAsk tl.mats) {} = some t) {a : Ask} (ha : a ∈ asks) {m k : ℕ}
    (hUa : Uni tl.mats a m k) (hNM : a.1 + a.2.1 ≤ tl.NM) {tb e : ℕ}
    (hs : (t.tab.find? fun x => x.1 == a.2.2.2.2).map (·.2.1) = some tb)
    (hv : (t.tab.any fun x => x.2.1 == tb && decide (e < x.2.2)) = true) :
    e < a.2.1 * (k * (m / a.2.2.1)) ∧
    recOf a tb (k * (m / a.2.2.1)) (e / (m / a.2.2.1) / k) ∈ t.funs ∧
    tl.tabAt (recOf a tb (k * (m / a.2.2.1)) (e / (m / a.2.2.1) / k))
      (e / (m / a.2.2.1) % k) (e % (m / a.2.2.1)) = some (tb + e) := by
  obtain ⟨W, -, -, hnames, hall⟩ := fold_spec tl.mats asks {} t hU wfT_empty hf
  obtain ⟨tb0, hmem, hrec⟩ := hall a ha m k hUa
  have hnd : (t.tab.map (·.1)).Nodup := by
    rw [hnames]
    exact hn
  have hfind := find_of_nodup t.tab hnd _ hmem
  have htb : tb0 = tb := by
    rw [hfind] at hs
    exact Option.some.inj hs
  subst htb
  obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp hv
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hp
  have hxe := W.uniq x hx _ hmem hp.1
  have he : e < a.2.1 * (k * (m / a.2.2.1)) := by
    have h2 := hp.2
    rw [hxe] at h2
    exact h2
  obtain ⟨hq, -, -, -⟩ := entry_split he
  refine ⟨he, hrec _ hq, ?_⟩
  exact entry_tabAt tl a.2.2.2.1 he fun p hp' =>
    ⟨by omega, (hUa p hp').1, (hUa p hp').2⟩

/-! ## One table -/

section Read

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} {tl : HTailF2} {asks : List Ask}
  {t : Tables} {iU3 K3 : ℕ} {M : Mats K}

/-- A short table: runs of T rows. Entry e is the sum of the cells of feature e under the table's
weights. -/
theorem short_read (H : ∀ Fn ∈ t.funs, Holds ρ W tl iU3 K3 M Fn)
    (hU : ∀ a ∈ asks, ∃ m k, Uni tl.mats a m k) (hn : (asks.map (·.2.2.2.2)).Nodup)
    (hf : asks.foldlM (addAsk tl.mats) {} = some t) {a : Ask} (ha : a ∈ asks) {m k : ℕ}
    (hUa : Uni tl.mats a m k) (hNM : a.1 + a.2.1 ≤ tl.NM) {tb e : ℕ}
    (hs : (t.tab.find? fun x => x.1 == a.2.2.2.2).map (·.2.1) = some tb)
    (hv : (t.tab.any fun x => x.2.1 == tb && decide (e < x.2.2)) = true) :
    W.entry iU3 ((tb + e) / K3) ((tb + e) % K3) =
      ∑ i ∈ range a.2.2.1, ρ.val (a.2.2.2.1.getD i zeroE) *
        cellIn M a.1 k (m / a.2.2.1) a.2.2.1 e i := by
  obtain ⟨-, hm, ht⟩ := table_entry hU hn hf ha hUa hNM hs hv
  exact H _ hm _ _ _ ht

/-- The feature e S + r, r < S, in a matrix whose columns hold n S features: its column is that of
block e among blocks of which a column holds n, and its place in the column is (e mod n) S + r. -/
theorem block_split {S n e r : ℕ} (hr : r < S) :
    (e * S + r) / (n * S) = e / n ∧ (e * S + r) % (n * S) = e % n * S + r := by
  have hS : 0 < S := by omega
  have d1 : (e * S + r) / S = e := by
    rw [Nat.mul_comm, Nat.mul_add_div hS, Nat.div_eq_of_lt hr, Nat.add_zero]
  have d2 : (e * S + r) % S = r := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  constructor
  · rw [Nat.mul_comm n S, ← Nat.div_div_eq_div_mul, d1]
  · rw [Nat.mul_comm n S, Nat.mod_mul, d1, d2]
    ring

/-- A long table: runs of S T rows, the rows of a block of S features. Entry e is the sum of the
cells of the features e S + r, r < S, under the table's weights, which are numbered r T + i. -/
theorem long_read (H : ∀ Fn ∈ t.funs, Holds ρ W tl iU3 K3 M Fn)
    (hU : ∀ a ∈ asks, ∃ m k, Uni tl.mats a m k) (hn : (asks.map (·.2.2.2.2)).Nodup)
    (hf : asks.foldlM (addAsk tl.mats) {} = some t) {a : Ask} (ha : a ∈ asks) {m k : ℕ}
    (hUa : Uni tl.mats a m k) (hNM : a.1 + a.2.1 ≤ tl.NM) {S T : ℕ} (hL : a.2.2.1 = S * T)
    (hfc : m / T = m / (S * T) * S) {tb e : ℕ}
    (hs : (t.tab.find? fun x => x.1 == a.2.2.2.2).map (·.2.1) = some tb)
    (hv : (t.tab.any fun x => x.2.1 == tb && decide (e < x.2.2)) = true) :
    W.entry iU3 ((tb + e) / K3) ((tb + e) % K3) =
      ∑ r ∈ range S, ∑ i ∈ range T, ρ.val (a.2.2.2.1.getD (r * T + i) zeroE) *
        cellIn M a.1 k (m / T) T (e * S + r) i := by
  obtain ⟨-, hm, ht⟩ := table_entry hU hn hf ha hUa hNM hs hv
  rw [H _ hm _ _ _ ht]
  show ∑ j ∈ range a.2.2.1, ρ.val (a.2.2.2.1.getD j zeroE) *
    M (a.1 + e / (m / a.2.2.1) / k) (e % (m / a.2.2.1) * a.2.2.1 + j) (e / (m / a.2.2.1) % k) = _
  rw [hL, sum_blocks]
  refine sum_congr rfl fun r hr => sum_congr rfl fun i _ => ?_
  obtain ⟨b1, b2⟩ := block_split (n := m / (S * T)) (e := e) (mem_range.mp hr)
  unfold cellIn
  rw [hfc, b1, b2]
  have e2 : e % (m / (S * T)) * (S * T) + (r * T + i) = (e % (m / (S * T)) * S + r) * T + i := by
    ring
  rw [e2]

end Read

/-! ## The list of tablesOf -/

section Asks

open OnBytes.Model (eqTab longPhi longPoint lastOf cutLast)
open OnBytes.Model.Head (Heard Covered tablesOf costWeights zjOf ztOf callNo)

/-- The list of tablesOf, line by line. What the routine computes on the way stands here as letters:
two points ZV and YN, the two vectors phiC and rhoCv of the positions with a cost, the numbers qFC
and qROW of two calls, and the two vectors b0 and b1 of weights on the rows of bH. -/
def asksH (h : Model.Head.Shape) (L : HL) (x : Heard) (ZV YN phiC rhoCv : Array E) (qFC qROW : ℕ)
    (b0 b1 : Array E) : List Ask :=
  [(0, h.NHf, 2 ^ h.la, longPhi x.Zl h.ls h.lt, "hf@Z"),
   (0, h.NHf, 2 ^ h.la, (Array.range (2 ^ h.la)).map fun i => phiC.getD (i % h.T) zeroE, "hf@phiZ"),
   (h.NHf + 1 + 1 + 1, 1, 2 ^ h.la, longPhi ZV h.ls h.lt, "xbL@Z_V"),
   (h.NHf + 1 + 1 + 1, 1, 2 ^ h.la, longPhi YN h.ls h.lt, "xbL@Y_N"),
   (h.NHf, 1, h.T, eqTab (ztOf h L x.g1 qFC), "hd@zt_FC"),
   (h.NHf, 1, h.T, eqTab x.tH.r, "hd@r_H"),
   (h.NHf + 1, 1, h.T, eqTab (ztOf h L x.g1 qROW), "hr@zt_ROW"),
   (h.NHf + 1, 1, h.T, eqTab x.PV, "hr@P_V"),
   (h.NHf + 1, 1, h.T, eqTab x.tV.r, "hr@r_tV"),
   (h.NHf + 1, 1, h.T, eqTab x.tN.r, "hr@rt_N"),
   (h.NHf + 1, 1, h.T, phiC, "hr@phiC"),
   (h.NHf + 1, 1, h.T, rhoCv, "hr@rhoC"),
   (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, b0, "bH-bits-0"),
   (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, b1, "bH-bits-1"),
   (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, Model.Forest.phiP h.lmbH, "bH-pin")]

/-- The names of the fifteen tables differ. -/
theorem asksH_names (h : Model.Head.Shape) (L : HL) (x : Heard) (ZV YN phiC rhoCv : Array E)
    (qFC qROW : ℕ) (b0 b1 : Array E) :
    ((asksH h L x ZV YN phiC rhoCv qFC qROW b0 b1).map (·.2.2.2.2)).Nodup := by
  have e : (asksH h L x ZV YN phiC rhoCv qFC qROW b0 b1).map (·.2.2.2.2) =
      ["hf@Z", "hf@phiZ", "xbL@Z_V", "xbL@Y_N", "hd@zt_FC", "hd@r_H", "hr@zt_ROW", "hr@P_V",
        "hr@r_tV", "hr@rt_N", "hr@phiC", "hr@rhoC", "bH-bits-0", "bH-bits-1", "bH-pin"] := rfl
  rw [e]
  decide

/-- What tablesOf returns. If the routine succeeds, the values that it computes on the way are
there, a block has S2 T rows, the point YN has one coordinate for each bit of a block's row, and the
tables are what addFun makes of the list asksH, line after line, from the empty list, over the
matrices of the plan's record. -/
theorem tables_of_ok {h : Model.Head.Shape} {L : HL} {hp : HPlanH2} {cov : Covered} {x : Heard}
    {F G : Fork} {C D : Ctx} {t : Tables} (hk : Ok (tablesOf h L hp cov x) F C t G D) :
    ∃ ZV lowN qFC qROW b0 b1, lastOf x.wpl.r h.la = .ok ZV ∧
      cutLast (zjOf L x.g1 x.qN) h.ls = .ok lowN ∧ callNo L "CNF" = some qFC ∧
      callNo L "ROW" = some qROW ∧ h.la = h.ls + h.lt ∧
      (longPoint lowN.2 x.tN.r).size = h.la ∧
      (asksH h L x ZV (longPoint lowN.2 x.tN.r) (costWeights cov (ztOf h L x.g1 x.qH)).1
        (costWeights cov (ztOf h L x.g1 x.qH)).2.2 qFC qROW b0 b1).foldlM
          (addAsk hp.tl.mats) {} = some t := by
  unfold Model.Head.tablesOf at hk
  obtain ⟨u1, F1, C1, -, hk⟩ := (ok_bind _ _ _ _ _ _ _).mp hk
  obtain ⟨ZV, F2, C2, k2, hk⟩ := (ok_bind _ _ _ _ _ _ _).mp hk
  obtain ⟨lowN, F3, C3, k3, hk⟩ := (ok_bind _ _ _ _ _ _ _).mp hk
  obtain ⟨u4, F4, C4, k4, hk⟩ := (ok_bind _ _ _ _ _ _ _).mp hk
  obtain ⟨qFC, F5, C5, k5, hk⟩ := (ok_bind _ _ _ _ _ _ _).mp hk
  obtain ⟨qROW, F6, C6, k6, hk⟩ := (ok_bind _ _ _ _ _ _ _).mp hk
  obtain ⟨b0, F7, C7, -, hk⟩ := (ok_bind _ _ _ _ _ _ _).mp hk
  obtain ⟨b1, F8, C8, -, hk⟩ := (ok_bind _ _ _ _ _ _ _).mp hk
  obtain ⟨t1, F9, C9, k9, hk⟩ := (ok_bind _ _ _ _ _ _ _).mp hk
  obtain ⟨u10, F10, C10, -, hk⟩ := (ok_bind _ _ _ _ _ _ _).mp hk
  obtain ⟨rfl, -, -⟩ := (ok_pure _ _ _ _ _ _).mp hk
  have j2 := ((held_ok _ _ _ _).mp ((ok_lift _ _ _ _ _ _).mp k2).1).1
  have j3 := ((held_ok _ _ _ _).mp ((ok_lift _ _ _ _ _ _).mp k3).1).1
  have j4 := ((mustAs_ok _ _ _ _ _).mp ((ok_lift _ _ _ _ _ _).mp k4).1).1
  have j5 := ((getAs_ok _ _ _ _ _).mp ((ok_lift _ _ _ _ _ _).mp k5).1).1
  have j6 := ((getAs_ok _ _ _ _ _).mp ((ok_lift _ _ _ _ _ _).mp k6).1).1
  have j9 := ((getAs_ok _ _ _ _ _).mp ((ok_lift _ _ _ _ _ _).mp k9).1).1
  simp only [Bool.and_eq_true, beq_iff_eq] at j4
  exact ⟨ZV, lowN, qFC, qROW, b0, b1, j2, j3, j5, j6, j4.2, j4.1, j9⟩

end Asks

/-! ## What the reads hold -/

section True

open OnBytes.Model (eqTab longPhi longPoint lastOf cutLast)
open OnBytes.Model.Head (tablesOf costWeights zjOf ztOf callNo)

variable {K : Type} [Field K] (ρ : Reading K) (W : World K)

/-- The table with the name nm is a short table with the weights phi on the cells cell: each entry e
that the forms can name holds the sum, over the positions, of weight times the cell of feature e.
K3: the number of columns of the array that holds the reads. -/
def SumShort (R : Model.Head.Run) (K3 : ℕ) (nm : String) (phi : Array E) (cell : ℕ → ℕ → K) :
    Prop :=
  ∀ tb, Starts R nm tb → ∀ e, Valid R tb e →
    rdW W R.iU3 K3 (tb + e) = ∑ i ∈ range R.h.T, ρ.val (phi.getD i zeroE) * cell e i

/-- The table with the name nm is a long table with the weights phi on the cells cell: each entry e
that the forms can name holds the sum, over the S2 features of block e and the positions, of weight
times cell. The weight of feature e S2 + r at position i has the number r T + i. -/
def SumLong (R : Model.Head.Run) (K3 : ℕ) (nm : String) (phi : Array E) (cell : ℕ → ℕ → K) : Prop :=
  ∀ tb, Starts R nm tb → ∀ e, Valid R tb e →
    rdW W R.iU3 K3 (tb + e) = ∑ r ∈ range R.h.S2, ∑ i ∈ range R.h.T,
      ρ.val (phi.getD (r * R.h.T + i) zeroE) * cell (e * R.h.S2 + r) i

/-- The reads are true of the cells t: each of the twelve tables on hf, the stream, hd and hr holds
sums of cells of t under the weights that tablesOf gives the table. -/
structure TrueH (R : Model.Head.Run) (K3 : ℕ) (t : Inst.Model.Head.Cells K) : Prop where
  hfZ : SumLong ρ W R K3 "hf@Z" (longPhi R.x.Zl R.h.ls R.h.lt) t.hf
  hfPhiZ : SumLong ρ W R K3 "hf@phiZ"
    ((Array.range (2 ^ R.h.la)).map fun i =>
      (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).1.getD (i % R.h.T) zeroE) t.hf
  xZV : ∀ ZV, lastOf R.x.wpl.r R.h.la = .ok ZV →
    SumLong ρ W R K3 "xbL@Z_V" (longPhi ZV R.h.ls R.h.lt) t.x
  xYN : ∀ lowN, cutLast (zjOf R.L R.x.g1 R.x.qN) R.h.ls = .ok lowN →
    SumLong ρ W R K3 "xbL@Y_N" (longPhi (longPoint lowN.2 R.x.tN.r) R.h.ls R.h.lt) t.x
  hdFC : ∀ q, callNo R.L "CNF" = some q →
    SumShort ρ W R K3 "hd@zt_FC" (eqTab (ztOf R.h R.L R.x.g1 q)) t.hd
  hdRH : SumShort ρ W R K3 "hd@r_H" (eqTab R.x.tH.r) t.hd
  hrROW : ∀ q, callNo R.L "ROW" = some q →
    SumShort ρ W R K3 "hr@zt_ROW" (eqTab (ztOf R.h R.L R.x.g1 q)) t.hr
  hrPV : SumShort ρ W R K3 "hr@P_V" (eqTab R.x.PV) t.hr
  hrTV : SumShort ρ W R K3 "hr@r_tV" (eqTab R.x.tV.r) t.hr
  hrTN : SumShort ρ W R K3 "hr@rt_N" (eqTab R.x.tN.r) t.hr
  hrPhiC : SumShort ρ W R K3 "hr@phiC" (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).1 t.hr
  hrRhoC : SumShort ρ W R K3 "hr@rhoC" (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).2.2 t.hr

/-- The member with the number j of a list is a member. -/
theorem mem_drop {α : Type} {a : α} : ∀ (j : ℕ) (l : List α), (l.drop j).head? = some a → a ∈ l
  | 0, [], h => by simp at h
  | 0, x :: xs, h => by
    have e : x = a := Option.some.inj h
    subst e
    exact List.mem_cons_self
  | j + 1, [], h => by simp at h
  | j + 1, x :: xs, h => List.mem_cons_of_mem _ (mem_drop j xs h)

/-- A matrix in one part has parts of one size. -/
theorem uni_one (mats : Array TMat) (a : Ask) (h1 : a.2.1 = 1) :
    Uni mats a (mats.getD a.1 {}).m (mats.getD a.1 {}).k := by
  intro q hq
  have e : q = 0 := by omega
  subst e
  exact ⟨rfl, rfl⟩

/-- The rows of a block, and the blocks of a column, at the full size. -/
theorem block_known {la S T m : ℕ} (hla : la = 16) (hS : S = 64) (hT : T = 1024)
    (hm : m = 65536) : 2 ^ la = S * T ∧ m / T = m / (S * T) * S := by
  subst hla hS hT hm
  decide

variable {ρ W}

/-- **If every record of the list of tables holds what it says of its matrix, the reads are true of
the cells that are read in the matrices' entries.** R: a run whose plan has the list of matrices of
the plan H0 that planH2 returns for the run's numbers, layout and stream, and whose tables are what
tablesOf returns. tl: a record of the smallness test with the plan's list of matrices. M: the
entries of these matrices. -/
theorem trueH_of_holds {R : Model.Head.Run} {g : Settings} {O : Owner} {NGr lkW : ℕ}
    {H0 : HPlanH2} (hpl : planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM) (hF : FullH R.h)
    (N : NumH R.h R.L) (Bd : BorderH R.b) {F G : Fork} {C D : Ctx}
    (ht : Ok (tablesOf R.h R.L R.hp R.cov R.x) F C R.t G D) {tl : HTailF2}
    (hm : tl.mats = R.hp.tl.mats) (hNM : tl.NM = R.hp.tl.NM) {K3 : ℕ} {M : Mats K}
    (H : ∀ Fn ∈ R.t.funs, Holds ρ W tl R.iU3 K3 M Fn) :
    TrueH ρ W R K3 (cellsH R.h R.L R.b M) := by
  obtain ⟨sid, p1, p2⟩ := planH2_mats hpl
  obtain ⟨z0, zf, zD1, zD2, zR1, zR2, zX1, zX2⟩ := matsH_at R.L R.b (1 + NGr) sid N.NHf
  rw [← p1, ← hm0, ← hm] at z0 zf zD1 zD2 zR1 zR2 zX1 zX2
  have hN8 : tl.NM = 8 := by rw [hNM, hN0, p2, ← p1, ← hm0, ← hm, z0]
  obtain ⟨ZV, lowN, qFC, qROW, b0, b1, j2, j3, j5, j6, -, -, hf⟩ := tables_of_ok ht
  rw [← hm] at hf
  have hn := asksH_names R.h R.L R.x ZV (longPoint lowN.2 R.x.tN.r)
    (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).1
    (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).2.2 qFC qROW b0 b1
  have hS : R.h.S2 = 64 := pow_known (a := 6) (sub_known hF.la hF.lt (by decide)) (by decide)
  have uF : ∀ (phi : Array E) (nm : String),
      Uni tl.mats (0, R.h.NHf, 2 ^ R.h.la, phi, nm) R.L.m R.L.k := by
    intro phi nm q hq
    have hq' : q < 4 := by
      have h0 : q < R.h.NHf := hq
      rw [N.NHf] at h0
      exact h0
    have e := zf q hq'
    rw [← Nat.zero_add q] at e
    exact e
  have uX : ∀ (phi : Array E) (nm : String),
      Uni tl.mats (R.h.NHf + 1 + 1 + 1, 1, 2 ^ R.h.la, phi, nm) R.b.mxb R.b.kxb := by
    intro phi nm q hq
    have e : q = 0 := by
      have h0 : q < 1 := hq
      omega
    subst e
    show (tl.mats.getD (R.h.NHf + 1 + 1 + 1 + 0) {}).m = _ ∧
      (tl.mats.getD (R.h.NHf + 1 + 1 + 1 + 0) {}).k = _
    rw [N.NHf]
    exact ⟨zX1, zX2⟩
  have uD : ∀ (phi : Array E) (nm : String),
      Uni tl.mats (R.h.NHf, 1, R.h.T, phi, nm) R.L.mD R.L.kD := by
    intro phi nm q hq
    have e : q = 0 := by
      have h0 : q < 1 := hq
      omega
    subst e
    show (tl.mats.getD (R.h.NHf + 0) {}).m = _ ∧ (tl.mats.getD (R.h.NHf + 0) {}).k = _
    rw [N.NHf]
    exact ⟨zD1, zD2⟩
  have uR : ∀ (phi : Array E) (nm : String),
      Uni tl.mats (R.h.NHf + 1, 1, R.h.T, phi, nm) R.L.mR R.L.kR := by
    intro phi nm q hq
    have e : q = 0 := by
      have h0 : q < 1 := hq
      omega
    subst e
    show (tl.mats.getD (R.h.NHf + 1 + 0) {}).m = _ ∧ (tl.mats.getD (R.h.NHf + 1 + 0) {}).k = _
    rw [N.NHf]
    exact ⟨zR1, zR2⟩
  have hU : ∀ a ∈ asksH R.h R.L R.x ZV (longPoint lowN.2 R.x.tN.r)
      (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).1
      (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).2.2 qFC qROW b0 b1,
      ∃ m k, Uni tl.mats a m k := by
    intro a ha
    unfold asksH at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact ⟨_, _, uF _ _⟩
    · exact ⟨_, _, uF _ _⟩
    all_goals exact ⟨_, _, uni_one _ _ rfl⟩
  have h4 := N.NHf
  have nF : 0 + R.h.NHf ≤ tl.NM := by omega
  have nX : R.h.NHf + 1 + 1 + 1 + 1 ≤ tl.NM := by omega
  have nD : R.h.NHf + 1 ≤ tl.NM := by omega
  have nR : R.h.NHf + 1 + 1 ≤ tl.NM := by omega
  obtain ⟨bF1, bF2⟩ := block_known hF.la hS N.T N.m
  obtain ⟨-, bX2⟩ := block_known hF.la hS N.T Bd.mxb
  have xcell : ∀ φ i, cellIn M (R.h.NHf + 1 + 1 + 1) R.b.kxb (R.b.mxb / R.h.T) R.h.T φ i =
      (cellsH R.h R.L R.b M).x φ i := by
    intro φ i
    show _ = cellIn M (R.h.NHf + 3) R.b.kxb (R.b.mxb / R.h.T) R.h.T
      (R.b.cell (φ / R.h.d) (φ % R.h.d)) i
    rw [(placeIn_x N Bd φ i).1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tb hs e hv
    exact long_read H hU hn hf (a := (0, R.h.NHf, 2 ^ R.h.la, longPhi R.x.Zl R.h.ls R.h.lt, "hf@Z"))
      (mem_drop 0 _ rfl) (uF _ _) nF bF1 bF2 hs hv
  · intro tb hs e hv
    exact long_read H hU hn hf
      (a := (0, R.h.NHf, 2 ^ R.h.la, (Array.range (2 ^ R.h.la)).map fun i =>
        (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).1.getD (i % R.h.T) zeroE, "hf@phiZ"))
      (mem_drop 1 _ rfl) (uF _ _) nF bF1 bF2 hs hv
  · intro ZV' hZ
    have e1 : ZV' = ZV := Except.ok.inj (hZ.symm.trans j2)
    rw [e1]
    intro tb hs e hv
    rw [show rdW W R.iU3 K3 (tb + e) = _ from long_read H hU hn hf
      (a := (R.h.NHf + 1 + 1 + 1, 1, 2 ^ R.h.la, longPhi ZV R.h.ls R.h.lt, "xbL@Z_V"))
      (mem_drop 2 _ rfl) (uX _ _) nX bF1 bX2 hs hv]
    exact sum_congr rfl fun r _ => sum_congr rfl fun i _ => by rw [xcell]
  · intro lowN' hl
    have e1 : lowN' = lowN := Except.ok.inj (hl.symm.trans j3)
    rw [e1]
    intro tb hs e hv
    rw [show rdW W R.iU3 K3 (tb + e) = _ from long_read H hU hn hf
      (a := (R.h.NHf + 1 + 1 + 1, 1, 2 ^ R.h.la,
        longPhi (longPoint lowN.2 R.x.tN.r) R.h.ls R.h.lt, "xbL@Y_N"))
      (mem_drop 3 _ rfl) (uX _ _) nX bF1 bX2 hs hv]
    exact sum_congr rfl fun r _ => sum_congr rfl fun i _ => by rw [xcell]
  · intro q hq
    have e1 : q = qFC := Option.some.inj (hq.symm.trans j5)
    rw [e1]
    intro tb hs e hv
    exact short_read H hU hn hf
      (a := (R.h.NHf, 1, R.h.T, eqTab (ztOf R.h R.L R.x.g1 qFC), "hd@zt_FC"))
      (mem_drop 4 _ rfl) (uD _ _) nD hs hv
  · intro tb hs e hv
    exact short_read H hU hn hf (a := (R.h.NHf, 1, R.h.T, eqTab R.x.tH.r, "hd@r_H"))
      (mem_drop 5 _ rfl) (uD _ _) nD hs hv
  · intro q hq
    have e1 : q = qROW := Option.some.inj (hq.symm.trans j6)
    rw [e1]
    intro tb hs e hv
    exact short_read H hU hn hf
      (a := (R.h.NHf + 1, 1, R.h.T, eqTab (ztOf R.h R.L R.x.g1 qROW), "hr@zt_ROW"))
      (mem_drop 6 _ rfl) (uR _ _) nR hs hv
  · intro tb hs e hv
    exact short_read H hU hn hf (a := (R.h.NHf + 1, 1, R.h.T, eqTab R.x.PV, "hr@P_V"))
      (mem_drop 7 _ rfl) (uR _ _) nR hs hv
  · intro tb hs e hv
    exact short_read H hU hn hf (a := (R.h.NHf + 1, 1, R.h.T, eqTab R.x.tV.r, "hr@r_tV"))
      (mem_drop 8 _ rfl) (uR _ _) nR hs hv
  · intro tb hs e hv
    exact short_read H hU hn hf (a := (R.h.NHf + 1, 1, R.h.T, eqTab R.x.tN.r, "hr@rt_N"))
      (mem_drop 9 _ rfl) (uR _ _) nR hs hv
  · intro tb hs e hv
    exact short_read H hU hn hf
      (a := (R.h.NHf + 1, 1, R.h.T, (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).1, "hr@phiC"))
      (mem_drop 10 _ rfl) (uR _ _) nR hs hv
  · intro tb hs e hv
    exact short_read H hU hn hf
      (a := (R.h.NHf + 1, 1, R.h.T, (costWeights R.cov (ztOf R.h R.L R.x.g1 R.x.qH)).2.2,
        "hr@rhoC"))
      (mem_drop 11 _ rfl) (uR _ _) nR hs hv

/-- The parts of a run are the verifier's own results, as its check of the head's sub-proof puts
them together (runForkHidH2, OnBytes/Model/Head.lean): the layout is what layout returns for the
run's numbers; the stream's record is that of a layers' layout y; the plan has the list of matrices
of the plan H0 that planH2 returns; the array of the reads is the plan's; the tables are what
tablesOf returns. The run's plan is not asked to be H0 itself: the verifier's public part hands on
H0 with one other field rewritten (publicOf, OnBytes/Model/VerifyPublic.lean; madeH_trim). -/
structure MadeH (R : Model.Head.Run) (tau : Array OnBytes.F) (y : Model.Layer.Lay) (g : Settings)
    (O : Owner) (NGr lkW : ℕ) (H0 : HPlanH2) (F G : Fork) (C D : Ctx) : Prop where
  L : Model.Head.layout R.h tau = .ok R.L
  b : R.b = Model.Verify.borderOf y
  hp : planH2 g R.h R.L R.b O NGr lkW = .ok H0
  mats : R.hp.tl.mats = H0.tl.mats
  NM : R.hp.tl.NM = H0.tl.NM
  iU3 : R.hp.tl.ix.U.getD 2 none = some R.iU3
  t : Ok (tablesOf R.h R.L R.hp R.cov R.x) F C R.t G D

/-- The plan that the verifier's public part hands on has the record of the smallness test of the
plan that planH2 returned. -/
theorem madeH_trim (H0 : HPlanH2) :
    ({ H0 with Fp := H0.Fp.trimL } : HPlanH2).tl = H0.tl := rfl

/-- The same for a run whose parts are the verifier's own results, at the sizes at which the
library's head is written. The proof does not read the field iU3: the array's number is only a name
under which Holds and the forms find the reads. -/
theorem trueH_of_made {R : Model.Head.Run} {tau : Array OnBytes.F} {hy : Model.Layer.Shape}
    {pc : List (List String)} {y : Model.Layer.Lay} {g : Settings} {O : Owner} {NGr lkW : ℕ}
    {H0 : HPlanH2} {F G : Fork} {C D : Ctx} (A : MadeH R tau y g O NGr lkW H0 F G C D)
    (hF : FullH R.h)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy Inst.Model.All.DF)
    (Z2 : Sized2 hy Inst.Model.All.DF) {tl : HTailF2} (hm : tl.mats = R.hp.tl.mats)
    (hNM : tl.NM = R.hp.tl.NM) {K3 : ℕ} {M : Mats K}
    (H : ∀ Fn ∈ R.t.funs, Holds ρ W tl R.iU3 K3 M Fn) :
    TrueH ρ W R K3 (cellsH R.h R.L (Model.Verify.borderOf y) M) := by
  have Bd : BorderH R.b := by
    rw [A.b]
    exact borderH_of_layout hl S Z Z2
  have T := trueH_of_holds A.hp A.mats A.NM hF (numH_of_layout hF A.L) Bd A.t hm hNM H
  rw [A.b] at T
  exact T

end True

/-! ## The same at points -/

section Points

open OnBytes.Model (eqTab longPhi)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K}

/-- A long table whose weights the verifier makes from a point Z of ls + lt coordinates is true at
the point whose feature part is the first ls coordinates of Z and whose position part is the last
lt, in the sense of Johnson/Road/HeadLines.lean. -/
theorem longAt_of_sum {R : Model.Head.Run} {K3 : ℕ} {nm : String} {Z : Array E} {c : ℕ → ℕ → K}
    (hs : Z.size = R.h.ls + R.h.lt) (h : SumLong ρ W R K3 nm (longPhi Z R.h.ls R.h.lt) c) :
    LongAt W R K3 nm R.h.ls R.h.lt (pt ρ Z) (fun j => pt ρ Z (R.h.ls + j)) c := by
  intro tb hst b hv
  rw [h tb hst b hv]
  show ∑ r ∈ range (2 ^ R.h.ls), ∑ i ∈ range (2 ^ R.h.lt),
    ρ.val ((longPhi Z R.h.ls R.h.lt).getD (r * 2 ^ R.h.lt + i) zeroE) *
      c (b * 2 ^ R.h.ls + r) i = _
  unfold Blocks.ext
  refine sum_congr rfl fun r hr => ?_
  rw [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [longPhi_value ρ hs (mem_range.mp hr) (mem_range.mp hi)]
  ring

/-- A short table whose weights are the equality weights of a point zt of lt coordinates is true at
zt, in the sense of Johnson/Road/HeadLines.lean. -/
theorem shortAt_of_sum {R : Model.Head.Run} {K3 : ℕ} {nm : String} {zt : Array E} {c : ℕ → ℕ → K}
    (hz : zt.size = R.h.lt) (h : SumShort ρ W R K3 nm (eqTab zt) c) :
    ShortAt W R K3 nm R.h.lt (pt ρ zt) c := by
  intro tb hst φ hv
  rw [h tb hst φ hv]
  show ∑ i ∈ range (2 ^ R.h.lt), ρ.val ((eqTab zt).getD i zeroE) * c φ i = _
  unfold Blocks.ext
  refine sum_congr rfl fun i hi => ?_
  rw [eqTab_value ρ zt i (by rw [hz]; exact mem_range.mp hi), hz]

/-- The stream's table at the point of the sum of squares is true at that point: its length follows
from tests that tablesOf makes. -/
theorem xZV_point {R : Model.Head.Run} {K3 : ℕ} {t : Inst.Model.Head.Cells K}
    (T : TrueH ρ W R K3 t) {F G : Fork} {C D : Ctx}
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F C R.t G D) {ZV : Array E}
    (hZ : Model.lastOf R.x.wpl.r R.h.la = .ok ZV) :
    LongAt W R K3 "xbL@Z_V" R.h.ls R.h.lt (pt ρ ZV) (fun j => pt ρ ZV (R.h.ls + j)) t.x := by
  obtain ⟨_, _, _, _, _, _, -, -, -, -, hla, -, -⟩ := tables_of_ok ht
  exact longAt_of_sum (by rw [size_last hZ, hla]) (T.xZV ZV hZ)

/-- The stream's table at the point of the stream times the reciprocal is true at that point. -/
theorem xYN_point {R : Model.Head.Run} {K3 : ℕ} {t : Inst.Model.Head.Cells K}
    (T : TrueH ρ W R K3 t) {F G : Fork} {C D : Ctx}
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F C R.t G D) {lowN : Array E × Array E}
    (hl : Model.cutLast (Model.Head.zjOf R.L R.x.g1 R.x.qN) R.h.ls = .ok lowN) :
    LongAt W R K3 "xbL@Y_N" R.h.ls R.h.lt (pt ρ (Model.longPoint lowN.2 R.x.tN.r))
      (fun j => pt ρ (Model.longPoint lowN.2 R.x.tN.r) (R.h.ls + j)) t.x := by
  obtain ⟨_, lowN0, _, _, _, _, -, j3, -, -, hla, hY, -⟩ := tables_of_ok ht
  have e1 : lowN0 = lowN := Except.ok.inj (j3.symm.trans hl)
  rw [e1] at hY
  exact longAt_of_sum (by rw [hY, hla]) (T.xYN lowN hl)

/-- The hypothesis LentH of Johnson/Road/HeadPlace.lean can be met: by two lists in which every
matrix is one and the same. This shows no more than that the hypothesis is not empty. -/
theorem lentH_same {K' : Type} (h : Model.Head.Shape) (y : Model.Layer.Lay) (X : ℕ → ℕ → K') :
    LentH h y (fun _ r c => X r c) (fun _ r c => X r c) := fun _ _ _ _ => rfl

end Points

#print axioms planH2_mats
#print axioms matsH_at
#print axioms fold_spec
#print axioms table_entry
#print axioms short_read
#print axioms long_read
#print axioms tables_of_ok
#print axioms trueH_of_holds
#print axioms trueH_of_made
#print axioms longAt_of_sum
#print axioms shortAt_of_sum
#print axioms xZV_point
#print axioms xYN_point

end OnBytes.Road.Hd
