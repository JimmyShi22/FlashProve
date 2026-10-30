-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadLedger.lean: the claims on the ledger of the output head's final normalisation, and
their values on cells.

If a value of the residual stream has five limbs, the check of the output head's sub-proof adds 23
claims on the ledger of the final normalisation (claimLedger in OnBytes/Model/Head.lean). Two tie
the products' sumcheck to its slots. The other 21 are added by claimLedger5: four on the end values
of that sumcheck, nine lines of carries, and eight lines on the square root and the reciprocal. The
library has 17 identities at each position (Ledger.idn in Inst/Model/Common/Ledger.lean; for the
head Head.N.idn in Inst/Model/Head/TraceN.lean and Cm.Plain.idn in Cm/Head.lean). This file states
in what sense the last 17 claims are the 17 identities.

How to read the statements. The routine reads the first 99 cells of the head's row twice, in two
tables of the reads: one for the four claims, one for the 17. In a world where each entry of the
second table holds its feature's cells, summed over the positions under the equality weights of a
point u (ShortAt in Johnson/Road/HeadLines.lean), the value of form number k is the library's
identity number k with letters for the products (Ledger.idnP), taken at the extensions of the bytes
at u, at what nine slots hold in the place of the sums W_s, and at what seven slots hold in the
place of the products. If the nine slots hold the extensions of the W_s and the seven slots the
extensions of the products, it is the extension, at u, of the library's identity number k. "A form
is worth x" means: its value in the world is x.

Main definitions: cellAt, RowOf (a row is read in a table); ledEnds, carry, ledCarries, prSlots,
ledTail (the 21 forms, in the verifier's own functions); ledFirst.
Main theorems: lins_cons_some, lins_one, lins_append_some; ok_lins_range, ok_lins_array (loops that
add claims); ok_row5At; ok_claimLedger5 (the routine adds these 21 claims, in this order, and does
nothing else to the state); ok_claimLedger (the routine that calls it); ledger_length_17, _21, _23;
RowOf.bytes, RowOf.bytesDv; ledger_idnP, ledger_idn, ledger_idn_held (the values); ledger_idn_ref,
ledger_idn_plain (the same in the library's names); ledger_ends (the four claims on end values);
foldSlots_value, ledFirst_value, productsShown_value; row_R_cells; ShortAt.of_entry,
slots_witness, ledger_hyps_meet.

What is not claimed.
- Every theorem on a routine begins "if the routine succeeds". None says that it does, and no run
  here shows a state from which it does. No refusal is named, and no converse is stated.
- Nothing is said about when a world is true, or about what the slots hold. ledger_hyps_meet starts
  from a world with one true table. That such a world exists, and that the two tables can be true in
  one world, is not shown here.
- ledger_idn_ref and ledger_idn_plain have the library's names on the right. They do not tie the
  number of positions 2^lt to the library's 1,024, the point u to the verifier's point, the three
  numbers npOf R.h to the library's, or the field K to the ring in which the library's relation
  reads its identities.
- That an extension vanishes at one point does not say that the identity holds at a position.
- Nothing is said about what a verifier's acceptance shows. The program does not import this file.
-/
import Johnson.Road.HeadLines
import Johnson.Road.HeadLedgerLin

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open OnBytes.Model (Reading World Aff Fork SubM LedK Row5 row5 ledCarry5 ledLines5)
open Inst.Model (NormPar)
open HeadSizes (Sizes)

/-! ## Lists of claims -/

/-- A claim, and then a list of claims. -/
theorem lins_cons (F : Fork) (f : Aff) (l : List Aff) :
    F.lins (f :: l) = (F.lin f).bind fun G => G.lins l := by
  unfold Fork.lins
  rw [List.foldlM_cons]
  rfl

/-- A claim that is added, and then a list of claims that is added. -/
theorem lins_cons_some {F F1 G : Fork} {f : Aff} {l : List Aff} (h1 : F.lin f = some F1)
    (h2 : F1.lins l = some G) : F.lins (f :: l) = some G := by
  have e := lins_cons F f l
  rw [h1] at e
  exact e.trans h2

/-- One claim. -/
theorem lins_one {F G : Fork} {f : Aff} (h : F.lin f = some G) : F.lins [f] = some G :=
  lins_cons_some h rfl

/-- Two lists of claims that are added, one after the other. -/
theorem lins_append_some {F F1 G : Fork} {l1 l2 : List Aff} (h1 : F.lins l1 = some F1)
    (h2 : F1.lins l2 = some G) : F.lins (l1 ++ l2) = some G := by
  have e := lins_append F l1 l2
  rw [h1] at e
  exact e.trans h2

/-- A loop over the numbers below n that adds the claim g s at the number s adds the list of these
claims, and leaves the context. -/
theorem ok_lins_range (g : ℕ → Aff) (n : ℕ) {F G : Fork} {C D : Ctx} {u : PUnit}
    (h : Ok (forIn [:n] PUnit.unit fun s _ =>
      SubM.lin (g s) >>= fun _ => pure (ForInStep.yield PUnit.unit)) F C u G D) :
    F.lins ((List.range n).map g) = some G ∧ D = C := by
  refine ok_forIn_range n _
    (fun x _ F' C' => F.lins ((List.range x).map g) = some F' ∧ C' = C) ?_ ?_ h
  · rintro x b F1 C1 r F2 C2 _ ⟨hl, hc⟩ hr
    try dsimp only at hr
    rw [ok_bind] at hr
    obtain ⟨_, F3, C3, h1, h2⟩ := hr
    rw [ok_lin] at h1
    rw [ok_pure] at h2
    obtain ⟨e1, e2, e3⟩ := h2
    refine ⟨PUnit.unit, e1, ?_, e3.trans (h1.2.trans hc)⟩
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, e2]
    exact lins_append_some hl (lins_one h1.1)
  · exact ⟨rfl, rfl⟩

/-- A loop over a list that adds each member as a claim. -/
theorem ok_lins_list : ∀ (l : List Aff) {F G : Fork} {C D : Ctx} {u : PUnit},
    Ok (forIn l PUnit.unit fun o _ =>
      SubM.lin o >>= fun _ => pure (ForInStep.yield PUnit.unit)) F C u G D →
    F.lins l = some G ∧ D = C
  | [], F, G, C, D, u, h => by
    rw [List.forIn_nil, ok_pure] at h
    obtain ⟨_, e2, e3⟩ := h
    rw [e2]
    exact ⟨rfl, e3⟩
  | o :: l, F, G, C, D, u, h => by
    rw [List.forIn_cons, ok_bind] at h
    obtain ⟨r, F1, C1, h1, h2⟩ := h
    rw [ok_bind] at h1
    obtain ⟨_, F2, C2, h3, h4⟩ := h1
    rw [ok_lin] at h3
    rw [ok_pure] at h4
    obtain ⟨e1, e2, e3⟩ := h4
    rw [e1, e2, e3] at h2
    obtain ⟨i1, i2⟩ := ok_lins_list l h2
    exact ⟨lins_cons_some h3.1 i1, i2.trans h3.2⟩

/-- A loop over an array that adds each member as a claim. -/
theorem ok_lins_array (a : Array Aff) {F G : Fork} {C D : Ctx} {u : PUnit}
    (h : Ok (forIn a PUnit.unit fun o _ =>
      SubM.lin o >>= fun _ => pure (ForInStep.yield PUnit.unit)) F C u G D) :
    F.lins a.toList = some G ∧ D = C := by
  rw [← Array.forIn_toList] at h
  exact ok_lins_list a.toList h

/-! ## A row that is read in a table -/

/-- The form that names entry tb + j of the vector of reads, if the vector is stored as array number
iU3 with K3 columns. -/
def cellAt (iU3 K3 tb j : ℕ) : Aff := Aff.ent iU3 ((tb + j) / K3) ((tb + j) % K3)

/-- The row r is made from the first 99 entries of the table of the matrix hr under the weights
named P. K3: the number of columns of the array that stores the reads. -/
def RowOf (R : Model.Head.Run) (K3 : ℕ) (P : String) (r : Row5 Aff) : Prop :=
  ∃ (tb : ℕ) (cell : ℕ → Aff), Starts R ("hr@" ++ P) tb ∧ r = row5 cell ∧
    ∀ j, j < 99 → Valid R tb j ∧ cell j = cellAt R.iU3 K3 tb j

/-- A member of an array whose list of members is known. -/
theorem getD_of_toList {a : Array Aff} {n : ℕ} {f : ℕ → Aff}
    (h : a.toList = (List.range n).map f) {j : ℕ} (hj : j < n) : a.getD j {} = f j := by
  have e : a.getD j {} = (Option.map f (some j)).getD {} := by
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, h, List.getElem?_map,
      List.getElem?_range hj]
  exact e

/-- The routine that reads a row leaves state and context, and its row is read in the table. -/
theorem ok_row5At {R : Model.Head.Run} {P : String} {F G : Fork} {C D : Ctx} {r : Row5 Aff}
    (h : Ok (Model.Head.row5At R P) F C r G D) :
    G = F ∧ D = C ∧ RowOf R (colsOf F R.iU3) P r := by
  unfold Model.Head.row5At at h
  rw [ok_bind] at h
  obtain ⟨tb, F1, C1, h1, h2⟩ := h
  obtain ⟨e1, e2, hst⟩ := ok_tabAt h1
  rw [e1, e2] at h2
  try dsimp only at h2
  rw [ok_bind] at h2
  obtain ⟨cells, F2, C2, h3, h4⟩ := h2
  rw [ok_pure] at h4
  obtain ⟨e3, e4, e5⟩ := h4
  obtain ⟨i1, i2, i3, i4⟩ := ok_forIn_range 99 _
    (fun x (a : Array Aff) F' C' => F' = F ∧ C' = C ∧
      a.toList = (List.range x).map (cellAt R.iU3 (colsOf F R.iU3) tb) ∧
      ∀ j, j < x → Valid R tb j)
    (by
      rintro x a F3 C3 s F4 C4 _ ⟨eF, eC, hl, hv⟩ hs
      try dsimp only at hs
      rw [ok_bind] at hs
      obtain ⟨c, F5, C5, h5, h6⟩ := hs
      obtain ⟨e6, e7, e8, e9⟩ := ok_U3at h5
      rw [eF] at e8
      have e8' : c = cellAt R.iU3 (colsOf F R.iU3) tb x := e8
      rw [ok_bind] at h6
      obtain ⟨_, F6, C6, h7, h8⟩ := h6
      rw [ok_pure] at h7 h8
      obtain ⟨_, e10, e11⟩ := h7
      obtain ⟨e12, e13, e14⟩ := h8
      refine ⟨a.push c, e12, e13.trans (e10.trans (e6.trans eF)),
        e14.trans (e11.trans (e7.trans eC)), ?_, ?_⟩
      · rw [Array.toList_push, hl, e8', List.range_succ, List.map_append, List.map_cons,
          List.map_nil]
      · intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h9 | h9
        · exact hv j h9
        · rw [h9]
          exact e9)
    (by exact ⟨rfl, rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩)
    h3
  refine ⟨e4.trans i1, e5.trans i2, tb, fun j => cells.getD j {}, hst, e3, fun j hj => ?_⟩
  exact ⟨i4 j hj, getD_of_toList i3 hj⟩

/-! ## The 21 claims -/

/-- The four claims on the end values of the products' sumcheck: each slot against a number of the
row r. -/
def ledEnds (R : Model.Head.Run) (r : Row5 Aff) : List Aff :=
  [Aff.slot R.x.tV.sEnd - r.a, Aff.slot (R.x.tV.sEnd + 1) - r.b,
    Aff.slot (R.x.tV.sEnd + 2) - r.Rlo, Aff.slot (R.x.tV.sEnd + 3) - r.Rhi]

/-- The carries' line s of the row q, with the slot of the sum W_s. -/
def carry (R : Model.Head.Run) (q : Row5 Aff) (s : ℕ) : Aff :=
  ledCarry5 q s (Aff.slot (R.x.sW + s))

/-- The nine lines of the carries. -/
def ledCarries (R : Model.Head.Run) (q : Row5 Aff) : List Aff := (List.range 9).map (carry R q)

/-- The slots of the seven products. -/
def prSlots (R : Model.Head.Run) : Array Aff :=
  (Array.range 7).map fun j => Aff.slot (R.x.sPv + j)

/-- The eight lines on the square root and the reciprocal. -/
def ledTail (R : Model.Head.Run) (q : Row5 Aff) : List Aff :=
  (ledLines5 q (prSlots R) (Model.ofNat R.h.epsF)
    (Aff.ofConst (Model.ofNat (2 ^ (R.h.MF + 1))))).toList

/-- If the routine succeeds from a state with one coefficient for each slot, it leaves the context,
and what it does to the state is to add 21 claims: the four on end values, on a row r that is read
in the table "hr@r_tV", then the nine and the eight, on a row q that is read in the table
"hr@P_V". -/
theorem ok_claimLedger5 {R : Model.Head.Run} {F G : Fork} {C D : Ctx} {u : Unit}
    (hs : F.LS.size = F.ns) (h : Ok (Model.Head.claimLedger5 R) F C u G D) :
    D = C ∧ ∃ r q, RowOf R (colsOf F R.iU3) "r_tV" r ∧ RowOf R (colsOf F R.iU3) "P_V" q ∧
      F.lins (ledEnds R r ++ (ledCarries R q ++ ledTail R q)) = some G := by
  unfold Model.Head.claimLedger5 at h
  try dsimp only at h
  rw [ok_bind] at h
  obtain ⟨r, F1, C1, h1, h⟩ := h
  obtain ⟨e1, e2, hr⟩ := ok_row5At h1
  rw [e1, e2, ok_bind] at h
  obtain ⟨_, Fa, Ca, ha, h⟩ := h
  rw [ok_lin] at ha
  rw [ha.2, ok_bind] at h
  obtain ⟨_, Fb, Cb, hb, h⟩ := h
  rw [ok_lin] at hb
  rw [hb.2, ok_bind] at h
  obtain ⟨_, Fc, Cc, hc, h⟩ := h
  rw [ok_lin] at hc
  rw [hc.2, ok_bind] at h
  obtain ⟨_, Fd, Cd, hd, h⟩ := h
  rw [ok_lin] at hd
  rw [hd.2, ok_bind] at h
  have L4 : F.lins (ledEnds R r) = some Fd :=
    lins_cons_some ha.1 (lins_cons_some hb.1 (lins_cons_some hc.1 (lins_one hd.1)))
  obtain ⟨_, c4⟩ := lins_cols _ hs L4
  obtain ⟨q, F2, C2, h2, h⟩ := h
  obtain ⟨e3, e4, hq⟩ := ok_row5At h2
  rw [c4] at hq
  rw [e3, e4, ok_bind] at h
  obtain ⟨_, F3, C3, h3, h⟩ := h
  obtain ⟨L9, e5⟩ := ok_lins_range (carry R q) 9 h3
  try dsimp only at h
  rw [e5, ok_bind] at h
  obtain ⟨_, F4, C4, h4, h⟩ := h
  obtain ⟨L8, e6⟩ := ok_lins_array (ledLines5 q (prSlots R) (Model.ofNat R.h.epsF)
    (Aff.ofConst (Model.ofNat (2 ^ (R.h.MF + 1))))) h4
  rw [ok_pure] at h
  obtain ⟨_, e7, e8⟩ := h
  refine ⟨e8.trans e6, r, q, hr, hq, ?_⟩
  rw [e7]
  exact lins_append_some L4 (lins_append_some L9 L8)

/-- The first claim of claimLedger: the slot of the products' sumcheck against the slots of the
products (seven with five limbs) under the batching weights. -/
def ledFirst (R : Model.Head.Run) : Aff :=
  (List.range (Model.ledNP R.h.XL)).foldl
    (fun a i => Aff.addMul a (Aff.slot (R.x.sPv + i)) (subE zeroE (R.x.omV.getD i zeroE)))
    (Aff.slot R.x.tV.sCl)

/-- With five limbs claimLedger adds 23 claims: the first, the claim that the products' sumcheck
leaves, and the 21 of claimLedger5. -/
theorem ok_claimLedger {R : Model.Head.Run} {F G : Fork} {C D : Ctx} {u : Unit}
    (hXL : R.h.XL = 5) (hs : F.LS.size = F.ns) (h : Ok (Model.Head.claimLedger R) F C u G D) :
    D = C ∧ ∃ r q, RowOf R (colsOf F R.iU3) "r_tV" r ∧ RowOf R (colsOf F R.iU3) "P_V" q ∧
      F.lins ([ledFirst R, R.x.tV.rowU] ++
        (ledEnds R r ++ (ledCarries R q ++ ledTail R q))) = some G := by
  unfold Model.Head.claimLedger at h
  try dsimp only at h
  rw [ok_bind] at h
  obtain ⟨_, Fa, Ca, ha, h⟩ := h
  rw [ok_lin] at ha
  rw [ha.2, ok_bind] at h
  obtain ⟨_, Fb, Cb, hb, h⟩ := h
  rw [ok_lin] at hb
  have b5 : (R.h.XL == 5) = true := by simp [hXL]
  rw [hb.2, if_pos b5] at h
  have L2 : F.lins [ledFirst R, R.x.tV.rowU] = some Fb := lins_cons_some ha.1 (lins_one hb.1)
  obtain ⟨s2, c2⟩ := lins_cols _ hs L2
  obtain ⟨e, r, q, hr, hq, L⟩ := ok_claimLedger5 s2 h
  rw [c2] at hr hq
  exact ⟨e, r, q, hr, hq, lins_append_some L2 L⟩

/-! ## The values -/

section Values

variable {K : Type} [Field K] {ρ : Reading K} {W : World K}

/-- In a world where the table is true of the cells c at the point u, the form of cell n of a row
that is read in the table is worth, with 128 added, the extension at u of byte n. -/
theorem RowOf.bytes {R : Model.Head.Run} {K3 lt : ℕ} {P : String} {r : Row5 Aff} {u : ℕ → K}
    {c : ℕ → ℕ → K} (hr : RowOf R K3 P r) (hS : ShortAt W R K3 ("hr@" ++ P) lt u c) :
    ∃ cell : ℕ → Aff, r = row5 cell ∧
      ∀ n, n < 99 → (cell n).value ρ W + 128 = Blocks.ext lt (fun i => 128 + c n i) u := by
  obtain ⟨tb, cell, hst, e, hc⟩ := hr
  refine ⟨cell, e, fun n hn => ?_⟩
  obtain ⟨hv, he⟩ := hc n hn
  have h1 : (cell n).value ρ W = rdW W R.iU3 K3 (tb + n) := by
    rw [he]
    exact Aff.value_ent ρ W _ _ _
  rw [h1, hS tb hst n hv, Blocks.ext_add, Blocks.ext_const, add_comm]

variable {R : Model.Head.Run} {K3 lt : ℕ} {u : ℕ → K} {t : Inst.Model.Head.Cells K}

/-- The same for the cells of the matrix hr, in the library's name for a byte. -/
theorem RowOf.bytesDv {P : String} {r : Row5 Aff} (hr : RowOf R K3 P r)
    (hS : ShortAt W R K3 ("hr@" ++ P) lt u t.hr) :
    ∃ cell : ℕ → Aff, r = row5 cell ∧ ∀ n, n < 99 →
      (cell n).value ρ W + 128 = Blocks.ext lt (fun i => Inst.Model.Head.Dv t n i) u :=
  hr.bytes hS

/-- The name of the table of the 17 lines, joined from its parts. -/
theorem hr_PV : "hr@" ++ "P_V" = "hr@P_V" := by decide
/-- The name of the table of the four claims on end values, joined from its parts. -/
theorem hr_rtV : "hr@" ++ "r_tV" = "hr@r_tV" := by decide

/-- There are seven slots of products. -/
theorem prSlots_size (R : Model.Head.Run) : (prSlots R).size = 7 := by
  unfold prSlots
  rw [Array.size_map, Array.size_range]

/-- The value of the form of a product is what its slot holds. -/
theorem prSlots_value (R : Model.Head.Run) {j : ℕ} (hj : j < 7) :
    ((prSlots R).getD j (LedK.c zeroE)).value ρ W = W.slot (R.x.sPv + j) := by
  have e : (prSlots R).getD j (LedK.c zeroE) = Aff.slot (R.x.sPv + j) := by
    simp [prSlots, Array.getD, hj]
  rw [e, Aff.value_slot]

/-- There are nine lines of carries. -/
theorem ledCarries_length (R : Model.Head.Run) (q : Row5 Aff) : (ledCarries R q).length = 9 := by
  unfold ledCarries
  rw [List.length_map, List.length_range]

/-- There are eight lines on the square root and the reciprocal. -/
theorem ledTail_length (R : Model.Head.Run) (q : Row5 Aff) : (ledTail R q).length = 8 :=
  (congrArg List.length (ledLines5_list q (prSlots R) (prSlots_size R) _ _)).trans rfl

/-- The nine and the eight lines are 17 forms. -/
theorem ledger_length_17 (R : Model.Head.Run) (q : Row5 Aff) :
    (ledCarries R q ++ ledTail R q).length = 17 := by
  simp [ledCarries_length, ledTail_length]
/-- claimLedger5's list has 21 forms. -/
theorem ledger_length_21 (R : Model.Head.Run) (r q : Row5 Aff) :
    (ledEnds R r ++ (ledCarries R q ++ ledTail R q)).length = 21 := by
  simp [ledEnds, ledCarries_length, ledTail_length]
/-- claimLedger's list has 23 forms. -/
theorem ledger_length_23 (R : Model.Head.Run) (r q : Row5 Aff) :
    ([ledFirst R, R.x.tV.rowU] ++ (ledEnds R r ++ (ledCarries R q ++ ledTail R q))).length =
      23 := by
  simp [ledEnds, ledCarries_length, ledTail_length]

/-- Form number k of the 17 is worth the library's identity number k with letters for the products:
at the extensions of the bytes, at what the nine slots of the sums hold, and at what the seven slots
of the products hold. -/
theorem ledger_idnP (hρ : Numerals ρ) {q : Row5 Aff} (hq : RowOf R K3 "P_V" q)
    (hS : ShortAt W R K3 "hr@P_V" lt u t.hr) {k : ℕ} (hk : k < 17) :
    ((ledCarries R q ++ ledTail R q).getD k {}).value ρ W =
      Inst.Model.Ledger.idnP (npOf R.h) (fun s => W.slot (R.x.sW + s))
        (fun n => Blocks.ext lt (fun i => Inst.Model.Head.Dv t n i) u)
        (fun j => W.slot (R.x.sPv + j)) k := by
  rw [← hr_PV] at hS
  obtain ⟨cell, rfl, hD⟩ := hq.bytesDv (ρ := ρ) hS
  have len9 := ledCarries_length R (row5 cell)
  by_cases h9 : k < 9
  · have e : (ledCarries R (row5 cell) ++ ledTail R (row5 cell)).getD k {} =
        (Option.map (carry R (row5 cell)) (some k)).getD {} := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [len9]; exact h9)]
      unfold ledCarries
      rw [List.getElem?_map, List.getElem?_range h9]
    rw [e]
    exact ledCarry5_value hρ hD h9 _ _ _ _ (Aff.value_slot ρ W _)
  · obtain ⟨m, rfl⟩ : ∃ m, k = 9 + m := ⟨k - 9, by omega⟩
    have e : (ledCarries R (row5 cell) ++ ledTail R (row5 cell)).getD (9 + m) {} =
        (ledTail R (row5 cell)).getD m {} := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by rw [len9]; exact Nat.le_add_right 9 m), len9,
        Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
    have eT : ledTail R (row5 cell) = ledRoots (row5 cell) (prSlots R) (Model.ofNat R.h.epsF)
        (Aff.ofConst (Model.ofNat (2 ^ (R.h.MF + 1)))) :=
      ledLines5_list _ _ (prSlots_size R) _ _
    have heps : ρ.val (Model.ofNat R.h.epsF) = (((R.h.epsF : ℕ) : ℤ) : K) := by
      rw [hρ.ofNat, Int.cast_natCast]
    have htwo : (Aff.ofConst (Model.ofNat (2 ^ (R.h.MF + 1)))).value ρ W =
        (2 : K) ^ (R.h.MF + 1) := by
      rw [Aff.value_ofConst, hρ.ofNat, Nat.cast_pow, Nat.cast_ofNat]
    rw [e, eT]
    exact ledRoots_value hρ hD _ _ _ (npOf R.h) _ _ heps htwo
      (fun j hj => prSlots_value R hj) (by omega)

/-- Form number k of the 17 is worth the extension, at the point of the table, of the library's
identity number k, plus what the identity gains by what the slots hold beyond the extensions of the
nine sums and of the seven products. The sizes z enter through the sums alone. -/
theorem ledger_idn (hρ : Numerals ρ) (z : Sizes) {q : Row5 Aff} (hq : RowOf R K3 "P_V" q)
    (hS : ShortAt W R K3 "hr@P_V" lt u t.hr) {k : ℕ} (hk : k < 17) :
    ((ledCarries R q ++ ledTail R q).getD k {}).value ρ W =
      Blocks.ext lt (fun i => HeadSizes.idn z (npOf R.h) t i k) u +
        slack
          (fun s => W.slot (R.x.sW + s) - Blocks.ext lt
            (fun i => Inst.Model.Ledger.Wsum z.d (fun l j => HeadSizes.bl z t l j i) s) u)
          (fun j => W.slot (R.x.sPv + j) - Blocks.ext lt
            (fun i => Inst.Model.Ledger.prods (fun n => Inst.Model.Head.Dv t n i) j) u) k := by
  have e : Blocks.ext lt (fun i => HeadSizes.idn z (npOf R.h) t i k) u =
      Inst.Model.Ledger.idnP (npOf R.h)
        (fun s => Blocks.ext lt
          (fun i => Inst.Model.Ledger.Wsum z.d (fun l j => HeadSizes.bl z t l j i) s) u)
        (fun n => Blocks.ext lt (fun i => Inst.Model.Head.Dv t n i) u)
        (fun j => Blocks.ext lt
          (fun i => Inst.Model.Ledger.prods (fun n => Inst.Model.Head.Dv t n i) j) u) k :=
    Inst.Model.Ledger.ext_idn lt (fun n i => Inst.Model.Head.Dv t n i) u (npOf R.h)
      (fun s i => Inst.Model.Ledger.Wsum z.d (fun l j => HeadSizes.bl z t l j i) s) k
  rw [e, ledger_idnP hρ hq hS hk]
  exact idnP_slack _ _ _ _ _ _ _

/-- If the nine slots hold the extensions of the sums and the seven slots the extensions of the
products, form number k is worth the extension of the library's identity number k. -/
theorem ledger_idn_held (hρ : Numerals ρ) (z : Sizes) {q : Row5 Aff} (hq : RowOf R K3 "P_V" q)
    (hS : ShortAt W R K3 "hr@P_V" lt u t.hr) {k : ℕ} (hk : k < 17)
    (hW : ∀ s, s < 9 → W.slot (R.x.sW + s) = Blocks.ext lt
      (fun i => Inst.Model.Ledger.Wsum z.d (fun l j => HeadSizes.bl z t l j i) s) u)
    (hP : ∀ j, j < 7 → W.slot (R.x.sPv + j) = Blocks.ext lt
      (fun i => Inst.Model.Ledger.prods (fun n => Inst.Model.Head.Dv t n i) j) u) :
    ((ledCarries R q ++ ledTail R q).getD k {}).value ρ W =
      Blocks.ext lt (fun i => HeadSizes.idn z (npOf R.h) t i k) u := by
  rw [ledger_idn hρ z hq hS hk,
    slack_zero (fun s hs => sub_eq_zero.mpr (hW s hs)) (fun j hj => sub_eq_zero.mpr (hP j hj)),
    add_zero]

/-- The same at the library's sizes, in the names of Inst/Model/Head/TraceN.lean. -/
theorem ledger_idn_ref (hρ : Numerals ρ) {q : Row5 Aff} (hq : RowOf R K3 "P_V" q)
    (hS : ShortAt W R K3 "hr@P_V" lt u t.hr) {k : ℕ} (hk : k < 17)
    (hW : ∀ s, s < 9 → W.slot (R.x.sW + s) = Blocks.ext lt (fun i => Inst.Model.Ledger.Wsum
      Inst.Model.Head.nD (fun l j => Inst.Model.Head.bl t l j i) s) u)
    (hP : ∀ j, j < 7 → W.slot (R.x.sPv + j) = Blocks.ext lt
      (fun i => Inst.Model.Ledger.prods (fun n => Inst.Model.Head.Dv t n i) j) u) :
    ((ledCarries R q ++ ledTail R q).getD k {}).value ρ W =
      Blocks.ext lt (fun i => Inst.Model.Head.N.idn (npOf R.h) t i k) u :=
  ledger_idn_held hρ HeadSizes.ref hq hS hk hW hP

/-- The same in the names of Cm/Head.lean. -/
theorem ledger_idn_plain (hρ : Numerals ρ) {q : Row5 Aff} (hq : RowOf R K3 "P_V" q)
    (hS : ShortAt W R K3 "hr@P_V" lt u t.hr) {k : ℕ} (hk : k < 17)
    (hW : ∀ s, s < 9 → W.slot (R.x.sW + s) = Blocks.ext lt (fun i => Inst.Model.Ledger.Wsum
      Inst.Model.Head.nD (fun l j => Inst.Model.Head.bl t l j i) s) u)
    (hP : ∀ j, j < 7 → W.slot (R.x.sPv + j) = Blocks.ext lt
      (fun i => Inst.Model.Ledger.prods (fun n => Inst.Model.Head.Dv t n i) j) u) :
    ((ledCarries R q ++ ledTail R q).getD k {}).value ρ W =
      Blocks.ext lt (fun i => Cm.Plain.idn (npOf R.h) t i k) u :=
  ledger_idn_held hρ HeadSizes.ref hq hS hk hW hP

/-- The four claims on end values: each is worth what its slot holds, minus the extension, at the
point of the table "hr@r_tV", of one of the four factors of the products. -/
theorem ledger_ends (hρ : Numerals ρ) {r : Row5 Aff} (hr : RowOf R K3 "r_tV" r)
    (hS : ShortAt W R K3 "hr@r_tV" lt u t.hr) :
    (ledEnds R r).map (fun f => f.value ρ W) =
      [W.slot R.x.tV.sEnd - Blocks.ext lt
          (fun i => Inst.Model.Ledger.sa fun n => Inst.Model.Head.Dv t n i) u,
        W.slot (R.x.tV.sEnd + 1) - Blocks.ext lt
          (fun i => Inst.Model.Ledger.sb fun n => Inst.Model.Head.Dv t n i) u,
        W.slot (R.x.tV.sEnd + 2) - Blocks.ext lt
          (fun i => Inst.Model.Ledger.Rlo fun n => Inst.Model.Head.Dv t n i) u,
        W.slot (R.x.tV.sEnd + 3) - Blocks.ext lt
          (fun i => Inst.Model.Ledger.Rhi fun n => Inst.Model.Head.Dv t n i) u] := by
  rw [← hr_rtV] at hS
  obtain ⟨cell, rfl, hD⟩ := hr.bytesDv (ρ := ρ) hS
  have ea := Inst.Model.Ledger.ext_sa lt (fun n i => Inst.Model.Head.Dv t n i) u
  have eb := Inst.Model.Ledger.ext_sb lt (fun n i => Inst.Model.Head.Dv t n i) u
  have el := Inst.Model.Ledger.ext_Rlo lt (fun n i => Inst.Model.Head.Dv t n i) u
  have eh := Inst.Model.Ledger.ext_Rhi lt (fun n i => Inst.Model.Head.Dv t n i) u
  have va : (Aff.slot R.x.tV.sEnd - (row5 cell).a).value ρ W = W.slot R.x.tV.sEnd - Blocks.ext lt
      (fun i => Inst.Model.Ledger.sa fun n => Inst.Model.Head.Dv t n i) u := by
    rw [Aff.value_sub, Aff.value_slot, row5_a hρ hD]
    exact congrArg _ ea.symm
  have vb : (Aff.slot (R.x.tV.sEnd + 1) - (row5 cell).b).value ρ W = W.slot (R.x.tV.sEnd + 1) -
      Blocks.ext lt (fun i => Inst.Model.Ledger.sb fun n => Inst.Model.Head.Dv t n i) u := by
    rw [Aff.value_sub, Aff.value_slot, row5_b hρ hD]
    exact congrArg _ eb.symm
  have vl : (Aff.slot (R.x.tV.sEnd + 2) - (row5 cell).Rlo).value ρ W = W.slot (R.x.tV.sEnd + 2) -
      Blocks.ext lt (fun i => Inst.Model.Ledger.Rlo fun n => Inst.Model.Head.Dv t n i) u := by
    rw [Aff.value_sub, Aff.value_slot, row5_Rlo hρ hD]
    exact congrArg _ el.symm
  have vh : (Aff.slot (R.x.tV.sEnd + 3) - (row5 cell).Rhi).value ρ W = W.slot (R.x.tV.sEnd + 3) -
      Blocks.ext lt (fun i => Inst.Model.Ledger.Rhi fun n => Inst.Model.Head.Dv t n i) u := by
    rw [Aff.value_sub, Aff.value_slot, row5_Rhi hρ hD]
    exact congrArg _ eh.symm
  unfold ledEnds
  rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil, va, vb, vl, vh]

/-- The reciprocal of a row that is read in a table is worth the extension, at the table's point, of
the library's reciprocal. -/
theorem row_R_cells (hρ : Numerals ρ) {P : String} {r : Row5 Aff} (hr : RowOf R K3 P r)
    (hS : ShortAt W R K3 ("hr@" ++ P) lt u t.hr) :
    r.R.value ρ W =
      Blocks.ext lt (fun i => Inst.Model.Ledger.R fun n => Inst.Model.Head.Dv t n i) u := by
  obtain ⟨cell, rfl, hD⟩ := hr.bytesDv (ρ := ρ) hS
  rw [row5_R hρ hD]
  exact (Inst.Model.Ledger.ext_R lt (fun n i => Inst.Model.Head.Dv t n i) u).symm

/-- The value of a fold that subtracts slots under weights from a form. -/
theorem foldSlots_value (p : ℕ) (om : Array E) (a0 : Aff) (n : ℕ) :
    ((List.range n).foldl
      (fun a i => Aff.addMul a (Aff.slot (p + i)) (subE zeroE (om.getD i zeroE))) a0).value ρ W =
      a0.value ρ W - ∑ i ∈ range n, ρ.val (om.getD i zeroE) * W.slot (p + i) := by
  induction n with
  | zero =>
    have e : (List.range 0).foldl
        (fun a i => Aff.addMul a (Aff.slot (p + i)) (subE zeroE (om.getD i zeroE))) a0 = a0 := rfl
    rw [e, Finset.sum_range_zero, sub_zero]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Aff.value_addMul, ih,
      ρ.sub, ρ.zero, Aff.value_slot, Finset.sum_range_succ]
    ring

/-- With five limbs the first claim is worth what the slot of the products' sumcheck holds, minus
what the seven slots of the products hold under the batching weights. A weight past the end of the
array of weights counts as 0: that the array has seven members is not asked here. -/
theorem ledFirst_value (hXL : R.h.XL = 5) :
    (ledFirst R).value ρ W = W.slot R.x.tV.sCl -
      ∑ i ∈ range 7, ρ.val (R.x.omV.getD i zeroE) * W.slot (R.x.sPv + i) := by
  have e7 : Model.ledNP 5 = 7 := rfl
  unfold ledFirst
  rw [hXL, e7, foldSlots_value, Aff.value_slot]

/-- With five limbs the summand of the products' sumcheck on the four shown end values reads as the
sum, under the batching weights, of the library's seven products of these four. -/
theorem productsShown_value (ρ : Reading K) (omV sh : Array E) :
    ρ.val (Model.Head.productsShown 5 omV sh) = ∑ j ∈ range 7, ρ.val (omV.getD j zeroE) *
      Inst.Model.Ledger.prodsOf (ρ.val (sh.getD 0 zeroE)) (ρ.val (sh.getD 1 zeroE))
        (ρ.val (sh.getD 2 zeroE)) (ρ.val (sh.getD 3 zeroE)) j := by
  have e : Model.Head.productsShown 5 omV sh = Model.ledProducts5 omV 0 (sh.getD 0 zeroE)
      (sh.getD 1 zeroE) (sh.getD 2 zeroE) (sh.getD 3 zeroE) := rfl
  rw [e, ledProducts5_zero]

/-! ## The hypotheses can be met together -/

/-- Whether a table is true depends on the entries of a world alone, not on its slots. -/
theorem ShortAt.of_entry {W' : World K} {nm : String} {c : ℕ → ℕ → K} (h : W'.entry = W.entry)
    (hS : ShortAt W R K3 nm lt u c) : ShortAt W' R K3 nm lt u c := by
  intro tb hst φ hv
  have e := hS tb hst φ hv
  unfold rdW at e ⊢
  rw [h]
  exact e

omit [Field K] in
/-- If the nine slots of the sums and the seven slots of the products do not overlap, any world can
be changed on these 16 slots alone so that they hold given values. -/
theorem slots_witness (hA : R.x.sW + 9 ≤ R.x.sPv ∨ R.x.sPv + 7 ≤ R.x.sW) (W : World K)
    (a b : ℕ → K) : ∃ W' : World K, W'.entry = W.entry ∧
      (∀ s, s < 9 → W'.slot (R.x.sW + s) = a s) ∧ (∀ j, j < 7 → W'.slot (R.x.sPv + j) = b j) ∧
      ∀ x, ¬(R.x.sW ≤ x ∧ x < R.x.sW + 9) → ¬(R.x.sPv ≤ x ∧ x < R.x.sPv + 7) →
        W'.slot x = W.slot x := by
  refine ⟨⟨fun x => if R.x.sW ≤ x ∧ x < R.x.sW + 9 then a (x - R.x.sW)
    else if R.x.sPv ≤ x ∧ x < R.x.sPv + 7 then b (x - R.x.sPv) else W.slot x,
    W.entry⟩, rfl, fun s hs => ?_, fun j hj => ?_, fun x h1 h2 => ?_⟩
  · show (if R.x.sW ≤ R.x.sW + s ∧ R.x.sW + s < R.x.sW + 9 then a (R.x.sW + s - R.x.sW)
      else if R.x.sPv ≤ R.x.sW + s ∧ R.x.sW + s < R.x.sPv + 7 then b (R.x.sW + s - R.x.sPv)
      else W.slot (R.x.sW + s)) = a s
    rw [if_pos (by omega), Nat.add_sub_cancel_left]
  · show (if R.x.sW ≤ R.x.sPv + j ∧ R.x.sPv + j < R.x.sW + 9 then a (R.x.sPv + j - R.x.sW)
      else if R.x.sPv ≤ R.x.sPv + j ∧ R.x.sPv + j < R.x.sPv + 7 then b (R.x.sPv + j - R.x.sPv)
      else W.slot (R.x.sPv + j)) = b j
    rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  · show (if R.x.sW ≤ x ∧ x < R.x.sW + 9 then a (x - R.x.sW)
      else if R.x.sPv ≤ x ∧ x < R.x.sPv + 7 then b (x - R.x.sPv) else W.slot x) = W.slot x
    rw [if_neg h1, if_neg h2]

/-- From a world in which the table of the 17 lines is true, and slots that do not overlap, there is
a world that differs on the 16 slots alone, so with the same true table, in which the nine and the
seven slots hold the extensions. So the three hypotheses of ledger_idn_held on the world do not
contradict each other. -/
theorem ledger_hyps_meet (z : Sizes) (hA : R.x.sW + 9 ≤ R.x.sPv ∨ R.x.sPv + 7 ≤ R.x.sW)
    (hS : ShortAt W R K3 "hr@P_V" lt u t.hr) :
    ∃ W' : World K, W'.entry = W.entry ∧ ShortAt W' R K3 "hr@P_V" lt u t.hr ∧
      (∀ s, s < 9 → W'.slot (R.x.sW + s) = Blocks.ext lt
        (fun i => Inst.Model.Ledger.Wsum z.d (fun l j => HeadSizes.bl z t l j i) s) u) ∧
      (∀ j, j < 7 → W'.slot (R.x.sPv + j) = Blocks.ext lt
        (fun i => Inst.Model.Ledger.prods (fun n => Inst.Model.Head.Dv t n i) j) u) ∧
      ∀ x, ¬(R.x.sW ≤ x ∧ x < R.x.sW + 9) → ¬(R.x.sPv ≤ x ∧ x < R.x.sPv + 7) →
        W'.slot x = W.slot x := by
  obtain ⟨W', e, h1, h2, h3⟩ := slots_witness hA W
    (fun s => Blocks.ext lt
      (fun i => Inst.Model.Ledger.Wsum z.d (fun l j => HeadSizes.bl z t l j i) s) u)
    (fun j => Blocks.ext lt
      (fun i => Inst.Model.Ledger.prods (fun n => Inst.Model.Head.Dv t n i) j) u)
  exact ⟨W', e, hS.of_entry e, h1, h2, h3⟩

end Values

#print axioms ok_claimLedger
#print axioms ledFirst_value
#print axioms productsShown_value
#print axioms slots_witness
#print axioms ledger_hyps_meet
#print axioms ledger_length_23
#print axioms ShortAt.of_entry
#print axioms ok_row5At
#print axioms ok_lins_range
#print axioms ok_lins_array
#print axioms ok_claimLedger5
#print axioms ledger_idnP
#print axioms ledger_idn
#print axioms ledger_idn_ref
#print axioms ledger_idn_plain
#print axioms ledger_ends
#print axioms row_R_cells

end OnBytes.Road.Hd
