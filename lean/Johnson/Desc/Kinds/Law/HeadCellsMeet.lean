-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadCellsMeet.lean: THE LOOKUP'S CALLER'S CELLS AT THE OUTPUT HEAD AND THE
CELLS THAT THE HEAD'S LAW READS OFF THE WITNESS ARE THE SAME INSIDE THE RANGES THAT THE HEAD'S
RELATION NAMES: the frame of that tie, with what is left named.

Two readings. Another file's caller of the proved lookup sub-protocol at the head's calls
(Johnson/Desc/First/Look/K3CallerHead.lean) reads K6's structure of cells off its own
entries
mu: cellsH adr mu: at an address adr, the one small integer whose cast the entry is. K6's
law reads compCut w (Law/K6Cut.lean): the library's Hd.cellsH at segment 24's own integers, cut to
four ranges. The table's item "worth 24 3" speaks in the first; K6In in the second.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  InRanges h L b: THE GEOMETRY: the places at which the library's map lays the features that the
      head's relation names (wide below 4 d + 6 JV, act below 2 d, row below NR + 21, the stream
      below 5 d; positions below T) lie inside the four ranges.
  EntriesMeet ... mu w: THE TWO READERS: inside the four ranges the caller's entry is the cast of
      segment 24's own integer.
  own_small, smallH_own, beta_landed: SmallH HOLDS OF SEGMENT 24'S OWN INTEGERS AT EVERY
      WITNESS, by their make (an entry of the one small column that packs to the committed symbols,
      or 0), at a shift of at most 2 ^ 17: the library's sizes' is that.
  sameCells_head: under these two, SmallH of the own integers, and "the weights meet"
      (hW): SameCells (cellsH (adrOf h L b) mu) (compCut ... w).1: so, by Law/CellsAlike.lean, THE
      SAME KEY TABLES AND THE SAME TWO CORNER VALUES.

  entriesMeet_of_syms: EntriesMeet at the caller's own reading msgLay of a tuple of messages, WHERE
      THE TWO READERS FIND THE SAME SYMBOLS in the columns of the four ranges (hsym) and the four
      ranges lie inside the plan's sizes (hsz): by cell_ownAt (the cast of an own integer
      IS the cell behind its symbols, by the make) and cellsOf_congr.

Every letter under "there is": none.
What it does not say. InRanges: a sentence on public numbers: "that K6's numbers of features
are the library's" is held by nobody. hsym: that two readers of one witness (the caller's, through
its own list of members and seats; the table's, through readAt) find the same symbols: NOT SHOWN.
hsz: on the plan's numbers: not shown.
hW: the caller's weight (off the committed table's message, two bytes) against whOf of the witness's
cells: NOT SHOWN. The mask row is not spoken of. Nothing on soundness.
-/
import Johnson.Desc.First.Look.K3CallerHead
import Johnson.Desc.Kinds.Law.CellsAlike
import Johnson.Desc.Kinds.Law.K6Cut
import Johnson.Goal.Meaning.HidBase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model.Verify (borderOf)
open VerifiableInference.Desc.First.Look (JLay matsOfE wOfE)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT)
open Norm (d T)

/-- **The geometry.** -/
structure InRanges [Sizes] (h : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL)
    (b : OnBytes.Model.Head.Border) : Prop where
  wide : ∀ f t, f < 4 * d + 6 * JV → t < T → InFour h L b ((adrOf h L b).cell .wide f t).1
    ((adrOf h L b).cell .wide f t).2.1 ((adrOf h L b).cell .wide f t).2.2
  act : ∀ f t, f < 2 * d → t < T → InFour h L b ((adrOf h L b).cell .act f t).1
    ((adrOf h L b).cell .act f t).2.1 ((adrOf h L b).cell .act f t).2.2
  row : ∀ f t, f < NR + 21 → t < T → InFour h L b ((adrOf h L b).cell .row f t).1
    ((adrOf h L b).cell .row f t).2.1 ((adrOf h L b).cell .row f t).2.2
  stream : ∀ f t, f < 5 * d → t < T → InFour h L b ((adrOf h L b).stream f t).1
    ((adrOf h L b).stream f t).2.1 ((adrOf h L b).stream f t).2.2

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
  (pl : Nat → Nat × Bool × Nat × Nat)

/-- **The two readers.** -/
def EntriesMeet {ns : Nat} {tl : OnBytes.Model.HTailF2} {nr nc : Nat}
    (μ : JLay ns tl nr nc → Cb.Gl.E) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) : Prop :=
  ∀ a r c, InFour Wp.hS Wp.HLy (borderOf Wp.y) a r c →
    matsOfE μ a r c = ((P5J.ownQ cs arr msR N s seat w 24 a r c : Int) : Cb.Gl.E)

namespace Came

/-- **Segment 24's own integers are small BY THEIR MAKE**: each is an entry of the one small column
that packs to the committed symbols, or 0 where there is none. (What bites is the packing: the
table's own clause base.) -/
theorem own_small {Cells : Type} (w : Wit Cells Tok MsgT) (hb : 0 < (s 24).beta)
    (h2 : 2 * ((s 24).beta : Int) ≤ 2 ^ 18) (a r c : Nat) :
    |P5J.ownQ cs arr msR N s seat w 24 a r c| < 2 ^ 18 := by
  have hb' : (0 : Int) < ((s 24).beta : Int) := by exact_mod_cast hb
  unfold P5J.ownQ Meaning.ownOf OnBytes.Road.Rows.Norms.mzTot
  beta_reduce
  by_cases h1 : a < (s 24).NM
  · rw [dif_pos h1]
    by_cases h3 : c < (s 24).k (⟨a, h1⟩ : Fin (s 24).NM)
    · rw [dif_pos h3]
      by_cases h4 : r < (s 24).m (⟨a, h1⟩ : Fin (s 24).NM)
      · rw [dif_pos h4]
        refine lt_of_lt_of_le ?_ h2
        by_cases h : ∃ z, Cb.Pv.Tail.Packs (Cb.Pv.Tail.symL Cb.Gl.E (s 24))
            (Meaning.symAt (s 24) (seat 24) (Sound.readAt cs arr msR N 24 w)) ⟨a, h1⟩ ⟨c, h3⟩ z
        · exact (Cb.Pv.Tail.packs_cellsOf (Cb.Pv.Tail.symL Cb.Gl.E (s 24)) h).1 ⟨r, h4⟩
        · show |Cb.Pv.Tail.cellsOf (Cb.Pv.Tail.symL Cb.Gl.E (s 24)) _ ⟨a, h1⟩ ⟨c, h3⟩ ⟨r, h4⟩| < _
          unfold Cb.Pv.Tail.cellsOf
          rw [dif_neg h, abs_zero]
          omega
      · rw [dif_neg h4, abs_zero]
        norm_num
    · rw [dif_neg h3, abs_zero]
      norm_num
  · rw [dif_neg h1, abs_zero]
    norm_num

/-- So SmallH holds of them, at every witness. -/
theorem smallH_own {Cells : Type} (w : Wit Cells Tok MsgT) (hb : 0 < (s 24).beta)
    (h2 : 2 * ((s 24).beta : Int) ≤ 2 ^ 18) :
    OnBytes.Road.Hd.SmallH Wp.hS Wp.HLy (borderOf Wp.y) (P5J.ownQ cs arr msR N s seat w 24) :=
  OnBytes.Road.Hd.smallH_of_all (own_small cs arr msR N s seat w hb h2)

/-- At the library's sizes the shift is 2 ^ 17. -/
theorem beta_landed (k : Nat) : (Meaning.sizesOf Wp k).beta = 2 ^ 17 := rfl

/-- One cell. -/
theorem cell_meets {ns : Nat} {tl : OnBytes.Model.HTailF2} {nr nc : Nat}
    (μ : JLay ns tl nr nc → Cb.Gl.E) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (hE : EntriesMeet cs arr msR N s seat Wp μ w)
    (hS : OnBytes.Road.Hd.SmallH Wp.hS Wp.HLy (borderOf Wp.y) (P5J.ownQ cs arr msR N s seat w 24))
    (a r c : Nat) (hin : InFour Wp.hS Wp.HLy (borderOf Wp.y) a r c) :
    intOf (matsOfE μ a r c) = ownCut cs arr msR N s seat Wp w a r c := by
  have hc : ownCut cs arr msR N s seat Wp w a r c = P5J.ownQ cs arr msR N s seat w 24 a r c :=
    if_pos hin
  have hsm := cut_small hS a r c
  rw [hE a r c hin, hc]
  refine intOf_cast ?_
  have e : cutM Wp.hS Wp.HLy (borderOf Wp.y) (P5J.ownQ cs arr msR N s seat w 24) a r c =
      P5J.ownQ cs arr msR N s seat w 24 a r c := if_pos hin
  rw [e] at hsm
  rw [Int.abs_eq_natAbs]
  exact_mod_cast hsm

/-- **The two structures of cells agree inside the ranges.** -/
theorem sameCells_head [Sizes] {ns : Nat} {tl : OnBytes.Model.HTailF2} {nr nc : Nat}
    (μ : JLay ns tl nr nc → Cb.Gl.E) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (hG : InRanges Wp.hS Wp.HLy (borderOf Wp.y))
    (hE : EntriesMeet cs arr msR N s seat Wp μ w)
    (hS : OnBytes.Road.Hd.SmallH Wp.hS Wp.HLy (borderOf Wp.y) (P5J.ownQ cs arr msR N s seat w 24))
    (hW : ∀ k v, k < d → v < V →
      intW (Inst.Model.Head.Hof (wOfE μ) k v) = whOf w.cells k v) :
    SameCells (cellsH (adrOf Wp.hS Wp.HLy (borderOf Wp.y)) μ)
      (compCut cs arr msR N s seat Wp pl w).1 :=
  ⟨fun f t hf ht => cell_meets cs arr msR N s seat Wp μ w hE hS _ _ _ (hG.wide f t hf ht),
    fun f t hf ht => cell_meets cs arr msR N s seat Wp μ w hE hS _ _ _ (hG.act f t hf ht),
    fun f t hf ht => cell_meets cs arr msR N s seat Wp μ w hE hS _ _ _ (hG.row f t hf ht),
    fun f t hf ht => cell_meets cs arr msR N s seat Wp μ w hE hS _ _ _ (hG.stream f t hf ht),
    hW⟩

/-- **The two readers meet where they find the same symbols.** The caller's entries are its own
reading msgLay of a tuple of messages m, at the plan's entry for segment 24. -/
theorem entriesMeet_of_syms (seat24 : ∀ k, Fin (Meaning.sizesOf Wp k).NM → Nat → Nat → Nat × Nat ×
    Nat)
    (x : First.Look.Place) (D : First.Look.Sent) (rad : OnBytes.OracleShape → Nat)
    (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → Nat → Nat → Cb.Gl.E) (nr nc : Nat)
    (m : (First.Look.laySg x D rad oW).Msg) (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (hsz : ∀ a r c, InFour Wp.hS Wp.HLy (borderOf Wp.y) a r c →
      a < (Meaning.sizesOf Wp 24).NM ∧ c < (Meaning.sizesOf Wp 24).k a ∧
        r < (Meaning.sizesOf Wp 24).m a)
    (hsym : ∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (c : Fin ((Meaning.sizesOf Wp 24).k μ)),
      ColFour Wp.hS Wp.HLy (borderOf Wp.y) μ.val c.val → ∀ i',
      First.Look.symAt D.codes (First.Look.sigListCalls D rad x.link)
          (First.Look.seatCalls D x.link) (Meaning.tlAt Wp 24) (First.Look.ownPart m) μ i' c =
        Meaning.symAt (Meaning.sizesOf Wp 24) (seat24 24) (Sound.readAt cs arr msR N 24 w) μ i' c) :
    EntriesMeet cs arr msR N (Meaning.sizesOf Wp) seat24 Wp
      (First.Look.msgLay x (Meaning.tlAt Wp 24) D rad oW wOf nr nc m) w := by
  intro a r c hin
  obtain ⟨h1, h2, h3⟩ := hsz a r c hin
  have eL : matsOfE (First.Look.msgLay x (Meaning.tlAt Wp 24) D rad oW wOf nr nc m) a r c =
      Cb.Pv.Tail.cellValS (First.Look.symAt D.codes (First.Look.sigListCalls D rad x.link)
        (First.Look.seatCalls D x.link) (Meaning.tlAt Wp 24) (First.Look.ownPart m))
        ⟨⟨a, h1⟩, ⟨c, h2⟩, ⟨r, h3⟩⟩ := by
    unfold matsOfE First.Look.lyCell First.Look.cellJ
    rw [dif_pos ⟨h1, h2, h3⟩]
    rfl
  rw [eL, P5J.ownQ_at, Meaning.cell_ownAt h1 h2 h3]
  exact congrArg (fun z : Int => (z : Cb.Gl.E))
    (congrFun (Cb.Pv.Tail.cellsOf_congr (Λ := Cb.Pv.Tail.symL Cb.Gl.E (Meaning.sizesOf Wp 24))
      (msg := First.Look.symAt D.codes (First.Look.sigListCalls D rad x.link)
        (First.Look.seatCalls D x.link) (Meaning.tlAt Wp 24) (First.Look.ownPart m))
      (msg' := Meaning.symAt (Meaning.sizesOf Wp 24) (seat24 24) (Sound.readAt cs arr msR N 24 w))
      (μ := ⟨a, h1⟩) (c := ⟨c, h2⟩) (hsym ⟨a, h1⟩ ⟨c, h2⟩ (colFour_of_in hin))) ⟨r, h3⟩)

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.own_small
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.smallH_own
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.beta_landed
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.cell_meets
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.sameCells_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.entriesMeet_of_syms
