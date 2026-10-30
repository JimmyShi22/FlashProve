-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/KeptLong.lean: the code switch: WHAT THE FRONT READS OFF THE ORACLES
AT A KEPT ROW IS THE KEPT MEMBER's OWN MAIN SYMBOL: entry number 1 + (rowsBefore + b) of
K2Hears/LongOne.lean's longFront at a position q is main symbol number b of the column, at q, of the
message that the frame lists as its kept member number a.
  layMembers_some  where the laying succeeds every member of the list has a column
  colAtW_one     a member's column in openedOne is LongCols.lean's colOne
  colOne_size    a column of colOne has as many main symbols as the message's shape has main rows
  keptSym        main symbol number b of the message o's column at q, off the oracles; 0 where the
                 book, the message's place or the column lacks
  longFront_kept  THE STATEMENT
WHAT IT IS FOR. K2Hands/StrMade.lean's open word is made of longFront's entries at coordOf, and
coordOf at a kept slot is 1 + (rowsBefore + row). So the open word's kept slot holds, at every
position at which the front reads something, the kept member's own symbols: the second stone of «the
slot of the made open word is the kept member's own committed word».
LIMITS. Untyped still: no word of the library, no decoder. It speaks of positions at which longFront
has a value. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hands.StrMade
import Johnson.Top.H0.K2Hears.KeptNos
import Johnson.Top.H.SwitchKeptRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Model Johnson.Top.H
open VerifiableInference.Desc.Own (rowsAt layMembers layMember colAtW keptNos rowsAt_kept_at
  rowsAt_list switchKept_at switchKept_list Tables)
open _root_.Tw.K2 (switchNotices)

theorem layMembers_some (L : GroupLayout) (opened : Array (Array Column)) (i : Nat) :
    ∀ (ws : List Nat) (t t' : Tables), layMembers L opened i ws t = some t' →
      ∀ w ∈ ws, ∃ col, (opened[w]?).bind (fun (c : Array Column) => c[i]?) = some col
  | [], _, _, _, w, hw => by simp at hw
  | v :: ws, t, t', h, w, hw => by
    unfold layMembers at h
    obtain ⟨col, hc, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨t1, -, h2⟩ := Option.bind_eq_some_iff.1 h
    rcases List.mem_cons.1 hw with rfl | hw'
    · exact ⟨col, hc⟩
    · exact layMembers_some L opened i ws t1 t' h2 w hw'

/-- A member's column in openedOne. -/
theorem colAtW_one (S : Statement) (B : TreeBook) (ft logN : Nat) (orc : Nat → Nat → List UInt64)
    (idp : Array (Nat × Nat × Nat)) (q w : Nat) (col : Column)
    (h : ((K2.openedOne S B ft logN orc idp q)[w]?).bind (fun (c : Array Column) => c[0]?) =
      some col) :
    ∃ y, idp[w]? = some y ∧ K2.colOne S B ft logN orc y.1 y.2 q = some col := by
  unfold K2.openedOne at h
  rw [Array.getElem?_map] at h
  cases hy : idp[w]? with
  | none => simp [hy] at h
  | some y =>
    refine ⟨y, rfl, ?_⟩
    rw [hy] at h
    cases hc : K2.colOne S B ft logN orc y.1 y.2 q with
    | none => simp [hc] at h
    | some c => simpa [hc] using h

theorem colOne_size {S : Statement} {B : TreeBook} {ft logN : Nat} {orc : Nat → Nat → List UInt64}
    {o : Nat} {pl : Nat × Nat} {q : Nat} {col : Column}
    (h : K2.colOne S B ft logN orc o pl q = some col) :
    col.main.size = (S.oracles.getD o default).shape.mainRows := by
  unfold K2.colOne at h
  split at h
  · rename_i tree x h1 h2
    cases h
    simp [Blk.columnOf, Array.getD_eq_getD_getElem?, h2]
  · cases h

/-- Main symbol number b of the message o's column at the position q, off the oracles. -/
def keptSym (p : K2.P2) (s : VerifiableInference.Desc.First.S) (x : _root_.Tw.K2.Front)
    (orc : Nat → Nat → List UInt64) (o b q : Nat) : OnBytes.E :=
  (((K2.bookAt (K2.par9 p).firstTree x.st s.book s.roots (switchNotices x.T x.others)).bind fun B =>
      (B.place[o]?).bind fun pl =>
        K2.colOne (K2.skelOf x) B (K2.par9 p).firstTree p.logN orc o pl q).map
    fun c => c.main.getD b zeroE).getD zeroE

/-- **What the front reads at a kept row is the kept member's own main symbol.** -/
theorem longFront_kept {p : K2.P2} {s : VerifiableInference.Desc.First.S} {x : _root_.Tw.K2.Front}
    {orc : Nat → Nat → List UInt64} {q : Nat} {seg : Array OnBytes.E} {W₀ : SwitchFrame}
    (hm : x.f.rows.masks = 2) (h : K2.longFront p s x orc q = some seg)
    (hW : K2.frameAt x = some W₀) (a : ℕ) (k : KeptPlace) (b : ℕ) (hk : W₀.kept[a]? = some k)
    (hb : b < k.rows) :
    seg.getD (1 + (rowsBefore W₀.kept a + b)) zeroE = keptSym p s x orc k.old b q := by
  unfold K2.longFront at h
  obtain ⟨B, hB, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨places, hP, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨t, -, -, -, hlay, -⟩ := rowsAt_list x.f.rows hm _ 0 seg h
  obtain ⟨zs, zp⟩ := OnBytes.Slice.array_mapM_inv _ _ _ hP
  have hso : singleRowsOracles x.f.rows = x.f.rows.layout.members.push x.f.rows.fresh := by
    unfold singleRowsOracles
    simp [hm]
  have key : ∀ (j w : ℕ) (k' : KeptPlace), (keptNos x.f.rows.layout)[j]? = some w →
      W₀.kept[j]? = some k' → ∃ pl col, B.place[k'.old]? = some pl ∧
        K2.colOne (K2.skelOf x) B (K2.par9 p).firstTree p.logN orc k'.old pl q = some col ∧
        colAtW (K2.openedOne (K2.skelOf x) B (K2.par9 p).firstTree p.logN orc
          ((singleRowsOracles x.f.rows).zip places) q) 0 w = col ∧ col.main.size = k'.rows := by
    intro j w k' hw hk'
    have hwm : w < x.f.rows.layout.members.size :=
      List.mem_range.1 (List.mem_filter.1 (List.mem_of_getElem? hw)).1
    obtain ⟨col, hcol⟩ := layMembers_some _ _ _ _ _ _ hlay w (List.mem_range.2 hwm)
    obtain ⟨y, hy, hc⟩ := colAtW_one _ _ _ _ _ _ _ _ _ hcol
    obtain ⟨hi, e1, e2, -, -⟩ := kept_rec _ _ _ _ _ W₀ hW j k' hk'
    have e3 := switchKept_at x.f.rows j w hw
    rw [Array.getElem?_eq_getElem hi] at e3
    have eo : k'.old = x.f.rows.layout.members[w] := by
      rw [e1, Option.some.inj e3, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hwm]
      rfl
    have hws : w < (singleRowsOracles x.f.rows).size := by
      rw [hso, Array.size_push]
      omega
    have hwp : w < places.size := by rw [zs]; exact hws
    have hwz : w < ((singleRowsOracles x.f.rows).zip places).size := by
      rw [Array.size_zip]
      omega
    rw [Array.getElem?_eq_getElem hwz] at hy
    have ey : y = ((singleRowsOracles x.f.rows)[w], places[w]) := by
      rw [← Option.some.inj hy, Array.getElem_zip]
    have es : (singleRowsOracles x.f.rows)[w] = k'.old := by
      rw [eo]
      simp only [hso]
      exact Array.getElem_push_lt hwm
    have hpl := zp w hws
    rw [Array.getElem?_eq_getElem hwp, es] at hpl
    rw [ey] at hc
    simp only [es] at hc
    refine ⟨places[w], col, hpl, hc, ?_, ?_⟩
    · unfold colAtW
      rw [hcol]
      rfl
    · rw [colOne_size hc, e2, e1]
  obtain ⟨hi, -, -, -, -⟩ := kept_rec _ _ _ _ _ W₀ hW a k hk
  have hlen : (keptNos x.f.rows.layout).length = (switchKept x.f.rows).size := by
    have := congrArg List.length (switchKept_list x.f.rows)
    simpa using this.symm
  have hka : a < (keptNos x.f.rows.layout).length := by rw [hlen]; exact hi
  obtain ⟨pl, col, h1, h2, h3, h4⟩ := key a _ k (List.getElem?_eq_getElem hka) hk
  have hsum : ((W₀.kept.take a).map (·.rows)) = ((keptNos x.f.rows.layout).take a).map fun y =>
      (colAtW (K2.openedOne (K2.skelOf x) B (K2.par9 p).firstTree p.logN orc
        ((singleRowsOracles x.f.rows).zip places) q) 0 y).main.size := by
    apply List.ext_getElem?
    intro j
    simp only [List.getElem?_map, List.getElem?_take]
    by_cases hj : j < a
    · have hj1 : j < W₀.kept.length := Nat.lt_trans hj (List.getElem?_eq_some_iff.1 hk).1
      have hj2 : j < (keptNos x.f.rows.layout).length := Nat.lt_trans hj hka
      obtain ⟨-, c', -, -, g3, g4⟩ := key j _ _ (List.getElem?_eq_getElem hj2)
        (List.getElem?_eq_getElem hj1)
      simp only [if_pos hj, List.getElem?_eq_getElem hj1, List.getElem?_eq_getElem hj2,
        Option.map_some, g3, g4]
    · simp only [if_neg hj, Option.map_none]
  have e := rowsAt_kept_at x.f.rows hm _ 0 seg h a _ b (List.getElem?_eq_getElem hka)
    (by rw [h3, h4]; exact hb)
  rw [← hsum, h3] at e
  unfold keptSym rowsBefore
  rw [hB]
  simp only [Option.bind_some, h1, h2, Option.map_some, Option.getD_some]
  rw [Array.getD_eq_getD_getElem?, e, Array.getD_eq_getD_getElem?]

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.longFront_kept
