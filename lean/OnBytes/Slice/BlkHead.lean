-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkHead.lean: the program's link, run on a written transcript: the row after the
batching.

OnBytes/Slice/BlkChain.lean follows the program's yes from block to block. Its first statement,
`HeadRuns`, is on the link's steps and the batching after them: the head. This file has the claim
of that head, for a run whose five rounds are the written ones: the row which the program holds,
read in the field, is the sum of the link's rows under the powers of the drawn element. It does
not prove `HeadRuns`.

How the proof goes. The two runs are hypotheses (`LinkRan`, `BatRan`). The
five rounds of the link are the written ones by hypothesis, so what the program drew and received
is what the written rounds hold. Each stored column that the program took is an opened column
under the stored table's key, so it is that table's column, again by hypothesis (`hop`).
With these the program's rows are the rows of OnBytes/Slice/RowsX.lean at the statement that the
library's verifier holds after the five rounds (OnBytes/Slice/BlkLinkJoin.lean), and the batching
adds them up under the powers of the drawn element (OnBytes/Slice/BlkLinkHead.lean).

Main definitions.
 `rvW`         a written round as a view holds it.

Main theorem.

 `head_claim`    the row that the batching returns is the sum of the link's rows.



What is asked: public facts on sizes, shapes and draws (`LinkSizes`, `LinkFit`, `BatDraws`), the
hypotheses above, and that the row's first `S.P.Z.l` coefficients on the mask table read as 0.
Not claimed. `HeadRuns` of any run. The tie of the group's columns to the written oracles. Nothing
on the dry run. Nothing on soundness.
-/
import OnBytes.Slice.BlkJoints
import OnBytes.Slice.BlkLinkHead
import OnBytes.Slice.BlkLinkJoin
import OnBytes.Slice.BlkBat
import OnBytes.Slice.BlkPlain
import OnBytes.Slice.WrittenView

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb _root_.Run
open Params (LinkShape IoppStage)

/-- A written round as a view holds it. -/
def rvW (d : PQ.RD) (m : (wRound d).Msg) (c : (wRound d).Chal) : Fmt.RoundView :=
  ⟨PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
    (ckP .two).dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩

/-- The elements that it draws are those that the format's decision reads. -/
theorem rvW_elems (d : PQ.RD) (m : (wRound d).Msg) (c : (wRound d).Chal) :
    (rvW d m c).drawn.elems = (rvOf d m c).els := rfl

/-- The positions likewise. -/
theorem rvW_poss (d : PQ.RD) (m : (wRound d).Msg) (c : (wRound d).Chal) :
    (rvW d m c).drawn.poss = (rvOf d m c).poss := rfl

/-- The elements that it sends likewise. -/
theorem rvW_sent (d : PQ.RD) (m : (wRound d).Msg) (c : (wRound d).Chal) :
    Fmt.M1.sentOf (rvW d m c).vals = (rvOf d m c).sent := rfl

section
variable (S : Sz) (t₀ : ℕ) (Λ : LinkShape) (first further : TableKey) (st1 : IoppStage)
  (s : Start) (V : Fmt.View) (d1 d2 d3 d4 d5 dA : PQ.RD)
  (m1 : (wRound d1).Msg) (c1 : (wRound d1).Chal) (m2 : (wRound d2).Msg)
  (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) (c3 : (wRound d3).Chal)
  (m4 : (wRound d4).Msg) (c4 : (wRound d4).Chal) (m5 : (wRound d5).Msg) (c5 : (wRound d5).Chal)
  (mA : (wRound dA).Msg) (cA : (wRound dA).Chal) (rest0 : List Fmt.RoundView)

end

/-! ## The claim after the batching -/

/-- The entry after the first n of a list whose tail after them is one entry. -/
theorem getD_of_drop {α : Type} (l : List α) (n : ℕ) (a d : α) (h : l.drop n = [a]) :
    l.getD n d = a := by
  rw [List.getD_eq_getElem?_getD, ← Nat.add_zero n, ← List.getElem?_drop, h]
  rfl

section
variable (S : Sz) (t₀ : ℕ) (Λ : LinkShape) (first further : TableKey)
  (d1 d2 d3 d4 d5 dA : PQ.RD)
  (m1 : (wRound d1).Msg) (c1 : (wRound d1).Chal) (m2 : (wRound d2).Msg)
  (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) (c3 : (wRound d3).Chal)
  (m4 : (wRound d4).Msg) (c4 : (wRound d4).Chal) (m5 : (wRound d5).Msg) (c5 : (wRound d5).Chal)

/-- The row that the batching returns, read in the field, is the sum of the link's rows under the
powers of the drawn element. Asked, beside public sizes: the five rounds that the run took are the
written ones, each opened column under a stored table's key is that table's column (`hop`), and the
row's first `S.P.Z.l` coefficients on the mask table read as 0 (`hmask`). -/
theorem head_claim (c c' cd : Ctx) (x : LinkRun) (D : LinkData) (G0 : Group) (L : GroupLayout)
    (θ : E) (row : GroupRow) (hS : LinkSizes S Λ c.st.codes)
    (hF : LinkFit S Λ (Λ.side false 1) (Λ.side true 1)) (hd : BatDraws S d1 d2 d3 d4 d5 dA)
    (hn0 : (Λ.side false 1).columns = Λ.columnsFirst)
    (hn1 : (Λ.side true 1).columns = Λ.columnsFurther)
    (hi0 : first.item = 0) (hi1 : further.item = 1) (y : S.lk.E0.Str)
    (hR : LinkRan Λ first further c c' x D) (hB : BatRan x.group c' cd G0 L θ row)
    (a1 : D.r1 = rvW d1 m1 c1) (a2 : D.r2 = rvW d2 m2 c2) (a3 : D.r3 = rvW d3 m3 c3)
    (a4 : D.r4 = rvW d4 m4 c4) (a5 : D.r5 = rvW d5 m5 c5)
    (hop : ∀ o ∈ c.ch.opened,
      (o.1 = Fmt.storedKey 0 → storedOf S.P.T.a y 0 o.2.1 = some o.2.2) ∧
      (o.1 = Fmt.storedKey 1 → storedOf S.P.T.a y 1 o.2.1 = some o.2.2))
    (hmask : ∀ i, i < S.P.Z.l → readV row.d i = 0) :
    stmG (S.sg t₀) row =
      sumStm S t₀ (rowsX S t₀ (st4 S d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).1
        (rowsX S t₀ (st4 S d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).2 (readE θ) := by
  have hbits := hS.bits
  have haR : ceilLog2 Λ.rows = S.P.aR := by rw [hS.rows]; rfl
  have hpl : (rvOf d4 m4 c4).poss.length = S.P.nu0 + S.P.nuj := hd.r4.poss_length m4 c4
  have hdr : D.pos.draws.toList = (rvOf d4 m4 c4).poss := by
    rw [hR.pos, a4]
    rfl
  -- the columns that were read are the stored tables'
  have hat : ∀ (key : ℕ) (l : List ℕ) (cols : Array (Array F)) (i xx : ℕ) (col : Array F),
      cols.size = l.toArray.size → l.toArray.idxOf? xx = some i → cols[i]? = some col →
      (key, xx, col.toList) ∈ viewColumns key l.toArray cols := by
    intro key l cols i xx col hsz hi hc
    rw [List.idxOf?_toArray] at hi
    obtain ⟨h1, h2, -⟩ := List.idxOf?_eq_some_iff.1 hi
    have h3 : i < l.toArray.size := h1
    have h4 : i < cols.size := hsz ▸ h3
    have h5 := mem_viewColumns key l.toArray cols i h3 h4
    have e1 : l.toArray.getD i 0 = xx := by
      rw [← h2]
      simp [Array.getD, h1]
    have e2 : cols.getD i #[] = col := by
      rw [Array.getElem?_eq_getElem h4] at hc
      rw [← Option.some.inj hc]
      simp [Array.getD, h4]
    rwa [e1, e2] at h5
  have hcol0 : ∀ (i : ℕ) (col : Array F) (xx : S.Pos),
      (storedList (linkStored Λ first false) D.pos).toArray.idxOf? xx.val = some i →
      D.cols0[i]? = some col → col.toList = (y.1 xx).2 := by
    intro i col xx hi hc
    have hm : (Fmt.storedKey first.item, xx.val, col.toList) ∈ c.ch.opened := by
      rw [hR.opened]
      exact List.mem_append_left _ (hat _ _ _ i xx.val col hR.size0 hi hc)
    have h0 := (hop _ hm).1 (by rw [hi0])
    unfold storedOf at h0
    rw [dif_pos xx.isLt, if_pos rfl] at h0
    exact (Option.some.inj h0).symm
  have hcol1 : ∀ (i : ℕ) (col : Array F) (xx : S.Pos),
      (storedList (linkStored Λ further true) D.pos).toArray.idxOf? xx.val = some i →
      D.cols1[i]? = some col → col.toList = (y.2 xx).2 := by
    intro i col xx hi hc
    have hm : (Fmt.storedKey further.item, xx.val, col.toList) ∈ c.ch.opened := by
      rw [hR.opened]
      exact List.mem_append_right _
        (List.mem_append_left _ (hat _ _ _ i xx.val col hR.size1 hi hc))
    have h0 := (hop _ hm).2 (by rw [hi1])
    unfold storedOf at h0
    rw [dif_pos xx.isLt, if_neg Nat.one_ne_zero, if_pos rfl] at h0
    exact (Option.some.inj h0).symm
  -- what the program drew and received is what the written rounds hold
  have hmt : ∀ l : List (UInt64 × UInt64 × UInt64), (l.map E.ofTriple).map E.triple = l := by
    intro l
    rw [List.map_map]
    exact List.map_id l
  have hgamma : x.gamma.map E.triple = (rvOf d1 m1 c1).els := by
    rw [hR.gamma, hmt, a1]
    rfl
  have hphi : x.phi.map E.triple = (rvOf d5 m5 c5).els := by
    rw [hR.phi, hmt, a5]
    rfl
  have hz : ((D.r2.drawn.elems.map E.ofTriple).take
      (Send.cube c.st.codes (rowShape Λ)).bits).map E.triple =
      (rvOf d2 m2 c2).els.take (S.P.aR + S.P.aP) := by
    rw [List.map_take, hmt, a2, hbits]
    rfl
  have hbeta : D.beta.triple = (rvOf d2 m2 c2).els.getD (S.P.aR + S.P.aP) Fmt.Fld.zeroE := by
    have h0 := getD_of_drop _ _ _ (E.ofTriple Fmt.Fld.zeroE) hR.factor
    rw [hbits, List.getD_map, a2] at h0
    rw [← h0]
    rfl
  have hsent : (rvOf d3 m3 c3).sent = [D.y0.triple, D.y1.triple] := by
    rw [← rvW_sent, ← a3, hR.vals3]
    rfl
  have hy0 : D.y0.triple = (rvOf d3 m3 c3).sent.getD 0 Fmt.Fld.zeroE := by rw [hsent]; rfl
  have hy1 : D.y1.triple = (rvOf d3 m3 c3).sent.getD 1 Fmt.Fld.zeroE := by rw [hsent]; rfl
  have hl0 : ((D.pos.draws.toList.drop 0).take (Λ.side false 1).columns).length = S.P.nu0 := by
    rw [hdr, hn0, hS.n0, List.length_take, List.length_drop, hpl]
    omega
  have hl1 : ((D.pos.draws.toList.drop Λ.columnsFirst).take (Λ.side true 1).columns).length =
      S.P.nuj := by
    rw [hdr, hn1, hS.n0, hS.n1, List.length_take, List.length_drop, hpl]
    omega
  have hD0 : ∀ i, i < S.P.nu0 →
      ((D.pos.draws.toList.drop 0).take (Λ.side false 1).columns).getD i 0 =
        (rvOf d4 m4 c4).poss.getD i 0 := by
    intro i hi
    rw [hdr, hn0, hS.n0, List.drop_zero, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt hi]
  have hD1 : ∀ i, i < S.P.nuj →
      ((D.pos.draws.toList.drop Λ.columnsFirst).take (Λ.side true 1).columns).getD i 0 =
        (rvOf d4 m4 c4).poss.getD (S.P.nu0 + i) 0 := by
    intro i hi
    rw [hdr, hn1, hS.n0, hS.n1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt hi, List.getElem?_drop]
  have heq := hR.eqRow
  rw [hR.uFirst, hR.uFurther] at heq
  have hc0 := hR.rows0
  rw [hR.uFirst] at hc0
  have hc1 := hR.rows1
  rw [hR.uFurther] at hc1
  have hrows := head_rows S Λ c.st.codes hS hF d1 d2 d3 d4 d5 dA hd y m1 c1 m2 c2 m3 c3 m4 c4 m5 c5
    c.st.oracles.size x.gamma x.phi _ D.beta D.y0 D.y1 _ _ D.rE D.row0 D.row1 D.rows0 D.rows1 _ _
    _ _ hgamma hz hbeta hy0 hy1 hl0 hl1 hD0 hD1 hphi heq hR.form0 hR.form1 hc0 hc1 hcol0 hcol1
  -- the number of rows
  have hlen : D.rows.length = S.nRows := by
    have e0 := (colRows_getD _ _ _ _ _ _ _ hc0).1
    have e1 := (colRows_getD _ _ _ _ _ _ _ hc1).1
    show (D.rows0 ++ D.rows1).length + 1 + 1 + 1 = 3 + (S.P.nu0 + S.P.nuj)
    rw [List.length_append, e0, e1, hl0, hl1]
    omega
  refine stmG_rowsX S t₀ hF.pow _ D.rows c.st.oracles.size (c.st.oracles.size + 1) (readE θ) row
    hrows ?_ ?_ hmask
  · have h0 := hR.bat_target hB rdE
    rw [hlen] at h0
    exact h0
  · intro a r p hr _
    have h0 := hR.bat_main hB rdE a r p (by rw [haR]; exact hr)
    rw [hlen, haR] at h0
    exact h0

end

/-! ## The joint after the head -/

section
variable (S : Sz) (t₀ : ℕ) (Λ : LinkShape) (first further : TableKey) (st1 : IoppStage)
  (s : Start) (V : Fmt.View) (K : Codes) (Tie : Ctx → GroupRow → GroupLayout → Nat → Prop)
  (d1 d2 d3 d4 d5 dA : PQ.RD)
  (m1 : (wRound d1).Msg) (c1 : (wRound d1).Chal) (m2 : (wRound d2).Msg)
  (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) (c3 : (wRound d3).Chal)
  (m4 : (wRound d4).Msg) (c4 : (wRound d4).Chal) (m5 : (wRound d5).Msg) (c5 : (wRound d5).Chal)
  (mA : (wRound dA).Msg) (cA : (wRound dA).Chal) (rest0 : List Fmt.RoundView)

end

/-! ## At the view of the written link -/

section
variable (S : Sz) (t₀ : ℕ) (s2 : Sg) (Λ : LinkShape) (first further : TableKey) (st1 : IoppStage)
  (s : Start) (K : Codes) (Tie : Ctx → GroupRow → GroupLayout → Nat → Prop)
  (d1 d2 d3 d4 d5 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB : PQ.RD)
  (m1 : (wRound d1).Msg) (c1 : (wRound d1).Chal) (m2 : (wRound d2).Msg)
  (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) (c3 : (wRound d3).Chal)
  (m4 : (wRound d4).Msg) (c4 : (wRound d4).Chal) (m5 : (wRound d5).Msg) (c5 : (wRound d5).Chal)
  (mA : (wRound dA).Msg) (cA : (wRound dA).Chal)
  (τF1 : Tr (PQ.uL (ckP .two) (foldRds (S.sg t₀) dE1 dT1)))
  (τC1 : Tr (PQ.uL (ckP .two) [dS2, dC1])) (τF2 : Tr (PQ.uL (ckP .two) (foldRds s2 dE2 dT2)))
  (τC2 : Tr (PQ.uL (ckP .two) [dS3, dC2])) (τB : Tr (PQ.uL (ckP .two) [dL, dB]))

end

end OnBytes.Slice

#print axioms OnBytes.Slice.head_claim
#print axioms OnBytes.Slice.rvW_elems
#print axioms OnBytes.Slice.rvW_poss
#print axioms OnBytes.Slice.rvW_sent
#print axioms OnBytes.Slice.getD_of_drop
