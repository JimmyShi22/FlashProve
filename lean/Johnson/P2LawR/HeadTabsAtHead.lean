-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P2LawR/HeadTabsAtHead.lean: TWO TESTS ON THE TABLES OF THE LOOKUP ON THE OUTPUT HEAD's
CALLS, AS THEOREMS UNDER THE HEAD: `rowsOk (rowH x) = true` and "each call's table has the kind's
number of rows" (the fields rows and bits of `HeadTabs`,
Johnson/Desc/First/Look/K3CallerHeadParts.lean). Statements and proofs. A joining, and some
arithmetic.

How. NO ROW IS EVALUATED. Both tests read of the place x its shape's calls alone, and the first the
number F of the kind's sizes. Under the head the place's shape is the layout's (`headAt_fs`,
Johnson/Desc/Kinds/Law/TabIsEXInScope.lean); the layout is what `Head.layout` returns at the written
table of the clamp (`layoutW_of_public`, Johnson/Road/HeadPub.lean); its six calls are written
(`layout_fs`, `lookups_is`, Johnson/Desc/Kinds/Law/HeadFsWritten.lean; `calls_six`,
Johnson/Goal/Meaning/HeadColsScope.lean); a call's table goes by its kind; the three numbers of
which the table of exponentials is made are 24, 8 and 4 (`numbers_in_scope`,
Johnson/Goal/Meaning/HeadCondScope.lean); that table's and the clamp's rows are closed forms
(`tauFE_getD`, `rowFE`, `tauFCw`, Johnson/Road/HeadTabs.lean).

  `lookOne_tau_FC`, `lookOne_tau_R16`, `lookOne_tau_R8`, `lookOne_k_at`: a call's table and table
    bits, by its kind.
  `cl_six`: the six records of a layout whose call lines are the stored example's.
  `kOf_getD`, `bits_of_layout`: the table bits. `tauN_none`, `tauN_some`, `rows_of_layout`: the
    rows.
  `exG_pos`, `rowFE_parts`, `rowFE_zero`, `rowFC_clamp`: arithmetic on the two closed forms.
  `rowsOk_of`: the test's yes from equations on the rows. `rowsOk_rejects`, `bits_rejects`: each
    test says no where one row, or one call's table bits, is bent.
  `lines_at_head`; `hbits_at_head`, `hrows_at_head`: MAIN.

Limits. Facts on public parameters alone. The head is a premise: a member of the head is proved at
`storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). The full size
alone. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Kinds.Law.TabIsEXInScope
import Johnson.Desc.Kinds.Law.HeadFsWritten
import Johnson.Road.HeadPub
import Johnson.Desc.First.Look.K3LettersAt
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.K3

open OnBytes.Model (Call CallD place Forest.Shape)
open OnBytes.Model.Head (Shape HL tauFEOf)
open OnBytes.Road.Hd (tauFCw rowFE)
open Inst.Model (exG)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Desc.Kinds.Head.Law.InScope
open VerifiableInference.OnPublicFiles (k3SizesAt k3PolicyAt)

/-! ### a call's table and table bits, by its kind -/

/-- A call of the kind "FC" bears the table that is handed in for that kind. -/
theorem lookOne_tau_FC (h : Shape) (a b : Array UInt64) (c : CallD) (hk : c.kind = "FC") :
    (lookOne h a b c).tau = some a := by
  unfold lookOne
  dsimp only
  rw [hk]
  rfl

/-- A call of the kind "R16" bears no table. -/
theorem lookOne_tau_R16 (h : Shape) (a b : Array UInt64) (c : CallD) (hk : c.kind = "R16") :
    (lookOne h a b c).tau = none := by
  unfold lookOne
  dsimp only
  rw [hk]
  rfl

/-- A call of the kind "R8" bears no table. -/
theorem lookOne_tau_R8 (h : Shape) (a b : Array UInt64) (c : CallD) (hk : c.kind = "R8") :
    (lookOne h a b c).tau = none := by
  unfold lookOne
  dsimp only
  rw [hk]
  rfl

/-- A call's table bits, at its kind. -/
theorem lookOne_k_at (h : Shape) (a b : Array UInt64) (c : CallD) (s : String) (hk : c.kind = s) :
    (lookOne h a b c).k = if s == "R8" then 8 else 16 := by
  rw [lookOne_k, hk]

/-! ### the six records -/

/-- **The six records of a layout whose call lines are the stored example's.** -/
theorem cl_six {h : Shape} {tauFC : Array UInt64} {L : HL}
    (hl : OnBytes.Model.Head.callLines h = VerifierAndGoals.Lines.callsHRef)
    (hy : OnBytes.Model.Head.layout h tauFC = .ok L) :
    ∃ (L0 : HL) (fs0 : Forest.Shape), L.fs.calls = L.cl ∧
      L.cl.getD 0 {} =
        { lookOne h tauFC (tauFEOf h.famF h.digSh h.tabS)
            (place "R16a" "R16" [("NF", h.d, false), ("NFH", h.d, false), ("HD0", L0.JV, false)]
              (OnBytes.Model.Head.keyFloor h - h.lt)) with
          iota := fs0.iota.getD 0 0 } ∧
      L.cl.getD 1 {} =
        { lookOne h tauFC (tauFEOf h.famF h.digSh h.tabS)
            (place "R16b" "R16" [("HD1", L0.JV, false)]
              (OnBytes.Model.Head.keyFloor h - h.lt)) with
          iota := fs0.iota.getD 1 0 } ∧
      L.cl.getD 2 {} =
        { lookOne h tauFC (tauFEOf h.famF h.digSh h.tabS)
            (place "R8" "R8" [("ROW", OnBytes.Model.ledNRH h.XL, false), ("HD2", L0.JV, false)]
              (OnBytes.Model.Head.keyFloor h - h.lt)) with
          iota := fs0.iota.getD 2 0 } ∧
      L.cl.getD 3 {} =
        { lookOne h tauFC (tauFEOf h.famF h.digSh h.tabS)
            (place "FEa" "FE" [("HE0", L0.JVa, false)]
              (OnBytes.Model.Head.keyFloor h - h.lt)) with
          iota := fs0.iota.getD 3 0 } ∧
      L.cl.getD 4 {} =
        { lookOne h tauFC (tauFEOf h.famF h.digSh h.tabS)
            (place "FEb" "FE" [("HE1", L0.JV - L0.JVa, false)]
              (OnBytes.Model.Head.keyFloor h - h.lt)) with
          iota := fs0.iota.getD 4 0 } ∧
      L.cl.getD 5 {} =
        { lookOne h tauFC (tauFEOf h.famF h.digSh h.tabS)
            (place "FC" "FC" [("CNF", h.d, false)]
              (OnBytes.Model.Head.keyFloor h - h.lt)) with
          iota := fs0.iota.getD 5 0 } := by
  obtain ⟨L0, calls, fs0, pub, _, h4, _, _, _, hcl, hfs⟩ := layout_fs hy
  have hc := calls_six h4 hl
  refine ⟨L0, fs0, by rw [hfs], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [hcl, lookups_is, hc]
      simp [Array.getD_eq_getD_getElem?]

/-! ### the table bits -/

/-- The table bits of call q, off the record with that number. -/
theorem kOf_getD (s : Forest.Shape) (q : ℕ) : Cb.LdLkp.Port.kOf s q = (s.calls.getD q {}).k := by
  unfold Cb.LdLkp.Port.kOf
  rw [Array.getD_eq_getD_getElem?]
  cases s.calls[q]? <;> rfl

/-- **Each call's table has the kind's number of rows.** -/
theorem bits_of_layout {h : Shape} {tauFC : Array UInt64} {L : HL}
    (hl : OnBytes.Model.Head.callLines h = VerifierAndGoals.Lines.callsHRef)
    (hy : OnBytes.Model.Head.layout h tauFC = .ok L) :
    ∀ c, c < 6 → Cb.LdLkp.Port.kOf L.fs c = bitsOf c := by
  obtain ⟨L0, fs0, hcs, e0, e1, e2, e3, e4, e5⟩ := cl_six hl hy
  intro c hc
  rw [kOf_getD, hcs]
  interval_cases c
  · rw [e0]
    exact (lookOne_k_at _ _ _ _ "R16" rfl).trans (by decide)
  · rw [e1]
    exact (lookOne_k_at _ _ _ _ "R16" rfl).trans (by decide)
  · rw [e2]
    exact (lookOne_k_at _ _ _ _ "R8" rfl).trans (by decide)
  · rw [e3]
    exact (lookOne_k_at _ _ _ _ "FE" rfl).trans (by decide)
  · rw [e4]
    exact (lookOne_k_at _ _ _ _ "FE" rfl).trans (by decide)
  · rw [e5]
    exact (lookOne_k_at _ _ _ _ "FC" rfl).trans (by decide)

/-- The equation fails where call 2's table has 16 bits. -/
theorem bits_rejects (s : Forest.Shape) (h : (s.calls.getD 2 {}).k = 16) :
    Cb.LdLkp.Port.kOf s 2 ≠ bitsOf 2 := by
  rw [kOf_getD, h]
  decide

/-! ### the rows -/

/-- A row of a call without a table. -/
theorem tauN_none {s : Forest.Shape} {q : ℕ} (h : (s.calls.getD q {}).tau = none) {u : ℕ}
    (hu : u < 2 ^ 41) : FoNums.tauN s q u = u := by
  unfold FoNums.tauN
  rw [OnBytes.Road.Hd.tauAt_none h]
  exact UInt64.toNat_ofNat_of_lt' (lt_trans hu (by decide))

/-- A row of a call with a table. -/
theorem tauN_some {s : Forest.Shape} {q : ℕ} {a : Array UInt64}
    (h : (s.calls.getD q {}).tau = some a) (u : ℕ) : FoNums.tauN s q u = (a.getD u 0).toNat := by
  unfold FoNums.tauN
  rw [OnBytes.Road.Hd.tauAt_some h]

/-- **The rows of the six calls' tables**, at the written table of the clamp and the three numbers
24, 8 and 4. -/
theorem rows_of_layout {h : Shape} {L : HL}
    (hl : OnBytes.Model.Head.callLines h = VerifierAndGoals.Lines.callsHRef)
    (hy : OnBytes.Model.Head.layout h tauFCw = .ok L) (hF : h.famF = 24) (hs : h.digSh = 8)
    (hT : h.tabS = 4) :
    ∀ u, u < 2 ^ 16 → FoNums.tauN L.fs 0 u = u ∧ FoNums.tauN L.fs 1 u = u ∧
      FoNums.tauN L.fs 2 u = u ∧ FoNums.tauN L.fs 3 u = rowFE u ∧ FoNums.tauN L.fs 4 u = rowFE u ∧
      FoNums.tauN L.fs 5 u = OnBytes.Model.Layer.rowFC u := by
  obtain ⟨L0, fs0, hcs, e0, e1, e2, e3, e4, e5⟩ := cl_six hl hy
  have t0 : (L.fs.calls.getD 0 {}).tau = none := by
    rw [hcs, e0]
    exact lookOne_tau_R16 _ _ _ _ rfl
  have t1 : (L.fs.calls.getD 1 {}).tau = none := by
    rw [hcs, e1]
    exact lookOne_tau_R16 _ _ _ _ rfl
  have t2 : (L.fs.calls.getD 2 {}).tau = none := by
    rw [hcs, e2]
    exact lookOne_tau_R8 _ _ _ _ rfl
  have t3 : (L.fs.calls.getD 3 {}).tau = some (tauFEOf 24 8 4) := by
    rw [hcs, e3, hF, hs, hT]
    exact lookOne_tau_FE _ _ _ _ rfl
  have t4 : (L.fs.calls.getD 4 {}).tau = some (tauFEOf 24 8 4) := by
    rw [hcs, e4, hF, hs, hT]
    exact lookOne_tau_FE _ _ _ _ rfl
  have t5 : (L.fs.calls.getD 5 {}).tau = some tauFCw := by
    rw [hcs, e5]
    exact lookOne_tau_FC _ _ _ _ rfl
  intro u hu
  have hu' : u < 65536 := hu
  have hw : u < 2 ^ 41 := lt_trans hu (by decide)
  have fe : ((tauFEOf 24 8 4).getD u 0).toNat = rowFE u := by
    rw [OnBytes.Road.Hd.tauFE_getD hu']
    exact UInt64.toNat_ofNat_of_lt' (lt_trans (OnBytes.Road.Hd.rowFE_lt hu') (by decide))
  have fc : (tauFCw.getD u 0).toNat = OnBytes.Model.Layer.rowFC u := by
    unfold OnBytes.Road.Hd.tauFCw
    rw [OnBytes.Road.Hd.getD_map_rangeT _ _ _ _ hu']
    exact UInt64.toNat_ofNat_of_lt' (lt_trans (OnBytes.Road.Hd.rowFC_lt hu') (by decide))
  exact ⟨tauN_none t0 hw, tauN_none t1 hw, tauN_none t2 hw, (tauN_some t3 u).trans fe,
    (tauN_some t4 u).trans fe, (tauN_some t5 u).trans fc⟩

/-! ### arithmetic on the two closed forms -/

/-- The library's running value never falls to 0. -/
theorem exG_pos (u : ℕ) : 1 ≤ exG u := by
  induction u with
  | zero =>
    show 1 ≤ 2 ^ 41
    norm_num
  | succ n ih =>
    show 1 ≤ (exG n * 484 + (2 ^ 32 - 1)) / 2 ^ 32
    omega

/-- A row of the table of exponentials: its low 16 bits are its number; what stands above them lies
from 1 to 2^24. -/
theorem rowFE_parts {u : ℕ} (hu : u < 2 ^ 16) :
    rowFE u % 2 ^ 16 = u ∧ 1 ≤ rowFE u / 2 ^ 16 ∧ rowFE u / 2 ^ 16 ≤ 2 ^ 24 := by
  have h1 := exG_pos u
  have h2 := OnBytes.Road.Hd.exG_le u
  unfold OnBytes.Road.Hd.rowFE
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  generalize exG u = g at h1 h2 ⊢
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- Row 0 of the table of exponentials holds 2^24. -/
theorem rowFE_zero : rowFE 0 / 2 ^ 16 = 2 ^ 24 := by decide

/-- A row of the clamp's table is the kind's own closed form. -/
theorem rowFC_clamp (u : ℕ) : OnBytes.Model.Layer.rowFC u = clampRow u := by
  have e : OnBytes.Model.Layer.rowFC u =
      u + ((if u + 2047 < 32768 then 0 else min (u + 2047 - 32768) (2 * 2047)) + 1) * 2 ^ 28 := rfl
  have c : clampRow u =
      u + 2 ^ 28 * (min (max ((u : Int) - 2 ^ 15) (-2047)) 2047 + 2 ^ 11).toNat := rfl
  rw [e, c]
  split_ifs <;> omega

/-! ### the test on the rows -/

/-- **The test's yes, from equations on the rows.** -/
theorem rowsOk_of [Sizes] (row : ℕ → ℕ → ℕ) (h0 : ∀ u, u < 2 ^ 16 → row 0 u = u)
    (h1 : ∀ u, u < 2 ^ 16 → row 1 u = u) (h2 : ∀ u, u < 2 ^ 8 → row 2 u = u)
    (h3 : ∀ u, u < 2 ^ 16 → row 3 u % 2 ^ 16 = u ∧ 1 ≤ row 3 u / 2 ^ 16 ∧ row 3 u / 2 ^ 16 ≤ 2 ^ F)
    (h4 : ∀ u, u < 2 ^ 16 → row 4 u = row 3 u) (h5 : ∀ u, u < 2 ^ 16 → row 5 u = clampRow u)
    (h30 : row 3 0 / 2 ^ 16 = 2 ^ F) : rowsOk row = true := by
  unfold rowsOk
  rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨⟨fun u hu => ?_, fun u hu => ?_⟩, ?_⟩
  · have hu' := List.mem_range.1 hu
    obtain ⟨a, b, c⟩ := h3 u hu'
    unfold rowsOkAt
    rw [h0 u hu', h1 u hu', h4 u hu', h5 u hu', a]
    simp
    exact ⟨b, c⟩
  · rw [h2 u (List.mem_range.1 hu)]
    simp
  · rw [h30]
    simp

/-- The test says no where row 1 of call 0's table is not 1. -/
theorem rowsOk_rejects [Sizes] (row : ℕ → ℕ → ℕ) (h : row 0 1 ≠ 1) : rowsOk row = false := by
  by_contra hn
  have ht : rowsOk row = true := by
    cases hr : rowsOk row
    · exact absurd hr hn
    · rfl
  unfold rowsOk at ht
  rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true] at ht
  have h1 := ht.1.1 1 (List.mem_range.2 (by norm_num))
  unfold rowsOkAt at h1
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  exact h h1.1.1.1.1.1.1

/-! ### under the head -/

/-- The call lines under the head are the stored example's. -/
theorem lines_at_head {o} {Z} {D} {r} {Zp} {Np} {cF} {x} (h : P5J.AtMgA o Z D r Zp Np cF x) :
    OnBytes.Model.Head.callLines (P5J.At.X Zp).hS = VerifierAndGoals.Lines.callsHRef := by
  have St := VerifiableInference.PlanWritten.publicSteps_of h.pubOne
  have hP := OnBytes.Road.Hd.scan_of_scope h.scope h.reads h.pubOne
  have Zs : SizesH (P5J.At.X Zp).hS := by
    rw [St.hS, hP]
    exact sizesH_scan _ _
  exact Zs.lines

/-- **Each call's table has the kind's number of rows, under the head.** -/
theorem hbits_at_head {o} {Z} {D} {r} {Zp} {Np} {cF} {x} (h : P5J.AtMgA o Z D r Zp Np cF x) :
    ∀ c, c < 6 → Cb.LdLkp.Port.kOf x.fs c = bitsOf c := by
  rw [headAt_fs h.scope h.pubOne h.headAt]
  exact bits_of_layout (lines_at_head h) (OnBytes.Road.Hd.layoutW_of_public h.pubOne)

/-- **The test on the rows accepts, under the head.** -/
theorem hrows_at_head {o} {Z} {D} {r} {Zp} {Np} {cF} {x} (h : P5J.AtMgA o Z D r Zp Np cF x) :
    letI := k3SizesAt (P5J.At.X Zp)
    letI := k3PolicyAt (P5J.At.X Zp)
    rowsOk (rowH x) = true := by
  have N := numbers_in_scope h.scope h.reads h.pubOne
  have R := rows_of_layout (lines_at_head h) (OnBytes.Road.Hd.layoutW_of_public h.pubOne) N.F N.sh
    N.sT
  rw [← headAt_fs h.scope h.pubOne h.headAt] at R
  have hF : @F (k3SizesAt (P5J.At.X Zp)) = 24 := N.F
  refine @rowsOk_of (k3SizesAt (P5J.At.X Zp)) (rowH x) (fun u hu => (R u hu).1)
    (fun u hu => (R u hu).2.1) (fun u hu => (R u (lt_trans hu (by decide))).2.2.1)
    (fun u hu => ?_) (fun u hu => (R u hu).2.2.2.2.1.trans (R u hu).2.2.2.1.symm)
    (fun u hu => (R u hu).2.2.2.2.2.trans (rowFC_clamp u)) ?_
  · rw [hF]
    show FoNums.tauN x.fs 3 u % 2 ^ 16 = u ∧ 1 ≤ FoNums.tauN x.fs 3 u / 2 ^ 16 ∧
      FoNums.tauN x.fs 3 u / 2 ^ 16 ≤ 2 ^ 24
    rw [(R u hu).2.2.2.1]
    exact rowFE_parts hu
  · rw [hF]
    show FoNums.tauN x.fs 3 0 / 2 ^ 16 = 2 ^ 24
    rw [(R 0 (by decide)).2.2.2.1]
    exact rowFE_zero

end P2Law.K3

#print axioms P2Law.K3.lookOne_tau_FC
#print axioms P2Law.K3.lookOne_tau_R16
#print axioms P2Law.K3.lookOne_tau_R8
#print axioms P2Law.K3.lookOne_k_at
#print axioms P2Law.K3.cl_six
#print axioms P2Law.K3.kOf_getD
#print axioms P2Law.K3.bits_of_layout
#print axioms P2Law.K3.bits_rejects
#print axioms P2Law.K3.tauN_none
#print axioms P2Law.K3.tauN_some
#print axioms P2Law.K3.rows_of_layout
#print axioms P2Law.K3.exG_pos
#print axioms P2Law.K3.rowFE_parts
#print axioms P2Law.K3.rowFE_zero
#print axioms P2Law.K3.rowFC_clamp
#print axioms P2Law.K3.rowsOk_of
#print axioms P2Law.K3.rowsOk_rejects
#print axioms P2Law.K3.lines_at_head
#print axioms P2Law.K3.hbits_at_head
#print axioms P2Law.K3.hrows_at_head
