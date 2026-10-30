-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/ReadsQuietSame.lean: a yardstick beside Johnson/Desc/K8/ReadsQuiet.lean: the closing
as it is written there (closed, over Johnson/Desc/First/K8/Order.lean's close and front) gives, at
every argument, the verdict and the record of the closing as it was written before (closedOld, over
Johnson/Top/H0/L3/Frame.lean's closeStep and drawFront). The refusals' names part.

No running text imports this file.

So do the head's tables (tables, over Johnson/Desc/Own/HeadTabs.lean's five makers) and the tables
as they were written before (tablesOld, over the program's five): there the refusals' names are this
text's own, and they are the same: one value.

Main names: closedOld, closed_same; planned_same; tablesOld, tables_same.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Desc.First.K8.OrderAgrees
import Johnson.Desc.Own.HeadTabsAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K8.ReadsQuiet
open OnBytes OnBytes.Model OnBytes.Model.Head
open VerifiableInference.Desc (need named)
open VerifiableInference.Desc.First.K8 (Order.close Order.front Order.orderOk Order.orderOk_eq)

/-- The closing as it was written before, to the letter. F, the sub-proof's engine, went into the
frame's record and was read by neither function. -/
def closedOld (tl : HTailF2) (funs : Array HFun) (L : LinkCtx) (F : Fork) (st : Statement) :
    Except String HTailF2 := do
  let s ← L3.closeStep funs (⟨L, F, tl, ()⟩ : L3.St Unit)
  L3.drawFront s.tl s.L st
  pure s.tl

/-- **The two closings give one verdict and one record**, whatever F is. -/
theorem closed_same (tl : HTailF2) (funs : Array HFun) (L : LinkCtx) (F : Fork) (st : Statement) :
    (closed tl funs L st).toOption = (closedOld tl funs L F st).toOption := by
  unfold closed closedOld Order.close Order.front L3.closeStep HTailF2.closeFuns L3.drawFront
  simp only [Order.orderOk_eq]
  by_cases h1 : tl.funClosed <;> by_cases h2 : tl.shp.size = tl.NM <;>
    by_cases h3 : L3.orderGuard { tl with funClosed := true, funs := funs } L st <;>
    simp [h1, h2, h3, bind, Except.bind, pure, Except.pure, Except.toOption]

/-- The test on the plan is the one that was written before. -/
theorem planned_same (tl : HTailF2) : planned tl = (tl.funOpen && tl.shp.size == tl.NM) := rfl

theorem under_named {α : Type} (n : String) (x : Except String α) :
    under n x = named n x.toOption := by
  cases x <;> rfl

/-- The head's tables as they were written before, to the letter but for the refusals' words. -/
def tablesOld (h : Shape) (L : HL) (hp : HPlanH2) (cov : Covered) (x : Heard) :
    Except String Tables := do
  need "tables: the plan's list of tables is closed already" hp.tl.funOpen
  let mats := hp.tl.mats
  let iHF := 0
  let iHD := h.NHf
  let iHR := iHD + 1
  let iBH := iHR + 1
  let iXL := iBH + 1
  let La := 2 ^ h.la
  let ZV ← under "tables: the squares' point has fewer than la coordinates" (lastOf x.wpl.r h.la)
  let lowN ← under "tables: the norm's point has fewer than ls coordinates"
    (cutLast (zjOf L x.g1 x.qN) h.ls)
  let YN := longPoint lowN.2 x.tN.r
  need "tables: the long point has not la = ls + lt coordinates"
    (YN.size == h.la && h.la == h.ls + h.lt)
  let (phiC, _, rhoCv) := costWeights cov (ztOf h L x.g1 x.qH)
  -- weight 1 on each of a block's S2 features, phiC on the positions
  let phiZ := (Array.range La).map fun i => phiC.getD (i % h.T) zeroE
  let qFC ← named "tables: no call has a segment CNF" (callNo L "CNF")
  let qROW ← named "tables: no call has a segment ROW" (callNo L "ROW")
  let mb := 2 ^ h.lmbH
  let b0 ← named "tables: the lookup's plane 0 is not there" (Forest.phiB x.g1 h.lmbH 0)
  let b1 ← named "tables: the lookup's plane 1 is not there" (Forest.phiB x.g1 h.lmbH 1)
  let asks : List (Nat × Nat × Nat × Array E × String) := [
    (iHF, h.NHf, La, longPhi x.Zl h.ls h.lt, "hf@Z"),
    (iHF, h.NHf, La, phiZ, "hf@phiZ"),
    (iXL, 1, La, longPhi ZV h.ls h.lt, "xbL@Z_V"),
    (iXL, 1, La, longPhi YN h.ls h.lt, "xbL@Y_N"),
    (iHD, 1, h.T, eqTab (ztOf h L x.g1 qFC), "hd@zt_FC"),
    (iHD, 1, h.T, eqTab x.tH.r, "hd@r_H"),
    (iHR, 1, h.T, eqTab (ztOf h L x.g1 qROW), "hr@zt_ROW"),
    (iHR, 1, h.T, eqTab x.PV, "hr@P_V"),
    (iHR, 1, h.T, eqTab x.tV.r, "hr@r_tV"),
    (iHR, 1, h.T, eqTab x.tN.r, "hr@rt_N"),
    (iHR, 1, h.T, phiC, "hr@phiC"),
    (iHR, 1, h.T, rhoCv, "hr@rhoC"),
    (iBH, 1, mb, b0, "bH-bits-0"),
    (iBH, 1, mb, b1, "bH-bits-1"),
    (iBH, 1, mb, Forest.phiP h.lmbH, "bH-pin")]
  let t ← named "tables: a table is empty"
    (asks.foldlM (fun t a => addFun mats t a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) {})
  need "tables: they do not fill the vector of reads" (t.p == hp.nU.getD 2 0)
  pure t

/-- **The two writings of the head's tables are one function.** -/
theorem tables_same (h : Shape) (L : HL) (hp : HPlanH2) (cov : Covered) (x : Heard) :
    tables h L hp cov x = tablesOld h L hp cov x := by
  unfold tables tablesOld HTailF2.funOpen
  simp only [under_named, Own.tailOf_agrees, Own.cutTail_agrees, Own.callWith_agrees,
    Own.planeWeights_agrees, Own.tableAdded_agrees]

end VerifiableInference.Desc.K8.ReadsQuiet
