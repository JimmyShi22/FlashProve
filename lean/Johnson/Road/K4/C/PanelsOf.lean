-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/PanelsOf.lean: CONDITIONAL. Statements with their proofs.

What is here. The layers' own rounds (sub-protocol K4), the prover's side: THE VERIFIER's PANELS, AS
THE TWO JOBS THAT SHARE THEM ASK FOR THEM, ARE MADE (`Sides.panels`,
Johnson/Desc/K4/Honest/Sides.lean), at all values sh, of the stated number, in the place of what the
second token sumcheck has shown. With the return: the places' number has the plan's number of bits;
the claims' tables are as many as the panels count weight claims, and as many as the plan counts;
the verifier's `stackEnd` returns over these placed panels at all values of the plan's sizes.
FROM: that `Sides.of` has returned; the two public facts under which the structure that the forms
read is made (hU, hl); one test with code on public data, `pansB`
(Johnson/Desc/First/K4/Returns/Pub/PansB.lean), at the plan's own arguments.
How. `pans_of_B` (that file) has the panels, the two comparisons and `stackEnd` at every structure
of the blank one's layout, tables and number of columns. The library's `claims_of_panels`
(Johnson/Road/FormsKeysFold.lean): the panels count as many weight claims as the verifier's list
has; the honest side makes one table for each.

Not shown here. THAT `pansB` IS TRUE: PansBPlan.lean has it from the verifier's lines and five facts
on the plan; it is not called here. That `Sides.of` returns (SidesOf.lean). RETURNS AND NUMBERS
ALONE: nothing on what a panel's side is worth. Nothing on soundness, on completeness or on any
other property. No property is claimed.

  `optMapM_len`, `optAmapM_size`   a walk that returns returns as many
  `panels_return`   **the panels are made**
-/
import Johnson.Road.K4.C.TermsAtOf
import Johnson.Road.K4.C.TriPlain
import Johnson.Road.K4.C.StackPanelsAt
import Johnson.Road.K4.C.RowMapsOf
import Johnson.Desc.First.K4.Returns.Pub.Hear

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (TableAsk TableAt layTables tableAsks nEndT panelsA panelsT placePanels
  stackEnd)
open OnBytes.Desc.First.K4.RtPub (pansB blankEnv nclpOf pans_of_B)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In Pts Sides matsOf)

/-- A walk that returns returns as many. -/
theorem optMapM_len {α β : Type} {g : α → Option β} :
    ∀ (l : List α) (L : List β), l.mapM g = some L → L.length = l.length
  | [], L, h => by
    obtain rfl : [] = L := Option.some.inj h
    rfl
  | x :: l, L, h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨M, hM, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl : b :: M = L := Option.some.inj h
    rw [List.length_cons, List.length_cons, optMapM_len l M hM]

/-- The same over an array. -/
theorem optAmapM_size {α β : Type} {g : α → Option β} {a : Array α} {b : Array β}
    (h : a.mapM g = some b) : b.size = a.size := by
  rw [Array.mapM_eq_mapM_toList] at h
  obtain ⟨L, hL, e⟩ := Option.map_eq_some_iff.1 h
  rw [← e, List.size_toArray, optMapM_len _ _ hL, Array.length_toList]

variable {Q : K4Pub} {w : K4In} {p : Pts} {S : Sides} {iU3 : ℕ}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- CONDITIONAL on every hypothesis named. **THE PANELS ARE MADE**, with their numbers, and the
verifier's `stackEnd` returns over them. -/
theorem panels_return (hS : Sides.of Q w p = some S) (hU : Q.hp.tl.ix.U.getD 2 none = some iU3)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hPB : pansB Q.P (blankEnv Q.P Q.hp Q.g iU3 r.1) Q.hp.lamS (nclpOf Q.hp Q.g) = true)
    {sh : Array E} (hsh : sh.size = nEndT Q.P.y) :
    ∃ pans, panelsT (sidesEnv S sh) S.TS (panelsA (sidesEnv S sh) {}) = some pans ∧
      S.panels sh = some (placePanels pans.bl) ∧
      ceilLog2 (placePanels pans.bl).2 = Q.hp.lamS ∧ S.opens.size = pans.nextV ∧
      pans.nextV = nclpOf Q.hp Q.g ∧
      ∀ (rs om H1 V : Array E) (a b : E), rs.size = Q.hp.lamS → om.size = 2 →
        H1.size = 1 + Q.P.y.LamM → V.size = nclpOf Q.hp Q.g →
        ∃ fin, stackEnd Q.P.y (placePanels pans.bl).1 rs Q.hp.lamS om H1 V a b = some fin := by
  obtain ⟨_, _, _, hv, _, hTS, _⟩ := sides_fields hS
  have ev : S.v = envPub Q r.1 iU3 p.fo.zk := Option.some.inj (hv.symm.trans (envOf_pub hU hl p))
  have hy : S.v.y = Q.P.y := by rw [ev]; rfl
  obtain ⟨TS, hTS', hall⟩ := pans_of_B (v := S.v) (by rw [ev]; exact ⟨rfl, rfl, rfl⟩) hPB
    { fo := S.fo, PV := #[], ztF := S.zt, sW := 0, gp := #[], wpl := {}, sPv := 0, omV := #[],
      tV := {}, tT := some {} }
  obtain rfl : TS = S.TS := Option.some.inj (hTS'.symm.trans hTS)
  obtain ⟨pans, hp, h1, h2, h3⟩ := hall sh hsh
  have hp' : panelsT (sidesEnv S sh) S.TS (panelsA (sidesEnv S sh) {}) = some pans := by
    unfold sidesEnv
    rw [hy]
    exact hp
  obtain ⟨cls, hc, ho, hcv, _⟩ := sides_claims hS
  have hn : pans.nextV = cls.length :=
    (claims_of_panels (sidesEnv S sh) S.ce hcv.symm S.TS hp' hc).1
  have hsz : S.opens.size = cls.length := by
    rw [optAmapM_size ho, List.size_toArray]
  refine ⟨pans, hp', ?_, eq_of_beq h1, hsz.trans hn.symm, eq_of_beq h2, h3⟩
  have e : S.panels sh =
      (panelsT (sidesEnv S sh) S.TS (panelsA (sidesEnv S sh) {})).bind fun pans =>
        if (pans.nextV != S.opens.size) = true then none else some (placePanels pans.bl) := rfl
  rw [e, hp', Option.bind_some, if_neg (by simp [hsz, hn])]

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.optMapM_len
#print axioms OnBytes.Road.K4.C.optAmapM_size
#print axioms OnBytes.Road.K4.C.panels_return
