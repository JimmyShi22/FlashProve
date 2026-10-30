--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Second/K08/SeatK8.lean: THE SMALLNESS TEST's 25 SEATED PLACES AND THE 25 WRITTEN ROUNDS
«RNG»:
in the goals' scope, where the verifier's test madePinnedAt accepts, the place that the proof file's
description seats at segment l (ProofFile.k8ParW Z G₀ Xl l, Xl := G₀.built[l]) has the number of columns
of RoomK8.lean's table at l and 128 combinations: so its declared round has the very entry of the
written list's round at the table's position. No other file of this library uses that equation of
entries (round_at_seat, entry_at_seat); tail_at_seat is used in
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeDigitsAt.lean. Definitions, statements,
proofs; three closed facts by Lean's kernel (decide +kernel).
  colsOf V              of a view of the public data's shape: for each segment the sum of its
                        matrices' columns.
  cols_written          colsOf xShapeFull = the table's columns. cols_moved: a negative test.
  tlAt_text             under «attention is there» and «twelve groups»: Look.tlAt's three arms.
  tail_at_seat          InScope P · readFiles P = .ok pp · ProofFile.pubPlain secondHashFunction P.pol lay P.KL = .ok
  Z ·
                        blankBy pureRoad.links Z = some G₀ · l ≤ 24 · G₀.built[l]? = some Xl ⊢
                        Look.tlAt Z.p.X l = some Xl.tl ∧ Xl.tl.tau = 128. By the integer-model
                        thread's
                        ground_tails and the landed scope_plans · tau_layers | tau_attention |
                        tau_head.
  ★ columns_at_seat     these (at lay := P.lay) · madePinnedAt Z.p.X.P Z.p.chains.made Z.first
  Z.made =
                        true ⊢ K8.columns (ProofFile.k8ParW Z G₀ Xl l).toPar = (table.map (·.2)).getD l 0.
                        By
                        the pin's fourth comparison (xShape_in_scope) and tail_of_is.
  ★ entry_at_seat       the same ⊢ (K8.round …).entry = { name := "RNG", trits := ‹that› * 128 }.
  entries_at_positions  at the table's 25 positions proofLit.plan's rounds have just these entries.
  ★ round_at_seat       the same ⊢ ∃ x, table[l]? = some x ∧ the place's columns are x.2 ∧
                        (proofLit.plan.rounds[x.1]?).map (·.entry) = some (K8.round …).entry.
Limits. THAT THE CHAIN's DECLARED ROUND OF THE PLACE STANDS AT THAT POSITION among the description's
declared rounds is not said here (the description's own test on the plan compares the two lists
whole). Of the place: ks and tau alone; nothing on ms, asks, matsIn, readsIn, nU. readFiles' return
and the public part's are premises. At OnBytes.secondHashFunction. Nothing on a reached state. No soundness and
no level is claimed.

-/
import Johnson.Second.K08.RoomK8
import Johnson.IMR.K8Seat
import Johnson.Goal.Numbers.TauInScope
import Johnson.Desc.Ok.PlanWritten.XShapeLaws
import Johnson.Desc.ProofFile.Lot.K8

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Second.K08
open OnBytes OnBytes.Model Johnson.G
open OnBytes.Model.Verify (publicOf)
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc.First (Look.tlAt)
open VerifiableInference.Desc.First.K8 (columns round)
open VerifiableInference.PlanWritten (XShape tailView xShapeOf xShapeIs_of tail_of_is madePinnedAt
  proofLit)
open VerifiableInference.PlanWritten.Joined (xShape_in_scope)

def colsOf (V : XShape) : List ℕ :=
  V.1.map fun o => (o.map fun v => (v.2.1.map fun x => x.2.2).foldl (· + ·) 0).getD 0

theorem cols_written : colsOf xShapeFull = table.map (·.2) := by decide +kernel

theorem cols_moved : decide (colsOf xShapeFull = (table.map (·.2)).drop 1 ++ [0]) = false := by
  decide +kernel

theorem tlAt_text {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12) (k : ℕ) :
    Look.tlAt X k = if k == 2 * 12 then some X.H.tl
      else if k % 2 == 0 then X.G[k / 2]?.map (·.tl) else X.A[k / 2]?.map (·.seam.tl) := by
  unfold Look.tlAt
  simp only [h4, hN, if_true]

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}
  {l : ℕ} {Xl : LinkH}

theorem tail_at_seat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) (hl : l ≤ 24)
    (hX : G₀.built[l]? = some Xl) : Look.tlAt Z.p.X l = some Xl.tl ∧ Xl.tl.tau = 128 := by
  have eW : G₀.W = Z.p.X := ProofFile.Law.blankBy_W hG
  have hW : publicOf P.pol P.KL (some lay) = .ok Z.p.X := by
    rw [← eW]
    exact IM.ground_publicK hZ hG
  obtain ⟨h4, hN, -, -⟩ := Meaning.scope_plans hS hR hW
  obtain ⟨tails, l24, e24, t24, -⟩ := IM.ground_tails hS hR hZ hG
  rw [tlAt_text h4 hN]
  by_cases h24 : l = 24
  · subst h24
    obtain rfl : l24 = Xl := Option.some.inj (e24.symm.trans hX)
    rw [eW] at t24
    refine ⟨?_, by rw [t24]; exact Meaning.Tau.tau_head hS hR hW⟩
    rw [if_pos (by decide), t24]
  · obtain ⟨g, hg⟩ : ∃ g, l = 2 * g ∨ l = 2 * g + 1 := ⟨l / 2, by omega⟩
    have hg12 : g < 12 := by omega
    obtain ⟨hp, a, x, x', ehp, ea, ex, etl, -, -, -, -, ex', etl', -⟩ := tails g hg12
    rw [eW] at ehp ea
    rcases hg with rfl | rfl
    · obtain rfl : x = Xl := Option.some.inj (ex.symm.trans hX)
      refine ⟨?_, by rw [etl]; exact Meaning.Tau.tau_layers hS hR hW ehp⟩
      rw [if_neg (by rw [beq_iff_eq]; omega), if_pos (by rw [beq_iff_eq]; omega),
        (by omega : 2 * g / 2 = g), ehp, etl]
      rfl
    · obtain rfl : x' = Xl := Option.some.inj (ex'.symm.trans hX)
      refine ⟨?_, by rw [etl']; exact Meaning.Tau.tau_attention hS hR hW ea⟩
      rw [if_neg (by rw [beq_iff_eq]; omega), if_neg (by rw [beq_iff_eq]; omega),
        (by omega : (2 * g + 1) / 2 = g), ea, etl']
      rfl

/-- ★ -/
theorem columns_at_seat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol P.lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) (hl : l ≤ 24)
    (hX : G₀.built[l]? = some Xl) :
    columns (ProofFile.k8ParW Z G₀ Xl l).toPar = (table.map (·.2)).getD l 0 := by
  have hx : xShapeOf Z.p.X = xShapeFull := xShape_in_scope (o := OnBytes.secondHashFunction) hS hZ hy
  have t := tail_of_is (xShapeIs_of hx) (k := l) (by omega)
  rw [(tail_at_seat hS hR hZ hG hl hX).1] at t
  rw [← cols_written]
  unfold colsOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, t]
  show (Xl.tl.mats.toList.map (·.k)).foldl (· + ·) 0 =
    ((Xl.tl.mats.toList.map fun x => (x.aId, x.m, x.k)).map fun x => x.2.2).foldl (· + ·) 0
  rw [List.map_map]
  rfl

/-- ★ -/
theorem entry_at_seat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol P.lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) (hl : l ≤ 24)
    (hX : G₀.built[l]? = some Xl) :
    (round (ProofFile.k8ParW Z G₀ Xl l).toPar).entry =
      { name := "RNG", trits := (table.map (·.2)).getD l 0 * 128 } := by
  show ({ name := "RNG", trits := columns (ProofFile.k8ParW Z G₀ Xl l).toPar * Xl.tl.tau } :
    Fmt.Entry) = _
  rw [columns_at_seat hS hR hZ hG hy hl hX, (tail_at_seat hS hR hZ hG hl hX).2]

theorem entries_at_positions :
    (table.map fun x => (proofLit.plan.rounds[x.1]?).map (·.entry)) =
      table.map fun x => some { name := "RNG", trits := x.2 * 128 } := by decide +kernel

/-- ★ -/
theorem round_at_seat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol P.lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) (hl : l ≤ 24)
    (hX : G₀.built[l]? = some Xl) :
    ∃ x, table[l]? = some x ∧ columns (ProofFile.k8ParW Z G₀ Xl l).toPar = x.2 ∧
      (proofLit.plan.rounds[x.1]?).map (·.entry) =
        some (round (ProofFile.k8ParW Z G₀ Xl l).toPar).entry := by
  have hlen : l < table.length := by
    have : table.length = 25 := rfl
    omega
  have hx : table[l]? = some table[l] := List.getElem?_eq_getElem hlen
  have hc : (table.map (·.2)).getD l 0 = table[l].2 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hx]
    rfl
  refine ⟨table[l], hx, by rw [columns_at_seat hS hR hZ hG hy hl hX, hc], ?_⟩
  rw [entry_at_seat hS hR hZ hG hy hl hX, hc]
  exact List.map_inj_left.1 entries_at_positions table[l] (List.getElem_mem hlen)

end Second.K08

#print axioms Second.K08.cols_written
#print axioms Second.K08.cols_moved
#print axioms Second.K08.tlAt_text
#print axioms Second.K08.tail_at_seat
#print axioms Second.K08.columns_at_seat
#print axioms Second.K08.entry_at_seat
#print axioms Second.K08.entries_at_positions
#print axioms Second.K08.round_at_seat
