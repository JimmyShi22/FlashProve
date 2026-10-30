-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/PieceOfSilence.lean: the proofs of the three statements of
Johnson/P1K8R/PieceOfSilenceStatement.lean, to the letter, and one helper. Lemmas; none of the
library's goals.

How. `look_point`: the key side's last point p₀: it has h.v coordinates (`keyPt_size`), none reads
as 0 or 1 (`keyPt_fine`), and g.e and g.zk are written in it (`look_e`, `look_zk`, with the
agreement): all four of Johnson/P1K8R/DigitsOfSilence.lean. The first two statements: as that file's
`digits_of_silence` goes: a call's key point is two stretches of p₀ in a row (`mem_extract`,
Johnson/Desc/K8/Honest/DigitsLiveOf.lean); a call's weight reads coordinates of a stretch of p₀
(`callWeight_ne`). The third: the first clause of `PieceLive` by the equation and the second
statement; the two others by `eqAtNe` and `eqPlainFNe` (Johnson/Desc/K8/Honest/PieceLiveOf.lean) at
the first statement, read by number through `getD_mem`.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.P1K8R.PieceOfSilenceStatement
import Johnson.Desc.K8.Honest.PieceLiveOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open ProofFile.Honest.K3 (goodK3Out lookHeardAt OpenSame)

/-- The key side's last point, with what the two statements spend of it. -/
theorem look_point (h : Forest.Shape) (g : Forest.Heard) (own : List Fmt.Drawn)
    (ho : OpenSame g (lookHeardAt h 0 own)) (hs : goodK3Out (K3.faceOf h) own = true)
    (hl : 0 < h.v) (hord : ProdV.orderOk (h.v - 1) (K3.keyOrders h (h.v - 1)) = true) :
    ∃ p₀ : Array E, p₀.size = h.v ∧ (∀ w ∈ p₀.toList, Fine w) ∧
      g.e = (Array.range h.NC).map (Forest.callWeight h (p₀.extract h.dT p₀.size)) ∧
      g.zk = (Array.range h.NC).map fun c =>
        ((p₀.extract h.dT p₀.size).extract (h.rK - h.iota.getD c 0)
          (p₀.extract h.dT p₀.size).size) ++ p₀.extract 0 h.dT := by
  obtain ⟨m, hv⟩ : ∃ m, h.v = m + 1 := ⟨h.v - 1, by omega⟩
  have hm : h.v - 1 = m := by omega
  rw [hm] at hord
  exact ⟨_, keyPt_size h own m hv, keyPt_fine h own m hv hord hs, ho.e.trans (look_e h own),
    ho.zk.trans (look_zk h own)⟩

/-- **No coordinate of a call's key point reads as 0 or as 1.** -/
theorem look_zk_fine : LookZkFine := by
  intro h g own ho hs hl hord q hq w hw
  obtain ⟨p₀, -, hfine, -, hk⟩ := look_point h g own ho hs hl hord
  rw [hk, map_range_getD _ _ _ _ hq, Array.toList_append] at hw
  rcases List.mem_append.1 hw with hw | hw
  · exact hfine _ (K8.Honest.mem_extract _ _ _ _ (K8.Honest.mem_extract _ _ _ _ hw))
  · exact hfine _ (K8.Honest.mem_extract _ _ _ _ hw)

/-- **No call's weight reads as 0.** -/
theorem look_e_ne : LookENe := by
  intro h g own ho hs hl hord q hq
  obtain ⟨p₀, hsize, hfine, he, -⟩ := look_point h g own ho hs hl hord
  have hvd : h.v = h.dT + h.rK := rfl
  rw [he, map_range_getD _ _ _ _ hq]
  refine callWeight_ne _ _ _ fun i hi => ?_
  have hsz : (p₀.extract h.dT p₀.size).size = h.rK := by
    rw [Array.size_extract, hsize]
    omega
  exact hfine _ (K8.Honest.mem_extract _ _ _ _ (getD_mem _ i (by omega)))

/-- **`PieceLive` where the lookup's second test says yes.** -/
theorem piece_of_silence : PieceOfSilence := by
  intro tl g own W ho hs K hc hH w hw
  have hq : w.call < tl.f9.NC := Nat.lt_of_lt_of_le (hc w hw) K.calls
  have hz : ∀ v, v < (g.zk.getD w.call #[]).size →
      Reading.gl.val ((g.zk.getD w.call #[]).getD v zeroE) ≠ 0 ∧
        Reading.gl.val ((g.zk.getD w.call #[]).getD v zeroE) ≠ 1 := fun v hv =>
    look_zk_fine tl.f9 g own ho hs K.level K.order w.call hq _ (getD_mem _ v hv)
  refine ⟨?_, fun cc _ => K8.Honest.eqAtNe _ _ cc hz, fun r _ => K8.Honest.eqPlainFNe _ _ hz⟩
  rw [← hH w hw]
  exact look_e_ne tl.f9 g own ho hs K.level K.order w.call hq

end P1K8

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms P1K8.look_point
#print axioms P1K8.look_zk_fine
#print axioms P1K8.look_e_ne
#print axioms P1K8.piece_of_silence
