-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Gated.lean: THE LAYERS' OWN ROUNDS (K4): hearGated RETURNS
(OnBytes/Desc/First/K4/Hear.lean: the two product layers of the gated products). A general law:
nothing is evaluated.

  rowsGated, slotsGated   the rows of K4's table that it hears; the slots that it takes.
  orderRange_ok, downFrom_size   the order of a gated layer's rounds at nine variables or more; a
                  size.
  GatedLeft       what it leaves: the numbers of challenges; the end values' slots by number; every
                  slot that it takes is filled.
  **hearGated_returns**   room, a tape of its rows' shape, the second token sumcheck is there, four
                  comparisons of numbers, and the batched sumcheck's values of the never-sent
                  vectors have been shown. It has no test on values.

Limits. A conditional law. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.K4.Returns.Stack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc D6.Ret
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.PscRun (Sized Filled)

/-- The rows of K4's table that hearGated hears: its number 6. -/
def rowsGated (P : Pub) : List Rd :=
  layerRds P.rd.muH ++ ([pointRd .join (P.y.h.ll - 1)] ++ layerRds P.rd.muH2)

/-- The slots that hearGated takes. -/
def slotsGated (P : Pub) : Nat := (1 + (2 * P.rd.muH + (2 + 2))) + (1 + (2 * P.rd.muH2 + (2 + 2)))

/-- The order of a gated layer's rounds, at nine variables or more. -/
theorem orderRange_ok {mu : Nat} (h : 9 ≤ mu) :
    (orderRange mu).length = mu ∧ ∀ v ∈ orderRange mu, v < mu := by
  unfold orderRange
  refine ⟨by simp; omega, fun v hv => ?_⟩
  rcases List.mem_append.1 hv with h1 | h1
  · have : v ≤ 8 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
      omega
    omega
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h1
    have : x < mu - 9 := by simpa using hx
    omega

/-- The challenges of the lowest n bits, turned round: their number. -/
theorem downFrom_size (rs : Array E) (n : Nat) : (downFrom rs n).size = min n rs.size := by
  unfold downFrom
  simp

/-- What hearGated leaves. -/
structure GatedLeft (P : Pub) (F G : Fork) (hd hd2 : Level) : Prop where
  r : hd.r.size = P.rd.muH
  r2 : hd2.r.size = P.rd.muH2
  ends : Filled G hd.sL ∧ Filled G hd.sR ∧ Filled G hd2.sL ∧ Filled G hd2.sR
  sR : hd.sR = hd.sL + 1 ∧ hd2.sR = hd2.sL + 1
  sL : hd.sL = F.next + (1 + (2 * P.rd.muH + 2)) ∧
    hd2.sL = F.next + (1 + (2 * P.rd.muH + (2 + 2))) + (1 + (2 * P.rd.muH2 + 2))
  /-- every slot that it takes is filled -/
  marks : ∀ j, F.next ≤ j → j < G.next → Filled G j

/-- **hearGated returns.** -/
theorem hearGated_returns (P : Pub) (H : Heard) (K : HeardStack) {tT : Tsc} {F : Fork} {k : Nat}
    (hR : Room F (slotsGated P + k)) {t : Tape} (hT : TapeOf (rowsGated P) t) (u : Tape)
    (htT : H.tT = some tT)
    -- numbers: two of the plan alone; two hold the plan's against sizes of what was heard
    (h9 : 9 ≤ P.rd.muH) (h9' : 9 ≤ P.rd.muH2)
    (hmu : P.rd.muH ≤ min K.fin.wD K.rs.size + H.ztF.size)
    (hmu' : P.rd.muH2 ≤ (P.y.h.ll - 1) + min P.y.lfe K.rs.size + tT.r.size)
    -- what the batched sumcheck has shown
    (hs : ∀ i, i < 1 + P.y.LamM → K.sH1 + i < F.next ∧ Filled F (K.sH1 + i)) :
    ∃ hd hd2 G, hearGated engFl P H K F (t ++ u) = some ((hd, hd2), G, u) ∧ Room G k ∧
      Below F G ∧ G.next = F.next + slotsGated P ∧ GatedLeft P F G hd hd2 := by
  unfold rowsGated at hT
  unfold slotsGated at hR
  obtain ⟨t1, r1, rfl, h1, hT⟩ := tape_append hT
  obtain ⟨t2, t3, rfl, h2, h3⟩ := tape_append hT
  simp only [List.append_assoc]
  obtain ⟨o1, o2⟩ := orderRange_ok h9
  obtain ⟨o1', o2'⟩ := orderRange_ok h9'
  have hs0 := hs 0 (by omega)
  rw [Nat.add_zero] at hs0
  obtain ⟨hd, G1, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := levelIn_tape (F := F)
    (mu := P.rd.muH)
    (k := (1 + (2 * P.rd.muH2 + (2 + 2))) + k) (by refine hR.mono ?_; omega)
    (shown_slot hs0.1 hs0.2) (downFrom K.rs K.fin.wD ++ H.ztF) (orderRange P.rd.muH) o1
    (fun v hv => ⟨o2 v hv, by
      rw [Array.size_append, downFrom_size]
      have := o2 v hv
      omega⟩) h1 (t2 ++ (t3 ++ u))
  obtain ⟨rhoM, b1, b1s⟩ := point_tape (r := .join) rfl h2 G1 (t3 ++ u)
  obtain ⟨hd2, G2, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := levelIn_tape (F := G1)
    (mu := P.rd.muH2)
    (k := k) (by refine a2.mono ?_; omega)
    (C := (List.range P.y.LamM).foldl
      (fun (C : Aff) lm => C.addMul (Aff.slot (K.sH1 + 1 + lm)) ((eqTab rhoM).getD lm zeroE)) aff0)
    (shown_foldl (fun lm => Aff.slot (K.sH1 + 1 + lm)) _ _ _ (shown_const G1 _) fun lm hlm => by
      have := hs (1 + lm) (by have := List.mem_range.1 hlm; omega)
      rw [← Nat.add_assoc] at this
      exact (shown_slot this.1 this.2).below a3)
    (rhoM ++ downFrom K.rs P.y.lfe ++ tT.r) (orderRange P.rd.muH2) o1'
    (fun v hv => ⟨o2' v hv, by
      rw [Array.size_append, Array.size_append, downFrom_size, b1s]
      have := o2' v hv
      omega⟩) h3 u
  have l1 : hd.sL < G1.next := by omega
  have l2 : hd.sR < G1.next := by omega
  refine ⟨hd, hd2, G2, ?_, c2, a3.trans c3, by unfold slotsGated; omega,
    ⟨a9, c9, ⟨(c3.same _ l1).2 a7, (c3.same _ l2).2 a8, c7, c8⟩, ⟨a6, c6⟩,
      ⟨a5, by rw [c5, a4]⟩, fun j h1 h2 => by
        by_cases q : j < G1.next
        · exact (c3.same j q).2 (a10 j h1 q)
        · exact c10 j (by omega) h2⟩⟩
  unfold hearGated
  refine bindR a1 ?_
  refine bindR (needR htT _ _) ?_
  refine bindR b1 ?_
  refine bindR c1 ?_
  rfl

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.orderRange_ok
#print axioms OnBytes.Desc.First.K4.Rt.downFrom_size
#print axioms OnBytes.Desc.First.K4.Rt.hearGated_returns
