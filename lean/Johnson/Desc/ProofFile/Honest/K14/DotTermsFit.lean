-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/DotTermsFit.lean: kind K14: "K14, second part" (the place
⟨3, none, 0, .K14⟩): THE TERMS OF THE ROW (Dot) FIT THEIR PLACES: the last test of secondRest5
(Honest/K14/OmegaJoin.lean), "addRow: the terms fit their places", from facts on the state in front.
Statements with their proofs. No definition.

  dot_small       both tables of the row (Dot) have at most 63 index bits, where the library's test
                  linOk accepts (in the description's own letters by the library's linFits_eq,
                  Johnson/Desc/Own/LinAgree.lean): Omega's by the library's omega_has_room
                  (Johnson/Desc/Own/LinMeans.lean) and roomCan_iff; W's is the library's shape_small
                  (Johnson/Desc/K13/Honest/FromShape.lean), called
  dot_terms_fit   **where the taking-over and linDotRow return, each term of the row is in order and
                  fits its place in the own group behind the taking-over.** Which terms there are:
                  dot_blocks (Honest/K14/CutBlocks.lean) with the library's mem_addLaid
                  (Johnson/Desc/K14/Honest/YesCut.lean). In order: onTable_tensorInOrder
                  (Honest/K14/OnTableOk.lean). The places: the library's takeOver_says
                  (Johnson/Desc/Third/Law/Says.lean), placedDot_of_seated
                  (Johnson/Desc/K14/Law/PlacedDot.lean), placeFits_of
                  (Johnson/Desc/K13/Honest/RowsAccept.lean) and its laws on an insertion into an
                  array and on a filter's size (Johnson/Desc/Third/Law/Later.lean). The taking-over
                  leaves the codes: the library's carries_takeOver
                  (Johnson/Desc/Third/Law/Keeps.lean)

THE PREMISES OF dot_terms_fit, beside the two returns: the border's weights each have a block's form
and do not reach beyond the matrix's rows (so each cut returns the weight as it is) · each passes
Tensor.ok · linOk at the state's codes · the shared point has kCol coordinates · Omega, in the
shared chain's last statement, has the plan's shape · W is in the state's statement with the plan's
shape, and among the own group's members. NONE IS SHOWN HERE (Honest/K14/SecondTerms.lean), NOR THAT
THEY CAN HOLD TOGETHER AT ANY STATE.

What is not claimed. That the taking-over or linDotRow returns. The other tests on a new row. That
the sub-protocol accepts. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.OnTableOk
import Johnson.Desc.ProofFile.Honest.K14.CutBlocks
import Johnson.Desc.ProofFile.Honest.K14.OmegaJoin
import Johnson.Desc.K14.Law.PlacedDot
import Johnson.Desc.K14.Honest.YesCut
import Johnson.Desc.K13.Honest.RowsAccept
import Johnson.Desc.K13.Honest.FromShape
import Johnson.Desc.Own.LinMeans
import Johnson.Desc.Own.LinAgree
import Johnson.Desc.Third.Law.Says
import Johnson.Desc.Third.Law.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (linDotRow linLayOmega linLayW Tensor Row addLaid linOk oneE negE)
open Desc.Plain (DState)
open VerifiableInference.Desc (Own.tensorInOrder Own.placeFits)
open VerifiableInference.Desc.Ground (has)
open VerifiableInference.Desc.Third (S₃ P₁₄ Border Loc₃ takeOver)
open VerifiableInference.Desc.Third.Law (takeOver_says carries_takeOver)
open VerifiableInference.Desc.Later (mem_insertIdxIfInBounds self_mem_insertIdxIfInBounds
  size_filter_le')
open VerifiableInference.Desc.K13.Honest (placeFits_of)
open Desc.K14.Law (SeatedDot placedDot_of_seated)
open Desc.K14.Honest (mem_addLaid)

/-- Both tables of the row (Dot) have at most 63 index bits, where the library's test on the shape
with its codes accepts. -/
theorem dot_small {codes : OnBytes.Codes} {S : OnBytes.Params.LinShape} (h : linOk codes S = true) :
    (linLayOmega codes S).bits ≤ 63 ∧ (linLayW codes S).bits ≤ 63 := by
  have h' : VerifiableInference.Desc.Own.linFits codes S = true := by
    rw [VerifiableInference.Desc.Own.linFits_eq]
    exact h
  exact ⟨le_trans ((VerifiableInference.Desc.Own.roomCan_iff _ _ _).1
      (VerifiableInference.Desc.Own.omega_has_room codes S h').1).2.1 (by norm_num),
    VerifiableInference.Desc.K13.Honest.shape_small h'⟩

/-- **The terms of the row (Dot) fit their places**, where the taking-over and linDotRow return. -/
theorem dot_terms_fit (p : P₁₄) (s : S₃) (x : Border) (a : Nat × DState Loc₃) (dot : Row)
    (ha : takeOver p.S s.loc.own x.shared (s.withCols []) = .ok a)
    (hd : linDotRow p.S x.g x.shared.psi a.1 (linLayOmega a.2.st.codes p.S) s.loc.w
      (linLayW a.2.st.codes p.S) = some dot)
    (hB : ∀ w ∈ x.g, ∃ d q, d ≤ p.S.kRow ∧ BlockForm p.S.kRow d q w ∧
      2 ^ d * q + 2 ^ d ≤ p.S.matrixRows)
    (hok : ∀ w ∈ x.g, w.ok = true) (hlin : linOk s.st.codes p.S = true)
    (hp : x.shared.psi.length = p.S.kCol)
    (hO : ∀ y, x.shared.st.oracles[x.shared.omega]? = some y → y.shape = p.S.omega)
    (hW : ∃ xw G, s.st.oracles[s.loc.w]? = some xw ∧ xw.shape = p.S.w ∧
      s.st.groups[s.loc.own]? = some G ∧ G.members.contains s.loc.w = true) :
    has a.2.st.groups[s.loc.own]? (fun G => dot.terms.all fun t =>
      Own.tensorInOrder t.v && Own.placeFits a.2.st G t.oracle t.part t.v.vars 0) = true := by
  obtain ⟨y, G, e1, hy, -, -, hnew, hG, -, hG', hold, -, -⟩ := takeOver_says _ _ _ _ a ha
  have hc : a.2.st.codes = s.st.codes := (carries_takeOver _ _ _ _ a ha).1.1.codes
  obtain ⟨xw, G₀, hxw, hsw, hG₀, hmw⟩ := hW
  obtain rfl : G = G₀ := Option.some.inj (hG.symm.trans hG₀)
  have hlt : s.loc.w < s.st.oracles.size := (Array.getElem?_eq_some_iff.1 hxw).1
  have hnew' := hnew
  rw [← e1] at hnew'
  have SD : SeatedDot a.2.st s.st.codes p.S a.1 s.loc.w :=
    ⟨hc, by rw [e1]; exact Nat.ne_of_gt hlt, ⟨_, hnew', hO y hy⟩,
      ⟨xw, by rw [hold _ hlt]; exact hxw, hsw⟩⟩
  have PD := placedDot_of_seated SD hlin
  obtain ⟨sO, sW⟩ := dot_small hlin
  rw [hc] at hd
  rw [dot_blocks p.S x.g hB x.shared.psi hp] at hd
  obtain rfl := Option.some.inj hd
  rw [hG']
  show (Array.all _ _) = true
  rw [Array.all_eq_true_iff_forall_mem]
  intro t ht
  rw [Bool.and_eq_true]
  rcases mem_addLaid _ _ _ _ _ ht with h3 | ⟨v, hv, rfl⟩
  · rcases mem_addLaid _ _ _ _ _ h3 with h4 | ⟨v, hv, rfl⟩
    · simp at h4
    · obtain ⟨d, q, hdk, hf, -⟩ := hB v hv
      obtain ⟨o1, o2⟩ := onTable_tensorInOrder (linLayOmega s.st.codes p.S) v
        (by rw [← VerifiableInference.Desc.Own.tensorInOrder_agrees]; exact hok v hv)
        (by rw [form_vars hf hdk]; exact PD.roomOmega) sO
      refine ⟨o1, placeFits_of ?_ PD.hasOmega (by rw [o2, PD.bitsOmega]) (Nat.two_pow_pos _)⟩
      rw [e1]
      exact Array.mem_toList_iff.2 (self_mem_insertIdxIfInBounds _ _ _ (size_filter_le' _ _))
  · obtain rfl := List.mem_singleton.1 hv
    obtain ⟨o1, o2⟩ := onTable_tensorInOrder (linLayW s.st.codes p.S)
      (Tensor.eq x.shared.psi (negE oneE))
      (by rw [VerifiableInference.Desc.Own.tensorInOrder_iff]
          exact ⟨by
            show (Tensor.eq x.shared.psi (negE oneE)).vars ≤ 63
            rw [OnBytes.Slice.vars_eqTensor, hp]
            exact le_trans PD.roomW sW, Or.inl rfl, fun _ h => absurd h List.not_mem_nil,
            List.nodup_nil⟩)
      (by rw [OnBytes.Slice.vars_eqTensor, hp]; exact PD.roomW) sW
    refine ⟨o1, placeFits_of ?_ PD.hasW (by rw [o2, PD.bitsW]) (Nat.two_pow_pos _)⟩
    exact Array.mem_toList_iff.2 (mem_insertIdxIfInBounds _ _ _ _
      (Array.contains_iff_mem.1 hmw))

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.dot_small
#print axioms ProofFile.Honest.K14.dot_terms_fit
