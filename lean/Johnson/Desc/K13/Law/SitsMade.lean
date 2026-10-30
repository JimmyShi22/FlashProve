-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/SitsMade.lean: "W SITS AS THE PLAN SAYS" (`wSitsB`,
Johnson/Desc/K13/Law/SitsAt.lean: a test with code on the first chain's record) IS MADE BY W's
COMMITMENT WITH KIND K13's BLOCK BEHIND IT, AND KEPT BY THE CHAIN's LAST BLOCK. Statements with
their proofs. It names no table of joints.
Main names:
  `PlanSits P P'`: what is asked of the plan alone, four tests with code: the first message of the
    place's sending has the shape that the kind's numbers have for W; every message length of the
    place's codes is a power of two; the number of W's shape's code is in the codes' list.
    `planSitsB`: the test; `planSitsB_iff`.
  `sendAtS_shape`: at W's sending: message number (messages in front) + i bears the shape of the
    i-th notice (by `K1.outs_get`, Johnson/Desc/K1/Law/Targets2.lean); the record's codes behind are
    the place's.
  `atM4_sits`: **the maker**: a yes of `atM4 P (K1.sendAtS P')` from a record that has `FrontOk`, at
    a plan that passes: `wSitsB P'.codes P` says yes of the record behind.
  `firstEnd_sits`: **kept**: the first chain's last block (`First.firstEnd`) returns the record
    (`Keeps.chainEnd_same`, Johnson/Desc/Tidy/Still.lean).

What is not claimed. That a plan passes `planSitsB` (a run can show it). W's seat in the record's
book (Johnson/Desc/K1/Law/BookAtRecord.lean: `Booked.newer` gives the place of a new message where
the book in front has a place for every message). Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.AtRecord
import Johnson.Desc.K13.Law.SitsAt
import Johnson.Desc.K13.Law.Mask
import Johnson.Desc.K1.Law.Targets2
import Johnson.Desc.Tidy.Still

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame)

variable {Cl : Type}

/-- **What is asked of the plan alone.** -/
structure PlanSits (P : Where) (P' : K1.Par) : Prop where
  first : (P'.sent[0]?).map (·.shape) = some P.lin.w
  lengths : P'.codes.lengthsOk = true
  code : P.lin.w.code < P'.codes.base.size

/-- The test. -/
def planSitsB (P : Where) (P' : K1.Par) : Bool :=
  decide ((P'.sent[0]?).map (·.shape) = some P.lin.w) && P'.codes.lengthsOk &&
    decide (P.lin.w.code < P'.codes.base.size)

theorem planSitsB_iff (P : Where) (P' : K1.Par) : planSitsB P P' = true ↔ PlanSits P P' := by
  simp only [planSitsB, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.first, h.lengths⟩, h.code⟩⟩

theorem wr_shape (codes : Codes) (seeds : List (List E × E)) (o : ℕ) (s : OracleShape)
    (ys : List E) : (K1.wr codes seeds o s ys).shape = s := by
  unfold K1.wr
  split <;> rfl

/-- **At W's sending**: the new messages' shapes; the codes. -/
theorem sendAtS_shape (P' : K1.Par) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (K1.sendAtS P' : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    s'.st.codes = P'.codes ∧ ∀ i (hi : i < (K1.shapesOf P').length),
      (s'.st.oracles[s.st.oracles.size + i]?).map (·.shape) = some (K1.shapesOf P')[i] := by
  obtain ⟨ids, d', hd, hst, _⟩ := K1.sendAtS_ok P' s s' _ gs h
  obtain ⟨ha, _, rfl⟩ := (K1.decideSend_iff P' _ _ d' r₁ r₂ ids).1 hd
  rw [hst]
  refine ⟨ha.2.1, fun i hi => ?_⟩
  have hget := K1.outs_get P'.codes (K1.seedsOf P' r₁) (K1.shapesOf P') s.st.oracles.size
    (K1.answersIn r₂) i hi
  have hx : (s.st.oracles.toList ++ K1.outs P'.codes (K1.seedsOf P' r₁) s.st.oracles.size
      (K1.shapesOf P') (K1.answersIn r₂)).toArray[s.st.oracles.size + i]? = some
        (K1.wr P'.codes (K1.seedsOf P' r₁) (s.st.oracles.size + i) (K1.shapesOf P')[i]
          ((K1.answersIn r₂).drop (K1.offsetOf (K1.shapesOf P') i))) := by
    rw [List.getElem?_toArray, List.getElem?_append_right (by simp)]
    simpa using hget
  show ((s.st.oracles.toList ++ K1.outs P'.codes (K1.seedsOf P' r₁) s.st.oracles.size
    (K1.shapesOf P') (K1.answersIn r₂)).toArray[s.st.oracles.size + i]?).map (·.shape) = _
  rw [hx, Option.map_some, wr_shape]

/-- **THE MAKER.** -/
theorem atM4_sits {F : Frame} {P : Where} {P' : K1.Par} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (atM4 (Cl := Cl) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s') (y : F.E.Str)
    (hon : FrontOk P ((s, y) : S × F.E.Str)) (hP : PlanSits P P') :
    wSitsB P'.codes P s' = true := by
  have hL := (atM4_laid h y y hon).1
  obtain ⟨D, hD, _, _, hst, l, hlin, hw, hlay, _⟩ := laidOf_ok hL
  obtain ⟨s₁, g₁, rs₂, g₂, h1, h2⟩ := atM4_mid h
  obtain ⟨hc, hsh⟩ := sendAtS_shape P' s s₁ r₁ r₂ g₁ h1
  obtain ⟨m, hm, hsz, hI⟩ := sendAtS_idsLast P' s s₁ r₁ r₂ g₁ h1
  obtain ⟨m₀, l', hm₀, hl', hmask⟩ := rowsB_mask h2
  rw [hm] at hm₀
  obtain rfl : m = m₀ := by
    injection hm₀
  obtain rfl : l = l' := Option.some.inj (hlin.symm.trans hl')
  have hsame := rowsB_same h2
  have hn := sameAll_size hsame
  have hb := (K1.sendAtS_booked P' s s₁ r₁ r₂ g₁ h1).msgs
  have hlw : l.w = s.st.oracles.size + 0 := by
    rw [(hmask hI).1, hsz, hn, hb]
    omega
  have hcodes : s'.st.codes = P'.codes := hsame.1.trans hc
  have hshape : (s'.st.oracles[l.w]?).map (·.shape) = some P.lin.w := by
    have e := congrArg (Option.map (·.1)) (hsame.2 l.w)
    unfold sampleOf at e
    rw [Option.map_map, Option.map_map] at e
    have e' : (s'.st.oracles[l.w]?).map (·.shape) = (s₁.st.oracles[l.w]?).map (·.shape) := e
    have h0 : 0 < (K1.shapesOf P').length := by
      have e0 := hP.first
      unfold K1.shapesOf
      rw [List.length_map, Array.length_toList]
      by_contra hn
      rw [Array.getElem?_eq_none (by omega)] at e0
      cases e0
    rw [e', hlw, hsh 0 h0, ← hP.first]
    unfold K1.shapesOf
    rw [List.getElem_map, Array.getElem_toList, Array.getElem?_eq_getElem, Option.map_some]
  unfold wSitsB wSitsL
  rw [hD, List.all_cons, List.all_cons, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨(evalLaidB_iff P s').2 hL, rfl, (sitsB_iff P'.codes P.lin D).2 ⟨?_, ?_, ?_, hP.lengths,
    hP.code⟩⟩
  · rw [hst]
    exact hcodes
  · rw [hst, hw]
    exact hshape
  · rw [hlay, hcodes]

/-- **KEPT**: the first chain's last block returns the record. -/
theorem firstEnd_sits (cs : Codes) (P : Where) (piece : ℕ) (front : List (Block S Cl)) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (First.firstEnd piece front).decide s rs gs = .ok s') (hs : wSitsB cs P s = true) :
    wSitsB cs P s' = true := by
  rw [Keeps.chainEnd_same _ _ _ _ _ h]
  exact hs

end VerifiableInference.Desc.K13.Law
