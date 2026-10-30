-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/StackFinAt.lean: CONDITIONAL.

What is here. The premise hfin of FlatStack.lean's `stack_zero`: the verifier's summand at the end
of the batched sumcheck reads as the honest job's summand on the values that the round of the end
values sent.

What is shown. By the library's `hearStack_both` (OnBytes/Desc/First/K4/StackWords.lean) the four
things on which the verifier calls `stackEnd` are what the ledger behind the round of the end values
shows, and that ledger holds the words which the round sent (`stackVals`): so they are the four
stretches that the honest side's `StackData.sidesOn` cuts out of that list. By
Johnson/Road/K4/C/StackFin.lean the verifier's panels, number of rounds and weights are the honest
side's. Statements and proofs.

  `arr_ext`   two arrays of one size with the same entries
  `stack_words_cut`   **the verifier's call, at the stretches of what was sent**
  `stack_sides_fin`   the honest side's call returns the verifier's two numbers
  `stack_hfin`   **hfin**

Limits. Equations between machine words but for the last step. Premises: the honest side's maker of
the job's data returns; the verifier's text `hearStack` returns, from a sized ledger; SIX TIES
BETWEEN THE TWO SIDES, each a hypothesis here: the structure that the forms read (hv), the lookup's
weights of the calls (he), its token point (hzt), the two weights that join the passes (hom), the
values that the second token sumcheck has shown (hsh), the public numbers at which the verifier's
text is called (hPy, hPT); and the verifier's challenges by bit are the given list reversed (hrs:
FlatStack.lean's `stack_worth` has it of the part's challenges). No example of the premises together
is known. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.StackAffine
import Johnson.Road.K4.C.StackFin
import OnBytes.Desc.First.K4.StackWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE mulE)
open OnBytes.Model (Reading Fork Tsc powers)
open OnBytes.Model.Layer (HeardStack Panels stackEnd panelsA panelsT placePanels stubO callsTS
  nEndT)
open OnBytes.PscRun (Sized)
open OnBytes.K.Kc (Tape)
open OnBytes.Desc.First.P1 (tapeEps shown_some)
open OnBytes.Desc.First.K4 (engFl hearStack hearStack_both stackVals shown_run hideRun_shown
  mapM_size)
open OnBytes.Road.K4.C (hfin_of)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In Pts StackData stackData jobStackOn ztOf)

/-- Two arrays of one size with the same entries are one. -/
theorem arr_ext (a b : Array E) (hs : a.size = b.size)
    (h : ∀ i, i < a.size → a.getD i zeroE = b.getD i zeroE) : a = b := by
  refine Array.ext hs fun i h1 h2 => ?_
  have := h i h1
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
    Array.getElem?_eq_getElem h2] at this
  exact this

variable {P : OnBytes.Model.Layer.Pub} {v : OnBytes.Model.Layer.Env}
  {H : OnBytes.Model.Layer.Heard} {lamS NCLp : ℕ} {F G : Fork} {t u : Tape} {K : HeardStack}

/-- **The verifier's call of `stackEnd`, at the stretches of what the round of the end values
sent.** -/
theorem stack_words_cut (hS : Sized F)
    (h : hearStack engFl P v H lamS NCLp F t = some (K, G, u)) :
    ∃ (tT : Tsc) (shownT : Array E) (TS : List ℕ) (pans : Panels),
      H.tT = some tT ∧
      ((Array.range (nEndT P.y)).mapM fun i => F.shown (tT.sEnd + i)) = some shownT ∧
      callsTS P = some TS ∧
      panelsT { v := v, e := H.fo.e, shownT := shownT, zt := H.ztF, stubO := stubO P.y } TS
        (panelsA { v := v, e := H.fo.e, shownT := shownT, zt := H.ztF, stubO := stubO P.y } {}) =
        some pans ∧
      stackEnd P.y (placePanels pans.bl).1 K.rs lamS (powers (tapeEps t) 2)
        ((stackVals lamS t).toArray.extract 1 (1 + (1 + P.y.LamM)))
        ((stackVals lamS t).toArray.extract (2 + (1 + P.y.LamM)) (stackVals lamS t).toArray.size)
        ((stackVals lamS t).toArray.getD 0 zeroE)
        ((stackVals lamS t).toArray.getD (1 + (1 + P.y.LamM)) zeroE) = some K.fin := by
  obtain ⟨tT, shownT, TS, pans, G1, vals, H1, V, shA, shB, beta, q2, q3, q4, q5, hv, hs, hG1, s1,
    s2, s3, q12, q13, q14, q15, q16⟩ := hearStack_both h
  have hF' : Sized ({ F with next := F.next + 1 + 2 * lamS + 2 + (2 + (1 + P.y.LamM) + NCLp) } :
      Fork) := hS
  have w : ∀ i, i < 2 + (1 + P.y.LamM) + NCLp →
      G1.vp.getD (K.sA0 + i) zeroE = (stackVals lamS t).getD i zeroE := fun i hi =>
    hideRun_shown hF' hG1 hv (Fo.Later.refl G1) i (by rw [hs]; exact hi)
  have hsz : (stackVals lamS t).toArray.size = 2 + (1 + P.y.LamM) + NCLp := by
    rw [List.size_toArray, ← hv, Array.length_toList, hs]
  have ga : ∀ i, (stackVals lamS t).toArray.getD i zeroE = (stackVals lamS t).getD i zeroE :=
    fun i => by
      rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
  have eA : shA = (stackVals lamS t).toArray.getD 0 zeroE := by
    rw [ga, (shown_some q14).2.2, ← w 0 (by omega), Nat.add_zero]
  have eB : shB = (stackVals lamS t).toArray.getD (1 + (1 + P.y.LamM)) zeroE := by
    rw [ga, (shown_some q15).2.2, ← w (1 + (1 + P.y.LamM)) (by omega), s2, s1, Nat.add_assoc]
  have eH : H1 = (stackVals lamS t).toArray.extract 1 (1 + (1 + P.y.LamM)) := by
    have z1 : H1.size = 1 + P.y.LamM := mapM_size q12
    refine arr_ext _ _ (by rw [z1, Array.size_extract, hsz]; omega) fun k hk => ?_
    rw [z1] at hk
    rw [extract_getD, hsz, if_pos (by omega), ga, shown_run q12 hk, ← w (1 + k) (by omega), s1,
      Nat.add_assoc]
  have eV : V = (stackVals lamS t).toArray.extract (2 + (1 + P.y.LamM))
      (stackVals lamS t).toArray.size := by
    have z1 : V.size = NCLp := mapM_size q13
    refine arr_ext _ _ (by rw [z1, Array.size_extract, hsz]; omega) fun k hk => ?_
    rw [z1] at hk
    rw [extract_getD, hsz, if_pos (by omega), ga, shown_run q13 hk,
      ← w (2 + (1 + P.y.LamM) + k) (by omega), s3, s2, s1]
    congr 1
    omega
  exact ⟨tT, shownT, TS, pans, q2, q3, q4, q5, by rw [← eA, ← eB, ← eH, ← eV]; exact q16⟩

variable {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E} {D : StackData}

/-- **The honest side's call on what was sent returns the verifier's two numbers.** -/
theorem stack_sides_fin (hD : stackData Q w p shownT = some D)
    (hF : hearStack engFl P v H Q.hp.lamS NCLp F t = some (K, G, u)) (hS : Sized F)
    (hPy : P.y = Q.P.y) (hPT : callsTS P = callsTS Q.P)
    (hv : OnBytes.Desc.First.K4.Honest.envOf Q p = some v) (he : p.fo.e = H.fo.e)
    (hzt : ztOf Q p = H.ztF) (hom : p.om = powers (tapeEps t) 2)
    (hsh : ∀ tT a, H.tT = some tT →
      ((Array.range (nEndT P.y)).mapM fun i => F.shown (tT.sEnd + i)) = some a → a = shownT) :
    D.sidesOn K.rs (stackVals Q.hp.lamS t).toArray = some (K.fin.As, K.fin.Bs) := by
  obtain ⟨tT, sh', TS, pans, q2, q3, q4, q5, q6⟩ := stack_words_cut hS hF
  obtain rfl := hsh tT sh' q2 q3
  rw [hPy] at q5 q6
  rw [hPT] at q4
  have key := hfin_of hD hv he hzt q4 q5 hom q6
  have hy : D.S.v.y = Q.P.y := by
    unfold stackData at hD
    obtain ⟨S, hS', hD'⟩ := Option.bind_eq_some_iff.mp hD
    have e1 := (OnBytes.Road.K4.C.sides_parts hS').1
    have e2 : D.S = S := by
      unfold OnBytes.Desc.First.K4.Honest.stackDataOn at hD'
      obtain ⟨R, _, hD'⟩ := Option.bind_eq_some_iff.1 hD'
      obtain ⟨⟨bl, places⟩, _, hD'⟩ := Option.bind_eq_some_iff.1 hD'
      dsimp only at hD'
      by_cases hc : (OnBytes.ceilLog2 places != S.Q.hp.lamS || p.om.size != 2 ||
          S.opens.size != S.Q.hp.NCL - (if (S.Q.g == 0) = true then 1 else 0)) = true
      · rw [if_pos hc] at hD'
        simp at hD'
      · rw [if_neg hc] at hD'
        obtain ⟨_, _, hD'⟩ := Option.bind_eq_some_iff.1 hD'
        obtain ⟨sides, _, hD'⟩ := Option.bind_eq_some_iff.1 hD'
        obtain rfl := Option.some.inj hD'
        rfl
    rw [e2]
    exact e1
  unfold StackData.sidesOn StackData.nVirt
  rw [hy]
  rw [hy] at key
  show (stackEnd Q.P.y D.bl K.rs D.S.Q.hp.lamS D.om _ _ _ _).bind _ = _
  rw [key]
  rfl

/-- **hfin.** rsL: the part's challenges in the order of the rounds. -/
theorem stack_hfin (hD : stackData Q w p shownT = some D)
    (hF : hearStack engFl P v H Q.hp.lamS NCLp F t = some (K, G, u)) (hS : Sized F)
    (hPy : P.y = Q.P.y) (hPT : callsTS P = callsTS Q.P)
    (hv : OnBytes.Desc.First.K4.Honest.envOf Q p = some v) (he : p.fo.e = H.fo.e)
    (hzt : ztOf Q p = H.ztF) (hom : p.om = powers (tapeEps t) 2)
    (hsh : ∀ tT a, H.tT = some tT →
      ((Array.range (nEndT P.y)).mapM fun i => F.shown (tT.sEnd + i)) = some a → a = shownT)
    (rsL : List E) (hrs : K.rs.toList = rsL.reverse) :
    Reading.gl.val (mulE K.fin.As K.fin.Bs) =
      Reading.gl.val ((jobStackOn D).atEnds rsL (stackVals Q.hp.lamS t)) := by
  have e : rsL.toArray.reverse = K.rs := by
    apply Array.toList_inj.mp
    rw [Array.toList_reverse, hrs]
  show _ = Reading.gl.val
    ((D.summandOn rsL.toArray.reverse (stackVals Q.hp.lamS t).toArray).getD zeroE)
  unfold StackData.summandOn
  rw [e, stack_sides_fin hD hF hS hPy hPT hv he hzt hom hsh]
  rfl

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.arr_ext
#print axioms ProofFile.Honest.K4.stack_words_cut
#print axioms ProofFile.Honest.K4.stack_sides_fin
#print axioms ProofFile.Honest.K4.stack_hfin
