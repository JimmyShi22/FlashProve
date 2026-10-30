-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/K4/StackPublic.lean: what a return of the batched sumcheck of the layers' own
rounds says of the PUBLIC values that the text fetches on its way.

`hearStack` (OnBytes/Desc/First/K4/Hear.lean) makes the list of panels, places them, tests two
numbers against the plan, and at its end calls the plain function `stackEnd` on what was shown. The
library's theorems on that end (Johnson/Road/FormsKeysEnd.lean; Rows/LayerEnds34.lean) take each of
these lines as a hypothesis. Here they are concluded from a return of K4's own text over the plain
engine. OnBytes/Desc/First/K4/StackTape.lean takes the same text apart for its rounds and its
ledger; this file keeps what that one leaves out.

  `mapM_size`: a run over the numbers below n that returns has n members.
  `hearStack_public`: if `hearStack engFl P v H lamS NCLp F t` returns K: the two weights are the
      powers 1, x of the element x that the tape's first round drew; `joinStart` returned at these;
          the second token sumcheck
      is there; the panels are the
      verifier's own list at what that sumcheck showed; both tests on numbers passed; the four
      slots follow each other as written; `stackEnd` returned K.fin on arrays of 1 + LamM and NCLp
      shown values and two shown values; each of these is what a ledger Fe shows under its slot.

  `hearStack_rs`: K.rs has lamS members.

Limits. One direction: from a return. An identity on data: nothing on what anything is worth, on a
draw, on soundness. Of the ledger Fe, behind the round of the end values, nothing is said here but
that it shows these values (StackTape.lean says which ledger it is).
-/
import OnBytes.Desc.First.K4.StackLaw
import OnBytes.Maker.TablesLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.Desc.First.P1 (bind_some pure_some need_some ask_some batch_spec tapeEps)

theorem mapM_size {α : Type} {n : Nat} {f : Nat → Option α} {a : Array α}
    (h : (Array.range n).mapM f = some a) : a.size = n := by
  rw [Array.mapM_eq_mapM_toList] at h
  obtain ⟨l, hl, e⟩ := Option.map_eq_some_iff.mp h
  rw [← e, List.size_toArray, OnBytes.Maker.mapM_length _ _ _ hl, Array.length_toList,
    Array.size_range]

theorem hearStack_public {P : Pub} {v : Env} {H : Heard} {lamS NCLp : Nat} {F G : Fork}
    {t u : Tape} {K : HeardStack} (h : hearStack engFl P v H lamS NCLp F t = some (K, G, u)) :
    ∃ (tT : Tsc) (shownT : Array E) (TS : List Nat) (pans : Panels) (Fe : Fork)
      (H1 V : Array E) (shA shB : E) (C : Aff) (Fk : Fork) (tk : Tape),
      joinStart engFl v H (powers (tapeEps t) 2) F (t.drop 1) = some (C, Fk, tk) ∧
      H.tT = some tT ∧
      ((Array.range (nEndT P.y)).mapM fun i => F.shown (tT.sEnd + i)) = some shownT ∧
      callsTS P = some TS ∧
      panelsT { v := v, e := H.fo.e, shownT := shownT, zt := H.ztF, stubO := stubO P.y } TS
        (panelsA { v := v, e := H.fo.e, shownT := shownT, zt := H.ztF, stubO := stubO P.y } {}) =
        some pans ∧
      (ceilLog2 (placePanels pans.bl).2 == lamS) = true ∧ (pans.nextV == NCLp) = true ∧
      K.sH1 = K.sA0 + 1 ∧ K.sB0 = K.sH1 + (1 + P.y.LamM) ∧ K.sV = K.sB0 + 1 ∧
      ((Array.range (1 + P.y.LamM)).mapM fun i => Fe.shown (K.sH1 + i)) = some H1 ∧
      ((Array.range NCLp).mapM fun i => Fe.shown (K.sV + i)) = some V ∧
      Fe.shown K.sA0 = some shA ∧ Fe.shown K.sB0 = some shB ∧
      H1.size = 1 + P.y.LamM ∧ V.size = NCLp ∧
      stackEnd P.y (placePanels pans.bl).1 K.rs lamS (powers (tapeEps t) 2) H1 V shA shB =
        some K.fin := by
  unfold hearStack at h
  obtain ⟨om, F1, t1, h1, k1⟩ := bind_some.mp h
  obtain ⟨_, rfl, x, e1, rfl⟩ := batch_spec h1
  subst e1
  obtain ⟨tT, A2, a2, c2, k2⟩ := bind_some.mp k1
  obtain ⟨q2, rfl, rfl⟩ := need_some.mp c2
  obtain ⟨shownT, A3, a3, c3, k3⟩ := bind_some.mp k2
  obtain ⟨rfl, rfl, q3⟩ := shownRun_spec c3
  obtain ⟨TS, A4, a4, c4, k4⟩ := bind_some.mp k3
  obtain ⟨q4, rfl, rfl⟩ := need_some.mp c4
  obtain ⟨pans, A5, a5, c5, k5⟩ := bind_some.mp k4
  obtain ⟨q5, rfl, rfl⟩ := need_some.mp c5
  obtain ⟨_, A6, a6, c6, k6⟩ := bind_some.mp k5
  obtain ⟨q6, rfl, rfl⟩ := P1.must_some.mp c6
  obtain ⟨C, A7, a7, c7, k7⟩ := bind_some.mp k6
  obtain ⟨p0, F8, t8, c8, k8⟩ := bind_some.mp k7
  obtain ⟨st, F9, t9, c9, k9⟩ := bind_some.mp k8
  obtain ⟨_, A10, a10, c10, k10⟩ := bind_some.mp k9
  obtain ⟨q10, rfl, rfl⟩ := P1.must_some.mp c10
  obtain ⟨z, F11, t11, c11, k11⟩ := bind_some.mp k10
  obtain ⟨sA0, p2⟩ := z
  obtain ⟨x1, A12, a12, c12, k12⟩ := bind_some.mp k11
  obtain ⟨rfl, rfl, q12⟩ := shownRun_spec c12
  obtain ⟨x2, A13, a13, c13, k13⟩ := bind_some.mp k12
  obtain ⟨rfl, rfl, q13⟩ := shownRun_spec c13
  obtain ⟨x3, A14, a14, c14, k14⟩ := bind_some.mp k13
  have c14' : Fl.shown _ _ _ = some (x3, A14, a14) := c14
  obtain ⟨q14, rfl, rfl⟩ := ask_some.mp c14'
  obtain ⟨x4, A15, a15, c15, k15⟩ := bind_some.mp k14
  have c15' : Fl.shown _ _ _ = some (x4, A15, a15) := c15
  obtain ⟨q15, rfl, rfl⟩ := ask_some.mp c15'
  obtain ⟨fin, A16, a16, c16, k16⟩ := bind_some.mp k15
  obtain ⟨q16, rfl, rfl⟩ := need_some.mp c16
  obtain ⟨z2, F17, t17, c17, k17⟩ := bind_some.mp k16
  obtain ⟨rowS, p3⟩ := z2
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k17
  exact ⟨tT, shownT, TS, pans, F11, x1, x2, x3, x4, C, _, _, c7, q2, q3, q4, q5, q6, q10,
    rfl, rfl, rfl,
    q12, q13, q14, q15, mapM_size q12, mapM_size q13, q16⟩

/-- There is one challenge for each round of the plan. -/
theorem hearStack_rs {P : Pub} {v : Env} {H : Heard} {lamS NCLp : Nat} {F G : Fork} {t u : Tape}
    {K : HeardStack} (h : hearStack engFl P v H lamS NCLp F t = some (K, G, u)) :
    K.rs.size = lamS := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ms, _, _, c⟩ := hearStack_tape h
  have h9 := c.2.2.2.2.2.2.2.2.1
  have h12 := c.2.2.2.2.2.2.2.2.2.2.2.1
  have e1 : ms.length = lamS := by
    have := congrArg List.length h9
    rw [List.length_map] at this
    rw [this]
    exact List.length_replicate
  rw [← Array.length_toList, h12, List.length_reverse, List.length_map, e1]

#print axioms hearStack_public
#print axioms hearStack_rs

end OnBytes.Desc.First.K4
