-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/JoinTies.lean: CONDITIONAL.

What is here. At a state behind the step of the member of the feed-forward layers' own rounds
(sub-protocol K4): what the honest side's data of the batched sumcheck read is what the verifier's
hearing has returned. These are the ties that `joinWorth_made` (Law/JoinMade.lean) asks between the
two sides: the structure which the forms read, the lookup's weights of the calls, its token point
and its point, the end point of the second token sumcheck and the list of named points
(`joinAt_ties`); the values that the second token sumcheck has shown (`joinAt_shown`, with the
hearing's own return); the first weight of the two passes is 1 (`joinAt_om`); the inverse that the
second token sumcheck's claim spends (`joinAt_inv`). All by laws that lie: Law/PtsAt.lean,
PtsPow.lean, PtsAtStand.lean, ClaimsAre.lean, SeenTerms.lean, TermsWindow.lean,
Law/W/BackOfLed.lean, StandHear.lean.

  `joinAt_ties`   six ties of the data to what was heard.
  `joinAt_shown`   the hearing's return, and the shown values.
  `joinAt_om`   the first weight of the two passes.
  `joinAt_inv`   the inverse of the second token sumcheck's first challenge.

Not shown here. K4Stand (Z), that the thread stands (hT), the tie on what the lookup has heard
(hLk), that the data are made (data), that the three words of the challenge lie below the prime
(hok: Law/OkAtStand.lean has it at a state): hypotheses. JoinWorth itself. No example is known. AT A
THREAD NONE OF WHOSE STEPS ACCEPTS THERE IS NO SUCH STATE. By a walk of import lines the closure
holds seven modules under Johnson/RecCompile/ (Join, Wire, Pass, CmsGlue, CmsBcs, Cms, Bcs), through
Law/SlotsTrue.lean's imports; none under Johnson/Goal/ or Johnson/D/; under Johnson/RecCompile/ none
of the names Honest…, Both…, PassH…. Nothing on soundness, on completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.BackOfLed
import Johnson.Desc.ProofFile.Honest.K4.Law.W.StandHear
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MakersReturn
import Johnson.Desc.ProofFile.Honest.K4.Law.ClaimsAre
import Johnson.Desc.ProofFile.Honest.K4.Law.SeenTerms
import Johnson.Desc.ProofFile.Honest.K4.Law.TermsWindow
import Johnson.Desc.ProofFile.Honest.K4.Law.OwnAtStand
import Johnson.Desc.ProofFile.Honest.K4.Law.StackPass
import Johnson.Road.FormsKeysKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes (E zeroE negE invE)
open OnBytes.Model (Reading Fork Tsc Forest.Heard)
open OnBytes.Model.Layer (Own Heard pointsOf nEndT)
open OnBytes.K.Kc (Tape paired)
open OnBytes.Road.K4.C (PtsPart named_part stack_open sides_fields)
open OnBytes.Desc.First.K4 (Par engFl hear hearNorms hearTerms entries)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
  {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E' : Env}
  {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
  {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}

/-- **SIX TIES OF THE DATA TO WHAT WAS HEARD.** CONDITIONAL: on every hypothesis named. -/
theorem joinAt_ties
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E' ds y cols s' A o)
    (hT : Thr T b k s m E') (hLk : K4LookTieAt look Q s m) {sh : Array E} {SD : StackData}
    (data : stackData Q (k4Wit Q cells weights tokens (look Q) m.st.input)
      (pts4 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds) sh = some SD) :
    SD.S.v = o.v ∧ SD.S.fo.e = o.H.fo.e ∧ SD.S.zt = o.H.ztF ∧
      (pts4 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds).fo.zx =
        o.H.fo.zx ∧
      (∀ tT', o.H.tT = some tT' →
        (pts4 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds).rt = tT'.r) ∧
      ∀ pts, pointsOf Q.P.y o.H o.hd o.hd2 = some pts →
        PtsPart
          (namedPts Q (pts4 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds))
          pts := by
  obtain ⟨hd2, tT, ⟨F0, G, t, u, H1, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, L, hD⟩, hr, _,
    _⟩ := stand_led Z
  have l4 : k4StartAt Q 4 ≤ ds.length := by
    simp only [k4StartAt] at hr ⊢
    omega
  have l3 : k4StartAt Q 3 ≤ ds.length := by
    simp only [k4StartAt] at hr ⊢
    omega
  obtain ⟨_, _, _, e3, _, _, _⟩ := k4StartAt_eq Q
  have hh := k4_heard_front Z.seat hT
  have hzx := stand_zx Z hLk
  obtain ⟨Fh, hH⟩ := stand_hear Z
  obtain ⟨g, _, q2, _, hzk, he⟩ := hLk
  have el := stand_look Z
  rw [q2] at el
  obtain rfl := Option.some.inj el
  obtain ⟨_, _, efo, hv, _, _, ezt⟩ := sides_fields (stack_open data).1
  have hv' := env_is hH
    (pts4 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds) (by
    show (ptsOf Q _ (m.st.heard ++ ds.take (rJ4 Q.P Q.g))).fo.zk = _
    rw [at_look _ _ ds hh]
    exact hzk)
  refine ⟨Option.some.inj (hv.symm.trans hv'), ?_, ?_, ?_, ?_, ?_⟩
  · rw [efo]
    show (ptsOf Q _ (m.st.heard ++ ds.take (rJ4 Q.P Q.g))).fo.e = _
    rw [at_look _ _ ds hh]
    exact he
  · rw [ezt]
    exact at_zt _ _ L ds hh hzx _
  · show (ptsOf Q _ (m.st.heard ++ ds.take (rJ4 Q.P Q.g))).fo.zx = _
    rw [at_look _ _ ds hh]
    exact hzx
  · intro tT' h1
    rw [L.kTT] at h1
    obtain rfl := Option.some.inj h1
    exact at_rt _ _ L ds hD l3 hh _ (by
      rw [← e3]
      simp only [k4StartAt]
      omega)
  · intro pts hp
    exact named_part hp (namedTie_led L hD l4 hh hzx)

/-- **THE HEARING's RETURN, AND THE VALUES THAT THE SECOND TOKEN SUMCHECK HAS SHOWN.** CONDITIONAL:
on Z and hT. -/
theorem joinAt_shown
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E' ds y cols s' A o)
    (hT : Thr T b k s m E') :
    ∃ Fh, hear engFl { Q.P with tokv := s.tokv } Q.hp Q.g o.H.fo Fh
        (paired (roundsOf y.1) (entries Q.P Q.hp Q.g)) = some (o, A.F, []) ∧
      ∀ (H1 : Heard) (G1 G2 : Fork) (u1 u2 : Tape) (tT' : Tsc) (a : Array E),
        hearNorms engFl { Q.P with tokv := s.tokv } Q.g o.H.fo Fh
          (paired (roundsOf y.1) (entries Q.P Q.hp Q.g)) = some (H1, G1, u1) →
        hearTerms engFl { Q.P with tokv := s.tokv } H1 G1 u1 = some (o.H, G2, u2) →
        o.H.tT = some tT' →
        ((Array.range (nEndT Q.P.y)).mapM fun i => G2.shown (tT'.sEnd + i)) = some a →
        a = (k4SentAt (m.seen ++ roundsOf (y.1.take (rJ4 Q.P Q.g))) (k4TermsEnds Q)) := by
  obtain ⟨a, H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, ha, L⟩ := stand_led_tape Z
  obtain ⟨a', _, fo, ha', _, _, _, hh0, _⟩ := step_tape Z.seat Z.sits Z.stepped Z.seg Z.heard
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  obtain rfl : o.H.fo = fo := OnBytes.Desc.First.K4.Slots.own_fo hh0
  refine ⟨a'.F, hh0, fun H1' K1 K2 u1 u2 tT' x n1 n2 g1 g3 => ?_⟩
  obtain ⟨v1, m1, m2⟩ := L.nt
  obtain ⟨rfl, rfl, rfl⟩ : H1' = H1 ∧ K1 = G1 ∧ u1 = v1 := by
    have e := Option.some.inj (n1.symm.trans m1)
    exact ⟨congrArg (·.1) e, congrArg (·.2.1) e, congrArg (·.2.2) e⟩
  obtain rfl : K2 = G2 := congrArg (·.2.1) (Option.some.inj (n2.symm.trans m2))
  exact stand_terms_run Z hT tT' g1 K2 x L.g2 g3

/-- **THE FIRST WEIGHT OF THE TWO PASSES IS 1.** CONDITIONAL: on Z, hT and the return. -/
theorem joinAt_om
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E' ds y cols s' A o)
    (hT : Thr T b k s m E') {sh : Array E} {SD : StackData}
    (data : stackData Q (k4Wit Q cells weights tokens (look Q) m.st.input)
      (pts4 Q (k4Wit Q cells weights tokens (look Q) m.st.input) m.st.heard ds) sh = some SD) :
    Reading.gl.val (SD.om.getD 0 zeroE) = 1 := by
  obtain ⟨hd2, tT, ⟨F0, G, t, u, H1, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, L, hD⟩, hr, _,
    _⟩ := stand_led Z
  have l3 : k4StartAt Q 3 ≤ ds.length := by
    simp only [k4StartAt] at hr ⊢
    omega
  obtain ⟨_, _, _, e3, _, _, _⟩ := k4StartAt_eq Q
  have hh := k4_heard_front Z.seat hT
  unfold stackData at data
  obtain ⟨S, _, hS⟩ := Option.bind_eq_some_iff.mp data
  rw [(stackDataOn_open hS).2.1]
  show Reading.gl.val ((ptsOf Q _ (m.st.heard ++ ds.take (rJ4 Q.P Q.g))).om.getD 0 zeroE) = 1
  rw [at_stackPow _ _ L ds hD l3 hh _ (Nat.le_of_eq e3)]
  exact Reading.gl.one

/-- **THE INVERSE THAT THE SECOND TOKEN SUMCHECK's CLAIM SPENDS.** CONDITIONAL: on Z and hok. -/
theorem joinAt_inv
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E' ds y cols s' A o)
    (hok : ∀ tT, o.H.tT = some tT → OnBytes.okE tT.p.eps = true) :
    ∀ tT', o.H.tT = some tT' →
      Reading.gl.val (negE (invE tT'.p.eps)) * Reading.gl.val tT'.p.eps = -1 := by
  obtain ⟨hd2, tT, ⟨F0, G, t, u, H1, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, L, _⟩, _, _,
    _⟩ := stand_led Z
  intro tT' h1
  have h2 := hok tT' h1
  rw [L.kTT] at h1
  obtain rfl := Option.some.inj h1
  rw [OnBytes.Road.gl_numerals.neg, neg_mul]
  have h3 : OnBytes.okE tT.p.eps = true := h2
  have h4 := led_hinv L h3
  exact congrArg Neg.neg h4

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.joinAt_ties
#print axioms ProofFile.Honest.K4.W.joinAt_shown
#print axioms ProofFile.Honest.K4.W.joinAt_om
#print axioms ProofFile.Honest.K4.W.joinAt_inv
