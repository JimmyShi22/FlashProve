-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/HeardTie.lean: THE OUTPUT HEAD'S OWN ROUNDS: WHAT THE VERIFIER'S
HEARING RETURNS AS CHALLENGES, AND WHAT ITS TEXT LAYS INTO ITS STATE OF THEM, ARE THE VALUES THAT
Honest/K6/HeardWhole.lean AND Honest/K6/Heard.lean MAKE OF THE ROUNDS' CHALLENGES BY ROUND NUMBER.
WHAT IT IS NOT. CONDITIONAL: THAT THE HEARING RETURNS IS A PREMISE; so are a well-laid ledger and
that the lookup's point on the positions has lt coordinates. THE WELL-LAID LEDGER IS SPENT ON
NOTHING THAT THE TOPS KEEP (Law/K06HeardDraws.lean's head says why it is asked). FIELD BY FIELD, NOT
WHOLE: the equation "heardOf g1 H = headHeardWhole .." IS FALSE of a true return [argued here;
no theorem says it]: headHeardWhole is made of a
hearing in which every sent value and each sumcheck's own data are blank, and heardOf makes sW,
sPv, wpl.sL, wpl.sR, wpl.row and, in tV, tN and tH, sCl, sEnd, p and rowU of these (so tV.p: begun
at a true return, blank there). OF THESE FIELDS NOTHING IS SAID HERE. Of any return, not of an
honest run's: no prover is in this file. NOT AT A STATE: that the verifier's state behind its step
holds heardOf of the hearing's return is not said here. Nothing on soundness, on completeness or
on what a proof hides. The frame of the honest side is not imported.
  elemOf_rounds, stretch_range, at_mid, elemOf_shift   Ask.lean's reader of challenges by number, at
                  the challenges of a list of rounds.
  hearing_tie     own: the rounds' challenges. The point on the positions, the two batching
                  elements, the element that ends the first sumcheck and the four sumchecks'
                  challenges are the eight fields that headHearingOf p own lays.
  heardOf_tie     THE LETTERS: the sizes are p.sizes, the next token y; the request is the class's
                  own letter. Fourteen fields of
                  heardOf g1 H are headHeardWhole's: win, g1, Zl, PV, gp, wpl.r, wpl.tau, omV, tV.r,
                  tN.r, tH.r, rs, qN, qH. FIVE OF THE FOURTEEN (win, g1, Zl, qN, qH) READ NOTHING OF
                  THE HEARING: both sides are one function at the same letters (by rfl); NINE ARE
                  MADE, of hearing_tie's eight equations.
  tables_tie      so the maker of the head's tables of reads gives one answer at both
                  (HeardWhole.lean: tables_nine).
  logits_tie      at a chain's challenges front ++ (own ++ later), base := front.length: tH.r, rs
                  and win are Heard.lean's headTHr, headRs, headWin.
CALLED: Law/K06HeardDraws.lean (hear_pieces, hear_draws), HeardWhole.lean (tables_nine).

-/
import Mathlib
import Johnson.Desc.ProofFile.Honest.K6.HeardWhole
import Johnson.Desc.Kinds.Law.K06HeardDraws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes (E zeroE)
open OnBytes.Model (Fork)
open VerifiableInference.Desc.Kinds (Point Head.Par Head.Sizes Head.Policy Head.Request Head.Token
  Head.In Head.HeardAll Head.heardOf FinalNorm.In FinalNorm.zt halves Norm.lt Norm.lPd)
open VerifiableInference.Desc.Kinds.Head.Law (WellLaid firstDrawn hear_pieces hear_draws)

/-! ## 1 The reader of challenges by number -/

/-- At the challenges of a list of rounds: the first element that round number k sampled. -/
theorem elemOf_rounds (rs : List Fmt.RoundView) (k : Nat) :
    elemOf (rs.map (·.drawn)) k = ((rs[k]?).map firstDrawn).getD zeroE := by
  unfold elemOf
  rw [List.getElem?_map]
  cases rs[k]? with
  | none => rfl
  | some r =>
    show ((elemsOf r.drawn).head?).getD zeroE = firstDrawn r
    unfold elemsOf firstDrawn
    rw [List.head?_map]

/-- The rounds number 1 .. n of a stretch B that stands behind A. -/
theorem stretch_range (A B C : List Fmt.RoundView) (n : Nat) (hB : n + 1 ≤ B.length) :
    ((B.drop 1).take n).map firstDrawn = (List.range n).map fun j =>
      elemOf ((A ++ (B ++ C)).map (·.drawn)) (A.length + 1 + j) := by
  refine List.ext_getElem (by simp; omega) fun j h1 h2 => ?_
  have hj : j < n := by simpa using h2
  have hb : 1 + j < B.length := by omega
  rw [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_map,
    List.getElem_range, elemOf_rounds, Nat.add_assoc,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_left hb, List.getElem?_eq_getElem hb]
  rfl

/-- One round r that stands behind A. -/
theorem at_mid (A C : List Fmt.RoundView) (r : Fmt.RoundView) :
    elemOf ((A ++ ([r] ++ C)).map (·.drawn)) A.length = firstDrawn r := by
  rw [elemOf_rounds, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- Behind challenges in front, and with later ones behind. -/
theorem elemOf_shift (front own later : List Fmt.Drawn) (k : Nat) (hk : k < own.length) :
    elemOf (front ++ (own ++ later)) (front.length + k) = elemOf own k := by
  unfold elemOf
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_left hk]

/-! ## 2 The hearing -/

/-- **THE EIGHT CHALLENGE FIELDS OF THE HEARING'S RETURN ARE headHearingOf'S**, at the rounds' own
challenges. -/
theorem hearing_tie [sz : Head.Sizes] [Head.Policy] [Head.Request] [Head.Token] [FinalNorm.In]
    [Head.In] (p : Head.Par) (hp : sz = p.sizes) {F G : Fork} {H : Head.HeardAll}
    {rs : List Fmt.RoundView} (hW : WellLaid F)
    (h : VerifiableInference.Desc.Kinds.Head.hear F rs = some (H, G, []))
    (hzt : (FinalNorm.zt).size = Norm.lt) :
    H.1.pV = headPV (rs.map (·.drawn)) ∧ H.1.gam = headGam (rs.map (·.drawn)) ∧
    H.1.squares.r = headSumR p 2 (headLPd p + headLt p) (rs.map (·.drawn)) ∧
    H.1.squares.down = elemOf (rs.map (·.drawn)) (headInFront p 3) ∧
    H.1.om = headOm p (rs.map (·.drawn)) ∧
    H.1.products.r = headSumR p 5 (headLt p) (rs.map (·.drawn)) ∧
    H.2.1.normed.r = headSumR p 6 (headLt p) (rs.map (·.drawn)) ∧
    H.2.2.logits.r = headSumR p 7 (headLt p + headLPd p) (rs.map (·.drawn)) := by
  subst hp
  letI : Head.Sizes := p.sizes
  obtain ⟨r0, r1, line, r4, tS, tP, tN, tL, hrs, lS, lP, lN, lL⟩ := hear_pieces hW h
  have lS' : tS.length = headLPd p + headLt p + 3 := lS
  have lP' : tP.length = headLt p + 3 := lP
  have lN' : tN.length = headLt p + 3 := by rw [lN, hzt]; rfl
  have zL : (FinalNorm.zt ++ halves Norm.lPd).size = headLt p + headLPd p := by
    rw [Array.size_append, hzt]
    unfold halves
    rw [Array.size_replicate]
    rfl
  have lL' : tL.length = headLt p + headLPd p + 3 := by rw [lL, zL]
  rw [hrs] at h
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := hear_draws hW h lS lP lN
  rw [hzt] at a6
  rw [zL] at a7
  -- the numbers of rounds in front of the parts
  have v3 : headInFront p 3 = headLPd p + headLt p + 5 := by
    show 0 + 1 + 1 + (headLPd p + headLt p + 3) = _
    omega
  have v4 : headInFront p 4 = headLPd p + headLt p + 6 := by
    show 0 + 1 + 1 + (headLPd p + headLt p + 3) + 1 = _
    omega
  have v5 : headInFront p 5 = headLPd p + headLt p + 7 := by
    show 0 + 1 + 1 + (headLPd p + headLt p + 3) + 1 + 1 = _
    omega
  have v6 : headInFront p 6 = headLPd p + headLt p + 7 + (headLt p + 3) := by
    show 0 + 1 + 1 + (headLPd p + headLt p + 3) + 1 + 1 + (headLt p + 3) = _
    omega
  have v7 : headInFront p 7 = headLPd p + headLt p + 7 + (headLt p + 3) + (headLt p + 3) := by
    show 0 + 1 + 1 + (headLPd p + headLt p + 3) + 1 + 1 + (headLt p + 3) + (headLt p + 3) = _
    omega
  -- the rounds, bracketed behind each front
  have e2 : rs = ([r0] ++ [r1]) ++ (tS ++ ([line] ++ ([r4] ++ (tP ++ (tN ++ tL))))) := by
    rw [hrs]
    simp only [List.append_assoc]
  have e3 : rs = ([r0] ++ ([r1] ++ tS)) ++ ([line] ++ ([r4] ++ (tP ++ (tN ++ tL)))) := by
    rw [hrs]
    simp only [List.append_assoc]
  have e4 : rs = ([r0] ++ ([r1] ++ (tS ++ [line]))) ++ ([r4] ++ (tP ++ (tN ++ tL))) := by
    rw [hrs]
    simp only [List.append_assoc]
  have e5 : rs = ([r0] ++ ([r1] ++ (tS ++ ([line] ++ [r4])))) ++ (tP ++ (tN ++ tL)) := by
    rw [hrs]
    simp only [List.append_assoc]
  have e6 : rs = ([r0] ++ ([r1] ++ (tS ++ ([line] ++ ([r4] ++ tP))))) ++ (tN ++ (tL ++ [])) := by
    rw [hrs]
    simp only [List.append_assoc, List.append_nil]
  have e7 : rs = ([r0] ++ ([r1] ++ (tS ++ ([line] ++ ([r4] ++ (tP ++ tN)))))) ++ (tL ++ []) := by
    rw [hrs]
    simp only [List.append_assoc, List.append_nil]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a0, hrs]
    rfl
  · rw [a1, hrs]
    exact (at_mid [r0] _ r1).symm
  · rw [a2]
    unfold headSumR
    congr 1
    have k := stretch_range ([r0] ++ [r1]) tS ([line] ++ ([r4] ++ (tP ++ (tN ++ tL))))
      (headLPd p + headLt p) (by omega)
    rw [← e2] at k
    exact k
  · rw [a3]
    have k := at_mid ([r0] ++ ([r1] ++ tS)) ([r4] ++ (tP ++ (tN ++ tL))) line
    rw [← e3] at k
    rw [← k, v3]
    congr 1
    simp only [List.length_append, List.length_singleton, lS']
    omega
  · rw [a4]
    have k := at_mid ([r0] ++ ([r1] ++ (tS ++ [line]))) (tP ++ (tN ++ tL)) r4
    rw [← e4] at k
    unfold headOm
    rw [← k, v4]
    congr 1
    simp only [List.length_append, List.length_singleton, lS']
    omega
  · rw [a5]
    unfold headSumR
    congr 1
    have k := stretch_range ([r0] ++ ([r1] ++ (tS ++ ([line] ++ [r4])))) tP (tN ++ tL) (headLt p)
      (by omega)
    rw [← e5] at k
    have hl : ([r0] ++ ([r1] ++ (tS ++ ([line] ++ [r4])))).length = headInFront p 5 := by
      simp only [List.length_append, List.length_singleton, lS', v5]
      omega
    rw [hl] at k
    exact k
  · rw [a6]
    unfold headSumR
    congr 1
    have k := stretch_range ([r0] ++ ([r1] ++ (tS ++ ([line] ++ ([r4] ++ tP))))) tN (tL ++ [])
      (headLt p) (by omega)
    rw [← e6] at k
    have hl : ([r0] ++ ([r1] ++ (tS ++ ([line] ++ ([r4] ++ tP))))).length = headInFront p 6 := by
      simp only [List.length_append, List.length_singleton, lS', lP', v6]
      omega
    rw [hl] at k
    exact k
  · rw [a7]
    unfold headSumR
    congr 1
    have k := stretch_range ([r0] ++ ([r1] ++ (tS ++ ([line] ++ ([r4] ++ (tP ++ tN)))))) tL []
      (headLt p + headLPd p) (by omega)
    rw [← e7] at k
    have hl : ([r0] ++ ([r1] ++ (tS ++ ([line] ++ ([r4] ++ (tP ++ tN)))))).length =
        headInFront p 7 := by
      simp only [List.length_append, List.length_singleton, lS', lP', lN', v7]
      omega
    rw [hl] at k
    exact k

/-! ## 3 What the verifier's text lays into its state of the hearing -/

/-- **FOURTEEN FIELDS OF heardOf g1 H ARE headHeardWhole'S.** The letters: the sizes are p.sizes,
the next token is y; request is the class's own letter. Five of the fourteen (win, g1, Zl, qN, qH)
read nothing of the hearing and hold by rfl; nine are made. -/
theorem heardOf_tie [sz : Head.Sizes] [Head.Policy] [request : Head.Request]
    [tk : Head.Token] [FinalNorm.In] [Head.In] (p : Head.Par) (y : Nat) (hp : sz = p.sizes)
    (ht : tk = ⟨y⟩) (g1 : OnBytes.Model.Forest.Heard) {F G : Fork}
    {H : Head.HeardAll} {rs : List Fmt.RoundView} (hW : WellLaid F)
    (h : VerifiableInference.Desc.Kinds.Head.hear F rs = some (H, G, []))
    (hzt : (FinalNorm.zt).size = Norm.lt) :
    (Head.heardOf g1 H).win = (headHeardWhole p request y g1 (rs.map (·.drawn))).win ∧
    (Head.heardOf g1 H).g1 = (headHeardWhole p request y g1 (rs.map (·.drawn))).g1 ∧
    (Head.heardOf g1 H).Zl = (headHeardWhole p request y g1 (rs.map (·.drawn))).Zl ∧
    (Head.heardOf g1 H).PV = (headHeardWhole p request y g1 (rs.map (·.drawn))).PV ∧
    (Head.heardOf g1 H).gp = (headHeardWhole p request y g1 (rs.map (·.drawn))).gp ∧
    (Head.heardOf g1 H).wpl.r = (headHeardWhole p request y g1 (rs.map (·.drawn))).wpl.r ∧
    (Head.heardOf g1 H).wpl.tau = (headHeardWhole p request y g1 (rs.map (·.drawn))).wpl.tau ∧
    (Head.heardOf g1 H).omV = (headHeardWhole p request y g1 (rs.map (·.drawn))).omV ∧
    (Head.heardOf g1 H).tV.r = (headHeardWhole p request y g1 (rs.map (·.drawn))).tV.r ∧
    (Head.heardOf g1 H).tN.r = (headHeardWhole p request y g1 (rs.map (·.drawn))).tN.r ∧
    (Head.heardOf g1 H).tH.r = (headHeardWhole p request y g1 (rs.map (·.drawn))).tH.r ∧
    (Head.heardOf g1 H).rs = (headHeardWhole p request y g1 (rs.map (·.drawn))).rs ∧
    (Head.heardOf g1 H).qN = (headHeardWhole p request y g1 (rs.map (·.drawn))).qN ∧
    (Head.heardOf g1 H).qH = (headHeardWhole p request y g1 (rs.map (·.drawn))).qH := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := hearing_tie p hp hW h hzt
  subst hp ht
  refine ⟨rfl, rfl, rfl, a0, ?_, a2, a3, ?_, a5, a6, ?_, ?_, rfl, rfl⟩
  · exact congrArg (fun x => VerifiableInference.Desc.Kinds.Head.powersOf x 9) a1
  · exact congrArg (fun x => VerifiableInference.Desc.Kinds.Head.powersOf x 7) a4
  · exact congrArg (fun r : Point => r.extract 0 (headLt p)) a7
  · exact congrArg (fun r : Point =>
      (r.extract (headLt p) (headLt p + headLPd p)).reverse) a7

/-- **The maker of the head's tables of reads gives one answer at both.** ht is spent on the field
win alone, which this proof does not keep: the maker's answer is the same at every y. -/
theorem tables_tie [sz : Head.Sizes] [Head.Policy] [request : Head.Request]
    [tk : Head.Token] [FinalNorm.In] [Head.In] (p : Head.Par) (y : Nat) (hp : sz = p.sizes)
    (ht : tk = ⟨y⟩) (g1 : OnBytes.Model.Forest.Heard) {F G : Fork}
    {H : Head.HeardAll} {rs : List Fmt.RoundView} (hW : WellLaid F)
    (h : VerifiableInference.Desc.Kinds.Head.hear F rs = some (H, G, []))
    (hzt : (FinalNorm.zt).size = Norm.lt) (hS : OnBytes.Model.Head.Shape)
    (L : OnBytes.Model.Head.HL) (hpl : OnBytes.Model.Head.HPlanH2)
    (cov : OnBytes.Model.Head.Covered) :
    VerifiableInference.Desc.K8.ReadsQuiet.tables hS L hpl cov (Head.heardOf g1 H) =
      VerifiableInference.Desc.K8.ReadsQuiet.tables hS L hpl cov
        (headHeardWhole p request y g1 (rs.map (·.drawn))) := by
  obtain ⟨_, b1, b2, b3, _, b5, _, _, b8, b9, b10, _, b12, b13⟩ :=
    heardOf_tie p y hp ht g1 hW h hzt
  exact tables_nine hS L hpl cov b3 b5 b8 b9 b10 b1 b2 b12 b13

/-- **AT A CHAIN'S CHALLENGES**: front, later: any two lists; meant: the challenges heard before the
sub-protocol began, and any behind its own. -/
theorem logits_tie [sz : Head.Sizes] [Head.Policy] [request : Head.Request]
    [tk : Head.Token] [FinalNorm.In] [Head.In] (p : Head.Par) (y : Nat) (hp : sz = p.sizes)
    (ht : tk = ⟨y⟩) (g1 : OnBytes.Model.Forest.Heard) {F G : Fork}
    {H : Head.HeardAll} {rs : List Fmt.RoundView} (hW : WellLaid F)
    (h : VerifiableInference.Desc.Kinds.Head.hear F rs = some (H, G, []))
    (hzt : (FinalNorm.zt).size = Norm.lt) (front later : List Fmt.Drawn) :
    (Head.heardOf g1 H).tH.r =
      headTHr p front.length (front ++ (rs.map (·.drawn) ++ later)) ∧
    (Head.heardOf g1 H).rs = headRs p front.length (front ++ (rs.map (·.drawn) ++ later)) ∧
    (Head.heardOf g1 H).win = headWin p request y := by
  obtain ⟨_, _, _, _, _, _, _, a7⟩ := hearing_tie p hp hW h hzt
  obtain ⟨_, _, _, _, tS, tP, tN, tL, hrs, lS, lP, lN, lL⟩ := hear_pieces hW h
  subst hp ht
  letI : Head.Sizes := p.sizes
  have zL : (FinalNorm.zt ++ halves Norm.lPd).size = headLt p + headLPd p := by
    rw [Array.size_append, hzt]
    unfold halves
    rw [Array.size_replicate]
    rfl
  have v7 : headInFront p 7 = headLPd p + headLt p + 7 + (headLt p + 3) + (headLt p + 3) := by
    show 0 + 1 + 1 + (headLPd p + headLt p + 3) + 1 + 1 + (headLt p + 3) + (headLt p + 3) = _
    omega
  have hlen : (rs.map (·.drawn)).length =
      headInFront p 7 + (headLt p + headLPd p + 3) := by
    have lS' : tS.length = headLPd p + headLt p + 3 := lS
    have lP' : tP.length = headLt p + 3 := lP
    have lN' : tN.length = headLt p + 3 := by rw [lN, hzt]; rfl
    rw [List.length_map, hrs, v7]
    simp only [List.length_append, List.length_singleton, lS', lP', lN', lL, zL]
    omega
  have key : headLogitsR p front.length (front ++ (rs.map (·.drawn) ++ later)) =
      headSumR p 7 (headLt p + headLPd p) (rs.map (·.drawn)) := by
    unfold headLogitsR headSumR headLogitsAt
    congr 1
    refine List.map_congr_left fun j hj => ?_
    have hj' : j < headLt p + headLPd p := List.mem_range.1 hj
    rw [Nat.add_assoc, elemOf_shift front _ later _ (by rw [hlen]; omega)]
  refine ⟨?_, ?_, rfl⟩
  · show H.2.2.logits.r.extract 0 (headLt p) =
      (headLogitsR p front.length (front ++ (rs.map (·.drawn) ++ later))).extract 0 (headLt p)
    rw [key, a7]
  · show (H.2.2.logits.r.extract (headLt p) (headLt p + headLPd p)).reverse =
      ((headLogitsR p front.length (front ++ (rs.map (·.drawn) ++ later))).extract (headLt p)
        (headLt p + headLPd p)).reverse
    rw [key, a7]

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.elemOf_rounds
#print axioms ProofFile.Honest.K6.stretch_range
#print axioms ProofFile.Honest.K6.at_mid
#print axioms ProofFile.Honest.K6.elemOf_shift
#print axioms ProofFile.Honest.K6.hearing_tie
#print axioms ProofFile.Honest.K6.heardOf_tie
#print axioms ProofFile.Honest.K6.tables_tie
#print axioms ProofFile.Honest.K6.logits_tie
