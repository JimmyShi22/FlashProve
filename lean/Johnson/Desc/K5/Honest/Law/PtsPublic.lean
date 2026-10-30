-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/PtsPublic.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: the premises of `meets_behind` (Johnson/Desc/K5/Honest/Law/MeetsBehind.lean)
on the numbers of challenges, on the key points' lengths and on the lists of pieces, FROM THE PUBLIC
PREMISES IN ONE (`PublicAll`, Johnson/Desc/K5/Honest/Law/PublicAtPlan.lean), the lengths of what was
heard, and the lengths of the lookup's key points. Statements with their proofs; arithmetic on
lengths.

Main names:
  `size_chal`, `size_piecesOf`   counts
  `chalLens_of_lengths`   `ChalLens` (Law/PtsFitOf.lean) from the lengths of what was heard, in the
                     planner's letters
  `planes_public`    every plane claim: its call's key point is long enough; its list has a piece
                     for each pair, in the pairs' order
  `lists_public`     the three lists of the division: piece b is pair b

EVERY STATEMENT BUT `size_piecesOf` IS CONDITIONAL (`size_chal`: on the number of challenges heard).
The premises, and who is meant to show each:
  `PublicAll`, and the shape's numbers of coordinates of the two regions: public.
  the lengths of what was heard: facts on the return of the verifier's hearing.
  the verifier's function of the points returns: the caller's.
  Kz: each lookup call's key point has the call's number of coordinates: THE LOOKUP's, of what it
    hands on.
Limits. `PublicAll` holds that the place has two remainder-table units and two softmax-table units:
a plan in which the layers of the group have more than one shift is not reached. Nothing here says
that a premise holds at any place or run.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.PtsFitOf
import Johnson.Desc.K5.Honest.Law.MeetsRuns
import Johnson.Desc.K5.Honest.Law.PublicImplies

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E zeroE)
open OnBytes.Road.L5 (callsOf)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (RemP UnitG Pts Heard Left chal pointsOf remainders
  piecesOf pcsSorted)
open Inst.Model.AttSeg (Step)

/-! ## The numbers of challenges -/

/-- All challenges of a sumcheck but the last, counted. -/
theorem size_chal (h : VerifiableInference.Desc.Part.MaskedSum.Heard) {n : ℕ}
    (hl : h.r.length = n + 1) : (chal h).size = n := by
  unfold chal
  rw [List.size_toArray, List.length_dropLast, hl, Nat.add_sub_cancel]

/-- **`ChalLens` from the lengths of what was heard, in the planner's letters.** CONDITIONAL on the
public premises in one (`PublicAll`, Law/PublicAtPlan.lean) and on: as many units were heard as the
planner counts; of each sumcheck one challenge a variable of the planner's and one more; the round
that draws many elements has the planner's number of them. These are facts on the hearing's return.
-/
theorem chalLens_of_lengths {P : Pub5} {fs : OnBytes.Model.Forest.Shape} (Pu : PublicAll P fs)
    {hd : Heard} (nU : hd.scores.size = P.x.score.length)
    (lU : ∀ (i : ℕ) (u : ℕ × ℕ) (o : ℕ × VerifiableInference.Desc.Part.MaskedSum.Heard),
      P.x.score[i]? = some u → hd.scores[i]? = some o → o.2.r.length = u.1 + 1)
    (lE : hd.division.r.length = P.x.e + 1) (lM : hd.below.r.length = P.x.valueM + 1)
    (lD : hd.on.r.length = P.x.valueD + 1) (lF : hd.atIndex.r.length = P.x.attained + 1)
    (lK : hd.key.r.length = P.x.lt + P.x.lgk + P.x.lt + 1)
    (lH : hd.cells.r.length = P.x.bits + 1)
    (lP : hd.point.size = 2 * P.x.lgk + 2 * P.x.lt + 4) : ChalLens P.S hd := by
  have H := Pu.sized
  have Pl := Pu.planned
  have hn := H.Z.lnT
  have htok : P.S.cf.lt = P.S.lnT + P.S.cf.lB := H.tok
  have xlt : P.x.lt = P.S.cf.lt := Pl.lt
  have xlg : P.x.lgk = P.S.cf.lgk := Pl.lgk
  have vE : P.x.e = P.S.cf.lgk + (P.S.lnT - 1 + 1 + P.S.cf.lB) := (cut_iSE P.x).symm.trans Pl.vSE
  have vM : P.x.valueM = P.S.cf.lgk + (P.S.lnT - 1) + (P.S.lnT - 1 + 1) + P.S.cf.lB :=
    (cut_iVM P.x).symm.trans Pl.vVM
  have vD : P.x.valueD = P.S.cf.lgk + (P.S.lnT - 1 + 1) + P.S.cf.lB :=
    (cut_iVD P.x).symm.trans Pl.vVD
  have vF : P.x.attained = P.S.lnT - 1 + 1 + P.S.cf.lB + P.S.cf.lgk + P.S.cf.ldh :=
    (cut_iSF P.x).symm.trans Pl.vSF
  have vH : P.x.bits = P.S.lnT - 1 + 1 + P.S.cf.lB + P.S.cf.lgk + 4 :=
    (cut_iHB P.x).symm.trans Pl.vHB
  refine ⟨fun o ho => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨n, hn'⟩ := List.mem_iff_getElem?.1 ho
    rw [Array.getElem?_toList] at hn'
    have hlt : n < 2 := by
      rcases Nat.lt_or_ge n 2 with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none (by rw [nU, Pu.score2]; exact h')] at hn'
        cases hn'
    obtain ⟨u, hu⟩ : ∃ u, P.x.score[n]? = some u :=
      ⟨_, List.getElem?_eq_getElem (by rw [Pu.score2]; exact hlt)⟩
    rw [size_chal o.2 (lU n u o hu hn'), ← cut_unit P.x n u hu]
    interval_cases n
    · rw [Pu.vKM]
      show P.S.cf.lgk + P.S.cf.ldh ≤
        P.S.cf.lgk + (P.S.lnT - 1) + (P.S.lnT - 1 + 1) + P.S.cf.ldh
      omega
    · rw [Pu.vKD]
      show P.S.cf.lgk + P.S.cf.ldh ≤ P.S.cf.lgk + (P.S.lnT - 1 + 1) + P.S.cf.ldh
      omega
  · rw [size_chal _ lE]
    omega
  · rw [size_chal _ lM]
    omega
  · rw [size_chal _ lD]
    omega
  · rw [size_chal _ lF]
    show _ = P.S.cf.lt + P.S.cf.lgk + P.S.cf.ldh
    omega
  · rw [size_chal _ lK]
    omega
  · rw [size_chal _ lH]
    show _ = P.S.cf.lt + P.S.cf.lgk + 4
    omega
  · rw [lP]
    omega

/-! ## The plane claims and the three lists -/

/-- The pieces of a unit are as many as the unit lists. -/
theorem size_piecesOf (u : UnitG) (key : Array E) : (piecesOf u key).size = u.pcs.length := by
  rw [pieces_eq]
  simp [pcsSorted]

/-- **Every plane claim that the verifier's function of the points lays**: its call's key point has
at least the coordinates of its region; its list has a piece for each pair, in the pairs' order.
CONDITIONAL on `PublicAll`; N: the shape's numbers of coordinates of the two regions (public); the
function returns; Kz: EACH LOOKUP CALL's KEY POINT HAS THE CALL's NUMBER OF COORDINATES: the
lookup's, of what it hands on. -/
theorem planes_public {P : Pub5} {fs : OnBytes.Model.Forest.Shape} (Pu : PublicAll P fs)
    (N : OnBytes.Road.L5.Norm P.S) {zk : Array (Array E)} {hh : Heard} {L : Left} {p : Pts}
    (hP : pointsOf P.g zk hh L = some p)
    (Kz : ∀ q : Fin 4, (zk.getD q.1 #[]).size = (callsOf fs).a q) :
    ∀ pc ∈ p.planes.toList,
      (if pc.isD = true then P.S.nD else P.S.nM) ≤ (zk.getD pc.call #[]).size ∧
        PairsAre P.g pc.pw ∧ pc.pw.size = P.S.NP := by
  intro pc hpc
  obtain ⟨r1, r2, u1, u2, _, _, _, U, _, _, _, _⟩ := Pu.units
  have F := Pu.lookFits
  have PA := K5Law.points_are hP
  have Pl := K5Law.planes_are hP
  have nP := (K5Law.points_counts hP).2.1
  have hM := N.nM
  have hD := N.nD
  have lM : P.S.cf.lgk + (P.S.lnT - 1) + (P.S.lnT - 1 + 1) + P.S.cf.lB + P.S.cf.lB ≤
      (callsOf fs).a 0 := F.lM
  have big : ∀ b : Bool, (if b = true then P.S.nD else P.S.nM) ≤ (callsOf fs).a 0 := by
    intro b
    cases b
    · rw [if_neg (by decide)]
      omega
    · rw [if_pos rfl]
      omega
  -- the claim's unit: one of the four, at call 0 or 1
  have key : ∃ u : UnitG, (u ∈ remainders P.g ∨ u ∈ P.g.scores) ∧ pc.call = u.call ∧
      pc.pw = piecesOf u (zk.getD u.call #[]) := by
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hpc
    rw [Array.getElem?_toList] at hn
    have hlt : n < hh.remainders.size + hh.scores.size := by
      rcases Nat.lt_or_ge n (hh.remainders.size + hh.scores.size) with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none (by rw [nP]; exact h')] at hn
        cases hn
    rcases Nat.lt_or_ge n hh.remainders.size with h1 | h1
    · obtain ⟨r, e1⟩ : ∃ r, (P.g.units .kr [.rm, .rd])[n]? = some r :=
        ⟨_, List.getElem?_eq_getElem (by rw [Pl.nR]; exact h1)⟩
      have e2 := Pl.rem n _ _ e1 (Array.getElem?_eq_getElem h1)
      rw [e2] at hn
      refine ⟨P.g.unitAt r.1 r.2.1 r.2.2,
        .inl (List.mem_map.2 ⟨_, List.mem_of_getElem? e1, rfl⟩), ?_, ?_⟩ <;>
        rw [← Option.some.inj hn] <;> rfl
    · have h2 : n - hh.remainders.size < hh.scores.size := by omega
      obtain ⟨v, e1⟩ : ∃ v, P.g.scores[n - hh.remainders.size]? = some v :=
        ⟨_, List.getElem?_eq_getElem (by rw [PA.nH]; exact h2)⟩
      obtain ⟨k, _, c1, c2, _⟩ := Pl.unit _ _ _ e1 (Array.getElem?_eq_getElem h2)
      rw [c1, show hh.remainders.size + (n - hh.remainders.size) = n by omega, hn] at c2
      refine ⟨v, .inr (List.mem_of_getElem? e1), ?_, ?_⟩ <;>
        rw [Option.some.inj c2] <;> rfl
  obtain ⟨u, hu, ec, ew⟩ := key
  have hrem : remainders P.g = [r1, r2] := U.rem
  have hsco : P.g.scores = [u1, u2] := U.sco
  have four : (u.call = 0 ∨ u.call = 1) ∧ u.pcs.length = P.S.NP := by
    rcases hu with hu | hu
    · rw [hrem] at hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact ⟨.inl U.m1.call, np_of_unitIs U.m1⟩
      · exact ⟨.inl U.d1.call, np_of_unitIs U.d1⟩
    · rw [hsco] at hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact ⟨.inr U.m2.call, np_of_unitIs U.m2⟩
      · exact ⟨.inr U.d2.call, np_of_unitIs U.d2⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [ec]
    rcases four.1 with h0 | h0
    · rw [h0]
      exact (big pc.isD).trans (Nat.le_of_eq (Kz 0).symm)
    · rw [h0]
      exact (big pc.isD).trans (Nat.le_of_eq (F.a01.trans (Kz 1).symm))
  · rw [ew]
    rcases hu with hu | hu
    · exact Pu.pairsRem u hu _
    · exact Pu.pairsScores u hu _
  · rw [ew, size_piecesOf]
    exact four.2

/-- **The three lists of the division**: piece b is pair b. CONDITIONAL on `PublicAll` and the
function's return. -/
theorem lists_public {P : Pub5} {fs : OnBytes.Model.Forest.Shape} (Pu : PublicAll P fs)
    {zk : Array (Array E)} {hh : Heard} {L : Left} {p : Pts}
    (hP : pointsOf P.g zk hh L = some p) :
    PairsAre P.g p.d.pwW ∧ PairsAre P.g p.d.pwX ∧ PairsAre P.g p.d.pwH := by
  obtain ⟨uW, uX, uH, sW, sX, sH, eW, eX, eH, _, _, _⟩ := (K5Law.cut5w_of hP).at'
  rw [eW, eX, eH]
  exact ⟨Pu.pairsWl uW sW _, Pu.pairsIx uX sX _, Pu.pairsWh uH sH _⟩

end H2K5.Honest

#print axioms H2K5.Honest.size_chal
#print axioms H2K5.Honest.chalLens_of_lengths
#print axioms H2K5.Honest.size_piecesOf
#print axioms H2K5.Honest.planes_public
#print axioms H2K5.Honest.lists_public
