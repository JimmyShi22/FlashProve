-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/NoBadTrue.lean: Lemma 2b's PREMISE "NO BAD DRAW" CAN BE MET: AT THE TRUTH THE RULE's LISTS ARE
EMPTY. `noBad_of_empty` (generic in the sets; the converse of Bad.lean's two bridges): at a transcript
that the part's reading takes, if the set for eps and each round's set at that round's completed
polynomial are empty, then NoBad holds of Bad.lean's rule. `noBad_true`: at Lemma2b.lean's rule badP
(which lemma2b and K06's core and out name): IF the claimed sum's hidden scalar is the true one
(cvP = sigP) AND each round's completed polynomial is the true round polynomial tqP
(sound_hear_true), THEN NoBad (badP c mask F0) t, WHATEVER IS DRAWN.
WHAT IT DOES NOT SAY: that there is such a transcript: that an honest prover's rounds, as elements of
the program, complete to tqP, and that the hearing returns on them, is stated nowhere
(MaskedSumTruth.lean says so of itself). tqP is chosen (Classical.choose): no run can evaluate it.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.Lemma2b

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE addE mulE okE)
open OnBytes.Model (Reading Fork)
open Polynomial
open Part.MaskedSum (Var VarsRead Sent scalars movesOf Lens readAll leadScalars)

section Generic
variable (all : List Var) (cvOf : E → K) (bE : K → K → K → Finset K)
  (bd : K → K → K → K → List (K[X] × K) → K[X] → Finset K)
  {t used : List Fmt.RoundView} {r0 rv : Fmt.RoundView} {c0 mu eps : E} {rounds : List (List E × E)}

/-- **Where the sets are empty, no draw is bad.** -/
theorem noBad_of_empty (ht : t = r0 :: (used ++ [rv])) (h0 : Sent r0 2 1 [c0, mu] [eps])
    (hv : VarsRead all used rounds) (h3 : ∀ v ∈ all, v.d = 3) (hrv : rv.drawn.elems = [])
    (hE : bE (rd (tgt c0)) (cvOf c0) (rd mu) = ∅)
    (hB : ∀ i m, (movesOf Reading.gl all rounds (addE mu (mulE eps (tgt c0))))[i]? = some m →
      bd (rd (tgt c0)) (cvOf c0) (rd mu) (rd eps)
        ((movesOf Reading.gl all rounds (addE mu (mulE eps (tgt c0)))).take i) m.1 = ∅) :
    NoBad (bad all cvOf bE bd) t := by
  obtain ⟨e0, he0, heps⟩ := drawn_one h0
  have hs : scalars r0.vals = some [c0, mu] := h0.1
  have hg0 : ([c0, mu] : List E).getD 0 zeroE = c0 := rfl
  have hg1 : ([c0, mu] : List E).getD 1 zeroE = mu := rfl
  obtain ⟨hl1, hl2⟩ := hv.length
  have hlens : Lens all rounds :=
    Part.MaskedSum.lens_of_read hv (fun v hv' => by rw [h3 v hv']; omega)
  have hch := Part.MaskedSum.movesOf_chal Reading.gl all rounds (addE mu (mulE eps (tgt c0))) hlens
  have hMl : (movesOf Reading.gl all rounds (addE mu (mulE eps (tgt c0)))).length
      = rounds.length := by
    have := congrArg List.length hch
    simpa using this
  intro j r hj x hx
  cases j with
  | zero =>
    have hr : r = r0 := by
      rw [ht] at hj
      exact (Option.some.inj hj).symm
    subst hr
    simp only [List.take_zero, List.nil_append]
    have hraw : raw all cvOf bE bd [{ r with drawn := ⟨[], [], [], none⟩ }] = [] := by
      show (bE (rd (tgt (((scalars r.vals).getD []).getD 0 zeroE)))
        (cvOf (((scalars r.vals).getD []).getD 0 zeroE))
        (rd (((scalars r.vals).getD []).getD 1 zeroE))).toList.map ofK = []
      rw [hs]
      simp only [Option.getD_some, hg0, hg1]
      rw [hE]; simp
    unfold bad
    rw [hraw]; simp
  | succ i =>
    by_cases hiu : i < used.length
    · have hru : used[i]? = some used[i] := List.getElem?_eq_getElem hiu
      have hti : t[i + 1]? = some used[i] := by
        rw [ht, List.getElem?_cons_succ, List.getElem?_append_left hiu]; exact hru
      have hr : r = used[i] := by
        rw [hti] at hj
        exact (Option.some.inj hj).symm
      subst hr
      obtain ⟨v, s, g, hvi, hli, hsent⟩ := varsRead_get hv i _ hru
      have hi : i < (movesOf Reading.gl all rounds (addE mu (mulE eps (tgt c0)))).length := by omega
      have hm := List.getElem?_eq_getElem hi
      have htake : t.take (i + 1) = r0 :: used.take i := by
        rw [ht, List.take_succ_cons, List.take_append_of_le_length (le_of_lt hiu)]
      rw [htake, List.cons_append]
      have hne : List.take i used ++
          [({ used[i] with drawn := ⟨[], [], [], none⟩ } : Fmt.RoundView)] ≠ [] := by simp
      have hlt : (List.take i used).length = i := by
        rw [List.length_take, Nat.min_eq_left (le_of_lt hiu)]
      have hlen : (List.take i used ++
          [({ used[i] with drawn := ⟨[], [], [], none⟩ } : Fmt.RoundView)]).length - 1 = i := by
        rw [List.length_append, hlt]; simp
      have hro : roundsOf used = rounds := roundsOf_read hv
      have hml : (List.map (fun r : Fmt.RoundView => ((scalars r.vals).getD [],
                 E.ofTriple (r.drawn.elems.headD (0, 0, 0)))) (List.take i used)).length = i := by
        rw [List.length_map, hlt]
      have hR1 : (roundsOf (List.take i used ++
          [({ used[i] with drawn := ⟨[], [], [], none⟩ } : Fmt.RoundView)])).take i = rounds.take i := by
        rw [← hro]
        unfold roundsOf
        rw [List.map_append, List.take_append_of_le_length (le_of_eq hml.symm),
          List.take_of_length_le (le_of_eq hml), List.map_take]
      have hR2 : ((roundsOf (List.take i used ++
          [({ used[i] with drawn := ⟨[], [], [], none⟩ } : Fmt.RoundView)]))[i]?).map (·.1)
          = (rounds[i]?).map (·.1) := by
        rw [hli]
        unfold roundsOf
        rw [List.map_append, List.getElem?_append_right (le_of_eq hml), hml, Nat.sub_self]
        simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero, Option.map_some]
        rw [hsent.1]
        rfl
      have e1 := movesOf_take Reading.gl i all _ rounds (addE mu (mulE eps (tgt c0))) hR1
      have e2 := movesOf_poly Reading.gl i all _ rounds (addE mu (mulE eps (tgt c0))) hR1 hR2
      unfold bad
      rw [raw_cons all cvOf bE bd r0 _ hne, hlen, hs, he0]
      simp only [Option.getD_some, hg0, hg1, List.headD_cons]
      rw [← heps, e1, e2, hm]
      simp only [Option.map_some, Option.getD_some]
      rw [hB i _ hm]
      simp
    · have hle : used.length ≤ i := Nat.le_of_not_lt hiu
      rw [ht, List.getElem?_cons_succ, List.getElem?_append_right hle] at hj
      cases hk : i - used.length with
      | zero =>
        rw [hk] at hj
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [hrv] at hx
        simp at hx
      | succ k =>
        rw [hk] at hj
        simp at hj

end Generic

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] (c : Cells) (mask : Nat → E)
  (F0 : Fork)

/-- **AT THE TRUTH NO DRAW IS BAD**, of Lemma 2b's own rule. R and c0 are what the part's reading makes
of the rounds t. -/
theorem noBad_true {t : List Fmt.RoundView} {R : Part.MaskedSum.Read} {c0 : E}
    (hread : readAll kP t = some R) (hlead : leadScalars kP t = some [c0])
    (hC : cvP mask F0 c0 = sigP c)
    (hq : ∀ i m, (movesOf Reading.gl kP.all R.rounds
        (addE R.mu (mulE R.eps (tgt c0))))[i]? = some m →
      m.1 = tqP c mask F0 (rd (tgt c0)) (cvP mask F0 c0) (rd R.mu) (rd R.eps)
        (((movesOf Reading.gl kP.all R.rounds (addE R.mu (mulE R.eps (tgt c0)))).take i).map
          (·.2))) :
    NoBad (badP c mask F0) t := by
  obtain ⟨r0, used, rv, front, ht, hs0, hfl, hvr, hsv⟩ :=
    Part.MaskedSum.readAll_spec (show readAll ⟨1, vsP, some ⟨2, 2⟩⟩ t = some R from hread)
  obtain ⟨c1, rfl⟩ := List.length_eq_one_iff.mp hfl
  have hs0' : Sent r0 2 1 [c1, R.mu] [R.eps] := hs0
  have hc : c1 = c0 := by
    have h1 : leadScalars ⟨1, vsP, some ⟨2, 2⟩⟩ t = some [c0] := hlead
    rw [ht, lead_of_sent hs0'] at h1
    simpa using h1
  subst hc
  have hrv : rv.drawn.elems = [] := by
    have := hsv.2.2.1
    exact List.length_eq_zero_iff.mp this
  refine noBad_of_empty kP.all (cvP mask F0) (bEP c mask F0) (bdP c mask F0) ht hs0' hvr allP_d hrv
    (bEP_empty c mask F0 _ _ hC _) ?_
  intro i m hm
  rw [hq i m hm]
  exact bdP_empty c mask F0 _ _ _ _ _

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.noBad_true
