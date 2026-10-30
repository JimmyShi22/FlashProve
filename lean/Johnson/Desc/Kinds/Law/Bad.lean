-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Bad.lean: FROM SETS OF THE FIELD's ELEMENTS TO A RULE ON PARTIAL TRANSCRIPTS (bridge
B7 of Lemma 2b). The law of the masked sumcheck (MaskedSumSound.lean: sound_hear) gives, for the
two values T and Cv of the claimed form, a set of bad eps for each mu and a set of bad challenges for
each mu, eps, moves in front and round's polynomial. HeadLaw.lean's Lemma 2b wants ONE rule from a
front of a transcript (the rounds in front, whole, and this round's message) to a list of elements.
`bad`: that rule: it reads the claimed scalar, mu, eps and the rounds off that front by
plain maps; the list is cut at the statement's ceiling, so that the ceiling holds at every list of
rounds, well made or not. `bridge`: at a transcript that the part's own reader has read, whose
elements are canonical and none of which is bad by the rule, no element is in that law's sets.
GENERIC: the variables, the value Cv as a function of the claimed scalar, and the two families of
sets are letters.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.Ends

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE addE mulE okE)
open OnBytes.Model (Reading)
open Polynomial
open Part.MaskedSum (Var VarsRead Sent scalars movesOf Lens)
open OnBytes.Desc.First.P1 (dAt)

/-- What the ledger's `publicPart` makes of the one slot's form at the shown scalar c0. -/
def tgt (c0 : E) : E := addE zeroE (mulE oneE c0)

variable (all : List Var) (cvOf : E → K) (bE : K → K → K → Finset K)
  (bd : K → K → K → K → List (K[X] × K) → K[X] → Finset K)

/-- The rule, uncut. -/
def raw : List Fmt.RoundView → List E
  | [] => []
  | [r0] =>
    let sc := (scalars r0.vals).getD []
    (bE (rd (tgt (sc.getD 0 zeroE))) (cvOf (sc.getD 0 zeroE)) (rd (sc.getD 1 zeroE))).toList.map ofK
  | r0 :: r1 :: tl =>
    let sc := (scalars r0.vals).getD []
    let eps := E.ofTriple (r0.drawn.elems.headD (0, 0, 0))
    let ms := movesOf Reading.gl all (roundsOf (r1 :: tl))
      (addE (sc.getD 1 zeroE) (mulE eps (tgt (sc.getD 0 zeroE))))
    (bd (rd (tgt (sc.getD 0 zeroE))) (cvOf (sc.getD 0 zeroE)) (rd (sc.getD 1 zeroE)) (rd eps)
      (ms.take tl.length) (((ms[tl.length]?).map (·.1)).getD 0)).toList.map ofK

/-- **The rule.** -/
def bad (h : List Fmt.RoundView) : List E :=
  (raw all cvOf bE bd h).take (((h.getLast?.map fun r => r.vals.length).getD 0) + 1)

/-- The statement's ceiling, at every list of rounds. -/
theorem bad_length (h : List Fmt.RoundView) :
    (bad all cvOf bE bd h).length ≤ ((h.getLast?.map fun r => r.vals.length).getD 0) + 1 := by
  unfold bad
  exact List.length_take_le _ _

theorem scalars_length : ∀ (l : List Fmt.ItemValue) (s : List E), scalars l = some s → s.length = l.length
  | [], s, h => by
    simp only [scalars, Option.some.injEq] at h
    subst h; rfl
  | .e x :: l, s, h => by
    simp only [scalars] at h
    cases hl : scalars l with
    | none => rw [hl] at h; simp at h
    | some s' =>
      rw [hl] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      simp [scalars_length l s' hl]
  | .f _ :: _, _, h => by simp [scalars] at h
  | .word _ :: _, _, h => by simp [scalars] at h
  | .root _ :: _, _, h => by simp [scalars] at h
  | .answer _ :: _, _, h => by simp [scalars] at h

/-- The part's reader, at one round. -/
theorem varsRead_get : ∀ {vs : List Var} {used : List Fmt.RoundView} {l : List (List E × E)},
    VarsRead vs used l → ∀ (i : Nat) (r : Fmt.RoundView), used[i]? = some r →
    ∃ v s g, vs[i]? = some v ∧ l[i]? = some (s, g) ∧ Sent r (v.d - 1) 1 s [g]
  | [], [], [], _, i, r, h => by simp at h
  | [], [], _ :: _, h, _, _, _ => h.elim
  | [], _ :: _, _, h, _, _, _ => h.elim
  | _ :: _, [], _, h, _, _, _ => h.elim
  | _ :: _, _ :: _, [], h, _, _, _ => h.elim
  | v :: vs, r0 :: rs, (s, g) :: l, h, 0, r, hr => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
    subst hr
    exact ⟨v, s, g, rfl, rfl, h.1⟩
  | v :: vs, r0 :: rs, (s, g) :: l, h, i + 1, r, hr => by
    simp only [List.getElem?_cons_succ] at hr ⊢
    exact varsRead_get h.2 i r hr

/-- The rule on a first round and a tail that is not empty. -/
theorem raw_cons (r0 : Fmt.RoundView) (tl : List Fmt.RoundView) (h : tl ≠ []) :
    raw all cvOf bE bd (r0 :: tl) =
      (bd (rd (tgt (((scalars r0.vals).getD []).getD 0 zeroE)))
        (cvOf (((scalars r0.vals).getD []).getD 0 zeroE))
        (rd (((scalars r0.vals).getD []).getD 1 zeroE))
        (rd (E.ofTriple (r0.drawn.elems.headD (0, 0, 0))))
        ((movesOf Reading.gl all (roundsOf tl)
          (addE (((scalars r0.vals).getD []).getD 1 zeroE)
            (mulE (E.ofTriple (r0.drawn.elems.headD (0, 0, 0)))
              (tgt (((scalars r0.vals).getD []).getD 0 zeroE))))).take (tl.length - 1))
        ((((movesOf Reading.gl all (roundsOf tl)
          (addE (((scalars r0.vals).getD []).getD 1 zeroE)
            (mulE (E.ofTriple (r0.drawn.elems.headD (0, 0, 0)))
              (tgt (((scalars r0.vals).getD []).getD 0 zeroE)))))[tl.length - 1]?).map
                (·.1)).getD 0)).toList.map ofK := by
  cases tl with
  | nil => exact absurd rfl h
  | cons r1 tl => rfl

theorem not_mem_take {x : E} {l : List E} {n : Nat} (h : x ∉ l.take n) (hl : l.length ≤ n) :
    x ∉ l := by
  rwa [List.take_of_length_le hl] at h

/-- One drawn element. -/
theorem drawn_one {r : Fmt.RoundView} {n : Nat} {s : List E} {g : E} (h : Sent r n 1 s [g]) :
    ∃ e, r.drawn.elems = [e] ∧ g = E.ofTriple e := by
  obtain ⟨_, _, h3, h4⟩ := h
  cases he : r.drawn.elems with
  | nil => rw [he] at h3; simp at h3
  | cons e es =>
    cases es with
    | nil =>
      rw [he] at h4
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h4
      exact ⟨e, rfl, h4⟩
    | cons _ _ => rw [he] at h3; simp at h3

section Bridge
variable {all cvOf bE bd}
variable {t : List Fmt.RoundView} {r0 rv : Fmt.RoundView} {used : List Fmt.RoundView} {c0 mu eps : E}
  {rounds : List (List E × E)}

/-- **The bridge, at eps.** -/
theorem bridge_eps (ht : t = r0 :: (used ++ [rv])) (h0 : Sent r0 2 1 [c0, mu] [eps])
    (hcan : Canonical t) (hnb : NoBad (bad all cvOf bE bd) t)
    (cE : ∀ T Cv m, (bE T Cv m).card ≤ 1) :
    rd eps ∉ bE (rd (tgt c0)) (cvOf c0) (rd mu) := by
  obtain ⟨e, he, rfl⟩ := drawn_one h0
  have hs : scalars r0.vals = some [c0, mu] := h0.1
  have hmem : r0 ∈ t := by rw [ht]; simp
  have hok : okE (E.ofTriple e) = true := (hcan r0 hmem).2 e (by rw [he]; simp)
  have hx := hnb 0 r0 (by rw [ht]; rfl) e (by rw [he]; simp)
  simp only [List.take_zero, List.nil_append] at hx
  have hraw : raw all cvOf bE bd [{ r0 with drawn := ⟨[], [], [], none⟩ }]
      = (bE (rd (tgt c0)) (cvOf c0) (rd mu)).toList.map ofK := by
    show (bE (rd (tgt (((scalars r0.vals).getD []).getD 0 zeroE)))
      (cvOf (((scalars r0.vals).getD []).getD 0 zeroE))
      (rd (((scalars r0.vals).getD []).getD 1 zeroE))).toList.map ofK = _
    rw [hs]; rfl
  unfold bad at hx
  rw [hraw] at hx
  refine not_mem_of_list hok (not_mem_take hx ?_)
  rw [List.length_map, Finset.length_toList]
  have := cE (rd (tgt c0)) (cvOf c0) (rd mu)
  omega

/-- **The bridge, at the variables' rounds.** -/
theorem bridge_rounds (ht : t = r0 :: (used ++ [rv])) (h0 : Sent r0 2 1 [c0, mu] [eps])
    (hv : VarsRead all used rounds) (h3 : ∀ v ∈ all, v.d = 3)
    (hcan : Canonical t) (hnb : NoBad (bad all cvOf bE bd) t)
    (cB : ∀ T Cv m e pre g,
      (bd T Cv m e pre g).card < dAt (all.map (Var.wt Reading.gl)) pre.length) :
    ∀ i m, (movesOf Reading.gl all rounds (addE mu (mulE eps (tgt c0))))[i]? = some m →
      m.2 ∉ bd (rd (tgt c0)) (cvOf c0) (rd mu) (rd eps)
        ((movesOf Reading.gl all rounds (addE mu (mulE eps (tgt c0)))).take i) m.1 := by
  intro i m hm
  obtain ⟨e0, he0, heps⟩ := drawn_one h0
  have hs : scalars r0.vals = some [c0, mu] := h0.1
  obtain ⟨hl1, hl2⟩ := hv.length
  have hlens : Lens all rounds :=
    Part.MaskedSum.lens_of_read hv (fun v hv' => by rw [h3 v hv']; omega)
  have hch := Part.MaskedSum.movesOf_chal Reading.gl all rounds (addE mu (mulE eps (tgt c0))) hlens
  have hMl : (movesOf Reading.gl all rounds (addE mu (mulE eps (tgt c0)))).length
      = rounds.length := by
    have := congrArg List.length hch
    simpa using this
  have hi : i < (movesOf Reading.gl all rounds (addE mu (mulE eps (tgt c0)))).length :=
    (List.getElem?_eq_some_iff.mp hm).1
  have hiu : i < used.length := by omega
  have hr : used[i]? = some used[i] := List.getElem?_eq_getElem hiu
  obtain ⟨v, s, g, hvi, hli, hsent⟩ := varsRead_get hv i _ hr
  obtain ⟨ge, hge, rfl⟩ := drawn_one hsent
  have hvd : v.d = 3 := h3 v (List.mem_of_getElem? hvi)
  have hm2 : m.2 = rd (E.ofTriple ge) := by
    have := congrArg (fun l => l[i]?) hch
    simp only [List.getElem?_map, hm, hli, Option.map_some, Option.some.injEq] at this
    exact this
  have hmem : used[i] ∈ t := by rw [ht]; simp
  have hok : okE (E.ofTriple ge) = true := (hcan _ hmem).2 ge (by rw [hge]; simp)
  have hti : t[i + 1]? = some used[i] := by
    rw [ht, List.getElem?_cons_succ, List.getElem?_append_left hiu]; exact hr
  have hx := hnb (i + 1) _ hti ge (by rw [hge]; simp)
  have htake : t.take (i + 1) = r0 :: used.take i := by
    rw [ht, List.take_succ_cons, List.take_append_of_le_length (le_of_lt hiu)]
  rw [htake, List.cons_append] at hx
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
  have hg0 : ([c0, mu] : List E).getD 0 zeroE = c0 := rfl
  have hg1 : ([c0, mu] : List E).getD 1 zeroE = mu := rfl
  unfold bad at hx
  rw [raw_cons all cvOf bE bd r0 _ hne, hlen, hs, he0] at hx
  simp only [Option.getD_some, hg0, hg1, List.headD_cons] at hx
  rw [← heps, e1, e2, hm] at hx
  simp only [Option.map_some, Option.getD_some] at hx
  rw [hm2]
  refine not_mem_of_list hok (not_mem_take hx ?_)
  rw [List.length_map, Finset.length_toList]
  have hc := cB (rd (tgt c0)) (cvOf c0) (rd mu) (rd eps)
    (List.take i (movesOf Reading.gl all rounds (addE mu (mulE eps (tgt c0))))) m.1
  have hd3 : dAt (all.map (Var.wt Reading.gl))
      (List.take i (movesOf Reading.gl all rounds (addE mu (mulE eps (tgt c0))))).length = 3 := by
    rw [List.length_take, Nat.min_eq_left (le_of_lt hi)]
    unfold dAt
    rw [List.getElem?_map, hvi]
    simp [Part.MaskedSum.Var.wt_d, hvd]
  have hvl : used[i].vals.length = 2 := by
    rw [← scalars_length _ _ hsent.1, hsent.2.1, hvd]
  have hlast : (((r0 :: (List.take i used ++
      [({ used[i] with drawn := ⟨[], [], [], none⟩ } : Fmt.RoundView)])).getLast?.map
        fun r => r.vals.length).getD 0) = 2 := by
    rw [← List.cons_append, List.getLast?_append]
    simp [hvl]
  rw [hlast]
  omega

end Bridge

end VerifiableInference.Desc.Kinds.Head.Law
