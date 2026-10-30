-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/ReadsAgree.lean: CONDITIONAL.

Not shown here. That layTables and readsAt return. For tok_named: that the second token sumcheck's
end point has lt coordinates, and that the lookup's point is whole and not empty. No example is
known. No property is claimed.

THE HONEST READS AT A LIST OF POINTS AGREE, WORD FOR WORD, WITH THE HONEST READS AT A LONGER LIST,
wherever the first are there. An entry of the honest reads (readsAt,
Johnson/Desc/K4/Honest/Cells.lean) reads the list of points through its family's weights alone
(wtsOf), and these through what the list holds under the family's point. So where the second list
holds whatever the first holds (PtsPart), an entry that is there at the first list is there at the
second and is the same machine word; and a form that has a value on the first reads has the same
value on the second.

  phiOf_find     the verifier's weights read the list through what it holds under the family's
                 point.
  wts_part       a family's weights and its test, at the two lists.
  reads_agree    an entry.
  foldl_mem      two loops whose steps agree at the list's members.
  valAffQ_agree  a form's value.
  lastSeg, fullSeg, namedPts_eq, lastSeg_name, fullSeg_name, find_skip   namedPts, stretch by
                 stretch.
  tok_named      the two points at the second token sumcheck's end point stand in the list of all
                 points that the honest side has heard (namedPts).
-/
import Johnson.Road.K4.C.TermsOpen
import Johnson.Road.K4.C.NamedPart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Env TableAsk TableAt layTables tableAsks phiOf)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In Pts Reads matsOf readsAt wtsOf wtsFit famEntry valAff
  valAff? affFits namedPts ztOf)

/-- The verifier's weights read the list of points through what it holds under the family's point.
-/
theorem phiOf_find {y : Lay} {fo : Forest.Heard} {pt pt' : List (String × Array E)} {a : TableAsk}
    (h : (pt'.find? fun p => p.1 == a.point) = (pt.find? fun p => p.1 == a.point)) :
    phiOf y fo pt' a = phiOf y fo pt a := by
  unfold phiOf
  rw [h]

/-- **A family's weights and its test, at a list and at a longer one.** -/
theorem wts_part {y : Lay} {fo : Forest.Heard} {pt pt' : List (String × Array E)} {a : TableAsk}
    (hp : PtsPart pt pt') (hfit : wtsFit y fo pt a = true) :
    wtsOf y fo pt' a = wtsOf y fo pt a ∧ wtsFit y fo pt' a = true := by
  cases he : a.point.isEmpty with
  | true =>
    have hf := hfit
    unfold wtsFit at hf
    rw [if_pos he] at hf
    cases hq : phiOf y fo pt a with
    | none =>
      rw [hq] at hf
      cases hf
    | some φ =>
      have hq' := phiOf_part hp hq
      constructor
      · unfold wtsOf
        simp only [he, ↓reduceIte, hq, hq']
      · unfold wtsFit
        rw [if_pos he, hq', ← hq]
        exact hf
  | false =>
    have hf := hfit
    unfold wtsFit at hf
    rw [he, if_neg Bool.false_ne_true] at hf
    cases hfd : (pt.find? fun p => p.1 == a.point) with
    | none =>
      rw [hfd] at hf
      cases hf
    | some p =>
      have hfd' := hp _ _ hfd
      have hph : phiOf y fo pt' a = phiOf y fo pt a := phiOf_find (hfd'.trans hfd.symm)
      constructor
      · unfold wtsOf
        simp only [he, Bool.false_eq_true, ↓reduceIte, hfd, hfd', hph]
      · unfold wtsFit
        rw [he, if_neg Bool.false_ne_true, hfd', ← hfd]
        exact hf

variable {Q : K4Pub} {w : K4In} {fo : Forest.Heard} {pt pt' : List (String × Array E)}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {R R' : Reads}

/-- **An entry that is there at the first list is there at the second, and is the same word.** -/
theorem reads_agree (hR : readsAt Q w fo pt = some R) (hR' : readsAt Q w fo pt' = some R')
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r) (hp : PtsPart pt pt')
    {pos : ℕ} (hh : R.has pos = true) : R'.has pos = true ∧ R'.u3 pos = R.u3 pos := by
  obtain ⟨q, hq, m, hmq, c, sg, hc, hsg, rfl⟩ := place_of_has hR hl hh
  have hj := place_lt (matsOf Q) q.1.L m.1 hc hsg
  obtain ⟨u1, u2, -⟩ := fam_at hR hl hq hmq hj
  obtain ⟨v1, v2, -⟩ := fam_at hR' hl hq hmq hj
  have hfit : wtsFit Q.P.y fo pt q.1 = true := by
    rw [← u2]
    exact hh
  obtain ⟨e1, e2⟩ := wts_part hp hfit
  refine ⟨by rw [v2]; exact e2, ?_⟩
  rw [u1, v1]
  unfold famEntry mkFam
  simp only [e1]

/-- Two loops whose steps agree at the list's members. -/
theorem foldl_mem {α σ : Type} {f g : σ → α → σ} : ∀ (l : List α) (s : σ),
    (∀ x ∈ l, ∀ s, f s x = g s x) → l.foldl f s = l.foldl g s
  | [], _, _ => rfl
  | x :: l, s, h => by
    rw [List.foldl_cons, List.foldl_cons, h x List.mem_cons_self]
    exact foldl_mem l _ fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- **A form that has a value on the first reads has the same value on the second.** -/
theorem valAffQ_agree (hR : readsAt Q w fo pt = some R) (hR' : readsAt Q w fo pt' = some R')
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r) (hp : PtsPart pt pt')
    {v : Env} {slot : ℕ → E} {a : Aff} {x : E} (h : valAff? v R slot a = some x) :
    valAff? v R' slot a = some x := by
  obtain ⟨hfit, rfl⟩ := (valAffQ_some v R slot a x).mp h
  have hx : ∀ e ∈ a.ents.toList, (e.tree == v.iU3) = true ∧
      R.has (e.row * v.K3 + e.idx) = true := by
    have h0 := hfit
    unfold affFits at h0
    rw [← Array.all_toList, List.all_eq_true] at h0
    intro e he
    have h1 := h0 e he
    rw [Bool.and_eq_true] at h1
    exact h1
  refine (valAffQ_some v R' slot a _).mpr ⟨?_, ?_⟩
  · unfold affFits
    rw [← Array.all_toList, List.all_eq_true]
    intro e he
    rw [Bool.and_eq_true]
    exact ⟨(hx e he).1, (reads_agree hR hR' hl hp (hx e he).2).1⟩
  · show a.ents.foldl (fun s e =>
        if e.tree == v.iU3 then maddE s e.coef (R.u3 (e.row * v.K3 + e.idx)) else s)
      (a.slots.foldl (fun s e => maddE s e.2 (slot e.1)) a.const) =
      a.ents.foldl (fun s e =>
        if e.tree == v.iU3 then maddE s e.coef (R'.u3 (e.row * v.K3 + e.idx)) else s)
      (a.slots.foldl (fun s e => maddE s e.2 (slot e.1)) a.const)
    simp only [← Array.foldl_toList]
    refine foldl_mem _ _ fun e he s => ?_
    rw [(reads_agree hR hR' hl hp (hx e he).2).2]

/-! ## The two token points stand in the list of all points -/

/-- A stretch of namedPts: the last la coordinates of z under the name n, if z is not empty. -/
def lastSeg (la : ℕ) (n : String) (z : Array E) : List (String × Array E) :=
  match (lastOf z la).toOption with
  | some x => if z.isEmpty then [] else [(n, x)]
  | none => []

/-- A stretch of namedPts: z under the name n, if it has k coordinates and k is not 0. -/
def fullSeg (n : String) (k : ℕ) (z : Array E) : List (String × Array E) :=
  if z.size == k && k != 0 then [(n, z)] else []

/-- namedPts, stretch by stretch. -/
theorem namedPts_eq (Q : K4Pub) (p : Pts) : namedPts Q p =
    lastSeg Q.P.y.h.la "Z" p.fo.zx ++ fullSeg "zt" Q.P.y.h.lt (ztOf Q p) ++
      lastSeg Q.P.y.h.la "Z_V" p.r6 ++ fullSeg "P_V" Q.P.y.h.lt p.PV ++
      fullSeg "Z_E" Q.P.y.h.la p.ZE ++ fullSeg "r_tV" Q.P.y.h.lt p.rtV ++
      lastSeg Q.P.y.h.la "Z_a" p.r12 ++
      (match lastSeg Q.P.y.h.la "Z" p.fo.zx, p.rt.size == Q.P.y.h.lt with
        | [(_, z)], true => [("Y", longPoint (z.extract 0 Q.P.y.ls) p.rt), ("rt", p.rt)]
        | _, _ => []) ++
      lastSeg Q.P.y.h.la "Z_b" p.r14 := rfl

/-- A member of such a stretch bears the stretch's name. -/
theorem lastSeg_name {la : ℕ} {n : String} {z : Array E} {x : String × Array E}
    (h : x ∈ lastSeg la n z) : x.1 = n := by
  obtain ⟨-, y, -, rfl⟩ := mem_last h
  rfl

/-- Likewise. -/
theorem fullSeg_name {n : String} {k : ℕ} {z : Array E} {x : String × Array E}
    (h : x ∈ fullSeg n k z) : x.1 = n := by
  obtain ⟨-, -, rfl⟩ := mem_full h
  rfl

/-- A search passes a list none of whose members bears the name. -/
theorem find_skip {n : String} : ∀ (l l' : List (String × Array E)), (∀ x ∈ l, x.1 ≠ n) →
    ((l ++ l').find? fun x => x.1 == n) = l'.find? fun x => x.1 == n
  | [], _, _ => rfl
  | y :: l, l', h => by
    rw [List.cons_append, List.find?_cons_of_neg (by
      rw [beq_iff_eq]
      exact h y List.mem_cons_self)]
    exact find_skip l l' fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- **The two points at the second token sumcheck's end point stand in the list of all points that
the honest side has heard.** Z: the last la coordinates of the lookup's point. -/
theorem tok_named {Q : K4Pub} {p : Pts} {Z : Array E}
    (hZ : (lastOf p.fo.zx Q.P.y.h.la).toOption = some Z) (he : p.fo.zx.isEmpty = false)
    (hs : p.rt.size = Q.P.y.h.lt) :
    PtsPart (tokPts (Z.extract 0 Q.P.y.ls) p.rt) (namedPts Q p) := by
  have eZ : lastSeg Q.P.y.h.la "Z" p.fo.zx = [("Z", Z)] := by
    unfold lastSeg
    rw [hZ, he]
    rfl
  have es : (p.rt.size == Q.P.y.h.lt) = true := by
    rw [hs]
    exact beq_self_eq_true _
  have pre : ∀ n : String, n = "rt" ∨ n = "Y" →
      ∀ x ∈ [("Z", Z)] ++ fullSeg "zt" Q.P.y.h.lt (ztOf Q p) ++ lastSeg Q.P.y.h.la "Z_V" p.r6 ++
        fullSeg "P_V" Q.P.y.h.lt p.PV ++ fullSeg "Z_E" Q.P.y.h.la p.ZE ++
        fullSeg "r_tV" Q.P.y.h.lt p.rtV ++ lastSeg Q.P.y.h.la "Z_a" p.r12, x.1 ≠ n := by
    intro n hn x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with (((((hx | hx) | hx) | hx) | hx) | hx) | hx
    · have e : x.1 = "Z" := by rw [hx]
      rw [e]
      rcases hn with rfl | rfl <;> decide
    · rw [fullSeg_name hx]
      rcases hn with rfl | rfl <;> decide
    · rw [lastSeg_name hx]
      rcases hn with rfl | rfl <;> decide
    · rw [fullSeg_name hx]
      rcases hn with rfl | rfl <;> decide
    · rw [fullSeg_name hx]
      rcases hn with rfl | rfl <;> decide
    · rw [fullSeg_name hx]
      rcases hn with rfl | rfl <;> decide
    · rw [lastSeg_name hx]
      rcases hn with rfl | rfl <;> decide
  intro n q hq
  rw [namedPts_eq, eZ, es, List.append_assoc]
  by_cases c1 : n = "rt"
  · subst c1
    obtain rfl : ("rt", p.rt) = q := Option.some.inj ((find_rt _ _).symm.trans hq)
    rw [find_skip _ _ (pre "rt" (Or.inl rfl))]
    rfl
  · by_cases c2 : n = "Y"
    · subst c2
      obtain rfl : ("Y", longPoint (Z.extract 0 Q.P.y.ls) p.rt) = q :=
        Option.some.inj ((find_Y _ _).symm.trans hq)
      rw [find_skip _ _ (pre "Y" (Or.inr rfl))]
      rfl
    · rw [find_none _ _ c1 c2] at hq
      cases hq

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.phiOf_find
#print axioms OnBytes.Road.K4.C.wts_part
#print axioms OnBytes.Road.K4.C.reads_agree
#print axioms OnBytes.Road.K4.C.foldl_mem
#print axioms OnBytes.Road.K4.C.valAffQ_agree
#print axioms OnBytes.Road.K4.C.namedPts_eq
#print axioms OnBytes.Road.K4.C.lastSeg_name
#print axioms OnBytes.Road.K4.C.fullSeg_name
#print axioms OnBytes.Road.K4.C.find_skip
#print axioms OnBytes.Road.K4.C.tok_named
