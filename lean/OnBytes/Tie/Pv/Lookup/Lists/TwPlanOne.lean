-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Lists/TwPlanOne.lean.
The planner's list of a lookup in closed form, and the rule that ties a round's count of bad
challenges to the planner's quotient.

Main statements.
  finish_step: a routine that adds the list L, run on an empty plan and finished, gives a plan whose
    rounds, seen as (entry, error), are L, each quotient turned into an error by errOf.
  lookI_one, items_fst, items_snd: with one part of 2^(v'+1) keys the lookup's list is the shift's
    round, if there is one, and then a list whose entries are TwPlan.entN and whose quotients are
    TwErr.ratN.
  finish_one: for a lookup with one part (live and shifted are letters): if finish s sc (planLookup
    x) = .ok P, then P's entries are entN, after the shift's entry if x.shifted, and P's errors are
    errOf of ratN, after (2^d, 1) if x.shifted.
  finish_all: the same where all planes count and mu ≤ 6. finish_forest: the same at planForest,
    where mu = 5.
  rule_all: for all sizes and every q, round by round, c · b = a · n: c the count of bad challenges
    (TwErr.epsN), n the size of the round's challenge set (TwErr.nN), (a, kind) the planner's
    quotient (TwErr.ratN), b = q, q - 1 or 1 by kind (TwErr.bOf).
    quadN is the three lists zipped by construction (quad_c, quad_n, quad_r).
What is not claimed: that the planner does not refuse; that epsN and nN are the errors and the sizes
of a typed lookup (for that: OnBytes/Tie/Pv/Lookup/Port/TwFour.lean).

-/
import OnBytes.Tie.Pv.Lookup.Port.TwPlanLaw

set_option autoImplicit false

namespace TwLaw
open OnBytes OnBytes.Params TwPlan TwErr

theorem flat_succ {α : Type} (f : Nat → List α) (n : Nat) :
    (List.range (n + 1)).flatMap f = f 0 ++ (List.range n).flatMap fun l => f (l + 1) := by
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]

theorem timesI_eq (L : List Item) : ∀ n, timesI L n = (List.range n).flatMap fun _ => L
  | 0 => rfl
  | n + 1 => by
    rw [flat_succ]
    show L ++ timesI L n = _
    rw [timesI_eq L n]

theorem levelsI_eq (wk more : Nat) : ∀ fuel l, levelsI wk more fuel l =
    (List.range fuel).flatMap fun i => pscI wk (List.replicate (l + i + more) 2) true 2 2 ++
        [lineI wk]
  | 0, _ => rfl
  | fuel + 1, l => by
    rw [flat_succ]
    show pscI wk (List.replicate (l + more) 2) true 2 2 ++ [lineI wk] ++ levelsI wk more fuel
        (l + 1) = _
    rw [levelsI_eq wk more fuel (l + 1)]
    have e : ∀ i, l + 1 + i + more = l + (i + 1) + more := fun i => by omega
    simp only [e, Nat.add_zero]

def itemsN (wk v' d w n : Nat) : List Item :=
  [(rd wk "LKP" 0 1, (2 ^ (v' + 1) - 1, 1))] ++ pscI wk [] true 3 3 ++ (List.range n).flatMap
      (fun _ => pscI wk [] true 3 2) ++ [(rd wk "JOIN" 0 w, (w, 1))] ++
  (List.range (v' + 1)).flatMap (fun l => pscI wk (List.replicate l 2) true 2 2 ++
      [(rd wk "LINE" 0 1, (1, 1))]) ++
  (List.range d).flatMap (fun l => pscI wk (List.replicate (w + l) 2) true 2 2 ++
      [(rd wk "LINE" 0 1, (1, 1))]) ++
  pscI wk (List.replicate d 2 ++ List.replicate w 1) false 0 0 ++
  [(rd wk "ZERO" 0 (w + d), (w + d, 1))] ++ pscI wk (List.replicate (w + d) 2) true 2 1

theorem pscI_fst (wk : Nat) (degs : List Nat) (withY : Bool) (gY vals : Nat) :
    (pscI wk degs withY gY vals).map Prod.fst = pscN wk degs withY gY vals := by
  cases withY <;> simp [pscI, pscN, Function.comp_def]

theorem items_fst (wk v' d w n : Nat) : (itemsN wk v' d w n).map Prod.fst = entN wk v' d w n := by
  simp only [itemsN, entN, List.map_append, List.map_flatMap, pscI_fst, List.map_cons, List.map_nil]

theorem pscI_snd (wk k g gY vals : Nat) : (pscI wk (List.replicate k g) true gY vals).map Prod.snd =
    pscR k g gY := by
  simp [pscI, pscR]

theorem pscI_snd0 (wk gY vals : Nat) : (pscI wk [] true gY vals).map Prod.snd = pscR 0 0 gY :=
  pscI_snd wk 0 0 gY vals

theorem items_snd (wk v' d w n : Nat) : (itemsN wk v' d w n).map Prod.snd = ratN v' d w n := by
  have hc : (pscI wk (List.replicate d 2 ++ List.replicate w 1) false 0 0).map Prod.snd =
      [(1, 1)] ++ List.replicate d (2, 1) ++ List.replicate w (1, 1) := by simp [pscI]
  simp only [itemsN, ratN, List.map_append, List.map_flatMap, pscI_snd, pscI_snd0, hc,
      List.map_cons, List.map_nil, flat_succ (fun _ => pscR 0 0 3) n,
    List.append_assoc]

theorem lookI_one (wk : Nat) (sh : Bool) (w v' d mu : Nat) :
    lookI wk sh (sumT ([v' + 1].map (2 ^ ·))) w [v' + 1] d mu = (if sh then [shiftI wk d] else [])
        ++ itemsN wk v' d mu (w - 2) := by
  have hk : sumT ([v' + 1].map (2 ^ ·)) = 2 ^ (v' + 1) := by simp [sumT]
  have hc : pscI wk (List.replicate d 2 ++ List.replicate mu 1) false 2 2 = pscI wk
      (List.replicate d 2 ++ List.replicate mu 1) false 0 0 := by simp [pscI]
  have e1 : ∀ i, i + mu = mu + i := fun i => Nat.add_comm i mu
  simp only [lookI, itemsN, hk, hc, timesI_eq, levelsI_eq, eachI, lineI, e1, Nat.add_zero,
      List.length_cons, List.length_nil, Nat.zero_add, Nat.sub_self, List.range_zero,
    List.flatMap_nil, List.nil_append, List.append_nil, List.append_assoc]

section
variable {s : Setting} {sc : Scope}

theorem finish_step {x : Planning Unit} {L : List Item} (h : Step s sc x 0 0 L) {P : Planned}
    (hf : finish s sc x = .ok P) :
    P.rounds.map seen = L.map (said s sc) := by
  unfold finish at hf
  split at hf
  · cases hf
  · rename_i u p hx
    split at hf
    · cases hf
    · cases hf
      obtain ⟨_, _, _, _, _, h6⟩ :=
        h { set := s, scope := sc } p rfl rfl rfl rfl rfl (by cases u; exact hx)
      simpa [view] using h6

theorem map_entry (l : List PlanRound) : l.map (·.entry) = (l.map seen).map Prod.fst := by
  simp [seen, Function.comp_def]
theorem map_error (l : List PlanRound) : l.map (·.error) = (l.map seen).map Prod.snd := by
  simp [seen, Function.comp_def]
theorem said_fst (L : List Item) : (L.map (said s sc)).map Prod.fst = L.map Prod.fst := by
  simp [said, Function.comp_def]
theorem said_snd (L : List Item) : (L.map (said s sc)).map Prod.snd = (L.map Prod.snd).map
    (errOf s sc) := by simp [said, Function.comp_def]

/-- A lookup with one part; live and shifted are free. -/
theorem finish_one (x : LookupSize) (v' : Nat) (hp : x.parts = []) (hv : x.v = v' + 1) {P : Planned}
    (hf : finish s sc (planLookup x) = .ok P) :
    P.rounds.map (·.entry) = (if x.shifted then [shiftN (s.workOf .field sc)] else []) ++
        entN (s.workOf .field sc) v' x.d x.mu ((if x.live != 0 then x.live else 2 ^ min x.mu 6) - 2)
            ∧
    P.rounds.map (·.error) = ((if x.shifted then [(2 ^ x.d, 1)] else []) ++
        ratN v' x.d x.mu ((if x.live != 0 then x.live else 2 ^ min x.mu 6) - 2)).map (errOf s sc) :=
            by
  have h := finish_step (planLookup_step x) hf
  rw [hp, hv] at h
  have h' : P.rounds.map seen = ((if x.shifted then [shiftI (s.workOf .field sc) x.d] else []) ++
      itemsN (s.workOf .field sc) v' x.d x.mu ((if x.live != 0 then x.live else 2 ^ min x.mu 6) -
          2)).map (said s sc) := by
    rw [← lookI_one]
    exact h
  constructor
  · rw [map_entry, h', said_fst, List.map_append, items_fst]
    cases x.shifted <;> rfl
  · rw [map_error, h', said_snd, List.map_append, items_snd]
    cases x.shifted <;> rfl

/-- The same where all planes count (live = 0) and mu ≤ 6. -/
theorem finish_all (x : LookupSize) (v' : Nat) (hp : x.parts = []) (hv : x.v = v' + 1)
    (hl : x.live = 0) (hmu : x.mu ≤ 6) {P : Planned}
    (hf : finish s sc (planLookup x) = .ok P) :
    P.rounds.map (·.entry) = (if x.shifted then [shiftN (s.workOf .field sc)] else []) ++ entN
        (s.workOf .field sc) v' x.d x.mu (2 ^ x.mu - 2) ∧
    P.rounds.map (·.error) = ((if x.shifted then [(2 ^ x.d, 1)] else []) ++ ratN v' x.d x.mu
        (2 ^ x.mu - 2)).map (errOf s sc) := by
  have h := finish_one x v' hp hv hf
  rw [hl, Nat.min_eq_left hmu] at h
  exact h

/-- The same at planForest, where mu = 5. -/
theorem finish_forest (v' d : Nat) (sh : Bool) {P : Planned}
    (hf : finish s sc (planForest ⟨v' + 1, d, sh⟩) = .ok P) :
    P.rounds.map (·.entry) = (if sh then [shiftN (s.workOf .field sc)] else []) ++ entN
        (s.workOf .field sc) v' d 5 30 ∧
    P.rounds.map (·.error) = ((if sh then [(2 ^ d, 1)] else []) ++ ratN v' d 5 30).map (errOf s sc)
        :=
  finish_all { v := v' + 1, d := d, mu := 5, shifted := sh } v' rfl rfl rfl
      (show 5 ≤ 6 by decide) hf

end

/-! ### the rule c · b = a · n, for all sizes -/

/-- (c, n, (a, kind)) -/
abbrev Quad : Type := Nat × Nat × (Nat × Nat)
def OKq (q : Nat) (x : Quad) : Prop := x.1 * bOf q x.2.2.2 = x.2.2.1 * x.2.1

def pscQ (q k g gY : Nat) : List Quad :=
  [(1, q, (1, 1))] ++ List.replicate k (g, q, (g, 1)) ++ [(gY, q - 1, (gY, 2)), (0, 1, (0, 0))]

def quadN (v' d w n q : Nat) : List Quad :=
  [(2 ^ (v' + 1) - 1, q, (2 ^ (v' + 1) - 1, 1))] ++ (List.range (n + 1)).flatMap
      (fun _ => pscQ q 0 0 3) ++ [(w * q ^ (w - 1), q ^ w, (w, 1))] ++
  (List.range (v' + 1)).flatMap (fun l => pscQ q l 2 2 ++ [(1, q, (1, 1))]) ++
  (List.range d).flatMap (fun l => pscQ q (w + l) 2 2 ++ [(1, q, (1, 1))]) ++
  ([(1, q, (1, 1))] ++ List.replicate d (2, q, (2, 1)) ++ List.replicate w (1, q, (1, 1))) ++
  [((w + d) * q ^ (w + d - 1), q ^ (w + d), (w + d, 1))] ++ pscQ q (w + d) 2 2

theorem quad_c (v' d w n q : Nat) : (quadN v' d w n q).map (·.1) = epsN v' d w n q := by
  simp [quadN, epsN, pscQ, pscC, List.map_flatMap]
theorem quad_n (v' d w n q : Nat) : (quadN v' d w n q).map (·.2.1) = nN v' d w n q := by
  simp [quadN, nN, pscQ, pscV, List.map_flatMap, -List.replicate_append_replicate]
theorem quad_r (v' d w n q : Nat) : (quadN v' d w n q).map (·.2.2) = ratN v' d w n := by
  simp [quadN, ratN, pscQ, pscR, List.map_flatMap]

theorem ok_same (q a : Nat) : OKq q (a, q, (a, 1)) := by simp [OKq, bOf]
theorem ok_pt (q k : Nat) : OKq q (k * q ^ (k - 1), q ^ k, (k, 1)) := by
  cases k with
  | zero => simp [OKq]
  | succ k => simp [OKq, bOf, Nat.pow_succ, Nat.mul_assoc]

theorem ok_psc (q k g gY : Nat) : ∀ x ∈ pscQ q k g gY, OKq q x := by
  intro x hx
  simp only [pscQ, List.mem_append, List.mem_cons, List.mem_replicate, List.not_mem_nil, or_false]
      at hx
  rcases hx with (rfl | ⟨_, rfl⟩) | rfl | rfl
  · exact ok_same q 1
  · exact ok_same q g
  · simp [OKq, bOf]
  · simp [OKq, bOf]

/-- c · b = a · n at every round, for all sizes and every q. -/
theorem rule_all (v' d w n q : Nat) : ∀ x ∈ quadN v' d w n q, OKq q x := by
  intro x hx
  simp only [quadN, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_replicate,
      List.not_mem_nil, or_false] at hx
  rcases hx with ((((((rfl | ⟨_, _, h⟩) | rfl) | ⟨_, _, h | rfl⟩) | ⟨_, _, h | rfl⟩) |
      ((rfl | ⟨_, rfl⟩) | ⟨_, rfl⟩)) | rfl) | h
  · exact ok_same q _
  · exact ok_psc _ _ _ _ x h
  · exact ok_pt q w
  · exact ok_psc _ _ _ _ x h
  · exact ok_same q 1
  · exact ok_psc _ _ _ _ x h
  · exact ok_same q 1
  · exact ok_same q 1
  · exact ok_same q 2
  · exact ok_same q 1
  · exact ok_pt q (w + d)
  · exact ok_psc _ _ _ _ x h

end TwLaw
