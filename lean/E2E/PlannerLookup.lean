--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/PlannerLookup.lean: the planner's routine for the rounds of a lookup (`Params.planLookup`,
OnBytes/Params/Planner.lean) makes, at EVERY setting and scope and at every face that passes its
tests, just the entries by which the lookup's hearing on a view's rounds goes (`K3.entriesV`,
Johnson/Desc/First/Look/Via/Rounds.lean), but for the work bits. Statements and proofs; nothing is
evaluated.

Why. The library's bridge from that hearing (`hearV`) to the hearing off a tape, by which the key
file's IOP as written in Lean hears its lookups (`hearV_hearG`,
Johnson/Top/H/K3Via/BridgeEntries.lean), asks a test on the plan's entries: `entriesFit`. At the
full size a lookup has over nine thousand rounds: to evaluate the planner there in Lean's kernel is
dear. The test holds for a reason that reads no number: the routine only PUSHES rounds, and a
setting enters an entry through its work bits alone, which the test strikes.

What is defined.
  `ents p`: the entries of a plan in the writing, the work bits struck.
  `From b x l`: from a state with b open bytes, no open root and no open answer: wherever the
    routine x does not refuse, it adds just the entries l and leaves nothing open.
What is shown.
  `from_pure`, `from_seq`, `from_setting`, `from_needs`, `from_scal`, `from_close`,
    `from_close_end`, `from_closeNone_end`: how `From` goes along the routine's steps.
  `from_psc`, `from_times`, `from_levels`, `from_tree`, `from_each`, `from_join`, `from_zero`,
    `from_shift`: the pieces: a masked sumcheck; a routine n times; a product tree; a tree for each
    part; the rounds in which nothing is sent.
  **`from_lookup`**: at a face with mu ≤ 6, two planes at least and a part at least:
    `From 0 (planLookup f.size) (esMsg f)`; `esMsg f` is the library's list, which its `esMsg_eq`
    shows equal to `entriesV f`.
  **`fit_of_planner`**: `f.ok = true → entriesG set scope f = some es → entriesFit f es = true`.

Limits.
- It says nothing where the planner refuses, and not that it does not refuse.
- Nothing on the work bits, on the rounds' errors or on the plan's verdict.
- It is a statement on two lists of public numbers. Nothing on soundness, completeness or what a
  view shows.


-/
import Johnson.Top.H.K3Via.BridgeEntries

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.PlanLookup
open OnBytes OnBytes.Params
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.Part.MaskedSum (entry)

/-- The entries that a plan in the writing holds, the work bits struck. -/
def ents (p : PlanState) : List Fmt.Entry :=
  p.rounds.toList.map fun r => { r.entry with work := 0 }

/-- From a state with b open bytes, no open root and no open answer: wherever the routine does not
refuse it adds just these entries (work bits struck) and leaves nothing open. -/
def From (b : ℕ) (x : Planning Unit) (l : List Fmt.Entry) : Prop :=
  ∀ p p', p.openBytes = b → p.openRoots = 0 → p.openAnswers = 0 → x p = .ok ((), p') →
    ents p' = ents p ++ l ∧ p'.openBytes = 0 ∧ p'.openRoots = 0 ∧ p'.openAnswers = 0

theorem bind_ok {α : Type} {x : Planning α} {f : α → Planning Unit} {p p' : PlanState}
    (h : (x >>= f) p = .ok ((), p')) : ∃ a q, x p = .ok (a, q) ∧ f a q = .ok ((), p') := by
  have h' : (x p).bind (fun r => f r.1 r.2) = .ok ((), p') := h
  cases hx : x p with
  | error e => rw [hx] at h'; cases h'
  | ok r => rw [hx] at h'; exact ⟨r.1, r.2, rfl, h'⟩

theorem from_pure : From 0 (pure ()) [] := by
  intro p p' hb hr ha h
  have h' : (Except.ok ((), p) : Except String (Unit × PlanState)) = .ok ((), p') := h
  cases h'
  exact ⟨(List.append_nil _).symm, hb, hr, ha⟩

theorem from_seq {x y : Planning Unit} {l₁ l₂ : List Fmt.Entry} (hx : From 0 x l₁)
    (hy : From 0 y l₂) : From 0 (x >>= fun _ => y) (l₁ ++ l₂) := by
  intro p p' hb hr ha h
  obtain ⟨⟨⟩, q, h1, h2⟩ := bind_ok h
  obtain ⟨e1, b1, r1, a1⟩ := hx p q hb hr ha h1
  obtain ⟨e2, c2⟩ := hy q p' b1 r1 a1 h2
  exact ⟨by rw [e2, e1, List.append_assoc], c2⟩

theorem from_setting {b : ℕ} {f : Setting → Planning Unit} {l : List Fmt.Entry}
    (h : ∀ s, From b (f s) l) : From b (theSetting >>= f) l := by
  intro p p' hb hr ha hh
  obtain ⟨s, q, h1, h2⟩ := bind_ok hh
  have h1' : (Except.ok (p.set, p) : Except String (Setting × PlanState)) = .ok (s, q) := h1
  cases h1'
  exact h _ p p' hb hr ha h2

theorem from_needs {b : ℕ} {c : Bool} {why : String} {y : Planning Unit} {l : List Fmt.Entry}
    (h : c = true → From b y l) : From b (needs c why >>= fun _ => y) l := by
  intro p p' hb hr ha hh
  obtain ⟨⟨⟩, q, h1, h2⟩ := bind_ok hh
  cases c with
  | false =>
    have h1' : (Except.error why : Except String (Unit × PlanState)) = .ok ((), q) := h1
    cases h1'
  | true =>
    have h1' : (Except.ok ((), p) : Except String (Unit × PlanState)) = .ok ((), q) := h1
    cases h1'
    exact h rfl p p' hb hr ha h2

theorem from_scal {n : ℕ} {y : Planning Unit} {l : List Fmt.Entry} (h : From (24 * n) y l) :
    From 0 (planScalars n >>= fun _ => y) l := by
  intro p p' hb hr ha hh
  obtain ⟨⟨⟩, q, h1, h2⟩ := bind_ok hh
  have h1' : (Except.ok ((), { p with openBytes := p.openBytes + 24 * n }) :
      Except String (Unit × PlanState)) = .ok ((), q) := h1
  cases h1'
  exact h { p with openBytes := p.openBytes + 24 * n } p'
    (by show p.openBytes + 24 * n = 24 * n; rw [hb, Nat.zero_add]) hr ha h2

/-- The entry that a round with a verifier's message gets, the work bits struck. -/
def mk (name : String) (b : ℕ) (d : Draws) : Fmt.Entry :=
  { name := name, msg := b, drawE := d.drawE, drawNZ := d.drawNZ, poss := d.poss, logN := d.logN,
    trits := d.trits, rows := d.rows }

theorem ite_ok {q : PlanState} (c : Prop) [Decidable c] (A : PlanState)
    (h : (if c then (Except.error notAdmitted : Except String (Unit × PlanState))
      else .ok ((), A)) = .ok ((), q)) : A = q := by
  split at h
  · cases h
  · cases h
    rfl

theorem close_ok {name : String} {why : ErrorKind} {err : Bound} {d : Draws} {b : ℕ}
    {p q : PlanState} (hb : p.openBytes = b) (hr : p.openRoots = 0) (ha : p.openAnswers = 0)
    (h : close name why err d p = .ok ((), q)) :
    ents q = ents p ++ [mk name b d] ∧ q.openBytes = 0 ∧ q.openRoots = 0 ∧ q.openAnswers = 0 := by
  obtain rfl := ite_ok _ _ h
  refine ⟨?_, rfl, rfl, rfl⟩
  simp only [ents, mk, hb, hr, ha, Array.toList_push, List.map_nil, List.map_cons,
    List.map_append]

theorem closeNone_ok {name : String} {b : ℕ} {p q : PlanState} (hb : p.openBytes = b)
    (hr : p.openRoots = 0) (ha : p.openAnswers = 0) (h : closeNone name p = .ok ((), q)) :
    ents q = ents p ++ [mk name b {}] ∧ q.openBytes = 0 ∧ q.openRoots = 0 ∧
      q.openAnswers = 0 := by
  obtain rfl := ite_ok _ _ h
  refine ⟨?_, rfl, hr, rfl⟩
  simp only [ents, mk, hb, ha, Array.toList_push, List.map_nil, List.map_cons, List.map_append]

theorem from_close {name : String} {why : ErrorKind} {err : Bound} {d : Draws} {b : ℕ}
    {y : Planning Unit} {l : List Fmt.Entry} (h : From 0 y l) :
    From b (close name why err d >>= fun _ => y) (mk name b d :: l) := by
  intro p p' hb hr ha hh
  obtain ⟨⟨⟩, q, h1, h2⟩ := bind_ok hh
  obtain ⟨e1, b1, r1, a1⟩ := close_ok hb hr ha h1
  obtain ⟨e2, c2⟩ := h q p' b1 r1 a1 h2
  exact ⟨by rw [e2, e1, List.append_assoc]; rfl, c2⟩

theorem from_close_end {name : String} {why : ErrorKind} {err : Bound} {d : Draws} {b : ℕ} :
    From b (close name why err d) [mk name b d] :=
  fun _ _ hb hr ha h => close_ok hb hr ha h

theorem from_closeNone_end {name : String} {b : ℕ} : From b (closeNone name) [mk name b {}] :=
  fun _ _ hb hr ha h => closeNone_ok hb hr ha h

/-! ## A sumcheck -/

theorem from_rounds (s : Setting) : ∀ gs : List ℕ,
    From 0 (planPscRounds s gs) (gs.map fun g => entry "PSC round" (g - 1) 1 0)
  | [] => from_pure
  | g :: gs => by
    unfold planPscRounds
    exact from_scal (from_close (from_rounds s gs))

/-- The entries of a sumcheck, by the planner's numbers. -/
def pscE (x : PscSize) : List Fmt.Entry :=
  entry "PSC epsilon" 1 1 0 :: ((x.degree.map fun g => entry "PSC round" (g - 1) 1 0) ++
    if x.withY then [entry "PSC Y" x.degreeY 1 1, entry "PSC values" x.values 0 0] else [])

theorem from_psc (x : PscSize) : From 0 (planPsc x) (pscE x) := by
  unfold planPsc pscE
  refine from_setting fun s => from_scal (from_close (from_seq (from_rounds s x.degree) ?_))
  cases x.withY with
  | true => exact from_scal (from_close (from_scal from_closeNone_end))
  | false => exact from_pure

/-! ## The pieces in the forms of the library's list -/

theorem psc_sum (m dY n : ℕ) :
    pscE { degree := List.replicate m 3, degreeY := dY, values := n } = sumE m dY n := by
  unfold pscE sumE
  rw [List.map_replicate]
  rfl

theorem leafDs_rep (f : Face) : leafDs f = List.replicate f.d 2 ++ List.replicate f.mu 1 := by
  unfold leafDs
  apply List.ext_getElem
  · simp [Nat.add_comm]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_append, List.getElem_replicate,
      List.length_replicate]
    split <;> rfl

theorem psc_open (f : Face) :
    pscE { degree := List.replicate f.d 3 ++ List.replicate f.mu 2, withY := false } =
      openE (leafDs f) := by
  unfold pscE openE
  rw [leafDs_rep, List.map_append, List.map_append, List.map_replicate, List.map_replicate,
    List.map_replicate, List.map_replicate]
  exact congrArg _ (List.append_nil _)

theorem from_draw {name : String} {why : ErrorKind} {err : Setting → Bound} {n : ℕ} {pr : Priced} :
    From 0 (theSetting >>= fun s => close name why (err s) { drawE := n, priced := pr })
      [drawEntry name n] :=
  from_setting fun _ => from_close_end

theorem from_join (n : ℕ) : From 0 (planJoin n) [drawEntry "JOIN" n] := by
  unfold planJoin
  exact from_draw

theorem from_zero (n : ℕ) : From 0 (planZero n) [drawEntry "ZERO" n] := by
  unfold planZero
  exact from_draw

theorem from_shift (n : ℕ) : From 0 (planShift n) [drawEntry "LKP shift" 1] := by
  unfold planShift
  exact from_draw

/-- n times a list. -/
def rep (l : List Fmt.Entry) : ℕ → List Fmt.Entry
  | 0 => []
  | k + 1 => l ++ rep l k

theorem from_times {x : Planning Unit} {l : List Fmt.Entry} (h : From 0 x l) :
    ∀ n, From 0 (times n x) (rep l n)
  | 0 => from_pure
  | k + 1 => by
    unfold times
    exact from_seq h (from_times h k)

theorem rep_flat (l : List Fmt.Entry) : ∀ n, rep l n = (List.range n).flatMap fun _ => l
  | 0 => rfl
  | k + 1 => by
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, rep, rep_flat l k]

/-- The levels of a product tree. -/
def lvls (more : ℕ) : ℕ → ℕ → List Fmt.Entry
  | 0, _ => []
  | fuel + 1, l => (sumE (l + more) 2 2 ++ [drawEntry "LINE" 1]) ++ lvls more fuel (l + 1)

theorem from_levels (more : ℕ) : ∀ fuel l, From 0 (planTreeLevels more fuel l) (lvls more fuel l)
  | 0, _ => from_pure
  | fuel + 1, l => by
    unfold planTreeLevels lvls
    rw [List.append_assoc, ← psc_sum]
    exact from_seq (from_psc _) (from_seq from_draw (from_levels more fuel (l + 1)))

theorem lvls_run (more : ℕ) : ∀ fuel l,
    lvls more fuel l = (List.range fuel).flatMap fun i => levelE (more + (l + i)) ++ []
  | 0, _ => rfl
  | fuel + 1, l => by
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, lvls,
      lvls_run more fuel (l + 1)]
    have e : (fun i => levelE (more + (l + 1 + i)) ++ []) =
        ((fun i => levelE (more + (l + i)) ++ []) ∘ Nat.succ) := by
      funext i
      show levelE (more + (l + 1 + i)) ++ [] = levelE (more + (l + (i + 1))) ++ []
      rw [Nat.add_right_comm l 1 i, Nat.add_assoc l i 1]
    rw [e, Nat.add_zero, Nat.add_comm l more]
    unfold levelE
    simp only [List.append_nil]
    rfl

theorem from_tree (levels more : ℕ) : From 0 (planProductTree levels more) (runE more levels) := by
  unfold planProductTree runE
  have h := from_levels more levels 0
  rw [lvls_run] at h
  simpa only [Nat.zero_add] using h

theorem from_each : ∀ (l : List ℕ) (k : ℕ),
    From 0 (forEach l fun v => planProductTree v 0) (keysE (l.zipIdx k))
  | [], _ => from_pure
  | v :: t, k => by
    unfold forEach
    rw [List.zipIdx_cons]
    unfold keysE
    rw [List.append_nil]
    exact from_seq (from_tree v 0) (from_each t (k + 1))

/-! ## The lookup -/

theorem rep_tie (n : ℕ) :
    rep (sumE 0 3 2) n = (List.range n).flatMap (fun _ => sumE 0 3 2 ++ []) := by
  rw [rep_flat]
  simp only [List.append_nil]

theorem rep_parts : ∀ n, rep (sumE 0 2 2) n = partsE n
  | 0 => rfl
  | k + 1 => by
    unfold rep partsE
    rw [rep_parts k, List.append_nil]

/-- What the face's tests give of the planner's record. -/
theorem size_planes {f : Face} (hm : f.mu ≤ 6) (h2 : 2 ≤ f.planes) :
    (if f.size.live != 0 then f.size.live else 2 ^ min f.size.mu 6) = f.planes := by
  show (if (if f.planes == 2 ^ f.mu then 0 else f.planes) != 0
    then (if f.planes == 2 ^ f.mu then 0 else f.planes) else 2 ^ min f.mu 6) = f.planes
  by_cases h : f.planes = 2 ^ f.mu
  · simp [h, Nat.min_eq_left hm]
  · have h0 : f.planes ≠ 0 := by omega
    simp [h, h0]

theorem size_parts {f : Face} (hp : f.parts ≠ []) :
    (if f.size.parts.isEmpty then [f.size.v] else f.size.parts) = f.parts := by
  show (if (if f.parts.length == 1 then [] else f.parts).isEmpty then [f.parts.headD 0]
    else (if f.parts.length == 1 then [] else f.parts)) = f.parts
  match hf : f.parts with
  | [] => exact absurd hf hp
  | [v] => rfl
  | v :: w :: t => rfl

/-- **The planner's routine for a lookup adds the hearing's own list of entries**, at every setting
and scope: at a face with mu ≤ 6, two planes at least and a part at least. -/
theorem from_lookup {f : Face} (hm : f.mu ≤ 6) (h2 : 2 ≤ f.planes) (hp : f.parts ≠ []) :
    From 0 (planLookup f.size) (esMsg f) := by
  unfold planLookup
  refine from_setting fun s => ?_
  dsimp only
  rw [size_planes hm h2, size_parts hp]
  refine from_needs fun _ => from_needs fun _ => ?_
  have tail : From 0 (do
      close "LKP" .field (Bound.ratio (sumT (f.parts.map (2 ^ ·)) - 1) s.cardE)
        { drawE := 1, priced := .callersWord }
      planPsc { degreeY := 3, values := 3 }
      times (f.planes - 2) (planPsc { degreeY := 3, values := 2 })
      times (f.parts.length - 1) (planPsc {})
      planJoin f.size.mu
      forEach f.parts fun v => planProductTree v 0
      planProductTree f.size.d f.size.mu
      planPsc { degree := List.replicate f.size.d 3 ++ List.replicate f.size.mu 2, withY := false }
      planZero (f.size.mu + f.size.d)
      planPsc { degree := List.replicate (f.size.mu + f.size.d) 3, degreeY := 2, values := 1 })
      (drawEntry "LKP" 1 :: (sumE 0 3 3 ++ (rep (sumE 0 3 2) (f.planes - 2) ++
        (rep (sumE 0 2 2) (f.parts.length - 1) ++
        ([drawEntry "JOIN" f.mu] ++ (keysE f.parts.zipIdx ++ (runE f.mu f.d ++
        (openE (leafDs f) ++
        ([drawEntry "ZERO" (f.mu + f.d)] ++ sumE (f.mu + f.d) 2 1))))))))) := by
    rw [← psc_open f, ← psc_sum (f.mu + f.d) 2 1, ← psc_sum 0 3 3, ← psc_sum 0 3 2,
      ← psc_sum 0 2 2]
    exact from_close (from_seq (from_psc _) (from_seq (from_times (from_psc _) _)
      (from_seq (from_times (from_psc _) _) (from_seq (from_join f.mu)
      (from_seq (from_each f.parts 0) (from_seq (from_tree f.d f.mu) (from_seq (from_psc _)
      (from_seq (from_zero (f.mu + f.d)) (from_psc _)))))))))
  have e : ((if f.shifted then [drawEntry "LKP shift" 1] else []) ++
      (drawEntry "LKP" 1 :: (sumE 0 3 3 ++ (rep (sumE 0 3 2) (f.planes - 2) ++
        (rep (sumE 0 2 2) (f.parts.length - 1) ++
        ([drawEntry "JOIN" f.mu] ++ (keysE f.parts.zipIdx ++ (runE f.mu f.d ++
        (openE (leafDs f) ++ ([drawEntry "ZERO" (f.mu + f.d)] ++ sumE (f.mu + f.d) 2 1)))))))))) =
      esMsg f := by
    unfold esMsg tieE
    rw [rep_tie, rep_parts]
    simp only [List.nil_append, List.append_nil, List.append_assoc]
    rfl
  rw [← e]
  by_cases hs : f.shifted = true
  · rw [if_pos (show f.size.shifted = true from hs), if_pos hs]
    exact from_seq (from_shift _) tail
  · rw [if_neg (show ¬ f.size.shifted = true from hs), if_neg hs]
    exact from_seq from_pure tail

theorem finish_ok {s : Setting} {sc : Scope} {x : Planning Unit} {P : Planned}
    (h : finish s sc x = .ok P) :
    ∃ p, x { set := s, scope := sc } = .ok ((), p) ∧ P.rounds = p.rounds.toList := by
  unfold finish at h
  cases hx : x { set := s, scope := sc } with
  | error e => rw [hx] at h; cases h
  | ok r =>
    obtain ⟨⟨⟩, p⟩ := r
    rw [hx] at h
    dsimp only at h
    split at h
    · cases h
    · cases h
      exact ⟨p, rfl, rfl⟩

/-- **At every setting and scope: the entries that the planner makes for a face that passes its
tests are, but for the work bits, the list that the hearing on a view's rounds goes by.** -/
theorem fit_of_planner {set : Setting} {scope : Scope} {f : Face} {es : List Fmt.Entry}
    (hok : f.ok = true) (h : entriesG set scope f = some es) : entriesFit f es = true := by
  unfold Face.ok at hok
  simp only [decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, hm⟩, h2⟩, -⟩, hp⟩, -⟩, -⟩, -⟩, -⟩ := hok
  have hp' : f.parts ≠ [] := by
    intro e
    rw [e] at hp
    cases hp
  unfold entriesG at h
  cases hf : finish set scope (planLookup f.size) with
  | error e => rw [hf] at h; cases h
  | ok P =>
    rw [hf] at h
    have h' : some (P.rounds.map (·.entry)) = some es := h
    cases h'
    obtain ⟨p, hx, hP⟩ := finish_ok hf
    obtain ⟨e1, -⟩ := from_lookup hm h2 hp' _ p rfl rfl rfl hx
    have e2 : ents p = esMsg f := e1
    unfold entriesFit
    rw [← esMsg_eq, ← e2, beq_iff_eq, hP, List.map_map]
    rfl

end AtPublicFiles.PlanLookup

#print axioms AtPublicFiles.PlanLookup.from_lookup
#print axioms AtPublicFiles.PlanLookup.fit_of_planner
