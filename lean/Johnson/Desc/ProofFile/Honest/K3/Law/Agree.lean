-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Agree.lean: the honest side of the kind "lookup" (K3). Summands
that agree at a run, as read, are lawful together. Theorems, with three definitions.

Terms. Honest/K3/GLOSSARY.md ("agree at the run", "course", "fit", "lawful"). In this file:
`swap R B` is the course R with the structure of summands B in the place of its own; `SameRd a b`
says that two lists of the program's elements are read alike.

What is shown.
  `AgreeLawful`, `agreeLawful`: the statement and its proof: where another structure of summands
    agrees with the course's at the run (`AgreeAt`, Honest/K3/Law/Statements.lean), and the course
    passes `Fit`, it is `Lawful` at that run if and only if the course's is.
  `lawful_swap`: one direction of it. The other theorems are steps to it: sums, true end values and
    what the forms should be worth are read alike at the two structures.

Hypotheses that remain.
  `Fit R`: the course stands at its place and its challenges can be sampled.
  `AgreeAt R B`: the two structures of summands agree at the run.
  They are `hF` (in `fit_swap`: `h`) and `hA` (in `agreeAt_symm`: `h`). The steps take besides:
    `hs`, `hc`: the stage is one of the row's (in `claimed_swap`: or the stage behind a key tree's
    last level), with the call k; `hn`, `hj`, `ht`: a round's, or an end value's, number is in
    range; the stage has two end values; `h2`, `hok`: the face has two planes at least; it passes
    the verifier's tests; `h`: `Sums`, or `Lawful`, at the course's own summands (in `sums_swap`,
    `lawful_swap`); `h0`, `h1`, `h`: (in `rd_add`, `sumOf_congr`) the elements, or the lists, are
    read alike. Without a name: `SameRd a b` in `sameRd_getD`, `foldl_add_congr`, `weigh_congr`,
    `valueAt_congr`; two starts that are read alike in `foldl_add_congr` and `joinV_fold`; a number
    in range in `padTo_getD` and `tabV_swap`; two in `sumsTo_congr`.

Users. `left_site_fast` (Honest/K3/Law/AtSite.lean) and Honest/K3/Law/Thread/LeftThr.lean call
`agreeLawful`. It is the half of the statement `AgreeSame` (Statements.lean) that is used: all that
is shown of a course is general in its summands, so a second structure is served as soon as it is
`Lawful`.

Limits. The other half of `AgreeSame` (the two structures give the same rounds) is not proved in
this file: it remains a statement. A lemma about definitions of the honest side. That any two
structures agree is other files' to show. `mem_bits'` is `mem_bits` (Honest/K3/Law/LookLeftOf.lean)
under another name.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.StageStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE oneE addE subE mulE)
open OnBytes.Model (Reading eqTab)
open OnBytes.Slice (GE)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call valueAt total)
open ProofFile.Honest.SumLaw (SumsTo jobPoly varsOf drawsOk ownOf)

variable {W : Type}

/-! ## Lists that are read alike -/

/-- Two lists are read alike. -/
def SameRd (a b : List E) : Prop := a.map rd = b.map rd

theorem sameRd_getD : ∀ {a b : List E}, SameRd a b → ∀ j, rd (a.getD j zeroE) = rd (b.getD j zeroE)
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [SameRd] at h
  | _ :: _, [], h, _ => by simp [SameRd] at h
  | x :: a, y :: b, h, 0 => by
    simp only [SameRd, List.map_cons, List.cons.injEq] at h
    simpa using h.1
  | x :: a, y :: b, h, j + 1 => by
    simp only [SameRd, List.map_cons, List.cons.injEq] at h
    simpa using sameRd_getD (a := a) (b := b) h.2 j

theorem rd_add {x y x' y' : E} (h0 : rd x = rd x') (h1 : rd y = rd y') :
    rd (addE x y) = rd (addE x' y') :=
  (Reading.gl.add x y).trans ((congrArg₂ (· + ·) h0 h1).trans (Reading.gl.add x' y').symm)

theorem foldl_add_congr : ∀ {a b : List E}, SameRd a b → ∀ c c' : E, rd c = rd c' →
    rd (a.foldl addE c) = rd (b.foldl addE c')
  | [], [], _, _, _, hc => hc
  | [], _ :: _, h, _, _, _ => by simp [SameRd] at h
  | _ :: _, [], h, _, _, _ => by simp [SameRd] at h
  | x :: a, y :: b, h, c, c', hc => by
    simp only [SameRd, List.map_cons, List.cons.injEq] at h
    rw [List.foldl_cons, List.foldl_cons]
    exact foldl_add_congr (a := a) (b := b) h.2 (addE c x) (addE c' y) (rd_add hc h.1)

theorem weigh_congr (v : Var) : ∀ {a b : List E}, SameRd a b → ∀ n,
    SameRd ((a.zipIdx n).map fun x => mulE x.1 (sumPow v x.2))
      ((b.zipIdx n).map fun x => mulE x.1 (sumPow v x.2))
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [SameRd] at h
  | _ :: _, [], h, _ => by simp [SameRd] at h
  | x :: a, y :: b, h, n => by
    simp only [SameRd, List.map_cons, List.cons.injEq] at h
    have ih := weigh_congr v (a := a) (b := b) h.2 (n + 1)
    simp only [SameRd, List.zipIdx_cons, List.map_cons, List.cons.injEq]
    exact ⟨rd_mul h.1 rfl, ih⟩

theorem sumOf_congr (v : Var) {a b : List E} (h : SameRd a b) :
    rd (sumOf v a) = rd (sumOf v b) := by
  unfold sumOf total
  exact foldl_add_congr (weigh_congr v h 0) zeroE zeroE rfl

theorem valueAt_congr (x : E) : ∀ {a b : List E}, SameRd a b → rd (valueAt a x) = rd (valueAt b x)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [SameRd] at h
  | _ :: _, [], h => by simp [SameRd] at h
  | p :: a, q :: b, h => by
    simp only [SameRd, List.map_cons, List.cons.injEq] at h
    have ih := valueAt_congr x (a := a) (b := b) h.2
    unfold valueAt at ih ⊢
    rw [List.foldr_cons, List.foldr_cons]
    exact rd_add (rd_mul ih rfl) h.1

theorem padTo_getD : ∀ (n : Nat) (a : List E) (j : Nat), j < n →
    (padTo n a).getD j zeroE = a.getD j zeroE
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, [], 0, _ => by simp [padTo_succ_nil]
  | n + 1, x :: a, 0, _ => by simp [padTo_succ_cons]
  | n + 1, [], j + 1, h => by
    have := padTo_getD n [] j (by omega)
    simpa [padTo_succ_nil] using this
  | n + 1, x :: a, j + 1, h => by
    have := padTo_getD n a j (by omega)
    simpa [padTo_succ_cons] using this

/-! ## The sums -/

/-- Summands whose polynomials are read alike, round by round along the challenges, sum alike. -/
theorem sumsTo_congr (p q : List E → List E) : ∀ (vs : List Var) (past rs : List E) (c c' : GE),
    (∀ n, n < vs.length → SameRd (padTo (vs.getD n (.plain 0)).d (p (past ++ rs.take n)))
      (padTo (vs.getD n (.plain 0)).d (q (past ++ rs.take n)))) →
    SumsTo Reading.gl vs p past rs c c' → SumsTo Reading.gl vs q past rs c c'
  | [], _, [], _, _, _, h => h
  | [], _, _ :: _, _, _, _, h => h
  | _ :: _, _, [], _, _, _, h => h
  | v :: vs, past, r :: rs, c, c', H, h => by
    obtain ⟨h1, h2⟩ := h
    have H0 : SameRd (padTo v.d (p past)) (padTo v.d (q past)) := by
      have := H 0 (by simp)
      simpa using this
    refine ⟨(sumOf_congr v H0).symm.trans h1, ?_⟩
    have e : Reading.gl.val (valueAt (padTo v.d (q past)) r) =
        Reading.gl.val (valueAt (padTo v.d (p past)) r) := (valueAt_congr r H0).symm
    rw [e]
    refine sumsTo_congr p q vs (past ++ [r]) rs _ c' (fun n hn => ?_) h2
    have := H (n + 1) (by simpa using hn)
    simpa [List.append_assoc] using this

/-! ## A course with other summands -/

/-- The course with another structure of summands. -/
abbrev swap (R : Course W) (B : LookJobs W) : Course W := { R with J := B }

theorem fit_swap {R : Course W} (B : LookJobs W) (h : Fit R) : Fit (swap R B) :=
  ⟨h.ok, h.base, h.draws⟩

theorem agreeAt_symm {R : Course W} {B : LookJobs W} (h : AgreeAt R B) : AgreeAt (swap R B) R.J :=
  fun s hs k hc => ⟨fun n hn => ((h s hs k hc).1 n hn).symm,
    fun e he => ⟨((h s hs k hc).2 e he).1.symm, ((h s hs k hc).2 e he).2.symm⟩⟩

/-- A stage's sumcheck has a challenge for each of its variables. -/
theorem r_length {R : Course W} (hF : Fit R) {s : Stage} (hs : s ∈ stages R.f) {k : Call}
    (hc : s.call R.f = some k) : (R.r s).length = (R.call s).all.length := by
  have h := drawsOk_stage hF hs hc
  unfold drawsOk at h
  have hl : (R.draws s).length = (VerifiableInference.Desc.Part.MaskedSum.entries (R.call s)).length
    := by
    have := congrArg List.length (eq_of_beq h)
    simpa using this
  unfold Course.r varsOf ownOf drawnE
  simp only [List.length_take, List.length_drop, List.length_map, hl]
  unfold VerifiableInference.Desc.Part.MaskedSum.entries Call.all
  cases (R.call s).ends <;> simp

theorem getD_d : ∀ (l : List Var) (n : Nat), (l.getD n (.plain 0)).d = (l.map Var.d).getD n 0
  | [], _ => by simp [Var.d]
  | _ :: _, 0 => by simp
  | _ :: l, n + 1 => by simpa using getD_d l n

/-- Along the run's challenges the two structures' polynomials are read alike. -/
theorem poly_agree {R : Course W} {B : LookJobs W} (hF : Fit R) (hA : AgreeAt R B) {s : Stage}
    (hs : s ∈ stages R.f) {k : Call} (hc : s.call R.f = some k) (n : Nat)
    (hn : n < (R.call s).all.length) :
    SameRd (padTo ((R.call s).all.getD n (.plain 0)).d (R.poly s ([] ++ (R.r s).take n)))
      (padTo ((R.call s).all.getD n (.plain 0)).d ((swap R B).poly s ([] ++ (R.r s).take n))) := by
  have hsh : shapeAt R.a s = k := shapeAt_of hc
  have hlen : ((R.r s).take n).length = n := by
    rw [List.length_take, r_length hF hs hc]
    omega
  have hd : ((R.call s).all.getD n (.plain 0)).d = (k.all.getD n (.plain 0)).d := by
    rw [getD_d, getD_d, all_map_d (call_vs_d R s) (call_ends R s), hsh]
  have hal : (R.call s).all.length = k.all.length := by
    have := congrArg List.length (all_map_d (call_vs_d R s) (call_ends R s))
    rw [hsh] at this
    simpa using this
  rw [hd, List.nil_append]
  have hp : ∀ J : LookJobs W, jobPoly (jobAt J R.a s) R.t.input (R.front s) (R.masks s)
      ((R.r s).take n) =
      if n < k.vs.length then (jobAt J R.a s).round R.t.input (R.front s) ((R.r s).take n)
      else (jobAt J R.a s).inY R.t.input (R.front s) ((R.r s).take n) (R.masks s) := by
    intro J
    unfold jobPoly
    rw [hlen]
    show (if n < (shapeAt R.a s).vs.length then _ else _) = _
    rw [hsh]
  show SameRd (padTo _ (jobPoly (jobAt R.J R.a s) R.t.input (R.front s) (R.masks s) _))
    (padTo _ (jobPoly (jobAt B R.a s) R.t.input (R.front s) (R.masks s) _))
  rw [hp, hp]
  by_cases h1 : n < k.vs.length
  · rw [if_pos h1, if_pos h1]
    have e : k.all.getD n (.plain 0) = k.vs.getD n (.plain 0) := by
      unfold Call.all
      cases k.ends with
      | none => rfl
      | some e => exact List.getD_append _ _ _ _ h1
    rw [e]
    exact (hA s hs k hc).1 n h1
  · rw [if_neg h1, if_neg h1]
    rw [hal] at hn
    cases he : k.ends with
    | none =>
      exfalso
      unfold Call.all at hn
      rw [he] at hn
      exact h1 hn
    | some e =>
      have hnv : n = k.vs.length := by
        unfold Call.all at hn
        rw [he] at hn
        simp at hn
        omega
      have e1 : (k.all.getD n (.plain 0)).d = e.dY + 1 := by
        unfold Call.all
        rw [he, hnv]
        simp [Var.d]
      rw [e1, hnv]
      exact ((hA s hs k hc).2 e he).1

theorem sums_swap {R : Course W} {B : LookJobs W} (hF : Fit R) (hA : AgreeAt R B) {s : Stage}
    (hs : s ∈ stages R.f) {k : Call} (hc : s.call R.f = some k) {c c' : GE} (h : Sums R s c c') :
    Sums (swap R B) s c c' :=
  sumsTo_congr (R.poly s) ((swap R B).poly s) _ [] (R.r s) c c'
    (fun n hn => poly_agree hF hA hs hc n hn) h

/-- The two structures' true end values are read alike. -/
theorem T_swap {R : Course W} {B : LookJobs W} (hA : AgreeAt R B) {s : Stage}
    (hs : s ∈ stages R.f) (j : Nat) (hj : j < s.tail R.f) :
    rd ((swap R B).T s j) = rd (R.T s j) := by
  obtain ⟨k, e, hc, he, hen⟩ := tail_pos (Nat.lt_of_le_of_lt (Nat.zero_le j) hj)
  have hsh : shapeAt R.a s = k := shapeAt_of hc
  have h := ((hA s hs k hc).2 e he).2
  have h' := sameRd_getD (a := padTo e.n _) (b := padTo e.n _) h j
  rw [padTo_getD _ _ _ (by omega), padTo_getD _ _ _ (by omega)] at h'
  have e1 : ∀ J : LookJobs W, (swap R J).T s j =
      ((jobAt J R.a s).ends R.t.input (R.front s) ((R.r s).take k.vs.length)).getD j zeroE := by
    intro J
    show ((jobAt J R.a s).ends R.t.input (R.front s)
      ((R.r s).take (shapeAt R.a s).vs.length)).getD j zeroE = _
    rw [hsh]
  rw [e1 B]
  have e2 := e1 R.J
  have e3 : (swap R R.J).T s j = R.T s j := rfl
  rw [← e3, e2]
  exact h'.symm

/-! ## What the forms should be worth -/

section
variable {R : Course W} {B : LookJobs W} (hA : AgreeAt R B)
include hA

theorem lineV_swap {s : Stage} (hs : s ∈ stages R.f) (ht : s.tail R.f = 2) (xi : E) :
    rd ((swap R B).lineV s xi) = rd (R.lineV s xi) :=
  rd_add (rd_mul rfl (T_swap hA hs 0 (by omega))) (rd_mul rfl (T_swap hA hs 1 (by omega)))

theorem planeV_swap (h2 : 2 ≤ R.f.planes) (j : Nat) :
    rd ((swap R B).planeV j) = rd (R.planeV j) := by
  unfold Course.planeV
  show rd (if j = 0 then _ else if j + 1 < R.f.planes then _ else if R.f.planes = 2 then _ else _) =
    _
  by_cases h0 : j = 0
  · rw [if_pos h0, if_pos h0]
    exact T_swap hA (mem_tie (by omega)) 2 (show 2 < 3 by omega)
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : j + 1 < R.f.planes
    · rw [if_pos h1, if_pos h1]
      obtain ⟨q, rfl⟩ : ∃ q, j = q + 1 := ⟨j - 1, by omega⟩
      exact T_swap hA (mem_tie (by omega)) 1 (show 1 < 2 by omega)
    · rw [if_neg h1, if_neg h1]
      by_cases h3 : R.f.planes = 2
      · rw [if_pos h3, if_pos h3]
        exact T_swap hA (mem_tie (by omega)) 1 (show 1 < 3 by omega)
      · rw [if_neg h3, if_neg h3]
        obtain ⟨q, hq⟩ : ∃ q, R.f.planes - 2 = q + 1 := ⟨R.f.planes - 3, by omega⟩
        rw [hq]
        exact T_swap hA (mem_tie (by omega)) 0 (show 0 < 2 by omega)

theorem joinV_fold (h2 : 2 ≤ R.f.planes) : ∀ (l : List Nat) (c c' : E), rd c = rd c' →
    rd (l.foldl (fun c j => addE c (mulE ((eqTab R.pts.rhoT).getD j zeroE)
        (if j < R.f.planes then (swap R B).planeV j else oneE))) c) =
    rd (l.foldl (fun c j => addE c (mulE ((eqTab R.pts.rhoT).getD j zeroE)
        (if j < R.f.planes then R.planeV j else oneE))) c')
  | [], _, _, hc => hc
  | j :: l, c, c', hc => by
    simp only [List.foldl_cons]
    apply joinV_fold h2 l
    refine rd_add hc (rd_mul rfl ?_)
    by_cases hj : j < R.f.planes
    · rw [if_pos hj, if_pos hj]
      exact planeV_swap hA h2 j
    · rw [if_neg hj, if_neg hj]

theorem tabV_swap (h2 : 2 ≤ R.f.planes) : ∀ l, l ≤ R.f.d →
    rd ((swap R B).tabV l) = rd (R.tabV l)
  | 0, _ => joinV_fold hA h2 _ _ _ rfl
  | l + 1, h => lineV_swap hA (mem_tabOf (by omega)) rfl _

theorem rootV_swap (h2 : 2 ≤ R.f.planes) (i : Nat) : rd ((swap R B).rootV i) = rd (R.rootV i) := by
  show rd (if i + 1 < R.f.parts.length then (swap R B).T (.split i) 0
      else if R.f.parts.length ≤ 1 then (swap R B).T (.tie 0) 0
      else (swap R B).T (.split (R.f.parts.length - 2)) 1) =
    rd (if i + 1 < R.f.parts.length then R.T (.split i) 0
      else if R.f.parts.length ≤ 1 then R.T (.tie 0) 0
      else R.T (.split (R.f.parts.length - 2)) 1)
  by_cases h0 : i + 1 < R.f.parts.length
  · rw [if_pos h0, if_pos h0]
    exact T_swap hA (mem_split (by omega)) 0 (show 0 < 2 by omega)
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : R.f.parts.length ≤ 1
    · rw [if_pos h1, if_pos h1]
      exact T_swap hA (mem_tie (by omega)) 0 (show 0 < 3 by omega)
    · rw [if_neg h1, if_neg h1]
      exact T_swap hA (mem_split (by omega)) 1 (show 1 < 2 by omega)

/-- What a stage's form should be worth is read alike at the two structures. -/
theorem claimed_swap (hok : R.f.ok = true) (s : Stage)
    (hs : s ∈ stages R.f ∨ ∃ y ∈ R.f.parts.zipIdx, s = .key y.2 y.1) :
    rd ((swap R B).claimed s) = rd (R.claimed s) := by
  have h2 : 2 ≤ R.f.planes := two_le_planes_of_ok R.f hok
  match s, hs with
  | .shift, _ => rfl
  | .alpha, _ => rfl
  | .join, _ => rfl
  | .keyLine _ _, _ => rfl
  | .tabLine _, _ => rfl
  | .zero, _ => rfl
  | .bits, _ => rfl
  | .tie 0, _ => rfl
  | .tie 1, _ => exact T_swap hA (mem_tie (by omega)) 1 (show 1 < 3 by omega)
  | .tie (n + 2), hs =>
    have hn : n + 2 < R.f.planes - 1 := by
      rcases hs with h | ⟨y, _, h⟩
      · exact tie_lt h
      · exact nomatch h
    exact T_swap hA (mem_tie (by omega)) 0 (show 0 < 2 by omega)
  | .split 0, _ => exact T_swap hA (mem_tie (by omega)) 0 (show 0 < 3 by omega)
  | .split (i + 1), hs =>
    have hn : i + 1 < R.f.parts.length - 1 := by
      rcases hs with h | ⟨y, _, h⟩
      · exact split_lt h
      · exact nomatch h
    exact T_swap hA (mem_split (by omega)) 1 (show 1 < 2 by omega)
  | .key i 0, _ => exact rootV_swap hA h2 i
  | .key i (m + 1), hs =>
    have hm : Stage.key i m ∈ stages R.f := by
      rcases hs with h | ⟨y, hy, h⟩
      · obtain ⟨x, hx, hi, hlt⟩ := mem_key h
        rw [hi]
        exact mem_keyOf hx (by omega)
      · injection h with h1 h2
        rw [h1]
        exact mem_keyOf hy (by omega)
    exact lineV_swap hA hm rfl _
  | .tab l, hs =>
    have hl : l < R.f.d := by
      rcases hs with h | ⟨y, _, h⟩
      · exact mem_tab h
      · exact nomatch h
    exact tabV_swap hA h2 l (by omega)
  | .leaves, _ => exact tabV_swap hA h2 R.f.d (Nat.le_refl _)

end

/-! ## Lawful together -/

theorem mem_leaves (f : LFace) : Stage.leaves ∈ stages f := by
  unfold stages
  simp

theorem mem_bits' (f : LFace) : Stage.bits ∈ stages f := by
  unfold stages
  simp

theorem lawful_swap {R : Course W} {B : LookJobs W} {planes : List (E × E) → GE}
    {keys : Nat → Array E → GE} (hF : Fit R) (hA : AgreeAt R B) (h : Lawful R planes keys) :
    Lawful (swap R B) planes keys where
  sums := by
    intro s hs ht
    obtain ⟨k, e, hc, _, _⟩ := tail_pos ht
    have h1 := sums_swap hF hA hs hc (h.sums s hs ht)
    have e1 : rd (endTerm R.factor s ((swap R B).shown s)) = rd (endTerm R.factor s (R.shown s)) :=
      endTerm_congr R.f R.factor _ _ s ht (fun j hj => by
        have a1 := shown_getD (R.beta s) (s.tail R.f) ((swap R B).ends s) (R.masks s) j hj
        have a2 := shown_getD (R.beta s) (s.tail R.f) (R.ends s) (R.masks s) j hj
        exact a1.trans ((congrArg (· + rd (R.beta s) * rd ((R.masks s).getD j zeroE))
          (T_swap hA hs j hj)).trans a2.symm))
    show Sums (swap R B) s (rd ((swap R B).claimed s))
      (rd (endTerm R.factor s ((swap R B).shown s)))
    rw [claimed_swap hA hF.ok s (Or.inl hs), e1]
    exact h1
  leaves := by
    have h1 := sums_swap hF hA (mem_leaves R.f) (k := _) rfl h.leaves
    show Sums (swap R B) .leaves (rd ((swap R B).claimed .leaves)) _
    rw [claimed_swap hA hF.ok .leaves (Or.inl (mem_leaves R.f))]
    exact h1
  bits := (T_swap hA (mem_bits' R.f) 0 (show 0 < 1 by omega)).trans h.bits
  count := h.count
  keyEnds := fun y hy => (claimed_swap hA hF.ok _ (Or.inr ⟨y, hy, rfl⟩)).trans (h.keyEnds y hy)

/-- The statement that summands which agree at the run, as read, are lawful together. It is the half
of `AgreeSame` (Honest/K3/Law/Statements.lean) that speaks of `Lawful`. A lemma's statement, none of
the library's goals. -/
def AgreeLawful : Prop :=
  ∀ (W : Type) (R : Course W) (B : LookJobs W) (planes : List (E × E) → GE)
    (keys : Nat → Array E → GE),
    Fit R → AgreeAt R B → (Lawful { R with J := B } planes keys ↔ Lawful R planes keys)

/-- **Summands that agree at the run are lawful together** (the statement `AgreeLawful`). -/
theorem agreeLawful : AgreeLawful := fun _ R B _ _ hF hA =>
  ⟨fun h => lawful_swap (R := swap R B) (B := R.J) (fit_swap B hF) (agreeAt_symm hA) h,
    fun h => lawful_swap hF hA h⟩

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.sameRd_getD
#print axioms ProofFile.Honest.K3.Law.rd_add
#print axioms ProofFile.Honest.K3.Law.foldl_add_congr
#print axioms ProofFile.Honest.K3.Law.weigh_congr
#print axioms ProofFile.Honest.K3.Law.sumOf_congr
#print axioms ProofFile.Honest.K3.Law.valueAt_congr
#print axioms ProofFile.Honest.K3.Law.padTo_getD
#print axioms ProofFile.Honest.K3.Law.sumsTo_congr
#print axioms ProofFile.Honest.K3.Law.fit_swap
#print axioms ProofFile.Honest.K3.Law.agreeAt_symm
#print axioms ProofFile.Honest.K3.Law.r_length
#print axioms ProofFile.Honest.K3.Law.getD_d
#print axioms ProofFile.Honest.K3.Law.poly_agree
#print axioms ProofFile.Honest.K3.Law.sums_swap
#print axioms ProofFile.Honest.K3.Law.T_swap
#print axioms ProofFile.Honest.K3.Law.lineV_swap
#print axioms ProofFile.Honest.K3.Law.planeV_swap
#print axioms ProofFile.Honest.K3.Law.joinV_fold
#print axioms ProofFile.Honest.K3.Law.tabV_swap
#print axioms ProofFile.Honest.K3.Law.rootV_swap
#print axioms ProofFile.Honest.K3.Law.claimed_swap
#print axioms ProofFile.Honest.K3.Law.mem_leaves
#print axioms ProofFile.Honest.K3.Law.mem_bits'
#print axioms ProofFile.Honest.K3.Law.lawful_swap
#print axioms ProofFile.Honest.K3.Law.agreeLawful
