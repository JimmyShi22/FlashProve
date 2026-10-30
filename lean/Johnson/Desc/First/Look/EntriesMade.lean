-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/EntriesMade.lean: the kind "lookup" (K3): the planner makes the lookup's
entries. Definitions and theorems.

Why. `P.entries p` (Johnson/Desc/First/Look/LookKind.lean) is `p.shape.bind (lookEntries p.set)`,
and `lookEntries set h` (Johnson/Desc/First/Look/LookRounds.lean) is some list just where the
planner's `planLookup`, at h's v and d, five bits of planes and a shift, ends well from the empty
plan. "p.entries.isSome" is a conjunct of the block's own test on the plan. The library's laws on
the planner (`Runs`, OnBytes/Params/PlanningLaws.lean) speak only where a routine ends well. This
file has the converse.

Main names:
  `Made.good_div`, `Made.good_ratio`: a quotient of two natural numbers is not marked bad where
    the lower end of the divisor is not 0.
  `Ends s c b r a x v l b' r' a'`: if every description in l is good (`RoundSpec.Good`: what
    `close` tests), then x ends well from every state with that setting, scope and open counts,
    returns v, keeps setting and scope, and leaves the counts b', r', a'. Its laws go as those of
    `Runs` do (`ends_bind`, `ends_pure`, `ends_close`, `ends_closeNone` and so on); the lists are
    the library's own (`pscList`, `treeList`, `lookupList`, OnBytes/Params/PlanListsSum.lean).
  `ends_lookup`: one lookup ends well, under `planLookup`'s two tests on its numbers.
  `FieldFit s c`: what every round of a lookup asks of the setting. `good_lookup`: under it every
    description in `lookupList` is good.
  `LinesFit l`: two tests on the lines of the parameter file.
  `lookEntries_isSome_of` (at any setting), `lookEntries_isSome`, `P.entries_isSome`.

The laws on the planner stand in a namespace of their own, VerifiableInference.Desc.First.Look.Made:
the library has an `Ends` of another meaning (OnBytes/Params/Fit/PlanTestsMade.lean).

Limits. Nothing on what the entries are (that is said by `Runs`), on errors or on what work is
worth. `LinesFit` is a premise here; that it holds wherever the parameter file was read stands in
Johnson/Desc/First/Look/EntriesMadeRead.lean [not in this library].
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.LookKind
import OnBytes.Params.PlanListsSum
import OnBytes.Params.OrderedLaws
import OnBytes.Tie.Pv.Lookup.Port.FoNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look.Made
open OnBytes OnBytes.Params

section
open OnBytes.Params.Binary

/-- The quotient of two bounds that are not marked bad and enclose numbers is not marked bad, where
the lower end of the divisor is not 0. -/
theorem good_div {a b : Bound} {x y : ℚ} (ha : Encl a x) (hb : Encl b y) (ga : a.bad = false)
    (gb : b.bad = false) (gz : b.lo.isZero = false) : (a / b).bad = false := by
  obtain ⟨a1, a2⟩ := ha ga
  obtain ⟨b1, b2⟩ := hb gb
  have l0 : 0 < b.lo.val := val_pos _ gz
  have y0 : 0 < y := l0.trans_le b1
  have h0 : 0 < b.hi.val := y0.trans_le b2
  have x0 : 0 ≤ x := (val_nonneg _).trans a1
  have hlom : b.lo.m ≠ 0 := by simpa [isZero] using gz
  have hhim : b.hi.m ≠ 0 := by
    intro hz
    have : b.hi.val = 0 := by simp [val, hz]
    linarith
  show (Bound.div a b).bad = false
  unfold Bound.div
  rw [ga, gb, gz]
  show (Bound.ends (a.lo.div b.hi .down) (a.hi.div b.lo .up)).bad = false
  exact Bound.ends_good (((val_div_down _ _ hhim).trans (div_le_div₀ x0 a1 y0 b2)).trans
    ((div_le_div₀ (val_nonneg _) a2 l0 b1).trans (val_div_up _ _ hlom)))

/-- a / b is not marked bad where b's lower end is not 0. -/
theorem good_ratio (a : ℕ) {b : ℕ} (hb : (Bound.ofNat b).lo.isZero = false) :
    (Bound.ratio a b).bad = false :=
  good_div (Bound.encl_ofNat a) (Bound.encl_ofNat b) rfl rfl hb

end

/-- **If every description in l is good, the routine x ends well** from every state with the setting
s, the scope c and the open counts b, r, a: it returns v, keeps s and c, and leaves the open counts
b', r', a'. -/
def Ends (s : Setting) (c : Scope) (b r a : Nat) {α : Type} (x : Planning α) (v : α)
    (l : List RoundSpec) (b' r' a' : Nat) : Prop :=
  (∀ y ∈ l, y.Good s c) → ∀ p : PlanState, p.set = s → p.scope = c → p.openBytes = b →
    p.openRoots = r → p.openAnswers = a →
    ∃ p' : PlanState, x p = .ok (v, p') ∧ p'.set = s ∧ p'.scope = c ∧ p'.openBytes = b' ∧
      p'.openRoots = r' ∧ p'.openAnswers = a'

section
variable {s : Setting} {c : Scope}

theorem ends_bind {α β : Type} {x : Planning α} {f : α → Planning β} {v : α} {w : β}
    {l1 l2 : List RoundSpec} {b r a b1 r1 a1 b2 r2 a2 : Nat}
    (h1 : Ends s c b r a x v l1 b1 r1 a1) (h2 : Ends s c b1 r1 a1 (f v) w l2 b2 r2 a2) :
    Ends s c b r a (x >>= f) w (l1 ++ l2) b2 r2 a2 := by
  intro hg p hs hc hb hr ha
  obtain ⟨p1, e1, s1, c1, ob, or1, oa⟩ :=
    h1 (fun y hy => hg y (List.mem_append_left _ hy)) p hs hc hb hr ha
  obtain ⟨p2, e2, k⟩ := h2 (fun y hy => hg y (List.mem_append_right _ hy)) p1 s1 c1 ob or1 oa
  refine ⟨p2, ?_, k⟩
  rw [bind_run, e1]
  exact e2

theorem Ends.cast {α : Type} {x : Planning α} {v : α} {l l' : List RoundSpec}
    {b r a b' r' a' : Nat} (h : Ends s c b r a x v l b' r' a') (e : l = l') :
    Ends s c b r a x v l' b' r' a' := e ▸ h

theorem ends_pure {α : Type} (v : α) (b r a : Nat) :
    Ends s c b r a (pure v : Planning α) v [] b r a :=
  fun _ p hs hc hb hr ha => ⟨p, rfl, hs, hc, hb, hr, ha⟩

theorem ends_setting (b r a : Nat) : Ends s c b r a theSetting s [] b r a := by
  intro _ p hs hc hb hr ha
  subst hs
  exact ⟨p, rfl, rfl, hc, hb, hr, ha⟩

theorem ends_needs {t : Bool} (ht : t = true) (why : String) (b r a : Nat) :
    Ends s c b r a (needs t why) () [] b r a := by
  subst ht
  exact fun _ p hs hc hb hr ha => ⟨p, rfl, hs, hc, hb, hr, ha⟩

theorem ends_scalars0 (n r a : Nat) : Ends s c 0 r a (planScalars n) () [] (24 * n) r a :=
  fun _ p hs hc hb hr ha =>
    ⟨{ p with openBytes := p.openBytes + 24 * n }, rfl, hs, hc,
      by show p.openBytes + 24 * n = 24 * n; rw [hb, Nat.zero_add], hr, ha⟩

theorem ends_close (name : String) (why : ErrorKind) (error : Bound) (d : Draws) (b r a : Nat) :
    Ends s c b r a (close name why error d) () [.said name why error d b r a] 0 0 0 := by
  intro hg p hs hc hb hr ha
  have hG : (RoundSpec.said name why error d b r a).Good s c := hg _ (List.mem_singleton.2 rfl)
  obtain ⟨g1, g2, g3⟩ := hG
  subst hs hc hb hr ha
  have g2' : p.set.workOf why p.scope < p.set.target := g2
  have g3' : p.set.workOf why p.scope ≠ 0 →
      p.set.workOf why p.scope + 6 ≤ 8 * p.set.nonceBytes := g3
  refine ⟨{ p with
    rounds := p.rounds.push
      ((RoundSpec.said name why error d p.openBytes p.openRoots p.openAnswers).round p.set p.scope),
    openBytes := 0, openRoots := 0, openAnswers := 0 }, ?_, rfl, rfl, rfl, rfl, rfl⟩
  rw [close_run]
  split
  · rename_i hcond
    exfalso
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne, ne_eq] at hcond
    rcases hcond with (h | h) | ⟨h0, h⟩
    · rw [g1] at h
      cases h
    · omega
    · have := g3' h0
      omega
  · rfl

theorem ends_closeNone (name : String) (b a : Nat) :
    Ends s c b 0 a (closeNone name) () [.silent name b a] 0 0 0 := by
  intro _ p hs hc _ hr _
  refine ⟨{ p with
    rounds := p.rounds.push
      { entry := { name, msg := p.openBytes, answers := p.openAnswers }, scope := p.scope },
    openBytes := 0, openAnswers := 0 }, ?_, hs, hc, rfl, hr, rfl⟩
  have hne : ¬ ((p.openRoots != 0) = true) := by
    rw [hr]
    decide
  unfold closeNone
  rw [if_neg hne]

theorem ends_ite {α : Type} {P : Prop} [Decidable P] {x y : Planning α} {v w : α}
    {l1 l2 : List RoundSpec} {b r a b' r' a' : Nat} (h1 : P → Ends s c b r a x v l1 b' r' a')
    (h2 : ¬ P → Ends s c b r a y w l2 b' r' a') :
    Ends s c b r a (if P then x else y) (if P then v else w) (if P then l1 else l2) b' r' a' := by
  by_cases hp : P
  · rw [if_pos hp, if_pos hp, if_pos hp]
    exact h1 hp
  · rw [if_neg hp, if_neg hp, if_neg hp]
    exact h2 hp

theorem ends_when {β : Type} {P : Prop} [Decidable P] {x : Planning PUnit} {k : PUnit → Planning β}
    {w : β} {l1 l2 : List RoundSpec} {b r a b' r' a' : Nat} (h1 : Ends s c b r a x () l1 b r a)
    (h2 : Ends s c b r a (k ()) w l2 b' r' a') :
    Ends s c b r a (if P then x >>= k else pure PUnit.unit >>= k) w
      ((if P then l1 else []) ++ l2) b' r' a' := by
  by_cases hp : P
  · rw [if_pos hp, if_pos hp]
    exact ends_bind h1 h2
  · rw [if_neg hp, if_neg hp]
    exact ends_bind (ends_pure () b r a) h2

theorem ends_times {x : Planning Unit} {l : List RoundSpec} (h : Ends s c 0 0 0 x () l 0 0 0) :
    ∀ n : Nat, Ends s c 0 0 0 (times n x) () (List.replicate n l).flatten 0 0 0
  | 0 => ends_pure () 0 0 0
  | n + 1 => by
      have := ends_bind h (f := fun _ => times n x) (ends_times h n)
      rw [List.replicate_succ, List.flatten_cons]
      exact this

theorem ends_forEach {α : Type} {f : α → Planning Unit} {L : α → List RoundSpec}
    (h : ∀ x, Ends s c 0 0 0 (f x) () (L x) 0 0 0) :
    ∀ l : List α, Ends s c 0 0 0 (forEach l f) () (l.map L).flatten 0 0 0
  | [] => ends_pure () 0 0 0
  | x :: t => by
      have := ends_bind (h x) (f := fun _ => forEach t f) (ends_forEach h t)
      rw [List.map_cons, List.flatten_cons]
      exact this

/-! ## The routines of a lookup: each proof is the library's for Runs, with the laws above -/

theorem ends_pscRounds :
    ∀ gs : List Nat, Ends s c 0 0 0 (planPscRounds s gs) () (gs.map (pscVariable s)) 0 0 0
  | [] => ends_pure () 0 0 0
  | g :: gs => by
      unfold planPscRounds
      exact Ends.cast (ends_bind (ends_scalars0 (g - 1) 0 0)
        (ends_bind (ends_close _ _ _ _ _ _ _) (ends_pscRounds gs))) (by simp [pscVariable])

theorem ends_psc (x : PscSize) : Ends s c 0 0 0 (planPsc x) () (pscList s x) 0 0 0 := by
  unfold planPsc
  exact Ends.cast (ends_bind (ends_setting 0 0 0) (ends_bind (ends_scalars0 1 0 0)
    (ends_bind (ends_close _ _ _ _ _ _ _) (ends_bind (ends_pscRounds x.degree)
      (ends_ite
        (fun _ => ends_bind (ends_scalars0 x.degreeY 0 0) (ends_bind (ends_close _ _ _ _ _ _ _)
          (ends_bind (ends_scalars0 x.values 0 0) (ends_closeNone _ _ _))))
        (fun _ => ends_pure () 0 0 0))))))
    (by simp [pscList, pscEpsilon, pscY])

theorem ends_zero (vars : Nat) : Ends s c 0 0 0 (planZero vars) ()
    [.said "ZERO" .field (fieldError s vars) { drawE := vars, priced := .roundItself }
      0 0 0] 0 0 0 := by
  unfold planZero
  exact Ends.cast (ends_bind (ends_setting 0 0 0) (ends_close _ _ _ _ _ _ _)) (by simp)

theorem ends_line : Ends s c 0 0 0 planLine () [lineRound s] 0 0 0 := by
  unfold planLine
  exact Ends.cast (ends_bind (ends_setting 0 0 0) (ends_close _ _ _ _ _ _ _)) (by simp [lineRound])

theorem ends_shift (unionEntries : Nat) : Ends s c 0 0 0 (planShift unionEntries) ()
    [.said "LKP shift" .field (fieldError s unionEntries) { drawE := 1, priced := .callersWord }
      0 0 0] 0 0 0 := by
  unfold planShift
  exact Ends.cast (ends_bind (ends_setting 0 0 0) (ends_close _ _ _ _ _ _ _)) (by simp)

theorem ends_join (vars : Nat) : Ends s c 0 0 0 (planJoin vars) ()
    [.said "JOIN" .field (fieldError s vars) { drawE := vars, priced := .roundItself }
      0 0 0] 0 0 0 := by
  unfold planJoin
  exact Ends.cast (ends_bind (ends_setting 0 0 0) (ends_close _ _ _ _ _ _ _)) (by simp)

theorem ends_treeLevels (more : Nat) :
    ∀ fuel l : Nat, Ends s c 0 0 0 (planTreeLevels more fuel l) () (treeList s more fuel l) 0 0 0
  | 0, _ => ends_pure () 0 0 0
  | fuel + 1, l => by
      unfold planTreeLevels
      exact Ends.cast
        (ends_bind (ends_psc _) (ends_bind ends_line (ends_treeLevels more fuel (l + 1))))
        (by simp [treeList])

theorem ends_productTree (levels more : Nat) :
    Ends s c 0 0 0 (planProductTree levels more) () (treeList s more levels 0) 0 0 0 :=
  ends_treeLevels more levels 0

/-- **One lookup ends well**, if its descriptions are good, under its two tests on its numbers. -/
theorem ends_lookup (x : LookupSize)
    (h1 : (decide (1 ≤ x.mu) && decide (x.mu ≤ 6) &&
      decide (2 ≤ (if x.live != 0 then x.live else 2 ^ min x.mu 6)) &&
      decide ((if x.live != 0 then x.live else 2 ^ min x.mu 6) ≤ 2 ^ min x.mu 6)) = true)
    (h2 : (decide (sumT ((if x.parts.isEmpty then [x.v] else x.parts).map (2 ^ ·)) <
        2 ^ (if x.live != 0 then x.live else 2 ^ min x.mu 6)) &&
      decide (2 ^ x.d * (2 ^ (if x.live != 0 then x.live else 2 ^ min x.mu 6) - 1) < s.p)) = true) :
    Ends s c 0 0 0 (planLookup x) () (lookupList s x) 0 0 0 := by
  unfold planLookup
  exact Ends.cast (ends_bind (ends_setting 0 0 0) (ends_bind (ends_needs h1 _ 0 0 0)
    (ends_bind (ends_needs h2 _ 0 0 0)
    (ends_when (ends_shift _)
    (ends_bind (ends_close _ _ _ _ _ _ _) (ends_bind (ends_psc _)
    (ends_bind (ends_times (ends_psc _) _) (ends_bind (ends_times (ends_psc _) _)
    (ends_bind (ends_join _) (ends_bind (ends_forEach (fun v => ends_productTree v 0) _)
    (ends_bind (ends_productTree _ _) (ends_bind (ends_psc _)
    (ends_bind (ends_zero _) (ends_psc _))))))))))))))
    (by simp [lookupList, lookupLive, lookupParts])

/-- A routine that ends well with nothing open gives a finished plan. -/
theorem finish_ends {x : Planning Unit} {l : List RoundSpec} (hx : Ends s c 0 0 0 x () l 0 0 0)
    (hg : ∀ y ∈ l, y.Good s c) : ∃ P, finish s c x = .ok P := by
  obtain ⟨p', e, _, _, ob, orr, oa⟩ := hx hg { set := s, scope := c } rfl rfl rfl rfl rfl
  unfold finish
  rw [e]
  show ∃ P, (if (p'.openBytes != 0 || p'.openRoots != 0 || p'.openAnswers != 0) = true then
    (Except.error notAdmitted : Except String Planned) else .ok ⟨s, p'.rounds.toList⟩) = .ok P
  rw [ob, orr, oa]
  exact ⟨_, rfl⟩

/-! ## The descriptions of a lookup are good -/

/-- **What every round of a lookup asks of the setting**, in the scope c. -/
def FieldFit (s : Setting) (c : Scope) : Prop :=
  s.workOf .field c < s.target ∧
    (s.workOf .field c ≠ 0 → s.workOf .field c + 6 ≤ 8 * s.nonceBytes) ∧
    (Bound.ofNat s.cardE).lo.isZero = false ∧ (Bound.ofNat (s.cardE - 1)).lo.isZero = false

theorem good_said {name : String} {n den : Nat} {d : Draws} {b r a : Nat}
    (hw : s.workOf .field c < s.target)
    (hn : s.workOf .field c ≠ 0 → s.workOf .field c + 6 ≤ 8 * s.nonceBytes)
    (hd : (Bound.ofNat den).lo.isZero = false) :
    (RoundSpec.said name .field (Bound.ratio n den) d b r a).Good s c := by
  refine ⟨?_, hw, hn⟩
  show (if c == .request && 1 < s.instances then Bound.ratio n den * Bound.ofNat s.instances
    else Bound.ratio n den).bad = false
  split
  · exact Bound.good_mul (Bound.encl_hi (Bound.ordered_ratio n den)) (Bound.encl_ofNat _)
      (good_ratio n hd) rfl
  · exact good_ratio n hd

theorem good_field (hf : FieldFit s c) (name : String) (n : Nat) (d : Draws) (b r a : Nat) :
    (RoundSpec.said name .field (fieldError s n) d b r a).Good s c :=
  good_said hf.1 hf.2.1 hf.2.2.1

theorem good_fieldNZ (hf : FieldFit s c) (name : String) (n : Nat) (d : Draws) (b r a : Nat) :
    (RoundSpec.said name .field (fieldErrorNonzero s n) d b r a).Good s c :=
  good_said hf.1 hf.2.1 hf.2.2.2

theorem good_psc (hf : FieldFit s c) (x : PscSize) : ∀ y ∈ pscList s x, y.Good s c := by
  intro y hy
  unfold pscList at hy
  rcases List.mem_cons.1 hy with rfl | hy
  · exact good_field hf _ _ _ _ _ _
  rcases List.mem_append.1 hy with hy | hy
  · obtain ⟨g, _, rfl⟩ := List.mem_map.1 hy
    exact good_field hf _ _ _ _ _ _
  · split at hy
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact good_fieldNZ hf _ _ _ _ _ _
      · rw [List.mem_singleton.1 hy]
        trivial
    · exact absurd hy List.not_mem_nil

theorem good_tree (hf : FieldFit s c) (more : Nat) :
    ∀ (fuel l : Nat), ∀ y ∈ treeList s more fuel l, y.Good s c
  | 0, _, y, hy => absurd hy List.not_mem_nil
  | fuel + 1, l, y, hy => by
      unfold treeList at hy
      rcases List.mem_append.1 hy with hy | hy
      · exact good_psc hf _ y hy
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact good_field hf _ _ _ _ _ _
        · exact good_tree hf more fuel (l + 1) y hy

/-- **Every description of a lookup's rounds is good**, where the setting fits. -/
theorem good_lookup (hf : FieldFit s c) (x : LookupSize) : ∀ y ∈ lookupList s x, y.Good s c := by
  intro y hy
  unfold lookupList at hy
  rcases List.mem_append.1 hy with hy | hy
  · split at hy
    · rw [List.mem_singleton.1 hy]
      exact good_field hf _ _ _ _ _ _
    · exact absurd hy List.not_mem_nil
  rcases List.mem_cons.1 hy with rfl | hy
  · exact good_field hf _ _ _ _ _ _
  rcases List.mem_append.1 hy with hy | hy
  · exact good_psc hf _ y hy
  rcases List.mem_append.1 hy with hy | hy
  · obtain ⟨L, hL, hyL⟩ := List.mem_flatten.1 hy
    rw [List.eq_of_mem_replicate hL] at hyL
    exact good_psc hf _ y hyL
  rcases List.mem_append.1 hy with hy | hy
  · obtain ⟨L, hL, hyL⟩ := List.mem_flatten.1 hy
    rw [List.eq_of_mem_replicate hL] at hyL
    exact good_psc hf _ y hyL
  rcases List.mem_cons.1 hy with rfl | hy
  · exact good_field hf _ _ _ _ _ _
  rcases List.mem_append.1 hy with hy | hy
  · obtain ⟨L, hL, hyL⟩ := List.mem_flatten.1 hy
    obtain ⟨v, _, rfl⟩ := List.mem_map.1 hL
    exact good_tree hf 0 v 0 y hyL
  rcases List.mem_append.1 hy with hy | hy
  · exact good_tree hf _ _ 0 y hy
  rcases List.mem_append.1 hy with hy | hy
  · exact good_psc hf _ y hy
  rcases List.mem_cons.1 hy with rfl | hy
  · exact good_field hf _ _ _ _ _ _
  · exact good_psc hf _ y hy

end

end VerifiableInference.Desc.First.Look.Made

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model

/-- **The lookup's entries are made, at any setting**: the setting fits; 2 ^ v keys have room in a
count of 32 bits; the sum of all counts stays below the setting's prime. -/
theorem lookEntries_isSome_of (set : Params.Setting) (h : Forest.Shape)
    (hf : Made.FieldFit set .request) (hv : h.v < 32) (hd : 2 ^ h.d * (2 ^ 32 - 1) < set.p) :
    (lookEntries set h).isSome = true := by
  have h2 : (decide (sumT (([h.v] : List Nat).map (2 ^ ·)) < 2 ^ 32) &&
      decide (2 ^ h.d * (2 ^ 32 - 1) < set.p)) = true := by
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    refine ⟨?_, hd⟩
    show 0 + 2 ^ h.v < 2 ^ 32
    rw [Nat.zero_add]
    exact Nat.pow_lt_pow_right (by decide) hv
  obtain ⟨P, e⟩ := Made.finish_ends
    (Made.ends_lookup (s := set) (c := .request)
      { v := h.v, d := h.d, mu := 5, shifted := true } rfl h2)
    (Made.good_lookup hf _)
  unfold lookEntries
  have e' : Params.finish set .request
      (Params.planForest { v := h.v, d := h.d, shifted := true }) = .ok P := e
  rw [e']
  rfl

/-- **The two tests on the lines of the parameter file** that every round of a lookup asks of the
setting: the work in front of a field round of a request is below the target, and, if it is not 0,
it and six bits more fit the nonce of eight bytes. -/
def LinesFit (l : Params.Lines) : Prop :=
  l.workField.request < l.sec ∧ (l.workField.request ≠ 0 → l.workField.request + 6 ≤ 64)

/-- The number of elements of the extension field, as a bound, has a lower end that is not 0; so has
that number less 1. Two closed evaluations. -/
theorem cardE_lo : (Params.Bound.ofNat ((2 ^ 64 - 2 ^ 32 + 1) ^ 3)).lo.isZero = false := by
  decide +kernel

theorem cardE1_lo : (Params.Bound.ofNat ((2 ^ 64 - 2 ^ 32 + 1) ^ 3 - 1)).lo.isZero = false := by
  decide +kernel

theorem fieldFit_of_lines {l : Params.Lines} (hl : LinesFit l) :
    Made.FieldFit (Params.settingOf l) .request :=
  ⟨hl.1, hl.2, cardE_lo, cardE1_lo⟩

/-- **The planner makes the lookup's entries**, at the setting that the lines of the parameter file
fix. -/
theorem lookEntries_isSome (l : Params.Lines) (h : Forest.Shape) (hl : LinesFit l) (hv : h.v < 32)
    (hd : 2 ^ (h.d + 32) < pW.toNat) : (lookEntries (Params.settingOf l) h).isSome = true := by
  refine lookEntries_isSome_of _ h (fieldFit_of_lines hl) hv ?_
  show 2 ^ h.d * (2 ^ 32 - 1) < 2 ^ 64 - 2 ^ 32 + 1
  have e : pW.toNat = 2 ^ 64 - 2 ^ 32 + 1 := by decide
  rw [e, Nat.pow_add] at hd
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) hd

/-- **At a place.** -/
theorem P.entries_isSome (p : P) (h : Forest.Shape) (l : Params.Lines) (hs : p.shape = some h)
    (hset : p.set = Params.settingOf l) (hl : LinesFit l) (hok : FoNums.ok h = true) :
    p.entries.isSome = true := by
  unfold FoNums.ok at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  unfold P.entries
  rw [hs, hset]
  exact lookEntries_isSome l h hl hok.1.1.1.1.1.1.1.1.1.2 hok.2

end VerifiableInference.Desc.First.Look

#print axioms VerifiableInference.Desc.First.Look.Made.good_ratio
#print axioms VerifiableInference.Desc.First.Look.Made.ends_lookup
#print axioms VerifiableInference.Desc.First.Look.Made.good_lookup
#print axioms VerifiableInference.Desc.First.Look.lookEntries_isSome_of
#print axioms VerifiableInference.Desc.First.Look.lookEntries_isSome
#print axioms VerifiableInference.Desc.First.Look.P.entries_isSome
