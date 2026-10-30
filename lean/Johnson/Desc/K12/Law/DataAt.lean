-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/DataAt.lean: a stretch's data, a frame's list of trees and the trees' depths,
made by hand off the plan of a proximity test (the kind K12), general in the place, under one test
with code that the kernel evaluates at a closed place. Definitions, statements and proofs.

Why. The law of the kind in the plain form (Johnson/Desc/K12/Coin/Sheet.lean) asks, among its public
premises, that the stretch's wants be the declared rounds' wants, each tree by its number over the
file. Here the trees in front of the stretch are named by their declared source, so that how many
trees the earlier chains send can stay a letter.
Main names: all in the namespace `H2K.Member`.
  `rdsAt p`, `wsAt p`: the block's declared rounds; the written rounds. `r0At`, `w0At`: the round
    "BAT" as the maker lays it. `dBAt num p :: dtAt num p`: the stretch's data (`dataOf`,
    Johnson/Desc/K12/Law/DataOf.lean).
  `T : List (Fmt.TreeSource × ℕ)`: the trees in front of the stretch, by source, each with its depth.
    `sentAt p base`: the trees that the test's written rounds send, numbered from base. `allAt num p
    T base more`: T's trees by num, then the test's own, then more, a free letter.
  `openOk`, `opensOk p T`: the first declared round is "BAT"; as many written as declared rounds; no
    stored table; each declared opening either lies in front and stands in T with its declared
    depth, or is the test's own tree of that depth.
  `fitB b₁ b₂ ch free`: a source lies in front of the stretch: own n with n < free; taken c s with c
    < ch ≤ 2 and s below b₁ (c = 0) or b₂. `funOk T`: one source, one depth.
  `placeOk p ch b₁ b₂ T`: the three tests, and the place's chain is ch + 1.
  `find_front`: a tool on lists. `numAt_low`, `numAt_inj`: at `numAt`, where the first chain sends
    at least b₁ and the second at least b₂ trees: a source that fits is numbered below the stretch's
    base; two that fit and have one number are one.
  `depth_of`, `depth_at`: under `placeOk`, the block's test on the plan, b₁ ≤ t₁ and b₂ ≤ t₂: the
    depth of each declared opening's tree, at the stretch as the maker's `StageD`, is the declared
    one.
Limits: these data and this list of trees are no description's: that a description's stretch at the
block has just these data, or its chain's frame just these trees in this order, is not shown. «more»
stands behind: where it names a number that stands in front of it, the first match is taken. No
soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.DataOf
import Johnson.Desc.K12.Law.BatOneMade
import Johnson.Desc.K12.JoinGuarded
import Johnson.Desc.BlockSlot

set_option autoImplicit false
namespace H2K.Member
open OnBytes OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (WR writtenOf)
open H2K.Made (wr)

/-! ## The data -/

def rdsAt (p : P12) : List Fmt.DeclaredRound := (proximityTestKind guardedProximityTestParts p : Block T12 Unit).rounds
def wsAt (p : P12) : List WR := (writtenOf p.nums).getD []
def r0At (p : P12) : Fmt.DeclaredRound := ⟨{ Fmt.M1.rBat.entry with rows := p.nums.rows }, [], []⟩
def w0At (p : P12) : WR := wr (r0At p) .elems none
def dBAt (num : Fmt.TreeSource → ℕ) (p : P12) : RDT := rdtOf num (w0At p) (r0At p)
def dtAt (num : Fmt.TreeSource → ℕ) (p : P12) : List RDT := dataOf num (wsAt p).tail (rdsAt p).tail

/-- The trees that the test's written rounds send, numbered from base. -/
def sentAt (p : P12) (base : ℕ) : List LeftT :=
  (((wsAt p).filterMap (·.tree)).map (·.a)).zipIdx.map fun x => ⟨base + x.2, x.1⟩

/-- The trees in front by num, the test's own, and more. -/
def allAt (num : Fmt.TreeSource → ℕ) (p : P12) (T : List (Fmt.TreeSource × ℕ)) (base : ℕ)
    (more : List LeftT) : List LeftT :=
  (T.map fun x => (⟨num x.1, x.2⟩ : LeftT)) ++ (sentAt p base ++ more)

/-- The stretch as the maker's StageD. -/
def stAt (num : Fmt.TreeSource → ℕ) (p : P12) (a base : ℕ) (all : List LeftT) (key : ℕ → ℕ) : StageD :=
  ⟨a, base, all, dBAt num p :: dtAt num p, key, all⟩

/-! ## The tests with code -/

def openOk (p : P12) (T : List (Fmt.TreeSource × ℕ)) : Fmt.Shape × Fmt.TreeSource → Bool
  | (sh, .own n) =>
    if n < p.nums.free then T.contains (.own n, sh.a)
    else (treeW (wsAt p) (n - p.nums.free)).map (·.a) == some sh.a
  | (sh, .taken c s) => T.contains (.taken c s, sh.a)

def opensOk (p : P12) (T : List (Fmt.TreeSource × ℕ)) : Bool :=
  (rdsAt p).head? == some (r0At p) && (wsAt p).length == (rdsAt p).length &&
    (rdsAt p).all (·.stored.isEmpty) && ((rdsAt p).flatMap (·.opens)).all (openOk p T)

def fitB (b₁ b₂ ch free : ℕ) : Fmt.TreeSource → Bool
  | .own n => n < free
  | .taken c s => c < ch && ch ≤ 2 && s < (if c = 0 then b₁ else b₂)

def funOk (T : List (Fmt.TreeSource × ℕ)) : Bool :=
  T.all fun x => T.all fun y => x.1 != y.1 || x.2 == y.2

def placeOk (p : P12) (ch b₁ b₂ : ℕ) (T : List (Fmt.TreeSource × ℕ)) : Bool :=
  p.place.chain == ch + 1 && opensOk p T && T.all (fun x => fitB b₁ b₂ ch p.nums.free x.1) &&
    funOk T

/-! ## Tools -/

theorem find_front (num : Fmt.TreeSource → ℕ) (R : List LeftT) : ∀ (T : List (Fmt.TreeSource × ℕ)),
    (∀ x ∈ T, ∀ y ∈ T, num x.1 = num y.1 → x.2 = y.2) → ∀ x ∈ T,
    (((T.map fun x => (⟨num x.1, x.2⟩ : LeftT)) ++ R).find? (·.no == num x.1)).map (·.a) = some x.2
  | [], _, _, hx => by cases hx
  | y :: T, hc, x, hx => by
    by_cases h : num y.1 = num x.1
    · rw [List.map_cons, List.cons_append, List.find?_cons_of_pos (by simpa using h)]
      exact congrArg some (hc y (List.mem_cons_self ..) x hx h)
    · rw [List.map_cons, List.cons_append, List.find?_cons_of_neg (by simpa using h)]
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact absurd rfl h
      · exact find_front num R T
          (fun u hu v hv => hc u (List.mem_cons_of_mem _ hu) v (List.mem_cons_of_mem _ hv)) x hx'

theorem numAt_own (t₁ t₂ ch n : ℕ) : numAt t₁ t₂ ch (.own n) =
    (if ch = 0 then 0 else if ch = 1 then t₁ else t₁ + t₂) + n := rfl

theorem numAt_taken (t₁ t₂ ch c s : ℕ) : numAt t₁ t₂ ch (.taken c s) =
    (if c = 0 then 0 else if c = 1 then t₁ else t₁ + t₂) + s := rfl

theorem fitB_taken {b₁ b₂ ch free c s : ℕ} (h : fitB b₁ b₂ ch free (.taken c s) = true) :
    c < ch ∧ ch ≤ 2 ∧ s < (if c = 0 then b₁ else b₂) := by
  simp only [fitB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem numAt_low (t₁ t₂ ch free b₁ b₂ : ℕ) (h₁ : b₁ ≤ t₁) (h₂ : b₂ ≤ t₂) (x : Fmt.TreeSource)
    (hx : fitB b₁ b₂ ch free x = true) : numAt t₁ t₂ ch x < numAt t₁ t₂ ch (.own free) := by
  cases x with
  | own n =>
    have : n < free := by simpa [fitB] using hx
    rw [numAt_own, numAt_own]
    omega
  | taken c s =>
    obtain ⟨h1, h2, h3⟩ := fitB_taken hx
    rw [numAt_own, numAt_taken]
    split_ifs at h3 ⊢ <;> omega

theorem numAt_inj (t₁ t₂ ch free b₁ b₂ : ℕ) (h₁ : b₁ ≤ t₁) (h₂ : b₂ ≤ t₂) (x y : Fmt.TreeSource)
    (hx : fitB b₁ b₂ ch free x = true) (hy : fitB b₁ b₂ ch free y = true)
    (h : numAt t₁ t₂ ch x = numAt t₁ t₂ ch y) : x = y := by
  cases x with
  | own n =>
    cases y with
    | own m =>
      rw [numAt_own, numAt_own] at h
      have : n = m := by omega
      rw [this]
    | taken c s =>
      exfalso
      obtain ⟨h1, h2, h3⟩ := fitB_taken hy
      rw [numAt_own, numAt_taken] at h
      split_ifs at h3 h <;> omega
  | taken c s =>
    obtain ⟨h1, h2, h3⟩ := fitB_taken hx
    cases y with
    | own m =>
      exfalso
      rw [numAt_own, numAt_taken] at h
      split_ifs at h3 h <;> omega
    | taken c' s' =>
      obtain ⟨k1, k2, k3⟩ := fitB_taken hy
      rw [numAt_taken, numAt_taken] at h
      have : c = c' ∧ s = s' := by
        split_ifs at h3 k3 h <;> omega
      rw [this.1, this.2]

/-! ## The lists' heads -/

theorem wsAt_cons (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) :
    writtenOf p.nums = some (w0At p :: (wsAt p).tail) ∧ wsAt p = w0At p :: (wsAt p).tail := by
  obtain ⟨w0, w, hw⟩ := H2K.Made.written_of_planOk guardedProximityTestParts p hp
  have e := H2K.Made.written_bat_eq p.nums w0 w hw
  have h : wsAt p = w0 :: w := by
    unfold wsAt
    rw [hw]
    rfl
  have e' : w0 = w0At p := e
  subst e'
  rw [h]
  exact ⟨hw, rfl⟩

section
variable {p : P12} {T : List (Fmt.TreeSource × ℕ)}

theorem opensOk_parts (h : opensOk p T = true) :
    (rdsAt p).head? = some (r0At p) ∧ (wsAt p).length = (rdsAt p).length ∧
      (∀ r ∈ rdsAt p, r.stored = []) ∧ ∀ r ∈ rdsAt p, ∀ o ∈ r.opens, openOk p T o = true := by
  unfold opensOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, fun r hr => List.isEmpty_iff.1 (h3 r hr),
    fun r hr o ho => h4 o (List.mem_flatMap.2 ⟨r, hr, ho⟩)⟩

theorem rdsAt_cons (h : opensOk p T = true) : rdsAt p = r0At p :: (rdsAt p).tail := by
  have h1 := (opensOk_parts h).1
  cases e : rdsAt p with
  | nil =>
    rw [e] at h1
    cases h1
  | cons r rs =>
    rw [e] at h1
    rw [Option.some.inj h1]
    rfl

theorem data_at (num : Fmt.TreeSource → ℕ)
    (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) (h : opensOk p T = true) :
    dBAt num p :: dtAt num p = dataOf num (wsAt p) (rdsAt p) := by
  conv_rhs => rw [(wsAt_cons p hp).2, rdsAt_cons h]
  rfl

theorem len_at (h : opensOk p T = true) :
    (wsAt p).tail.length = (rdsAt p).tail.length := by
  rw [List.length_tail, List.length_tail, (opensOk_parts h).2.1]

end

/-! ## The depths -/

/-- **The depth of each declared opening's tree is the declared one**, under three facts on num. -/
theorem depth_of (p : P12) (T : List (Fmt.TreeSource × ℕ)) (num : Fmt.TreeSource → ℕ) (a base : ℕ)
    (more : List LeftT) (key : ℕ → ℕ)
    (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) (h : opensOk p T = true)
    (hown : ∀ n, num (.own (p.nums.free + n)) = base + n) (hlow : ∀ x ∈ T, num x.1 < base)
    (hc : ∀ x ∈ T, ∀ y ∈ T, num x.1 = num y.1 → x.2 = y.2) :
    ∀ r ∈ rdsAt p, ∀ o ∈ r.opens,
      (stAt num p a base (allAt num p T base more) key).depth (num o.2) = some o.1.a := by
  intro r hr o ho
  have hm := (opensOk_parts h).2.2.2 r hr o ho
  have front : ∀ (s : Fmt.TreeSource) (d : ℕ), T.contains (s, d) = true →
      (stAt num p a base (allAt num p T base more) key).depth (num s) = some d := by
    intro s d hs
    have hs' : (s, d) ∈ T := by simpa using hs
    unfold StageD.depth
    rw [if_pos (show num s < (stAt num p a base (allAt num p T base more) key).base from
      hlow _ hs')]
    exact find_front num _ T hc (s, d) hs'
  obtain ⟨sh, src⟩ := o
  cases src with
  | taken c s => exact front _ _ hm
  | own n =>
    by_cases hn : n < p.nums.free
    · exact front _ _ (by simpa [openOk, hn] using hm)
    · have hm' : (treeW (wsAt p) (n - p.nums.free)).map (·.a) = some sh.a := by
        simpa [openOk, hn] using hm
      have e : num (.own n) = base + (n - p.nums.free) := by
        rw [← hown]
        congr 2
        omega
      show (stAt num p a base (allAt num p T base more) key).depth (num (.own n)) = some sh.a
      rw [e]
      unfold StageD.depth
      rw [if_neg (show ¬ base + (n - p.nums.free) <
        (stAt num p a base (allAt num p T base more) key).base from
          Nat.not_lt.2 (Nat.le_add_right _ _))]
      show (treeShT (dBAt num p :: dtAt num p) (base + (n - p.nums.free) - base)).map (·.a) = _
      rw [data_at num hp h, treeSh_dataOf num _ _ _ (opensOk_parts h).2.1, Nat.add_sub_cancel_left]
      exact hm'

section
variable {p : P12} {ch b₁ b₂ : ℕ} {T : List (Fmt.TreeSource × ℕ)}

theorem placeOk_parts (h : placeOk p ch b₁ b₂ T = true) :
    p.place.chain = ch + 1 ∧ opensOk p T = true ∧
      (∀ x ∈ T, fitB b₁ b₂ ch p.nums.free x.1 = true) ∧
      ∀ x ∈ T, ∀ y ∈ T, x.1 = y.1 → x.2 = y.2 := by
  unfold placeOk funOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true, bne_iff_ne] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun x hx y hy e => ?_⟩
  rcases h4 x hx y hy with h5 | h5
  · exact absurd e h5
  · exact h5

end

/-- **The same at numAt**: the base is the number of the chain's own tree «free». -/
theorem depth_at (p : P12) (ch b₁ b₂ : ℕ) (T : List (Fmt.TreeSource × ℕ)) (t₁ t₂ a : ℕ)
    (more : List LeftT) (key : ℕ → ℕ)
    (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) (h : placeOk p ch b₁ b₂ T = true)
    (h₁ : b₁ ≤ t₁) (h₂ : b₂ ≤ t₂) :
    ∀ r ∈ rdsAt p, ∀ o ∈ r.opens,
      (stAt (numAt t₁ t₂ ch) p a (numAt t₁ t₂ ch (.own p.nums.free))
        (allAt (numAt t₁ t₂ ch) p T (numAt t₁ t₂ ch (.own p.nums.free)) more) key).depth
          (numAt t₁ t₂ ch o.2) = some o.1.a := by
  obtain ⟨_, hO, hf, hu⟩ := placeOk_parts h
  refine depth_of p T (numAt t₁ t₂ ch) a _ more key hp hO (fun n => ?_)
    (fun x hx => numAt_low t₁ t₂ ch _ b₁ b₂ h₁ h₂ x.1 (hf x hx))
    (fun x hx y hy e =>
      hu x hx y hy (numAt_inj t₁ t₂ ch _ b₁ b₂ h₁ h₂ x.1 y.1 (hf x hx) (hf y hy) e))
  rw [numAt_own, numAt_own]
  omega

end H2K.Member

#print axioms H2K.Member.find_front
#print axioms H2K.Member.numAt_low
#print axioms H2K.Member.numAt_inj
#print axioms H2K.Member.wsAt_cons
#print axioms H2K.Member.depth_of
#print axioms H2K.Member.depth_at
