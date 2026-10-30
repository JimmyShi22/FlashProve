-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4DeclsWhole.lean: each read that the layers' own rounds declare
(Johnson/Road/K4/K4Decls.lean) is WHOLE and its PARTS FIT (ReadDecl.Whole,
Johnson/Desc/Reads/Decl.lean; PartsFit, Johnson/Desc/Reads/Join.lean), at the list of matrices that
tailsOf makes for a layout with the numbers of Laid2 (Johnson/Road/FormsKeysAddr.lean: what layout
has tested). So the join of Johnson/Road/K4/K4DeclsJoin.lean holds of every declaration: AT A
HEARING's RETURN, AT A FREE RECORD tl: not yet at a state with closed tables, at no letters. Of
Whole, count = room holds BY MAKE (rfl); what is shown are the makes' cells: long at powers of two,
the planes' whole column, short.

  `asks_shapes`: a family of tableAsks is long, with runs of 2 ^ la rows, on af, qa or a stream; or
    short, with runs of T rows, on ad, ar or qa; or one of three with runs of 2 ^ lmb rows on the
    matrix of the lookup's planes.
  `mem_k4Decls`: a declaration of the list is k4Decl of a family of the list.
  `long_fits`: the two equations of the make long, at powers of two.
  `planes_rows`: the planes' matrix has 2 ^ lmb rows.
  `k4Decl_whole`, `k4Decl_fit`: Whole and PartsFit of a family's declaration.
  `k4_joined_all`: at a hearing: the equation, and EVERY declaration is whole and joined.
Limits. PREMISES THAT STAY in k4_joined_all: the hearing's return; Laid2 of the plan's layout; the
plan's list of matrices is what tailsOf makes; g is a group of the layout; the smallness test's
record tl has that list's rows and columns and its length (htl, hNM); the test on lengths has said
yes of o.funs (lensB). NOT HERE: the address of a use: that a form of K4's names the entry that its
clause means. Met through Lean at no member. Nothing on soundness.


-/
import Johnson.Road.K4.K4DeclsJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Lay Reads TableAsk TableAt layParts layTables tableAsks phiOf funsOf Pub
  Own HPlan2 pointsOf tailsOf matIx)
open OnBytes.Desc.First.K4 (engFl hear)
open VerifiableInference.Reads
open Cb.Pv.Tail (TSize)

/-- The three sorts of families. -/
theorem asks_shapes (y : Lay) (rd : Reads) (g : ℕ) : ∀ a ∈ tableAsks y rd g,
    (a.lng = true ∧ a.L = 2 ^ y.h.la ∧
      ∃ mat, mat ∈ [0, 3, 4, 5] ∧ a.M0 = firstM y mat ∧ a.parts = partsM y mat) ∨
    (a.lng = false ∧ a.L = y.T ∧
      ∃ mat, mat ∈ [1, 2, 3] ∧ a.M0 = firstM y mat ∧ a.parts = partsM y mat) ∨
    (a.lng = false ∧ a.L = 2 ^ y.h.lmb ∧ a.M0 = (matIx y).iB ∧ a.parts = 1) := by
  intro a ha
  unfold tableAsks at ha
  simp only [List.mem_append] at ha
  rcases ha with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h)
  · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h
    exact Or.inl ⟨rfl, rfl, 0, by simp, rfl, rfl⟩
  · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h
    exact Or.inl ⟨rfl, rfl, 3, by simp, rfl, rfl⟩
  · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h
    exact Or.inl ⟨rfl, rfl, 4, by simp, rfl, rfl⟩
  · split at h
    · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h
      exact Or.inl ⟨rfl, rfl, 4, by simp, rfl, rfl⟩
    · exact absurd h List.not_mem_nil
  · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h
    exact Or.inl ⟨rfl, rfl, 5, by simp, rfl, rfl⟩
  · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h
    exact Or.inr (Or.inl ⟨rfl, rfl, 1, by simp, rfl, rfl⟩)
  · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h
    exact Or.inr (Or.inl ⟨rfl, rfl, 2, by simp, rfl, rfl⟩)
  · split at h
    · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h
      exact Or.inr (Or.inl ⟨rfl, rfl, 3, by simp, rfl, rfl⟩)
    · exact absurd h List.not_mem_nil
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> exact Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)

/-- A declaration of the list is that of a family of the list. -/
theorem mem_k4Decls {y : Lay} {fo : Forest.Heard} {pt : List (String × Array E)}
    {mats : Array (ℕ × ℕ)} : ∀ (asks : List TableAsk) (p : ℕ) (ds : List (ReadDecl E)),
    k4Decls y fo pt mats asks p = some ds → ∀ d ∈ ds,
      ∃ a ∈ asks, ∃ q phi, d = k4Decl y mats a q phi
  | [], _, ds, h, d, hd => by
    obtain rfl := Option.some.inj h
    exact absurd hd List.not_mem_nil
  | a :: rest, p, ds, h, d, hd => by
    have h' : ((phiOf y fo pt a).bind fun phi =>
        (k4Decls y fo pt mats rest (layParts mats a a.parts p).2).map fun ds =>
          k4Decl y mats a p phi :: ds) = some ds := h
    obtain ⟨phi, _, h2⟩ := Option.bind_eq_some_iff.mp h'
    obtain ⟨ds', h3, rfl⟩ := map_some h2
    rcases List.mem_cons.mp hd with rfl | hd'
    · exact ⟨a, List.mem_cons_self, p, phi, rfl⟩
    · obtain ⟨a', ha', r⟩ := mem_k4Decls rest _ ds' h3 d hd'
      exact ⟨a', List.mem_cons_of_mem _ ha', r⟩

/-- The make long fits, at powers of two. -/
theorem long_fits {lt la lm : ℕ} (h1 : lt ≤ la) (h2 : la ≤ lm) :
    (Make.long (2 ^ la / 2 ^ lt)).Fits (2 ^ la) (2 ^ lm) := by
  have e1 : 2 ^ la / 2 ^ lt = 2 ^ (la - lt) := Nat.pow_div h1 (by omega)
  have e2 : 2 ^ la / 2 ^ (la - lt) = 2 ^ lt := by
    rw [Nat.pow_div (Nat.sub_le _ _) (by omega), Nat.sub_sub_self h1]
  show 2 ^ la / 2 ^ lt * (2 ^ la / (2 ^ la / 2 ^ lt)) = 2 ^ la ∧
    2 ^ lm / (2 ^ la / (2 ^ la / 2 ^ lt)) = 2 ^ lm / 2 ^ la * (2 ^ la / 2 ^ lt)
  rw [e1, e2, Nat.pow_div (Nat.le_trans h1 h2) (by omega), Nat.pow_div h2 (by omega), ← pow_add,
    ← pow_add]
  constructor
  · congr 1
    omega
  · congr 1
    omega

/-- The planes' matrix has 2 ^ lmb rows. -/
theorem planes_rows (y : Lay) {g : ℕ} (hg : g < y.NGr) :
    ((matsR y g).getD (matIx y).iB (0, 0)).1 = 2 ^ y.h.lmb := by
  obtain ⟨_, _, t3⟩ := getD_three (y.parts.getD 0 0) (y.parts.getD 1 0)
    (y.mrow.getD 0 0, y.kcol.getD 0 0) (y.mrow.getD 1 0, y.kcol.getD 1 0)
    [(y.mrow.getD 2 0, y.kcol.getD 2 0), (2 ^ y.h.lmb, y.kbm), (y.mrow.getD 3 0, y.kcol.getD 3 0),
     (y.mxb, y.kxb), (y.mxb, y.kxb)] (0, 0)
  have hl := sizesTab_length y
  have e : (matIx y).iB = y.parts.getD 0 0 + y.parts.getD 1 0 + 1 := rfl
  have h1 : (sizesTab y).getD (y.parts.getD 0 0 + y.parts.getD 1 0 + 1) (0, 0) =
      (2 ^ y.h.lmb, y.kbm) := t3 1
  unfold matsR
  rw [tails_pairs y hg, e]
  have h2 : (sizesTab y).toArray.getD (y.parts.getD 0 0 + y.parts.getD 1 0 + 1) (0, 0) =
      (sizesTab y).getD (y.parts.getD 0 0 + y.parts.getD 1 0 + 1) (0, 0) := by
    simp [Array.getD, List.getD_eq_getElem?_getD, hl]
  rw [h2, h1]

/-- **A family's declaration is whole.** -/
theorem k4Decl_whole {y : Lay} (L2 : Laid2 y) (rd : Reads) {g : ℕ} (hg : g < y.NGr)
    {a : TableAsk} (ha : a ∈ tableAsks y rd g) (p : ℕ) (phi : Array E) :
    (k4Decl y (matsR y g) a p phi).Whole ((matsR y g).getD a.M0 (0, 0)).1
      ((matsR y g).getD a.M0 (0, 0)).2 := by
  refine ⟨?_, rfl, ?_⟩
  · show 0 < a.L
    rcases asks_shapes y rd g a ha with ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩
    · rw [h]
      positivity
    · rw [h, L2.T]
      positivity
    · rw [h]
      positivity
  · show (makeOf y a).Fits a.L _
    unfold makeOf
    rcases asks_shapes y rd g a ha with ⟨h0, h, mat, hm, h1, h2⟩ | ⟨h0, h, mat, hm, h1, _⟩ |
      ⟨h0, h, h1, _⟩
    · obtain ⟨lm, hla, hr⟩ := rows_of_laid2 L2 mat hm
      have hp : 0 < partsM y mat := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl
        · show 0 < y.parts.getD 0 0
          rw [L2.parts0]
          exact Nat.pos_of_ne_zero L2.NAf0
        · exact Nat.one_pos
        · exact Nat.one_pos
        · exact Nat.one_pos
      have hmat : mat ≤ 5 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        omega
      have e := tails_pair y hg hmat hp
      rw [Nat.add_zero] at e
      rw [if_pos h0, h, L2.T, h1, e, hr]
      exact long_fits (Nat.le_of_lt L2.lt_la) hla
    · have hne : (a.M0 == (matIx y).iB) = false := by
        rw [h1]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl
        all_goals first
          | (simp [firstM, matIx]; done)
          | (simp [firstM, matIx]; omega)
      rw [h0, hne]
      exact True.intro
    · have he : (a.M0 == (matIx y).iB) = true := by rw [h1]; exact beq_self_eq_true _
      rw [h0, he, h, h1]
      exact (planes_rows y hg).symm

/-- **Its parts fit.** -/
theorem k4Decl_fit {y : Lay} (rd : Reads) {g : ℕ} (hg : g < y.NGr) {a : TableAsk}
    (ha : a ∈ tableAsks y rd g) (p : ℕ) (phi : Array E) (t : TSize)
    (ht : ∀ i, (matsR y g).getD i (0, 0) = (t.m i, t.k i))
    (hNM : t.NM = y.parts.getD 0 0 + y.parts.getD 1 0 + 5) :
    PartsFit t (k4Decl y (matsR y g) a p phi) := by
  refine ⟨?_, fun q hq => ?_⟩
  · show a.M0 + a.parts ≤ t.NM
    rw [hNM]
    rcases asks_shapes y rd g a ha with ⟨_, _, mat, hm, h1, h2⟩ | ⟨_, _, mat, hm, h1, h2⟩ |
      ⟨_, _, h1, h2⟩
    · rw [h1, h2]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl
      all_goals first
        | (simp [firstM, partsM, matIx]; done)
        | (simp [firstM, partsM, matIx]; omega)
    · rw [h1, h2]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl <;> simp [firstM, partsM, matIx]
    · have e : (matIx y).iB = y.parts.getD 0 0 + y.parts.getD 1 0 + 1 := rfl
      rw [h1, h2, e]
      omega
  · have e := asks_fit y rd hg a ha q hq
    rw [ht, ht] at e
    exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩

/-- **At a hearing: the equation, and every declared read is whole and joined.** -/
theorem k4_joined_all {K : Type} {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard}
    {F G : Fork} {t u : Tape} {o : Own} (h : hear engFl P hp g fo F t = some (o, G, u))
    (val : E → K) (tl : HTailF2) (L2 : Laid2 P.y) (hT : P.tails = tailsOf P.y)
    (hg : g < P.y.NGr)
    (htl : ∀ i, (matsR P.y g).getD i (0, 0) = ((tl.mats.getD i {}).m, (tl.mats.getD i {}).k))
    (hNM : tl.NM = P.y.parts.getD 0 0 + P.y.parts.getD 1 0 + 5) (hB : lensB o.funs = true) :
    ∃ pts ds, pointsOf P.y o.H o.hd o.hd2 = some pts ∧
      k4Decls P.y fo pts (matsR P.y g) (tableAsks P.y P.rd g) 0 = some ds ∧
      FunsAre (sizeU3 tl o.funs) o.funs ds ∧
      ∀ d ∈ ds, d.Whole ((sizeU3 tl o.funs).m d.mat) ((sizeU3 tl o.funs).k d.mat) ∧
        Joined (sizeU3 tl o.funs) (phiU3 val o.funs) val d := by
  obtain ⟨pts, ds, h1, h2, h3, h4⟩ := k4_joined_hear h val tl hT hg htl hB
  refine ⟨pts, ds, h1, h2, h3, fun d hd => ?_⟩
  obtain ⟨a, ha, q, phi, rfl⟩ := mem_k4Decls _ _ ds h2 d hd
  have hW : (k4Decl P.y (matsR P.y g) a q phi).Whole
      ((sizeU3 tl o.funs).m (k4Decl P.y (matsR P.y g) a q phi).mat)
      ((sizeU3 tl o.funs).k (k4Decl P.y (matsR P.y g) a q phi).mat) := by
    have w := k4Decl_whole L2 P.rd hg ha q phi
    rw [htl a.M0] at w
    exact w
  exact ⟨hW, h4 _ hd (k4Decl_fit P.rd hg ha q phi (sizeU3 tl o.funs) htl hNM) hW⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.asks_shapes
#print axioms OnBytes.Road.K4.mem_k4Decls
#print axioms OnBytes.Road.K4.long_fits
#print axioms OnBytes.Road.K4.planes_rows
#print axioms OnBytes.Road.K4.k4Decl_whole
#print axioms OnBytes.Road.K4.k4Decl_fit
#print axioms OnBytes.Road.K4.k4_joined_all
