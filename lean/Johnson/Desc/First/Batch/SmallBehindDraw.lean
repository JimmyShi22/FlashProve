-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/SmallBehindDraw.lean: THE PUBLIC TEST ON THE SMALLNESS TEST's SINGLE
EQUATIONS (`formsInA`, Johnson/Desc/First/Batch/Ahead.lean) AT THE VERIFIER's STATE BEHIND A YES OF
THE DRAW OF THE MATRIX (Johnson/Desc/First/K8/Hear.lean). Definitions with code, and theorems.

Why. The table of joints opens the item on the single equations right behind the draw, and ties the
public test to it; the opener owes the test. The test a tree, `smallFits`
(Johnson/Desc/First/Batch/SmallFits.lean), gives the public test; here it is taken to the state, is
carried across the draw, and is cut into a half on sizes and a half on "there or ahead".
  `smallFitsAt sent own s`: THE NAMED TEST AT A STATE: `smallFits` at the boxes `boxInA`, off what
    the state holds: the open segment's part, the smallness test's part, the caller's list of
    tables. No where one of the three is missing.
  `formsInA_of_smallFitsAt`: its yes gives the public test, at every family of readers that gives
    `smallReader` at the name "K8.equations"; `formsInA_at_link`: so at the readers of a link.
  `smallFits_draw`: the test a tree reads neither field that the draw lays.
  `smallFitsAt_putTl`, `smallFitsAt_draw`: **a yes of the draw leaves the named test as it was**:
    an equation: both ways.
  `formsInA_behind_draw`: **the public test behind the draw, from the named test in front.**
  `sizeBox L`: array t is in the link's list and in the layout, with at least R rows and C columns:
    it reads the link's list of arrays and the layout alone: nothing that a sending turns.
  `nearA sent own a t`: array t is there, at a seat that may be read, or ahead.
  `boxInA_of_split`: the two give the box. `smallFits_split`: a test a tree at "B and p" from the
    test at B and p at the arrays that the equations name: the digits' array, each matrix's array of
    symbols, and the vector of reads of each table.
  `smallFitsAt_of_split`: **the named test from the half on sizes and the half on presence.**
Limits: (1) THAT THE NAMED TEST, OR EITHER HALF, HOLDS AT ANY STATE IS NOT SHOWN: both halves are
premises; neither has run. (2) One way, as `smallFits`: sufficient for the public test, not
necessary. (3) Nothing on what the equations are worth. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.SmallFits
import Johnson.Desc.First.K8.LawFunsStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S TailClaims.rowsAff TailClaims.rowsAff_all)
open VerifiableInference.Desc.First.TailClaims (readsP)

/-! ## 1 What the open segment's part reads of the state -/

/-- Where a link, a ledger and the smallness test's part are there, the open segment's part is
there. -/
theorem segAt_of (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) (hL : s.link? = some L)
    (hF : s.fork? = some F) (ht : s.tl? = some tl) :
    ∃ a, segAt? s = some a ∧ a.L = L ∧ a.F = F ∧ a.d.book = s.book := by
  unfold segAt?
  rw [hL, hF, ht]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

/-- And only there. -/
theorem segAt_reads (s : S) (a : Part) (ha : segAt? s = some a) :
    s.link? = some a.L ∧ s.fork? = some a.F ∧ a.d.book = s.book ∧ ∃ tl, s.tl? = some tl := by
  unfold segAt? at ha
  cases hL : s.link? with
  | none =>
    rw [hL] at ha
    exact nomatch ha
  | some L =>
    cases hF : s.fork? with
    | none =>
      rw [hL, hF] at ha
      exact nomatch ha
    | some F =>
      cases ht : s.tl? with
      | none =>
        rw [hL, hF, ht] at ha
        exact nomatch ha
      | some tl =>
        rw [hL, hF, ht] at ha
        obtain rfl := Option.some.inj ha
        exact ⟨rfl, rfl, rfl, tl, rfl⟩

/-! ## 2 The boxes read the link's part and the book alone -/

section
variable (sent : Nat → List (Nat × Nat)) (own : List (Nat × Nat))

theorem arrayIn_congr (a a' : Part) (hL : a'.L = a.L) (hb : a'.d.book = a.d.book) :
    arrayIn own a' = arrayIn own a := by
  funext t
  unfold arrayIn
  rw [hL, hb]

theorem aheadIn_congr (a a' : Part) (hL : a'.L = a.L) :
    aheadIn sent own a' = aheadIn sent own a := by
  funext b
  unfold aheadIn aheadOf
  rw [hL]

theorem boxInA_congr (a a' : Part) (hL : a'.L = a.L) (hb : a'.d.book = a.d.book) :
    boxInA sent own a' = boxInA sent own a := by
  funext t R C
  unfold boxInA boxIn
  rw [arrayIn_congr own a a' hL hb, aheadIn_congr sent own a a' hL, hL]

/-! ## 3 The named test at a state -/

/-- **The named test at a state.** -/
def smallFitsAt (s : S) : Bool :=
  match segAt? s, s.tl?, s.funs? with
  | some a, some tl, some funs => smallFits (boxInA sent own a) tl funs
  | _, _, _ => false

theorem smallFitsAt_some (s : S) (h : smallFitsAt sent own s = true) :
    ∃ a tl funs, segAt? s = some a ∧ s.tl? = some tl ∧ s.funs? = some funs ∧
      smallFits (boxInA sent own a) tl funs = true := by
  unfold smallFitsAt at h
  cases ea : segAt? s with
  | none =>
    rw [ea] at h
    exact nomatch h
  | some a =>
    cases et : s.tl? with
    | none =>
      rw [ea, et] at h
      exact nomatch h
    | some tl =>
      cases ef : s.funs? with
      | none =>
        rw [ea, et, ef] at h
        exact nomatch h
      | some funs =>
        rw [ea, et, ef] at h
        exact ⟨a, tl, funs, rfl, rfl, rfl, h⟩

theorem smallFitsAt_of (s : S) (a : Part) (tl : HTailF2) (funs : Array HFun)
    (ha : segAt? s = some a) (ht : s.tl? = some tl) (hf : s.funs? = some funs)
    (h : smallFits (boxInA sent own a) tl funs = true) : smallFitsAt sent own s = true := by
  unfold smallFitsAt
  rw [ha, ht, hf]
  exact h

/-- **Its yes gives the public test**, at every family of readers that gives the reader of the
single equations at that piece and name. -/
theorem formsInA_of_smallFitsAt (Rd : Readers) (b : Nat) (s : S)
    (hRd : Rd.forms b "K8.equations" s = smallReader s)
    (h : smallFitsAt sent own s = true) : formsInA Rd sent own b "K8.equations" s = true := by
  obtain ⟨a, tl, funs, ha, ht, hf, h⟩ := smallFitsAt_some sent own s h
  unfold formsInA
  rw [hRd, ha]
  unfold smallReader
  rw [ht, hf]
  show (lateOk [] a && (TailClaims.rowsAff tl funs).all fun f =>
    affInA sent own (mergeOf s) [] a f) = true
  rw [TailClaims.rowsAff_all]
  exact allForms_of_smallFits (entInA sent own a) (boxInA sent own a)
    (slotIn own (mergeOf s) [] a) (entInA_of_box sent own a) tl funs h

/-- So at the readers of a link. -/
theorem formsInA_at_link (H : LinkHoles) (l : Link S Claim) (b : Nat) (s : S)
    (h : smallFitsAt sent own s = true) :
    formsInA (readersOfLink (withSmall H) l) sent own b "K8.equations" s = true :=
  formsInA_of_smallFitsAt sent own _ b s (forms_small H l b s) h

/-! ## 4 Across the draw -/

omit sent own in
/-- The test a tree reads neither field that the draw lays. -/
theorem smallFits_draw (B : Nat → Nat → Nat → Bool) (tl : HTailF2) (funs : Array HFun)
    (m : Array Int) (f : Array Nat) :
    smallFits B { tl with cfF := m, cfFirst := f } funs = smallFits B tl funs := rfl

/-- The writing of the draw leaves the named test. -/
theorem smallFitsAt_putTl (s : S) (tl : HTailF2) (ht : s.tl? = some tl) (m : Array Int)
    (f : Array Nat) :
    smallFitsAt sent own (s.putTl { tl with cfF := m, cfFirst := f }) = smallFitsAt sent own s := by
  have e1 := First.K8.putTl_link s { tl with cfF := m, cfFirst := f }
  have e2 := First.K8.putTl_fork s { tl with cfF := m, cfFirst := f }
  have e3 := First.K8.putTl_tl s tl { tl with cfF := m, cfFirst := f } ht
  have e4 := First.K8.putTl_funs s { tl with cfF := m, cfFirst := f }
  have e5 := (First.K8.putTl_rest s { tl with cfF := m, cfFirst := f }).2.1
  cases ea : segAt? s with
  | none =>
    cases eb : segAt? (s.putTl { tl with cfF := m, cfFirst := f }) with
    | none =>
      unfold smallFitsAt
      rw [ea, eb]
    | some b =>
      obtain ⟨b1, b2, _, _⟩ := segAt_reads _ b eb
      rw [e1] at b1
      rw [e2] at b2
      obtain ⟨a, ha, _⟩ := segAt_of s b.L b.F tl b1 b2 ht
      rw [ea] at ha
      exact nomatch ha
  | some a =>
    obtain ⟨a1, a2, a3, _⟩ := segAt_reads s a ea
    obtain ⟨b, hb, b1, _, b3⟩ := segAt_of (s.putTl { tl with cfF := m, cfFirst := f }) a.L a.F _
      (e1.trans a1) (e2.trans a2) e3
    unfold smallFitsAt
    rw [ea, hb, e3, e4, ht]
    cases s.funs? with
    | none => rfl
    | some funs =>
      show smallFits (boxInA sent own b) { tl with cfF := m, cfFirst := f } funs =
        smallFits (boxInA sent own a) tl funs
      rw [boxInA_congr sent own a b b1 (b3.trans (e5.trans a3.symm)), smallFits_draw]

/-- **A yes of the draw leaves the named test as it was.** -/
theorem smallFitsAt_draw {Cl : Type} (p : First.K8.Par) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (First.K8.approximateRangeProofDrawKind (Cl := Cl) First.K8.atS p).decide s rs gs = .ok t) :
    smallFitsAt sent own t = smallFitsAt sent own s := by
  obtain ⟨r, rfl⟩ := First.K8.decide_one First.K8.atS p s t rs gs h
  obtain ⟨tl, ht, hm⟩ := (First.K8.decide_atS_iff p s t r gs).1 h
  rw [hm.2.2.2.2.2.2.2.2]
  exact smallFitsAt_putTl sent own s tl ht _ _

/-- **The public test behind the draw, from the named test in front.** -/
theorem formsInA_behind_draw {Cl : Type} (Rd : Readers) (b : Nat) (p : First.K8.Par) (s t : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hRd : Rd.forms b "K8.equations" t = smallReader t)
    (h : (First.K8.approximateRangeProofDrawKind (Cl := Cl) First.K8.atS p).decide s rs gs = .ok t)
    (hs : smallFitsAt sent own s = true) : formsInA Rd sent own b "K8.equations" t = true :=
  formsInA_of_smallFitsAt sent own Rd b t hRd
    ((smallFitsAt_draw sent own p s t rs gs h).trans hs)

/-! ## 5 The half on sizes and the half on presence -/

omit sent own in
/-- Array t is in the link's list and in the layout, with at least R rows and C columns. -/
def sizeBox (L : LinkCtx) (t R C : Nat) : Bool :=
  match (L.arrayOf[t]?).bind fun b => reqArray L.check.rows.layout b.1 b.2 with
  | some A => decide (R ≤ A.sizeI) && decide (C ≤ A.sizeC)
  | none => false

/-- Array t is there, at a seat that may be read, or ahead. -/
def nearA (a : Part) (t : Nat) : Bool :=
  (arrayIn own a t).isSome || ((a.L.arrayOf[t]?).bind (aheadIn sent own a)).isSome

omit own in
/-- The array of what is ahead is the layout's. -/
theorem aheadOf_array (a : Part) (b : Nat × String) (h : Ahead) (e : aheadOf sent a b = some h) :
    reqArray a.L.check.rows.layout b.1 b.2 = some h.A := by
  unfold aheadOf at e
  split at e
  · obtain ⟨A, hA, e⟩ := Option.bind_eq_some_iff.1 e
    split at e
    · exact nomatch e
    · obtain ⟨ms, _, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨M, _, e⟩ := Option.bind_eq_some_iff.1 e
      split at e
      · exact nomatch e
      · obtain ⟨x, _, e⟩ := Option.map_eq_some_iff.1 e
        subst e
        exact hA
  · exact nomatch e

/-- **The two halves give the box.** -/
theorem boxInA_of_split (a : Part) (t R C : Nat) (h1 : sizeBox a.L t R C = true)
    (h2 : nearA sent own a t = true) : boxInA sent own a t R C = true := by
  unfold sizeBox at h1
  unfold nearA at h2
  unfold boxInA
  rcases Eq.mp (Bool.or_eq_true _ _) h2 with h2 | h2
  · obtain ⟨A, hA⟩ := Option.isSome_iff_exists.1 h2
    obtain ⟨b, o, x, e1, e2, _, _⟩ := arrayIn_some own a t A hA
    rw [e1, Option.bind_some, e2] at h1
    refine Eq.mpr (Bool.or_eq_true _ _) (Or.inl ?_)
    unfold boxIn
    rw [hA]
    exact h1
  · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 h2
    obtain ⟨b, e1, e2⟩ := Option.bind_eq_some_iff.1 hq
    have e3 : aheadOf sent a b = some q := by
      unfold aheadIn at e2
      exact (Option.filter_eq_some_iff.1 e2).1
    rw [e1, Option.bind_some, aheadOf_array sent a b q e3] at h1
    refine Eq.mpr (Bool.or_eq_true _ _) (Or.inr ?_)
    rw [hq]
    exact h1

omit sent own in
/-- A read of the list is a read of one of the caller's tables, on the first or the third vector. -/
theorem readsP_mem (tl : HTailF2) (funs : Array HFun) (x : HFun × Nat) (hx : x ∈ readsP tl funs) :
    x.1 ∈ funs.toList ∧ (x.1.tree = 0 ∨ x.1.tree = 2) := by
  unfold readsP at hx
  obtain ⟨mu, _, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨un, hun, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨Fn, hFn, hx⟩ := List.mem_flatMap.1 hx
  split at hx
  · rename_i hc
    obtain ⟨sg, _, rfl⟩ := List.mem_map.1 hx
    obtain ⟨_, h2⟩ := Eq.mp (Bool.and_eq_true _ _) hc
    have h3 : Fn.tree = un := by simpa using h2
    refine ⟨hFn, ?_⟩
    show Fn.tree = 0 ∨ Fn.tree = 2
    rw [h3]
    simpa using hun
  · exact nomatch hx

omit sent own in
/-- **A test a tree at "B and p"**, from the test at B, and p at the arrays that are named. -/
theorem smallFits_split (B : Nat → Nat → Nat → Bool) (p : Nat → Bool) (tl : HTailF2)
    (funs : Array HFun) (h : smallFits B tl funs = true) (hZ : p tl.ix.ZZ = true)
    (hG : ∀ mu, mu < tl.NM → p (tl.gtTree.getD mu 0) = true)
    (hU : ∀ Fn ∈ funs.toList, Fn.tree = 0 ∨ Fn.tree = 2 →
      p ((tl.ix.U.getD Fn.tree none).getD 0) = true) :
    smallFits (fun t R C => B t R C && p t) tl funs = true := by
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h
  unfold smallFits
  refine Eq.mpr (Bool.and_eq_true _ _) ⟨List.all_eq_true.2 fun mu hmu => ?_,
    List.all_eq_true.2 fun x hx => ?_⟩
  · obtain ⟨g1, g2⟩ := Eq.mp (Bool.and_eq_true _ _) (List.all_eq_true.1 h1 mu hmu)
    unfold tieFits
    exact Eq.mpr (Bool.and_eq_true _ _)
      ⟨Eq.mpr (Bool.and_eq_true _ _) ⟨g1, hZ⟩,
       Eq.mpr (Bool.and_eq_true _ _) ⟨g2, hG mu (List.mem_range.1 hmu)⟩⟩
  · obtain ⟨g1, g2⟩ := Eq.mp (Bool.and_eq_true _ _) (List.all_eq_true.1 h2 x hx)
    obtain ⟨m1, m2⟩ := readsP_mem tl funs x hx
    unfold readFits
    exact Eq.mpr (Bool.and_eq_true _ _)
      ⟨Eq.mpr (Bool.and_eq_true _ _) ⟨g1, hZ⟩,
       List.all_eq_true.2 fun d hd => Eq.mpr (Bool.and_eq_true _ _)
        ⟨List.all_eq_true.1 g2 d hd, hU x.1 m1 m2⟩⟩

omit sent own in
/-- The test a tree grows with the box. -/
theorem smallFits_mono (B B' : Nat → Nat → Nat → Bool)
    (hB : ∀ t R C, B t R C = true → B' t R C = true) (tl : HTailF2) (funs : Array HFun)
    (h : smallFits B tl funs = true) : smallFits B' tl funs = true := by
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h
  unfold smallFits
  refine Eq.mpr (Bool.and_eq_true _ _) ⟨List.all_eq_true.2 fun mu hmu => ?_,
    List.all_eq_true.2 fun x hx => ?_⟩
  · obtain ⟨g1, g2⟩ := Eq.mp (Bool.and_eq_true _ _) (List.all_eq_true.1 h1 mu hmu)
    unfold tieFits
    exact Eq.mpr (Bool.and_eq_true _ _) ⟨hB _ _ _ g1, hB _ _ _ g2⟩
  · obtain ⟨g1, g2⟩ := Eq.mp (Bool.and_eq_true _ _) (List.all_eq_true.1 h2 x hx)
    unfold readFits
    exact Eq.mpr (Bool.and_eq_true _ _) ⟨hB _ _ _ g1,
      List.all_eq_true.2 fun d hd => hB _ _ _ (List.all_eq_true.1 g2 d hd)⟩

/-- **The named test from the half on sizes and the half on presence.** -/
theorem smallFitsAt_of_split (s : S) (a : Part) (tl : HTailF2) (funs : Array HFun)
    (ha : segAt? s = some a) (ht : s.tl? = some tl) (hf : s.funs? = some funs)
    (hS : smallFits (sizeBox a.L) tl funs = true) (hZ : nearA sent own a tl.ix.ZZ = true)
    (hG : ∀ mu, mu < tl.NM → nearA sent own a (tl.gtTree.getD mu 0) = true)
    (hU : ∀ Fn ∈ funs.toList, Fn.tree = 0 ∨ Fn.tree = 2 →
      nearA sent own a ((tl.ix.U.getD Fn.tree none).getD 0) = true) :
    smallFitsAt sent own s = true := by
  refine smallFitsAt_of sent own s a tl funs ha ht hf ?_
  refine smallFits_mono _ _ (fun t R C h => ?_) tl funs
    (smallFits_split (sizeBox a.L) (nearA sent own a) tl funs hS hZ hG hU)
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h
  exact boxInA_of_split sent own a t R C h1 h2

end

end VerifiableInference.Desc.K9

#print axioms VerifiableInference.Desc.K9.segAt_of
#print axioms VerifiableInference.Desc.K9.segAt_reads
#print axioms VerifiableInference.Desc.K9.boxInA_congr
#print axioms VerifiableInference.Desc.K9.formsInA_of_smallFitsAt
#print axioms VerifiableInference.Desc.K9.formsInA_at_link
#print axioms VerifiableInference.Desc.K9.smallFits_draw
#print axioms VerifiableInference.Desc.K9.smallFitsAt_putTl
#print axioms VerifiableInference.Desc.K9.smallFitsAt_draw
#print axioms VerifiableInference.Desc.K9.formsInA_behind_draw
#print axioms VerifiableInference.Desc.K9.aheadOf_array
#print axioms VerifiableInference.Desc.K9.boxInA_of_split
#print axioms VerifiableInference.Desc.K9.readsP_mem
#print axioms VerifiableInference.Desc.K9.smallFits_split
#print axioms VerifiableInference.Desc.K9.smallFits_mono
#print axioms VerifiableInference.Desc.K9.smallFitsAt_of_split
