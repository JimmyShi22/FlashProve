-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/SmallFits.lean: THE PUBLIC TEST AT THE SMALLNESS TEST's SINGLE EQUATIONS,
BY A TEST A TREE. Definitions with code and theorems. No Mathlib.

Why. The public test `formsIn` at the reader `smallReader`
(Johnson/Desc/First/Batch/SmallReader.lean) asks of each single equation that it names only what is
there: at one small proof 10,568,064 equations (their authors' count): a run over all of them had
not ended after a quarter of an hour. But the forms' entries go in loops with plain bounds.
  GENERAL FIRST: E: a test on an entry; B t R C: a box; `BoxGives E B`: a box's yes gives E at every
    entry of array t below R and C. `tieFits`, `readFits`: the boxes of one matrix's ties; of one
    read's
    equations. `smallFits B tl funs`: all of them: one test a matrix, and for each read one test and
    one a column of its table. `allForms_of_smallFits`: **`smallFits` gives `allForms` of "every
    entry
    meets E"**.
  THEN TWICE: `boxIn own a` with `entIn` (the array is there, at a seat that may be read):
    `formsIn_of_smallFits`: the public test itself at the reader `smallReader` · `boxInA sent own a`
    with
    `entInA` (there, OR AHEAD: Johnson/Desc/First/Batch/Ahead.lean): `formsInA_of_smallFits`.
Limits: ONE WAY: `smallFits` is sufficient, not necessary: a false of it is not yet a false of the
public test. Nothing on what the equations are worth. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.SmallReader
import Johnson.Desc.First.Batch.Ahead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S TailClaims.rowsAff TailClaims.rowsAff_all)
open VerifiableInference.Desc.First.TailClaims (allForms tieAff readAff readsP digitEnts)

/-! ## 1 General in the test on an entry (E) and in the box (B) -/

section
variable (E : Ent → Bool) (B : Nat → Nat → Nat → Bool) (Sl : Nat → Bool)

/-- A form's entries meet E, its slots Sl. -/
def affG (f : Aff) : Bool := (f.ents.toList.all fun x => E x) && f.slots.toList.all fun x => Sl x.1

/-- What a box owes: every entry of that array below R and C meets E. -/
def BoxGives : Prop :=
  ∀ t R C, B t R C = true → ∀ x : Ent, x.tree = t → x.row < R → x.idx < C → E x = true

variable (hB : BoxGives E B)
include hB

/-- The two digits of one cell. -/
theorem digit_in (tl : HTailF2) (C u c0 c1 : Nat) (w : OnBytes.E)
    (h : B tl.ix.ZZ tl.tau C = true) (hu : u < tl.tau) (h0 : c0 < C) (h1 : c1 < C) :
    ∀ x ∈ digitEnts tl u c0 c1 w, E x = true := by
  intro x hx
  unfold digitEnts at hx
  rcases List.mem_cons.1 hx with e | hx
  · subst e
    exact hB _ _ _ h _ rfl hu h0
  · rcases List.mem_cons.1 hx with e | hx
    · subst e
      exact hB _ _ _ h _ rfl hu h1
    · cases hx

omit hB in
/-- The boxes of matrix mu's ties. -/
def tieFits (tl : HTailF2) (mu : Nat) : Bool :=
  B tl.ix.ZZ tl.tau
      (max ((tl.zzCol mu 0 0).getD 0) ((tl.zzCol mu 1 0).getD 0) + (tl.shp.getD mu {}).m) &&
    B (tl.gtTree.getD mu 0) (((tl.shp.getD mu {}).m + 2) / 3) (tl.shp.getD mu {}).k

theorem tie_in (tl : HTailF2) (mu i u : Nat) (h : tieFits B tl mu = true)
    (hi : i < ((tl.shp.getD mu {}).m + 2) / 3) (hu : u < tl.tau) :
    affG E Sl (tieAff tl mu i u) = true := by
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h
  unfold affG
  refine Eq.mpr (Bool.and_eq_true _ _) ⟨List.all_eq_true.2 fun x hx => ?_, rfl⟩
  simp only [tieAff, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter,
    List.mem_range, decide_eq_true_eq] at hx
  rcases hx with ⟨l, ⟨_, hl⟩, hx⟩ | ⟨c, hc, e⟩
  · exact digit_in E B hB tl _ u _ _ _ h1 hu (by omega) (by omega) x hx
  · subst e
    exact hB _ _ _ h2 _ rfl hi hc

omit hB in
/-- The boxes of the read x's equations. -/
def readFits (tl : HTailF2) (x : HFun × Nat) : Bool :=
  B tl.ix.ZZ tl.tau
      (max ((tl.zzCol x.1.mat 0 (x.2 * x.1.len)).getD 0)
        ((tl.zzCol x.1.mat 1 (x.2 * x.1.len)).getD 0) + x.1.len) &&
    (List.range (tl.mats.getD x.1.mat {}).k).all fun d =>
      B ((tl.ix.U.getD x.1.tree none).getD 0) 1 ((tl.tabAt x.1 d x.2).getD 0 + 1)

theorem read_in (tl : HTailF2) (x : HFun × Nat) (u : Nat) (h : readFits B tl x = true)
    (hu : u < tl.tau) : affG E Sl (readAff tl x u) = true := by
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h
  unfold affG
  refine Eq.mpr (Bool.and_eq_true _ _) ⟨List.all_eq_true.2 fun z hz => ?_, rfl⟩
  simp only [readAff, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at hz
  rcases hz with ⟨j, hj, hz⟩ | ⟨d, hd, e⟩
  · exact digit_in E B hB tl _ u _ _ _ h1 hu (by omega) (by omega) z hz
  · subst e
    exact hB _ _ _ (List.all_eq_true.1 h2 d (List.mem_range.2 hd)) _ rfl
      Nat.one_pos (Nat.lt_succ_self _)

omit hB in
/-- **The test a tree.** -/
def smallFits (tl : HTailF2) (funs : Array HFun) : Bool :=
  ((List.range tl.NM).all fun mu => tieFits B tl mu) &&
    (readsP tl funs).all fun x => readFits B tl x

/-- **It gives the test on every single equation.** -/
theorem allForms_of_smallFits (tl : HTailF2) (funs : Array HFun)
    (h : smallFits B tl funs = true) : allForms (affG E Sl) tl funs = true := by
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h
  unfold allForms
  refine Eq.mpr (Bool.and_eq_true _ _) ⟨?_, ?_⟩
  · exact List.all_eq_true.2 fun mu hmu => List.all_eq_true.2 fun i hi =>
      List.all_eq_true.2 fun u hu => tie_in E B Sl hB tl mu i u (List.all_eq_true.1 h1 mu hmu)
        (List.mem_range.1 hi) (List.mem_range.1 hu)
  · exact List.all_eq_true.2 fun x hx => List.all_eq_true.2 fun u hu =>
      read_in E B Sl hB tl x u (List.all_eq_true.1 h2 x hx) (List.mem_range.1 hu)

end

/-! ## 2 At what is there; and at what is there or ahead -/

section
variable (sent : Nat → List (Nat × Nat)) (own : List (Nat × Nat))

/-- The array is there and has at least R rows and C columns. -/
def boxIn (a : Part) (t R C : Nat) : Bool :=
  match arrayIn own a t with
  | some A => decide (R ≤ A.sizeI) && decide (C ≤ A.sizeC)
  | none => false

theorem entIn_of_box (a : Part) : BoxGives (entIn own a) (boxIn own a) := by
  intro t R C h x ht hr hc
  unfold boxIn at h
  unfold entIn
  rw [ht]
  cases e : arrayIn own a t with
  | none =>
    rw [e] at h
    exact nomatch h
  | some A =>
    rw [e] at h
    have h' : (decide (R ≤ A.sizeI) && decide (C ≤ A.sizeC)) = true := h
    obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h'
    show (decide (x.row < A.sizeI) && decide (x.idx < A.sizeC)) = true
    exact Eq.mpr (Bool.and_eq_true _ _)
      ⟨decide_eq_true (Nat.lt_of_lt_of_le hr (of_decide_eq_true h1)),
       decide_eq_true (Nat.lt_of_lt_of_le hc (of_decide_eq_true h2))⟩

/-- The array is there, or ahead, and has at least R rows and C columns. -/
def boxInA (a : Part) (t R C : Nat) : Bool :=
  boxIn own a t R C ||
    match (a.L.arrayOf[t]?).bind (aheadIn sent own a) with
    | some h => decide (R ≤ h.A.sizeI) && decide (C ≤ h.A.sizeC)
    | none => false

theorem entInA_of_box (a : Part) : BoxGives (entInA sent own a) (boxInA sent own a) := by
  intro t R C h x ht hr hc
  unfold boxInA at h
  rcases Eq.mp (Bool.or_eq_true _ _) h with h | h
  · exact entInA_of_entIn sent own a x (entIn_of_box own a t R C h x ht hr hc)
  · unfold entInA
    refine Eq.mpr (Bool.or_eq_true _ _) (Or.inr ?_)
    rw [ht]
    cases e : (a.L.arrayOf[t]?).bind (aheadIn sent own a) with
    | none =>
      rw [e] at h
      exact nomatch h
    | some q =>
      rw [e] at h
      have h' : (decide (R ≤ q.A.sizeI) && decide (C ≤ q.A.sizeC)) = true := h
      obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h'
      show (decide (x.row < q.A.sizeI) && decide (x.idx < q.A.sizeC)) = true
      exact Eq.mpr (Bool.and_eq_true _ _)
        ⟨decide_eq_true (Nat.lt_of_lt_of_le hr (of_decide_eq_true h1)),
         decide_eq_true (Nat.lt_of_lt_of_le hc (of_decide_eq_true h2))⟩

/-- **The public test at the reader of the single equations, at what is there.** -/
theorem formsIn_of_smallFits (H : LinkHoles) (l : Link S Claim) (b : Nat) (s : S) (a : Part)
    (tl : HTailF2) (funs : Array HFun) (ha : segAt? s = some a) (ht : s.tl? = some tl)
    (hf : s.funs? = some funs) (h : smallFits (boxIn own a) tl funs = true) :
    formsIn (readersOfLink (withSmall H) l) own b "K8.equations" s = true := by
  rw [formsIn_small H l own b s a tl funs ha ht hf]
  exact allForms_of_smallFits (entIn own a) (boxIn own a) (slotIn own (mergeOf s) [] a)
    (entIn_of_box own a) tl funs h

/-- **And at what is there or ahead.** -/
theorem formsInA_of_smallFits (H : LinkHoles) (l : Link S Claim) (b : Nat) (s : S) (a : Part)
    (tl : HTailF2) (funs : Array HFun) (ha : segAt? s = some a) (ht : s.tl? = some tl)
    (hf : s.funs? = some funs) (h : smallFits (boxInA sent own a) tl funs = true) :
    formsInA (readersOfLink (withSmall H) l) sent own b "K8.equations" s = true := by
  unfold formsInA
  rw [forms_small, ha]
  unfold smallReader
  rw [ht, hf]
  show (lateOk [] a && (TailClaims.rowsAff tl funs).all fun f =>
    affInA sent own (mergeOf s) [] a f) = true
  rw [TailClaims.rowsAff_all]
  exact allForms_of_smallFits (entInA sent own a) (boxInA sent own a)
    (slotIn own (mergeOf s) [] a) (entInA_of_box sent own a) tl funs h

end

end VerifiableInference.Desc.K9

#print axioms VerifiableInference.Desc.K9.tie_in
#print axioms VerifiableInference.Desc.K9.read_in
#print axioms VerifiableInference.Desc.K9.allForms_of_smallFits
#print axioms VerifiableInference.Desc.K9.entIn_of_box
#print axioms VerifiableInference.Desc.K9.entInA_of_box
#print axioms VerifiableInference.Desc.K9.formsIn_of_smallFits
#print axioms VerifiableInference.Desc.K9.formsInA_of_smallFits
