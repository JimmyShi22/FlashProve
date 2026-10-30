-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Tab/TabGLaw.lean:
the reader of a group's keys and bits off tables is the filling's own. Theorems without a
hypothesis, and definitions with code.

Terms. Honest/K3/GLOSSARY.md; Honest/K3/Tab/TabG.lean.

What is shown.
  `Ok1` to `Ok5` (definitions) with their lemmas: an array, to a depth of five, at which `Memo.read`
    is the function: the empty array; a table of such arrays (`h` in `ok2_tab` to `ok5_tab`: each of
    the arrays is one of the depth below).
  `tenTab_ok`, `tensTab_ok`, `suTab_ok`, `w0Tab_ok`, `w2Tab_ok`, `w3Tab_ok`, `colTab_ok`: each table
    of Honest/K3/Tab/TabG.lean is one. `colTab_read`: so `colG` read off its table is `colG`.
  `innerTab_is`: the values of the rows off the five tables are the library's own factors
    (`Inner.Is`, Honest/K3/Tab/SisterG.lean).
  `layersTab_eq`: the main theorem: `layersTab X g C W` is the field `layers` of `ownSources` at g,
    C, W.
  `tabSourcesG_eq`, `sourcesAtTabG_eq`, `tabWitG_eq`: so the letters with that one field exchanged
    are `ownSourcesBound`, `sourcesAtBound`, and the reader at a site is `boundWit`
    (Honest/K3/WitBound.lean).

What is defined. `tabSourcesG`, `sourcesAtTabG`, `tabWitG`: `ownSourcesBound`, `sourcesAtBound` and
`boundWit` with the layers' field off tables. The other three sorts of lookup are as they were.

Imported. Honest/K3/Tab/TabG.lean, Honest/K3/WitBound.lean.

Users. Honest/K3/Tab/LotTabG.lean, Honest/K3/Tab/TabAllLaw.lean [not in this library],
Honest/K3/Tab/TabAll2Law.lean, Honest/K3/Tab/TabGToy.lean [not in this library] and
Honest/K3/Tab/TabHLaw.lean import this file.

Limits. The equations say that the terms are equal, not how long either takes. Of the 24 theorems 13
have a line `#print axioms` in this file; eleven helpers (`getD_nil`, `lookup_ok` and the nine on
`Ok1` to `Ok5`) have none.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Tab.TabG
import Johnson.Desc.ProofFile.Honest.K3.WitBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.TabG
open OnBytes.Model OnBytes.Ends.G
open ProofFile.Honest.K3.Memo (read tab read_tab read_empty getD_tab)

/-! ## 1 Arrays at which `read` is the function -/

section Ok

variable {α : Type}

def Ok1 (a : Array α) (f : ℕ → α) : Prop := ∀ i, read a f i = f i
def Ok2 (a : Array (Array α)) (f : ℕ → ℕ → α) : Prop := ∀ i, Ok1 (a.getD i #[]) (f i)
def Ok3 (a : Array (Array (Array α))) (f : ℕ → ℕ → ℕ → α) : Prop := ∀ i, Ok2 (a.getD i #[]) (f i)
def Ok4 (a : Array (Array (Array (Array α)))) (f : ℕ → ℕ → ℕ → ℕ → α) : Prop :=
  ∀ i, Ok3 (a.getD i #[]) (f i)
def Ok5 (a : Array (Array (Array (Array (Array α))))) (f : ℕ → ℕ → ℕ → ℕ → ℕ → α) : Prop :=
  ∀ i, Ok4 (a.getD i #[]) (f i)

theorem getD_nil {β : Type} (i : ℕ) (d : β) : (#[] : Array β).getD i d = d := by
  simp [Array.getD]

theorem ok1_nil (f : ℕ → α) : Ok1 #[] f := read_empty f
theorem ok1_tab (n : ℕ) (f : ℕ → α) : Ok1 (tab n f) f := read_tab n f

theorem ok2_nil (f : ℕ → ℕ → α) : Ok2 #[] f := fun i => by rw [getD_nil]; exact ok1_nil (f i)
theorem ok2_tab (n : ℕ) (A : ℕ → Array α) (f : ℕ → ℕ → α) (h : ∀ i, Ok1 (A i) (f i)) :
    Ok2 (tab n A) f := fun i => by
  rw [getD_tab]
  split_ifs
  · exact h i
  · exact ok1_nil (f i)

theorem ok3_nil (f : ℕ → ℕ → ℕ → α) : Ok3 #[] f := fun i => by rw [getD_nil]; exact ok2_nil (f i)
theorem ok3_tab (n : ℕ) (A : ℕ → Array (Array α)) (f : ℕ → ℕ → ℕ → α)
    (h : ∀ i, Ok2 (A i) (f i)) : Ok3 (tab n A) f := fun i => by
  rw [getD_tab]
  split_ifs
  · exact h i
  · exact ok2_nil (f i)

theorem ok4_nil (f : ℕ → ℕ → ℕ → ℕ → α) : Ok4 #[] f := fun i => by
  rw [getD_nil]; exact ok3_nil (f i)
theorem ok4_tab (n : ℕ) (A : ℕ → Array (Array (Array α))) (f : ℕ → ℕ → ℕ → ℕ → α)
    (h : ∀ i, Ok3 (A i) (f i)) : Ok4 (tab n A) f := fun i => by
  rw [getD_tab]
  split_ifs
  · exact h i
  · exact ok3_nil (f i)

theorem ok5_tab (n : ℕ) (A : ℕ → Array (Array (Array (Array α)))) (f : ℕ → ℕ → ℕ → ℕ → ℕ → α)
    (h : ∀ i, Ok4 (A i) (f i)) : Ok5 (tab n A) f := fun i => by
  rw [getD_tab]
  split_ifs
  · exact h i
  · exact ok4_nil (f i)

end Ok

/-! ## 2 The tables -/

section Tables

variable {R : Type} [CommRing R] (P : Layer.Pub) (g : ℕ) (cell : NameG → R)

theorem tenTab_ok (n : String) : Ok3 (tenTab P cell n) fun inst i x => ten P cell n inst x i := by
  unfold tenTab
  cases P.y.T_ n with
  | none => exact ok3_nil _
  | some X => exact ok3_tab _ _ _ fun inst => ok2_tab _ _ _ fun i => ok1_tab _ _

theorem lookup_ok (names : List String) (n : String) :
    Ok3 (((names.map fun m => (m, tenTab P cell m)).lookup n).getD #[])
      fun inst i x => ten P cell n inst x i := by
  induction names with
  | nil => exact ok3_nil _
  | cons m ms ih =>
    rw [List.map_cons, List.lookup_cons]
    by_cases h : n = m
    · subst h
      simp only [beq_self_eq_true, Option.getD_some]
      exact tenTab_ok P cell n
    · have h' : (n == m) = false := by simpa using h
      simp only [h']
      exact ih

theorem tensTab_ok (n : String) :
    Ok3 (((tensTab P cell).lookup n).getD #[]) fun inst i x => ten P cell n inst x i :=
  lookup_ok P cell sumNames n

theorem suTab_ok : Ok3 (suTab P cell) fun lam i k => gated P cell lam k i := by
  unfold suTab
  cases P.y.T_ "s" with
  | none => exact ok3_nil _
  | some X => exact ok3_tab _ _ _ fun lam => ok2_tab _ _ _ fun i => ok1_tab _ _

theorem w0Tab_ok :
    Ok4 (w0Tab P g cell) fun lam hd cd k => wt P cell 0 (lOf P g lam) [hd, cd, k] := by
  unfold w0Tab
  refine ok4_tab _ _ _ fun lam => ?_
  cases unitAt P 0 (lOf P g lam) with
  | none => exact ok3_nil _
  | some u => exact ok3_tab _ _ _ fun hd => ok2_tab _ _ _ fun cd => ok1_tab _ _

theorem w2Tab_ok : Ok4 (w2Tab P g cell) fun X lam x k => wt P cell X (lOf P g lam) [k, x] := by
  unfold w2Tab
  refine ok4_tab _ _ _ fun X => ok3_tab _ _ _ fun lam => ?_
  cases unitAt P X (lOf P g lam) with
  | none => exact ok2_nil _
  | some u =>
    show Ok2 (if _ then _ else _) _
    split_ifs
    · exact ok2_tab _ _ _ fun x => ok1_tab _ _
    · exact ok2_nil _

theorem w3Tab_ok :
    Ok5 (w3Tab P g cell) fun X lam e x k => wt P cell X (lOf P g lam) [k, e, x] := by
  unfold w3Tab
  refine ok5_tab _ _ _ fun X => ok4_tab _ _ _ fun lam => ?_
  cases unitAt P X (lOf P g lam) with
  | none => exact ok3_nil _
  | some u =>
    dsimp only
    split_ifs
    · exact ok3_tab _ _ _ fun e => ok2_tab _ _ _ fun x => ok1_tab _ _
    · exact ok3_nil _

theorem colTab_ok : Ok2 (colTab P) (colG P.y) :=
  ok2_tab _ _ _ fun _ => ok1_tab _ _

/-- Read off its table, `colG` is `colG`. -/
theorem colTab_read : Memo.read2 (colTab P) (colG P.y) = colG P.y :=
  funext fun q => funext fun j => colTab_ok P q j

/-- **The values of the rows off the five tables are the library's own factors.** -/
theorem innerTab_is :
    (innerTab P g cell (tensTab P cell) (suTab P cell) (w0Tab P g cell) (w2Tab P g cell)
      (w3Tab P g cell)).Is P g cell :=
  ⟨fun n inst i x => tensTab_ok P cell n inst i x, fun lam i k => suTab_ok P cell lam i k,
   fun lam hd cd k => w0Tab_ok P g cell lam hd cd k, fun X lam x k => w2Tab_ok P g cell X lam x k,
   fun X lam e x k => w3Tab_ok P g cell X lam e x k⟩

end Tables

/-! ## 3 The reader -/

/-- **The reader off tables is the filling's own.** -/
theorem layersTab_eq {W₀ Xi Tr : Type} (X : OnBytes.Model.Verify.Public) (cells : Tr → Cells)
    (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) (g : ℕ) (C : Cells) (W : Weights) :
    layersTab X g C W = (ownSources X cells weights pubH).layers g C W := by
  have h : ∀ sn lam x i,
      affG X.layers g (ownG X C.cell W.entry (linkG X g)) sn lam x i +
        algebraMap Cb.Gl.F Cb.Gl.E
          (gamGBy X.layers g (ownGF X C.cell W.entry (linkG X g))
            (innerTab X.layers g (ownGF X C.cell W.entry (linkG X g))
              (tensTab X.layers (ownGF X C.cell W.entry (linkG X g)))
              (suTab X.layers (ownGF X C.cell W.entry (linkG X g)))
              (w0Tab X.layers g (ownGF X C.cell W.entry (linkG X g)))
              (w2Tab X.layers g (ownGF X C.cell W.entry (linkG X g)))
              (w3Tab X.layers g (ownGF X C.cell W.entry (linkG X g)))) sn lam x i) =
      segG X.layers g (ownG X C.cell W.entry (linkG X g)) sn lam x i := by
    intro sn lam x i
    rw [gamGBy_of (innerTab_is _ _ _), ← gamG_own]
    rfl
  unfold layersTab
  simp only [h, colTab_read]
  rfl

variable {W₀ Rc Xi Tr : Type}

/-- `ownSourcesBound` with the layers' field off tables. -/
def tabSourcesG (X : OnBytes.Model.Verify.Public) (cells : Tr → Cells)
    (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) : Sources W₀ Xi Tr :=
  { ownSourcesBound X cells weights pubH with layers := layersTab X }

theorem tabSourcesG_eq (X : OnBytes.Model.Verify.Public) (cells : Tr → Cells)
    (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) :
    tabSourcesG X cells weights pubH = ownSourcesBound X cells weights pubH := by
  have h : layersTab X = (ownSourcesBound X cells weights pubH).layers := by
    funext g C W
    exact layersTab_eq X cells weights pubH g C W
  unfold tabSourcesG
  rw [h]

/-- `sourcesAtBound` over it. -/
def sourcesAtTabG (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) : Sources W₀ Xi Tr :=
  tabSourcesG Z.p.X cells weights fun x =>
    let q := req x
    headPub Z.p.X q.1 q.2

theorem sourcesAtTabG_eq (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) :
    sourcesAtTabG cells weights req Z = sourcesAtBound cells weights req Z :=
  tabSourcesG_eq Z.p.X cells weights _

/-- `boundWit` over it: the reader of the input at a site, the layers' calls off tables. -/
def tabWitG (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (s : Site) :
    Local W₀ Rc Xi Tr → Ask :=
  match s.rng with
  | some r => fun t heard => fastAsk Z.p.X s.link r (cells t.trace) heard
  | none => (fastFill (Rc := Rc) (sourcesAtTabG cells weights req Z)).wit s

/-- **It is `boundWit`, at every site.** -/
theorem tabWitG_eq (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (s : Site) :
    tabWitG (Rc := Rc) cells weights req Z s = boundWit cells weights req Z s := by
  unfold tabWitG boundWit
  rw [sourcesAtTabG_eq]
  rfl

end ProofFile.Honest.K3.TabG

#print axioms ProofFile.Honest.K3.TabG.tenTab_ok
#print axioms ProofFile.Honest.K3.TabG.tensTab_ok
#print axioms ProofFile.Honest.K3.TabG.suTab_ok
#print axioms ProofFile.Honest.K3.TabG.w0Tab_ok
#print axioms ProofFile.Honest.K3.TabG.w2Tab_ok
#print axioms ProofFile.Honest.K3.TabG.w3Tab_ok
#print axioms ProofFile.Honest.K3.TabG.colTab_ok
#print axioms ProofFile.Honest.K3.TabG.colTab_read
#print axioms ProofFile.Honest.K3.TabG.innerTab_is
#print axioms ProofFile.Honest.K3.TabG.layersTab_eq
#print axioms ProofFile.Honest.K3.TabG.tabSourcesG_eq
#print axioms ProofFile.Honest.K3.TabG.sourcesAtTabG_eq
#print axioms ProofFile.Honest.K3.TabG.tabWitG_eq
