-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/DoorMkRow.lean: THE MAKE OF THE ONE EQUATION's ROW, WHOLE, AND WHAT
THE DOOR DOES TO THE MAKES OF THE STATEMENT's ROWS (formsOf, Johnson/Desc/First/Shape/Forms.lean).
Over DoorMk.lean. General laws, FROM A RETURN; nothing is evaluated.

  `rowTermsS`, `rowTerms_mk`: the terms of one virtual row, without their weights: one where the row
    has a product form; else one for each row of the array. All of one make.
  **`termsShS`**, **`allTerms_mk`**: the terms on the listed arrays, off the link's table of arrays,
    the number of listed arrays and the arrays' shapes.
  **`eqMk`**, **`asRow_mk`**: the row's make: a plain row; no term on a tensor; no single entry; one
    run on the link's mask row where there are slots; the terms' forms.
  `takeN_forms`: taking mask entries turns no row's make.
  **`door_forms`**: K9.door … d = .ok o: the makes behind are those in front with the row's make
    behind the open rows of the link's group.

Limits. From a return alone. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Batch.Shape.DoorMk
import Johnson.Desc.First.Batch.Shape.DoorFits
import Johnson.Desc.First.Shape.Forms
import Johnson.Desc.First.Shape.Parts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open OnBytes.Params (ReqLayout)
open VerifiableInference.Desc.First.Shape

/-! ## 1 The terms, without their weights -/

/-- The terms of one virtual row. R: the array's number of rows. -/
def rowTermsS (born : Nat) (array : String) (R : Nat) (r : RowSh) : List TermSh :=
  List.replicate (if r.form then 1 else R) ⟨born, array, none, some r.entries⟩

theorem values_of {w : IndexWeights} {a b : Nat} (h : wSh w = ⟨a, b, none⟩) :
    w.values.map (·.size) = none := congrArg WSh.values h

theorem rowTerms_mk (born : Nat) (array : String) (X : HTree) (r : HRow)
    (acc acc' : Array ReqTerm) (h : rowTerms born array X acc r = .ok acc') :
    acc'.toList.map termShOf = acc.toList.map termShOf ++ rowTermsS born array X.R (rowSh r) := by
  unfold rowTerms at h
  simp only [ans_bind, need_ok, exists_const] at h
  obtain ⟨-, h⟩ := h
  unfold rowTermsS
  show _ = _ ++ List.replicate (if r.rowForm then 1 else X.R)
    (⟨born, array, none, some r.L.size⟩ : TermSh)
  by_cases hf : r.rowForm = true
  · rw [if_pos hf] at h
    rw [if_pos hf]
    simp only [ans_bind] at h
    obtain ⟨w, hw, e⟩ := h
    obtain rfl := Except.ok.inj e
    have ew : w = rowProduct X r := by
      unfold rowWeights at hw
      simp only [ans_bind, need_ok, exists_const] at hw
      exact (Except.ok.inj hw.2.2).symm
    rw [Array.toList_push, List.map_append]
    congr 1
    show [TermSh.mk born array (w.values.map (·.size)) (some r.L.size)] = _
    rw [ew, values_of (wSh_product X r)]
    rfl
  · rw [if_neg hf] at h
    rw [if_neg hf]
    obtain rfl := Except.ok.inj h
    rw [foldl_push_map, List.map_append, List.map_map]
    congr 1
    rw [List.map_congr_left (g := fun _ => (⟨born, array, none, some r.L.size⟩ : TermSh))
      fun i _ => by
        show TermSh.mk born array ((pickIndex (clog2 X.R) i).values.map (·.size))
          (some r.L.size) = _
        rw [values_of (wSh_pick _ i)]]
    simp

/-- The terms on the listed arrays. -/
def termsShS (arrayOf : Array (Nat × String)) (n : Nat) (trees : List TreeSh) : List TermSh :=
  (List.range n).flatMap fun ti =>
    (trees.getD ti (treeSh {})).rows.flatMap
      (rowTermsS (arrayOf.getD ti (0, "")).1 (arrayOf.getD ti (0, "")).2
        (trees.getD ti (treeSh {})).R)

theorem rows_mk (born : Nat) (array : String) (X : HTree) :
    ∀ (rows : List HRow) (acc acc' : Array ReqTerm),
      rows.foldlM (rowTerms born array X) acc = .ok acc' →
      acc'.toList.map termShOf =
        acc.toList.map termShOf ++ (rows.map rowSh).flatMap (rowTermsS born array X.R)
  | [], acc, acc', h => by
    obtain rfl : acc = acc' := Except.ok.inj h
    simp
  | r :: rows, acc, acc', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨a₁, h1, h2⟩ := (ans_bind _ _ _).1 h
    rw [rows_mk born array X rows a₁ acc' h2, rowTerms_mk born array X r acc a₁ h1,
      List.map_cons, List.flatMap_cons, List.append_assoc]

theorem treeD_sh (trees : Array HTree) (ti : Nat) :
    (trees.toList.map treeSh).getD ti (treeSh {}) = treeSh (trees.getD ti {}) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList]
  by_cases h : ti < trees.size <;> simp [Array.getD, h]

theorem allTerms_mk (L : LinkCtx) (F : Fork) (terms : Array ReqTerm)
    (h : allTerms L F = .ok terms) :
    terms.toList.map termShOf =
      termsShS L.arrayOf L.list.nt.size (F.trees.toList.map treeSh) := by
  unfold allTerms at h
  unfold termsShS
  have key : ∀ (l : List Nat) (acc acc' : Array ReqTerm),
      l.foldlM (fun (terms : Array ReqTerm) ti => do
        let (born, array) := L.arrayOf.getD ti (0, "")
        let X := F.trees.getD ti {}
        need "K9.array-laid" (arrayLaid L.check.rows.layout born array X.R X.K)
        X.rows.foldlM (rowTerms born array X) terms) acc = .ok acc' →
      acc'.toList.map termShOf = acc.toList.map termShOf ++ l.flatMap fun ti =>
        ((F.trees.toList.map treeSh).getD ti (treeSh {})).rows.flatMap
          (rowTermsS (L.arrayOf.getD ti (0, "")).1 (L.arrayOf.getD ti (0, "")).2
            ((F.trees.toList.map treeSh).getD ti (treeSh {})).R) := by
    intro l
    induction l with
    | nil =>
      intro acc acc' h
      obtain rfl : acc = acc' := Except.ok.inj h
      simp
    | cons ti l ih =>
      intro acc acc' h
      rw [List.foldlM_cons] at h
      obtain ⟨a₁, h1, h2⟩ := (ans_bind _ _ _).1 h
      simp only [ans_bind, need_ok, exists_const] at h1
      obtain ⟨-, h1⟩ := h1
      rw [← Array.foldlM_toList] at h1
      rw [ih a₁ acc' h2, rows_mk _ _ _ _ acc a₁ h1, List.flatMap_cons, List.append_assoc, treeD_sh]
      rfl
  have := key _ #[] terms h
  simpa using this

/-! ## 2 The row's make -/

/-- **THE MAKE OF THE ONE EQUATION's ROW.** n: the number of coefficients on the mask row. -/
def eqMk (layout : ReqLayout) (f : ReqFrame) (rb pb : Nat → Nat) (ts : List TermSh) (n : Nat) :
    Option RowMk :=
  (termsMk layout f rb pb ts []).bind fun forms =>
    if n == 0 then some ⟨.plain, [], [], [], forms⟩
    else (maskAt f).map fun o => ⟨.plain, [], [], [⟨o, .mask, 0, 1, n⟩], forms⟩

variable {X : Type}

theorem asRow_mk (R : ReqRows) (f : ReqFrame) (q : Equation) (d : St X) (y : OnBytes.Row × St X)
    (h : asRow R f q d = .ok y) :
    eqMk R.layout f (d.st.rowBits · .main) (d.st.placeBits · .main) (q.terms.toList.map termShOf)
      q.onMasks.size = some (rowMk y.1) := by
  obtain ⟨row, hr, hc⟩ := (asRow_iff _ _ _ _ _).1 h
  obtain ⟨r1, r2, r3, r4, r5⟩ := termsRow_mk _ _ _ _ _ _ hr
  have r1' : termsMk R.layout f (d.st.rowBits · .main) (d.st.placeBits · .main)
      (q.terms.toList.map termShOf) [] = some (rowMk row).forms := r1
  have e0 : rowMk row = ⟨.plain, [], [], [], (rowMk row).forms⟩ := by
    have a2 : (rowMk row).kind = .plain := r2
    have a3 : (rowMk row).terms = [] := r3
    have a4 : (rowMk row).units = [] := r4
    have a5 : (rowMk row).runs = [] := r5
    cases hm : rowMk row with
    | mk k t u w fo =>
      rw [hm] at a2 a3 a4 a5
      dsimp only at a2 a3 a4 a5
      rw [a2, a3, a4, a5]
  unfold eqMk
  rw [r1']
  show (if q.onMasks.size == 0 then some _ else _) = _
  rcases hc with ⟨he, rfl⟩ | ⟨he, o, x, hm, -, -, rfl⟩
  · rw [empty_iff] at he
    rw [if_pos he]
    exact congrArg some e0.symm
  · rw [empty_iff] at he
    rw [if_neg (by rw [he]; exact Bool.false_ne_true), hm]
    show some _ = some (rowMk (row.addRun o .mask 0 1 (.own q.onMasks)))
    congr 1
    show _ = RowMk.mk row.kind (row.terms.toList.map termMk) (row.units.toList.map unitMk)
      ((row.runs.push ⟨o, .mask, 0, 1, .own q.onMasks⟩).toList.map runMk)
      (row.forms.toList.map mainMk)
    have a2 : row.kind = .plain := r2
    have a3 : row.terms.toList.map termMk = [] := r3
    have a4 : row.units.toList.map unitMk = [] := r4
    have a5 : row.runs.toList.map runMk = [] := r5
    rw [a2, a3, a4, Array.toList_push, List.map_append, a5]
    rfl

/-! ## 3 The door, on the makes -/

theorem takeN_forms (o : Nat) : ∀ (n : Nat) (d : St X) (acc : List Nat) (y : List Nat × St X),
    takeN o n d acc = .ok y → formsOf y.2.st = formsOf d.st
  | 0, d, acc, y, h => by
    obtain rfl : (acc.reverse, d) = y := Except.ok.inj h
    rfl
  | n + 1, d, acc, y, h => by
    have h' : (there "K9.mask-entry-free" (Ground.takeMaskP d o) >>= fun x =>
      takeN o n x.2 (x.1 :: acc)) = .ok y := h
    obtain ⟨x, hx, hy⟩ := (ans_bind _ _ _).1 h'
    rw [takeN_forms o n x.2 _ y hy, takeMask_forms ((there_ok _ _ _).1 hx)]

/-- **WHAT THE DOOR DOES TO THE MAKES.** -/
theorem door_forms (owed : RowsOwed) (laid : Option Nat) (L : LinkCtx) (F : Fork) (d : St X)
    (o : Out X) (h : door owed laid L F d = .ok o) :
    ∃ mk, eqMk L.check.rows.layout L.check.frame (d.st.rowBits · .main) (d.st.placeBits · .main)
        (termsShS L.arrayOf L.list.nt.size (F.trees.toList.map treeSh)) F.ns = some mk ∧
      formsOf o.d.st = { formsOf d.st with
        groups := Ground.Sh.modAt (formsOf d.st).groups L.check.group (· ++ [mk]) } := by
  obtain ⟨n, q, F', y, d', -, hq, -, hy, hd, rfl⟩ := (door_iff _ _ _ _ _ _).1 h
  obtain ⟨-, -, -, terms, mc, ht, -, eq⟩ := (equation_iff L F F' q).1 hq
  have hs := equation_size L F F' q hq
  have hm := asRow_mk _ _ _ _ _ hy
  have et : q.terms = terms := by rw [eq]
  rw [et, allTerms_mk L _ terms ht, hs] at hm
  refine ⟨rowMk y.1, hm, ?_⟩
  have e1 : formsOf y.2.st = formsOf d.st := by
    obtain ⟨row, -, hc⟩ := (asRow_iff _ _ _ _ _).1 hy
    rcases hc with ⟨-, rfl⟩ | ⟨-, m, x, -, hx, -, rfl⟩
    · rfl
    · exact takeN_forms m _ d [] x hx
  show formsOf d'.st = _
  rw [addRow_forms hd, e1]

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.asRow_mk
#print axioms VerifiableInference.Desc.K9.Shape.door_forms
#print axioms VerifiableInference.Desc.K9.Shape.rowTerms_mk
#print axioms VerifiableInference.Desc.K9.Shape.allTerms_mk
