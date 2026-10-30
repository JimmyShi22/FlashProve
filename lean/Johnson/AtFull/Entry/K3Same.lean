-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Entry/K3Same.lean: when two places of a lookup, or two structures of a segment's
approximate range proof, are one after narrowing (`narrowP`, `narrowT`, `narrowC`, `narrowM`:
Johnson/AtFull/ProofRows/K3Views.lean). For each narrowing a view: a short tuple of strings and
lists, on which equality can be decided; and the law that equal views give equal narrowed terms.
Nine definitions with code and eleven laws. No goal is stated.
Why. The rows 11 to 13 of the proof file's entry tests say yes at the full size under equations
"what the public part holds, narrowed, is the written value" (Johnson/AtFull/ProofRows/K3Rows.lean).
A place and a structure hold ledgers and tables, and Lean has no decision of equality for them. A
view has one, and Lean's kernel can evaluate it.
  `callV`, `pieceV`: all ten fields of a call, of a piece. `callV_inj`, `pieceV_inj`: they determine
    it. `array_of_map`: two arrays are one where the lists of their members' views are.
  `viewP`, `viewT`, `viewC`, `viewM`: what each narrowing keeps. `decCallV`, `decP`, `decT`: the
    decisions of equality on the three deep views, laid by hand out of Lean's own for pairs and
    lists.
  **`narrowP_of_view`**, **`narrowT_of_view`**, **`narrowC_of_view`**, **`narrowM_of_view`**: equal
    views give equal narrowed terms (at `narrowT` with the field f9 laid empty on both sides, as
    K3Rows.lean asks it).
  `narrowP_pFull`, `narrowT_tFull`, `narrowC_cFull`, `narrowM_mFull`: the written values
    (Johnson/AtFull/ProofRows/K3Full.lean) are narrowed already.
Limits. General laws and four small facts on written values: NOTHING IS SAID OF ANY PUBLIC PART.
Nothing on soundness, on a binding of the commitment (the opening form, `BindsWith`), on correctness
of extraction, on completeness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.AtFull.ProofRows.K3Full

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Entry
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (Place)
open Johnson.AtFull.ProofRows.K3

/-- All ten fields of a call. -/
def callV (c : Call) : String × List Nat × Option (Array UInt64) × Array Nat ×
    List (List (Nat × Nat)) :=
  (c.name, [c.n, c.iota, c.k, c.kappa, c.fn, c.t0], c.tau, c.pub, c.heavy)

theorem callV_inj {a b : Call} (h : callV a = callV b) : a = b := by
  cases a
  cases b
  simp only [callV, Prod.mk.injEq, List.cons.injEq, and_true] at h
  obtain ⟨h1, ⟨h2, h3, h4, h5, h6, h7⟩, h8, h9, h10⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rfl

/-- All ten fields of a piece. -/
def pieceV (p : Piece) : List Nat :=
  [p.tree, p.row, p.r0, p.Rp, p.c0, p.Cp, p.CP, p.off, p.a, p.b]

theorem pieceV_inj {a b : Piece} (h : pieceV a = pieceV b) : a = b := by
  cases a
  cases b
  simp only [pieceV, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rfl

/-- Two arrays are one where the lists of their members' views are. -/
theorem array_of_map {α β : Type} {f : α → β} (hf : ∀ a b, f a = f b → a = b) {x y : Array α}
    (h : x.toList.map f = y.toList.map f) : x = y := by
  have e : x.toList = y.toList := List.map_injective_iff.2 (fun a b => hf a b) h
  exact Array.toList_inj.1 e

/-- What `narrowP` keeps of a place. -/
def viewP (x : Place) : String × List Nat × List (String × List Nat × Option (Array UInt64) ×
    Array Nat × List (List (Nat × Nat))) × Array Nat × List (Nat × Nat) :=
  (x.name, [x.link, x.lid, x.F.next, x.ns, x.lm], x.calls.toList.map callV, x.pub,
    x.base.trees.toList.map (fun T => (T.R, T.K)))

/-- The decision of equality on a call's view, laid by hand out of Lean's own for pairs. (Left to
itself, Lean's search failed on the views of this file; it was seen to find a decision on a tuple of
three members and to find none on one of ten.) -/
def decCallV : DecidableEq (String × List Nat × Option (Array UInt64) × Array Nat ×
    List (List (Nat × Nat))) :=
  @instDecidableEqProd _ _ _ (@instDecidableEqProd _ _ _ (@instDecidableEqProd _ _ _
    (@instDecidableEqProd _ _ _ _)))

/-- The like on a place's view. -/
def decP : DecidableEq (String × List Nat × List (String × List Nat × Option (Array UInt64) ×
    Array Nat × List (List (Nat × Nat))) × Array Nat × List (Nat × Nat)) :=
  @instDecidableEqProd _ _ _ (@instDecidableEqProd _ _ _ (@instDecidableEqProd _ _
    (@instDecidableEqList _ decCallV) (@instDecidableEqProd _ _ _ _)))

/-- **Equal views give equal narrowed places.** -/
theorem narrowP_of_view {x p : Place} (h : viewP x = viewP p) : narrowP x = narrowP p := by
  simp only [viewP, Prod.mk.injEq, List.cons.injEq, and_true] at h
  obtain ⟨h1, ⟨h2, h5, h7, h8, h9⟩, h3, h4, h6⟩ := h
  have hc : x.calls = p.calls := array_of_map (fun _ _ => callV_inj) h3
  have ht : x.base.trees.map narrowTree = p.base.trees.map narrowTree := by
    apply Array.toList_inj.1
    rw [Array.toList_map, Array.toList_map]
    have e : ∀ l : List HTree, l.map narrowTree =
        (l.map fun T => (T.R, T.K)).map fun y => ({ R := y.1, K := y.2 } : HTree) := by
      intro l
      rw [List.map_map]
      rfl
    rw [e, e, h6]
  unfold narrowP
  rw [h1, h2, hc, h4, h5, ht, h7, h8, h9]

/-- What `narrowT` keeps of a structure, f9 apart. -/
def viewT (tl : HTailF2) : List Nat × (String × List Nat × Option (Array UInt64) × Array Nat ×
    List (List (Nat × Nat))) × List (List Nat) × (String × List Nat × Option (Array UInt64) ×
    Array Nat × List (List (Nat × Nat))) × List (List Nat) :=
  ([tl.tau, tl.mz, tl.ix.ZZ, tl.ix.BZ], callV tl.z1.call, tl.z1.pieces.toList.map pieceV,
    callV tl.z2.call, tl.z2.pieces.toList.map pieceV)

/-- The decision of equality on a structure's view, laid by hand. -/
def decT : DecidableEq (List Nat × (String × List Nat × Option (Array UInt64) × Array Nat ×
    List (List (Nat × Nat))) × List (List Nat) × (String × List Nat × Option (Array UInt64) ×
    Array Nat × List (List (Nat × Nat))) × List (List Nat)) :=
  @instDecidableEqProd _ _ _ (@instDecidableEqProd _ _ decCallV (@instDecidableEqProd _ _ _
    (@instDecidableEqProd _ _ decCallV _)))

/-- **Equal views give equal narrowed structures**, f9 laid empty on both sides. -/
theorem narrowT_of_view {a b : HTailF2} (h : viewT a = viewT b) :
    narrowT { a with f9 := {} } = narrowT { b with f9 := {} } := by
  simp only [viewT, Prod.mk.injEq, List.cons.injEq, and_true] at h
  obtain ⟨⟨h1, h2, h7, h8⟩, h3, h4, h5, h6⟩ := h
  have z1 : a.z1 = b.z1 := by
    have c := callV_inj h3
    have p : a.z1.pieces = b.z1.pieces := array_of_map (fun _ _ => pieceV_inj) h4
    cases ha : a.z1
    cases hb : b.z1
    rw [ha, hb] at c p
    simp only at c p
    rw [c, p]
  have z2 : a.z2 = b.z2 := by
    have c := callV_inj h5
    have p : a.z2.pieces = b.z2.pieces := array_of_map (fun _ _ => pieceV_inj) h6
    cases ha : a.z2
    cases hb : b.z2
    rw [ha, hb] at c p
    simp only at c p
    rw [c, p]
  unfold narrowT
  simp only
  rw [h1, h2, z1, z2, h7, h8]

/-- What `narrowC` keeps of a place. -/
def viewC (x : Place) : List Nat :=
  [x.link, x.F.next, x.fs.dT, x.fs.rK, x.fs.kT, x.fs.cK]

theorem narrowC_of_view {x p : Place} (h : viewC x = viewC p) : narrowC x = narrowC p := by
  simp only [viewC, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  unfold narrowC
  rw [h1, h2, h3, h4, h5, h6]

/-- What `narrowM` keeps of a structure. -/
def viewM (tl : HTailF2) : Nat × Array Nat × List (Nat × Nat) :=
  (tl.NM, tl.gtTree, tl.mats.toList.map fun M => (M.m, M.k))

theorem narrowM_of_view {a b : HTailF2} (h : viewM a = viewM b) : narrowM a = narrowM b := by
  simp only [viewM, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hm : (a.mats.map fun M => ({ m := M.m, k := M.k } : TMat)) =
      b.mats.map fun M => ({ m := M.m, k := M.k } : TMat) := by
    apply Array.toList_inj.1
    rw [Array.toList_map, Array.toList_map]
    have e : ∀ l : List TMat, (l.map fun M => ({ m := M.m, k := M.k } : TMat)) =
        (l.map fun M => (M.m, M.k)).map fun y => ({ m := y.1, k := y.2 } : TMat) := by
      intro l
      rw [List.map_map]
      rfl
    rw [e, e, h3]
  unfold narrowM
  rw [h1, h2, hm]

/-- The written places are narrowed already. -/
theorem narrowP_pFull (i : Nat) : narrowP (pFull i) = pFull i := by
  unfold narrowP pFull
  simp only [List.map_toArray, List.map_map]
  rfl

theorem narrowT_tFull (i : Nat) : narrowT { tFull i with f9 := {} } = tFull i := rfl

theorem narrowC_cFull (i : Nat) : narrowC (cFull i) = cFull i := rfl

theorem narrowM_mFull : narrowM mFull = mFull := by
  unfold narrowM mFull
  simp only [List.map_toArray, List.map_cons, List.map_nil]

end Johnson.AtFull.Entry

#print axioms Johnson.AtFull.Entry.callV_inj
#print axioms Johnson.AtFull.Entry.pieceV_inj
#print axioms Johnson.AtFull.Entry.array_of_map
#print axioms Johnson.AtFull.Entry.narrowP_of_view
#print axioms Johnson.AtFull.Entry.narrowT_of_view
#print axioms Johnson.AtFull.Entry.narrowC_of_view
#print axioms Johnson.AtFull.Entry.narrowM_of_view
#print axioms Johnson.AtFull.Entry.narrowP_pFull
#print axioms Johnson.AtFull.Entry.narrowT_tFull
#print axioms Johnson.AtFull.Entry.narrowC_cFull
#print axioms Johnson.AtFull.Entry.narrowM_mFull
