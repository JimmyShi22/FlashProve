-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/ReqRefGlueS.lean: the sums among the atoms of a glued family (`Fam.glue`, Cb/Req/ReqGlue.lean):
their sizes, their number and their further variables.

Generic lemmas on data; no model, no protocol. A family (`Fam`, Cb/Req/ReqSpec.lean) is a sum of
terms over numbered atoms; an atom `Atom.sum w P` is a sum over w further variables. Gluing joins a
list of families, the members, into one. `sS f`, `lS f`: the sizes (`sz`, Cm/ReqRefNeed.lean) of the
sums among the atoms of f, added up; their number. `WLe f Wm`: none has more than Wm further
variables.

Main names:
  `sumsN_to`, `sumsN_mask`, `sumsN_pub`, `sumsN_add`: the steps of gluing put the members' sums side
    by side, each on more variables (`Poly0.to`), which changes neither its number w of further
    variables nor its size.
  `sS_glue`, `lS_glue`: `sS` and `lS` of a glued family are the members' `sS` and `lS` added up.
  `WLe_glue`: if every member has `WLe f Wm`, so has the glued family.
-/
import Cm.ReqRefNeed
import Ior.Frame

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Cm.Ref
open Cb Cb.Req

section
variable {X E : Type}

/-- the sum that an atom is, if it is one -/
def asSum : Atom X E → Option (ℕ × Poly0 X E)
  | .sum w P => some (w, P)
  | _ => none

/-- the sums among the atoms below f.na -/
def sumsN (f : Fam X E) : List (ℕ × Poly0 X E) :=
  (List.range f.na).filterMap fun j => asSum (f.atom j)

theorem asSum_to (N v : ℕ) (a : Atom X E) :
    asSum (a.to N v) = (asSum a).map fun b => (b.1, b.2.to (N + b.1)) := by
  cases a <;> rfl

theorem sumsN_to (f : Fam X E) (N : ℕ) :
    sumsN (f.to N) = (sumsN f).map fun b => (b.1, b.2.to (N + b.1)) := by
  unfold sumsN
  rw [List.map_filterMap]
  exact congrArg (fun φ => List.filterMap φ (List.range f.na))
    (funext fun j => asSum_to N f.v (f.atom j))

theorem sumsN_mask [Mul E] (c : X → ℕ → E) (f : Fam X E) : sumsN (f.mask c) = sumsN f := rfl

theorem sumsN_pub [Zero E] (v : ℕ) (c : X → ℕ → E) : sumsN (Fam.pub v c) = [] := rfl

theorem sumsN_add (f g : Fam X E) : sumsN (f.add g) = sumsN f ++ sumsN g := by
  unfold sumsN
  show List.filterMap _ (List.range (f.na + g.na)) = _
  rw [List.range_add, List.filterMap_append, List.filterMap_map]
  congr 1
  · refine List.filterMap_congr fun j hj => ?_
    show asSum (if j < f.na then f.atom j else g.atom (j - f.na)) = _
    rw [if_pos (List.mem_range.1 hj)]
  · refine List.filterMap_congr fun j _ => ?_
    show asSum (if f.na + j < f.na then f.atom (f.na + j) else g.atom (f.na + j - f.na)) = _
    rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem sz_toFam_to (P : Poly0 X E) (M : ℕ) : sz (P.to M).toFam = sz P.toFam := by
  unfold sz Fam.lists Poly0.toFam Poly0.to
  simp only [List.map_map]
  rfl

/-- `sS`: the sizes of the sums together; `lS`: their number; `WLe f Wm`: no sum has more than Wm
further variables -/
def sS (f : Fam X E) : ℕ := ((sumsN f).map fun a => sz a.2.toFam).sum
def lS (f : Fam X E) : ℕ := (sumsN f).length
def WLe (f : Fam X E) (Wm : ℕ) : Prop := ∀ a ∈ sumsN f, a.1 ≤ Wm

theorem sS_to (f : Fam X E) (N : ℕ) : sS (f.to N) = sS f := by
  unfold sS
  rw [sumsN_to, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun a _ => sz_toFam_to a.2 _)
theorem lS_to (f : Fam X E) (N : ℕ) : lS (f.to N) = lS f := by
  unfold lS
  rw [sumsN_to, List.length_map]
theorem WLe_to {f : Fam X E} {Wm : ℕ} (h : WLe f Wm) (N : ℕ) : WLe (f.to N) Wm := fun a ha => by
  rw [sumsN_to] at ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
  exact h b hb
theorem sS_add (f g : Fam X E) : sS (f.add g) = sS f + sS g := by
  unfold sS
  rw [sumsN_add, List.map_append, List.sum_append]
theorem lS_add (f g : Fam X E) : lS (f.add g) = lS f + lS g := by
  unfold lS
  rw [sumsN_add, List.length_append]
theorem WLe_add {f g : Fam X E} {Wm : ℕ} (hf : WLe f Wm) (hg : WLe g Wm) :
    WLe (f.add g) Wm := fun a ha => by
  rw [sumsN_add, List.mem_append] at ha
  exact ha.elim (hf a) (hg a)

variable [Zero E] [One E] [Mul E]

theorem sS_glueFrom (N V : ℕ) :
    ∀ (L : List (Fam X E)) (i : ℕ), sS (glueFrom N V i L) = (L.map sS).sum
  | [], _ => rfl
  | f :: L, i => by
    show sS (Fam.add (Fam.mask _ (f.to N)) (glueFrom N V (i + 1) L)) = sS f + (L.map sS).sum
    rw [sS_add, sS_glueFrom N V L (i + 1)]
    exact congrArg (· + _) (sS_to f N)
theorem lS_glueFrom (N V : ℕ) :
    ∀ (L : List (Fam X E)) (i : ℕ), lS (glueFrom N V i L) = (L.map lS).sum
  | [], _ => rfl
  | f :: L, i => by
    show lS (Fam.add (Fam.mask _ (f.to N)) (glueFrom N V (i + 1) L)) = lS f + (L.map lS).sum
    rw [lS_add, lS_glueFrom N V L (i + 1)]
    exact congrArg (· + _) (lS_to f N)
theorem WLe_glueFrom (N V : ℕ) {Wm : ℕ} :
    ∀ (L : List (Fam X E)) (i : ℕ), (∀ f ∈ L, WLe f Wm) → WLe (glueFrom N V i L) Wm
  | [], _, _ => fun _ h => absurd h List.not_mem_nil
  | f :: L, i, h =>
    WLe_add (WLe_to (h f List.mem_cons_self) N)
      (WLe_glueFrom N V L (i + 1) fun g hg => h g (List.mem_cons_of_mem _ hg))

theorem sS_glue (pad : E) (L : List (Fam X E)) : sS (Fam.glue pad L) = (L.map sS).sum := by
  unfold Fam.glue
  rw [sS_add, sS_glueFrom]
  exact Nat.zero_add _
theorem lS_glue (pad : E) (L : List (Fam X E)) : lS (Fam.glue pad L) = (L.map lS).sum := by
  unfold Fam.glue
  rw [lS_add, lS_glueFrom]
  exact Nat.zero_add _
theorem WLe_glue (pad : E) {L : List (Fam X E)} {Wm : ℕ} (h : ∀ f ∈ L, WLe f Wm) :
    WLe (Fam.glue pad L) Wm :=
  WLe_add (fun _ ha => absurd ha List.not_mem_nil) (WLe_glueFrom _ _ L 0 h)

end

end Cm.Ref
