-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tail/ClOf.lean: the last block of a sub-proof's link takes any list of forms for the smallness
test's ties and reads, if these forms give every tie and every read.

`dig_know` (Cb/Pv/Tail/DigBatch.lean) is general in the ledger that is laid, if it gives the ledger
`layD`, whose ties and reads are the forms of Cb/Pv/Tail/Claims.lean. A verifier's own list of the
same equations may be spelled otherwise. Knowledge soundness walks one way: it is enough that the
verifier's forms give the equations.

Main names:
  `cl_of_eqs`: if every tie and every read holds, the claims of Cb/Pv/Tail/Claims.lean hold: the
    converse of `eqs_of_cl`.
  `layR D rows`: the caller's claims, the lookup's end claims, and a list `rows x'` in the place of
    the ties and reads.
  `hlay_rows`: if `rows x'` gives every tie and every read at the digits of the late message,
    `layR` gives `layD`: the premise `hlay` of `dig_know`.
  `hlay_rows_layout`: the same, at one statement, for a ledger that is laid out by exponents and
    has every form of `layR`.

Limits: `rows` is a letter.


Terms: lean/GLOSSARY.md.
-/
import Cb.Pv.Tail.DigBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail
open TWhole

variable {K : Type} [Field K] {s : Size}

/-- If every tie and every read holds, the claims hold. -/
theorem cl_of_eqs (Λ : Letters K s) (e : Exps s) (keep : ∀ μ : Fin s.NM, Fin (s.nr μ) → Bool)
    (x : Λ.X) (β : Dr s) (msg : Λ.M) (Z : Dig K s) (h : Late.Eqs x β msg Z) :
    (cl Λ e keep (x, β)).Holds (vals Λ msg Z) := by
  intro f hf
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hf
  rcases List.mem_append.1 hz with hz | hz
  · obtain ⟨μ, -, hz⟩ := List.mem_flatMap.1 hz
    obtain ⟨u, -, hz⟩ := List.mem_flatMap.1 hz
    obtain ⟨i', -, rfl⟩ := List.mem_map.1 hz
    exact (tie_iff Λ β msg Z μ u i').2 (h.1 μ u i')
  · obtain ⟨μ, -, hz⟩ := List.mem_flatMap.1 hz
    obtain ⟨u, -, hz⟩ := List.mem_flatMap.1 hz
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 hz
    exact (read_iff Λ x β msg Z μ u r).2 (h.2 μ u r)

variable {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] {Q : Host K s J₁ J₂} {U W₀ MM J₃ : Type}
  [Fintype J₃] [DecidableEq J₃] (T : LateU Q.let U W₀) (left : MM → Q.M) (right : MM → U)
  (D : Tail3 Q MM J₃)

/-- The caller's claims, the lookup's end claims, and a list in the place of the ties and reads. -/
def layR (rows : D.X' → Ledger K J₃) (x' : D.X') : Ledger K J₃ :=
  (D.pr x').1.2.map (pushF D.i12) ++ (D.endCl x' ++ rows x')

/-- A list that gives every tie and every read serves in the place of the ties and reads. -/
theorem hlay_rows (rows : D.X' → Ledger K J₃)
    (hs : ∀ m j, D.msg₃ m (D.is j) = vals Q.let (left m) (T.digs (right m)) j)
    (hrows : ∀ x' m, Ledger.Holds (rows x') (D.msg₃ m) →
      Late.Eqs (D.pr x').1 (D.pr x').2 (left m) (T.digs (right m))) :
    ∀ x' m, Ledger.Holds (layR D rows x') (D.msg₃ m) → Ledger.Holds (layD D x') (D.msg₃ m) := by
  intro x' m h f hf
  rcases List.mem_append.1 hf with hf | hf
  · exact h f (List.mem_append_left _ hf)
  · rcases List.mem_append.1 hf with hf | hf
    · exact h f (List.mem_append_right _ (List.mem_append_left _ hf))
    · have g : Ledger.Holds (rows x') (D.msg₃ m) :=
        fun f' hf' => h f' (List.mem_append_right _ (List.mem_append_right _ hf'))
      have g2 : Ledger.Holds ((cl Q.let D.e D.keep (D.pr x')).map (pushF D.is)) (D.msg₃ m) := by
        rw [pushL_holds, show (fun j => D.msg₃ m (D.is j)) = _ from funext (hs m)]
        exact cl_of_eqs Q.let D.e D.keep _ _ _ _ (hrows x' m g)
      exact g2 f hf

/-- The same at one statement for a ledger that is laid out by exponents (`layout`,
Cb/Pv/Tail/Claims.lean), if its list has every form of `layR`, with exponents that differ and are
below n. -/
theorem hlay_rows_layout (rows : D.X' → Ledger K J₃)
    (hs : ∀ m j, D.msg₃ m (D.is j) = vals Q.let (left m) (T.digs (right m)) j)
    (hrows : ∀ x' m, Ledger.Holds (rows x') (D.msg₃ m) →
      Late.Eqs (D.pr x').1 (D.pr x').2 (left m) (T.digs (right m)))
    (n : ℕ) (x' : D.X') (Lx : List (ℕ × Form K J₃))
    (hmem : ∀ f, f ∈ layR D rows x' → ∃ z ∈ Lx, z.2 = f)
    (hinj : ∀ z ∈ Lx, ∀ z' ∈ Lx, z.1 = z'.1 → z = z') (hlt : ∀ z ∈ Lx, z.1 < n) (m : MM)
    (h : Ledger.Holds (layout n Lx) (D.msg₃ m)) : Ledger.Holds (layD D x') (D.msg₃ m) := by
  refine hlay_rows T left right D rows hs hrows x' m fun f hf => ?_
  obtain ⟨z, hz, rfl⟩ := hmem f hf
  exact (layout_holds n Lx (D.msg₃ m) hinj hlt).1 h z hz

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.cl_of_eqs
#print axioms Cb.Pv.Tail.hlay_rows
#print axioms Cb.Pv.Tail.hlay_rows_layout
