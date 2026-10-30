-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Member.lean
(kind K9's soundness lemma): THEOREMS: two hypotheses of the lemma's last forms are
met, for good.
  reading_inj   the library's reading Reading.gl is one to one on typed elements of the extension
                field: the hypothesis "hinj" of Law/RealPiece.lean and Law/Row3.lean at ρ := gl.
  idLens, idLens_reads   a lens that meets every law of a lens that these files ask: the state is
                the part itself.
  fits_id       Fits (Law/BatchAdds.lean) at that lens and at letters that ask nothing.
Not a member of the whole list of hypotheses: no segment, no run of claims, no piece is here.

-/
import OnBytes.Slice.Draws
import Johnson.Desc.First.Batch.Law.BatchAdds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Lens Where)

/-- **The library's reading is one to one on typed elements.** -/
theorem reading_inj :
    Function.Injective fun a : _root_.Run.EV .two =>
      Reading.gl.val (E.ofTriple (_root_.Run.toU3 a)) := by
  intro a b h
  apply Slice.evE_inj
  have e : ∀ x : Fmt.Ext, Reading.gl.val (E.ofTriple x) = Slice.toE x := fun x => by
    show Slice.toE (E.ofTriple x).triple = _
    rw [E.triple_ofTriple]
  simp only [e] at h
  exact h

/-- The state is the part itself. -/
def idLens : Lens K9.Part := ⟨some, fun _ a => a⟩

theorem idLens_reads (s a : K9.Part) :
    ∃ a', idLens.get? (idLens.set s a) = some a' ∧ a'.F = a.F ∧ a'.L = a.L ∧ a'.d.st = a.d.st :=
  ⟨a, rfl, rfl, rfl, rfl⟩

/-- Letters that ask nothing. -/
def plainOthers (K : Type) : Others K9.Part Unit K where
  fixed := fun _ => ()
  ready := fun _ => True
  good := fun _ => True
  behind := fun _ => True
  more := fun _ _ => True
  full := fun _ => True
  cnt := fun _ _ => 0
  eqs := fun _ _ _ => []
  exps := fun _ _ _ => []

theorem fits_id (K : Type) (p : Where) : Fits idLens (plainOthers K) p where
  lens := fun _ a _ => ⟨a, rfl, rfl⟩
  atDraw := fun _ _ _ _ _ _ _ => ⟨rfl, trivial⟩
  atAdding := fun _ _ _ _ _ _ _ => ⟨trivial, trivial⟩

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.reading_inj
#print axioms VerifiableInference.Desc.K9L.fits_id
