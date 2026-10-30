--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/ShapeTie.lean: kind K13: the two shapes of what stands at the first chain's
end say the same of the claim: that of Johnson/Desc/K13/Honest/ShapeSim.lean (`EndSh`, `endOf`),
which the members' batching writes, and that of Johnson/Desc/K13/Honest/ShapeM4.lean (`LaidSh`,
`sh4`), which the sub-protocol behind W's commitment reads. Definitions with code, and statements
with their proofs.

Why. The guards of the sub-protocol behind W's commitment read the claim's shape: how many
coordinates its point has, and the places of its masks. That shape is laid by the batching.
ShapeSim.lean gives it as a function of the plan, the pile's rows' shapes and the mask entries taken
(`endOf_behind`). Here it is carried into the form that the guards read.
Main names:
  `claimOfRow`: from a row's shape (`RowSh`, ShapeDefs.lean of this folder) to a claim's shape
    (`ClaimSh`): the point's length; the slots, as entries of mask tables. The weights' numbers of
    variables are left out: no guard behind the batching reads them.
  `claimSh4_member`: the shape of the claim that is made of a row is `claimOfRow` of the row's
    shape.
  `laidOfEnd`, `laid_of_end`: where the claim that is laid is made of a row, what `sh4` holds as
    laid is a function of what `endOf` holds.
  `laid_behind_m3`: **behind the batching**: what `sh4` holds as laid, as a function of the plan's
    number of column variables, the pile's rows' shapes and the mask entries taken.

What is not claimed. Nothing on W's commitment, which stands between the two sub-protocols and
writes the numbers handed on and the new messages. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.ShapeSim
import Johnson.Desc.K13.Honest.ShapeM4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Slice
open VerifiableInference.Desc.First (S rowOfClaim)
open VerifiableInference.Desc.K13.Law

/-- From a row's shape to a claim's shape. -/
def claimOfRow (r : RowSh) : ClaimSh :=
  ⟨r.point, r.slots.map fun t => (t.oracle, OnBytes.Part.mask, t.index)⟩

/-- The shape of the claim that is made of a row. -/
theorem claimSh4_member (row : TensorRow) :
    claimSh4 (memberClaim row) = claimOfRow (rowSh row) := by
  show ClaimSh.mk row.psi.length
    (((row.masks.map fun m => (⟨m.1.oracle, .mask, m.1.index, m.2⟩ : Single)).toArray).toList.map
      fun u => (u.oracle, u.part, u.index)) = ⟨row.psi.length, (row.masks.map (·.1)).map _⟩
  rw [List.toList_toArray, List.map_map, List.map_map]
  rfl

/-- What is laid for the last chain, off the other shape. -/
def laidOfEnd (e : EndSh) : Option LaidSh :=
  e.lin.map fun q => ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1, claimOfRow q.2.2.2.2⟩

/-- Where the claim that is laid is made of a row, what `sh4` holds as laid is a function of what
`endOf` holds. -/
theorem laid_of_end {s : S} {a : First.MemOwn} (hs : s.here = .mem a)
    (hc : ∀ l, a.lin = some l → ∃ row, l.claim = memberClaim row) :
    (sh4 s).laid = (endOf s).bind laidOfEnd := by
  have e1 : (sh4 s).laid = a.lin.map laidSh := by
    unfold sh4
    rw [hs]
  have e2 : endOf s = some ⟨a.msg, a.ids,
      a.lin.map fun l => (l.w, l.split, l.own, l.mask, rowSh (rowOfClaim l.claim))⟩ := by
    unfold endOf
    rw [hs]
  rw [e1, e2]
  cases hl : a.lin with
  | none => rfl
  | some l =>
    obtain ⟨row, hrow⟩ := hc l hl
    show some (laidSh l) = some ⟨l.w, l.split, l.own, l.mask,
      claimOfRow (rowSh (rowOfClaim l.claim))⟩
    rw [hrow, rowOfClaim_member, ← claimSh4_member, ← hrow]
    rfl

/-- **At the state that the batching's return has the form of** (`withClaim`; that the return has
that form is `atM3_return_row`, ShapeSim.lean, which is not called here): what `sh4` holds as laid.
-/
theorem laid_behind_m3 {k : ℕ} (s : S) (st : Statement) (msg : Array OracleNotice) {x : E}
    {fresh : List Slot} {hd : Psc.Heard} {o : Psc.Out} (hf : Batt.fits k s.out.pending = true)
    (hr : Psc.run (Batt.claimOf s.out.pending x) (Batt.summandOf s.out.pending x) fresh hd =
      some o) :
    (sh4 (withClaim s st msg (Batt.rowOf s.out.pending o))).laid =
      some ⟨noId, noId, noId, none, claimOfRow (claimSh k (shOf s).pile fresh)⟩ := by
  have hc : ∀ l : LinFirst,
      (some { claim := memberClaim (Batt.rowOf s.out.pending o) } : Option LinFirst) = some l →
      ∃ row, l.claim = memberClaim row := by
    intro l hl
    obtain rfl := Option.some.inj hl
    exact ⟨_, rfl⟩
  rw [laid_of_end (a := ⟨msg, #[], some { claim := memberClaim (Batt.rowOf s.out.pending o) }⟩) rfl
    hc, endOf_behind s st msg hf hr]
  rfl

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.claimSh4_member
#print axioms VerifiableInference.Desc.K13.Honest.laid_of_end
#print axioms VerifiableInference.Desc.K13.Honest.laid_behind_m3
