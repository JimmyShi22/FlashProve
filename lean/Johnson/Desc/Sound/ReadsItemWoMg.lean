-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ReadsItemWoMg.lean: THE ITEM wo m AT THE COMPOSED MEANING: ITS SENTENCE READS
ONLY WHAT THE TABLE BOOKS, AND THE PREMISE ON THE ROW FALLS. Three theorems.

Why. `readsItem_wo` (Johnson/Desc/Sound/ReadsItemWo.lean) had one named premise hOn: every mask
entry that the row names is of the index masks' message. At the composed meaning the row is the
frame's reader's (`rowAt`), and that reader hands the maker of the row the state's own number of the
index masks' message: so hOn holds by the maker's text, at every state.

What is said. `onLedger_pendingRowO`: the one mask entry of a row that `pendingRowO` returns is of
the message whose number it was handed. `onLedger_rowAt`: so every mask entry of the row that
`rowAt` gives at a state s is of the message number s.out.indexMasks. `readsItem_wo_mg`:
`ReadsItemQR 𝔇.arr 𝔇.N (mgAll 𝔇 Mg) links ps get Rch k (.wo m)` under the pending rows' own premises
alone: the two public items' texts, the listed seat of the index masks, the list's bound, the index
masks' pin open at k, and the four facts on reached states.

Limits. It reaches the borders at which the index masks' pin is open. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.ReadsItemWo
import Johnson.Desc.Sound.MgAll
import Johnson.Top.H0.Walk.FrameRow
import Johnson.Desc.First.Pend.RowMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers Comp)
open VerifiableInference.Desc.First.Pend (pendingRowO pendingRowO_iff)
open VerifiableInference.Desc.Sound (MsgT Frame ReadsItemQR MgData mgAll CellsQ)
open VerifiableInference.Desc.K12.Door (Laid)
open Johnson.Desc.First.Walk.Law (rowAt rowAt_some)

/-- The returned row's one mask entry is of the message whose number was handed in. -/
theorem onLedger_pendingRowO {lay : WsLay} {indexMasks : ℕ} {o : WsForkOut} {claims : ℕ}
    {Sh : LinShape} {oracles oracles' : Array OnBytes.Oracle} {row : TensorRow}
    (h : pendingRowO lay indexMasks o claims Sh oracles = .ok (row, oracles')) :
    OnLedger indexMasks row := by
  obtain ⟨-, -, -, -, _, _, -, -, -, -, -, _, -, _, -, l, -, c, l', -, rfl, -⟩ :=
    (pendingRowO_iff lay indexMasks o claims Sh oracles oracles' row).1 h
  intro t ht
  rw [List.mem_singleton] at ht
  subst ht
  rfl

/-- So is every mask entry of the frame's reader's row: at every state. -/
theorem onLedger_rowAt {lay : WsLay} {n : ℕ} {lin : LinShape} {s : S} {r : TensorRow}
    (h : rowAt lay n lin s = some r) : OnLedger s.out.indexMasks r := by
  obtain ⟨w, os, -, hp⟩ := rowAt_some.1 h
  exact onLedger_pendingRowO hp

section
variable {A Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public} {Fr : Frame}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- **The item wo m at the composed meaning.** -/
theorem readsItem_wo_mg (M : List OracleShape) (L : Laid)
    (hII : ∀ x, (mgAll 𝔇 Mg).pub .indexIs x = indexIsC 𝔇.N.indexNo x.2)
    (hIT : ∀ x, (mgAll 𝔇 Mg).pub .indexThere x = indexThereC x.2)
    (hL : L.places[𝔇.N.indexNo]? = some 𝔇.N.index) (hbelow : PlanBelow L 𝔇.N) (links : List ModelPart)
    (ps : List Place) (get : A → P × S) (Rch : ℕ → A × Fr.E.Str → Prop) (k : ℕ)
    (hpin : Item.pinI ∈ openAt links ps k) (m : ℕ)
    (hFacts : ∀ a, Rch k a → (get a.1).2.failed = none → FactsR13 M L (get a.1).2) :
    ReadsItemQR 𝔇.arr 𝔇.N (mgAll 𝔇 Mg) links ps get Rch k (.wo m) :=
  readsItem_wo 𝔇.N (mgAll 𝔇 Mg) 𝔇.arr 𝔇.mat13 M L hII hIT hL hbelow links ps get Rch k hpin m
    (rowAt 𝔇.d1.lay (𝔇.d1.ncl m) 𝔇.d1.lin) (fun _ _ _ => Iff.rfl) hFacts
    fun _ _ _ _ _ hrow => onLedger_rowAt hrow

end

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.onLedger_pendingRowO
#print axioms VerifiableInference.Desc.K13.Law.onLedger_rowAt
#print axioms VerifiableInference.Desc.K13.Law.readsItem_wo_mg
