-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/PackedAtSeg.lean: AT AN ATTENTION SEGMENT, IN THE GOALS' SCOPE:
WHAT THE FRAME's VALUES LAY FOR THE ARRAY OF A MATRIX OF THE SEGMENT's LIST IS THE PACKING OF THIS
KIND's OWN READING OF THE CELLS OF THAT COLUMN. CONDITIONAL: on the three premises on the public
files; on the matrix's not being the planes'; and ON ONE PREMISE ON THE READER OF THE CELLS: that it
answers the same under the owner's number and name as under the segment's. Lemmas. Nothing is said
of what the cells are.

What it is for. The equation that this kind's cells ask of a script's messages (`ESymsRaw`,
CellsQRaw.lean in this folder) has on its right the packing, at the radix of the plan's record, of
`cellAt` (Script.lean in this folder) down a column. The frame's filling of a first sending lays
`cellsVals`' value (Johnson/Desc/ProofFile/Honest/K1/FirstData.lean). This file says that the
second, read into the extension field, is the first.

Main names:
  `cells_pack_own`: **at the segment's own matrices as0, ah, ao: no premise on the reader**; the
    value stands at the segment's number 2 g + 1, under "M i". `cells_pack_qa`: **at qa: the one
    premise, spelled out**; the value stands at number 2 g, under "M6". Two corollaries of
    `cells_pack_att`: they add nothing to it.
  `cells_pack_label`: **THE LAW, in the letters of the plan's label**: lab: the label of entry i of
    the plan's list (`Meaning.labAt`); the value stands at the owner's number `Meaning.ownerK lab`
    and under the name `Meaning.nameOf (Meaning.ownerA lab)`, at which the library's ties look an
    array up in the layout.
  `cells_pack_att`: the same in the letters of the sizes `Sz.ref` (`Sz.owner`, `Sz.mu`), with the
    name's reading as a premise.
  `owner_numbers_att`: the label's two numbers are those of `Sz.ref`'s owner.
  `shape_at_plan`: the plan's record has `Sz.ref`'s rows and columns. `mu_att`: a helper.
  `labelOf_label`: this kind's name of matrix number i (`labelOf`, Row.lean one folder up) is the
    label of the name with that number. `nameOf_arrayLabel`: the two spellings of an array's name
    are one.

WHICH MATRICES. At an attention segment the list is as0, ah, ao, bA, qa. bA, the planes, is left
out, as in the library's law on shapes. as0, ah, ao are the segment's own: there the premise on the
reader is an equation of a term with itself. qa IS BORROWED from the group's feed-forward segment
(`Sz.owner`, Johnson/HonestTrace/Places.lean): the frame has no array for it at this segment; its
value stands at the owner's; there the premise says something: that the reader answers for qa the
same under both segments' numbers.

How. `cellsVals_pack`, `labelNo_arrayLabel`, `val_eOfF` (PackedVals.lean in this folder);
`shapeNo_in_scope` (Johnson/Goal/HonestTrace/ShapesAtRefInScope.lean), `planMats_eq`,
`parts_in_scope` (FullInScope.lean there), `H2K5.Door.tlAt_att`, `H2K5.Door.shapeA_at`
(Johnson/Desc/First/Att/Door/Law/): the plan's record has `Sz.ref`'s rows and columns;
`shape_owner`, `below_of_mu` (Johnson/HonestTrace/PlacesBack.lean): the owner's shape is the
borrower's; `Meaning.owner_label` (Johnson/Goal/Meaning/HidSeatsOf.lean), `Meaning.size_odd`,
`Meaning.ix_of_core` (HidOwner.lean there): the label names the owner.

Limits. At `Sz.ref`, the full-size example's numbers, typed by hand there. That the reader meets the
premise at qa is not shown: the library has the like for one trace of integers alone
(`borrowed_in_scope`, FullInScope.lean). That the entry of a segment's list of arrays is (owner's
number, that name) is not shown here: it is a clause of the library's tie (`Meaning.linkTieB`,
Johnson/Goal/Meaning/ReadingsOne.lean). `cells_pack_label` rests, through `labelNo_arrayLabel`, on
one closed fact that Lean's kernel decided by evaluation (see PackedVals.lean). Of the message, row
and place at which the value is laid nothing is said: WayBack.lean and WayBackFill.lean in this
folder.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.PackedVals
import Johnson.Desc.ProofFile.Honest.K5.Law.Script
import Johnson.Desc.First.Look.K3CallerAtt
import Johnson.Goal.HonestTrace.ShapesAtRefInScope
import Johnson.Goal.Meaning.HidSeatsOf
import Johnson.Desc.First.Att.Door.Law.K5CellsAny
import Johnson.Desc.First.Att.Door.Law.K5RestIdn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.HonestTrace (Sz Seg MatName pack3 pack3_eq_pack arrayLabel nameNo_eq_some_iff
  matAt_eq_some_iff no?_lt shapeNo_in_scope planMats planMats_eq parts_in_scope shape_owner
  below_of_mu ref_ok)
open ProofFile.Honest.K1 (labelNo cellsVals)
open VerifiableInference.Desc.First.Look (szOf)

/-- The two spellings of an array's name in the layout are one. -/
theorem nameOf_arrayLabel (a : ℕ) : Meaning.nameOf a = arrayLabel a := rfl

/-- **This kind's name of matrix number i is the label of the name with that number.** Conditional:
hN: the shape and the sizes have one number of parts of as; h: i is a number of the list. -/
theorem labelOf_label {Sh : OnBytes.Attention.Shape} {S : Sz} (hN : Sh.cf.NAs = S.NAs) {g i : ℕ}
    {μ : MatName} (h : S.nameNo (.att g) i = some μ) : labelOf Sh i = μ.label := by
  have nb : ∀ x y : ℕ, x ≠ y → ¬ ((x == y) = true) := fun x y hxy e => hxy (beq_iff_eq.1 e)
  simp only [Sz.nameNo] at h
  unfold labelOf
  rw [hN]
  split_ifs at h with h1 h2 h3 h4 h5
  · obtain rfl := Option.some.inj h
    rw [if_pos h1]
    rfl
  · obtain rfl := Option.some.inj h
    rw [if_neg h1, if_pos (beq_iff_eq.2 h2)]
    rfl
  · obtain rfl := Option.some.inj h
    rw [if_neg h1, if_neg (nb _ _ h2), if_pos (beq_iff_eq.2 h3)]
    rfl
  · obtain rfl := Option.some.inj h
    rw [if_neg h1, if_neg (nb _ _ h2), if_neg (nb _ _ h3), if_pos (beq_iff_eq.2 h4)]
    rfl
  · obtain rfl := Option.some.inj h
    rw [if_neg h1, if_neg (nb _ _ h2), if_neg (nb _ _ h3), if_neg (nb _ _ h4)]
    rfl

/-- The number of a name in an attention segment's list, in the sizes' two spellings. -/
theorem mu_att {g : ℕ} (hg : g < 12) {i : ℕ} {μ : MatName}
    (hi : Sz.ref.nameNo (.att g) i = some μ) : Sz.ref.mu (.att g) μ = some i := by
  unfold Sz.mu
  rw [if_pos (show Seg.Below Sz.ref.nGr (.att g) from hg)]
  exact (nameNo_eq_some_iff Sz.ref _ _ _).1 hi

section
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
  {X : OnBytes.Model.Verify.Public}

/-- **The label's two numbers are those of `Sz.ref`'s owner.** Conditional: the three premises on
the public files; g is below 12; i is the number of μ in the list. -/
theorem owner_numbers_att (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hX : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12) {i : ℕ}
    {μ : MatName} (hi : Sz.ref.nameNo (.att g) i = some μ) :
    Meaning.ownerK (Meaning.labAt X (2 * g + 1) i) = (Sz.ref.owner (.att g) μ).1.no 12 ∧
      Sz.ref.mu (Sz.ref.owner (.att g) μ).1 (Sz.ref.owner (.att g) μ).2 =
        some (Meaning.ownerA (Meaning.labAt X (2 * g + 1) i)) := by
  have C := OnBytes.Road.Hd.core_of_scope hZ hR hX
  have hno := (nameNo_eq_some_iff Sz.ref _ _ _).1 hi
  have hlt : i < 5 := no?_lt Sz.ref hno
  have hl := Meaning.owner_label hX C (k := 2 * g + 1) (a := i) (by omega)
    (by rw [Meaning.size_odd hX C hg]; exact hlt)
  have n1 := (parts_in_scope hZ hR hX).2.2.1 g hg
  have i6 := (Meaning.ix_of_core hX C).1
  unfold Meaning.ownerOf at hl
  rw [if_neg (by omega), if_pos (by omega), show (2 * g + 1) / 2 = g by omega, n1, i6] at hl
  by_cases e : i = 1 + 3
  · rw [if_pos e] at hl
    obtain ⟨k1, k2⟩ := Prod.mk.inj hl
    have hq : μ = .qa := MatName.no?_inj hno (by rw [e]; rfl)
    subst hq
    rw [k1, k2]
    refine ⟨?_, ?_⟩
    · show 2 * g + 1 - 1 = 2 * g
      omega
    · show Sz.ref.mu (.ff g) .qa = some 6
      unfold Sz.mu
      rw [if_pos (show Seg.Below Sz.ref.nGr (.ff g) from hg)]
      rfl
  · rw [if_neg e] at hl
    obtain ⟨k1, k2⟩ := Prod.mk.inj hl
    have ho : Sz.ref.owner (.att g) μ = (.att g, μ) := by
      cases μ with
      | qa => exact absurd (Option.some.inj hno).symm e
      | _ => rfl
    rw [ho, k1, k2]
    refine ⟨rfl, ?_⟩
    show Sz.ref.mu (.att g) μ = some i
    unfold Sz.mu
    rw [if_pos (show Seg.Below Sz.ref.nGr (.att g) from hg)]
    exact hno

/-- **The plan's record has `Sz.ref`'s rows and columns**, at a matrix of an attention segment's
list that is not the planes'. Conditional: the three premises on the public files; g is below 12; a
is the group's plan; i is the number of μ, which is not the planes'. -/
theorem shape_at_plan (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hX : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12)
    {a : OnBytes.Attention.Plan} (ha : X.A[g]? = some a) {i : ℕ} {μ : MatName}
    (hi : Sz.ref.nameNo (.att g) i = some μ) (hp : μ ≠ .bA) :
    (a.seam.tl.mats.getD i {}).m = (Sz.ref.shape (.att g) μ).1 ∧
      (a.seam.tl.mats.getD i {}).k = (Sz.ref.shape (.att g) μ).2 := by
  have hM : Sz.ref.matAt (2 * g + 1) i = some (.att g, μ) :=
    (matAt_eq_some_iff Sz.ref _ _ _ _).2 ⟨hg, rfl, mu_att hg hi⟩
  obtain ⟨-, -, hm, hk⟩ := shapeNo_in_scope hZ hR hX hM hp
  have eT : planMats X (2 * g + 1) = a.seam.tl.mats := by
    rw [planMats_eq]
    show (Meaning.tlAt X (2 * g + 1)).mats = _
    rw [H2K5.Door.tlAt_att hg ha]
  have eS : Sz.ref.shapeNo (2 * g + 1) i = Sz.ref.shape (.att g) μ := by
    unfold Sz.shapeNo
    rw [hM]
  rw [eT, eS] at hm hk
  exact ⟨hm, hk⟩

/-- **The law in the letters of the sizes.** Conditional: the three premises on the public files; g
is below 12; a is the group's plan; i is the number of μ, which is not the planes'; mu₀ is the
number of the owner's matrix in the owner's list; hn: the name is read as mu₀; c lies inside the
plan's columns; hC: the reader answers the same under the owner's number and label as under the
segment's.
-/
theorem cells_pack_att (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hX : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12)
    {a : OnBytes.Attention.Plan} (ha : X.A[g]? = some a) {i : ℕ} {μ : MatName}
    (hi : Sz.ref.nameNo (.att g) i = some μ) (hp : μ ≠ .bA) {mu₀ : ℕ}
    (h0 : Sz.ref.mu (Sz.ref.owner (.att g) μ).1 (Sz.ref.owner (.att g) μ).2 = some mu₀)
    {name : String} (hn : labelNo name = some mu₀) (R : Readers) (hd : List Fmt.Drawn) {c : ℕ}
    (hc : c < (a.seam.tl.mats.getD i {}).k)
    (hC : ∀ r, R.cells.cell ((Sz.ref.owner (.att g) μ).1.no 12)
      (Sz.ref.owner (.att g) μ).2.label r c = R.cells.cell (2 * g + 1) μ.label r c) (i' : ℕ) :
    asE (some ((cellsVals Sz.ref).val R hd ((Sz.ref.owner (.att g) μ).1.no 12) name i' c)) =
      Alg.pack (((szOf a.seam.tl).rad : ℕ) : ℤ)
        (fun r : Fin (a.seam.tl.mats.getD i {}).m =>
          OnBytes.Model.Reading.gl.val (cellAt a.S (2 * g + 1) R.cells i r.val c)) i' := by
  have hmu := mu_att hg hi
  obtain ⟨hm, hk⟩ := shape_at_plan hZ hR hX hg ha hi hp
  have eO : Sz.ref.shape (Sz.ref.owner (.att g) μ).1 (Sz.ref.owner (.att g) μ).2 =
      Sz.ref.shape (.att g) μ := shape_owner Sz.ref ref_ok.1 (.att g) μ (by rw [hmu]; rfl)
  have hM₀ : Sz.ref.matAt ((Sz.ref.owner (.att g) μ).1.no 12) mu₀ =
      some ((Sz.ref.owner (.att g) μ).1, (Sz.ref.owner (.att g) μ).2) :=
    (matAt_eq_some_iff Sz.ref _ _ _ _).2 ⟨below_of_mu (by rw [h0]; rfl), rfl, h0⟩
  have hc₀ : c < (Sz.ref.shape (Sz.ref.owner (.att g) μ).1 (Sz.ref.owner (.att g) μ).2).2 := by
    rw [eO, ← hk]
    exact hc
  have eN : a.S.cf.NAs = Sz.ref.NAs := by
    rw [← H2K5.Door.shapeA_at ha]
    exact (parts_in_scope hZ hR hX).2.2.1 g hg
  have eR : (((szOf a.seam.tl).rad : ℕ) : ℤ) = 2 ^ 20 := by
    show ((2 ^ 20 : ℕ) : ℤ) = 2 ^ 20
    norm_num
  have em : (Sz.ref.shape (Sz.ref.owner (.att g) μ).1 (Sz.ref.owner (.att g) μ).2).1 =
      (a.seam.tl.mats.getD i {}).m := by rw [eO, ← hm]
  have mid : pack3 (Sz.ref.shape (Sz.ref.owner (.att g) μ).1 (Sz.ref.owner (.att g) μ).2).1
      (fun r => algebraMap Cb.Gl.F Cb.Gl.E (R.cells.cell ((Sz.ref.owner (.att g) μ).1.no 12)
        (Sz.ref.owner (.att g) μ).2.label r c)) i' =
      pack3 (a.seam.tl.mats.getD i {}).m
        (fun r => OnBytes.Model.Reading.gl.val (cellAt a.S (2 * g + 1) R.cells i r c)) i' := by
    rw [em]
    congr 1
    funext r
    show _ = OnBytes.Model.Reading.gl.val (eOfF (R.cells.cell (2 * g + 1) (labelOf a.S i) r c))
    rw [val_eOfF, hC r, labelOf_label eN hi]
  rw [cellsVals_pack Sz.ref R hd hn hM₀ hc₀ i', eR]
  exact ((pack3_eq_pack _ _ i').symm.trans mid).trans (pack3_eq_pack _ _ i')

/-- **THE LAW, IN THE LETTERS OF THE PLAN's LABEL.** Conditional: the three premises on the public
files; g is below 12; a is the group's plan; i is the number of μ, which is not the planes'; c lies
inside the plan's columns; hC: THE READER ANSWERS THE SAME under the owner's number and label as
under the segment's number and this kind's name of the matrix. -/
theorem cells_pack_label (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hX : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12)
    {a : OnBytes.Attention.Plan} (ha : X.A[g]? = some a) {i : ℕ} {μ : MatName}
    (hi : Sz.ref.nameNo (.att g) i = some μ) (hp : μ ≠ .bA) (R : Readers)
    (hd : List Fmt.Drawn) {c : ℕ} (hc : c < (a.seam.tl.mats.getD i {}).k)
    (hC : ∀ r, R.cells.cell (Meaning.ownerK (Meaning.labAt X (2 * g + 1) i))
      (Sz.ref.owner (.att g) μ).2.label r c = R.cells.cell (2 * g + 1) (labelOf a.S i) r c)
    (i' : ℕ) :
    asE (some ((cellsVals Sz.ref).val R hd (Meaning.ownerK (Meaning.labAt X (2 * g + 1) i))
        (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X (2 * g + 1) i))) i' c)) =
      Alg.pack (((szOf a.seam.tl).rad : ℕ) : ℤ)
        (fun r : Fin (a.seam.tl.mats.getD i {}).m =>
          OnBytes.Model.Reading.gl.val (cellAt a.S (2 * g + 1) R.cells i r.val c)) i' := by
  obtain ⟨k1, k2⟩ := owner_numbers_att hZ hR hX hg hi
  have eN : a.S.cf.NAs = Sz.ref.NAs := by
    rw [← H2K5.Door.shapeA_at ha]
    exact (parts_in_scope hZ hR hX).2.2.1 g hg
  have h9 : ∀ σ : Seg, Sz.ref.len σ ≤ 9 := fun σ => by
    cases σ with
    | ff _ => exact (by decide : 3 + 1 + 5 ≤ 9)
    | att _ => exact (by decide : 1 + 4 ≤ 9)
    | head => exact (by decide : 4 + 4 ≤ 9)
  have hlt : Meaning.ownerA (Meaning.labAt X (2 * g + 1) i) < 26 := by
    have k3 := k2
    unfold Sz.mu at k3
    split_ifs at k3
    exact Nat.lt_of_lt_of_le (no?_lt Sz.ref k3) (Nat.le_trans (h9 _) (by decide))
  rw [k1] at hC ⊢
  exact cells_pack_att hZ hR hX hg ha hi hp k2 (labelNo_arrayLabel hlt) R hd hc
    (fun r => by rw [hC r, labelOf_label eN hi]) i'

/-- **AT THE SEGMENT's OWN MATRICES as0, ah, ao: NO PREMISE ON THE READER.** A corollary of
`cells_pack_att`. Conditional: the three premises on the public files; g is below 12; a is the
group's plan; i is below 3; c lies inside the plan's columns. -/
theorem cells_pack_own (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hX : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12)
    {a : OnBytes.Attention.Plan} (ha : X.A[g]? = some a) {i : ℕ} (hi : i < 3) (R : Readers)
    (hd : List Fmt.Drawn) {c : ℕ} (hc : c < (a.seam.tl.mats.getD i {}).k) (i' : ℕ) :
    asE (some ((cellsVals Sz.ref).val R hd (2 * g + 1) (Meaning.nameOf i) i' c)) =
      Alg.pack (((szOf a.seam.tl).rad : ℕ) : ℤ)
        (fun r : Fin (a.seam.tl.mats.getD i {}).m =>
          OnBytes.Model.Reading.gl.val (cellAt a.S (2 * g + 1) R.cells i r.val c)) i' := by
  have key : ∀ μ : MatName, Sz.ref.nameNo (.att g) i = some μ → μ ≠ .bA →
      Sz.ref.owner (.att g) μ = (.att g, μ) →
      asE (some ((cellsVals Sz.ref).val R hd (2 * g + 1) (Meaning.nameOf i) i' c)) =
        Alg.pack (((szOf a.seam.tl).rad : ℕ) : ℤ)
          (fun r : Fin (a.seam.tl.mats.getD i {}).m =>
            OnBytes.Model.Reading.gl.val (cellAt a.S (2 * g + 1) R.cells i r.val c)) i' := by
    intro μ hμ hp ho
    have h0 : Sz.ref.mu (Sz.ref.owner (.att g) μ).1 (Sz.ref.owner (.att g) μ).2 = some i := by
      rw [ho]
      exact mu_att hg hμ
    have t := cells_pack_att hZ hR hX hg ha hμ hp h0 (name := Meaning.nameOf i)
      (labelNo_arrayLabel (by omega)) R hd hc
      (fun r => congrArg (fun q : Seg × MatName => R.cells.cell (q.1.no 12) q.2.label r c) ho) i'
    rw [ho] at t
    exact t
  interval_cases i
  · exact key (.as 0) (by simp [Sz.nameNo, Sz.ref]) (by intro e; cases e) rfl
  · exact key .ah (by simp [Sz.nameNo, Sz.ref]) (by intro e; cases e) rfl
  · exact key .ao (by simp [Sz.nameNo, Sz.ref]) (by intro e; cases e) rfl

/-- **AT qa, WHICH THE SEGMENT BORROWS: THE ONE PREMISE ON THE READER, SPELLED OUT.** A corollary of
`cells_pack_att`. The value stands at the group's feed-forward segment, number 2 g, under "M6".
Conditional: the three premises on the public files; g is below 12; a is the group's plan; c lies
inside the plan's columns; hC: the reader answers for qa the same under both segments' numbers. -/
theorem cells_pack_qa (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hX : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) {g : ℕ} (hg : g < 12)
    {a : OnBytes.Attention.Plan} (ha : X.A[g]? = some a) (R : Readers) (hd : List Fmt.Drawn)
    {c : ℕ} (hc : c < (a.seam.tl.mats.getD 4 {}).k)
    (hC : ∀ r, R.cells.cell (2 * g) "qa" r c = R.cells.cell (2 * g + 1) "qa" r c) (i' : ℕ) :
    asE (some ((cellsVals Sz.ref).val R hd (2 * g) (Meaning.nameOf 6) i' c)) =
      Alg.pack (((szOf a.seam.tl).rad : ℕ) : ℤ)
        (fun r : Fin (a.seam.tl.mats.getD 4 {}).m =>
          OnBytes.Model.Reading.gl.val (cellAt a.S (2 * g + 1) R.cells 4 r.val c)) i' := by
  have h0 : Sz.ref.mu (Sz.ref.owner (.att g) .qa).1 (Sz.ref.owner (.att g) .qa).2 = some 6 := by
    show Sz.ref.mu (.ff g) .qa = some 6
    unfold Sz.mu
    rw [if_pos (show Seg.Below Sz.ref.nGr (.ff g) from hg)]
    rfl
  exact cells_pack_att hZ hR hX hg ha (i := 4) (μ := .qa) (by simp [Sz.nameNo, Sz.ref])
    (by intro e; cases e) h0 (name := Meaning.nameOf 6) (labelNo_arrayLabel (by decide)) R hd hc
    hC i'

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.nameOf_arrayLabel
#print axioms ProofFile.Honest.K5.labelOf_label
#print axioms ProofFile.Honest.K5.mu_att
#print axioms ProofFile.Honest.K5.owner_numbers_att
#print axioms ProofFile.Honest.K5.shape_at_plan
#print axioms ProofFile.Honest.K5.cells_pack_att
#print axioms ProofFile.Honest.K5.cells_pack_label
#print axioms ProofFile.Honest.K5.cells_pack_own
#print axioms ProofFile.Honest.K5.cells_pack_qa
