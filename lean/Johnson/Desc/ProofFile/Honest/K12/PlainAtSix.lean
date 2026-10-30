-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/PlainAtSix.lean

What it proves. Of the eight sub-protocols of the linear claim's shared rounds
(Johnson/Desc/K14/Text.lean), the six in which the prover sends no oracle message keep the mark
"no row of the statement has a written-out factor" (stPlainB,
Johnson/Desc/Ground/Shape/Marks.lean): wherever such a sub-protocol's function returns, and the mark
holds of the statement in front, it holds of the statement behind. No premise on the plan, the key,
the rounds or the columns. The two functions that note the new messages' numbers behind a sending
leave the statement as it is.

Names.
  eq_plain, product_plain   the two tensors of which the rows are made have no written-out factor.
  addLaid_plainRow, foldl_plain, part_plain   tools on rows.
  recGamma_plain, locX_plain, fold_plain   each row that the three makers return is plain.
  mapM_all   what holds of every value that a function returns holds of all that mapM returns.
  addRowsAll_plain   rows that are plain, added one behind the other, keep the mark.
  linPoint_plain, laysRec_plain, loc_plain, joins_plain, linZeta_plain, split_plain   the six.
  behindU_st, behindOmega_st   the statement stays.

By what. The library's tensorBelow_shape (OnBytes/Slice/BlkForm.lean), tensorBelow_shape_at
(OnBytes/Slice/BlkTensCut.lean), insertChoice_plain (BlkForm.lean), addLaid_plain and addLaid_terms
(OnBytes/Slice/BlkLink.lean); newGroup_plain, join_plain, addRow_plain, takeMask_plain (Marks.lean).
The six proofs open the functions' texts as Johnson/Desc/K14/Quiet.lean opens them.

Limits.
- The two sendings are not here.
- The mark is on the form of rows alone: nothing is said of what a row says or of its
  coefficients.
- One direction: from a return to the mark behind. When a function returns is not treated.
- Steps of the verifier's: nothing is shown of any prover. Nothing on completeness, on soundness or
  on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.K14.Quiet
import Johnson.Desc.Ground.Shape.Marks
import OnBytes.Slice.BlkLink
import OnBytes.Slice.BlkTensCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain Desc.K14
open VerifiableInference.Desc VerifiableInference.Desc.Ground VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Keeps

/-! ## 1 Tools on tensors and rows -/

theorem eq_plain (z : List E) (s : E) : (Tensor.eq z s).denseVars = [] := rfl

theorem product_plain (f : List F) (s : E) : (Tensor.product f s).denseVars = [] := rfl

/-- Placed tensors without a written-out factor leave a plain row plain. -/
theorem addLaid_plainRow (o : ℕ) (lay : VectorLay) (l : List Tensor) (row : Row)
    (hl : ∀ t ∈ l, t.denseVars = []) (hr : PlainRow row) : PlainRow (addLaid row o lay l) :=
  ⟨addLaid_plain o lay l row hl hr.1, by
    rw [(addLaid_terms o lay l row).2]
    exact hr.2⟩

/-- A loop whose every step keeps a row plain. -/
theorem foldl_plain {α : Type} (f : Row → α → Row)
    (hf : ∀ r a, PlainRow r → PlainRow (f r a)) :
    ∀ (l : List α) (r : Row), PlainRow r → PlainRow (l.foldl f r)
  | [], _, h => h
  | a :: l, r, h => foldl_plain f hf l (f r a) (hf r a h)

/-- The part of a plain row on some of the messages is plain. -/
theorem part_plain (row : Row) (members : Array ℕ) (mine : Bool) (h : PlainRow row) :
    PlainRow (part row members mine) := by
  refine ⟨fun t ht => h.1 t ?_, fun f hf => h.2 f ?_⟩
  · have ht' : t ∈ (row.terms.filter (members.contains ·.oracle == mine)).toList := ht
    rw [Array.toList_filter] at ht'
    exact (List.mem_filter.1 ht').1
  · have hf' : f ∈ (row.forms.filter (members.contains ·.oracle == mine)).toList := hf
    rw [Array.toList_filter] at hf'
    exact (List.mem_filter.1 hf').1

/-! ## 2 The three makers' rows -/

/-- A row (rec_gamma) is plain. -/
theorem recGamma_plain {s : IndexShape} {seed : SampleSeed} {i : ℕ} {w y : Array E}
    {u : FoldedRow} {r : Row} (h : recGamma s seed i w y u = some r) : PlainRow r := by
  unfold recGamma at h
  dsimp only at h
  obtain ⟨l, hl, h⟩ := obind_ok h
  obtain ⟨sum, _, h⟩ := obind_ok h
  cases h
  have base : PlainRow (u.addAll {} l) :=
    addLaid_plainRow _ _ _ _ (fun t ht => (tensorBelow_shape _ (eq_plain _ _) _ _ _ hl t ht).2)
      (plainRow_of_empty _ rfl rfl)
  have all := foldl_plain _ (fun r (a : ℕ × ℕ) (hr : PlainRow r) =>
    (show PlainRow (r.addUnit u.oracle .main (u.lay.index (s.padPlace a.1 a.2))
      (subE (if a.1 == i then mulE seed.beta (thetaE a.2) else zeroE)
        ((Tensor.eq seed.z).entry (s.padPlace a.1 a.2)))) from ⟨hr.1, hr.2⟩))
    ((List.range s.answers).flatMap fun a => (List.range 3).map fun t => (a, t)) _ base
  exact ⟨all.1, all.2⟩

/-- A row (loc_x) is plain. -/
theorem locX_plain {S : FoldeqShape} {x : ℕ} {w : Array E} {column : Array F} {u : FoldedRow}
    {r : Row} (h : locX S x w column u = some r) : PlainRow r := by
  unfold locX at h
  dsimp only at h
  obtain ⟨message, hm, h⟩ := obind_ok h
  have h1 : PlainRow (u.addAll {} message) :=
    addLaid_plainRow _ _ _ _
      (fun t hx => (tensorBelow_shape _ (product_plain _ _) _ _ _ hm t hx).2)
      (plainRow_of_empty _ rfl rfl)
  have fin : ∀ tail : List Tensor, (∀ t ∈ tail, t.denseVars = []) →
      PlainRow (u.addAll (u.addAll {} message)
        (tail.map (·.insertChoice S.index.code.logR (u.lay.bits - S.index.code.logR)
          (S.tailFirst / 2 ^ S.index.code.logR)))) := fun tail htail =>
    addLaid_plainRow _ _ _ _ (fun t hx => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
      exact insertChoice_plain v (htail v hv) _ _ _) h1
  split at h
  · obtain ⟨tail, ht, h⟩ := obind_ok h
    obtain ⟨sum, _, h⟩ := obind_ok h
    cases ht
    cases h
    have k := fin [] (fun t hx => by cases hx)
    exact ⟨k.1, k.2⟩
  · obtain ⟨tail, ht, h⟩ := obind_ok h
    obtain ⟨sum, _, h⟩ := obind_ok h
    cases h
    have k := fin tail fun t hx => (tensorBelow_shape _ (product_plain _ _) _ _ _ ht t hx).2
    exact ⟨k.1, k.2⟩

/-- The row (fold) is plain. -/
theorem fold_plain {S : LinShape} {l : Lin} {lay : VectorLay} {r : Row}
    (h : fold S l lay = some r) : PlainRow r := by
  unfold fold at h
  obtain ⟨_, _, h⟩ := obind_ok h
  obtain ⟨onOmega, h1, h⟩ := obind_ok h
  obtain ⟨onU, h2, h⟩ := obind_ok h
  cases h
  exact addLaid_plainRow _ _ _ _
    (fun t hx => (tensorBelow_shape_at _ (eq_plain _ _) _ _ _ _ h2 t hx).2)
    (addLaid_plainRow _ _ _ _
      (fun t hx => (tensorBelow_shape _ (eq_plain _ _) _ _ _ h1 t hx).2)
      (plainRow_of_empty _ rfl rfl))

/-! ## 3 Rows added one behind the other -/

/-- What holds of every value that a function returns holds of all that mapM returns. -/
theorem mapM_all {α β : Type} (f : α → Option β) (P : β → Prop)
    (hf : ∀ a b, f a = some b → P b) : ∀ (l : List α) (r : List β), l.mapM f = some r →
    ∀ b ∈ r, P b
  | [], r, h, b, hb => by
    rw [List.mapM_nil] at h
    cases h
    cases hb
  | a :: l, r, h, b, hb => by
    rw [List.mapM_cons] at h
    obtain ⟨y, hy, h⟩ := obind_ok h
    obtain ⟨ys, hys, h⟩ := obind_ok h
    cases h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hf a _ hy
    · exact mapM_all f P hf l ys hys b hb

theorem addRowsFromAll_plain {L : Type} (g : ℕ) : ∀ (rows : List Row) (d d' : DState L),
    addRowsFrom g rows d = some d' → stPlainB d.st = true → (∀ r ∈ rows, PlainRow r) →
    stPlainB d'.st = true
  | [], d, d', h, hp, _ => by
    cases h
    exact hp
  | r :: l, d, d', h, hp, hr => by
    obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.1 h
    exact addRowsFromAll_plain g l e d' h
      (addRow_plain d e g r he hp (rowPlainB_iff.2 (hr r List.mem_cons_self)))
      fun x hx => hr x (List.mem_cons_of_mem _ hx)

/-- Rows that are plain, added one behind the other, keep the mark. -/
theorem addRowsAll_plain {L : Type} (d d' : DState L) (g : ℕ) (rows : List Row)
    (h : addRowsP d g rows = some d') (hp : stPlainB d.st = true)
    (hr : ∀ r ∈ rows, PlainRow r) :
    stPlainB d'.st = true := by
  unfold addRowsP at h
  split at h
  · exact addRowsFromAll_plain g rows d d' h hp hr
  · cases h

/-! ## 4 The six, and the two notes behind a sending -/

theorem linPoint_plain (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : linPoint p d rs = some d')
    (hp : stPlainB d.st = true) : stPlainB d'.st = true := by
  unfold linPoint at h
  split at h
  · obtain ⟨_, _, h⟩ := obind_ok h
    obtain ⟨⟨gU, d₁⟩, h1, h⟩ := obind_ok h
    dsimp only at h
    split at h
    · obtain ⟨y, h2, h⟩ := obind_ok h
      cases h
      exact newGroup_plain d₁ y.2 _ _ y.1 h2 (newGroup_plain d d₁ _ _ gU h1 hp)
    · obtain ⟨y, h2, h⟩ := obind_ok h
      cases h2
      cases h
      exact newGroup_plain d d₁ _ _ gU h1 hp
  · cases h

theorem behindU_st (p : Par) (d d' : St) (ids : Array ℕ) (h : behindU p d ids = some d') :
    d'.st = d.st := by
  unfold behindU at h
  split at h <;>
    (obtain ⟨_, _, h⟩ := obind_ok h
     obtain ⟨_, _, h⟩ := obind_ok h
     cases h
     rfl)

theorem laysRec_plain (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : laysRec p d rs = some d')
    (hp : stPlainB d.st = true) : stPlainB d'.st = true := by
  unfold laysRec at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := obind_ok h
  obtain ⟨d₁, h1, h⟩ := obind_ok h
  obtain ⟨rows, hr, h⟩ := obind_ok h
  exact addRowsAll_plain _ _ _ _ h (join_plain _ _ _ _ _ h1 hp)
    (mapM_all _ PlainRow (fun _ _ e => recGamma_plain e) _ _ hr)

theorem loc_plain (p : Par) (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (h : loc p d rs gs = some d') (hp : stPlainB d.st = true) : stPlainB d'.st = true := by
  unfold loc at h
  split at h
  · dsimp only at h
    obtain ⟨rows, hr, h⟩ := obind_ok h
    refine addRowsAll_plain _ _ _ _ h hp (mapM_all _ PlainRow (fun a b e => ?_) _ _ hr)
    obtain ⟨_, _, e⟩ := obind_ok e
    exact locX_plain e
  · cases h

theorem behindOmega_st (p : Par) (d d' : St) (ids : Array ℕ)
    (h : behindOmega p d ids = some d') : d'.st = d.st := by
  unfold behindOmega at h
  split at h <;>
    (obtain ⟨_, _, h⟩ := obind_ok h
     obtain ⟨_, _, h⟩ := obind_ok h
     cases h
     rfl)

theorem joins_plain (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : joins p d rs = some d')
    (hp : stPlainB d.st = true) : stPlainB d'.st = true := by
  unfold joins at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := obind_ok h
  obtain ⟨d₁, h1, h⟩ := obind_ok h
  split at h
  · obtain ⟨d₂, h2, h⟩ := obind_ok h
    exact join_plain _ _ _ _ _ h (join_plain _ _ _ _ _ h2 (join_plain _ _ _ _ _ h1 hp))
  · cases h
    exact join_plain _ _ _ _ _ h1 hp

theorem linZeta_plain (d d' : St) (rs : List Fmt.RoundView) (h : linZeta d rs = some d')
    (hp : stPlainB d.st = true) : stPlainB d'.st = true := by
  unfold linZeta at h
  split at h
  · cases h
    exact hp
  · cases h

theorem split_plain (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : split p d rs = some d')
    (hp : stPlainB d.st = true) : stPlainB d'.st = true := by
  unfold split at h
  dsimp only at h
  obtain ⟨row, hrow, h⟩ := obind_ok h
  have hR : PlainRow row := fold_plain hrow
  split at h
  · exact addRow_plain _ _ _ _ h hp (rowPlainB_iff.2 hR)
  · split at h
    · obtain ⟨mu, _, h⟩ := obind_ok h
      obtain ⟨G, _, h⟩ := obind_ok h
      obtain ⟨_, _, h⟩ := obind_ok h
      obtain ⟨⟨kappa, d₁⟩, h1, h⟩ := obind_ok h
      dsimp only at h
      obtain ⟨d₂, h2, h⟩ := obind_ok h
      have pO := part_plain row G.members true hR
      have pU := part_plain row G.members false hR
      exact addRow_plain _ _ _ _ h
        (addRow_plain _ _ _ _ h2 (takeMask_plain _ _ _ _ h1 hp) (rowPlainB_iff.2 ⟨pO.1, pO.2⟩))
        (rowPlainB_iff.2 ⟨pU.1, pU.2⟩)
    · obtain ⟨mu, hm, h⟩ := obind_ok h
      cases hm
  · cases h

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.eq_plain
#print axioms ProofFile.Honest.K12.Light.product_plain
#print axioms ProofFile.Honest.K12.Light.addLaid_plainRow
#print axioms ProofFile.Honest.K12.Light.foldl_plain
#print axioms ProofFile.Honest.K12.Light.part_plain
#print axioms ProofFile.Honest.K12.Light.recGamma_plain
#print axioms ProofFile.Honest.K12.Light.locX_plain
#print axioms ProofFile.Honest.K12.Light.fold_plain
#print axioms ProofFile.Honest.K12.Light.mapM_all
#print axioms ProofFile.Honest.K12.Light.addRowsFromAll_plain
#print axioms ProofFile.Honest.K12.Light.addRowsAll_plain
#print axioms ProofFile.Honest.K12.Light.linPoint_plain
#print axioms ProofFile.Honest.K12.Light.behindU_st
#print axioms ProofFile.Honest.K12.Light.laysRec_plain
#print axioms ProofFile.Honest.K12.Light.loc_plain
#print axioms ProofFile.Honest.K12.Light.behindOmega_st
#print axioms ProofFile.Honest.K12.Light.joins_plain
#print axioms ProofFile.Honest.K12.Light.linZeta_plain
#print axioms ProofFile.Honest.K12.Light.split_plain
