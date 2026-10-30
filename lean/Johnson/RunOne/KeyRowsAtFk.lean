-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyRowsAtFk.lean (AtFk holds «reads»: ReadsPinned at the shared chain's own three messages: a condition on the letters R, B and at_; the readings hold no book and no offset: off₂ · off₃ ARE THE TABLES' LETTERS; t₁ is the plan's number outright; AtFk holds that the one-time plan's codes are the sized key's, ArrOk at the shared chain's own messages, and that off₃ leaves I's and V's trees' numbers; start := the description's own start₃ · src := the sources' test at the key file's own test's block). THE TWO SEAMS AND THE END, AT THE KEY FILE's OWN DESCRIPTION F := descriptionFromSource X N P, AT THE MAKER's OWN THREE FRAMES (frameAt D (allOf D) D.keyⱼ ftⱼ) AND AT THE THREE READINGS OF ONE BASE
(KeyOneReading.lean: BaseSt): IN THE LETTERS OF THE TOP's RowsOwed.seam₁ | seam₂ | ends (Johnson/Top/Fire/Code/KeyOfRows.lean): so that THE SEAMS' OWN premises are seen met together (NOT the laws of the blocks: of these nothing is said here): Agree₁ | Agree (agree₁_of_baseSt | agree_of_baseSt) · Starts (starts_fkD) · what the seam spends of the first chain's last book-keeping (last₁_gives) · «the two frames read the oracles
alike» (rfl at these frames) · the description's own start₂ | start₃.
  AtFk              WHAT IS LEFT AS A PREMISE, seven fields: ON PUBLIC VALUES: form · lin · codes (all three follow from the description's own tests on the plan: here and in KeyAtFkMore.lean) · ON THE LETTERS: orc (the base's numbers are the first chain's plan's: SPENT BY NO THEOREM HERE: for the laws) · arr (what PIN k pins is the
                    witness's message k, at 0 · 2 · 3 · 4 · 5) · reads (what the rows read of 3 · 4 · 5 is what PIN pins) · off (off₃ leaves I's and V's trees' numbers)
  lin_of_fileOk · form_of_fileOk   PROVED: two of AtFk's facts on values FOLLOW FROM THE DESCRIPTION's OWN fileOk
  seam₁_at_fk · seam₂_at_fk · ends_at_fk   PROVED
Limits. The tables' other letters stay letters (the base · at_ · R · enc · rad · coll). Whether a promise is ever met is not shown. Nothing on soundness.

-/
import Johnson.RunOne.KeySeam1
import Johnson.RunOne.KeySeam2On
import Johnson.Desc.Sound.Tiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows1 (plan₁ n₁ on₁ L₁)

section
variable {Cells M Smp Rec : Type} [Inhabited Cells] [Inhabited M] (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD)
  (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (enc : (Nat → OnBytes.E) → Nat → OnBytes.E) (rad : Nat)
  (coll : Strs → Rec → Prop) (off₂ off₃ : Nat → Nat)

/-- The one-time chain's public values, the shape and the codes, off what the description is made of. -/
abbrev oneAt : OneTime := X.Y.k.oneTime
abbrev shapeAt : LinShape := X.chains.made.sized.key.once.shape
abbrev codesAt : Codes := X.chains.made.sized.key.codes

theorem masks_of_form (S : LinShape) (h : LKFU.Shape23.formOk S = true) : S.masksAhead = true := by
  simp only [LKFU.Shape23.formOk, Bool.and_eq_true] at h
  exact h.1.1

/-- The description's test on the plan that ties chains holds each of its clauses by name. -/
theorem fileOk_all (h : (descriptionFromSource X N P).fileOk = true) : ∃ r₁ r₂ r₃, (fileClauses X N P r₁ r₂ r₃).all (·.2) = true := by
  have h' : ((fileClauses X N P _ _ _).all (·.2) && openedInBlocks _ _) = true := h
  exact ⟨_, _, _, (Bool.and_eq_true_iff.1 h').1⟩

/-- **The one-time chain's shape of the test on the table IS the sized key's**: out of fileOk (clauses of shapeClauses). -/
theorem lin_of_fileOk (h : (descriptionFromSource X N P).fileOk = true) : (oneAt X).lin = shapeAt X := by
  obtain ⟨r₁, r₂, r₃, ha⟩ := fileOk_all X N P h
  have hm : ∀ c ∈ shapeClauses X.Y.k (shapeAt X), c.2 = true := fun c hc =>
    List.all_eq_true.1 ha c (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hc))))))
  have h10 := hm _ (List.mem_of_getElem? (l := shapeClauses X.Y.k (shapeAt X)) (i := 10) rfl)
  have h11 := hm _ (List.mem_of_getElem? (l := shapeClauses X.Y.k (shapeAt X)) (i := 11) rfl)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h10 h11
  exact h10.2.trans h11.symm

/-- **The shape has the form that the book-keeping bears**: out of fileOk (clauses of shapeClauses and sourceClauses). -/
theorem form_of_fileOk (h : (descriptionFromSource X N P).fileOk = true) : LKFU.Shape23.formOk (shapeAt X) = true := by
  obtain ⟨r₁, r₂, r₃, ha⟩ := fileOk_all X N P h
  have hm : ∀ c ∈ shapeClauses X.Y.k (shapeAt X), c.2 = true := fun c hc =>
    List.all_eq_true.1 ha c (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hc))))))
  have hf : ∀ c ∈ sourceClauses X.Y, c.2 = true := fun c hc =>
    List.all_eq_true.1 ha c (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hc))))))
  have h11 := hm _ (List.mem_of_getElem? (l := shapeClauses X.Y.k (shapeAt X)) (i := 11) rfl)
  have h8 := hf _ (List.mem_of_getElem? (l := sourceClauses X.Y) (i := 8) rfl)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h8 h11
  unfold LKFU.Shape23.formOk
  rw [h11, h8.1.1.2, h8.1.2, h8.2]
  rfl

/-- **What is left as a premise.** -/
structure AtFk : Prop where
  form : LKFU.Shape23.formOk (shapeAt X) = true
  lin : (oneAt X).lin = shapeAt X
  codes : (oneAt X).codes = codesAt X
  orc : B.orc₁ = (plan₁ (oneAt X)).orc
  arr : ArrOk B.h₂ at_ [0, 2, 3, 4, 5]
  reads : ReadsPinned B.h₂ at_ R [3, 4, 5]
  off : ∀ k ∈ [0, 2], off₃ (at_ k).1 = (at_ k).1

abbrev Fk : FileDescription Xi := descriptionFromSource X N P
abbrev fr₁ : Frame := frameAt D (allOf D) D.key₁ 0
abbrev fr₂ : Frame := frameAt D (allOf D) D.key₂ 0
abbrev fr₃ : Frame := frameAt D (allOf D) D.key₃ (Fk X N P).lastChainFirstTreeNumber

abbrev On₁ := on₁ (Fk X N P) (fr₁ D) B.h₁ at_ (oneAt X) R coll
abbrev Cl₁ := L₁ (Fk X N P) (fr₁ D) B.h₁ at_ (oneAt X) R
abbrev On₂ := on₂ (Fk X N P) (fr₂ D) B.h₂ at_ (shapeAt X) (plan₁ (oneAt X)) R enc rad (oneAt X).given.plan.samples coll (last₁At (oneAt X)) off₂
abbrev Cl₂ := L₂ (Fk X N P) (fr₂ D) B.h₂ at_ (shapeAt X) (plan₁ (oneAt X)) R enc rad
abbrev On₃ := on₃ (Fk X N P) (fr₃ X N P D) B.h₃ at_ (shapeAt X) (plan₁ (oneAt X)) R (oneAt X).given.plan.samples [0] coll (srcOk (ownTest P)) off₂ off₃ ((oneAt X).ranges.stages.length + 2)
abbrev Cl₃ := L₃ (Fk X N P) (fr₃ X N P D) B.h₃ at_ (shapeAt X) (plan₁ (oneAt X)) R

/-- **RowsOwed.seam₁, at the boundary 19.** -/
theorem seam₁_at_fk (H : AtFk X B at_ R off₃)
    (b : (Xi × FirstState) × (EAll D (allOf D)).Str) (h : On₁ X N P D B at_ R coll 19 b) :
    On₂ X N P D B at_ R enc rad coll off₂ 0 ((b.1, (Fk X N P).start₂ b.1.1), b.2) ∧
      (Cl₂ X N P D B at_ R enc rad 0 ((b.1, (Fk X N P).start₂ b.1.1), b.2) → Cl₁ X N P D B at_ R 19 b) :=
  seam₁_rows (F := Fk X N P) (Fr₁ := fr₁ D) (Fr₂ := fr₂ D) (S := shapeAt X) (one := oneAt X) (R := R) (enc := enc) (rad := rad) (coll := coll) (off₂ := off₂)
    (codesAt X) (agree₁_of_baseSt B at_ _ (fun k hk => by
      have hk5 : ∀ k ∈ pinned seam, k ∈ [0, 2, 3, 4, 5] := by decide
      have hk3 : ∀ k ∈ pinned seam, k < 3 := by decide
      have e : B.arr (at_ k).1 (at_ k).2 = k := H.arr k (hk5 k hk)
      rw [e]
      exact hk3 k hk)) H.form H.codes H.lin (H.arr.mono (by decide)) H.reads b.1.1 b.1.2 b.2 b.2 rfl h

/-- **RowsOwed.seam₂, at the boundary 12.** -/
theorem seam₂_at_fk (H : AtFk X B at_ R off₃) (b : ((Xi × FirstState) × St₂) × (EAll D (allOf D)).Str) (h : On₂ X N P D B at_ R enc rad coll off₂ 12 b) :
    (∀ s, ((Fk X N P).start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s → On₃ X N P D B at_ R coll off₂ off₃ 0 (((b.1.1.1, b.1.1.2, b.1.2), s), b.2)) ∧
      ((∃ s, ((Fk X N P).start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s ∧ Cl₃ X N P D B at_ R 0 (((b.1.1.1, b.1.1.2, b.1.2), s), b.2)) → Cl₂ X N P D B at_ R enc rad 12 b) :=
  seam₂_rows (F := Fk X N P) (Fr₂ := fr₂ D) (Fr₃ := fr₃ X N P D) (S := shapeAt X) (K₁ := plan₁ (oneAt X)) (R := R) (enc := enc) (rad := rad) (a := (oneAt X).given.plan.samples) (idx := [0]) (coll := coll) (last₁ := last₁At (oneAt X)) (src := srcOk (ownTest P)) (off₂ := off₂) (off₃ := off₃) (t₁ := (oneAt X).ranges.stages.length + 2)
    (codesAt X) (fun x s₁ s₂ => (Fk X N P).start₃ x s₁ s₂) (agree_of_baseSt B at_ (codesAt X) (shapeAt X) (masks_of_form _ H.form) _ (starts_fkD X N P)) H.lin (starts_fkD X N P)
    (last₁_gives (oneAt X)) H.off b.1.1.1 b.1.1.2 b.1.2 b.2 b.2 rfl h

/-- **RowsOwed.ends, at the boundary 4.** -/
theorem ends_at_fk (b : ((Xi × FirstState × St₂) × St₃) × (EAll D (allOf D)).Str) (h : On₃ X N P D B at_ R coll off₂ off₃ 4 b) : Cl₃ X N P D B at_ R 4 b :=
  ends_rows (F := Fk X N P) (Fr₃ := fr₃ X N P D) (G₃ := B.h₃) (at_ := at_) (S := shapeAt X) (K₁ := plan₁ (oneAt X)) (R := R) (a := (oneAt X).given.plan.samples) (idx := [0]) (coll := coll) (src := srcOk (ownTest P)) (off₂ := off₂) (off₃ := off₃) (t₁ := (oneAt X).ranges.stages.length + 2) b h

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.lin_of_fileOk
#print axioms Johnson.RunOne.KeyRows23.form_of_fileOk
#print axioms Johnson.RunOne.KeyRows23.seam₁_at_fk
#print axioms Johnson.RunOne.KeyRows23.seam₂_at_fk
#print axioms Johnson.RunOne.KeyRows23.ends_at_fk
