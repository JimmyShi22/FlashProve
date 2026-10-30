-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyTies21.lean: ROW 2.1 OF THE KEY FILE's TABLE OF JOINTS:
THE TWO TIES ON LETTERS CollTie | DecTie (Johnson/RunOne/KeyGood21.lean) CUT DOWN TO FOUR EQUATIONS
ON THE TABLES' LETTERS, BY CALLS OF K14's FILES' OWN TIES (Johnson/Desc/K14/Law/CellsTie.lean:
colsOf · tabOf_cells · collAt · dcdAt; with DecTie.lean's ix_eq | coll_tie | dcd_tie these ARE the
library's DecR.coll | DecR.dcd at decROf p.S.fold err eM) and of dec_overF
(Johnson/Desc/K14/Law/BaseValued.lean: a corollary of Cb.ldFc_overF: a decoded table is
base-valued).
THE TYPES ARE FILLED: Rec := the library's record at ixOf2 p.S.fold err eM rank · Cells := a decoded
table (Row × Fin ell → GE).
ON EMPTINESS: as KeyRow21.lean's head: NO MEMBER OF on₂ … 1 IS SHOWN BY ANYBODY.
OBJECT: CollTie | DecTie at these types · USER: point_back₂_lib | _at | _rounds | _key | _seat
(hcoll | hdec) · LETTERS: the tables' but Rec | Cells; err eM rank.
  recK            the key's seeds and the record's answers, read: the library's record
    [CellsTie.lean's recAt, at a key]
  collTie_of_fill PROVED FROM: hrec (the reading's record IS the key's, read) · hcl (the tables'
    coll holds where the library's collision does)
  decTie_of_fill  PROVED FROM: hrec · hdc (the reading's decT IS the library's decoder) · htab
    (KRead.tab reads a BASE-VALUED table's entry as that entry) · four public facts (logN ≤ 32 · the
    code has room · eM below the distance · the matrix's places lie in a row's message)
LEFT, EACH WITH ITS PAYER: hrec [bare ∀ z r under «recOf z = some r»]: at the filling recOf x :=
the r with keyInstanceOfOutOfDomainSample r = x: KeyOfRecBack.lean's matter · hcl | hdc [bare ∀]: at coll := conf.coll
∘ yOf · decT := conf.dcd ∘ yOf they are DecTie.lean's coll_tie | dcd_tie WHERE DN = decROf …: the
numbers, and Z: K14's files' sampleOf against frZ · htab [bare ∀ c r k under «c is base-valued»]: an
instance that is not degenerate: tab c r k := the least word of (c (bitsOf v r, k)).c0.
Nothing on soundness.
-/
import Johnson.RunOne.KeyGood21
import Johnson.Desc.K14.Law.CellsTie
import Johnson.Desc.K14.Law.BaseValuedAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open _root_.Desc.Plain (Par)
open _root_.Desc.K14.Law (ixOf2 tabF seedsFn recOf bitsOf tabOf DecX2 TabX2 colsOf tabOf_cells
    collAt dcdAt dec_overF tabF_lift)
open VerifiableInference.Desc.K13.Law (ρg)
open OnBytes.Slice (GE GF codeOf)

section
variable {XI M Smp : Type} (F : FileDescription XI) (Fr₂ : Frame) (p : Par) (err eM : Nat)
  (rank : ((Fin p.S.fold.index.v → Bool) → Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) →
      Cb.Gl.E) → Nat)

/-- The key's seeds and the record's answers, read: the library's record. -/
noncomputable def recK (key : TableKey) : (ixOf2 p.S.fold err eM rank).Rec :=
  (seedsFn OnBytes.Model.Reading.gl p.S.fold.index key, recOf p.S.fold.index fun k =>
      OnBytes.Model.Reading.gl.val (key.record.getD k zeroE))

variable (G₂ : Reading (P₂ × St₂) ((ixOf2 p.S.fold err eM rank).Row × Fin p.S.fold.index.code.ell →
    GE) M Smp (ixOf2 p.S.fold err eM rank).Rec) (at_ : Where)
  (K₁ : KPlan) (R : KRead ((ixOf2 p.S.fold err eM rank).Row × Fin p.S.fold.index.code.ell → GE) M)
      (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → (ixOf2 p.S.fold err eM rank).Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat →
      Nat)

/-- **CollTie, from two equations on the letters.** -/
theorem collTie_of_fill (hrec : ∀ z r, G₂.recOf z = some r → r = recK p err eM rank z.1.1.key)
    (hcl : ∀ y r, collAt p err eM rank y.cell r → coll y r) :
    CollTie F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ err eM rank := by
  intro x hx hC
  have hf : Free₂ F G₂ at_ p.S K₁ R coll last₁ off₂ 1 x.1 (strsOf Fr₂ x.2) := by
    rcases hx with hn | ⟨_, _, h3, _⟩
    · exact absurd trivial hn
    · exact h3
  obtain ⟨r, hr, hnc⟩ := hf.record
  refine hnc (hcl _ _ ?_)
  rw [hrec _ _ hr]
  unfold collAt
  rw [← tabOf_cells]
  exact hC

/-- **DecTie, from three equations on the letters and four public facts.** -/
theorem decTie_of_fill (hrec : ∀ z r, G₂.recOf z = some r → r = recK p err eM rank z.1.1.key)
    (hdc : ∀ cell r, G₂.decT cell r = dcdAt p err eM rank cell r)
    (htab : ∀ (c : (ixOf2 p.S.fold err eM rank).Row × Fin p.S.fold.index.code.ell → GE) (r k : Nat)
        (hk : k < p.S.fold.index.code.ell),
      (∀ n, ∃ b : GF, c n = algebraMap GF GE b) → r < 2 ^ p.S.fold.index.v → ρg.val (ofF (R.tab c r
          k)) = c (bitsOf p.S.fold.index.v r, ⟨k, hk⟩))
    (ha : p.S.fold.index.code.logN ≤ 32) (hroom : p.S.fold.index.code.r + p.S.fold.index.code.ell ≤
        2 ^ p.S.fold.index.code.logN)
    (he : eM < 2 ^ p.S.fold.index.code.logN - (p.S.fold.index.code.r + p.S.fold.index.code.ell) + 1)
    (hell : p.S.matrixRows * 2 ^ p.S.kLo ≤ p.S.fold.index.code.ell) :
    DecTie F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ err eM rank := by
  intro x hx hD
  have hf : Free₂ F G₂ at_ p.S K₁ R coll last₁ off₂ 1 x.1 (strsOf Fr₂ x.2) := by
    rcases hx with hn | ⟨_, _, h3, _⟩
    · exact absurd trivial hn
    · exact h3
  obtain ⟨r, hr, -⟩ := hf.record
  obtain ⟨U, hU⟩ := Option.isSome_iff_exists.1 hD
  have hbase : ∀ n, ∃ b : GF, U n = algebraMap GF GE b := by
    have hU' := hU
    rw [tabF_lift] at hU'
    exact dec_overF (codeOf p.S.fold.index.code) ha hroom (ixOf2 p.S.fold err eM rank) rfl he _ _ U
        hU'
  refine ⟨U, ?_, fun r' k hr' hk => ?_⟩
  · unfold cellsAt
    rw [hr, Option.bind_some, hdc, hrec _ _ hr]
    unfold dcdAt
    rw [← tabOf_cells]
    exact hU
  · have hk' : k < p.S.fold.index.code.ell := Nat.lt_of_lt_of_le hk hell
    rw [htab U r' k hk' hbase hr']
    unfold TabX2
    rw [hU]
    show _ = (if h : k < p.S.fold.index.code.ell then U (bitsOf p.S.fold.index.v r', ⟨k, h⟩) else 0)
    rw [dif_pos hk']

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.collTie_of_fill
#print axioms Johnson.RunOne.KeyRows23.decTie_of_fill
