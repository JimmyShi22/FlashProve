-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyTies21Lib.lean: ROW 2.1 OF THE KEY FILE's TABLE OF JOINTS:
THE TWO TIES ON LETTERS CollTie | DecTie (Johnson/RunOne/KeyGood21.lean) AT THE LIBRARY's OWN
RECORD: Rec := the record of ixLib p.S.fold eM rank (Johnson/Desc/Sound/SampleAlong.lean:
K14's law's typed index with THE LIBRARY's sample map recZ, whose
seeds' factors are non-zero BY TYPE) · Cells := a decoded table. BY CALLS: that file's dcd_lib |
coll_lib (K14's law's decoder and collision at the seed trS ρ ARE the library's at ρ; over
Johnson/Desc/K14/Law/DecAlong.lean) · CellsTie.lean · dec_overF (Cb.ldFc_overF).
WHY: at the name's own configuration (The21AtName: Rec := RecFull · decT := configurationOfStoredTable.dcd · coll
:= configurationOfStoredTable.coll at DN := frS.toDecR frZ 402653181) the record is the library's. FROM HERE TO DN, NOT
CALLED HERE (the two files lie in Johnson/Desc/Sound/):
StoredAlong.lean: decROf_ix : (decROf S eM).ix = ixLib S eM (rankLib S) := rfl · tab_cells ·
dcdR_cells | collR_cells · FullClosed.lean: full_of_index : S.index = ⟨⟨32, 402653184, 44040191⟩,
11, 1, sb⟩ → decROf S 2852142980 = frS.toDecR frZ 402653181.
ON EMPTINESS: as KeyRow21.lean's head: NO MEMBER OF on₂ … 1 IS SHOWN BY ANYBODY.
OBJECT: CollTie | DecTie at these types · USER: point_back₂_lib | _at | _rounds | _key | _seat
(hcoll | hdec) · LETTERS: the tables' but Rec | Cells; err eM rank.
  collTie_lib   PROVED FROM: hrec · hcl
  decTie_lib    PROVED FROM: hrec · hdc · htab · four public facts
LEFT: hrec [bare ∀ z r under «recOf z = some r»]: the key's seeds and answers, read, ARE (trS r.1,
r.2): at recOf x := «the r with keyInstanceOfOutOfDomainSample r = x»: what keyOf writes is read back:
KeyOfRecBack.lean's matter · hcl | hdc [bare ∀]: definitions at the filling, through tab_cells ·
htab [bare ∀ under «c is base-valued»]: as KeyTies21.lean's head.
Nothing on soundness.
-/
import Johnson.RunOne.KeyTies21
import Johnson.Desc.Sound.SampleAlong

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound
open _root_.Desc.Plain (Par)
open _root_.Desc.K14.Law (ixOf2 ixLib trS dcd_lib coll_lib tabF bitsOf tabOf DecX2 TabX2 colsOf
    tabOf_cells collAt dcdAt dec_overF tabF_lift)
open VerifiableInference.Desc.K13.Law (ρg)
open OnBytes.Slice (GE GF codeOf)

section
variable {XI M Smp : Type} (F : FileDescription XI) (Fr₂ : Frame) (p : Par) (err eM : Nat)
  (rank : ((Fin p.S.fold.index.v → Bool) → Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) →
      Cb.Gl.E) → Nat)
  (G₂ : Reading (P₂ × St₂) ((ixLib p.S.fold eM rank).Row × Fin p.S.fold.index.code.ell → GE) M Smp
      (ixLib p.S.fold eM rank).Rec) (at_ : Where)
  (K₁ : KPlan) (R : KRead ((ixLib p.S.fold eM rank).Row × Fin p.S.fold.index.code.ell → GE) M) (enc
      : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → (ixLib p.S.fold eM rank).Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)

/-- **CollTie at the library's own record.** -/
theorem collTie_lib (hrec : ∀ z r, G₂.recOf z = some r → recK p err eM rank z.1.1.key = (trS
    p.S.fold.index err r.1, r.2))
    (hcl : ∀ y r, (ixLib p.S.fold eM rank).Coll (tabF OnBytes.Model.Reading.gl p.S.fold.index
        (colsOf y.cell)) r.1 → coll y r) :
    CollTie F Fr₂ G₂ at_ p K₁ R enc rad a coll last₁ off₂ err eM rank := by
  intro x hx hC
  have hf : Free₂ F G₂ at_ p.S K₁ R coll last₁ off₂ 1 x.1 (strsOf Fr₂ x.2) := by
    rcases hx with hn | ⟨_, _, h3, _⟩
    · exact absurd trivial hn
    · exact h3
  obtain ⟨r, hr, hnc⟩ := hf.record
  have hc : collAt p err eM rank (strsOf Fr₂ x.2).cell (recK p err eM rank x.1.1.1.key) := by
    unfold collAt
    rw [← tabOf_cells]
    exact hC
  rw [hrec _ _ hr] at hc
  exact hnc (hcl _ _ ((coll_lib p err eM rank (strsOf Fr₂ x.2).cell r.1 r.2).1 hc))

/-- **DecTie at the library's own record.** -/
theorem decTie_lib (hrec : ∀ z r, G₂.recOf z = some r → recK p err eM rank z.1.1.key = (trS
    p.S.fold.index err r.1, r.2))
    (hdc : ∀ cell r, G₂.decT cell r = (ixLib p.S.fold eM rank).dec (tabF OnBytes.Model.Reading.gl
        p.S.fold.index (colsOf cell)) r)
    (htab : ∀ (c : (ixLib p.S.fold eM rank).Row × Fin p.S.fold.index.code.ell → GE) (r k : Nat) (hk
        : k < p.S.fold.index.code.ell),
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
    rw [hr, Option.bind_some, hdc]
    have hd : dcdAt p err eM rank (strsOf Fr₂ x.2).cell (recK p err eM rank x.1.1.1.key) = some U :=
        by
      unfold dcdAt
      rw [← tabOf_cells]
      exact hU
    rw [hrec _ _ hr] at hd
    exact (dcd_lib p err eM rank (strsOf Fr₂ x.2).cell r.1 r.2).symm.trans hd
  · have hk' : k < p.S.fold.index.code.ell := Nat.lt_of_lt_of_le hk hell
    rw [htab U r' k hk' hbase hr']
    unfold TabX2
    rw [hU]
    show _ = (if h : k < p.S.fold.index.code.ell then U (bitsOf p.S.fold.index.v r', ⟨k, h⟩) else 0)
    rw [dif_pos hk']
    rfl

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.collTie_lib
#print axioms Johnson.RunOne.KeyRows23.decTie_lib
