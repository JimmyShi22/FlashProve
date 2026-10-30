-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRecBack21.lean: ROW 2.1 OF THE KEY FILE's TABLE OF JOINTS:
THE TIE ON THE RECORD (hrec of Johnson/RunOne/KeyTies21Lib.lean: collTie_lib | decTie_lib): THE KEY
THAT IS WRITTEN OF A RECORD OF THE LIBRARY's (OnBytes/Slice/KeyOfRec.lean: keyOf), READ AS K14's LAW
OF «LIN point» READS A KEY (recK: seedsFn | recOf), IS THAT RECORD AT THE CORRESPONDING SEED (trS,
Johnson/Desc/Sound/SampleAlong.lean): by keyOf_point | keyOf_beta | keyOf_record and numOf_rowNo
(Johnson/Desc/K14/Law/DecTie.lean).
OBJECT: recK p err eM rank (keyOf (fun β : NZ => β.val) r) · USER: hrec at a reading whose recOf z =
some r only where z.1.1.key = keyOf … r (at recOf x := «the r with keyInstanceOfOutOfDomainSample r = x», where keyInstanceOfOutOfDomainSample
lays keyOf r as the instance's key) · LETTERS: p err eM rank; r.
  recK_keyOf     recK … (keyOf … r) = (trS … r.1, r.2): at EVERY record r of the library's: no
    premise
  hrec_of_keyOf  so hrec, from «the reading's record writes the instance's key»
What is not claimed. That the instance's key IS keyOf of the reading's record (the filling's:
keyInstanceOfOutOfDomainSample's text). Nothing on soundness.

-/
import Johnson.RunOne.KeyTies21Lib
import Johnson.Desc.K14.Law.DecTie
import OnBytes.Slice.KeyOfRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc
open _root_.Desc.Plain (Par)
open _root_.Desc.K14.Law (ixLib trS seedsFn recOf ptFn numOf_rowNo)
open OnBytes.Slice (GE NZ keyOf keyOf_point keyOf_beta keyOf_record readE)

section
variable (p : Par) (err eM : Nat)
  (rank : ((Fin p.S.fold.index.v → Bool) → Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) →
      Cb.Gl.E) → Nat)

/-- **The written key, read back, is the record at the corresponding seed.** -/
theorem recK_keyOf (r : (ixLib p.S.fold eM rank).Rec) :
    recK p err eM rank (keyOf (v := p.S.fold.index.v) (lg := p.S.fold.index.cubeBits) (s :=
        p.S.fold.index.answers) (fun β : NZ => β.val) r) =
      (trS p.S.fold.index err r.1, r.2) := by
  refine Prod.ext (funext fun a => Prod.ext (funext fun t => ?_) ?_) (funext fun x => ?_)
  · have h := keyOf_point (v := p.S.fold.index.v) (fun β : NZ => β.val) r a
    have h3 := congrArg (fun l : List GE => l[t.val]?) h
    simp only [List.getElem?_map, List.getElem?_ofFn, dif_pos t.isLt] at h3
    obtain ⟨w, hw, e⟩ := Option.map_eq_some_iff.1 h3
    have e2 : ((keyOf (v := p.S.fold.index.v) (fun β : NZ => β.val) r).seeds.getD a.val
        default).z.getD t.val zeroE = w := by
      rw [List.getD_eq_getElem?_getD, hw]
      rfl
    exact (congrArg readE e2).trans e
  · exact keyOf_beta (v := p.S.fold.index.v) (fun β : NZ => β.val) r a
  · show readE ((keyOf (fun β : NZ => β.val) r).record.getD (_root_.Desc.K14.Law.numOf
      p.S.fold.index.v x.1 * p.S.fold.index.answers + x.2.val) zeroE) = r.2 x
    rw [numOf_rowNo]
    exact keyOf_record (fun β : NZ => β.val) r x.1 x.2

/-- **hrec, from «the reading's record writes the instance's key».** -/
theorem hrec_of_keyOf {Cells M Smp : Type} (G₂ : Reading (P₂ × St₂) Cells M Smp (ixLib p.S.fold eM
    rank).Rec)
    (hkey : ∀ z r, G₂.recOf z = some r → z.1.1.key =
      keyOf (v := p.S.fold.index.v) (lg := p.S.fold.index.cubeBits) (s := p.S.fold.index.answers)
          (fun β : NZ => β.val) r) :
    ∀ z r, G₂.recOf z = some r → recK p err eM rank z.1.1.key = (trS p.S.fold.index err r.1, r.2) :=
        fun z r h => by
  rw [hkey z r h]
  exact recK_keyOf p err eM rank r

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.recK_keyOf
#print axioms Johnson.RunOne.KeyRows23.hrec_of_keyOf
