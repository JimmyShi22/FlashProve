-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/BaseB.lean: the facts in front of the closing of a segment that name none of
its challenges (`CloseBase`, Johnson/Desc/K10/Honest/Base.lean) AS ONE TEST WITH CODE, and a member: so
that the theorems there are not empty, and so that a record can be asked.

  `closeBaseB P s`   the test: it reads the four things of which the facts speak off the record, and
                     asks each fact as a Bool; `GroupOk` and `RowIn` by the library's own tests
                     (`groupOkB`, `rowInB`, Johnson/Desc/Means/TestsB.lean)
  `closeBase_of`, `closeBaseB_of`, `closeBaseB_iff`   it says yes just where the facts hold
  `close_yes_of`     so the block's decision says yes at every list of 2 + k rounds of the kind's shape
  `Toy.base_member`  it says yes at Johnson/Desc/First/Close/Law/CloseToys.lean's record: by
                     `decide +kernel`: Lean's kernel evaluates the test itself
  `Toy.all_yes`      so that record's block's decision says yes at every such list of rounds

Limits. One member here: no kept member in it, no sampled member and so no sample row, rows of single
entries alone (so `termsOk` is idle at it): a file beside the seal,
Johnson/Desc/K10/Honest/BaseToys.lean, has members with these. Of the block's decision alone (the
step: Johnson/Desc/K10/Honest/Step.lean). Nothing on soundness, completeness or hiding of the protocol.

-/
import Johnson.Desc.K10.Honest.Base
import Johnson.Desc.K10.Honest.FrontToy
import Johnson.Desc.Means.TestsBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.YesFree
open OnBytes OnBytes.Means VerifiableInference.Desc VerifiableInference.Desc.First.Close

/-- The facts at given data, as a Bool. -/
def baseAtB (P : Par) (s : Rec) (D : BaseData) : Bool :=
  s.owed.isNone &&
  decide (s.frame.next = .laterOrClose) && s.frame.moment == reqMoments D.L &&
  Ground.ok (Ground.beginRunL s.st s.frame.group) &&
  groupOkB s.st D.G &&
  ((Slice.runRows s.st D.G).toList.all fun r => rowInB s.st D.G r) &&
  ((Slice.runRows s.st D.G).toList.all fun r =>
    r.terms.toList.all fun t => t.part != .main || t.v.ok) &&
  P.rows == (Slice.runRows s.st D.G).size &&
  (Own.layoutOf s.st D.G).k == D.Gq.k && (Own.layoutOf s.st D.G).h == D.Gq.h &&
  P.k == D.Gq.k &&
  D.G.code == s.frame.shape.code && D.G.maskCode == s.frame.shape.maskCode &&
  (s.st.codes.mask.getD s.frame.shape.maskCode default).ell ==
    2 ^ ceilLog2 (s.st.codes.mask.getD s.frame.shape.maskCode default).ell &&
  decide ((Own.layoutOf s.st D.G).k + (Own.layoutOf s.st D.G).logEll ≤ 63) &&
  Own.foldShapeFits (D.S1 s) (D.F s) && Own.foldMaskFits (D.S1 s) (D.F s) D.m &&
  Ground.ok (Ground.spendAsMaskL (D.S1 s) D.m)

/-- **The test.** -/
def closeBaseB (P : Par) (s : Rec) : Bool :=
  match s.frame.shape.link[s.frame.link]?, s.frame.groups[s.frame.link]?, s.frame.mask,
      s.st.groups[s.frame.group]? with
  | some L, some Gq, some m, some G => baseAtB P s ⟨L, Gq, m, G⟩
  | _, _, _, _ => false

/-- **Where the test says yes the facts hold.** -/
theorem closeBase_of {P : Par} {s : Rec} (h : closeBaseB P s = true) : ∃ D, CloseBase P s D := by
  unfold closeBaseB at h
  split at h
  · rename_i L Gq m G h1 h2 h3 h4
    unfold baseAtB at h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
      Option.isNone_iff_eq_none, and_assoc, Bool.or_eq_true, bne_iff_ne] at h
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := h
    exact ⟨⟨L, Gq, m, G⟩, a1, h1, h2, ⟨a2, a3⟩, h3, a4, h4, groupOkB_iff.1 a5,
      fun r hr => rowInB_iff.1 (a6 r hr), fun r hr t ht hp => (a7 r hr t ht).resolve_left fun c => c hp,
      a8, ⟨a9, a10⟩, a11, a12, a13, a14, a15, a16, a17, a18⟩
  · cases h

/-- **Where the facts hold the test says yes.** -/
theorem closeBaseB_of {P : Par} {s : Rec} {D : BaseData} (H : CloseBase P s D) :
    closeBaseB P s = true := by
  unfold closeBaseB
  rw [H.link, H.group, H.mask, H.there]
  show baseAtB P s D = true
  unfold baseAtB
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    Option.isNone_iff_eq_none, and_assoc, Bool.or_eq_true, bne_iff_ne]
  exact ⟨H.owed, H.due.1, H.due.2, H.beginRun, groupOkB_iff.2 H.inOrder,
    fun r hr => rowInB_iff.2 (H.rowsIn r hr),
    fun r hr t ht => (Classical.em (t.part = .main)).elim (fun c => Or.inr (H.termsOk r hr t ht c))
      Or.inl, H.rows, H.kh.1, H.kh.2, H.stretch, H.code, H.maskCode, H.power, H.bits, H.shape,
    H.maskfits, H.spendAsMask⟩

/-- The test says yes just where the facts hold. -/
theorem closeBaseB_iff (P : Par) (s : Rec) : closeBaseB P s = true ↔ ∃ D, CloseBase P s D :=
  ⟨closeBase_of, fun ⟨_, H⟩ => closeBaseB_of H⟩

/-- **Where the test says yes the block's decision says yes at every list of 2 + k rounds of the
kind's shape.** -/
theorem close_yes_of {Cl : Type} {P : Par} {s : Rec} (h : closeBaseB P s = true)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (hl : rs.length = 2 + P.k)
    (hs : ShapedAll rs) : ∃ s', ((kind (Cl := Cl)) P).decide s rs gs = .ok s' := by
  obtain ⟨D, H⟩ := closeBase_of h
  exact close_yes_all H rs gs hl hs

namespace Toy

theorem base_member : closeBaseB P s = true := by decide +kernel

theorem all_yes (rs : List Fmt.RoundView) (hl : rs.length = 4) (hs : ShapedAll rs) :
    ∃ s', ((kind (Cl := Unit)) P).decide s rs [] = .ok s' :=
  close_yes_of base_member rs [] hl hs

end Toy

end ProofFile.Honest.K10.YesFree

#print axioms ProofFile.Honest.K10.YesFree.closeBase_of
#print axioms ProofFile.Honest.K10.YesFree.closeBaseB_iff
#print axioms ProofFile.Honest.K10.YesFree.close_yes_of
#print axioms ProofFile.Honest.K10.YesFree.Toy.base_member
#print axioms ProofFile.Honest.K10.YesFree.Toy.all_yes
