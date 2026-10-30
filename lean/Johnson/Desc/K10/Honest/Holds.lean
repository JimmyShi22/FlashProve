-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/Holds.lean: THE VALUES' HALF OF THE CLOSING OF A SEGMENT, FROM THE FACTS ON THE
RECORD IN FRONT: Johnson/Desc/K10/Honest/Values.lean's `close_holds` with its premises on form paid by
`CloseBase` (Johnson/Desc/K10/Honest/Base.lean). A theorem; no prover's moves are named (`foldQK`: the
other house's honest round polynomials).

What is said (`closeBase_holds`). Let the facts `CloseBase P s D` hold of the record s in front of the
block; let a stage st of the library have the group's four numbers; let every row that the test takes in
hold of words m, at the statement in front. Then at EVERY element x that "BAT" may draw the batching
returns a row, and for all rounds "FOLD epsilon" and "FOLD round" that show what the shared fold's
second core says (the first scalar; the honest round polynomials with the kept forms' value), at a fresh
table that pairs with the hiding polynomial's coefficients W, THE SINGLE ROWS THAT THE FOLD RETURNS ARE
TRUE of the folded message, their kept forms with them.

By: `close_holds` (Values.lean); `batch_returns`, `batch_rowfits` (RowFits.lean);
`says_extends`, `extends_begun`, `begun_group`, `GroupOk.extends`, `RowIn.extends`, `layoutOf_extends`
(Johnson/Desc/Means/Keeps.lean); `layout_eq` (Means/Layout.lean); `layoutOf_same` (Base.lean);
`spent_extends` (Johnson/Desc/First/Close/Law/StBehind.lean); `batch_agrees`, `foldRowFits_agrees`
(Johnson/Desc/Own/BatchAgree.lean, FoldAgree.lean).

Limits. It stands over five other files (Johnson/Prover/Link/FoldEnc, FormFold, FormFoldLaws,
FoldHolds, FoldKept).
 That the single rows of the conclusion are those that the block's decision lays into
the frame: Leaves.lean. That a fresh table pairs, and that a prover's rounds show these polynomials,
are premises; the fresh table φ is a letter (Values.lean's Limits). That the words are what was
committed to is not spoken of. Nothing on soundness, completeness or hiding of the protocol.

-/
import Johnson.Desc.K10.Honest.Values
import Johnson.Desc.K10.Honest.Base
import Johnson.Desc.Own.FoldAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.Values
open OnBytes OnBytes.Means OnBytes.Slice Johnson.Prover.Link H2K.ClaimSays Cb
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par Rec)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase layoutOf_same)

/-- **FROM THE FACTS IN FRONT, AND ROWS THAT HOLD, THE SINGLE ROWS THAT THE FOLD RETURNS ARE TRUE.** -/
theorem closeBase_holds {P : Par} {s : Rec} {D : BaseData} (H : CloseBase P s D) (st : Sg)
    (nk : D.Gq.k = st.h + st.g) (nh : D.Gq.h = st.h)
    (nl : 2 ^ (Own.layoutOf s.st D.G).logEll = st.C.l)
    (nz : 2 ^ (Own.layoutOf s.st D.G).logEllZk = st.Z.l) (m : Words GE)
    (hs : AllSay rdE s.st (runRows s.st D.G).toList m) (x : E) :
    ∃ row, Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩ x = some row ∧
      ∀ (rE : Fmt.RoundView) (rR : List Fmt.RoundView) (φ : st.cFr.J → GE)
        (W : HIdx (sVars GE 2 (st.h + st.g)) → GE) (γ : HPt (sVars GE 2 (st.h + st.g))),
        Pairs st st.Z.l W φ →
        readE ((sentOf rE).getD 0 zeroE) = hMu (sVars GE 2 (st.h + st.g)) W →
        Shows (st.h + st.g) rR (foldQK st (vecG st row)
          (msgOf st (tablesOf (D.S1 s) (Own.layoutOf s.st D.G) m)) W (readE (drawnOf rE))
          (keptVal (keptLen (D.S1 s)) (tablesOf (D.S1 s) (Own.layoutOf s.st D.G) m).kept row.kept)
          γ) γ →
        ∑ j, vecS st (foldOutAt (D.S1 s) (D.F s) row D.m (rE :: rR)) j *
              foldMsg st (msgOf st (tablesOf (D.S1 s) (Own.layoutOf s.st D.G) m)) φ
                (sPt 2 (st.h + st.g) γ) j +
            keptVal (keptLen (D.S1 s)) (tablesOf (D.S1 s) (Own.layoutOf s.st D.G) m).kept
              (foldOutAt (D.S1 s) (D.F s) row D.m (rE :: rR)).kept =
          readE (foldOutAt (D.S1 s) (D.F s) row D.m (rE :: rR)).target := by
  have hE := extends_begun s.st s.frame.group D.G
  have hc : (D.S1 s).codes = s.st.codes := hE.codes
  have hG' := begun_group s.st s.frame.group D.G H.there
  have hOk' : GroupOk (D.S1 s) { D.G with inRun := true, rows := #[] } :=
    H.inOrder.extends hE rfl rfl rfl rfl
  have eL := layoutOf_same H.there
  have hL' : (D.S1 s).layout s.frame.group = some (Own.layoutOf s.st D.G) := by
    show (Slice.begun s.st s.frame.group D.G).layout s.frame.group = _
    rw [layout_eq _ _ _ hG', eL,
      layoutOf_extends (G' := { D.G with inRun := true, rows := #[] }) hE H.inOrder rfl rfl rfl rfl]
  have hr' : ∀ r ∈ (runRows s.st D.G).toList,
      RowIn (D.S1 s) { D.G with inRun := true, rows := #[] } r :=
    fun r h => RowIn.extends (G := D.G) hE (fun _ c => c) (H.rowsIn r h)
  have hs' : AllSay rdE (D.S1 s) (runRows s.st D.G).toList m :=
    fun r h => (says_extends rdE hE (H.rowsIn r h) m).2 (hs r h)
  obtain ⟨row, hrow⟩ := RowFit.batch_returns s.frame.group (runRows s.st D.G) x hG' hL' hOk' hr'
  have hb : Bat.combine (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩ x =
      some row := (Own.batch_agrees _ _ _ _).trans hrow
  have e2 : ((D.S1 s).codes.mask.getD s.frame.shape.maskCode default).ell =
      2 ^ (Own.layoutOf s.st D.G).logEllZk := by
    rw [hc, H.power, ← H.maskCode]
    rfl
  have hfit : Own.foldRowFits (First.Close.spent (D.S1 s) D.m) (D.F s) row = true :=
    RowFit.batch_rowfits hG' hL' hOk' hr' H.termsOk hrow (First.Close.spent (D.S1 s) D.m) rfl
      (fun o ho => (First.Close.spent_extends D.m (D.S1 s)).tableBits (hOk'.there o ho) .main)
      (D.F s) rfl rfl H.kh.1.symm H.kh.2.symm
      (by
        show ceilLog2 ((D.S1 s).codes.base.getD s.frame.shape.code default).ell = _
        rw [hc, ← H.code]
        rfl) e2 H.bits
  refine ⟨row, hrow, fun rE rR φ W γ hP hσ hR => ?_⟩
  exact close_holds st (D.S1 s) s.frame.group _ (Own.layoutOf s.st D.G) (runRows s.st D.G) x row hG'
    hL' hOk' hr' hb m hs' (H.kh.1.trans nk) (H.kh.2.trans nh) nl nz (D.F s) D.m rE rR nk nh
    ((Own.foldRowFits_agrees _ _ _).trans hfit) (e2.trans nz) φ W γ hP hσ hR

end ProofFile.Honest.K10.Values

#print axioms ProofFile.Honest.K10.Values.closeBase_holds
