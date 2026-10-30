-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchFreshAt.lean: the closing of a segment (K10): the pairing of the field fresh of
`CarryOwed` (Honest/K10/Xch/CarryTop.lean) under the facts on the record in front of the closing (`CloseBase`,
Johnson/Desc/K10/Honest/Base.lean), from one sentence on the witness's table at the fresh mask's message.

`fresh_of_tabs` (Pay/XchFresh.lean) asks three public things beside that sentence. All three follow from `CloseBase`:
  `mask_shape_of_base`   the fresh mask's message is there and has 2 ^ h mask rows: the verifier's test `foldMaskFits`
  `room_of_base`         the stage has room for the packing: a clause of the verifier's test `foldShapeFits`
  (the run's number of variables is the stage's: `CloseBase.stretch` and `stageB_k`, Johnson/Desc/K10/Honest/LeftClaim.lean)
  **`fresh_of_base`**      so the pairing, at a witness v and 2 k + 1 words u as letters

Limits. The sentence on the witness's table is a premise, shown here of no witness. `CloseBase` is a premise. No head,
thread or prover is named.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchFresh
import Johnson.Desc.Sound.WordsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes.Slice (GE readE)
open Cb (HIdx sVars)
open Johnson.Prover.Link (Pairs)
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par Rec)
open VerifiableInference.Desc.Sound (MsgT wordsFirst tabAt seatBy noFirst)
open ProofFile.Honest.K10.LeftIs (stageB freshB stageB_k)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

variable {P : Par} {r : Rec} {D : BaseData}

/-- The fresh mask's message is there and has 2 ^ h mask rows. -/
theorem mask_shape_of_base (Hb : CloseBase P r D) :
    ∃ y, r.st.oracles[D.m]? = some y ∧ y.shape.maskRows = 2 ^ (stageB D r).h := by
  obtain ⟨o, ho, -, hm, -⟩ := (Own.foldMaskFits_iff _ _ _).1 Hb.maskfits
  have e : ((D.S1 r).oracles[D.m]?).map (·.shape) = (r.st.oracles[D.m]?).map (·.shape) :=
    OnBytes.Slice.closeLedgers_shape D.G.members.toList r.st D.m
  rw [ho] at e
  have e' : (r.st.oracles[D.m]?).map (·.shape) = some o.shape := e.symm
  obtain ⟨y, hy, ey⟩ := Option.map_eq_some_iff.1 e'
  refine ⟨y, hy, ?_⟩
  rw [ey]
  exact hm

/-- The stage has room for the packing of the hiding polynomial's coefficients. -/
theorem room_of_base (Hb : CloseBase P r D) :
    (stageB D r).h + 2 * (stageB D r).g + 1 ≤ (stageB D r).Z.l := by
  obtain ⟨c, zk, -, hz, -, h2, -, h4, -⟩ := (Own.foldShapeFits_iff _ _).1 Hb.shape
  have hz' : (D.S1 r).codes.mask[r.frame.shape.maskCode]? = some zk := hz
  have eZ : (stageB D r).Z.l = zk.ell := by
    show ((D.S1 r).codes.mask.getD r.frame.shape.maskCode default).ell = _
    rw [Array.getD_eq_getD_getElem?, hz']
    rfl
  have eh : (stageB D r).h = (D.F r).layout.h := rfl
  have eg : (stageB D r).g = (D.F r).layout.k - (D.F r).layout.h := rfl
  rw [eZ, eh, eg]
  omega

/-- **The field fresh's pairing under `CloseBase`**, from: the witness's table at the fresh mask's message is, inside the
table, what a sending lays where a fold's fresh table rides, at the values of the words u. -/
theorem fresh_of_base {s : First.S} (Hb : CloseBase P (K9.recOf s) D) {Cells Tok : Type} (arr : Nat → Nat → Nat)
    (v : Wit Cells Tok MsgT) {n' : Nat} (hn : n' = P.k) (u : Fin (2 * n' + 1) → OnBytes.E)
    (hT : ∀ b j, b < 2 ^ (stageB D (K9.recOf s)).h → j < (stageB D (K9.recOf s)).Z.l →
      tabAt s.st.codes arr (seatBy noFirst s.book) s.st v D.m true b j =
        (⟨(stageB D (K9.recOf s)).h + (stageB D (K9.recOf s)).g, (stageB D (K9.recOf s)).h⟩ : K1.Ride).lay
          (fun n => readE (wordsAll u n)) b j)
    (W : HIdx (sVars GE 2 ((stageB D (K9.recOf s)).h + (stageB D (K9.recOf s)).g)) → GE) (hW : CoefOf u W) :
    Pairs (stageB D (K9.recOf s)) (stageB D (K9.recOf s)).Z.l W
      (freshB D (K9.recOf s) (wordsFirst arr s.st s.book v)) := by
  obtain ⟨y, hy, hr⟩ := mask_shape_of_base Hb
  exact fresh_of_tabs (r := K9.recOf s) (tabAt s.st.codes arr (seatBy noFirst s.book) s.st v) hy hr
    (room_of_base Hb) (hn.trans (Hb.stretch.trans (stageB_k Hb))) u hT W hW

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.mask_shape_of_base
#print axioms ProofFile.Honest.K10.room_of_base
#print axioms ProofFile.Honest.K10.fresh_of_base
