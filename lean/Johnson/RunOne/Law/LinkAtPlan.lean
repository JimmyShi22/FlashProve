-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/LinkAtPlan.lean: THE SIX
SEATS OF A LOOKUP'S LINK AT A PLAN THAT PASSES THE PROGRAM'S OWN TEST ON THE ITEM "RANGES"
(Wf.admitted, OnBytes/Iop/Wf.lean): link_seats (LinkSeats.lean) with fewer letters. The lookups are
the plan's; the promise is the one written out (PromKeyD.lean), and with it the lists of mask
entries that each lookup is handed; the six conditions on public numbers follow from the one test.

Main names:
  Lof one: the plan's lookups by their numbers.
  d_le, layout_of_admitted, tests_at: what Wf.admitted gives: d ≤ 64; the layout's first block fits
    a main row; the two tests on lookup number i.
  link_seats_at: THE SIX SEATS.

Limits. Left as letters: the decoder dec, its condition cond and what else rides, Oth (Blind; LowDec
at each piece's place) · wd, mx · the two ledgers lo, lk in front of the first link · what else is
promised, Ex (Kept). Left as premises: the plan passes Wf.admitted · the own message and the
index-mask message are different messages · the pieces hold the flat list's blocks, six of which are
the link's · the seven rows are the link's · no two trees of the frame's list have one number · a
value st0 of the riding part's type · the witnesses' type M × Wp is not empty · each piece's errors
lie below the bound · the piece of the kind's block puts no round back, its stretch is MadeOf the
lookup's shape, and the typed lookup's errors along the maps lie below its errors. Named nowhere in
the theorem, and owed beside it: that PromL 0 holds at the record that stands behind the sending of
the second message (promL_zero: four plain facts); without it the rows may be off everywhere.

-/
import Johnson.RunOne.Law.LinkSeats
import Johnson.RunOne.Law.PromKeyD
import OnBytes.Tie.Pv.KeyLookup.AdmAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace Johnson.RunOne.Law.LinkAtPlan
open Iop OnBytes OnBytes.Slice OnBytes.Params OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (FirstState Claim lookupLink layerOrder)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.PromKeyD
open Johnson.RunOne.Law.SeatsAtFK
open Johnson.RunOne.Law.LinkSeats

/-- The plan's lookups by their numbers. -/
def Lof (one : OneTime) (i : ℕ) : WfLookup := one.ranges.lookups.getD i default

theorem d_le {l : WfLookup} (h : Wf.lookupOk Wf.fBits l = true) : l.d ≤ 64 := by
  simp only [Wf.lookupOk, Bool.and_eq_true, decide_eq_true_eq] at h
  have := h.1.1.1.1.1.1.1.2
  unfold Wf.fBits at this
  omega

/-- The layout's first block fits a main row. -/
theorem layout_of_admitted {codes : Codes} {x : WfPublic} {m : Wf.Matrix}
    (h : Wf.admitted codes x m = true) :
    ((Wf.layout x.lookups (Planes.codeOf x codes).ell).head?.any
      fun b => decide (2 ^ b.bits ≤ (Planes.codeOf x codes).ell)) = true := by
  unfold Wf.admitted at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.2.1

theorem tests_at {one : OneTime} {m : Wf.Matrix} {i : ℕ}
    (h : Wf.admitted one.codes one.ranges m = true) (hi : i < one.ranges.lookups.length) :
    one.ranges.lookups[i]? = some (Lof one i) ∧ Wf.lookupOk Wf.fBits (Lof one i) = true ∧
      Wf.fitsMatrix m (Lof one i) = true := by
  have e : one.ranges.lookups[i]? = some (Lof one i) := by
    unfold Lof
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl
  have hm : Lof one i ∈ one.ranges.lookups := List.mem_of_getElem? e
  exact ⟨e, Lk6.admitted_tests h _ hm⟩

variable {Fr : Frame} {P W : Type} {one : OneTime} {set : Setting} {id : ℕ} {m : Wf.Matrix}
  {idxN : ℕ} {M Wp : Type} {wd : M → Means.Words GE} {mx : M → ℕ → ℕ → GE}
  {dec : TK P × Fr.E.Str → Option M} {cond : TK P × Fr.E.Str → Prop} {Oth : TK P → M × Wp → Prop}
  {lo lk : Ledger} {Ex : FirstState → Prop}

/-- **THE SIX SEATS OF THE LINK OF LOOKUP NUMBER i, AT A PLAN THAT PASSES THE PROGRAM'S OWN TEST.**
a: the place of the link's first block in the flat list. -/
theorem link_seats_at (εs : ℝ≥0∞) (A0 : JointRow (P × FirstState) Fr)
    (ps : List (Piece (ckP .two) Fr (P × FirstState) Claim W)) (rs : List (JointRow (P × FirstState)
        Fr))
    (bs : List (Block FirstState Claim)) (a i : ℕ) (hW : Wf.admitted one.codes one.ranges m = true)
    (hne : one.ranges.messageId ≠ idxN) (hE : Kept one id m (Lof one) Ex)
    (hi : i < one.ranges.lookups.length)
    (hbs : ps.map (·.b) = (bs.map below).map (Block.lift Prod.snd fun t s => (t.1, s)))
    (hlink : ∀ j < 6, bs[a + j]? =
      (lookupLink one set i (Wf.lookupOf id m (Lof one i))).blocksInOrder[j]?)
    (hr : ∀ j ≤ 6, keyRowAt A0 rs (a + j) =
      upF fun p₀ => (rows7 p₀ one set id m (Lof one) (handed (cntO id m (Lof one)) lo)
        (handed (cntK id m (Lof one)) lk) idxN wd mx dec cond one.ranges.lookups.length
        (PromL one id m (Lof one) idxN one.ranges.lookups.length lo lk Ex) i Wp Oth j))
    (hnd : (Fr.all.map (·.no)).Nodup) (hB : Blind dec cond Oth) (st0 : TK P)
    (hw : Nonempty (M × Wp))
    (hpc : ∀ j < 6, ∀ p, ps[a + j]? = some p → Err.Below p.err εs ∧ LowDec dec cond p.base)
    (hk3 : ∀ p, ps[a + 2]? = some p → p.back = [] ∧
      ∃ hds : List.Forall₂ MadeOf p.ds (shapeG (faceOfLkp (Wf.lookupOf id m (Lof one i)))),
        Err.le ((mapsAt (Fr := Fr) one id m (Lof one) (handed (cntO id m (Lof one)) lo)
          (handed (cntK id m (Lof one)) lk) idxN i
          (Lk6.adm_of_tests id m _ (tests_at hW hi).2.1 (tests_at hW hi).2.2)
          (d_le (tests_at hW hi).2.1) st0 p.ds hds).err
          (kAt one id m (Lof one) (handed (cntO id m (Lof one)) lo)
            (handed (cntK id m (Lof one)) lk) idxN wd mx dec cond one.ranges.lookups.length i Wp
            Oth).err) p.err) :
    ∀ j < 6, SeatGood εs A0 ps rs (a + j) :=
  link_seats εs A0 ps rs bs a i hbs hlink hr hnd (promise_ledgers hne hE) hB hi
    (Lk6.adm_of_tests id m _ (tests_at hW hi).2.1 (tests_at hW hi).2.2)
    (d_le (tests_at hW hi).2.1) (tests_at hW hi).2.1 (tests_at hW hi).2.2 (tests_at hW hi).1
    (layout_of_admitted hW) st0 hw hpc hk3

end Johnson.RunOne.Law.LinkAtPlan

#print axioms Johnson.RunOne.Law.LinkAtPlan.d_le
#print axioms Johnson.RunOne.Law.LinkAtPlan.layout_of_admitted
#print axioms Johnson.RunOne.Law.LinkAtPlan.tests_at
#print axioms Johnson.RunOne.Law.LinkAtPlan.link_seats_at
