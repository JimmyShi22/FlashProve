-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/InTFour.lean: FOUR FIELDS OF `InTAsks` (hK, mask, oneRow, reads:
Johnson/Road/K4/InT/Statement.lean) AT THE VERIFIER's STATE BEHIND A YES OF K4's BLOCK, OUT OF THE
TABLE OF JOINTS' PROMISE IN FRONT OF THE BLOCK AND TESTS WITH CODE ON THE PLAN's LETTERS. Statements
and proofs: calls. GLUE.

How. In front of the block the open segment's part of the state reads as the plan says (`RecIs`:
Johnson/Road/K4/Rec/Whole.lean). A yes leaves the link's context, the statement and the book
(`Rest`), and the ledger's arrays (`hear_trees`, Johnson/Road/K4/Slots/HearTrees.lean): so `RecIs`
holds behind. There the test on the array of reads is the test on the plan (`readsArray_plan`,
Johnson/Road/K4/Rec/ReadsArray.lean), and gives three of the four (`readsArray_gives`,
Johnson/Road/K4/ReadsArrayAt.lean); the fourth is `mask_plan` (Johnson/Road/K4/Rec/InT.lean).

  `RecIs.of_same`: `RecIs` reads the part's link's context, statement, book and ledger's arrays
    alone.
  `recIs_behind`: from `KeptAtS p s s'` and "the ledger in front has arrays of the right sizes".
  `Four own p s'`: the four fields, to the letter, as one sentence.
  **`four_of_kept`**: `KeptAtS p s s'`; sizes; `RecIs` at s's part; `maskSeatP` answers;
    `readsArrayP` says yes: `Four own p s'`.
  `sized_of_ledgerB`: the public item ledger's test gives the sizes.
  **`inT_four_of_front`**: `K4Means Mg D`, eSent, eTrees; ON THE PLAN: `openAllB` at border k; the
    item ledger m is open there; `maskSeatP` answers; `readsArrayP` says yes: then at every unmarked
    statement inside the promise at border k and every `Yes` of the piece: `Four` at the state
    behind.

OBJECT: none of its own. USER: meant: the assembly of K4's row out of `K4Means`. LETTERS, filled by
nobody: Mg, D, sd, Z, links, ps, k, m, par, q.

Limits. `K4Means`, eSent AND eTrees ARE PREMISES; "frame.sentIs" and "ledger.treesAre" lie in no
composed filling yet. THE FOUR TESTS ON THE PLAN HAVE BEEN EVALUATED NOWHERE. ONE DIRECTION, FROM A
YES. K04_law, the law of K4's block itself, IS NOT PROVED BY THIS. Nothing on soundness.

-/
import Johnson.Road.K4.KeptOfYes
import Johnson.Road.K4.Slots.HearTrees
import Johnson.Road.K4.Rec.ReadsArray
import Johnson.Road.K4.Rec.OfMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Rec
open Iop OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Desc.First.K4.Slots (hear_trees)
open OnBytes.Road.K4.InT (oneRowB readsThereB)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.First (S LayOwn ModelPart Pub Meaning Numbers pubSets ledgerB)
open VerifiableInference.Desc.First.FillSent (SentData)
open VerifiableInference.Desc.First.RecordPlan (maskSeatP)
open VerifiableInference.Desc.K9 (segAt? maskSeat)
open VerifiableInference.Desc.Sound (Frame Piece MsgT onQ)

/-- `RecIs` reads the part's link's context, statement, book and ledger's arrays alone. -/
theorem RecIs.of_same {A₀ A : Part9} {R : RecPlan} {n m : ℕ} (h : RecIs A₀ R n m)
    (eL : A.L = A₀.L) (eS : A.d.st = A₀.d.st) (eB : A.d.book = A₀.d.book)
    (eT : A.F.trees = A₀.F.trees) : RecIs A R n m where
  layout := by rw [eL]; exact h.layout
  shape := by rw [eL]; exact h.shape
  arrays := by rw [eL]; exact h.arrays
  link := by rw [eL]; exact h.link
  whereIs := by rw [eL]; exact h.whereIs
  mask := by rw [eL]; exact h.mask
  seat := by rw [eB]; exact h.seat
  rowBits := by rw [eS]; exact h.rowBits
  placeBits := by rw [eS]; exact h.placeBits
  trees := by rw [eT]; exact h.trees

variable {p : Par} {s s' : S}

/-- **`RecIs` goes over a yes**, where the ledger in front has arrays of the right sizes. -/
theorem recIs_behind (h : KeptAtS p s s') (hS : ∀ a : LayOwn, s.here = .lay a → PscRun.Sized a.F)
    {A₀ A : Part9} {R : RecPlan} {n m : ℕ} (hA₀ : segAt? s = some A₀) (hA : segAt? s' = some A)
    (r : RecIs A₀ R n m) : RecIs A R n m := by
  obtain ⟨a, fo, o, G, ha, _, hG, _, _, _, _, _, hR, _, _, t, u, hh⟩ := h
  obtain ⟨l0, f0, s0, b0⟩ := part_fields hA₀
  obtain ⟨l1, f1, s1, b1⟩ := part_fields hA
  have hF : s.fork? = some a.F := by
    unfold S.fork?
    rw [ha]
  have e0 : A₀.F = a.F := Option.some.inj (f0.symm.trans hF)
  have e1 : A.F = G := Option.some.inj (f1.symm.trans hG)
  refine r.of_same (Option.some.inj (l1.symm.trans (hR.link.trans l0))) ?_ ?_ ?_
  · rw [s1, s0, hR.st]
  · rw [b1, b0, hR.book]
  · rw [e1, e0]
    exact hear_trees (hS a ha) hh

/-- **The four fields, to the letter.** -/
def Four (own : List (ℕ × ℕ)) (p : Par) (s' : S) : Prop :=
  (∀ o, s'.own? = some o → p.hp.nU.getD 2 0 ≤ o.v.K3) ∧
    (∀ A, segAt? s' = some A → (maskSeat own A).isSome = true) ∧
    (∀ G o, s'.fork? = some G → s'.own? = some o → oneRowB G o.v.iU3 = true) ∧
    ∀ A o, segAt? s' = some A → s'.own? = some o →
      readsThereB A o.v.iU3 (p.hp.nU.getD 2 0) = true

/-- **The four behind a yes**, from `RecIs` in front and two tests on the plan. -/
theorem four_of_kept (h : KeptAtS p s s') (hS : ∀ a : LayOwn, s.here = .lay a → PscRun.Sized a.F)
    {A₀ : Part9} {R : RecPlan} {n m : ℕ} (hA₀ : segAt? s = some A₀) (r : RecIs A₀ R n m)
    (own : List (ℕ × ℕ)) (hM : (maskSeatP R.shape R.d own R.L.places n m).isSome = true)
    (hB : readsArrayP p.hp R.shape R.layout (R.arrs m) m (R.d.trees m) = true) :
    Four own p s' := by
  have h0 := h
  obtain ⟨a, fo, o, G, ha, _, hG, _, hO, _, _, _, hR, _, _, t, u, hh⟩ := h
  obtain ⟨a', ha', _⟩ := hR.here a ha
  obtain ⟨A, hA, eF, _⟩ := OnBytes.Desc.First.K4.InT.segAt_lay ha'
  have r' : RecIs A R n m := recIs_behind h0 hS hA₀ hA r
  have hB' : readsArrayB p.hp s' = true := by
    rw [readsArray_plan r' p.hp ha' hA]
    exact hB
  have I := readsArray_gives hh ha' hB'
  have hF' : s'.fork? = some a'.F := by
    unfold S.fork?
    rw [ha']
  refine ⟨fun o' ho' => ?_, fun A' hA' => ?_, fun G' o' hG' ho' => ?_, fun A' o' hA' ho' => ?_⟩
  · obtain rfl : o = o' := Option.some.inj (hO.symm.trans ho')
    exact I.cols
  · obtain rfl : A = A' := Option.some.inj (hA.symm.trans hA')
    exact mask_plan r' own hM
  · obtain rfl : o = o' := Option.some.inj (hO.symm.trans ho')
    obtain rfl : a'.F = G' := Option.some.inj (hF'.symm.trans hG')
    exact I.oneRow
  · obtain rfl : o = o' := Option.some.inj (hO.symm.trans ho')
    exact I.there A' hA'

/-- The public item ledger's test gives the sizes. -/
theorem sized_of_ledgerB (h : ledgerB s = true) (a : LayOwn) (ha : s.here = .lay a) :
    PscRun.Sized a.F := by
  have hF : s.fork? = some a.F := by
    unfold S.fork?
    rw [ha]
  unfold ledgerB at h
  rw [hF] at h
  simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

variable {Xi P Tok Cl : Type} {rows cols nR kC : ℕ} {X : Verify.Public} {Fr : Frame}

/-- **OUT OF THE PROMISE IN FRONT, UNDER `K4Means`, eSent AND eTrees (PREMISES) AND FOUR TESTS ON
THE PLAN: the four fields at the state behind every `Yes`.** -/
theorem inT_four_of_front {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)}
    {D : K4Data Xi P Tok rows cols nR kC X} (E : K4Means Mg D) (sd : SentData)
    (eS : ESent Mg sd) (eT : ETrees Mg sd) (Z : P) (links : List ModelPart) (ps : List Place) (k m : ℕ)
    (par : Par) (q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT))
    (hO : openAllB D.moreL links ps k m = true)
    (hL : ((pubSets D.moreL links ps)[k]?.getD []).contains (.ledger m) = true)
    (hM : (maskSeatP D.D3.shape sd (D.N.sent m 0) D.d12.L.places (D.N.msgsAt ps[k]?) m).isSome =
      true)
    (hB : readsArrayP par.hp D.D3.shape D.D3.layout (D.D3.arrayOf.getD m #[]) m (sd.trees m) =
      true)
    (a : S × Fr.E.Str) (τ : Tr (uLT (ckP .two) q.ds)) (fo : Forest.Heard) (o : Own) (G : Fork)
    (ha : onQ D.N Mg links ps (fun s => (Z, s)) k a) (hu : a.1.failed = none)
    (y : Yes seatS par q a τ fo o G) :
    Four (D.N.sent m 0) par (behindOf seatS q a τ o G).1 := by
  obtain ⟨al, hal, _⟩ := lay_of_look y.look
  obtain ⟨A₀, hA₀, _, _⟩ := OnBytes.Desc.First.K4.InT.segAt_lay hal
  have hb : AtBorder D.N Mg Z links ps k a A₀ := ⟨ha, hu, hA₀⟩
  have r := recIs_of_means E sd eS eT D.N Z links ps k m a A₀ hO hb
  have hLo : OpenAt Mg links ps k (.ledger m) := by
    unfold OpenAt
    rw [E.more]
    simpa using hL
  have hl : ledgerB a.1 = true := by
    have h1 := pub_of_open hb hLo
    rw [E.ledger m (Z, a.1)] at h1
    exact h1
  exact four_of_kept (kept_of_yes y) (sized_of_ledgerB hl) hA₀ r (D.N.sent m 0) hM hB

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.recIs_behind
#print axioms OnBytes.Road.K4.Rec.four_of_kept
#print axioms OnBytes.Road.K4.Rec.inT_four_of_front
