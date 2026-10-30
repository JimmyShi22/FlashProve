-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/RoundFrames.lean: three seats in the frame's own form: the chain's end (member
357), the draw of the smallness test's matrix (25 members) and the merge of the claims on the
weights (member 346): at each the two premises that the rule for acceptance asks at a member,
`Carries` and `Returns` (Johnson/Desc/ProofFile/Honest/Thread/Shape.lean), at the letters `firstZA g
vals` (Johnson/AtFull/Shape/FrameForm.lean). Under the head `P5J.AtMgA`; a joining of laws; nothing
is evaluated.

Main names.
* `liftQ_at`, `liftQ_ok`: two small laws on `liftQ g` (Johnson/AtFull/Shape/FrameLift.lean: a step g
  on the chain's shape alone as a step on the whole: the rows' makes stand): where g returns the
  shape behind and the statement stays, it returns `shA` of the state behind; and where it returns,
  g does.
* `putTl_st`, `draw_st`: a yes of the draw's decision leaves the statement. `draw_fit`: rounds that
  fit the draw's one declared round are one round with `drawN p` entries.
* `drawNo_numeral`: the draw's number as a numeral: 343 at link 24, else 14 l + 6.
* `seal_frame`: a member stands at 357; and for every ft, g and vals with g 357 = `liftQ sealGS`:
  `Carries` and `Returns` at 357.
* `draw_frame`: for l < 25, with the letters Bs and Xl tied as in `draw_at`: a member stands at ‹the
  member's number›; and for every ft, g and vals with g ‹that number› = `liftQ (drawStep (ProofFile.k8Par
  Zp Bs.G₀ Xl l))`: both at that number. THE PREMISE OF `draw_step_at` ON THE ROUND's NUMBER OF
  ENTRIES IS PAID HERE, off the frame's own test on the rounds' form.
* `merge_frame`: with Bs tied: a member stands at 346; and for every ft, g and vals with g 346 =
  `liftO (mergeG (K11.parOf Zp Bs.G₀))` (`liftO`, Johnson/AtFull/Shape/FrameOpt.lean: `liftQ` of a
  step that returns an Option): both at 346.
No test on values is asked at any of the three: vals stays a free letter.

Limits. TWO PREMISES OF THE RULE AT 27 OF 358 MEMBERS: the rule asks them at every member, and more
(that the run on shapes returns; the values; the fits). g and vals are letters: no table of steps is
laid. The proximity test (member 354) has no frame here: no law says what it does to the rows'
makes, and it has no "returns". At the format's second hash function. Nothing on soundness, completeness or
hiding.
-/
import Johnson.AtFull.Shape.FrameOpt
import Johnson.AtFull.Shape.DrawAtHead
import Johnson.AtFull.Shape.SealAtHead
import Johnson.AtFull.Shape.MergeAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain KindName roundsFit noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind headMergeDecide)
open ProofFile.Honest (Carries Returns)
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA F0T)

/-! ## 1 Two small laws on a step on the chain's shape alone -/

theorem liftQ_at {g : ChainSh → Except String ChainSh} {s t : S}
    (hg : g (chainSh s) = .ok (chainSh t)) (hs : t.st = s.st) :
    liftQ g (shA s) = .ok (shA t) := by
  show (g (chainSh s)).map _ = _
  rw [hg]
  show Except.ok (chainSh t, formsOf s.st) = Except.ok (chainSh t, formsOf t.st)
  rw [hs]

theorem liftQ_ok {g : ChainSh → Except String ChainSh} {x u : ShA} (h : liftQ g x = .ok u) :
    ∃ v, g x.1 = .ok v := by
  unfold liftQ at h
  cases e : g x.1 with
  | error w =>
    rw [e] at h
    cases h
  | ok v => exact ⟨v, rfl⟩

/-! ## 2 What the draw leaves -/

/-- Laying the test's record leaves the statement. (ValueFrames.lean's st_putTl says the same.) -/
theorem putTl_st (s : S) (tl : HTailF2) : (s.putTl tl).st = s.st := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head a => cases ho : a.opened <;> simp [S.putTl, ho]
  | _ => rfl

theorem draw_st {Cl : Type} {p : VerifiableInference.Desc.First.K8.Par} {s t : S} {r : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (VerifiableInference.Desc.First.K8.approximateRangeProofDrawKind (Cl := Cl)
      VerifiableInference.Desc.First.K8.atS p).decide s [r] gs = .ok t) :
    t.st = s.st := by
  obtain ⟨-, tl, -, rfl⟩ := (VerifiableInference.Desc.First.K8.draw_iff p s t r gs).1 h
  exact putTl_st _ _

/-- Rounds that fit the draw's one declared round. -/
theorem draw_fit {p : VerifiableInference.Desc.First.K8.Par} {rs : List Fmt.RoundView}
    (h : roundsFit [VerifiableInference.Desc.First.K8.round p] rs = true) :
    ∃ r, rs = [r] ∧ r.drawn.trits.length = drawN p := by
  match rs, h with
  | [r], h =>
    simp only [roundsFit, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨r, rfl, h.1.1.1.1.2⟩
  | [], h => cases h
  | _ :: _ :: _, h => simp [roundsFit] at h

/-- The draw's number, as a numeral. -/
theorem drawNo_numeral (l : Nat) :
    14 * l + drawNo (subAt l) + 2 = if l = 24 then 343 else 14 * l + 6 := by
  unfold subAt
  by_cases e : l = 24
  · subst e
    rfl
  · rw [if_neg e]
    simp only [e, if_false]
    split <;> rfl

/-! ## 3 The three frames -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The chain's end, in the frame's form.** -/
theorem seal_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (cF.blocksInOrder[357]?).isSome = true ∧
      ∀ (ft : Nat) (g : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        g 357 = liftQ sealGS →
        Carries cF.blocksInOrder ft (firstZA g vals) 357 ∧ Returns cF.blocksInOrder ft (firstZA g vals) 357 := by
  obtain ⟨b, q, -, hc, hr⟩ := seal_at h
  refine ⟨by rw [q]; rfl, fun ft g vals hg => ⟨carries_of_seat q fun s rs gs t u _ hd hu => ?_,
    returns_of_seat q fun s rs gs u _ hu _ => ?_⟩⟩
  · obtain ⟨rfl, h2⟩ := hc s _ gs t hd
    rw [hg, liftQ_at h2 rfl] at hu
    exact (Except.ok.inj hu).symm
  · rw [hg] at hu
    obtain ⟨v, hv⟩ := liftQ_ok hu
    exact ⟨s, hr s _ gs v hv⟩

/-- **The draw, at all 25 links, in the frame's form.** -/
theorem draw_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (Bs : ProofFile.PureBase) (Xl : Stages.LinkH),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      Bs.G₀.built[l]? = some Xl ∧
      (cF.blocksInOrder[14 * l + drawNo (subAt l) + 2]?).isSome = true ∧
      ∀ (ft : Nat) g vals,
        g (14 * l + drawNo (subAt l) + 2) = liftQ (drawStep (ProofFile.k8Par Zp Bs.G₀ Xl l)) →
        Carries cF.blocksInOrder ft (firstZA g vals) (14 * l + drawNo (subAt l) + 2) ∧
          Returns cF.blocksInOrder ft (firstZA g vals) (14 * l + drawNo (subAt l) + 2) := by
  obtain ⟨Bs, Xl, b, e1, e2, q, hrd, hc, hr⟩ := draw_step_at h l hl
  -- the seated block's yes is the kind's own: for what the draw leaves
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans e1)
  have hi : 2 ≤ drawNo (subAt l) + 1 ∧ drawNo (subAt l) + 1 ≤ 9 := by
    cases subAt l <;> exact ⟨by decide, by decide⟩
  obtain ⟨Lk, b', Xl', eL, eb, hX, -, la⟩ :=
    IM.k8_alone O l (subAt l) (IM.subs_scope h.scope h.reads O l hl) (drawNo (subAt l))
      (drawNo_index _ _) hi
  have q' := IM.hear_at_flat eL eb
  rw [IM.flatIx_scope h.scope h.reads O (by omega : l ≤ 24) (drawNo (subAt l))] at q'
  obtain rfl : b' = b := Option.some.inj (q'.symm.trans q)
  obtain rfl : Xl' = Xl := Option.some.inj (hX.symm.trans e2)
  have hy := IM.yes_alone la (by intro k; cases k)
  refine ⟨Bs', Xl', e1, e2, by rw [q]; rfl,
    fun ft g vals hg => ⟨carries_of_seat q fun s rs gs t u hf hd hu => ?_,
      returns_of_seat q fun s rs gs u hf hu _ => ?_⟩⟩
  · rw [hrd] at hf
    obtain ⟨r₁, rfl, hn⟩ := draw_fit hf
    obtain ⟨rd, erd, h2⟩ := hc s _ gs t hd
    obtain rfl : noDigest r₁ = rd := List.head_eq_of_cons_eq erd
    have hd' : (VerifiableInference.Desc.First.K8.approximateRangeProofDrawKind (Cl := ProofFile.Cl)
        VerifiableInference.Desc.First.K8.atS (ProofFile.k8Par Zp Bs'.G₀ Xl' l)).decide s
        [noDigest r₁] gs = .ok t := ((hy s t _ gs).1 hd).1
    rw [hg, liftQ_at (h2 hn) (draw_st hd')] at hu
    exact (Except.ok.inj hu).symm
  · rw [hrd] at hf
    obtain ⟨r₁, rfl, -⟩ := draw_fit hf
    rw [hg] at hu
    obtain ⟨v, hv⟩ := liftQ_ok hu
    exact hr s (noDigest r₁) gs v hv

/-- **The merge, in the frame's form.** -/
theorem merge_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ Bs : ProofFile.PureBase, ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      (cF.blocksInOrder[346]?).isSome = true ∧
      ∀ (ft : Nat) g vals, g 346 = liftO (mergeG (K11.parOf Zp Bs.G₀)) →
        Carries cF.blocksInOrder ft (firstZA g vals) 346 ∧ Returns cF.blocksInOrder ft (firstZA g vals) 346 := by
  obtain ⟨Bs, Lk, name, hB, -, -, -, -, q, -⟩ :=
    Johnson.Desc.First.ForkMerge.Exchange.headMergeAtFull Z D r Zp Np cF x h
  obtain ⟨Bs', b, hB', q', hrd, hc, hr⟩ := merge_at h
  obtain rfl : Bs' = Bs := Except.ok.inj (hB'.symm.trans hB)
  have la : IM.LaidAlone ProofFile.sameReply
      (IM.seatedAs ProofFile.sameReply (headClaimMergeKind (K11.parOf Zp Bs'.G₀)) name IM.k11Place)
      (headClaimMergeKind (K11.parOf Zp Bs'.G₀)) name IM.k11Place := rfl
  have hy := IM.yes_alone la (by intro k; cases k)
  obtain rfl : b = _ := Option.some.inj (q'.symm.trans q)
  refine ⟨Bs', hB, by rw [q]; rfl,
    fun ft g vals hg => ⟨carries_of_seat q fun s rs gs t u hf hd hu => ?_,
      returns_of_seat q fun s rs gs u hf hu _ => ?_⟩⟩
  · rw [hg] at hu
    obtain ⟨v, hv, rfl⟩ := liftO_ok.1 hu
    obtain rfl : v = chainSh t := hc s rs gs t v hf hd hv
    have k1 := (VerifiableInference.Desc.First.MergeLaw.leavesSeven _ s _ gs t
      ((hy s t _ gs).1 hd).1).1
    show (chainSh t, formsOf s.st) = (chainSh t, formsOf t.st)
    rw [k1]
  · rw [hg] at hu
    obtain ⟨v, hv, -⟩ := liftO_ok.1 hu
    exact hr s rs gs v hf hv

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.liftQ_at
#print axioms Johnson.AtFull.Shape.liftQ_ok
#print axioms Johnson.AtFull.Shape.putTl_st
#print axioms Johnson.AtFull.Shape.draw_st
#print axioms Johnson.AtFull.Shape.draw_fit
#print axioms Johnson.AtFull.Shape.drawNo_numeral
#print axioms Johnson.AtFull.Shape.seal_frame
#print axioms Johnson.AtFull.Shape.draw_frame
#print axioms Johnson.AtFull.Shape.merge_frame
