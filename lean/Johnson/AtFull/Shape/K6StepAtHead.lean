-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/K6StepAtHead.lean: THE OUTPUT HEAD's OWN ROUNDS (the place H:4, the kind K6;
member 341 of the flat list) AT ITS SEAT: "RETURNS" WHERE THE STEP RETURNS: the step of
K6AtHead.lean under two guards more, which are read off the chain's shape, and two premises on the
state, by name. Under the head P5J.AtMgA; a joining of laws; nothing is evaluated.
  `freshB L n`, `fresh_of_B`: on the ledger's shape: the arrays have their sizes, n more numbers are
    there, and every number from the next on is free: it gives the library's WellLaid and Fresh.
    `k6Takes h`: how many slots the hearing takes: 41 + 8 lt + 4 lPd.
  `k6GR h`: the step: a reply was heard; freshB at k6Takes h; then k6GS h. `k6G_some`.
  `front_of_step`: where k6GR returns at a state's shape, the state is ready (another house's
    K6Front, with no room asked behind), GIVEN two clauses that are asked of the state: the
    state's own test on the request's words (startOk), and the test on the lookup's points
    (PointsOk: each call's key point has its length and ends as the lookup's point does: an equality
    of field elements in the carried record).
  **`k6_step_at`**: the member b at number 341 of cF.blocksInOrder, at the step k6GR (P5J.At.X Zp).hS: where
    b says yes and the step returns, it returns the shape behind, and the statement is as it was;
    and where the step returns, under startOk, PointsOk and the step's own tests on the rounds' and
    columns' form (Block.Fits), b says yes at what its step shows it.
By k6_at (K6AtHead.lean) and Parts.lean's sized_of_B.
Limits. "Carries" is under the step's own return. "RETURNS" TAKES TWO NAMED PREMISES ON THE STATE
BEYOND ITS SHAPE (startOk; PointsOk): neither reads a round. OF PointsOk ONE HALF COULD BE READ OFF
THE SHAPE: the key points' lengths (the library cuts given's third test in two, the sizes and the
values: test_split, with zk_size, Johnson/Desc/K6/Shape/Seat.lean); here the whole of it stands
among the premises on the state. freshB asks more than the hearing needs (every number behind the
next is free): so the step may refuse where the member says yes. UNDER THE HEAD: that it has a
member is shown at two triples of files alone (VerifierAndGoals.storedPublicFiles and VerifierAndGoals.zGap), in a side library
(AtFullSide/Top/HeadMemberAtFull.lean, HeadMemberAtGap.lean). NO STATE IS SHOWN AT WHICH THE STEP
RETURNS. At the earlier hash OnBytes.secondHashFunction. Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.Shape.K6AtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName OpenedColumn noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.Kinds.Head (seatAt parOf startOk)
open VerifiableInference.Desc.Kinds.Head.Law (K6Front K6MemberIs readsOf workOf Fresh HeadOpen)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-- The ledger's arrays have their sizes; n more numbers are there; every number from the next on is
free: on the ledger's shape. -/
def freshB (L : LedSh) (n : Nat) : Bool :=
  sizedB L && decide (L.next + n ≤ L.ns) && (L.got.drop L.next).all (!·)

theorem fresh_of_B {F : Fork} {n : Nat} (h : freshB (ledSh F) n = true) :
    VerifiableInference.Desc.Kinds.Head.Law.WellLaid F ∧ Fresh F n := by
  unfold freshB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨s1, s2, s3⟩ := sized_of_B h1
  have h2' : F.next + n ≤ F.ns := h2
  refine ⟨⟨s3, s1, s2⟩, h2', Nat.le_refl _, s3, fun j j1 j2 => ?_⟩
  have hj : j < F.gotF.size := by rw [s3]; exact j2
  have hm : F.gotF[j] ∈ F.gotF.toList.drop F.next :=
    List.mem_iff_getElem.2 ⟨j - F.next, by simp; omega, by
      simp [show F.next + (j - F.next) = j by omega]⟩
  have h3' : ∀ b ∈ F.gotF.toList.drop F.next, (!b) = true := List.all_eq_true.1 h3
  have := h3' _ hm
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj]
  simpa using this

/-- How many slots the hearing takes. -/
def k6Takes (h : Model.Head.Shape) : Nat :=
  letI : VerifiableInference.Desc.Kinds.Head.Sizes := VerifiableInference.Desc.Kinds.Head.sizesOf h
  41 + 8 * VerifiableInference.Desc.Kinds.Norm.lt + 4 * VerifiableInference.Desc.Kinds.Norm.lPd

/-- **The step at the seat, with the guards that "returns" reads off the shape**: a reply was heard;
the ledger's arrays have their sizes and all that the hearing takes is there and free, as is every
number behind; then k6GS. -/
def k6GR (h : Model.Head.Shape) (a : ChainSh) : Option ChainSh :=
  if a.reply && (a.led.any fun L =>
      freshB L (k6Takes h)) then k6GS h a
  else none

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem k6G_some {h : Model.Head.Shape} {a u : ChainSh} (hg : k6G h a = some u) :
    a.lookHeard.isSome = true ∧ a.head.isSome = true := by
  unfold k6G at hg
  split at hg
  · rename_i L g hd e1 e2 e3
    rw [e2, e3]
    exact ⟨rfl, rfl⟩
  · cases hg

/-- Where the guarded step returns, the state in front is ready, but for two clauses that are asked
of the state (of the second, one half could be read off the shape: see the head's Limits). -/
theorem front_of_step {W : Model.Verify.Public} {s : S} {u : ChainSh}
    (hg : k6GR W.hS (chainSh s) = some u) (hst : startOk W s = true)
    (hP : ∀ g, s.lookHeard? = some g →
      @VerifiableInference.Desc.Kinds.Head.Law.PointsOk (parOf W.hS (workOf W)).sizes
        (parOf W.hS (workOf W)).floor g.zx fun c => g.zk.getD c #[]) :
    K6Front W 0 s := by
  unfold k6GR at hg
  split at hg
  · rename_i hc
    rw [Bool.and_eq_true] at hc
    obtain ⟨hr, hl⟩ := hc
    unfold k6GS at hg
    split at hg
    · cases hg
    · rename_i hm
      have hf : s.failed = none := by
        have h1 : (chainSh s).marked = false := by simpa using hm
        have h2 : s.failed.isSome = false := h1
        simpa using h2
      have hr' : s.out.reply.isSome = true := hr
      obtain ⟨y0, hy0⟩ := Option.isSome_iff_exists.1 hr'
      have hl' : (s.fork?.map ledSh).any (fun L => freshB L (k6Takes W.hS)) = true := hl
      cases hF : s.fork? with
      | none =>
        rw [hF] at hl'
        cases hl'
      | some F =>
        rw [hF] at hl'
        obtain ⟨w1, w2⟩ := fresh_of_B (F := F) hl'
        obtain ⟨hlk, hhd⟩ := k6G_some hg
        have hlk : (s.lookHeard?.map heardAll).isSome = true := hlk
        have hhd : (headOf s.here).isSome = true := hhd
        cases hq : s.lookHeard? with
        | none =>
          rw [hq] at hlk
          cases hlk
        | some g =>
          have hled : (seatAt W.hS (readsOf W)).ledger s = F := by
            show s.fork?.getD {} = F
            rw [hF]
            rfl
          have hty : (VerifiableInference.Desc.Kinds.Reply.token
              (seatAt W.hS (readsOf W)).toSeat s).isSome = true := by
            show (s.out.reply.map _).isSome = true
            rw [hy0]
            rfl
          obtain ⟨yt, hyt⟩ := Option.isSome_iff_exists.1 hty
          refine ⟨hf, ?_, hst, ⟨(g.zx, fun c => g.zk.getD c #[]), yt, ?_, hyt, hP g hq⟩, ?_, ?_⟩
          · cases hs : s.here with
            | head o =>
              cases hop : o.opened with
              | true =>
                refine ⟨o, hs, hop, ?_⟩
                simp only [S.lookHeard?, hs, hop, if_true] at hq
                rw [hq]
                rfl
              | false => simp [S.fork?, hs, hop] at hF
            | between => simp [headOf, hs] at hhd
            | lay a => simp [headOf, hs] at hhd
            | att a => simp [headOf, hs] at hhd
            | fin a => simp [headOf, hs] at hhd
            | mem a => simp [headOf, hs] at hhd
          · show (s.lookHeard?.map fun g => (g.zx, fun c => g.zk.getD c #[])) = _
            rw [hq]
            rfl
          · rw [hled]
            exact w1
          · rw [hled]
            exact w2
  · cases hg

/-- **"RETURNS" IN THE HOUSE's FORM, AND "CARRIES", AT THE GUARDED STEP.** -/
theorem k6_step_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ b : Block S ProofFile.Cl, cF.blocksInOrder[341]? = some b ∧
      (∀ s rs gs t u, b.decide s rs gs = .ok t → k6GR (P5J.At.X Zp).hS (chainSh s) = some u →
        u = chainSh t ∧ t.st = s.st) ∧
      ∀ s ft rs cols u, k6GR (P5J.At.X Zp).hS (chainSh s) = some u →
        startOk (P5J.At.X Zp) s = true →
        (∀ g, s.lookHeard? = some g →
          @VerifiableInference.Desc.Kinds.Head.Law.PointsOk
            (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))).sizes
            (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))).floor g.zx fun c => g.zk.getD c #[]) →
        b.Fits ft rs cols →
        ∃ t, b.decide s (rs.map noDigest) (b.shown ft rs cols) = .ok t := by
  obtain ⟨b, q, hc, hr⟩ := k6_at h
  refine ⟨b, q, fun s rs gs t u hd hg => ?_, fun s ft rs cols u hg hst hP hF =>
    hr s ft rs cols 0 (front_of_step hg hst hP) hF⟩
  unfold k6GR at hg
  split at hg
  · exact hc s rs gs t u hd hg
  · cases hg

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.fresh_of_B
#print axioms Johnson.AtFull.Shape.k6G_some
#print axioms Johnson.AtFull.Shape.front_of_step
#print axioms Johnson.AtFull.Shape.k6_step_at
#print axioms Johnson.AtFull.Shape.freshB
#print axioms Johnson.AtFull.Shape.k6Takes
#print axioms Johnson.AtFull.Shape.k6GR
