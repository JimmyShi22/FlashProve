-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstReached.lean: THE TESTS IN THE PROMISE's SLOT ARE MET BY EVERY STATE
THAT THE VERIFIER's OWN ACCEPTING STEPS REACH. The hand-ons of Sh.X
(Johnson/Desc/K14/Law/SharedConstWalk.lean) would hold of a test that is false everywhere, and the
promise would then be empty. HERE: Sh.X holds at the shared chain's first state and is handed on by
each sub-protocol's own accepting step IN THE WRAP ("below": every word shown is below the prime),
so it holds at every state that is reached by such steps (Reach, Johnson/Top/H0/Walk/Reach.lean;
the induction: ReachInv.lean).

  Sh.xk_eight     one of the kind's eight sub-protocols, at its accepting step in the wrap: XK from
                  border i + 1 to i + 2. smpK is EARNED here, at the two sendings (smpEarn_step):
                  this is where the wrap is spent.
  Sh.xk_nine, Sh.xk_ten   the two proximity tests, at their accepting decisions.
  Sh.X_of_parts   XK and "the book fits" give Sh.X, at every border (at the last: door_of_record).
  Sh.X_step       one step of the induction, by itself: what a law's "for certain" half at a piece
                  spends.
  Sh.X_reached    **the induction.**
WHAT STAYS. The facts on the parameters, in the forms that Sh.Tests gives · of the two proximity
tests' parameters: early, one answer, the first tree's number · THE CHAIN's FORM (h0, h8, h9, h10,
h11, hlen): which sub-protocol stands at which number of the list, each in the form in which its
step is spent · the first state's form (hst).
What is not claimed. Nothing on the other clauses of the promise. No soundness; no level.

-/
import Johnson.Desc.K14.Law.SharedConstLedger
import Johnson.Desc.K14.Law.LedgerSmpEarnStep
import Johnson.Top.H0.Walk.ReachInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)
open VerifiableInference.Desc.Ground (groundQuiet_tidy admitOn_tidy)

namespace Sh

variable {Xi Cl : Type} (A : ShPlan Xi)
  (hUw : withU A.Q.S = some (sentU A)) (hS : A.Q.S.sharedSplitNeeded = true)
  (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
  (hbl : blocks A.Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
  (hlU : layTrees A.Q.codes (sentU A) = some (layU A))
  (hlO : layTrees A.Q.codes (withOmega A.Q.S) = some (layO A))
  (hm : A.Q.par.S.masksAhead = true)
  (hp : ∀ b ∈ [b1, b2, b3, b4, b5, b6, b7, b8], b.planOk = true)
  (hok : A.Q.S.ok = true)
  (hC2 : condPort (parU A.Q (sentU A)) A.rad2 = true) (hC5 : condPort (parO A.Q) A.rad5 = true)
  (pyU : PlanY A.Q.codes A.Q.S.fold.u) (pyO : PlanY A.Q.codes A.Q.S.omega)
  (pyS : PlanY A.Q.codes A.Q.S.sharedSplit)

include hbl hlU hlO hm hp hok hC2 hC5 pyU pyO pyS in
/-- **One of the kind's eight, at its accepting step in the wrap.** -/
theorem xk_eight (i : ℕ) (b : Block St Unit) (hb : [b1, b2, b3, b4, b5, b6, b7, b8][i]? = some b)
    (c : Block St Cl) (hc : DecidesAs c b) (hr : c.rounds = b.rounds) (ft : ℕ) (s s' : St)
    (R : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn) (m : ℕ)
    (hst : (below c).step ft s R cols = .ok (s', m))
    (h : XK A.Q (sentU A) (layU A) (layO A) (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU
        A)).1 hUw⟩, shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩, shapeAt (parO A.Q) ⟨1,
        (places A.Q (sentU A)).2.2 hS⟩, smpK A.Q.codes (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q
        (sentU A)).1 hUw⟩) (shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩) (shapeAt (parO A.Q)
        ⟨1, (places A.Q (sentU A)).2.2 hS⟩) (sentU A).size) (sentU A).size (i + 1) s = true) :
    XK A.Q (sentU A) (layU A) (layO A) (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1
        hUw⟩, shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩, shapeAt (parO A.Q) ⟨1, (places A.Q
        (sentU A)).2.2 hS⟩, smpK A.Q.codes (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU
        A)).1 hUw⟩) (shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩) (shapeAt (parO A.Q) ⟨1,
        (places A.Q (sentU A)).2.2 hS⟩) (sentU A).size) (sentU A).size (i + 2) s' = true := by
  obtain ⟨e1, e2, e3⟩ := shapes_are A hUw hS
  have hsm := sampled A.Q (sentU A) hok
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := (XK_iff A.Q (sentU A).size (shapeAt (parU A.Q (sentU A))
      ⟨0, (places A.Q (sentU A)).1 hUw⟩, shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩, shapeAt
      (parO A.Q) ⟨1, (places A.Q (sentU A)).2.2 hS⟩, smpK A.Q.codes (shapeAt (parU A.Q (sentU A))
      ⟨0, (places A.Q (sentU A)).1 hUw⟩) (shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩)
      (shapeAt (parO A.Q) ⟨1, (places A.Q (sentU A)).2.2 hS⟩) (sentU A).size) (sentU A) (layU A)
      (layO A) (i + 1) s).1 h
  obtain ⟨_, gs, hdec⟩ := VerifiableInference.Desc.K1.step_ok _ _ _ _ _ _ _ hst
  have hd := (below_open c s s' _ gs hdec).2
  rw [hc] at hd
  have hmem := List.mem_of_getElem? hb
  have hB : blocksOr A.Q = [b1, b2, b3, b4, b5, b6, b7, b8] := by
    unfold blocksOr
    rw [hbl]
    rfl
  have mb : ∀ k d, sharedX A.Q (sentU A) (layU A) (layO A) k d = true →
      membX (sentU A).size k d = true := fun k d h =>
    ((sharedX_parts A.Q (sentU A) (layU A) (layO A) k d).1 h).2.2.1
  -- tidy: by the sub-protocol's own step
  have hT : tidY (i + 2) s' = true := (tidY_iff _ _).2
    (blocksOr_steps groundQuiet_tidy admitOn_tidy A.Q b (by rw [hB]; exact hmem) (hp b hmem) _ _ _ _
      _ _ (step_carry id (below c) b hr (fun t rs gs t' e => by
        rw [← hc]
        exact (below_open c t t' rs gs e).2) ft s R cols s' m hst) ((tidY_iff _ _).1 g4))
  have hSh := sharedX_k14 A.Q b1 b2 b3 b4 b5 b6 b7 b8 hbl (sentU A) hUw (layU A) (layO A) hlU hlO hS
    hm i b hb s s' _ gs hd g1
  have hCo := codX_k14 A.Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b hmem (i + 1) (i + 2) s s' _ gs hd g2
  obtain ⟨u, hu, eb2, eb5⟩ := blocks_two A.Q b1 b2 b3 b4 b5 b6 b7 b8 hbl
  obtain rfl : u = sentU A := Option.some.inj (hu.symm.trans hUw)
  -- the three tests on the messages' shapes
  have h3 : omY (shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩) (sentU A).size (i + 2) s' =
      true ∧
      msgY (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1 hUw⟩) 0 2 (i + 2) s' = true ∧
      msgY (shapeAt (parO A.Q) ⟨1, (places A.Q (sentU A)).2.2 hS⟩) ((sentU A).size + 1) 5 (i + 2) s'
          = true := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact ⟨(omY_iff _ _ 2 _).2 (Or.inl (by omega)), (msgY_iff _ _ _ 2 _).2 (Or.inl (by omega)),
        (msgY_iff _ _ _ 2 _).2 (Or.inl (by omega))⟩
    · have hA := (handsOn_sharedX A.Q b1 b2 b3 b4 b5 b6 b7 b8 hbl (sentU A) hUw (layU A) (layO A)
        hlU
        hlO hS hm).and (handsOn_codX A.Q b1 b2 b3 b4 b5 b6 b7 b8 hbl)
      have hBo := hands_omY A.Q b1 b2 b3 b4 b5 b6 b7 b8 hbl _ hA (sentU A).size (fun d hd =>
        ((membX45 (sentU A).size d 5 (.inr rfl)).1 (mb 5 d (Bool.and_eq_true_iff.1 hd).1)).2.2.2.1)
        (places A.Q (sentU A)).2.1 (hsm.2.1 _)
      have hCm := hands_msgY A.Q b1 b2 b3 b4 b5 b6 b7 b8 hbl _ hBo 1 _ _ _ _ _
        (behindU_book A.Q.par) (by rw [eb2]; rfl) 0 (fun d hd => ((membX2 (sentU A).size d).1 (mb 2
            d
          (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hd).1).1)).2.2.2)
        ⟨0, (places A.Q (sentU A)).1 hUw⟩ (hsm.1 hUw _) (by omega)
      have hDm := hands_msgY A.Q b1 b2 b3 b4 b5 b6 b7 b8 hbl _ hCm 4 _ _ _ _ _
        (behindOmega_book A.Q.par) (by rw [eb5]; rfl) (sentU A).size (fun d hd =>
          ((membX45 (sentU A).size d 5 (.inr rfl)).1 (mb 5 d (Bool.and_eq_true_iff.1
            (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hd).1).1).1)).2.2.2.1)
        ⟨1, (places A.Q (sentU A)).2.2 hS⟩ (hsm.2.2 _) (by omega)
      have h5 := hDm.step i b hi hb s s' _ gs hd (Bool.and_eq_true_iff.2
        ⟨Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨g1, g2⟩, g3⟩, g5⟩,
          g6⟩)
      obtain ⟨h51, q6⟩ := Bool.and_eq_true_iff.1 h5
      obtain ⟨h52, q5⟩ := Bool.and_eq_true_iff.1 h51
      exact ⟨(Bool.and_eq_true_iff.1 h52).2, q5, q6⟩
  -- smpK: earned at the two sendings, kept elsewhere
  obtain ⟨⟨kU, kO⟩, kS⟩ := (smpK_iff _ _ _ _ _ _ _).1 g7
  have hY : smpK A.Q.codes (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1 hUw⟩) (shapeAt
      (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩) (shapeAt (parO A.Q) ⟨1, (places A.Q (sentU A)).2.2
      hS⟩) (sentU A).size (i + 2) s' = true := by
    refine (smpK_iff _ _ _ _ _ _ _).2 ⟨⟨?_, ?_⟩, ?_⟩
    · by_cases h1 : i = 1
      · subst h1
        obtain rfl : b2 = b := Option.some.inj hb
        subst eb2
        have e := smpEarn_step A.Q _ (parU A.Q (sentU A)) _ _ _ (behindU_book A.Q.par) A.rad2 hC2
          ⟨0, (places A.Q (sentU A)).1 hUw⟩ (hsm.1 hUw _) (by rw [e1]; exact pyU) c hc hr ft s s' R
          cols m hst 2 3
        rw [((membX2 (sentU A).size s).1 (mb 2 s g1)).2.2.2] at e
        exact e
      · exact smp_keep _ A.Q b1 b2 b3 b4 b5 b6 b7 b8 hbl i b hb s s' _ gs hd _ _ _ (by omega) kU
    · by_cases h4 : i = 4
      · subst h4
        obtain rfl : b5 = b := Option.some.inj hb
        subst eb5
        have e := smpEarn_step A.Q _ (parO A.Q) _ _ _ (behindOmega_book A.Q.par) A.rad5 hC5
          ⟨0, (places A.Q (sentU A)).2.1⟩ (hsm.2.1 _) (by rw [e2]; exact pyO) c hc hr ft s s' R cols
          m hst 5 6
        rw [((membX45 (sentU A).size s 5 (.inr rfl)).1 (mb 5 s g1)).2.2.2.1] at e
        exact e
      · exact smp_keep _ A.Q b1 b2 b3 b4 b5 b6 b7 b8 hbl i b hb s s' _ gs hd _ _ _ (by omega) kO
    · by_cases h4 : i = 4
      · subst h4
        obtain rfl : b5 = b := Option.some.inj hb
        subst eb5
        have e := smpEarn_step A.Q _ (parO A.Q) _ _ _ (behindOmega_book A.Q.par) A.rad5 hC5
          ⟨1, (places A.Q (sentU A)).2.2 hS⟩ (hsm.2.2 _) (by rw [e3]; exact pyS) c hc hr ft s s' R
          cols m hst 5 6
        rw [((membX45 (sentU A).size s 5 (.inr rfl)).1 (mb 5 s g1)).2.2.2.1] at e
        exact e
      · exact smp_keep _ A.Q b1 b2 b3 b4 b5 b6 b7 b8 hbl i b hb s s' _ gs hd _ _ _ (by omega) kS
  exact (XK_iff A.Q (sentU A).size (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1 hUw⟩,
      shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩, shapeAt (parO A.Q) ⟨1, (places A.Q (sentU
      A)).2.2 hS⟩, smpK A.Q.codes (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1 hUw⟩)
      (shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩) (shapeAt (parO A.Q) ⟨1, (places A.Q
      (sentU A)).2.2 hS⟩) (sentU A).size) (sentU A) (layU A) (layO A) (i + 2) s').2 ⟨hSh, hCo, h3.1,
      hT, h3.2.1, h3.2.2, hY⟩

variable (πA πB : P12) (heA : πA.early = true) (ha1A : πA.answers = 1)
  (hftA : πA.nums.firstTree = A.Q.par.toGPar.firstTree)
  (heB : πB.early = true) (ha1B : πB.answers = 1)
  (hftB : πB.nums.firstTree = A.Q.par.toGPar.firstTree)
  (hl : A.Q.codes.lengthsOk = true) (hsU : (sentU A).size = 2)

include heA ha1A hftA hl hsU in
/-- **The proximity test on G_u, at its accepting decision.** -/
theorem xk_nine (s s' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (Seat.onGu (proximityTestKind guardedProximityTestParts πA : Block T12 Unit)).decide s rs gs = .ok s')
    (h : XK A.Q (sentU A) (layU A) (layO A) (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU
        A)).1 hUw⟩, shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩, shapeAt (parO A.Q) ⟨1,
        (places A.Q (sentU A)).2.2 hS⟩, smpK A.Q.codes (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q
        (sentU A)).1 hUw⟩) (shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩) (shapeAt (parO A.Q)
        ⟨1, (places A.Q (sentU A)).2.2 hS⟩) (sentU A).size) (sentU A).size 9 s = true) :
    XK A.Q (sentU A) (layU A) (layO A) (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1
        hUw⟩, shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩, shapeAt (parO A.Q) ⟨1, (places A.Q
        (sentU A)).2.2 hS⟩, smpK A.Q.codes (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU
        A)).1 hUw⟩) (shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩) (shapeAt (parO A.Q) ⟨1,
        (places A.Q (sentU A)).2.2 hS⟩) (sentU A).size) (sentU A).size 10 s' = true := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := (XK_iff A.Q (sentU A).size (shapeAt (parU A.Q (sentU A))
      ⟨0, (places A.Q (sentU A)).1 hUw⟩, shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩, shapeAt
      (parO A.Q) ⟨1, (places A.Q (sentU A)).2.2 hS⟩, smpK A.Q.codes (shapeAt (parU A.Q (sentU A))
      ⟨0, (places A.Q (sentU A)).1 hUw⟩) (shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩)
      (shapeAt (parO A.Q) ⟨1, (places A.Q (sentU A)).2.2 hS⟩) (sentU A).size) (sentU A) (layU A)
      (layO A) 9 s).1 h
  have hM := (membX_nine (sentU A).size s
    ((sharedX_parts A.Q (sentU A) (layU A) (layO A) 9 s).1 g1).2.2.1).2
  have hl' : s.st.codes.lengthsOk = true := by
    rw [(codX_iff A.Q 9 s).1 g2]
    exact hl
  exact (XK_iff A.Q (sentU A).size (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1 hUw⟩,
      shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩, shapeAt (parO A.Q) ⟨1, (places A.Q (sentU
      A)).2.2 hS⟩, smpK A.Q.codes (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1 hUw⟩)
      (shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩) (shapeAt (parO A.Q) ⟨1, (places A.Q
      (sentU A)).2.2 hS⟩) (sentU A).size) (sentU A) (layU A) (layO A) 10 s').2
    ⟨sharedX_onGu A.Q (sentU A) (layU A) (layO A) πA hftA heA ha1A s s' rs gs hd g1,
      codX_onGu A.Q πA heA ha1A 9 10 s s' rs gs hd g2,
      omY_onGu _ _ πA heA ha1A s s' rs gs hd (by rw [hM, hsU]; decide) g3,
      (tidY_iff 10 _).2 (onGu_tidy πA s s' rs gs hd hl' ((tidY_iff 9 _).1 g4)),
      msgY_onGu _ 0 2 (by omega) πA heA ha1A s s' rs gs hd (by rw [hM]; decide) g5,
      msgY_onGu _ ((sentU A).size + 1) 5 (by omega) πA heA ha1A s s' rs gs hd
        (by rw [hM, hsU]; decide) g6,
      smpKOnGu _ _ _ _ _ (by omega) πA heA ha1A s s' rs gs hd hM g7⟩

include heB ha1B hftB hl in
/-- **The proximity test on G_omega, at its accepting decision.** -/
theorem xk_ten (s s' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (Seat.onGomega (proximityTestKind guardedProximityTestParts πB : Block T12 Unit)).decide s rs gs = .ok s')
    (h : XK A.Q (sentU A) (layU A) (layO A) (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU
        A)).1 hUw⟩, shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩, shapeAt (parO A.Q) ⟨1,
        (places A.Q (sentU A)).2.2 hS⟩, smpK A.Q.codes (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q
        (sentU A)).1 hUw⟩) (shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩) (shapeAt (parO A.Q)
        ⟨1, (places A.Q (sentU A)).2.2 hS⟩) (sentU A).size) (sentU A).size 10 s = true) :
    XK A.Q (sentU A) (layU A) (layO A) (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1
        hUw⟩, shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩, shapeAt (parO A.Q) ⟨1, (places A.Q
        (sentU A)).2.2 hS⟩, smpK A.Q.codes (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU
        A)).1 hUw⟩) (shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩) (shapeAt (parO A.Q) ⟨1,
        (places A.Q (sentU A)).2.2 hS⟩) (sentU A).size) (sentU A).size 11 s' = true := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := (XK_iff A.Q (sentU A).size (shapeAt (parU A.Q (sentU A))
      ⟨0, (places A.Q (sentU A)).1 hUw⟩, shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩, shapeAt
      (parO A.Q) ⟨1, (places A.Q (sentU A)).2.2 hS⟩, smpK A.Q.codes (shapeAt (parU A.Q (sentU A))
      ⟨0, (places A.Q (sentU A)).1 hUw⟩) (shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩)
      (shapeAt (parO A.Q) ⟨1, (places A.Q (sentU A)).2.2 hS⟩) (sentU A).size) (sentU A) (layU A)
      (layO A) 10 s).1 h
  have hl' : s.st.codes.lengthsOk = true := by
    rw [(codX_iff A.Q 10 s).1 g2]
    exact hl
  exact (XK_iff A.Q (sentU A).size (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1 hUw⟩,
      shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩, shapeAt (parO A.Q) ⟨1, (places A.Q (sentU
      A)).2.2 hS⟩, smpK A.Q.codes (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1 hUw⟩)
      (shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩) (shapeAt (parO A.Q) ⟨1, (places A.Q
      (sentU A)).2.2 hS⟩) (sentU A).size) (sentU A) (layU A) (layO A) 11 s').2
    ⟨sharedX_onGomega A.Q (sentU A) (layU A) (layO A) πB hftB heB ha1B s s' rs gs hd g1,
      codX_onGomega A.Q πB heB ha1B 10 11 s s' rs gs hd g2,
      omY_onGomega _ _ πB heB ha1B s s' rs gs hd g3,
      (tidY_iff 11 _).2 (onGomega_tidy πB s s' rs gs hd hl' ((tidY_iff 10 _).1 g4)),
      msgY_onGomega _ 0 2 (by omega) πB heB ha1B s s' rs gs hd g5,
      msgY_onGomega _ ((sentU A).size + 1) 5 (by omega) πB heB ha1B s s' rs gs hd g6,
      smpKOnGomega _ _ _ _ _ πB heB ha1B s s' rs gs hd g7⟩

include hlO pyO in
/-- **XK and "the book fits" give Sh.X**, at every border. -/
theorem X_of_parts (hpS : A.p.S.omega = A.Q.S.omega) (k : ℕ) (s : St)
    (h : XK A.Q (sentU A) (layU A) (layO A) (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU
        A)).1 hUw⟩, shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩, shapeAt (parO A.Q) ⟨1,
        (places A.Q (sentU A)).2.2 hS⟩, smpK A.Q.codes (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q
        (sentU A)).1 hUw⟩) (shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩) (shapeAt (parO A.Q)
        ⟨1, (places A.Q (sentU A)).2.2 hS⟩) (sentU A).size) (sentU A).size k s = true) (hF : fitsX k
        s = true) : X A k s = true := by
  obtain ⟨_, e2, _⟩ := shapes_are A hUw hS
  rw [← X_is A hUw hS]
  refine (XW_iff A.Q (sentU A) (layU A) (layO A) _ _ A.p k s).2 ⟨h, ?_⟩
  by_cases hk : k = 12
  · subst hk
    exact (XD_iff A.p 12 s).2 ⟨hF, Or.inr (door_of_record A.Q (sentU A) (layU A) (layO A) _ _ A.p
      (by rw [e2]; exact hpS) (by rw [e2]; exact pyO.1) rfl hlO
      (by rw [sizeOmega A.Q.S hS]; decide) s h hF)⟩
  · exact XD_off A.p k hk s hF

include hUw hS hbl hlU hlO hm hp hok hC2 hC5 pyU pyO pyS heA ha1A hftA heB ha1B hftB hl hsU in
/-- **ONE STEP**: the sub-protocol at number k of the list, at its own accepting step: XK and "the
book fits" go from border k to border k + 1. -/
theorem X_step (bs : List (Block St Cl))
    (h0 : ∀ b, bs[0]? = some b → ∀ s rs gs s', b.decide s rs gs = .ok s' →
      ∃ c : Model.Verify.Chains, (frontBlock c).decide s rs gs = .ok s')
    (h8 : ∀ i b, i < 8 → bs[i + 1]? = some b → ∃ (c : Block St Cl) (b' : Block St Unit),
      [b1, b2, b3, b4, b5, b6, b7, b8][i]? = some b' ∧ b = below c ∧ DecidesAs c b' ∧
        c.rounds = b'.rounds)
    (h9 : ∀ b, bs[9]? = some b → ∀ s rs gs s', b.decide s rs gs = .ok s' →
      (Seat.onGu (proximityTestKind guardedProximityTestParts πA : Block T12 Unit)).decide s rs gs = .ok s')
    (h10 : ∀ b, bs[10]? = some b → ∀ s rs gs s', b.decide s rs gs = .ok s' →
      (Seat.onGomega (proximityTestKind guardedProximityTestParts πB : Block T12 Unit)).decide s rs gs = .ok s')
    (h11 : ∀ b, bs[11]? = some b → ∀ s rs gs s', b.decide s rs gs = .ok s' → s' = s)
    (hlen : bs.length = 12) (ft k : ℕ) (b : Block St Cl) (s s' : St) (hb : bs[k]? = some b)
    (hy : StepYes ft b s s')
    (hI : XK A.Q (sentU A) (layU A) (layO A) (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU
        A)).1 hUw⟩, shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩, shapeAt (parO A.Q) ⟨1,
        (places A.Q (sentU A)).2.2 hS⟩, smpK A.Q.codes (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q
        (sentU A)).1 hUw⟩) (shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩) (shapeAt (parO A.Q)
        ⟨1, (places A.Q (sentU A)).2.2 hS⟩) (sentU A).size) (sentU A).size k s = true ∧ fitsX k s =
        true) :
    XK A.Q (sentU A) (layU A) (layO A) (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1
        hUw⟩, shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩, shapeAt (parO A.Q) ⟨1, (places A.Q
        (sentU A)).2.2 hS⟩, smpK A.Q.codes (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU
        A)).1 hUw⟩) (shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩) (shapeAt (parO A.Q) ⟨1,
        (places A.Q (sentU A)).2.2 hS⟩) (sentU A).size) (sentU A).size (k + 1) s' = true ∧ fitsX (k
        + 1) s' = true := by
  obtain ⟨hK, hF⟩ := hI
  obtain hk | hk | hk | hk | hk | hk :
      k = 0 ∨ (1 ≤ k ∧ k ≤ 8) ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ 12 ≤ k := by omega
  · subst hk
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    obtain ⟨c, hd'⟩ := h0 b hb s rs gs s' hd
    have hx := XW_front A.Q (sentU A) (layU A) (layO A) _ _ A.p c s s' rs gs hd'
      (smpK_front_paid A.Q (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1 hUw⟩)
          (shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩) (shapeAt (parO A.Q) ⟨1, (places
          A.Q (sentU A)).2.2 hS⟩) (sentU A))
      ((XW_iff A.Q (sentU A) (layU A) (layO A) _ _ A.p 0 s).2 ⟨hK, XD_off A.p 0 (by omega) s
          hF⟩)
    obtain ⟨x1, x2⟩ := (XW_iff A.Q (sentU A) (layU A) (layO A) _ _ A.p 1 _).1 hx
    exact ⟨x1, ((XD_iff A.p 1 _).1 x2).1⟩
  · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    obtain ⟨c, b', hb', rfl, hc, hr⟩ := h8 i b (by omega) hb
    obtain ⟨R, cols, _, hs⟩ := hy
    obtain ⟨_, gs, hdec⟩ := VerifiableInference.Desc.K1.step_ok _ _ _ _ _ _ _ hs
    have hd := (below_open c s s' _ gs hdec).2
    rw [hc] at hd
    exact ⟨xk_eight A hUw hS b1 b2 b3 b4 b5 b6 b7 b8 hbl hlU hlO hm hp hok hC2 hC5 pyU pyO pyS i
        b' hb' c hc hr ft s s' R cols _ hs hK,
      fitsX_k14 A.Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b' (List.mem_of_getElem? hb') (i + 1) (i + 2) s
        s' _ gs hd hF⟩
  · subst hk
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    have hd' := h9 b hb s rs gs s' hd
    exact ⟨xk_nine A hUw hS πA heA ha1A hftA hl hsU s s' rs gs hd' hK,
      fitsX_onGu πA heA ha1A 9 10 s s' rs gs hd' hF⟩
  · subst hk
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    have hd' := h10 b hb s rs gs s' hd
    exact ⟨xk_ten A hUw hS πB heB ha1B hftB hl s s' rs gs hd' hK,
      fitsX_onGomega πB heB ha1B 10 11 s s' rs gs hd' hF⟩
  · subst hk
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    obtain rfl := h11 b hb s rs gs s' hd
    exact ⟨XK_last A.Q (sentU A) (layU A) (layO A) _ _
      (fun t ht => by
        obtain ⟨⟨kU, kO⟩, kS⟩ := (smpK_iff _ _ _ _ _ _ _).1 ht
        exact (smpK_iff _ _ _ _ _ _ _).2 ⟨⟨smpY_last _ _ _ _ (by omega) t kU,
          smpY_last _ _ _ _ (by omega) t kO⟩, smpY_last _ _ _ _ (by omega) t kS⟩) _ hK, hF⟩
  · exact absurd (List.getElem?_eq_some_iff.1 hb).1 (by omega)

include hUw hS hbl hlU hlO hm hp hok hC2 hC5 pyU pyO pyS heA ha1A hftA heB ha1B hftB hl hsU in
/-- **EVERY STATE THAT THE CHAIN's OWN ACCEPTING STEPS IN THE WRAP REACH MEETS Sh.X.** -/
theorem X_reached {P : Type} (bs : List (Block St Cl)) (start : P → St)
    (hst : ∀ z, ∃ key, start z = first A.Q.codes key)
    (h0 : ∀ b, bs[0]? = some b → ∀ s rs gs s', b.decide s rs gs = .ok s' →
      ∃ c : Model.Verify.Chains, (frontBlock c).decide s rs gs = .ok s')
    (h8 : ∀ i b, i < 8 → bs[i + 1]? = some b → ∃ (c : Block St Cl) (b' : Block St Unit),
      [b1, b2, b3, b4, b5, b6, b7, b8][i]? = some b' ∧ b = below c ∧ DecidesAs c b' ∧
        c.rounds = b'.rounds)
    (h9 : ∀ b, bs[9]? = some b → ∀ s rs gs s', b.decide s rs gs = .ok s' →
      (Seat.onGu (proximityTestKind guardedProximityTestParts πA : Block T12 Unit)).decide s rs gs = .ok s')
    (h10 : ∀ b, bs[10]? = some b → ∀ s rs gs s', b.decide s rs gs = .ok s' →
      (Seat.onGomega (proximityTestKind guardedProximityTestParts πB : Block T12 Unit)).decide s rs gs = .ok s')
    (h11 : ∀ b, bs[11]? = some b → ∀ s rs gs s', b.decide s rs gs = .ok s' → s' = s)
    (hlen : bs.length = 12) (hpS : A.p.S.omega = A.Q.S.omega) (ft k : ℕ) (a : P × St)
    (hR : Reach ft bs start k a) : X A k a.2 = true := by
  have key : XK A.Q (sentU A) (layU A) (layO A) (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU
      A)).1 hUw⟩, shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩, shapeAt (parO A.Q) ⟨1, (places
      A.Q (sentU A)).2.2 hS⟩, smpK A.Q.codes (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU
      A)).1 hUw⟩) (shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩) (shapeAt (parO A.Q) ⟨1,
      (places A.Q (sentU A)).2.2 hS⟩) (sentU A).size) (sentU A).size k a.2 = true ∧ fitsX k a.2 =
      true := by
    refine Johnson.Desc.First.Walk.Tied.Reach.inv (Inv := fun k a => XK A.Q (sentU A) (layU A) (layO
        A) (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1 hUw⟩, shapeAt (parO A.Q) ⟨0,
        (places A.Q (sentU A)).2.1⟩, shapeAt (parO A.Q) ⟨1, (places A.Q (sentU A)).2.2 hS⟩, smpK
        A.Q.codes (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU A)).1 hUw⟩) (shapeAt (parO
        A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩) (shapeAt (parO A.Q) ⟨1, (places A.Q (sentU A)).2.2
        hS⟩) (sentU A).size) (sentU A).size k a.2 = true ∧ fitsX k a.2 = true) (fun z => ?_)
      (fun k z s s' b _ hb hy hI => ?_) hR
    · obtain ⟨ky, e⟩ := hst z
      have hx := X_first A ky
      rw [← X_is A hUw hS] at hx
      obtain ⟨x1, x2⟩ := (XW_iff A.Q (sentU A) (layU A) (layO A) _ _ A.p 0 _).1 hx
      show XK A.Q (sentU A) (layU A) (layO A) (shapeAt (parU A.Q (sentU A)) ⟨0, (places A.Q (sentU
          A)).1 hUw⟩, shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩, shapeAt (parO A.Q) ⟨1,
          (places A.Q (sentU A)).2.2 hS⟩, smpK A.Q.codes (shapeAt (parU A.Q (sentU A)) ⟨0, (places
          A.Q (sentU A)).1 hUw⟩) (shapeAt (parO A.Q) ⟨0, (places A.Q (sentU A)).2.1⟩) (shapeAt (parO
          A.Q) ⟨1, (places A.Q (sentU A)).2.2 hS⟩) (sentU A).size) (sentU A).size 0 (start z) = true
          ∧ fitsX 0 (start z) = true
      rw [e]
      exact ⟨x1, ((XD_iff A.p 0 _).1 x2).1⟩
    · exact X_step A hUw hS b1 b2 b3 b4 b5 b6 b7 b8 hbl hlU hlO hm hp hok hC2 hC5 pyU pyO pyS πA πB
        heA
        ha1A hftA heB ha1B hftB hl hsU bs h0 h8 h9 h10 h11 hlen ft k b s s' hb hy hI
  exact X_of_parts A hUw hS hlO pyO hpS k a.2 key.1 key.2

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.xk_eight
#print axioms Desc.K14.Law.Sh.xk_nine
#print axioms Desc.K14.Law.Sh.xk_ten
#print axioms Desc.K14.Law.Sh.X_of_parts
#print axioms Desc.K14.Law.Sh.X_step
#print axioms Desc.K14.Law.Sh.X_reached
