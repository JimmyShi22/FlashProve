-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyRangesShape15.lean: WHERE A THREAD OVER THE KEY FILE's FIRST CHAIN STANDS IN FRONT OF THE
TEST ON THE RANGES (the border 15), THE STRUCTURE THAT THE TEST's SEAT MAKES OF THE VERIFIER's STATE
HAS THE WRITTEN SHAPE `shKRFull` (Johnson/Desc/K12/Honest/Shape/TestAtKeyRangesShape.lean), the
group 0 and the fresh table's message 2: in scope. That written shape was typed off a print; here it
is held, BY THE KERNEL's OWN EVALUATION (`decide +kernel`), against the term `T15`
(E2E/KeyShapeAtFull.lean) that the run of the first chain's guards on shapes reaches from the
description's first shape. So the closed facts at that shape hold at every such state. Statements
and proofs.

  `run15_full`, `run15_six`   the guards' run over the first fifteen sub-protocols returns `T15`,
                 where the two lookups' places have their entries
  **`core15`**, `loc15`   `T15`'s core is `shKRFull`; its group is 0, its rider the message 2, its
                 mark "tidy" is set: by the kernel
  **`shape15_of_thr`**   in scope, at every thread over the first chain that begins where the
                 description starts that chain: where it stands at the border 15 the state's shape
                 is `T15`. After the pattern of `last₁_of_thr` (E2E/KeyDoorShaped.lean)
  **`testSh_15`**, `thinSh_15`   so the shape, and the thin shape, of the structure that the seat
                 makes (`rangesState`, E2E/KeyRangesSeat.lean) are the written ones
  **`leaves_15`**   so, whatever rounds and columns the proximity test's sub-protocol accepts from
                 there, the seat's leaving returns (`leaves_at_KR`,
                 …/K12/Honest/Shape/TestEndedAtKeyRanges.lean)

Limits. In scope alone: the written terms are the full size's. It says WHERE A THREAD STANDS THERE;
that one does is shown nowhere. On the verifier's state's shape alone: no field element. Nothing on
completeness, on soundness or on what is hidden.


-/
import E2E.KeyDoorShaped
import E2E.KeyRangesSeat
import Johnson.Desc.K12.Honest.Shape.TestAtKeyRangesShape
import Johnson.Desc.K12.Honest.Shape.TestEndedAtKeyRanges

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.AtFiles.Full
open OnBytes OnBytes.Params AtPublicFiles.AtFiles AtPublicFiles.KeyShape
open ProofFile.Honest AtPublicFiles.KeyLink
open H2K.Member (nKRFull piKRFull)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Key (FirstState Source LaterPlaces lookupPlace leaveRanges)
open ProofFile.Honest.Sh (shKRFull frontSh frontKR testSh thinSh leaves_at_KR)

/-! ## 1 The run over the first fifteen -/

/-- The guards' run over the first fifteen returns `T15`. The two premises: at the written public
values each of the two lookups' places has its list of rounds' entries; `shape15_of_thr` pays them
by `entries_six` (E2E/KeyShapeFullInScope.lean). -/
theorem run15_full (h0 : (lookupPlace QF.set 0 (lookAt QF.one 0)).entries.isSome = true)
    (h1 : (lookupPlace QF.set 1 (lookAt QF.one 1)).entries.isSome = true) :
    runL (gsF.take 15) T0 = .ok T15 := by
  have e : gsF.take 15 = (g0 :: [g1]) ++ (gLink QF 0 ++ gLink QF 1) ++ [gLayRows QF] := rfl
  have a : runL (g0 :: [g1]) T0 = .ok T2 := by
    rw [runL_cons _ _ _ _ step0, runL_cons _ _ _ _ step1]
    rfl
  have b : runL (gLink QF 0 ++ gLink QF 1) T2 = .ok T14 := by
    rw [runL_append _ _ _ _ (link0 h0)]
    exact link1 h1
  rw [e, runL_append _ _ _ T14 (by rw [runL_append _ _ _ _ a]; exact b),
    runL_cons _ _ _ _ step14]
  rfl

/-- Under the six equations, at whatever declared rounds, told trees and named tests; with the same
two premises. -/
theorem run15_six {Q : Pub1} (h : Six Q) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
    (v : Nat → FirstState → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (h0 : (lookupPlace QF.set 0 (lookAt QF.one 0)).entries.isSome = true)
    (h1 : (lookupPlace QF.set 1 (lookAt QF.one 1)).entries.isSome = true) :
    (Z₁W Q CF D told nKRFull v).run 15 T0 = .ok T15 := by
  unfold Z₁W
  rw [gAll₁_six h]
  rw [run_take (sh₁B Q CF) gsF v T0 15 (by decide)]
  exact run15_full h0 h1

/-! ## 2 The written shape is the run's -/

/-- **The written shape is the core of the term that the run reaches.** -/
theorem core15 : T15.1 = shKRFull := by decide +kernel

theorem loc15 : T15.2.grp = 0 ∧ T15.2.rider = some 2 ∧ T15.2.tidy = true := by decide +kernel

/-! ## 3 At a thread -/

variable {Z : VerifierAndGoals.PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- **Where a thread stands at the border 15 the state's shape is `T15`**, in scope. -/
theorem shape15_of_thr {V W Xh Pb : Type} {Bk : ProverCoinCounts} (hs : KeySourced Z X N P)
    (scope : VerifierAndGoals.InScope Z = true)
    (T₁ : Thread Bk (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl V W Xh Pb)
    (hbs : T₁.bs = (keyFileDescription X N P).first.blocksInOrder)
    (hbeg : ∀ k w h s₀, T₁.valid w → T₁.begun k w h s₀ → ∃ x, s₀ = (keyFileDescription X N P).start₁ x)
    {k : Coins Bk} {e : (keyFileDescription X N P).S₁} {m : Mid W Xh} {E : Env} (h : Thr T₁ 15 k e m E) :
    sh₁B (pubOf X) CF e = T15 := by
  obtain ⟨hN, -, -, hlen, hsh0, -, hyes, -⟩ := first_of_sourced hs scope fun _ _ _ _ => true
  obtain ⟨bw, hw, he, ha, -⟩ := public_first_sourced hs scope
  have h6 := six_sourced hs scope
  have h15 := shape_at T₁ (Z₁W (pubOf X) CF X.Y.D.1 X.Y.told.1 N fun _ _ _ _ => true) (a₀ := T0)
    (n := 19) (b := 15) (le_of_eq (by rw [hbs, hlen])) (by decide) hyes
    (fun k w h s₀ h1 h2 => by
      obtain ⟨x, rfl⟩ := hbeg k w h s₀ h1 h2
      exact (start₁_shape (cs := CF) (N := N) (X := X) (P := P) _ x).trans hsh0)
    (fun j => by
      rw [hbs]
      exact carries_whole₁ (pubOf X) CF X.Y.D.1 X.Y.told.1 N T₁.ft _ bw hw he ha j) h
  subst hN
  have q0 := entries_six X nKRFull P hs.named.plan h6 0 (by decide)
  have q1 := entries_six X nKRFull P hs.named.plan h6 1 (by decide)
  exact Except.ok.inj (h15.symm.trans (run15_six h6 _ _ _ q0 q1))

/-- **The shape of the structure that the seat makes is the written one.** -/
theorem testSh_15 {Q : Pub1} (e : FirstState) (h : sh₁B Q CF e = T15) :
    testSh (rangesState e) = frontSh shKRFull 0 (some 2) := by
  have h1 : shD e.d = T15.1 := congrArg Prod.fst h
  have h2 : e.grp = T15.2.grp := congrArg (·.2.grp) h
  have h3 : e.rider = T15.2.rider := congrArg (·.2.rider) h
  show (⟨shD e.d, e.grp, .nothing, e.rider⟩ : ProofFile.Honest.Sh.TestSh) = _
  rw [h1, h2, h3, core15, loc15.1, loc15.2.1]
  rfl

/-- The thin shape. -/
theorem thinSh_15 {Q : Pub1} (e : FirstState) (h : sh₁B Q CF e = T15) :
    thinSh (rangesState e) = frontKR := by
  have h1 : shD e.d = T15.1 := congrArg Prod.fst h
  have h2 : e.grp = T15.2.grp := congrArg (·.2.grp) h
  have h3 : e.rider = T15.2.rider := congrArg (·.2.rider) h
  show (⟨shD e.d, e.grp, .nothing, e.rider⟩ : ProofFile.Honest.Sh.ThinSh) = _
  rw [h1, h2, h3, core15, loc15.1, loc15.2.1]
  rfl

/-- **Whatever the test's sub-protocol accepts from there, the seat's leaving returns.** -/
theorem leaves_15 {Q : Pub1} (e : FirstState) (h : sh₁B Q CF e = T15) (t' : T12)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (ha : (proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).decide (rangesState e) rs gs = .ok t')
    (s : FirstState) : ∃ s', leaveRanges s t' = .ok s' :=
  leaves_at_KR (rangesState e) t' rs gs (thinSh_15 e h) ha s

end AtPublicFiles.AtFiles.Full

#print axioms AtPublicFiles.AtFiles.Full.run15_full
#print axioms AtPublicFiles.AtFiles.Full.run15_six
#print axioms AtPublicFiles.AtFiles.Full.core15
#print axioms AtPublicFiles.AtFiles.Full.loc15
#print axioms AtPublicFiles.AtFiles.Full.shape15_of_thr
#print axioms AtPublicFiles.AtFiles.Full.testSh_15
#print axioms AtPublicFiles.AtFiles.Full.thinSh_15
#print axioms AtPublicFiles.AtFiles.Full.leaves_15
