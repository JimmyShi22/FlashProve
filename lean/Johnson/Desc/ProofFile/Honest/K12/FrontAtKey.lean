-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/FrontAtKey.lean: `FrontAsks` (ShapeAll.lean in this folder) AT THE
WRITTEN PLACE OF THE KEY FILE's TEST ON THE RANGES (`piKRFull`): at every job at that place and
every input and front at which the verifier's state in front has the written thin shape (`frontKR`,
Johnson/Desc/K12/Honest/Shape/TestEndedAtKeyRanges.lean): FIVE OF ITS EIGHT CLAUSES BY THE KERNEL's
OWN EVALUATION on that shape; THE OTHER THREE, the marks that read values of the open rows, are
asked. With them the first three clauses of `DataFront` at the job made of the sending of the
multiplicities. Statements and proofs.

  `door_KRJ`, `frontPub_KR`   the door's test, in this folder's letters, and `frontPubB`
                 (FrontPubB.lean) are true at the written shape: by the kernel
  `depth_KR`     the sending's first tree has the depth 22, at the written codes and messages
  `parts_of_thin`   a structure of that thin shape passes nothing, has the written core, the group 0
                 and the fresh table's message 2
  **`frontAsks_KR`**   the thin shape · the three marks ⟹ there are plain data Dp of one tree with
                 `FrontAsks` at the key file's codes, `oneFitsB` at Dp's shape, and Dp's layout is
                 the state's
  **`front_data_KR`**   at `jobOne piKRFull Q rec₀`: beside it the first three clauses of
                 `DataFront`

Limits. At written values: `piKRFull` and the written shape were typed off prints; in scope they are
held against the description's own numbers and against the run of its guards on shapes
(`place_sourced`, E2E/KeyRangesK12.lean; `core15`, E2E/KeyRangesShape15.lean). THE THREE MARKS ARE
ASKED HERE: the mark "tidy", no row with a written-out factor, the front's test on the open rows:
they read values that hang on the challenges in front of the test; at a thread's state they are paid
in E2E/KeyRangesSeated.lean. That a state of a run has the written thin shape is not shown here
(E2E/KeyRangesShape15.lean). `DataFront`'s last clause is not touched. Nothing on completeness, on
soundness or on what is hidden.


-/
import Johnson.Desc.ProofFile.Honest.K12.FrontPubB
import Johnson.Desc.ProofFile.Honest.K12.FrontPlainAtKey
import Johnson.Desc.K12.Honest.Shape.TestAtKeyRangesShape
import Johnson.Desc.K12.Honest.Shape.TestSeatAsks

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Member (piKRFull codesKeyFull)
open Lk6.AtPlan (keyFull)
open ProofFile.Honest.Sh (ThinSh thinSh testSh frontKR shKRFull frontSh plainSh claimsB codes_KR
  testSh_front thinSh_front)

variable {W X : Type}

/-- The door's test, in this folder's letters, at the written shape. -/
theorem door_KRJ : Sh.doorB piKRFull (stA piKRFull) (stN piKRFull)
    (((laidOf piKRFull).take 1).map (·.1)) (lettersOf piKRFull (stA piKRFull) (stN piKRFull)).i
    ((lettersOf piKRFull (stA piKRFull) (stN piKRFull)).n.code,
      (lettersOf piKRFull (stA piKRFull) (stN piKRFull)).n.maskCode)
    (frontSh shKRFull 0 (some 2)) = true := by decide +kernel

theorem frontPub_KR : frontPubB piKRFull frontKR = true := by decide +kernel

/-- The depth of the sending's first tree, at the written codes and messages. -/
theorem depth_KR (P : K1.Par) (hc : P.codes = keyFull.codes)
    (hs : P.sent = Wf.messageOf keyFull.ranges.x) : (P.trees.getD 0 {}).logN = 22 := by
  have k : (parKR.trees.getD 0 {}).logN = 22 := by decide +kernel
  have e2 : parKR.sent = Wf.messageOf keyFull.ranges.x := by
    show ([("", Wf.messageOf keyFull.ranges.x)].flatMap (·.2.toList)).toArray = _
    simp
  have e : P.trees = parKR.trees := by
    unfold K1.Par.trees
    rw [hc, hs, e2]
    rfl
  rw [e]
  exact k

/-- What a structure of the written thin shape has. -/
theorem parts_of_thin (t : T12) (ht : thinSh t = frontKR) :
    t.pass = .nothing ∧ coreSh ⟨t.st, t.book, t.roots⟩ = shKRFull ∧ t.g = 0 ∧ t.mask = some 2 := by
  have hp : t.pass = .nothing := by
    have k : ProofFile.Honest.Sh.thinPass t.pass = .nothing := congrArg (·.pass) ht
    cases h : t.pass with
    | nothing => rfl
    | claim _ _ => rw [h] at k; cases k
    | single _ _ => rw [h] at k; cases k
    | switched _ _ _ => rw [h] at k; cases k
  exact ⟨hp, congrArg (·.core) ht, congrArg (·.g) ht, congrArg (·.mask) ht⟩

/-- **`FrontAsks` at the written place and shape, from the three marks.** -/
theorem frontAsks_KR (J : TestJob W X) (hJ : J.p = piKRFull) (w : W) (fr : Front X) (P : K1.Par)
    (hc : P.codes = keyFull.codes) (hs : P.sent = Wf.messageOf keyFull.ranges.x)
    (ht : thinSh (J.rec₀ w fr) = frontKR) (m1 : stTidyB (J.rec₀ w fr).st = true)
    (m2 : stPlainB (J.rec₀ w fr).st = true) (m3 : claimsB (J.rec₀ w fr) = true) :
    ∃ Dp : Plain, Dp.ts.length = 1 ∧ FrontAsks J w fr codesKeyFull Dp ∧
      oneFitsB piKRFull P (plainSh Dp) = true ∧ Dp.L = layoutAt (J.rec₀ w fr) := by
  obtain ⟨hp, hcore, hg, hm⟩ := parts_of_thin _ ht
  obtain ⟨Dp, hB, hL, hpl⟩ := plain_at_KR P hc hs _ ht
  have hsh : testSh (J.rec₀ w fr) = frontSh shKRFull 0 (some 2) := by
    rw [testSh_front hp, hcore, hg, hm]
    rfl
  have h1 : Dp.ts.length = 1 := by
    obtain ⟨s, u, Ly, H⟩ := oneFits_of_B piKRFull ⟨P, fun _ => none, fun (_ : Unit) _ _ _ => none,
      ⟨⟨0, none, 0, .K1⟩, 0⟩⟩ (J.rec₀ w fr) Dp hB hL
    rw [H.ts]
    rfl
  refine ⟨Dp, h1, ⟨?_, ?_, ?_, m1, m2, m3, ?_, ?_⟩, hB, hL⟩
  · have k : (coreSh ⟨(J.rec₀ w fr).st, (J.rec₀ w fr).book, (J.rec₀ w fr).roots⟩).st.codes =
        (J.rec₀ w fr).st.codes := rfl
    rw [← k, hcore]
    exact codes_KR
  · rw [hJ, hsh]
    exact door_KRJ
  · rw [hm]
    rfl
  · rw [hJ]
    exact hpl
  · intro G id hG hid
    rw [hJ]
    exact frontPub_of_B piKRFull _ hp (by decide +kernel) (by rw [ht]; exact frontPub_KR) G id hG
      hid

/-- **At the job made of the sending: beside it the first three clauses of `DataFront`.** -/
theorem front_data_KR (Q : OneSent W) (rec₀ : W → Front X → T12) (w : W) (fr : Front X)
    (C : TestCoins) (hc : Q.P.codes = keyFull.codes)
    (hs : Q.P.sent = Wf.messageOf keyFull.ranges.x) (ht : thinSh (rec₀ w fr) = frontKR)
    (m1 : stTidyB (rec₀ w fr).st = true) (m2 : stPlainB (rec₀ w fr).st = true)
    (m3 : claimsB (rec₀ w fr) = true) :
    ∃ Dp : Plain, Dp.ts.length = 1 ∧ FrontAsks (jobOne piKRFull Q rec₀) w fr codesKeyFull Dp ∧
      ColsAt (stA piKRFull) Dp
        (colsFrom ((jobOne piKRFull Q rec₀).trees₀ w fr C.mem
          ((jobOne piKRFull Q rec₀).first w fr C)) Dp.ts)
        (plainOne Q w (C.mem 0) ((jobOne piKRFull Q rec₀).first w fr C)) ∧
      StateAt (stA piKRFull) Dp ((jobOne piKRFull Q rec₀).first w fr C)
        (plainOne Q w (C.mem 0) ((jobOne piKRFull Q rec₀).first w fr C)) ∧
      (jobOne piKRFull Q rec₀).trees₀ w fr C.mem ((jobOne piKRFull Q rec₀).first w fr C) =
        groupTrees Dp.ts (logAt Dp.book)
          (colsFrom ((jobOne piKRFull Q rec₀).trees₀ w fr C.mem
            ((jobOne piKRFull Q rec₀).first w fr C)) Dp.ts) := by
  obtain ⟨Dp, h1, F, hB, hL⟩ :=
    frontAsks_KR (jobOne piKRFull Q rec₀) rfl w fr Q.P hc hs ht m1 m2 m3
  obtain ⟨a, b, c⟩ := three_of_B piKRFull Q rec₀ w fr C Dp hB hL
  exact ⟨Dp, h1, F, a, b, c⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.door_KRJ
#print axioms ProofFile.Honest.K12.frontPub_KR
#print axioms ProofFile.Honest.K12.depth_KR
#print axioms ProofFile.Honest.K12.parts_of_thin
#print axioms ProofFile.Honest.K12.frontAsks_KR
#print axioms ProofFile.Honest.K12.front_data_KR
