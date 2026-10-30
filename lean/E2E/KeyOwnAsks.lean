-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyOwnAsks.lean: `OwnAsks` at a stand, joined from what has been shown of each clause.

  `own_asks`: agree by `agree_at_W`; opens by `opensFit_KW` and `hold`; dense and claims by `entry_marks` from `OwnMark`; say as given.

Left as premises: `hm`, `hf`: the job has `jobOwn`'s count of members and a fresh table; `hdepth`: the trees' depths; `hsent`: E.sent is 0: a
stand gives `treesTo T.bs 2`, and the last chain sends none in front of the test; `hold`: `OldAt` (lot P3); `hmark`: `OwnMark` at the stand (`mark_at_two`);
`hsay` (`say_stand`).
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyOwnAccepted
import E2E.KeyOwnAgree
import E2E.KeyOwnEntry
import E2E.KeyOwnOpens

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyLastChain
open ProofFile.Honest ProofFile.Honest.K12
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃)
open AtPublicFiles.AtFiles (sh₃ SF)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyTest (jobOwn)
open H2K.Member (piKWFull)

variable {W Y V : Type}

/-- **The five clauses, joined.** -/
theorem own_asks (A : Light.ManyJob W Y) (K₀ : KeyPub) (hK₀ : fullPub = some K₀)
    (hp : A.toRun.toTest.p = piKWFull) (hm : A.toRun.toTest.members.length = jobOwn.members.length)
    (f : Addr × ℕ) (hf : A.toRun.toTest.fresh = some f) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (m : Mid W Y) (E : Env) (c : RowCoins [(firstPart A.toRun.toTest : Part V W Y), restPart A.toRun.toTest])
    (hc : lendRow (keyBook K₀) rows look A.toRun.toTest.p.place
      [(firstPart A.toRun.toTest : Part V W Y), restPart A.toRun.toTest] 0 = .ok c)
    (st : S₃) (he : enterOwn st = .ok (A.toRun.toTest.rec₀ m.st.input (frontOf m))) (hsh : sh₃ SF st = A2)
    (hmark : OwnMark st)
    (hdepth : (A.toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1).mem
      (A.toRun.toTest.first m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1))).map (·.1) = [13, 22, 22])
    (hsent : E.sent = 0)
    (hold : OldAt E (A.toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1).mem
      (A.toRun.toTest.first m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1)))
      (fun k => [Fmt.TreeSource.taken 0 0, .taken 0 5, .taken 1 1].getD k (.own 0)))
    (hsay : ∀ G, (A.toRun.toTest.rec₀ m.st.input (frontOf m)).st.groups[
        (A.toRun.toTest.rec₀ m.st.input (frontOf m)).g]? = some G →
      OnBytes.Means.AllSay OnBytes.Slice.rdE (OnBytes.Slice.begun (A.toRun.toTest.rec₀ m.st.input (frontOf m)).st
          (A.toRun.toTest.rec₀ m.st.input (frontOf m)).g G)
        (OnBytes.Slice.runRows (A.toRun.toTest.rec₀ m.st.input (frontOf m)).st G).toList
        (wordsAt (OnBytes.Slice.begun (A.toRun.toTest.rec₀ m.st.input (frontOf m)).st
            (A.toRun.toTest.rec₀ m.st.input (frontOf m)).g G)
          (OnBytes.Means.layoutOf (A.toRun.toTest.rec₀ m.st.input (frontOf m)).st G)
          (Light.plainMany A m.st.input (frontOf m) (restCoins A.toRun.toTest c.2.1)))) :
    OwnAsks A m E c := by
  obtain ⟨h1, h2⟩ := entry_marks he hsh hmark
  refine ⟨agree_at_W K₀ hK₀ A hp hm f hf rows look c hc _ _, ⟨[13, 22, 22], _, hdepth, ?_, hold⟩, h2, h1, hsay⟩
  rw [hsent]
  exact opensFit_KW _ hp (by rw [hf]; rfl)

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.own_asks
