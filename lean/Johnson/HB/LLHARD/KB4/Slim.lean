-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/Slim.lean: the tests on a key file's plan that tie its chains
(Key.fileClauses, Johnson/Desc/Key/FileOk.lean), carried from a source that holds just what they
read. General: no value of the release is treated.

A source (Key.Source) holds the three chains' parameter bytes, the digest of the public files and
the items' bytes, which are no written values. Most of the named tests read none of these. Here a
source is made "slim": bytes, digest and items emptied, the units of rows struck, and of the
planner's values for seven chains only the sized key, the key's three plans and the key's chains as
read kept. Then: test by test, a yes at the slim source is a yes at the source: by unfolding. The
tests that do read what was struck, and those that Lean's kernel cannot evaluate, are premises, each
in its own words.

Main names.
  givenAt, slimK, slimY, chainsAt, slimC: the slim values.
  patch m l: the list l with the answer true laid at every place where the list of marks m says
  false; behind the marks' end l stays as it is.
  carries_source, carries_shape: Key.Carries (Johnson/Desc/Key/NoCfgLive.lean) from the patched list
  at the slim value to the list at the value itself.
  plan_slim, opened_slim, front_slim: three tests are the same at the slim value: by unfolding.
  allCons, all4: tools.
Limits. chainsAt fills the fields that no test reads with the library's written values of the full
size (writtenMade, Johnson/Goal/Written/Made.lean) and idle stand-ins: they are read nowhere.
Nothing on soundness.

-/
import Johnson.Desc.Key.NoCfgLive
import Johnson.Goal.Written.Made

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open OnBytes OnBytes.Params OnBytes.Plan

/-- A chain's parameters as read, with a plan alone. -/
def givenAt (P : Fmt.Plan) : Given := ⟨.empty, P, .empty, []⟩

/-- The three chains' values without bytes, digest and items. -/
def slimK (k : KeyChains) : KeyChains :=
  ⟨⟨givenAt k.oneTime.given.plan, k.oneTime.indexMasks, k.oneTime.ranges, k.oneTime.binding,
      k.oneTime.codes, k.oneTime.lin⟩,
    ⟨givenAt k.shared.given.plan, k.shared.codes, k.shared.lin⟩,
    ⟨givenAt k.second.given.plan⟩⟩

/-- What is made of the public files, at the slim chains and without the units of rows. -/
def slimY (Y : KeySource) : KeySource :=
  ⟨slimK Y.k, Y.cutShape, Y.cutCodes, Y.cutIdx, Y.cutRanges, Y.cutSamples, Y.D, Y.told, []⟩

/-- What the planner holds of the seven chains, with a sized key, a key's plans and a key's chains;
the rest is filled with values that no test on a key file reads. -/
def chainsAt (z : KeySized) (ks : List Planned) (k : KeyChains) : Model.Verify.Chains :=
  let W := VerifiableInference.PlanWritten.Joined.writtenMade
  { made := { W.at Johnson.G.MadeFree.Hung.none with sized := { W.sized with key := z }, key := ks }
    key := k
    link := ⟨givenAt k.second.given.plan, k.shared.codes, default⟩
    proof := ⟨⟨givenAt k.second.given.plan, k.shared.codes, k.shared.lin, default, default, [], 0,
        ⟨0, 0⟩, []⟩, k.shared, k.second⟩ }

/-- The slim form of what the planner holds of the seven chains. -/
def slimC (c : Model.Verify.Chains) : Model.Verify.Chains :=
  chainsAt c.made.sized.key c.made.key (slimK c.key)

/-- The list with true laid where the marks say false. -/
def patch : List Bool → List (String × Bool) → List (String × Bool)
  | true :: m, a :: l => a :: patch m l
  | false :: m, a :: l => (a.1, true) :: patch m l
  | _, l => l

theorem allCons {a : String × Bool} {l : List (String × Bool)} (h : a.2 = true)
    (t : l.all (·.2) = true) : (a :: l).all (·.2) = true := by
  rw [List.all_cons, h, t]
  rfl

theorem all4 {a b c d : List (String × Bool)} (ha : a.all (·.2) = true) (hb : b.all (·.2) = true)
    (hc : c.all (·.2) = true) (hd : d.all (·.2) = true) :
    (a ++ b ++ c ++ d).all (·.2) = true := by
  rw [List.all_append, List.all_append, List.all_append, ha, hb, hc, hd]
  rfl

/-- Which of sourceClauses' thirty are carried from the slim value. -/
abbrev maskS : List Bool :=
  [true, false, false, false, true, false, false, true, true, true, true, false, false]

theorem carries_source (Y : KeySource)
    (h1 : (sameSetting Y.k.oneTime.given Y.k.shared.given &&
      sameSetting Y.k.oneTime.given Y.k.second.given && Y.k.shared.given.record.isNone &&
      Y.k.second.given.record.isNone) = true)
    (h2 : (sameItem Y.k.oneTime.given Y.k.shared.given "codes" &&
      Y.k.oneTime.codes == Y.k.shared.codes) = true)
    (h3 : (sameItem Y.k.oneTime.given Y.k.shared.given "the test on the table" &&
      Y.k.oneTime.lin == Y.k.shared.lin) = true)
    (h5 : readAgainOk Y.k = true) (h6 : madeAgainOk Y = true)
    (h11 : Wf.admitted Y.k.oneTime.codes Y.k.oneTime.ranges (Wf.matrixOf Y.k.oneTime.lin) = true)
    (h12 : weightsCovered Y.units Y.k.oneTime.ranges = true) :
    Carries (patch maskS (sourceClauses (slimY Y))) (sourceClauses Y) := by
  unfold sourceClauses
  refine .cons id (.cons (fun _ => h1) (.cons (fun _ => h2) (.cons (fun _ => h3) (.cons id
    (.cons (fun _ => h5) (.cons (fun _ => h6) (.cons id (.cons id (.cons id (.cons id
    (.cons (fun _ => h11) (.cons (fun _ => h12) ?_))))))))))))
  repeat (first | exact .nil | refine .cons id ?_)

/-- Which of shapeClauses' twelve are carried from the slim value. -/
abbrev maskH : List Bool :=
  [true, false, true, true, true, true, true, true, true, false]

theorem carries_shape (k : KeyChains) (made : LinShape) (h1 : OnBytes.Key.admitted k.oneTime = true)
    (h9 : (sameSetting k.oneTime.given k.shared.given &&
        sameSetting k.oneTime.given k.second.given &&
        sameItem k.oneTime.given k.shared.given "codes" &&
        sameItem k.oneTime.given k.shared.given "the test on the table" &&
      k.shared.given.record.isNone && k.second.given.record.isNone) = true) :
    Carries (patch maskH (shapeClauses (slimK k) made)) (shapeClauses k made) := by
  unfold shapeClauses
  refine .cons id (.cons (fun _ => h1) (.cons id (.cons id (.cons id (.cons id (.cons id (.cons id
    (.cons id (.cons (fun _ => h9) (.cons id (.cons id .nil)))))))))))

theorem plan_slim (k : KeyChains) (r₁ r₂ r₃ : Nat) :
    planClauses k r₁ r₂ r₃ = planClauses (slimK k) r₁ r₂ r₃ := rfl

theorem opened_slim (Y : KeySource) : openedAsTold Y = openedAsTold (slimY Y) := rfl

theorem front_slim (c : Model.Verify.Chains) : sharedFrontOk c = sharedFrontOk (slimC c) := rfl

end Johnson.KB4

#print axioms Johnson.KB4.allCons
#print axioms Johnson.KB4.all4
#print axioms Johnson.KB4.carries_source
#print axioms Johnson.KB4.carries_shape
#print axioms Johnson.KB4.plan_slim
#print axioms Johnson.KB4.opened_slim
#print axioms Johnson.KB4.front_slim
