-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FrontsB.lean: the code switch's law: ONE NAMED TEST ON THE PLAN FOR ALL
PLACES OF THE KIND: at each place the closed facts of FrontClosed.lean (closedB, targetLikeB) at the
place's written entry. A definition with code and what its yes gives. A law file; no running text
imports it.

THE LETTERS ARE THE FOLD's: cs: the public codes · sh: the request's public shape · M: the listed
shapes of the first chain's oracle messages: all three are functions of the public files, no closed
terms: so the test is a test ON THE PLAN: a named premise of the kind's law, until the verifier's
own test on the plan asks it or a theorem in scope gives it.
CLOSED: tab: the written entries (K2Caller/LitRows.lean) · n0s, oldss: place by place the number of
messages in front and the kept old messages' numbers (n0Full | oldsFull: the values that
K2Hears/PlaceNums.lean has by the kernel for its n0At | oldsAt; n0Small | oldsSmall: as a
look at the honest small proof printed them).

  placeB cs sh M r l n0 olds   the written front of r has a frame; sh's groups have one at l;
                 closedB and targetLikeB say yes.
  k2FrontsB tab n0s oldss cs sh M   placeB at every entry of tab: entry i at the link i + 1.
  place_of_test, k2Fronts_at   what a yes gives at entry i: the frame, the group, Closed …,
                 TargetLike ….
Limits. The test is evaluated nowhere here. That n0s and oldss are the run's numbers is the walk's.
Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.FrontClosed
import Johnson.G.SwitchFrontMember

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes
open VerifiableInference.Desc.First.K2Caller (SwRow)
open Johnson.G (fxAt)

/-- The closed facts at one place. -/
def placeB (cs : Codes) (sh : Params.ReqShape) (M : List OracleShape) (r : SwRow) (l n0 : ℕ)
    (olds : List ℕ) : Bool :=
  match K2.frameAt (fxAt r), (reqGroups sh)[l]? with
  | some W₀, some g =>
    closedB (fxAt r) W₀ cs M n0 olds sh.code sh.maskCode && targetLikeB g.target (fxAt r).T
  | _, _ => false

/-- **The one test on the plan.** -/
def k2FrontsB (tab : List SwRow) (n0s : List ℕ) (oldss : List (List ℕ)) (cs : Codes)
    (sh : Params.ReqShape) (M : List OracleShape) : Bool :=
  (List.range tab.length).all fun i =>
    match tab[i]?, n0s[i + 1]?, oldss[i]? with
    | some r, some n0, some olds => placeB cs sh M r (i + 1) n0 olds
    | _, _, _ => false

/-- The full size: the messages in front of the switch into group l, l = 0 … 25. -/
def n0Full : List ℕ :=
  [0, 7, 14, 22, 29, 37, 44, 52, 59, 67, 74, 82, 89, 97, 104, 112, 119, 127, 134, 142, 149, 157,
    164, 172, 179, 185]

/-- The full size: the kept old messages of the switch into group l, l = 1 … 25. -/
def oldsFull : List (List ℕ) :=
  [[1, 2], [9], [17, 18], [24], [32, 33], [39], [47, 48], [54], [62, 63], [69], [77, 78], [84],
    [92, 93], [99], [107, 108], [114], [122, 123], [129], [137, 138], [144], [152, 153], [159],
    [167, 168], [174], []]

/-- The small example. -/
def n0Small : List ℕ := [0, 7, 14, 22, 29, 35]

def oldsSmall : List (List ℕ) := [[1, 2], [9], [17, 18], [24], []]

theorem place_of_test {cs : Codes} {sh : Params.ReqShape} {M : List OracleShape} {r : SwRow}
    {l n0 : ℕ} {olds : List ℕ} (h : placeB cs sh M r l n0 olds = true) :
    ∃ W₀ g, K2.frameAt (fxAt r) = some W₀ ∧ (reqGroups sh)[l]? = some g ∧
      Closed (fxAt r) W₀ cs M n0 olds sh.code sh.maskCode ∧ TargetLike g.target (fxAt r).T := by
  unfold placeB at h
  split at h
  · rename_i W₀ g hW hg
    rw [Bool.and_eq_true] at h
    exact ⟨W₀, g, hW, hg, closed_of_test h.1, targetLike_of_test h.2⟩
  · cases h

/-- **What a yes gives at entry i.** -/
theorem k2Fronts_at {tab : List SwRow} {n0s : List ℕ} {oldss : List (List ℕ)} {cs : Codes}
    {sh : Params.ReqShape} {M : List OracleShape} (h : k2FrontsB tab n0s oldss cs sh M = true)
    {i : ℕ} {r : SwRow} (hr : tab[i]? = some r) :
    ∃ n0 olds W₀ g, n0s[i + 1]? = some n0 ∧ oldss[i]? = some olds ∧
      K2.frameAt (fxAt r) = some W₀ ∧ (reqGroups sh)[i + 1]? = some g ∧
      Closed (fxAt r) W₀ cs M n0 olds sh.code sh.maskCode ∧ TargetLike g.target (fxAt r).T := by
  have hi : i < tab.length := (List.getElem?_eq_some_iff.1 hr).1
  have h1 := (List.all_eq_true.1 h) i (List.mem_range.2 hi)
  rw [hr] at h1
  split at h1
  · rename_i r' n0 olds e1 e2 e3
    obtain rfl := Option.some.inj e1
    obtain ⟨W₀, g, a, b, c, d⟩ := place_of_test h1
    exact ⟨n0, olds, W₀, g, e2, e3, a, b, c, d⟩
  · cases h1

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.k2Fronts_at
