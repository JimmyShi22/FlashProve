-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/SaltPlan.lean: the number of salt bytes in the plan that the description's frame lays
at three public files (`LPFD.Full.saltG (thePlan (asDescriptionFiles Z))`): in the goals' scope it is 40
exactly where the library's planner returns a plan.

Why. The committer that is written as mathematics over the description's frame hashes typed salts
whose length hangs on that number, while the commitment ID's string bears the number 40 as a
constant. A statement that ties that committer to a running one therefore holds only at files at
which the number is 40. This file says at which files that is.

Main statements.
  `given_salt_any`: the plan that is read back from spelled parameter bytes has the word of the salt
    as it was spelled. It is `given_salt` (OnBytes/Maker/Page/OnePlan.lean) without that law's three
    conditions: the word stands in front of everything whose length is not fixed.
  `chainsOf_key_salt`: in what `chainsOf` returns at the release's 32 lines, the parameters of the
    key file's one-time chain, as read back, have salts of 40 bytes.
  `salt_of_laid`: in scope, where the plan's seat holds a plan, the frame's number is 40.
  `salt_of_refused`: at all files, where the planner refuses, the frame's number is 0.
  `salt_iff_laid`: so in scope the number is 40 exactly where the planner returns.
  `salt_of_live`: in scope, where the description's test `protocolDataWellFormed` says yes, the number is 40.

Limits. THAT THE PLANNER RETURNS AT ANY FILES IS NOT SHOWN HERE. Nothing on a committer, on
soundness, on correctness of extraction or on a binding of the commitment.

-/
import Johnson.Goal.Numbers.DepthAtThe
import Johnson.Goal.Numbers.PlanTauInScope
import Johnson.Goal.Reads.SevenAtLive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker.Page
open OnBytes.Params Fmt

/-- The plan that the program's reader of parameter bytes returns on bytes that were spelled from a
plan P, any digest and any items has P's word of the salt. No condition on lengths or names: behind
the version's item, whose length is fixed, come the plan's eight words, and the salt's is one. -/
theorem given_salt_any {P : Plan} {c : ByteArray} {I : List (String × ByteArray)} {g : Given}
    (h : Given.read (paramsBytes P c I) = some g) : g.plan.salt = (UInt64.ofNat P.salt).toNat := by
  unfold Given.read at h
  rw [paramsReadT_eq] at h
  cases hp : paramsRead (paramsBytes P c I) with
  | none =>
    rw [hp] at h
    cases h
  | some x =>
    rw [hp] at h
    simp only [Option.bind_some] at h
    split at h
    · cases h
      show x.plan.salt = _
      have a := undoes_item _ (version_ok P.field) ByteArray.empty
        (P.bytes ++ (item configName c ++ items I))
      simp only [ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at a
      have eb : paramsBytes P c I =
          item versionName (versionValue P.field) ++
            (P.bytes ++ (item configName c ++ items I)) := by
        simp only [paramsBytes, paramsHead, ByteArray.append_assoc]
      have e2 : item versionName (versionValue P.field) ++
            (P.bytes ++ (item configName c ++ items I)) =
          item versionName (versionValue P.field) ++ P.bytes ++
            (item configName c ++ items I) := by
        simp only [ByteArray.append_assoc]
      rw [eb] at hp
      unfold paramsRead at hp
      rw [a] at hp
      dsimp only at hp
      rw [e2] at hp
      split at hp
      · rename_i P' j hr
        have hs := rdPlan_salt hr
        split at hp
        · split at hp
          · split at hp
            · obtain ⟨y, -, hy⟩ := Option.map_eq_some_iff.1 hp
              cases hy
              exact hs
            · cases hp
          · cases hp
        · cases hp
      · cases hp
    · cases h

end OnBytes.Maker.Page

namespace OnBytes.Model.Verify
open OnBytes.Params

/-- **The salt in the key file's one-time chain, in what chainsOf returns at the release's lines.**
At every digest in the argument's place. -/
theorem chainsOf_key_salt {X : Public} {layout : Option ByteArray} {c : ByteArray} {ch : Chains}
    (h : chainsOf X layout c = .ok ch) (hl : X.P.frame = recordLines) :
    ch.key.oneTime.given.plan.salt = 40 := by
  obtain ⟨r1, -, -⟩ := OnBytes.TieK.G.chainsOf_read h
  obtain ⟨shapes, hm⟩ := chainsOf_made h
  rw [hl] at hm
  obtain ⟨P1, F, e1, -, s1, -, -, -⟩ := Maker.Page.configure_salts hm
  have g1 := OneTime.read_given (KeyChains.read_parts r1).1
  have b1 : ch.bytes .keyOneTime = ch.made.keyOneTime := rfl
  rw [b1, e1] at g1
  rw [Maker.Page.given_salt_any g1]
  show (UInt64.ofNat P1.set.saltBytes).toNat = 40
  rw [s1]
  rfl

end OnBytes.Model.Verify

namespace FlashProve
open VerifierAndGoals VerifiableInference OnBytes.Model OnBytes.Model.Verify
open VerifiableInference.PlanWritten (plannedAtO plannedAtO_parts)

/-- **In scope, where the plan's seat holds a plan, its salts have 40 bytes.** -/
theorem salt_of_laid {Z : PublicFiles} (hZ : InScope Z = true) {G : OnBytes.Flat.FilesParameters LPFD.Full.XF
            OnBytes.Flat.RecFull} (h : thePlanLaid (asDescriptionFiles Z) = .ok G) :
    LPFD.Full.saltG (thePlan (asDescriptionFiles Z)) = 40 := by
  have e : thePlan (asDescriptionFiles Z) = G := thePlanAt_ok h
  rw [e]
  unfold thePlanLaid filesParametersOrRefusalAt at h
  cases hp : plannedAtO OnBytes.secondHashFunction (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL (some (asDescriptionFiles Z).lay)
      fixedConfigurationDigest with
  | error m =>
    rw [hp] at h
    cases h
  | ok p =>
    rw [hp] at h
    obtain rfl : VerifiableInference.OnPublicFiles.bigReq p = G := Except.ok.inj h
    obtain ⟨hX, hc⟩ := plannedAtO_parts hp
    show p.chains.key.oneTime.given.plan.salt = 40
    exact chainsOf_key_salt hc (H2K.Sizes.publicO_at_scope (Z := Z) hZ hX).frame

/-- **Where the planner refuses, at whatever files, the frame's plan has salts of no bytes.** -/
theorem salt_of_refused {Zk : OnBytes.K.Pub} {m : String} (h : thePlanLaid Zk = .error m) :
    LPFD.Full.saltG (thePlan Zk) = 0 := by
  unfold thePlan thePlanAt
  unfold thePlanLaid at h
  rw [h]
  rfl

/-- **In scope the frame's salts have 40 bytes exactly where the planner returns.** -/
theorem salt_iff_laid {Z : PublicFiles} (hZ : InScope Z = true) :
    LPFD.Full.saltG (thePlan (asDescriptionFiles Z)) = 40 ↔ ∃ G, thePlanLaid (asDescriptionFiles Z) = .ok G := by
  constructor
  · intro h
    cases hG : thePlanLaid (asDescriptionFiles Z) with
    | ok G => exact ⟨G, rfl⟩
    | error m =>
      rw [salt_of_refused hG] at h
      cases h
  · rintro ⟨G, hG⟩
    exact salt_of_laid hZ hG

/-- **In scope, where the description's test on the public files says yes, 40.** -/
theorem salt_of_live {Z : PublicFiles} (hZ : InScope Z = true) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    LPFD.Full.saltG (thePlan (asDescriptionFiles Z)) = 40 := by
  obtain ⟨p, hp, -⟩ := planned_of_live OnBytes.secondHashFunction (asDescriptionFiles Z) hl
  refine salt_of_laid hZ (G := VerifiableInference.OnPublicFiles.bigReq p) ?_
  unfold thePlanLaid filesParametersOrRefusalAt
  rw [hp]
  rfl

end FlashProve

#print axioms OnBytes.Maker.Page.given_salt_any
#print axioms OnBytes.Model.Verify.chainsOf_key_salt
#print axioms FlashProve.salt_of_laid
#print axioms FlashProve.salt_of_refused
#print axioms FlashProve.salt_iff_laid
#print axioms FlashProve.salt_of_live
