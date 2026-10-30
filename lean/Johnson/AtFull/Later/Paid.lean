-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Later/Paid.lean: what the proof file's description asks of its two later chains (the
shared chain and the last chain), at the public part that the planner's answer gives, all at ONE
pair of seats A and B. A joining: each field is a call of a statement that stands elsewhere; nothing
is evaluated here.

  `LaterPaid Z A B`: ten facts under one name. A helper for the joining above it: a list, no
    goal. r₆ r₇: the two makers of the later seats return A and B · c₂ c₃: their cuts into
    sub-protocols are the written ones · d₂ d₃: the rounds that their sub-protocols declare are the
    second and the third of the written declared rounds · b₂ b₃: each sub-protocol passes its own
    test on the plan · fA fB: the two seats' tests on the plan pass.
  `later_paid`: **there are such A and B**, wherever the public part X₀ is as at the full size
    (seven of the eight premises of `madeAt_fields`, Johnson/AtFull/Made/MadeAtJoinD.lean; the
    eighth, that the digest has 32 bytes, is `fixedDigest_size`) and m is the planner's answer
    there.

How the statements of several files meet at one A and one B: each speaks of "every A that the maker
returns" or of "some A that it returns"; a maker's return is one value, so they are the same.

Which premise of the statement on the shared chain (`shared_whole`, fourteen hypotheses by field)
is paid by what: the sizes, the three plans as made and as read back, the samples:
`madeAt_fields` · the request's shape: `FirstWritten` · the shared chain's shape and codes, and the
first plan made anew: Johnson/AtFull/Later/Fields.lean · the setting: `PubFull.frame` and
`proofSet_eq` · the parameters of the three proximity tests: `H2K12.members_written`.

Limits. THE SEVEN PREMISES ON X₀ ARE PREMISES HERE. The full size alone. A test on the plan that
passes says nothing on what a sub-protocol decides. Nothing on soundness or on hiding.

-/
import Johnson.AtFull.Later.Fields
import Johnson.AtFull.Desc.SharedWhole
import Johnson.AtFull.Rounds.Shared
import Johnson.AtFull.Rounds.Second
import Johnson.Loose.H2K12.K12MemberWritten
import Johnson.AtFull.Top.ProofLaidOfMade
import Johnson.Desc.Ok.PlanWritten.SizedTies

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Later
open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Params
open VerifiableInference.PlanWritten (proofSizedFull publicOfO cutSharedFull cutSecondFull
  proofSet_eq)
open VerifiableInference.PlanWritten.Joined (writtenSized)
open VerifiableInference.Number.ByRuns (proofThree)
open VerifiableInference.Desc.Key (madeAt fixedDigest fixedDigest_size)
open VerifiableInference.Desc.LinkJoin (armsB)
open Johnson.AtFull.LayoutRead (LW)
open Johnson.AtFull.Made
open Johnson.AtFull.Pub (DW decl_of_made)
open Johnson.AtFull.Desc (piU piO piW)
open Johnson.G.OfPlan (Made)
open H2K.Sizes (PubFull)
open ProofFile.Law (blankM)
open _root_.AtFull.Top (ZqM)

/-- **What the description asks of its two later chains**, at a public part Z and two seats A, B.
A list of facts under one name, for the joining above it: no goal. -/
structure LaterPaid (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) : Prop where
  r₆ : ProofFile.onlineSharedChain Z = some A
  r₇ : ProofFile.onlineLastChain Z = some B
  c₂ : VerifiableInference.PlanWritten.cutOf (A.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder = cutSharedFull
  c₃ : VerifiableInference.PlanWritten.cutOf (B.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder = cutSecondFull
  d₂ : (A.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder.flatMap (·.rounds) = DW.2.1
  d₃ : (B.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder.flatMap (·.rounds) = DW.2.2
  b₂ : ∀ b ∈ (A.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder, b.planOk = true
  b₃ : ∀ b ∈ (B.chain.retype (Cl' := ProofFile.Cl)).blocksInOrder, b.planOk = true
  fA : A.fileOk = true
  fB : B.fileOk = true

/-- **There are two seats at which all ten hold**, at the public part that the planner's answer
gives, wherever the public part X₀ of the program `verify-on-bytes` is as at the full size. -/
theorem later_paid {pol lay KL : ByteArray} {X₀ : Public} {m : Made}
    (hX : publicOfO OnBytes.secondHashFunction pol KL (some lay) = .ok X₀)
    (hm : madeAt X₀ lay fixedDigest = .ok m) (P : PubFull X₀)
    (hG : X₀.G.size = 12) (hA : X₀.A.size = 12)
    (hV : (OnBytes.TieK.listedOf X₀ default).map Decl.viewL = Decl.viewsFull)
    (bL : Plan.layoutRead lay = some LW) (ha : armsB X₀ = true)
    (hc : rangeChecksOf X₀ = some checksFull) :
    ∃ (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat), LaterPaid (ZqM pol KL m) A B := by
  obtain ⟨m', hm', F⟩ := madeAt_fields P hG hA hV bL fixedDigest_size ha hc
  have em : m' = m := Except.ok.inj (hm'.symm.trans hm)
  rw [em] at F
  obtain ⟨hx, -, -, hs, hz, hzp, hpl, -, p0, p1, p2, -, hF, -⟩ := F
  obtain ⟨r₄, r₅⟩ := shared_read P hG hA hV bL fixedDigest_size ha hc hm
  have hset : m.p.chains.made.sized.set = recordSet :=
    (congrArg (fun z => z.set) hz).trans (rfl : writtenSized.set = recordSet)
  have M := H2K12.members_written (blankM m) hset hzp hpl ⟨p0, p1, p2⟩ hs DW
    (decl_of_made hX hm hz hpl hs)
  have m₁ : H2U.p12FoldedOfMade (ZqM pol KL m).made 9 = piU := M.2.1
  have m₂ : H2U.p12OmegaOfMade (ZqM pol KL m).made 10 = piO := M.2.2.1
  have m₃ : H2U.p12OwnOfMade (ZqM pol KL m).made 2 = piW := M.2.2.2
  have hzZ : (ZqM pol KL m).p.chains.made.sized.proof = proofSizedFull := hzp
  have e₁ : firstPlan proofSizedFull
      (subproofsWith (ZqM pol KL m).p.X proofSizedFull.request.link) = .ok proofThree.A.plan := by
    show firstPlan proofSizedFull (subproofsWith m.p.X proofSizedFull.request.link) = _
    rw [hx]
    exact first_anew P hc ha
  have hS : proofSizedFull.set = settingOf (ZqM pol KL m).p.X.P.frame := by
    show proofSizedFull.set = settingOf m.p.X.P.frame
    rw [hx, P.frame]
    exact proofSet_eq
  obtain ⟨A, r₆, fA, b₂, c₂⟩ := Johnson.AtFull.Desc.shared_whole (ZqM pol KL m) hzZ hpl e₁
    (congrArg (fun p => p.entries) p0) p1 p2 r₄ r₅ (congrArg (fun p => p.samples) p0) hF.2.2.1 hS
    m₁ m₂ m₃
  obtain ⟨B, r₇, b₃, c₃, fB⟩ := Johnson.AtFull.Desc.second_share (ZqM pol KL m)
    (congrArg (·.set) hzZ) (congrArg (·.codes) hzZ) (congrArg (·.batch) hzZ) m₃
  exact ⟨A, B, r₆, r₇, c₂, c₃,
    Johnson.AtFull.Rounds.Shared.shared_decl_whole r₆ hzZ m₁ m₂ m₃,
    (Johnson.AtFull.Rounds.second_rounds_of (ZqM pol KL m) (congrArg (·.set) hzZ)
      (congrArg (·.codes) hzZ) (congrArg (·.batch) hzZ) m₃ r₇).2, b₂, b₃, fA, fB⟩

end Johnson.AtFull.Later

#print axioms Johnson.AtFull.Later.later_paid
