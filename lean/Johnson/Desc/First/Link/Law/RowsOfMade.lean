-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/RowsOfMade.lean: THE SECOND READING OF THE THREE PUBLIC FILES IN TERMS
OF THE PROOF FILE's OWN PUBLIC PART: what its maker has made, the number of the request's links, the
number of the groups of layers, and the links' arms. AT THE SECOND HASH FUNCTION. Theorems on
public data. A law file; no running text imports it.
  `withReply_length`, `open_rows`   BY THE MAKE: where shapesOf returns shapes and configure returns
                    made at them: shapes.sub.openRows = List.replicate
                    made.sized.proof.request.link.length 1 and shapes.sub.pendingRows = X.NGr + 1.
  `made_tie`        ProofFile.pubPlain secondHashFunction pol lay KL = .ok Zp · Verify.planned pol KL (some lay) = .ok
                    p ⊢ p.X is Zp's; the four fields of p.chains.made that do not hang on the digest
                    are Zp's; shapesOf returns at it; configure returns Zp's "made" at these shapes.
  `rows_of_made`    … ⊢ sendRowsOf pol lay KL = rowsFrom Zp.made.p.chains.made
                    (List.replicate Zp.made.p.chains.made.sized.proof.request.link.length 1)
                    (Zp.made.p.X.NGr + 1) (armOf Zp.made.p.X).

Limits. That planned returns is a premise (other files have it from the description's test
protocolDataWellFormed). That rowsFrom returns is shown nowhere here. Nothing on soundness or on hiding.

-/
import Johnson.Desc.First.Link.Law.RowsFromCongr
import Johnson.Desc.ProofFile.Law.PlainIsMade
import Johnson.Goal.Numbers.PlanTauInScope
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws
import OnBytes.Model.Fit.PlannedParts
import OnBytes.Tie.EntryPlanAtCfg
import OnBytes.Plan.PlanListsProof
import OnBytes.Params.Fit.TreesSized

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G (sendRowsOf)

theorem withReply_length : ∀ l : List ReqLink, (OnBytes.Model.Verify.withReply l).length = l.length
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    unfold OnBytes.Model.Verify.withReply
    rw [List.length_cons, List.length_cons, withReply_length (b :: l)]

/-- **The open rows and the pending rows, by the make.** -/
theorem open_rows {X : OnBytes.Model.Verify.Public} {lay : Option ByteArray}
    {ls : Array OnBytes.Model.Stages.LinkH} {shapes : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (hs : OnBytes.Model.Verify.shapesOf X lay = .ok (ls, shapes))
    (hc : configure X.P.frame shapes cfg bits = .ok made) :
    shapes.sub.openRows = List.replicate made.sized.proof.request.link.length 1 ∧
      shapes.sub.pendingRows = X.NGr + 1 := by
  obtain ⟨_, _, rl, _, _, he⟩ := OnBytes.Model.Verify.shapesOf_sub hs
  obtain ⟨_, hl, _⟩ := proofSized_request (configure_proof_sizes hc).1
  rw [hl, he]
  refine ⟨?_, rfl⟩
  show List.replicate rl.length 1 = _
  unfold fillLinks
  rw [List.length_map]
  show _ = List.replicate (OnBytes.Model.Verify.withReply rl).length 1
  rw [withReply_length]

section
variable {pol lay KL : ByteArray} {Zp : ProofFile.Pub} {p : OnBytes.Model.Verify.Planned}

/-- What the two planners' values share. -/
theorem made_tie (h : ProofFile.pubPlain OnBytes.secondHashFunction pol lay KL = .ok Zp)
    (hp : OnBytes.Model.Verify.planned pol KL (some lay) = .ok p) :
    p.X = Zp.made.p.X ∧ p.chains.made.sized = Zp.made.p.chains.made.sized ∧
      p.chains.made.key = Zp.made.p.chains.made.key ∧
      p.chains.made.proof = Zp.made.p.chains.made.proof ∧
      p.chains.made.entry = Zp.made.p.chains.made.entry ∧
      ∃ ls shapes, OnBytes.Model.Verify.shapesOf p.X (some lay) = .ok (ls, shapes) ∧
        configure p.X.P.frame shapes VerifiableInference.Desc.fixedConfigurationDigest 0 =
          .ok Zp.made.p.chains.made := by
  unfold OnBytes.Model.Verify.planned at hp
  obtain ⟨X, hX, hp⟩ := exc_bind hp
  dsimp only at hp
  obtain ⟨ch, hc, hp⟩ := exc_bind hp
  obtain ⟨b, _, hp⟩ := exc_bind hp
  cases hp
  obtain ⟨m, hm, hb⟩ := ProofFile.Law.pub_madeOfAtO
    (show ProofFile.pureRoad.pub OnBytes.secondHashFunction pol lay KL = .ok Zp from h)
  unfold VerifiableInference.PlanWritten.madeOfAtO at hm
  obtain ⟨p', hp', hm⟩ := exc_bind hm
  obtain ⟨s', _, hm⟩ := exc_bind hm
  have ep := VerifiableInference.Number.packMade_p hm
  have e1 : Zp.made.p.chains = p'.chains := by
    rw [← hb, ← ep]
    rfl
  have e0 : Zp.made.p.X = p'.X := by
    rw [← hb, ← ep]
    rfl
  obtain ⟨hX', hc'⟩ := VerifiableInference.PlanWritten.plannedAtO_parts hp'
  rw [VerifiableInference.PlanWritten.publicOfO_older] at hX'
  obtain rfl : X = p'.X := Except.ok.inj (hX.symm.trans hX')
  obtain ⟨l1, x1, hs1, hf1, _, _⟩ := OnBytes.Model.Verify.chainsOf_parts hc
  obtain ⟨l2, x2, hs2, hf2, _, _⟩ := OnBytes.Model.Verify.chainsOf_parts hc'
  obtain ⟨-, rfl⟩ : l1 = l2 ∧ x1 = x2 := Prod.mk.inj (Except.ok.inj (hs1.symm.trans hs2))
  obtain ⟨a1, a2, a3, b1, b2, b3, _, _, hat⟩ := OnBytes.Tie.configure_at hf1
  have e2 := Except.ok.inj ((hat VerifiableInference.Desc.fixedConfigurationDigest).symm.trans hf2)
  rw [e0, e1, ← e2]
  refine ⟨rfl, rfl, rfl, rfl, rfl, l1, x1, hs1, ?_⟩
  rw [e2]
  exact hf2

/-- **The second reading, in terms of the proof file's own public part.** -/
theorem rows_of_made (h : ProofFile.pubPlain OnBytes.secondHashFunction pol lay KL = .ok Zp)
    (hp : OnBytes.Model.Verify.planned pol KL (some lay) = .ok p) :
    sendRowsOf pol lay KL = rowsFrom Zp.made.p.chains.made
      (List.replicate Zp.made.p.chains.made.sized.proof.request.link.length 1)
      (Zp.made.p.X.NGr + 1) (armOf Zp.made.p.X) := by
  obtain ⟨eX, e1, e2, e3, e4, ls, shapes, hs, hc⟩ := made_tie h hp
  obtain ⟨o1, o2⟩ := open_rows hs hc
  rw [sendRowsOf_of hp hs, o1, o2, eX]
  exact rowsFrom_four e1 e2 e3 e4 _ _ _

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.open_rows
#print axioms VerifiableInference.Desc.LinkJoin.made_tie
#print axioms VerifiableInference.Desc.LinkJoin.rows_of_made
