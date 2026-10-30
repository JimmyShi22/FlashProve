-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/HeadRecord.lean: WHAT THE STATE's RECORD OF THE SMALLNESS TEST
IS BEHIND THE READS' MEMBER OF THE OUTPUT HEAD's SEGMENT: FROM THE MEMBER's OWN ACCEPT: THE PLAN's
RECORD, CLOSED AT THE TABLES THAT THE DESCRIPTION's OWN "tables" RETURNS AT THE STATE's OWN COVERED
POSITIONS AND AT WHAT THE STATE HOLDS AS HEARD. Two statements and their proofs. No definition.
Public: no witness stands in it; the run's coins and the thread's middle stand as binders of the
step alone.

  head_record         under which block the member is (the step is that block's) and which block
                      its quiet half is (hquiet): behind the step, if the state's record is tl:
                      the library's block itself says yes from s to s'; there is a state s₁ with:
                      the sending's own decision says yes from s to s₁; the quiet block says yes
                      from s₁ to s'; and the head's own part a of s₁, covered positions cov, what
                      was heard x, and tables t with: s₁.here = .head a · s₁.covered ... = .ok cov
                      · a.x = some x · tables Ph.h Ph.L Ph.hp cov x = .ok t · tl.mats and tl.NM
                      are the plan's · tl.funs = t.funs
  head_record_front   the library's TablesCome G.W s s': the record behind, tied to THE STATE IN
                      FRONT of the member: by the library's own tablesCome_at_reads
                      (Johnson/Desc/K1/Law/ArmHead.lean)

THE ROAD is tieStateS_head's (Johnson/Desc/ProofFile/Honest/K1/Law/TieStateHead.lean):
Block.step_ok, joined_yes, head_ok, closed_ok. That file keeps its own proof: it is not turned for
this.

WHAT IT IS FOR. tie_reads_head (Johnson/Desc/ProofFile/Honest/K1/Law/TieReadsHead.lean) asks hmats
and hfuns. This pays hmats where Ph.hp is the ground's plan, and brings hfuns down to: "tables"
returns one list of tables at the state's (cov, x) and at the filler's.

THE MEMBER IS A LETTER (since […]). The blocks' class of claims Cl is a letter, and the
reads' member is a letter of the type Block S Cl, with ONE PUBLIC PREMISE: hU: it has the rounds of
the library's own block IM.k1Reads (Johnson/IMR/K1Seat.lean; typed there at Unit), carried to Cl by
Block.retype, and where it says yes that block says the same yes (Block.UnderR, step_under:
Johnson/Desc/Sound/SeatGuardChain.lean). WHY: the true chain's entry at a reads' place is not that
block: it is that block, retyped, under the seat's wrappers: k01_flat_reads
(Johnson/Desc/K1/Law/K01LawTied.lean), alone_underR (Johnson/IMR/SeatForm.lean): by these two hU is
meant to be paid there; NO FILE PAYS IT YET. Of the member the proof spends its rounds and its
decision's yes alone.

Limits. hquiet is proved here at no letters; kin, not called: quiet_head_of
(Johnson/Desc/K1/Law/ReadersHeadReads.lean): at a state of the head's segment the quiet step that
accepts is head P at P.h, P.L, P.hp the ground's own three. Nothing ties cov or x to the filler's.
Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieShare
import Johnson.Desc.K1.Law.BlocksAtLater
import Johnson.Desc.K1.Law.PubAtLaterIndex
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Desc.RunLaws
import Johnson.Desc.Sound.Gather
import Johnson.Desc.Sound.SeatGuardChain
import Johnson.Desc.K1.Law.ArmHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT roundsFit_len)
open VerifiableInference.Desc.K1 (joined_yes rounds_k1Reads)
open VerifiableInference.Desc.K8.ReadsQuiet (PH head head_ok closed_ok tables)
open OnBytes.Model (HTailF2)
open OnBytes.Model.Stages (LinkH)
open ProofFile.Honest.FirstThread (Letters)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr' X' P Cells Tok : Type}

/-- **The state's record behind the head's reads, from the member's own accept.** s₁ IS TIED AT
BOTH ENDS (a find at this law's sister
att_record; it bit here too): the sending's own decision says yes from s to s₁, and the quiet block
head Ph from s₁ to s'. a is s₁'s own head's part. That a.x and cov are those of s:
head_record_front. -/
theorem head_record {L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} {X : LinkH} {pr : ℕ} {reads : Option (List ℕ)} {Ph : PH}
    (hquiet : IM.k1Quiet G 24 X = head Ph) {k : Coins Bk} {s s' : S}
    {μ : Mid (Local W₀ Rc Xi Tr') X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr') X'} {cols : List OpenedColumn}
    {blk : Block S Cl}
    (hU : blk.UnderR ((IM.k1Reads Z G 24 X pr reads).retype : Block S Cl))
    (hS : L.thread.Stepped blk k s μ E ds y cols s') {tl : HTailF2}
    (htl : s'.tl? = some tl) :
    ∃ (r₁ r₂ : Fmt.RoundView) (gs gs₁ : List (List (ℕ × List UInt64))) (rs₂ : List Fmt.RoundView)
      (gs₂ : List (List (ℕ × List UInt64))) (s₁ : S) (a : First.HeadOwn)
      (cov : OnBytes.Model.Head.Covered) (x : OnBytes.Model.Head.Heard)
      (t : OnBytes.Model.Head.Tables),
      (IM.k1Reads Z G 24 X pr reads).decide s [r₁, r₂] gs = .ok s' ∧
      (K1.laterAt (Cl := Unit) G.first (K1.gpOf Z) 24 pr 1 reads).decide s [r₁, r₂] gs₁ = .ok s₁ ∧
      (head Ph : Block S Unit).decide s₁ rs₂ gs₂ = .ok s' ∧
      s₁.here = .head a ∧ s₁.covered Ph.h.T Ph.h.V = .ok cov ∧ a.x = some x ∧
      tables Ph.h Ph.L Ph.hp cov x = .ok t ∧ tl.mats = Ph.hp.tl.mats ∧ tl.NM = Ph.hp.tl.NM ∧
      tl.funs = t.funs := by
  unfold Thread.Stepped at hS
  obtain ⟨hfit, -, hdec, -⟩ := Block.step_ok.1 (step_under hU hS.2)
  have hlen : ((roundsOf y.1).map noDigest).length = 2 := by
    rw [List.length_map, roundsFit_len _ _ hfit]
    exact rounds_k1Reads Z G 24 X pr reads
  obtain ⟨r₁, r₂, hr⟩ := List.length_eq_two.1 hlen
  rw [hr] at hdec
  have hdec : (IM.k1Reads Z G 24 X pr reads).decide s [r₁, r₂] _ = .ok s' := hdec
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ :=
    joined_yes _ _ _ _ _ (IM.k1Quiet G 24 X) s s' r₁ r₂ _ hdec
  rw [hquiet] at h3
  have h3' := h3
  obtain ⟨a, cov, x, t, tl', ha, hop, hcov, hx, ht, hc, e'⟩ := head_ok h3
  subst e'
  obtain ⟨-, rfl, -, -⟩ := closed_ok hc
  have e : some ({ Ph.hp.tl with funClosed := true, funs := t.funs } : HTailF2) = some tl := by
    rw [← htl]
    show _ = (if a.opened then some _ else none)
    rw [if_pos hop]
  obtain rfl := Option.some.inj e
  exact ⟨r₁, r₂, _, gs₁, rs₂, gs₂, s₁, a, cov, x, t, hdec, h1, h3', ha, hcov, hx, ht, rfl, rfl, rfl⟩

/-- **The same, tied to THE STATE IN FRONT OF THE MEMBER, by the library's own law**: the library's
TablesCome (Johnson/Desc/Kinds/Law/FourRunsTie.lean) from s to s': where the quiet step's own three
readers and its function "tables" return AT s (withTables_iff,
Johnson/Desc/Kinds/Law/K6Silent.lean), the record behind has these tables as its closed list, and
the plan's matrices, their number and the numbers of the arrays. By tablesCome_at_reads
(Johnson/Desc/K1/Law/ArmHead.lean). -/
theorem head_record_front {L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} {X : LinkH} {pr : ℕ} {reads : Option (List ℕ)}
    (hX : G.built[24]? = some X) {k : Coins Bk} {s s' : S}
    {μ : Mid (Local W₀ Rc Xi Tr') X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr') X'} {cols : List OpenedColumn}
    {blk : Block S Cl}
    (hU : blk.UnderR ((IM.k1Reads Z G 24 X pr reads).retype : Block S Cl))
    (hS : L.thread.Stepped blk k s μ E ds y cols s') :
    Kinds.Head.Law.TablesCome G.W s s' := by
  unfold Thread.Stepped at hS
  obtain ⟨hfit, -, hdec, -⟩ := Block.step_ok.1 (step_under hU hS.2)
  have hlen : ((roundsOf y.1).map noDigest).length = 2 := by
    rw [List.length_map, roundsFit_len _ _ hfit]
    exact rounds_k1Reads Z G 24 X pr reads
  exact K1.tablesCome_at_reads Z G X hX pr reads s s' _ _ hlen hdec

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.head_record
#print axioms ProofFile.Honest.K1.head_record_front
