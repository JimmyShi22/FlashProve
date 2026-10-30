-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieStateAttPlan.lean: TieStateP
(Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanShare.lean) AT AN ATTENTION's SEGMENT: THE PUBLIC HALF
OF THE SHARE AT THE ITEM "tie m", AT ANY SIZES. One definition of a premise's form, one statement
and its proof. No witness. The sister of tieStateP_layers (TieStatePlan.lean) and tieStateP_head
(TieStateHeadPlan.lean).

  AttTlS          PUBLIC, ON THE STATE IN FRONT ALONE: under the thread's own binders: an
                  attention's part is open, and its record has the plan's public part (the
                  library's TlLike at A.seam.tl)
  tieStateP_att   TieStateP L Said Sz₀ b m A.nW, from: hblk · hU · hX, hk (the built link at m has
                  the kind 1) · hA (the group's attention has the plan A) · hShape (A.seam.tl has
                  Sz₀'s shapes at m) · hSame (A.mats and A.seam.tl.mats have the same rows and
                  columns) · AttTlS

THE ROAD: att_record, tablesLie_att (AttRecord.lean); over the member's accept the record's public
part stays: the library's tlLike_over_reads (Johnson/Desc/K1/Law/ArmAttMats.lean); TablesLie.same
(Johnson/HonestTrace/Reads.lean); TieStateP's last conjunct off the quiet step's own guard of order:
orderOk_fixed (Johnson/Desc/K8/ReadsQuietLaws.lean).

WHO MIGHT PAY AttTlS: it is the library's clause TlIsPlan on a state
(Johnson/Desc/K1/Law/ArmAttPaid.lean), with "an attention's part is open", at the thread's stands.
NOT HERE. hShape and hSame are closed facts on the plan: evaluated nowhere.

ON AttTlS: "YES, ON THREE TERMS ... (1)
AttTlS, hShape and hSame are paid by nobody: nothing counts · (2) ... TieStateP's first conjunct at
attention is EXCHANGED for AttTlS with hShape, not paid · (3) A is a letter tied by hA to X.g;
TlIsPlan takes W.A[linkNo s / 2]: that the two are one is said nowhere". The proof does not lean on
att_record's a being s's part: it takes a₀ from AttTlS at s, carries it by tlLike_over_reads, and
meets att_record's record through "s'.tl? = some ..." alone.

Limits. A law under "Stepped". AttTlS has no member and no negative test; IT MAY HOLD EMPTILY.
Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.AttRecord
import Johnson.Desc.ProofFile.Honest.K1.Law.TiePlanShare
import Johnson.Desc.K1.Law.ArmAttMats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att (tabsBack)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K8.ReadsQuiet (orderOk_fixed)
open OnBytes.HonestTrace (Sz ShapesFit TablesLie SameSizes)
open OnBytes.Model.Stages (LinkH)
open ProofFile.Honest.FirstThread (Letters)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr' X' P Cells Tok : Type}

/-- **PUBLIC: IN FRONT OF the member's step an attention's part is open, and its record of the
smallness test has the plan's public part**: its matrices, their number, the numbers of the arrays
of reads and of the symbol arrays are those of A.seam.tl (the library's TlLike,
Johnson/Desc/K1/Law/ArmAttPaid.lean), under the thread's own binders. ON THE STATE IN FRONT ALONE.
No witness; no coin is read; nothing of the input; nothing of what was heard. WHY IT IS ASKED AT
ATTENTION ALONE: at a layers' segment and at the head the quiet step lays the plan's own record; at
an attention's it closes the list that the state holds. IT MAY HOLD EMPTILY. A definition: a
premise's form. NO MEMBER, NO NEGATIVE TEST. -/
def AttTlS (L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop) (b : ℕ)
    (A : OnBytes.Attention.Plan) : Prop :=
  ∀ blk, L.bs[b]? = some blk → ∀ k s μ E ds y cols s', ThrS L.thread Said b k s μ E →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k s μ E ds y cols s' →
    ∃ a₀, s.here = .att a₀ ∧ K1.TlLike A.seam.tl a₀.tl

/-- **The public half at an attention's segment, at sizes Sz₀.** The sister of tieStateP_layers and
tieStateP_head. -/
theorem tieStateP_att {Sz₀ : Sz} {L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop} {b m : ℕ} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} {X : LinkH} {pr : ℕ} {reads : Option (List ℕ)}
    {A : OnBytes.Attention.Plan} {blk₁ : Block S Cl} (hblk : L.bs[b]? = some blk₁)
    (hU : blk₁.UnderR ((IM.k1Reads Z G m X pr reads).retype : Block S Cl))
    (hX : G.built[m]? = some X) (hk : X.kind = 1) (hA : G.W.A[X.g]? = some A)
    (hShape : ShapesFit A.seam.tl Sz₀ m)
    (hSame : SameSizes A.mats A.seam.tl.mats) (hTl : AttTlS L Said b A) :
    TieStateP L Said Sz₀ b m A.nW := by
  intro blk hb k s μ E ds y cols s' hT hd hS
  obtain rfl : blk₁ = blk := Option.some.inj (hblk.symm.trans hb)
  obtain ⟨r₁, r₂, gs, -, s₁, a, -, g, p, t, hdec, -, -, -, -, -, -, ht, hord, htl⟩ :=
    att_record hk hA hU hS
  obtain ⟨a₀, hs0, hL0⟩ := hTl _ hb k s μ E ds y cols s' hT hd hS
  obtain ⟨tl', htl', hL1⟩ :=
    K1.tlLike_over_reads Z G m X hX pr reads s s' [r₁, r₂] gs rfl hdec a₀ hs0
  obtain rfl := Option.some.inj (htl'.symm.trans htl)
  have hL := hL0.trans hL1
  refine ⟨_, htl, fun ν hν => ?_, ?_, (orderOk_fixed hord).1.ge⟩
  · rw [hL.mats]
    exact hShape ν (hL.NM ▸ hν)
  · rw [hL.mats]
    exact TablesLie.same hSame (tablesLie_att (mats := A.mats) ht)

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.AttTlS
#print axioms ProofFile.Honest.K1.tieStateP_att
