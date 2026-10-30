-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanShareWide.lean: THE SHARED
"SENDING" (the kind K1): ITS SHARE OF THE THREADS' ExchangeS AT THE ITEM "tie m", AT THE PLAN's OWN
RECORD, AT ANY SIZES, AT THE READER's OWN CELLS, A BORROWED MATRIX ALLOWED. One statement and its
proof. No definition. exchangeAtS_tie_plan (Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanShare.lean)
is not turned.

  exchangeAtS_tie_wide   ExchangeAtS L.thread Said b (.tie m), from: hM · hOwn (at a valid input the
                         reader answers under the list's names as under m's own: OwnersAgree,
                         TiePlanWide.lean: IT NAMES THE INPUT) · hSmall (IT NAMES THE INPUT) ·
                         TieStateP · TieMatS · TieReadsS (TiePlanSplit.lean)

WHY. exchangeAtS_tie_plan's hmats bars a borrowed matrix, and each segment but the first has one
(TiePlanWide.lean's head): so at the place's own list that law can be met at the first segment
alone, whatever is paid. This one has its reach (ownersAgree_of_own) and is meant for all 25.

THE PROOF is exchangeAtS_tie_plan's, line for line, with tieOf_plan_wide for tieOf_plan and the two
halves for TiePlanS.

ON OwnersAgree: in the law it stands at the input's own cells under «valid», at hSmall's very
binders: of completeness's kind: NOT PUBLIC: told as such: NOT IN FRONT OF A LAW OVER COINS;
milder than hSmall. ON exchangeAtS_tie_wide: the term of exchangeAtS_tie_plan rides with it.
A public premise is swapped for a hidden one: the law reaches further and owes more: one more debt
of (P1)'s kind: what pays it comes from the trace (ownersAgree_trace, OwnersAgreeAtTrace.lean, by
cellOf_owner: under PartsFit and BorrowedSame, at Sz.ref); a premise laid anew pays nothing.
Every premise is asked and none is proved here. The term, and where the law is called:
Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanShare.lean's head.

Limits. A law under "Stepped": it holds of nothing at a book that does not cover the part's count.
It says what the witness holds; nothing on what is sent. Nothing on soundness, on completeness or on
any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TiePlanSplit
import Johnson.Desc.ProofFile.Honest.K1.Law.TiePlanWide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.Sound (MsgT Mem cellsAt)
open OnBytes.HonestTrace (Sz)
open ProofFile.Honest.K8 (signedOf)
open ProofFile.Honest.FirstThread (Letters)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr' X' P Cells Tok : Type}

/-- **THE SHARE AT THE PLAN's OWN RECORD, A BORROWED MATRIX ALLOWED**:
ExchangeAtS at the item tie m, at the member number b. exchangeAtS_tie_plan (TiePlanShare.lean) WITH
hOwn FOR hmats, AND TiePlanS AS ITS TWO HALVES. hOwn NAMES THE INPUT, as hSmall does: OF
COMPLETENESS's KIND. Where it is called: TiePlanShare.lean's head. hSmall is a premise of
completeness's kind. What pays it comes from the trace (hSmall_of_served, TieDebtsAtServed.lean:
from hTr and hMA); a premise laid anew pays nothing. -/
theorem exchangeAtS_tie_wide {L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop} {cs : OnBytes.Codes}
    {arr : ℕ → ℕ → ℕ} {ms : List Mem} {Sz₀ : Sz} {wit : Local W₀ Rc Xi Tr' → PlaceIn Xi}
    {mats : List (ℕ × String × ℕ)} {b m nR : ℕ}
    (hM : ∀ w, (L.Mg w).tie = First.K8.tieK8Rec (cellsAt cs arr ms L.N))
    (hOwn : ∀ w, L.valid w → OwnersAgree Sz₀ (wit w).R.cells mats m)
    (hSmall : ∀ w, L.valid w →
      ∀ k s r c, (signedOf ((wit w).R.cells.cell k s r c)).natAbs ≤ 128)
    (hSt : TieStateP L Said Sz₀ b m nR) (hF1 : TieMatS L Said cs arr ms Sz₀ wit b m)
    (hF2 : TieReadsS L Said cs arr ms wit mats b m nR) :
    ExchangeAtS L.thread Said b (.tie m) := by
  intro blk hblk k s μ E ds y cols s' hA hd hS ds' i hi'
  obtain rfl := List.mem_singleton.1 hi'
  have hA' := hA.1
  unfold Thr at hA'
  obtain ⟨-, -, -, -, -, -, hval⟩ := hA'
  have hS' := hS
  unfold Thread.Stepped Thread.Moved at hS'
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, -⟩ := hS'
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  obtain ⟨tl, htl, hSh, hLie, -⟩ := hSt blk hblk k s μ E ds y cols s' hA hd hS
  have hAeq := hF1 blk hblk k s μ E ds y cols s' hA hd hS tl htl ds' _ rfl
  have hSeq := hF2 blk hblk k s μ E ds y cols s' hA hd hS tl htl ds' _ rfl
  show (L.Mg y.2.st.input).tie m (L.pubOf y.2.st.input.x, s') (L.thread.strs (E.add y.1))
    (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))
  rw [ei, eh, List.append_assoc, hM]
  exact ⟨tl, htl, tieOf_plan_wide hSh (wit μ.st.input).R.cells mats (hOwn μ.st.input hval)
    (cellsSmall_cells _ _ _ (hSmall μ.st.input hval)) hLie _ hAeq hSeq⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.exchangeAtS_tie_wide
