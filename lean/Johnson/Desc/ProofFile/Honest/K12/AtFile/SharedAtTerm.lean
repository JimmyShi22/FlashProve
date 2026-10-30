-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/SharedAtTerm.lean: NOT IN FRONT OF A LAW OVER COINS. The proof
file's shared chain at the base return, walked through its twelve members, with no premise left on the
chain's own members.

  stand_twelve_at_term the statement

Premises left, each named. hw: the input's key is the committer's. hds: the lists of challenges fit.

By what. stand_twelve_at_ready (SharedStandTwelve.lean), five_term_laid
(AtFullSide/K12/InstanceTerm.lean), key_fits_term (AtFullSide/K12/InstanceKeyFits.lean), walk_at_term,
zero_at_term, none_at_end (TermFacts.lean).

What the stand says. Made: the verifier's fold over the twelve members returned; that nothing is left;
the order; the trees; K14's items on the words. The thread's other letters are idle here: shape says
true, the pin of the stored table says nothing, no rider, keepsEq, rest a letter.

Limits. A walk of the thread's steps, not a run of the frame. At the base return alone. ready's return is
a premise of this theorem and every member's rounds come out of it: the ∃ says nothing until ready
returns at the base. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.SharedStandTwelve
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TermFacts
import AtFullSide.K12.InstanceKeyFits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (St blocks)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.FirstThread

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn files A)
  {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit} {nO : H2U.PlaceNums} (w : Common FullSizeMatrix IndexCommitterCoins TableKey)
  (pO : P12) (rest : Coins A.B → Common FullSizeMatrix IndexCommitterCoins TableKey → List Fmt.Drawn → WtShared)

local notation "𝐓" =>
  sharedThread h (readsBase h)
    (sharedParts h (laterTerm h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest keepsEq)) w

/-- **The shared chain at the base return, through its twelve members.** -/
theorem stand_twelve_at_term (scope : VerifierAndGoals.InScope files = true)
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling = .ok A)
    (hb : blocks (K1.qAt A.Z h.places) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hO : h.places.O = some nO) (hO' : (fourOf h.places).O = some pO)
    (hw : AtFullSide.K14.KeyIsTheCommitters A w)
    {k : Coins A.B} {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit} {x : ProofFile.Inst}
    (hR : ready h.description A.B A.H w.w₀ w.rc x k = .ok R) (hc : R.common = w)
    (ds : ℕ → List Fmt.Drawn)
    (hds : ∀ j, j < 12 → ∃ blk, (𝐓).bs[j]? = some blk ∧ drawsFit blk.rounds (ds j) = true) :
    ∃ (s : St) (m : Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit) (E : Env),
      ThrS (𝐓) (SaidField (𝐓) BaseNil) 12 k s m E ∧
      m.st.heard = ((List.range 9).flatMap fun j => ds (0 + j)) ++ ds 9 ++ ds 10 ++ ds 11 := by
  have F : WalkFacts (𝐓) 12 := walk_at_term h base pO hO' rest keepsEq w
  have P₀ : MemberPaid (𝐓) (SaidField (𝐓) BaseNil) 0 := zero_at_term h pO rest w hb F
  exact stand_twelve_at_ready h w pO rest base hb hO hO'
    (key_fits_term h scope base _ _ w hw) (none_at_end h base hb hO')
    (fun b h1 h8 => five_term_laid h w base _ pO rest keepsEq hw _ _ b h1 h8) F P₀ hR hc ds hds

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.stand_twelve_at_term
