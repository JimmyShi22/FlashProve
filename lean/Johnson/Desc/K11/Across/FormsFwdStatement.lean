-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Across/FormsFwdStatement.lean: THE SENTENCE "forms" GOES FORWARD OVER THE ACCEPTING
STEP OF THE MERGE OF THE CLAIMS ON THE COMMITTED TABLE (kind K11): what it says at the state in
front it says at the state behind, at one witness: STATEMENTS ALONE: three definitions of
propositions. NOTHING IS PROVED IN THIS FILE, and none is one of the library's goals: they are
lemmas' statements.

  `FormsQFwd`       `formsQ` (Johnson/Desc/Sound/FormsQ.lean), at any run
  `FormsQAFwd`     `formsQA`, where a form may name what is ahead
                   (Johnson/Desc/Sound/FormsAhead.lean), at any run
  `FormsFwdMgAll`  the field forms of the composed meaning `mgAll 𝔇 Mg`
                   (Johnson/Desc/Sound/MgAll.lean), at every segment m, number k and name r other
                   than "weights", at any strings on the two sides

Why. The library has the way BACK (`formsQ_merge`, `formsQA_merge`, `forms_back_mgAll`,
Johnson/Top/H0/MergeLaw/FormsAcross.lean and FormsBackAtMerge.lean), which its tie on soundness
spends; the honest side's frame asks the way FORWARD: an item that is open in front of the member
and that its row neither closes nor owes is to hold behind it.

The premises, as the library's own lemmas on the public tests' way forward take them
(`formsIn_merge`, `formsInA_merge`): the decision's yes · the open segment's part in front, its
ledger with its sizes, the slot of the merge's end value free · run by run: what the run's reader
answers in front it answers behind (`Fwd`), and that slot is none of the run's late ones.

Limits. ALL THESE STAY PREMISES: shown here of no state and of no run: the two on a run are owed by
the run's owner. The name "weights" is left out: the merge's member closes that item. The two
sentences "worth" are not treated. A law from a yes: idle where the decision refuses. Free of the
honest side's frame: no thread stands here. Nothing on any property.
-/
import Johnson.Top.H0.MergeLaw.FormsBackAtMerge
import Johnson.Top.H0.MergeLaw.FormsAheadAcross

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Across
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc (Wit Strs)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.K9 (Part segAt? lateAt Readers)
open VerifiableInference.Desc.Sound (MsgQ formsQ formsQA MgData mgAll CellsQ MsgT)
open VerifiableInference.Reads.Pass (Fwd)

/-- The statement on the plain sentence. Not proved here; a lemma's statement, none of the library's
goals. -/
def FormsQFwd : Prop :=
  ∀ (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String)
    (P : HeadMergeP) (s s' : S) (rs : List Fmt.RoundView),
    headMergeDecide P s rs = .ok s' → ∀ pa : Part, segAt? s = some pa → Sized pa.F →
    pa.F.gotF.getD (pa.F.next + 2 * P.lay.lk + 2) false = false → Fwd Rd piece run s s' →
    (∀ R, Rd.forms piece run s = some R →
      lateAt R.late (pa.F.next + 2 * P.lay.lk + 2) = none) →
    ∀ rd : ℕ × ℕ → MsgQ, formsQ Rd own piece run s rd → formsQ Rd own piece run s' rd

/-- The statement on the sentence with what is ahead. Not proved here; a lemma's statement, none of
the library's goals. -/
def FormsQAFwd : Prop :=
  ∀ (Rd : Readers) (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String)
    (P : HeadMergeP) (s s' : S) (rs : List Fmt.RoundView),
    headMergeDecide P s rs = .ok s' → ∀ pa : Part, segAt? s = some pa → Sized pa.F →
    pa.F.gotF.getD (pa.F.next + 2 * P.lay.lk + 2) false = false → Fwd Rd piece run s s' →
    (∀ R, Rd.forms piece run s = some R →
      lateAt R.late (pa.F.next + 2 * P.lay.lk + 2) = none) →
    ∀ rd : ℕ × ℕ → MsgQ,
      formsQA sent own Rd piece run s rd → formsQA sent own Rd piece run s' rd

/-- The statement at the composed meaning. Not proved here; a lemma's statement, none of the
library's goals. -/
def FormsFwdMgAll : Prop :=
  ∀ (Xi Pp Tok : Type) (rows cols nR : ℕ) (X : OnBytes.Model.Verify.Public)
    (𝔇 : MgData Xi Pp Tok rows cols nR X) (Mg : Meaning Pp (Wit (CellsQ rows cols) Tok MsgT))
    (m k : ℕ) (r : String), r ≠ "weights" → ∀ (P : HeadMergeP) (z : Pp) (s s' : S),
    (∃ rs, headMergeDecide P s rs = .ok s') → ∀ pa : Part, segAt? s = some pa → Sized pa.F →
    pa.F.gotF.getD (pa.F.next + 2 * P.lay.lk + 2) false = false →
    (∀ p ∈ 𝔇.runs m k r, Fwd (𝔇.Rd m) p.1 p.2 s s' ∧
      ∀ R, (𝔇.Rd m).forms p.1 p.2 s = some R →
        lateAt R.late (pa.F.next + 2 * P.lay.lk + 2) = none) →
    ∀ (y y' : Strs) (w : Wit (CellsQ rows cols) Tok MsgT),
      (mgAll 𝔇 Mg).forms m k r (z, s) y w → (mgAll 𝔇 Mg).forms m k r (z, s') y' w

end Johnson.Desc.First.ForkMerge.Across

#print axioms Johnson.Desc.First.ForkMerge.Across.FormsQFwd
#print axioms Johnson.Desc.First.ForkMerge.Across.FormsQAFwd
#print axioms Johnson.Desc.First.ForkMerge.Across.FormsFwdMgAll
