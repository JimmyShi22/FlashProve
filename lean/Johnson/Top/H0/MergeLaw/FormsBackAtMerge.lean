-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/FormsBackAtMerge.lean: THE SIX NAMES OF "forms" THAT ARE OPEN ON
BOTH SIDES OF THE MERGE OF THE CLAIMS ON THE COMMITTED TABLE (kind K11): AT THE COMPOSED MEANING
`mgAll 𝔇 Mg` (Johnson/Desc/Sound/MgAll.lean) THE SENTENCE "forms" GOES BACK OVER THE MERGE's
ACCEPTING STEP: six of the eight that `t5_cut`'s premise hRest leaves (RidesJoin.lean).

WHAT THE TABLE's SIX NAMES STAND FOR. At the output head's sort of segment `runsOf` lays TEN runs of
the driver's under them; and at one of the ten, (5, "K8.equations") under the name 6 "small", the
composed meaning's sentence is NOT `formsQ` but `formsQA` (a form may name an array whose message is
not yet sent): `formsQ_merge` (FormsAcross.lean) does not speak of it. So:

  dataQA_same        the data that `formsQA` reads hang on the open link's context, the statement and
                     the book alone: not on the ledger
  formsQA_merge      **"forms, where a form may name what is ahead" goes back over the merge's
                     accepting step, at any run**: the sibling of `formsQ_merge`: a call of the
                     lemma `formsQA_back` (Johnson/Desc/Sound/FormsAhead.lean)
  FormsTest 𝔇 m k r s   the public test "formsIn m k r" at the composed meaning, written out
  formsTest_of_pub   it IS that test (`mgAll_pub`, `pubAll_formsIn`)
  forms_back_mgAll   **at every segment m, number k and name r other than "weights"**: from the step's
                     yes, `Fwd` at each run under the name, and the public test in front
  runs_at_sort       where segment m is of a sort, the runs under a name are `runsOf` at that sort
  six_are_ten        a closed fact: at the output head's sort the six names stand for these ten runs
  sixForms           the six names, as items
  six_forms_back     the six, in the letters of hRest

Limits. `Fwd` (what a run's reader answers in front it answers behind) IS A PREMISE, run by run: owed
by the runs' own files; shown here of no run. The public test in front is a premise: a clause of the
promise in front wherever the public item is open there: not drawn from the promise here. The two
sentences "worth" are not treated. Shown at no real state. No soundness statement.

-/
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.First.PubAllAt
import Johnson.Top.H0.MergeLaw.FormsAcross

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes OnBytes.Model OnBytes.Maker
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Item Meaning Numbers Pub pubAll pubAll_formsIn)
open VerifiableInference.Desc.K9 (segAt? Readers formsIn formsInA aheadIn aheadOf)
open VerifiableInference.Reads.Pass (Fwd)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-- **The data that "forms, with what is ahead" reads do not read the ledger.** -/
theorem dataQA_same (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ)) (a b : K9.Part)
    (rd : ℕ × ℕ → MsgQ) (hL : b.L = a.L) (hst : b.d.st = a.d.st) (hbk : b.d.book = a.d.book) :
    dataQA sent own b rd = dataQA sent own a rd := by
  unfold dataQA dataQ aheadIn aheadOf
  rw [hL, hst, hbk]

/-- **"forms, where a form may name what is ahead" BACK ACROSS THE MERGE's ACCEPTING STEP, AT ANY
RUN**: at one witness. -/
theorem formsQA_merge (Rd : Readers) (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ)) (piece : ℕ)
    (run : String) (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') (hf : Fwd Rd piece run s s')
    (hin : formsInA Rd sent own piece run s = true) (rd : ℕ × ℕ → MsgQ)
    (hq : formsQA sent own Rd piece run s' rd) : formsQA sent own Rd piece run s rd := by
  obtain ⟨pa, R, hpa, hR⟩ : ∃ pa R, segAt? s = some pa ∧ Rd.forms piece run s = some R := by
    unfold formsInA at hin
    cases e1 : segAt? s with
    | none => simp [e1] at hin
    | some pa =>
      cases e2 : Rd.forms piece run s with
      | none => simp [e1, e2] at hin
      | some R => exact ⟨pa, R, rfl, rfl⟩
  obtain ⟨a, a', pb, ha, ha', hpb, eF, eF', eL, est, ebk⟩ := seg_at_merge P h pa hpa
  obtain ⟨a₁, a₁', e1, e1', hl⟩ := decide_later h
  obtain rfl : a₁ = a := by
    rw [ha] at e1
    exact (First.Here.head.inj e1).symm
  obtain rfl : a₁' = a' := by
    rw [ha'] at e1'
    exact (First.Here.head.inj e1').symm
  have hl' : Later pa.F pb.F := by
    rw [eF, eF']
    exact hl
  have eD := dataQA_same sent own pa pb rd eL est ebk
  exact formsQA_back sent own Rd piece run s s' pa pb rd hpa hpb (by rw [hR, hf R hR]) hin
    (by rw [eL]) (fun j _ hj => (hl'.keep j hj).2) (fun _ _ _ _ _ _ _ _ => by rw [eD])
    (fun _ _ _ _ _ _ => by rw [eD]) hq

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- The public test "formsIn m k r" at the composed meaning, written out. -/
def FormsTest (m k : ℕ) (r : String) (s : S) : Prop :=
  ∀ p ∈ 𝔇.runs m k r,
    if 𝔇.ah p.1 p.2 = true then formsInA (𝔇.Rd m) (𝔇.N.sent m) (𝔇.N.group m) p.1 p.2 s = true
    else formsIn (𝔇.Rd m) (𝔇.N.group m) p.1 p.2 s = true

/-- It is that test. -/
theorem formsTest_of_pub (m k : ℕ) (r : String) (z : P) (s : S)
    (h : (mgAll 𝔇 Mg).pub (.formsIn m k r) (z, s) = true) : FormsTest 𝔇 m k r s := by
  rw [mgAll_pub, pubAll_formsIn] at h
  intro p hp
  have h1 := List.all_eq_true.1 h p hp
  by_cases e : 𝔇.ah p.1 p.2 = true
  · rw [if_pos e]
    have e' : 𝔇.pubD.ah p.1 p.2 = true := e
    rw [if_pos e'] at h1
    exact h1
  · rw [if_neg e]
    have e' : ¬ 𝔇.pubD.ah p.1 p.2 = true := e
    rw [if_neg e'] at h1
    exact h1

/-- **THE SENTENCE "forms m k r" AT THE COMPOSED MEANING GOES BACK OVER THE MERGE's ACCEPTING STEP**,
at every name but "weights", at any strings on the two sides. -/
theorem forms_back_mgAll (m k : ℕ) (r : String) (hr : r ≠ "weights") (Pm : HeadMergeP) (z : P)
    {s s' : S} (hy : ∃ rs, headMergeDecide Pm s rs = .ok s')
    (hf : ∀ p ∈ 𝔇.runs m k r, Fwd (𝔇.Rd m) p.1 p.2 s s') (hin : FormsTest 𝔇 m k r s)
    (y y' : VerifiableInference.Desc.Strs) (w : Wit (CellsQ rows cols) Tok MsgT)
    (h : (mgAll 𝔇 Mg).forms m k r (z, s') y' w) : (mgAll 𝔇 Mg).forms m k r (z, s) y w := by
  obtain ⟨rs, hy⟩ := hy
  rw [mgAll_forms] at h ⊢
  refine ⟨fun p hp => ?_, fun e => absurd e hr⟩
  have h1 := h.1 p hp
  have h2 := hin p hp
  by_cases e : 𝔇.ah p.1 p.2 = true
  · rw [if_pos e] at h1 h2 ⊢
    exact formsQA_merge _ _ _ _ _ Pm hy (hf p hp) h2 _ h1
  · rw [if_neg e] at h1 h2 ⊢
    obtain ⟨pa, hpa⟩ : ∃ pa, segAt? s = some pa := by
      unfold formsIn at h2
      cases e1 : segAt? s with
      | none => simp [e1] at h2
      | some pa => exact ⟨pa, rfl⟩
    exact formsQ_merge _ _ _ _ Pm hy pa hpa (hf p hp) h2 _ h1

/-- Where segment m is of a sort, the runs under a name are the table's own at that sort. -/
theorem runs_at_sort (m k : ℕ) (r : String) (sub : First.ModelPart) (h : 𝔇.links[m]? = some sub) :
    𝔇.runs m k r = First.runsOf sub k r := by
  show ((𝔇.links[m]?).map fun sub => First.runsOf sub k r).getD [] = _
  rw [h]
  rfl

/-- The six names, as items. -/
def sixForms : List Item :=
  [.forms 24 3 "objects", .forms 24 3 "planes", .forms 24 4 "join", .forms 24 4 "own",
    .forms 24 6 "small", .forms 24 8 "objects"]

/-- The six names, as pairs. -/
def sixNames : List (ℕ × String) :=
  [(3, "objects"), (3, "planes"), (4, "join"), (4, "own"), (6, "small"), (8, "objects")]

/-- **THE SIX, IN THE LETTERS OF `t5_cut`'s hRest.** -/
theorem six_forms_back {Fr : Frame} (Nn : Numbers) (Pm : HeadMergeP) (z : P)
    (a b : S × Fr.E.Str) (w : Wit (CellsQ rows cols) Tok MsgT)
    (hy : ∃ rs, headMergeDecide Pm a.1 rs = .ok b.1)
    (hf : ∀ x ∈ sixNames, ∀ p ∈ 𝔇.runs 24 x.1 x.2, Fwd (𝔇.Rd 24) p.1 p.2 a.1 b.1)
    (hin : ∀ x ∈ sixNames, FormsTest 𝔇 24 x.1 x.2 a.1) :
    ∀ j ∈ sixForms, meansQ Nn (mgAll 𝔇 Mg) (fun s => (z, s)) j b w →
      meansQ Nn (mgAll 𝔇 Mg) (fun s => (z, s)) j a w := by
  intro j hj hm
  unfold sixForms at hj
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · exact forms_back_mgAll 𝔇 Mg 24 3 "objects" (by decide) Pm z hy (hf (3, "objects") (by simp [sixNames]))
      (hin (3, "objects") (by simp [sixNames])) _ _ w hm
  · exact forms_back_mgAll 𝔇 Mg 24 3 "planes" (by decide) Pm z hy (hf (3, "planes") (by simp [sixNames]))
      (hin (3, "planes") (by simp [sixNames])) _ _ w hm
  · exact forms_back_mgAll 𝔇 Mg 24 4 "join" (by decide) Pm z hy (hf (4, "join") (by simp [sixNames]))
      (hin (4, "join") (by simp [sixNames])) _ _ w hm
  · exact forms_back_mgAll 𝔇 Mg 24 4 "own" (by decide) Pm z hy (hf (4, "own") (by simp [sixNames]))
      (hin (4, "own") (by simp [sixNames])) _ _ w hm
  · exact forms_back_mgAll 𝔇 Mg 24 6 "small" (by decide) Pm z hy (hf (6, "small") (by simp [sixNames]))
      (hin (6, "small") (by simp [sixNames])) _ _ w hm
  · exact forms_back_mgAll 𝔇 Mg 24 8 "objects" (by decide) Pm z hy (hf (8, "objects") (by simp [sixNames]))
      (hin (8, "objects") (by simp [sixNames])) _ _ w hm

end

/-- **What the six names stand for at the output head's sort of segment: ten runs; one of them is
the run whose forms may name what is ahead.** -/
theorem six_are_ten : sixNames.flatMap (fun x => First.runsOf .head x.1 x.2) =
    [(2, "objects"), (2, "guests"), (2, "planes"), (3, "join"), (3, "norm"), (3, "policy"),
      (3, "logits"), (5, "K8.equations"), (7, "objects"), (7, "guests")] := by decide

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.dataQA_same
#print axioms VerifiableInference.Desc.First.MergeLaw.formsQA_merge
#print axioms VerifiableInference.Desc.First.MergeLaw.formsTest_of_pub
#print axioms VerifiableInference.Desc.First.MergeLaw.forms_back_mgAll
#print axioms VerifiableInference.Desc.First.MergeLaw.runs_at_sort
#print axioms VerifiableInference.Desc.First.MergeLaw.six_forms_back
#print axioms VerifiableInference.Desc.First.MergeLaw.six_are_ten
