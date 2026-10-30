-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/SampleAt.lean: the sample row as the record holds it. Statements and proofs.

It mends a fault of two other files. `says_sample` (Johnson/Desc/K12/Law/SaysSample.lean) and
`answers_of_says` (Johnson/Desc/K12/Law/ShareWords.lean) speak of the row that `Send.form` returns.
That is the sample row's left side: its target is the default, 0 (OnBytes/Iop/Send.lean: "{ kind :=
.sample }"); what `Send.verify` lays into the record is "{ row with target := y }", y the answer
received. So both theorems, true as typed, said "… = fun _ => readE row.target" at a target that is
0. At a real record's row, whose answer is not 0, their premise "Send.form … = some r" is false:
they could be called at no real row.
Main names:
  `mem_foldl_samples`, `sample_mem_runRows`: a member's sample row stands among the rows that the
    proximity test takes in (the library's `runRows S G`: the plain rows; each member's sample rows;
    the generator rows): from o ∈ G.members, S.oracles[o]? = some x and r ∈ x.sampleRows: r ∈
    runRows S G.
  `value_target`: a row's value on words does not read its target: by rfl.
  `says_sample_t`: under the premises of `says_sample`, for every t: Says rdE S { row with target :=
    t } m ↔ (portZ …).val (the seed read, β) (the message that the words hold) = fun _ => readE t.
  `answers_of_says_t`: hS at that row: `answers_of_says` with { row with target := t } and readE t.
Limits: what is still owed for hS at a real member:
(1) That the record's entry x.sampleRows[0] is { row with target := t } for row := Send.form S.codes
x.shape o seed 0 at some seed with seed.z.length = bitsZ and β ≠ 0. The record keeps the rows, not
the seeds: it is an invariant of the record that the sending lays and every block behind it must
keep: for the law of the sending to pay. `Send.verify` draws one point for all messages of a round,
of "bits" coordinates, the largest of their cubes'; `Send.form` takes seed.z.take …. Where a
message's own cube is smaller, seed.z.length = bitsZ fails as typed: the premise hz of `says_sample`
wants "at least", or the seed cut to the cube. Johnson/Desc/K12/Law/FormTake.lean has that form.
(2) `runRows` is taken at the statement in front of the batching; the S of `answers_of_says_t` is
the statement behind (`begun S g G`). The closing of ledgers turns neither shapes nor sample rows:
not typed here (see `begun_samples`, Johnson/Desc/K12/Law/TieFront.lean).
No soundness is claimed, and nothing is said on hiding.
Lemmas called (none runs in a context of `verify-on-bytes`): `value_sample`, `words_share`,
`blank_of_near`, `padded_wordsOf`.
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.ShareWords

set_option autoImplicit false
namespace H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays

theorem mem_foldl_samples (S : Statement) (r : Row) : ∀ (l : List Nat) (acc : Array Row),
    (r ∈ acc.toList ∨ ∃ o ∈ l, ∃ x, S.oracles[o]? = some x ∧ r ∈ x.sampleRows.toList) →
    r ∈ (l.foldl (fun a o => a ++ ((S.oracles[o]?).map (·.sampleRows)).getD #[]) acc).toList
  | [], acc, h => by
    rcases h with h | ⟨o, ho, _⟩
    · exact h
    · cases ho
  | o' :: l, acc, h => by
    refine mem_foldl_samples S r l _ ?_
    rcases h with h | ⟨o, ho, x, hx, hr⟩
    · exact .inl (by rw [Array.toList_append]; exact List.mem_append_left _ h)
    · rcases List.mem_cons.1 ho with rfl | ho
      · refine .inl ?_
        rw [Array.toList_append, hx]
        exact List.mem_append_right _ hr
      · exact .inr ⟨o, ho, x, hx, hr⟩

/-- A member's sample row stands among the rows that the proximity test takes in (the library's
runRows: the plain rows; each member's sample rows; the generator rows). -/
theorem sample_mem_runRows (S : Statement) (G : Group) (o : Nat) (x : Oracle)
    (ho : o ∈ G.members.toList) (hx : S.oracles[o]? = some x) (r : Row)
    (hr : r ∈ x.sampleRows.toList) : r ∈ (runRows S G).toList := by
  unfold runRows
  rw [Array.toList_append, Array.toList_append]
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  rw [← Array.foldl_toList]
  exact mem_foldl_samples S r _ _ (.inr ⟨o, ho, x, hx, hr⟩)

/-- A row's value on words does not read its target. -/
theorem value_target (S : Statement) (row : Row) (t : E) (m : Words GE) :
    value rdE S { row with target := t } m = value rdE S row m := rfl

/-- says_sample at the row that the record holds. The program's Send.form makes the left side of
a sample row: its target is the default, 0; what Send.verify lays into the record is { row with
target := y }, y the answer received. Under says_sample's premises: that row says its claim of the
words just if the message that the words hold has the answer y, read. -/
theorem says_sample_t (S : Statement) (o : ℕ) (x : Oracle) (hx : S.oracles[o]? = some x)
    (seed : SampleSeed) (row : Row) (h : Send.form S.codes x.shape o seed 0 = some row) (t : E)
    (h1 : x.shape.answers = 1) (hc : CaseE x.shape ∨ CaseF x.shape)
    (hz : seed.z.length = bitsZ S.codes x.shape) (β : GEˣ) (hβ : (β : GE) = readE seed.beta)
    (hlM : 0 < x.shape.mainRows →
      2 ^ ceilLog2 (pMain S.codes x.shape).ell = (pMain S.codes x.shape).ell)
    (hlZ : 0 < x.shape.maskRows →
      2 ^ ceilLog2 (pMask S.codes x.shape).ell = (pMask S.codes x.shape).ell)
    (m : Words GE) (hP : Padded S m) :
    Says rdE S { row with target := t } m ↔
      (portZ S.codes x.shape).val (readP (bitsZ S.codes x.shape) seed.z, β)
        (fun j => m o (partZ S.codes x.shape j) (locZ S.codes x.shape j)) = fun _ => readE t := by
  unfold Says
  rw [value_target, value_sample S o x hx seed row h h1 hc hz β hβ hlM hlZ m hP]
  constructor
  · intro e
    funext u
    cases u
    exact e
  · intro e
    exact congrFun e ()

/-- hS at the row that the record holds: answers_of_says with { row with target := t } in the
row's place and readE t as the answer. -/
theorem answers_of_says_t {s : Sg} (hs : s.Sized) (e : ℕ) (he : e < s.d) (S : Statement) (G' :
    Group)
    (L : GroupLayout) (F : LayFacts S G' L) (y : s.cIn.Word) (hy : RowsBlank s S L y) (o n : ℕ)
    (x : Oracle) (hx : S.oracles[o]? = some x) (e0 : ℕ)
    (σs : Site s (mbOfShape S.codes x.shape e0)) (oM oZ : ℕ)
    (hpM : ∀ r, σs.pM r = vtx _ (oM + r.val)) (hpZ : ∀ r, σs.pZ r = vtx _ (oZ + r.val))
    (hrM : oM + x.shape.mainRows ≤ 2 ^ (s.h + s.g)) (hrZ : oZ + x.shape.maskRows ≤ 2 ^ s.h)
    (hf : L.find o = some n) (hk : L.kept.getD n false = false)
    (hm : 0 < x.shape.mainRows → L.mainFirst.getD n none = some oM)
    (hz : 0 < x.shape.maskRows → L.maskFirst.getD n none = some oZ)
    (hLk : L.k = s.h + s.g) (hLh : L.h = s.h)
    (seed : SampleSeed) (row : Row) (h : Send.form S.codes x.shape o seed 0 = some row) (t : E)
    (h1 : x.shape.answers = 1) (hc : CaseE x.shape ∨ CaseF x.shape)
    (hzl : seed.z.length = bitsZ S.codes x.shape) (β : GEˣ) (hβ : (β : GE) = readE seed.beta)
    (hlM : 0 < x.shape.mainRows →
      2 ^ ceilLog2 (pMain S.codes x.shape).ell = (pMain S.codes x.shape).ell)
    (hlZ : 0 < x.shape.maskRows →
      2 ^ ceilLog2 (pMask S.codes x.shape).ell = (pMask S.codes x.shape).ell)
    (w : s.cIn.N.Wit) (hn : offCnt (Ex := s.cIn.ext) y (s.cIn.N.enc w.1 w.2) ≤ e)
    (hS : Says rdE S { row with target := t } (H2K.ClaimSays.wordsOf S L (tabOf s w.1))) :
    (portOmZ S.codes x.shape e0).Z.val (readP (bitsZ S.codes x.shape) seed.z, β)
      (fun j => w.1 (σs.atJ j)) = fun _ => readE t := by
  have hP := padded_wordsOf F _ (blank_of_near s hs e he S L y hy w hn)
  have h2 := (says_sample_t S o x hx seed row h t h1 hc hzl β hβ hlM hlZ _ hP).1 hS
  have h3 : (fun j => H2K.ClaimSays.wordsOf S L (tabOf s w.1) o (partZ S.codes x.shape j)
      (locZ S.codes x.shape j)) = fun j => w.1 (σs.atJ j) :=
    funext fun j => words_share S.codes x.shape e0 σs oM oZ hpM hpZ hrM hrZ S L o n x hx rfl hf hk
        hm hz
      hLk hLh w.1 j
  rw [h3] at h2
  exact h2

end H2K.Pin

#print axioms H2K.Pin.sample_mem_runRows
#print axioms H2K.Pin.says_sample_t
#print axioms H2K.Pin.answers_of_says_t
