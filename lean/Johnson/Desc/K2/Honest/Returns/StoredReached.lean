-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/StoredReached.lean: THE CLAUSES OF THE LAW "THE KIND's OWN DECISION
SAYS YES" ON THE KEPT MEMBERS' STORED SAMPLE ROWS. WHEREVER EACH STORED SAMPLE ROW IS A ROW OF THE
PROGRAM's OWN MAKER (`SampleGood`, Johnson/Top/H0/K2Hears/SampleGood.lean), IT HAS NO RUN, NO FORM,
AND NO WRITTEN-OUT VARIABLE IN ANY TERM: BY CONSTRUCTION, AT ANY SIZE. SO `OldFits.stored` HOLDS
THERE, AND, IN THE GOALS' SCOPE, AT EVERY STATE REACHED IN FRONT OF THE SWITCH INTO A LATER GROUP;
AND `FrontCore.reads` FOLLOWS FROM `FrontCore.check`. Statements with their proofs: calls.

WHY IT MATTERS. One of the three clauses that compare field elements with (1, 1)
(`TablesFit.stored`, through `Own.InOrder`) makes that comparison at a tensor's written-out
variables. `stored_bare` shows that a stored sample row has none: THERE THE COMPARISON RANGES OVER
NOTHING.

  `stored_is_form` a stored sample row is a row of `Send.form` with another target
  `stored_bare` no run · no form · no written-out variable in any term: no premise on shapes
  `oldFits_stored` `OldFits.stored`, in its own letters
  `keptOld_bare` where the test on the target says yes, a kept old message has no mask row
  `reads_stored` `FrontCore.reads`, in its own letters, from the test on the target
  `link_good_reached` at a state reached in front of the switch into group m + 1, m < 23, the
                    front's statement has `SampleGood`
  `link_stored_reached` `OldFits.stored` at the front of a state reached in front of the switch into
                    group m + 1, m < 23: ONE CLAUSE MORE OF THE 67 (Returns/LinkReached.lean), WITH
                    NO PREMISE MORE
  `link_reads_reached` `FrontCore.reads` there, from `FrontCore.check`

By, all the library's: `form_parts` (OnBytes/Slice/BlkSend.lean) · `plainRow_form`
(OnBytes/Slice/BlkPlain.lean) · `form_plain` (Johnson/Top/H0/K2Hands/FormOnReads.lean) ·
`targetOk_eq` (Johnson/Top/H0/Tw/K2/TargetAgree.lean) · `targetOk_means` (Tw/K2/TargetMeans.lean) ·
`SampleGoodS.good` (Johnson/Top/H/SwitchSeedFits.lean) · `sw_link` (Johnson/P1K2R/HstReached.lean).
Near relatives, not called: `stored_of_goodS` (Top/H/SwitchSeedFits.lean): `stored_is_form` at one
typed kept place and one answer, with more in its end · `check_more`
(Johnson/Top/H0/K2Hands/Pays.lean) and `check_kept` (Johnson/Top/H/SwitchFront.lean):
`keptOld_bare` by index, among further clauses · `both_at_front`
(Johnson/Top/H0/Tw/K2C/DebtsState.lean): the stronger `SampleGoodS` at the library's own front,
where `link_good_reached` speaks of this folder's `frontAt`. The library's `readsMain`
(K2Hands/RowsOrder.lean) and `readsMainOf` (Tw/K2/RowsCan.lean) have one body under two names.

Limits. `TablesFit.stored` IS NOT SHOWN: beside "no written-out variable" it asks sizes (the pairs'
number is the table's bits, at most 63; the units' places lie in the table): not here.
`FrontCore.check` has no payer at a reached state that is known here. "Reached" is: over the list of
the wrapped sub-protocols. THE FIVE PREMISES IN FRONT ARE SHOWN MET TOGETHER BY NOBODY HERE: NO
MEMBER. This file's imports are heavy. Nothing on any property.



-/
import Johnson.Desc.K2.Honest.Returns.LinkReached
import Johnson.Top.H0.K2Hands.FormOnReads
import Johnson.Top.H0.K2Hears.SampleGood
import Johnson.Top.H.SwitchSeedFits
import Johnson.Top.H0.Tw.K2.TargetMeans
import Johnson.Top.H0.Tw.K2.TargetAgree
import Johnson.Top.H0.Tw.K2.RowsCan
import OnBytes.Slice.BlkPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open OnBytes.Slice (form_parts plainRow_form)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (SampleGood)
open VerifiableInference.Desc.First.K2Hands (form_plain)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open P1K2 (Prep Nums numsAt prepOf sw_link)
open _root_.Tw.K2 (readsMainOf targetOk_eq targetOk_means)
open ProofFile (Cl)

theorem stored_is_form {St : Statement} (h : SampleGood St) {o : Nat} {x : OnBytes.Oracle}
    (hx : St.oracles[o]? = some x) {r : OnBytes.Row} (hr : r ∈ x.sampleRows.toList) :
    ∃ (seed : SampleSeed) (row : OnBytes.Row) (y : OnBytes.E) (i : Nat),
      Send.form St.codes x.shape o seed i = some row ∧ r = { row with target := y } := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have hi' : i < x.sampleRows.size := by simpa using hi
  obtain ⟨seeds, hsz, hall⟩ := h o x hx (by omega)
  obtain ⟨seed, row, y, -, hf, hrow⟩ := hall i (by omega)
  refine ⟨seed, row, y, i, hf, ?_⟩
  rw [Array.getElem?_eq_getElem hi'] at hrow
  simpa using Option.some.inj hrow

/-- **No run, no form, no written-out variable**: by construction. -/
theorem stored_bare {St : Statement} (h : SampleGood St) (o : Nat) :
    ∀ r ∈ (St.oracles.getD o default).sampleRows.toList,
      r.runs.size = 0 ∧ r.forms.size = 0 ∧ ∀ t ∈ r.terms.toList, t.v.denseVars = [] := by
  intro r hr
  cases hx : St.oracles[o]? with
  | none =>
    have e : St.oracles.getD o default = default := by
      rw [Array.getD_eq_getD_getElem?, hx]
      rfl
    rw [e] at hr
    exact absurd hr List.not_mem_nil
  | some x =>
    have e : St.oracles.getD o default = x := by
      rw [Array.getD_eq_getD_getElem?, hx]
      rfl
    rw [e] at hr
    obtain ⟨seed, row, y, i, hf, rfl⟩ := stored_is_form h hx hr
    obtain ⟨-, h1, h2⟩ := form_parts _ _ _ _ _ _ hf
    refine ⟨?_, ?_, (plainRow_form _ _ _ _ _ _ hf).1⟩
    · show row.runs.size = 0
      rw [h1]
      rfl
    · show row.forms.size = 0
      rw [h2]
      rfl

theorem oldFits_stored {St : Statement} (h : SampleGood St) (old : SingleRows) :
    ∀ o ∈ (switchKept old).toList, ∀ r ∈ (St.oracles.getD o default).sampleRows.toList,
      r.runs.size = 0 ∧ r.forms.size = 0 :=
  fun o _ r hr => ⟨(stored_bare h o r hr).1, (stored_bare h o r hr).2.1⟩

/-- Where the test on the target says yes, a kept old message has no mask row. -/
theorem keptOld_bare {St : Statement} {old : SingleRows} {T : SwitchTarget}
    (hc : switchTargetCheck St old T = true) :
    ∀ o ∈ (switchKept old).toList, (St.oracles.getD o default).shape.maskRows = 0 := by
  have TF := (targetOk_means St old T).1 (by rw [targetOk_eq]; exact hc)
  intro o ho
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem ho
  have ha' : a < (switchKept old).size := by simpa using ha
  have hk : a < T.kept.size := by
    rw [TF.keptCount]
    exact ha'
  have hmem : ((switchKept old)[a], T.kept[a]) ∈ (switchKept old).zip T.kept :=
    Array.mem_iff_getElem.2 ⟨a, by simp only [Array.size_zip]; omega, by simp⟩
  simpa using (TF.keptShapes _ hmem).oldBare

theorem reads_stored {St : Statement} (h : SampleGood St) {old : SingleRows} {T : SwitchTarget}
    (hc : switchTargetCheck St old T = true) :
    ∀ o ∈ (switchKept old).toList, ∀ r ∈ (St.oracles.getD o default).sampleRows.toList,
      readsMainOf o r = true := by
  intro o ho r hr
  have hb := keptOld_bare hc o ho
  cases hx : St.oracles[o]? with
  | none =>
    have e : St.oracles.getD o default = default := by
      rw [Array.getD_eq_getD_getElem?, hx]
      rfl
    rw [e] at hr
    exact absurd hr List.not_mem_nil
  | some x =>
    have e : St.oracles.getD o default = x := by
      rw [Array.getD_eq_getD_getElem?, hx]
      rfl
    rw [e] at hr hb
    obtain ⟨seed, row, y, i, hf, rfl⟩ := stored_is_form h hx hr
    exact (form_plain hf).2.2 hb

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- At a reached state the front's statement has the state's messages and codes: so its stored
sample rows are the maker's too. -/
theorem link_good_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (L : Params.ReqLink) (Q : ReqGroup) : SampleGood (frontAt s L Q).st :=
  fun o x hx hs => (sw_link hS hR O hF hpl h23 hP hn hr).1.good.good o x hx hs

/-- **`OldFits.stored` at a reached state.** -/
theorem link_stored_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (L : Params.ReqLink) (Q : ReqGroup) :
    ∀ o ∈ (switchKept (frontAt s L Q).f.rows).toList,
      ∀ r ∈ ((frontAt s L Q).st.oracles.getD o default).sampleRows.toList,
        r.runs.size = 0 ∧ r.forms.size = 0 :=
  oldFits_stored (link_good_reached hS hR O hF hpl h23 hP hn hr L Q) _

/-- **`FrontCore.reads` at a reached state, from `FrontCore.check`.** -/
theorem link_reads_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {m : Nat} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (L : Params.ReqLink) (Q : ReqGroup)
    (check : switchTargetCheck (frontAt s L Q).st (frontAt s L Q).f.rows (frontAt s L Q).T = true) :
    ∀ o ∈ (switchKept (frontAt s L Q).f.rows).toList,
      ∀ r ∈ ((frontAt s L Q).st.oracles.getD o default).sampleRows.toList,
        readsMainOf o r = true :=
  reads_stored (link_good_reached hS hR O hF hpl h23 hP hn hr L Q) check

end

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.stored_is_form
#print axioms VerifiableInference.Desc.K2.Honest.Returns.stored_bare
#print axioms VerifiableInference.Desc.K2.Honest.Returns.oldFits_stored
#print axioms VerifiableInference.Desc.K2.Honest.Returns.keptOld_bare
#print axioms VerifiableInference.Desc.K2.Honest.Returns.reads_stored
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_good_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_stored_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_reads_reached
