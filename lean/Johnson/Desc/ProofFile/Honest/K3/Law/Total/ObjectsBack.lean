-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Total/ObjectsBack.lean: the kind "lookup" (K3): for the item
"totalB" at the batching. Conditional: at an entry at which a link states the lookup's run
"objects", the run's values are the values of the item's forms, as an equation of lists; so where
the table's item at that entry holds, every coefficient of the run's terms is 0. This is the reverse
of the library's clause `item_objects` (Johnson/P1K9R/ItemObjects.lean), which states the inclusion
alone. Two theorems, general in the lookup's accessors.

Terms. Honest/K3/GLOSSARY.md. In this file: an entry o is a pair of a piece's number and a run's
name. `At L o run` (Johnson/Desc/First/Link/Law/LinkJoinPay.lean) says that the link L states the
run at the entry o. What is fixed at a state s is `fixed9 φ s`
(Johnson/Desc/First/Batch/Law/FitsAtS.lean). The link's reader is
`K9.readersOfLink H L` (Johnson/Desc/First/Batch/ReadersOfLink.lean); H holds its holes
(`K9.LinkHoles`, there), and the second hole is the field silent. The table's item at the entry is
`formsQ` (Johnson/Desc/Sound/FormsQ.lean), its public test `K9.formsIn`. The lookups' promise at
what is fixed is `K3Ok` (Johnson/Top/H/Keep/RunsPlain.lean).

What is shown.
  `objects_values`: `objVals` (RunsPlain.lean) at what is fixed and the witness's data is the list
    of the values of the forms that the link's reader answers at the entry, in the world of the
    witness's own arrays.
  `objects_back`: so, where `formsQ` holds there, every coefficient of the table of terms at the
    entry is 0, the table answering `plainTm (objVals ..)` there (`plainTm`,
    Johnson/Desc/First/Batch/Law/PlainRuns.lean).
The statements are sentences on the verifier's state and the library's terms: no prover, coin or
play is named.

Hypotheses that remain.
  `hn`, `hAt`: the entry's name is not "K8.equations"; the run "objects" at these accessors
    (`objectsRun seat`, Johnson/Top/H/K3RunsLaw.lean) stands at the entry.
  `hA`: the accessors are the state's own (`AtS2`, Johnson/Top/H/Keep/RunsAtS.lean).
  `hφh`: what the lookup has heard is read off the fixed part.
  `hb`: a part is there at s.
  `hk`: `K3Ok` at what is fixed. Whether it holds at a real state is not shown here.
  `hsil`: the readers' second hole says nothing at the entry and the state.
  `hin`, `hq`: the table's public test at the entry holds (in `objects_values`); the table's item
    holds there (in `objects_back`).
  `ht`: (in `objects_back`) the table of terms at the entry is `plainTm` of the run's values.

How the proof goes. It is the library's own proof of `item_objects`, followed to the equation that
it holds on its way: "stands" says of each row heard that its worth is the flat row's residue, and
that there are as many rows.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
Nothing on "planes" or "join".
At the head's segment `hsil` cannot be had at the library's own holes (`K9.holesAt`,
Johnson/Desc/First/Batch/ReadersAt.lean) at a state at which the tables can be made and the run
answers: there the second hole is filled (`k6Silent`, Johnson/Desc/Kinds/Law/K6SilentCode.lean: the
run itself at the state with the tables laid), at every name of a run; where the tables cannot be
made at the state, or the run refuses there, that hole says nothing. There the lemma is meant at the
empty hole (`K9.withSmall K9.LinkHoles.none`, Johnson/Desc/First/Batch/SmallReader.lean: `hsil` by
`rfl`), and what it says is carried over to the library's holes by the library's `forms_of_run`
(Johnson/Desc/First/Link/Law/HitemsHead.lean), where the run's own reader answers at the state. That
carrying over is not made here, and that hypothesis of `forms_of_run` is not shown in this file. At
every other segment the library's second hole says nothing outright. This bears on the head's two
entries "objects". By a count over the table's text, not by Lean: of the
nine entries of "totalB" at which a link states one of the lookup's runs (six "objects", two
"planes", attention's "join") three are the head's (two "objects", one "planes"): so at the
library's own holes the theorems of Honest/K3/Law/Total/ObjectsBack.lean and
Honest/K3/Law/Total/PlanesJoinBack.lean apply at six of the nine. The nine are written out, by the
link's sort, in the statements of `theta_at_layers`, `theta_at_attention` and `theta_at_head`
(Honest/K3/Law/ThetaKept.lean).
The library has other theorems of the short name `objects_back`
(Johnson/Road/K4/Riders/Objects.lean; Johnson/Desc/Kinds/Law/K6RidersAtMgAll.lean). This one is
`ProofFile.Honest.K3.Law.Total.objects_back`.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.P1K9R.ItemObjects
import Johnson.Desc.Sound.FormsQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Total
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.First (S)
open VerifiableInference.OnPublicFiles (AtS2 objectsRun objVals K3Ok pick_some pick_spec objects_cut
        objects_answer lateOf_same)

variable {α : Type}

/-- **The equation of lists at "objects".** Conditional on what this file's head lists, and on the
table's public test at the entry. No instance of these hypotheses is exhibited in this file. -/
theorem objects_values (H : K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (hd : α → Option Forest.Heard) (lm jLK : ℕ) (seat : K3.Seat S Claim) (hA : AtS2 seat)
    (hφh : ∀ s, seat.heard s = hd (φ s)) (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ)
    (o : ℕ × String) (hn : (o.2 == "K8.equations") = false) (hAt : At L o (objectsRun seat))
    (s : S) (b : K9.Part) (hb : atS.get? s = some b)
    (hk : K3Ok hd lm jLK (fixed9 φ s)) (hsil : H.silent o.1 o.2 s = none)
    (hin : K9.formsIn (K9.readersOfLink H L) own o.1 o.2 s = true) :
    ∃ R, (K9.readersOfLink H L).forms o.1 o.2 s = some R ∧
      objVals hd lm jLK (fixed9 φ s) (dataQ own b rd) =
        R.forms.map fun f => f.value Reading.gl (worldOwn b R.late (dataQ own b rd)) := by
  obtain ⟨R, hR⟩ := reader_of_formsIn _ own o.1 o.2 s hin
  obtain ⟨z, G0, G, hz, hG0, hG, -, hRz⟩ := run_of_reader H L o hn _ hAt s hsil R hR
  obtain ⟨F1, g, e1, e2, -⟩ := objects_cut seat (l := z.1) (s' := z.2) hz
  have hz' := objects_answer seat 0 e1 e2
  obtain rfl : z = (g.rows.toList.map seat.claim, seat.mark s (F1.paid g.owedObjects)) :=
    Except.ok.inj (hz.symm.trans hz')
  obtain rfl : G0 = F1 := Option.some.inj (hG0.symm.trans ((hA.fork s).symm.trans e1))
  have hG' : G = G0.paid g.owedObjects := by
    have h1 : (seat.mark s (G0.paid g.owedObjects)).fork? = some (G0.paid g.owedObjects) := by
      rw [hA.mark]
      exact fork_putFork s G0 hG0 _
    exact Option.some.inj (hG.symm.trans h1)
  have hlate : K9.lateOf G0 G = [] := by
    rw [hG']
    exact lateOf_same G0 _ rfl
  have hforms : (g.rows.toList.map seat.claim).map (·.form) = g.rows.toList := by
    rw [List.map_map]
    exact (List.map_congr_left fun x _ => hA.form x).trans (List.map_id _)
  have hRz' : R = { forms := g.rows.toList, late := [] } := by
    rw [hRz, hlate]
    show K9.Read.mk ((g.rows.toList.map seat.claim).map (·.form)) [] = _
    rw [hforms]
  subst hRz'
  have hq2 : (fixed9 φ s).2 = some (pubOf b) := by
    show (atS.get? s).map pubOf = _
    rw [hb]
    rfl
  have hg' : hd (fixed9 φ s).1 = some g := by
    show hd (φ s) = _
    rw [← hφh]
    exact e2
  obtain ⟨rs0, hp⟩ := pick_some hd lm jLK hk hg' hq2
  obtain ⟨-, F0, u', hu', hI, hL⟩ := pick_spec hd lm jLK hp
  obtain rfl : pubOf b = u' := Option.some.inj (hq2.symm.trans hu')
  refine ⟨_, hR, ?_⟩
  unfold objVals
  rw [hp]
  show (Fo.endsOf g.shape lm jLK rs0).rows.map _ = g.rows.toList.map _
  apply List.ext_getElem
  · rw [List.length_map, List.length_map, ← hI.nRows]
    simp
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_map]
    have hlen : i < (Fo.endsOf g.shape lm jLK rs0).rows.length := by simpa using h1
    have hi' : i < g.rows.size := by
      rw [hI.nRows]
      exact hlen
    have hrow := hI.rows i hi' b.F hL (dataQ own b rd).mask
      (worldOwn b [] (dataQ own b rd)).entry
    rw [List.getD_eq_getElem _ _ hlen] at hrow
    rw [← hrow]
    have e3 : g.rows.getD i {} = g.rows.toList[i] := by
      simp [Array.getD, hi']
    rw [e3]
    rfl

/-- **The reverse of the library's clause at "objects"**: where the table's item at the entry holds,
every coefficient of the run's terms is 0. Conditional on what this file's head lists. No instance
of these hypotheses is exhibited in this file. -/
theorem objects_back (H : K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (hd : α → Option Forest.Heard) (lm jLK : ℕ) (seat : K3.Seat S Claim) (hA : AtS2 seat)
    (hφh : ∀ s, seat.heard s = hd (φ s))
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ)
    (o : ℕ × String) (hn : (o.2 == "K8.equations") = false) (hAt : At L o (objectsRun seat))
    (ht : tmOf o = plainTm (objVals hd lm jLK))
    (s : S) (b : K9.Part) (hb : atS.get? s = some b)
    (hk : K3Ok hd lm jLK (fixed9 φ s)) (hsil : H.silent o.1 o.2 s = none)
    (hq : formsQ (K9.readersOfLink H L) own o.1 o.2 s rd) :
    ∀ n, ∀ c ∈ tmOf o n (fixed9 φ s) (dataQ own b rd), c.2 = 0 := by
  rw [ht]
  obtain ⟨R, hR, hv⟩ := objects_values H L φ hd lm jLK seat hA hφh own rd o hn hAt s b hb hk
    hsil (formsQ_in _ own o.1 o.2 s rd hq)
  obtain ⟨a', R', ha', hR', -, hf⟩ := hq
  obtain rfl : a' = b := Option.some.inj (ha'.symm.trans (K9.segAt_of_atS s b hb))
  obtain rfl : R' = R := Option.some.inj (hR'.symm.trans hR)
  intro n c hc
  have h1 : c.2 ∈ (plainTm (objVals hd lm jLK) n (fixed9 φ s) (dataQ own a' rd)).map (·.2) :=
    List.mem_map.2 ⟨c, hc, rfl⟩
  rw [show (plainTm (objVals hd lm jLK) n (fixed9 φ s) (dataQ own a' rd)).map (·.2) =
    objVals hd lm jLK (fixed9 φ s) (dataQ own a' rd) from numbered_snd _ n, hv] at h1
  obtain ⟨f, hfm, e⟩ := List.mem_map.1 h1
  rw [← e]
  exact (hf f hfm).2

end ProofFile.Honest.K3.Law.Total

#print axioms ProofFile.Honest.K3.Law.Total.objects_values
#print axioms ProofFile.Honest.K3.Law.Total.objects_back
