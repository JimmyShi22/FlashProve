-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/BatValues.lean: the claim that comes out of the batching before a proximity
test is true at a prover's state, at a group of any layout; from the batching's acceptance and four
more hypotheses, two of them on values. The batching is the part `bat` of `guardedProximityTestParts`
(Johnson/Desc/K12/JoinGuarded.lean): it makes one claim of all rows that the test takes in. Where it
accepts, each of these rows says its claim of words m, and the two tables of a prover's state P hold
m on the members' blocks, the claim that the verifier's state passes after the batching is true at
the message of P (`ClaimTrue`, Johnson/Desc/K12/Honest/ClaimTrue.lean). `ClaimTrue` is the
hypothesis on the claim in `stages_accept`
(Johnson/Desc/K12/Honest/WholeStages.lean (not in the library yet)); `first_V`
(Johnson/Desc/K12/Honest/FirstValues.lean) has it unfolded at the claim that is passed. A
definition, a statement and its proof. It depends on no frame for an honest side: no file under
Johnson/Desc/ProofFile/Honest/ is imported.

In the list: a statement (`Statement`, OnBytes/Iop/Ground.lean) holds the codes, the oracle messages
and the groups. A group (`Group`) is a set of oracle messages, its members, that one proximity test
reads together, with its open rows (`Group.rows`). A row (`Row`) says that a linear form of the
messages equals the row's target. A layout (`GroupLayout`) says where each member's rows are among
the rows of the group's tables: the member's block. Words (`Words`, Johnson/Desc/Means/Says.lean)
are a value for each oracle message, table and index. p has the numbers of the test's place (`P12`,
Johnson/Desc/K12/Frame.lean). tF and t are the verifier's state inside the test (`T12`,
Johnson/Desc/K12/Join.lean) before and after the batching. s is a stage (`Sg`,
OnBytes/Slice/Stage.lean), and P is what a prover holds at a stage (`PS`,
Johnson/Prover/Link/BodyState.lean). All of these, and m, are free parameters.

  `bat_claimTrue`: under the five hypotheses below, `ClaimTrue s t P`: for every row and layout L
    that t passes as its claim, the row, read with L.k and L.h (`stmGk`,
    OnBytes/Slice/BlkRead.lean), holds of the message `μOf s P`
  `tabsOf P`: a definition: the two tables of P by index as the library's tables of a group
    (`Tables`, Johnson/Desc/Means/Says.lean): `P.tabM` as `main`, `P.tabZ` as `mask`; the part
    `kept` is 0

By what. `batK_ok` and `batK_comb` (Johnson/Desc/K12/Law/Top.lean) take from the acceptance the
acceptance of `batJ` (Johnson/Desc/K12/Join.lean) and the guards `noKept` and `combOk`
(JoinGuarded.lean). `batJ_ok` (Top.lean) and `bat_ok` (Johnson/Desc/K12/Law/BatOk.lean) give the group,
the layout, the statement after the batching, and the batched row as a value of `Bat.combine`
(OnBytes/Iop/Bat.lean). `combineAt_gives` (Johnson/Desc/Means/TestsLaw.lean) turns `combOk` into
what the next two lemmas ask. `combine_all` (Johnson/Desc/Means/Combine.lean) gives that the batched
row holds of the tables as m fills them (`GroupSays` at `tablesOf`, Says.lean); `combine_means`
(Combine.lean) that it has no coefficient where the tables hold no word (`Clean`, Says.lean). So
`groupValue_laidOn` (Johnson/Desc/Means/Bridge.lean), with `layFacts`
(Johnson/Desc/Means/Layout.lean), carries `GroupSays` over to `tabsOf P`. `noKept_spec` (Top.lean)
gives that the row has no kept form. `groupSays_iff` (Johnson/Desc/K12/Law/ClaimSays.lean) turns
`GroupSays` into: the claim `stmG s row` holds of `msgOf s (tabsOf P)`, which is `μOf s P` by
unfolding. `stmG_eq` (BlkRead.lean) and hnum bring `stmG` to the `stmGk` of `ClaimTrue`.

Hypotheses of `bat_claimTrue`. h: the batching accepts: `(guardedProximityTestParts.bat p cut).decide` at tF, the
rounds rs and no columns returns t. he, `p.early = true`: the masks come early. hnum: the layout
that t passes has the stage's four numbers: L.k = s.h + s.g, L.h = s.h, 2 ^ L.logEll = s.C.l and
2 ^ L.logEllZk = s.Z.l. hs: every row that the test takes in says its claim of m (`AllSay`,
Says.lean), at the statement after the batching, `t.st`. These rows are `runRows`
(OnBytes/Slice/BlkBegin.lean) at the statement before, `tF.st`, and its group number `tF.g`: the
group's open rows of the kinds `plain` and `generator`, and each member's sample rows. hT: the
tables `tabsOf P` hold m on the members' blocks (`LaidOn`, Bridge.lean), at `t.st` and the layout
that t passes.

Limits. The batching's acceptance is a hypothesis. That the rows say their claims of the words is a
hypothesis: for a sample row that is the sender's honest answer; for an open row it has to be shown
for the kind of sub-protocol that put the row on the group. `LaidOn` is a hypothesis. The stage s is
tied to the place p and to the two states by hnum only. Nothing says that a run of a verifier
reaches tF. The guard `noKept` refuses a layout that has a kept member: at such a layout h fails,
and the theorem is vacuous. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.FirstJoins
import Johnson.Desc.K12.Law.Top
import Johnson.Desc.K12.Law.BatOk
import Johnson.Desc.K12.Law.ClaimSays
import Johnson.Desc.Means.Bridge
import Johnson.Desc.Means.TestsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.ClaimSays
open Johnson.Prover.Link (PS μOf)

/-- The two tables of a prover's state as a group's tables (`Tables`); the part `kept` is 0. -/
def tabsOf (P : PS) : Tables GE := ⟨P.tabM, P.tabZ, fun _ _ => 0⟩

/-- **After the batching the claim that is passed is true** at the message of the prover's state P,
under the five hypotheses that the head lists. -/
theorem bat_claimTrue (p : P12) (he : p.early = true) (cut : List Fmt.DeclaredRound) (tF t : T12)
    (rs : List Fmt.RoundView) (h : (guardedProximityTestParts.bat p cut).decide tF rs [] = .ok t) (s : Sg) (P : PS)
    (hnum : ∀ row L, t.pass = .claim row L → L.k = s.h + s.g ∧ L.h = s.h ∧
      2 ^ L.logEll = s.C.l ∧ 2 ^ L.logEllZk = s.Z.l)
    (m : Words GE)
    (hs : ∀ G, tF.st.groups[tF.g]? = some G → AllSay rdE t.st (runRows tF.st G).toList m)
    (hT : ∀ row L, t.pass = .claim row L → LaidOn t.st L m (tabsOf P)) :
    ClaimTrue s t P := by
  intro row L hp
  obtain ⟨hJ, hk, -⟩ := batK_ok p cut tF t rs [] h
  have hc := batK_comb p cut tF t rs [] h
  obtain ⟨e, r, row₁, L₁, S', -, hb, rfl⟩ := batJ_ok p he cut tF t rs [] hJ
  have hp' : Passing.claim row₁ L₁ = .claim row L := hp
  injection hp' with a1 a2
  subst a1 a2
  obtain ⟨G, x, hG, hL, rfl, -, hcomb⟩ := bat_ok tF.st S' tF.g e r row₁ L₁ hb
  have hcA : combineAt (begun tF.st tF.g G) tF.g ⟨L₁, runRows tF.st G⟩ = true := by
    unfold combOk at hc
    rw [hG, hL] at hc
    exact hc
  obtain ⟨G', hG', hL', hOk, hr⟩ := combineAt_gives hcA
  obtain ⟨out, h1, -, hclean, -⟩ :=
    combine_means rdE (begun tF.st tF.g G) tF.g G' L₁ (runRows tF.st G) x hG' hL' hOk hr
  rw [hcomb] at h1
  obtain rfl := Option.some.inj h1
  have hsay := combine_all rdE (begun tF.st tF.g G) tF.g G' L₁ (runRows tF.st G) x row₁ hG' hL' hOk
    hr hcomb m (hs G hG)
  have hsay' : GroupSays rdE (begun tF.st tF.g G) L₁ row₁ (tabsOf P) := by
    unfold GroupSays at hsay ⊢
    rw [groupValue_laidOn rdE (layFacts hG' hL' hOk) hclean (hT row₁ L₁ rfl)]
    exact hsay
  obtain ⟨n1, n2, n3, n4⟩ := hnum row₁ L₁ rfl
  have hkept := (noKept_spec _ row₁ L₁ rfl hk).1
  have hH := (groupSays_iff s _ L₁ row₁ (tabsOf P) n1 n2 n3 n4 hkept).1 hsay'
  have e : stmGk s L₁.k L₁.h row₁ = stmG s row₁ := by rw [stmG_eq, n1, n2]
  rw [e]
  exact hH

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.bat_claimTrue
#print axioms ProofFile.Honest.K12.tabsOf
