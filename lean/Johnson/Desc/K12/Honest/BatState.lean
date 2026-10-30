-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/BatState.lean: `bat_claimTrue` (Johnson/Desc/K12/Honest/BatValues.lean) with
the prover's data as `first_V` (Johnson/Desc/K12/Honest/FirstValues.lean) has them. `bat_claimTrue`
has the hypothesis `LaidOn` (Johnson/Desc/Means/Bridge.lean): the tables of the prover's state hold
the words on the members' blocks. Here that hypothesis is proved, at the words `wordsAt`, by
`laidOn_state` (both in Johnson/Desc/K12/Honest/LaidState.lean) from `StateAt`
(Johnson/Desc/K12/Honest/FirstState.lean), which is a hypothesis of `first_V` too. Of the other
hypotheses of `laidOn_state`, its public hypothesis `MemsAre` (it reads the statement, the layout
and the plain data only) and the library's facts on the layout (`LayFacts`,
Johnson/Desc/Means/Layout.lean) are proved from the batching's own acceptance and the library's
plain data of the group; the four equations on the layout's numbers stay hypotheses. The four
theorems hold at all values of their parameters that meet the hypotheses listed below. Statements
and proofs. The file depends on no frame for an honest side (such as
Johnson/Desc/ProofFile/Honest/Frame.lean).

In the list: the batching is the part `guardedProximityTestParts.bat p cut` (Johnson/Desc/K12/JoinGuarded.lean) of a
proximity test, at a place's numbers p (`P12`, Johnson/Desc/K12/Frame.lean) and declared rounds cut:
all pending claims of the group under test become one. tF and t have the type `T12`
(Johnson/Desc/K12/Join.lean) of the verifier's state inside a proximity test; among its fields are a
statement `st`, the number `g` of the group under test and what is passed to the next part, `pass`.
"The batching accepts" is `(guardedProximityTestParts.bat p cut).decide tF rs [] = .ok t`: at tF, the rounds rs and
an empty list of columns the part's decision returns t. "t passes the claim" is
`t.pass = .claim row L`: a row on the whole group (`GroupRow`) with a layout L (`GroupLayout`; these
two, `Group` and `Statement`: OnBytes/Iop/Ground.lean). The members of a group or of a layout are
the numbers of its oracle messages (the field `members`). A layout gives each member blocks of rows
in the group's tables; a member can be marked as kept (the field `kept`). a is a stage
(`Fmt.M1.Stage`). The plain data Dp (`Plain`) are what `gpOf p t a L` returns (both in
Johnson/Desc/K12/Law/FirstOk.lean). P has the type `PS` (Johnson/Prover/Link/BodyState.lean) of what
a prover holds at a stage, by index; R are plain rows (`PlainRows`,
Johnson/Desc/K12/Honest/FirstRows.lean). Words (`Words`, Johnson/Desc/Means/Says.lean) give a value
for each oracle message, table and index.

  `bat_claimTrue_state`: under the hypotheses below: `ClaimTrue (sgOf a) t P`
    (Johnson/Desc/K12/Honest/ClaimTrue.lean): whatever claim t passes is true at the message of P,
    read with the layout that is passed with it. `sgOf a` (Johnson/Desc/K12/Law/ChainOf.lean) is the
    stage a in the library's form
  `memsAre_of`: where the batching accepts, `p.early = true`, t passes the claim and `gpOf p t a L`
    returns Dp: `MemsAre t.st L Dp`: the layout of Dp is L; the members of Dp are those of L, number
    by number, each with the shape that `t.st` has for it; none is marked as kept
  `bat_facts`: where the batching accepts, `p.early = true` and t passes the claim: `t.st` has a
    group G at the number `tF.g`; `t.st.layout tF.g` is L; the library's `GroupOk t.st G`
    (Johnson/Desc/Means/Says.lean) holds; no member of L is marked as kept
  `entered_keeps`: the entering of the first fold's fresh table keeps the oracle messages' shapes.
    As stated: where `entered p t cu L` (Johnson/Desc/K12/Law/FirstOk.lean) returns (id, st, book),
    `ShapesKeep t.st st` (OnBytes/Slice/BlkSeat.lean) holds: st has each oracle message of `t.st`,
    with its shape

By what. `bat_claimTrue_state` calls `bat_claimTrue`; it gets `LaidOn` from `laidOn_state`,
`LayFacts` from `layFacts` (Johnson/Desc/Means/Layout.lean) at what `bat_facts` gives, and `MemsAre`
from `memsAre_of`. `bat_facts` joins the library's lemmas on what an acceptance of the batching
holds: `batK_ok`, `batK_comb`, `batJ_ok`, `noKept_spec` (Johnson/Desc/K12/Law/Top.lean), `bat_ok`
(Johnson/Desc/K12/Law/BatOk.lean) and `combineAt_gives` (Johnson/Desc/Means/TestsLaw.lean).
`memsAre_of` uses `bat_facts`, `made_of` (Johnson/Desc/K12/Law/FirstOkLaw.lean), `layout_eq`,
`find_some` and `find_of_mem` (Johnson/Desc/Means/Layout.lean), and `entered_keeps`. `entered_keeps`
unfolds `entered` and uses `recvP_keeps` (Johnson/Desc/K12/Law/OutK.lean).

Hypotheses. Of `bat_claimTrue_state`. he: the masks come early (`p.early = true`). h: the batching
accepts. hp: t passes the claim. hD: `gpOf p t a L` returns Dp. hk, hh, hl, hz: the layout's four
numbers are the stage's: `L.k = kk a` (`kk`: Johnson/Desc/K12/Law/FirstOk.lean), `L.h = a.h`,
`2 ^ L.logEll = a.C.l`, `2 ^ L.logEllZk = a.Z.l`. hS: `StateAt a Dp P R`. hs: every row that the
test takes in (`runRows tF.st G`, OnBytes/Slice/BlkBegin.lean, at the group G that `tF.st` has at
the number `tF.g`) says its claim (`AllSay`, Johnson/Desc/Means/Says.lean, at the statement `t.st`)
of the words that the plain rows make (`wordsAt t.st L R`).

Limits. The batching's acceptance is a hypothesis. That the rows say their claims of the words is a
hypothesis. So are `StateAt`, that `gpOf` returns, that t passes a claim, the four equations on the
layout's numbers and `p.early = true`. tF, P and R are free parameters: that a verifier reaches tF,
or that a prover holds P, is not stated. No value is given at which the hypotheses hold together.
Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.LaidState
import Johnson.Desc.K12.Law.OutK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Means Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.ClaimSays H2K.First
open Johnson.Prover.Link (PS)
open H2K.Pub (sgOf)

theorem entered_keeps (p : P12) (t : T12) (cu : IoppStage) (L : GroupLayout) (id : ℕ)
    (st : Statement) (book : TreeBook) (h : entered p t cu L = some (id, st, book)) :
    ShapesKeep t.st st := by
  unfold entered at h
  cases hm : t.mask with
  | some id' =>
    rw [hm] at h
    cases h
    exact ShapesKeep.refl _
  | none =>
    rw [hm] at h
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, _, h⟩ := Option.map_eq_some_iff.1 h
    cases h
    exact (H2K.Out.recvP_keeps (ids := x.1) (d1 := x.2) hx).2.1

/-- What an acceptance of the batching gives of the group and its layout: the statement `t.st` has a
group at the number `tF.g`, its layout there is L, `GroupOk` holds, and no member of L is marked as
kept. -/
theorem bat_facts (p : P12) (he : p.early = true) (cut : List Fmt.DeclaredRound) (tF t : T12)
    (rs : List Fmt.RoundView) (h : (guardedProximityTestParts.bat p cut).decide tF rs [] = .ok t) (row : GroupRow)
    (L : GroupLayout) (hp : t.pass = .claim row L) :
    ∃ G, t.st.groups[tF.g]? = some G ∧ t.st.layout tF.g = some L ∧ GroupOk t.st G ∧
      ∀ i, i < L.members.size → L.kept.getD i false = false := by
  obtain ⟨hJ, hk, -⟩ := batK_ok p cut tF t rs [] h
  have hc := batK_comb p cut tF t rs [] h
  obtain ⟨e, r, row₁, L₁, S', -, hb, rfl⟩ := batJ_ok p he cut tF t rs [] hJ
  have hp' : Passing.claim row₁ L₁ = .claim row L := hp
  injection hp' with a1 a2
  subst a1 a2
  obtain ⟨G, x, hG, hL, rfl, -, -⟩ := bat_ok tF.st S' tF.g e r row₁ L₁ hb
  have hcA : combineAt (begun tF.st tF.g G) tF.g ⟨L₁, runRows tF.st G⟩ = true := by
    unfold combOk at hc
    rw [hG, hL] at hc
    exact hc
  obtain ⟨G', hG', hL', hOk, -⟩ := combineAt_gives hcA
  exact ⟨G', hG', hL', hOk, (noKept_spec _ row₁ L₁ rfl hk).2⟩

/-- **The plain data's members are the layout's.** From an acceptance of the batching and from
`gpOf p t a L = some Dp`. -/
theorem memsAre_of (p : P12) (he : p.early = true) (cut : List Fmt.DeclaredRound) (tF t : T12)
    (rs : List Fmt.RoundView) (h : (guardedProximityTestParts.bat p cut).decide tF rs [] = .ok t) (a : Fmt.M1.Stage)
    (row : GroupRow) (L : GroupLayout) (hp : t.pass = .claim row L) (Dp : Plain)
    (hD : gpOf p t a L = some Dp) : MemsAre t.st L Dp := by
  obtain ⟨G, hG, hL, hOk, hkept⟩ := bat_facts p he cut tF t rs h row L hp
  have hm := made_of p t a L Dp hD
  have hLG : L.members = G.members := by
    rw [layout_eq t.st tF.g G hG] at hL
    rw [← Option.some.inj hL]
    rfl
  have hid : ∀ i : Fin Dp.mems.length, L.members.getD i.val noId = (Dp.mems.get i).id := fun i => by
    rw [Array.getD_eq_getD_getElem?, (hm.mem i).1]
    rfl
  obtain ⟨cu, -, hent⟩ := hm.ent
  have hsk := entered_keeps p t cu L _ _ _ hent
  refine ⟨hm.lay, fun o i hf => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · obtain ⟨h1, h2⟩ := find_some hf
    exact ⟨hm.size ▸ h1, by rw [← hid ⟨i, hm.size ▸ h1⟩]; exact h2⟩
  · have hmem : (Dp.mems.get i).id ∈ L.members.toList := by
      have k := (hm.mem i).1
      exact Array.mem_toList_iff.2 (Array.mem_of_getElem? k)
    obtain ⟨j, hj⟩ := find_of_mem hmem
    obtain ⟨j1, j2⟩ := find_some hj
    have hnd : L.members.toList.Nodup := by rw [hLG]; exact hOk.nodup
    have hi1 : i.val < L.members.size := by rw [hm.size]; exact i.isLt
    have e1 : L.members.toList[j]'(by simpa using j1) =
        L.members.toList[i.val]'(by simpa using hi1) := by
      have a1 : L.members.getD j noId = L.members.getD i.val noId := by rw [j2, hid i]
      simpa [Array.getD_eq_getD_getElem?, j1, hi1] using a1
    have := (List.Nodup.getElem_inj_iff hnd).1 e1
    rw [hj, this]
  · have hmem : (Dp.mems.get i).id ∈ G.members.toList := by
      rw [← hLG]
      exact Array.mem_toList_iff.2 (Array.mem_of_getElem? (hm.mem i).1)
    have hlt := hOk.there _ hmem
    obtain ⟨x', hx', ex'⟩ := hsk _ _ (Array.getElem?_eq_getElem hlt)
    obtain ⟨x'', hx'', ex''⟩ := (hm.mem i).2.oracle
    rw [hx'] at hx''
    obtain rfl := Option.some.inj hx''
    exact ⟨_, Array.getElem?_eq_getElem hlt, ex'.symm.trans ex''⟩
  · exact hkept i.val (by rw [hm.size]; exact i.isLt)

/-- **After the batching the claim that is passed is true: from `StateAt`.** This is `bat_claimTrue`
with its hypothesis `LaidOn` proved by `laidOn_state`. That the rows say their claims of the words
(`hs`) is a hypothesis. -/
theorem bat_claimTrue_state (p : P12) (he : p.early = true) (cut : List Fmt.DeclaredRound) (tF t : T12)
    (rs : List Fmt.RoundView) (h : (guardedProximityTestParts.bat p cut).decide tF rs [] = .ok t) (a : Fmt.M1.Stage)
    (row : GroupRow) (L : GroupLayout) (hp : t.pass = .claim row L) (Dp : Plain)
    (hD : gpOf p t a L = some Dp) (hk : L.k = kk a) (hh : L.h = a.h)
    (hl : 2 ^ L.logEll = a.C.l) (hz : 2 ^ L.logEllZk = a.Z.l) (P : PS) (R : PlainRows)
    (hS : StateAt a Dp P R)
    (hs : ∀ G, tF.st.groups[tF.g]? = some G →
      AllSay rdE t.st (runRows tF.st G).toList (wordsAt t.st L R)) :
    ClaimTrue (sgOf a) t P := by
  obtain ⟨G, hG, hL, hOk, -⟩ := bat_facts p he cut tF t rs h row L hp
  have M := memsAre_of p he cut tF t rs h a row L hp Dp hD
  have hT := laidOn_state (layFacts hG hL hOk) a Dp P R hS M hk hh hl hz
  refine bat_claimTrue p he cut tF t rs h (sgOf a) P (fun row' L' h' => ?_) (wordsAt t.st L R) hs
    fun row' L' h' => ?_
  · rw [hp] at h'
    injection h' with _ e2
    rw [← e2]
    exact ⟨hk, hh, hl, hz⟩
  · rw [hp] at h'
    injection h' with _ e2
    rw [← e2]
    exact hT

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.entered_keeps
#print axioms ProofFile.Honest.K12.bat_facts
#print axioms ProofFile.Honest.K12.memsAre_of
#print axioms ProofFile.Honest.K12.bat_claimTrue_state
