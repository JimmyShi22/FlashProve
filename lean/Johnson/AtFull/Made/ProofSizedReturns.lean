-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ProofSizedReturns.lean: THE PLANNER's SIZING OF A PROOF FILE
(`Params.proofSized`, OnBytes/Params/DeriveReq.lean) RETURNS AT THE WRITTEN LINES OF THE FULL SIZE,
AND RETURNS THE WRITTEN SIZES (`proofSizedFull`, Johnson/Desc/Ok/PlanWritten/SizedLit.lean). A
forward law at all lines; then a joining of closed equations that lie. A law file; no running text
imports it. Nothing on codes as such: codes enter as written lists of sizes.

Why. The library's laws on these sizes say "where the sizing returns, its value is …". That it
returns was shown nowhere (the Limits of Johnson/Goal/Written/MadeOfSized.lean). The solver's steps
at these very arguments stand as closed equations in Johnson/Desc/K12/Law/Sizes/: here they are laid
end to end. The way is that of Johnson/Goal/PlanValues/KeySizedReturns.lean for a key file.

  `maskRowsIn`, `lastGroupIn`, `proofOfParts`: three terms of `proofSized`'s text, named.
  `proofSized_of`: **the forward law, at all lines and sub-proofs**: two tests that do not refuse ·
    the links' group solved · the last test's stages solved · the table derived · the stages
    numbered · the test on the table sized ⊢ proofSized l sub = some (proofOfParts …).
  `count_full`, `finish_yes`, `prFinish`, `prLin_returns`, `whole_yes`: the closed parts that did
    not lie yet. Called: `link_solved`, `L_stages`, `U_stages`, `O_stages`, `W_stages`, `prTurns`,
    `linkShape_full`, `linkLoad_full`, `lastK_at`, `maskRows_full`, `split_full` (that folder) ·
    `record_table`, `record_admitted` (OnBytes/Params/EntryStagesRecord.lean) · `linSized_of`
    (OnBytes/Params/Fit/KeySizedForward.lean) · `sameLin_eq`, `sameProof_eq`
    (Johnson/Desc/Ok/PlanWritten/SizedTestLaws.lean).
  `proofSized_returns`: fillLinks sub.links = linksFull · sub.openRows = 25 times 1 ·
    sub.pendingRows = 13 · sub.matrixRows = 3076096 ⊢ proofSized recordLines sub = some
    proofSizedFull. OF sub NOTHING ELSE IS READ: not its routine `plan`.
  `yes_bends`: the two tests with code say no at a bent value each.

Limits. THE FOUR PREMISES ARE PREMISES: that a public part's sub-proofs have these four is not shown
here. `linksFull` is made of 25 declared links and 99 typed group lines of the layout file: that the
file's reader returns these lines is shown nowhere here; and THE NUMBER 25 MUST COME FROM
`declareLinks`' RETURN: the law that has it (`last_of_public`,
Johnson/Desc/K12/Law/Sizes/LastAtScope.lean) takes it out of a yes of `shapesWith`, which for a run
forward is a circle. The premise on the pending rows is stronger than the sizing needs: it reads
them through the number of mask rows alone, which is 1 at 12 pending rows too (`maskRows_twelve`):
SO THE PENDING ROWS CANNOT BE READ BACK FROM `proofSizedFull`. `whole_yes` holds the test on the
table and the codes against themselves: only with `finish_yes` are all six fields paid.
`proofSizedFull` was printed by the library's own planner: here it is, for the first time, what the
sizing returns at written arguments; at no files. The tests that `Params.sized` asks of the finished
shapes behind this sizing are not here: Johnson/AtFull/Made/SizedReturns.lean. The full size alone.
Nothing on soundness.

-/
import Johnson.Desc.K12.Law.Sizes.LastAtScope
import Johnson.Desc.Ok.PlanWritten.SizedTestLaws
import OnBytes.Params.Fit.KeySizedForward

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params H2K.Sizes H2K.Member VerifiableInference.PlanWritten

/-! ## 1 The sizing of a proof file, forward: at all lines -/

/-- The mask rows of the request's mask message, at so many rows on the table: `proofSized`'s term.
-/
def maskRowsIn (l : Lines) (pending : Nat) : Nat :=
  Send.maskRowsFor (pending + (if 1 < pending then Batt.masksOf l.blockLog else 0))
    (2 ^ l.own.maskLogL) l.answers

/-- The group of the last test: `proofSized`'s term. links: as filled. -/
def lastGroupIn (l : Lines) (links : List ReqLink) (link : Solved) : GroupSize :=
  { link.group with k := lastKIn l links, slots := 1,
                    main := { link.group.main with overE := true } }

/-- What `proofSized` puts together of its parts: its last step's term. links: as filled. -/
def proofOfParts (l : Lines) (links : List ReqLink) (link : Solved) (stages : List StageSize)
    (last : List IoppStage) (batch : LinSized) (codes2 : Codes) : ProofSized :=
  { set := settingOf l, codes := codes2, link := link,
    last := ⟨lastGroupIn l links link, link.t, stages⟩,
    request :=
      { code := 0, maskCode := 0, link := links,
        atStart := [{ batch.input with
          leafClass := links.foldl
            (fun c x => x.messages.foldl (fun c m => max c (m.leafClass + 1)) c) 0 }],
        answers := l.answers, last := last, choice := ⟨true⟩ },
    batch := batch }

set_option maxRecDepth 100000 in
/-- **The sizing of a proof file, forward**: where no test refuses and each part returns a given
value, the whole returns the value that is put together of them. -/
theorem proofSized_of {l : Lines} {sub : Subproofs} {link : Solved} {stages : List StageSize}
    {T : TableSize} {last : List IoppStage} {codes1 codes2 : Codes} {batch : LinSized}
    (g1 : (sub.openRows.length != (fillLinks sub.links).length) = false)
    (hl : solveGroup (settingOf l) .request
      (linkLoadIn l (fillLinks sub.links) sub.openRows) id
      (linkShapeIn l (fillLinks sub.links) sub.openRows) = some link)
    (hs : solveStages (settingOf l) .request (lastGroupIn l (fillLinks sub.links) link) link.t
      l.link.stages = some stages)
    (hT : deriveTable (settingOf l) l = some T)
    (hio : ioppStages stages {} = (last, codes1))
    (g2 : (maskRowsIn l sub.pendingRows == 0) = false)
    (hb : linSized (settingOf l) (linLines l sub.matrixRows (maskRowsIn l sub.pendingRows) false) T
      codes1 = some (batch, codes2)) :
    proofSized l sub =
      some (proofOfParts l (fillLinks sub.links) link stages last batch codes2) := by
  unfold proofSized
  extract_lets
  refine (opt_pass (not_true_of g1)).trans ?_
  refine (opt_step hl).trans ?_
  refine (opt_step hs).trans ?_
  refine (opt_step hT).trans ?_
  beta_reduce
  rw [hio]
  refine (opt_pass (not_true_of g2)).trans ?_
  refine (opt_step hb).trans ?_
  rfl

/-! ## 2 The parts at the written lines and the typed links -/

/-- The last test's stages as the format numbers them, and the codes behind them. -/
def lastW : List IoppStage := (ioppStages szLFull {}).1

def codesL : Codes := (ioppStages szLFull {}).2

set_option maxRecDepth 1000000 in
/-- As many open rows as links. -/
theorem count_full : ((List.replicate 25 1).length != linksFull.length) = false := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- What `linSized`'s closing text makes of the solved groups and stages is the written value: as a
test with code. -/
theorem finish_yes :
    ((linFinish recordSet prLin recordTable codesL prX2 prY2 prZ2 szUFull szOFull szWFull).any
      fun p => sameLin p.1 proofSizedFull.batch && decide (p.2 = proofSizedFull.codes)) = true := by
  decide +kernel

theorem prFinish :
    linFinish recordSet prLin recordTable codesL prX2 prY2 prZ2 szUFull szOFull szWFull =
      some (proofSizedFull.batch, proofSizedFull.codes) := by
  have h := finish_yes
  cases e : linFinish recordSet prLin recordTable codesL prX2 prY2 prZ2 szUFull szOFull szWFull with
  | none =>
    rw [e] at h
    cases h
  | some p =>
    rw [e] at h
    obtain ⟨a, c⟩ := p
    have h' : (sameLin a proofSizedFull.batch && decide (c = proofSizedFull.codes)) = true := h
    rw [Bool.and_eq_true] at h'
    rw [sameLin_eq h'.1, of_decide_eq_true h'.2]

/-- **The sizing of the test on the table returns**, behind the last test's codes. -/
theorem prLin_returns :
    linSized recordSet prLin recordTable codesL =
      some (proofSizedFull.batch, proofSizedFull.codes) := by
  have hU : solveStages recordSet (linScopeShared prLin) prX2.group prX2.t prLin.folded.stages
      = some szUFull := U_stages
  have hO : (if linSplit prLin then
        solveStages recordSet (linScopeShared prLin) prY2.group prY2.t prLin.omega.stages
         
      else pure []) = some szOFull := by
    rw [if_pos split_full]
    exact O_stages
  have hW : solveStages recordSet (linScopeOwn prLin) prZ2.group prZ2.t prLin.own.stages
      = some szWFull := W_stages
  exact (linSized_of (X := prX2) (Y := prY2) (Z := prZ2) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) record_admitted (by decide +kernel)
    (by decide +kernel) prTurns (by decide +kernel) hU hO hW).trans prFinish

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- The parts, put together, are the written sizes: as a test with code. -/
theorem whole_yes :
    sameProof (proofOfParts recordLines linksFull ⟨gLink, 219⟩ szLFull lastW proofSizedFull.batch
      proofSizedFull.codes) proofSizedFull = true := by
  decide +kernel

/-- The sizing reads the pending rows through this number alone: it is 1 at 12 pending rows too. -/
theorem maskRows_twelve : maskRowsIn recordLines 12 = 1 := by decide +kernel

/-! ## 3 The whole -/

/-- **`proofSized` RETURNS THE WRITTEN SIZES** at the written lines, wherever the four things that
it reads of the sub-proofs are the full size's. -/
theorem proofSized_returns {sub : Subproofs} (h1 : fillLinks sub.links = linksFull)
    (h2 : sub.openRows = List.replicate 25 1) (h3 : sub.pendingRows = 13)
    (h4 : sub.matrixRows = 3076096) : proofSized recordLines sub = some proofSizedFull := by
  have hr : maskRowsIn recordLines sub.pendingRows = 1 := by
    rw [h3]
    exact maskRows_full
  have e := proofSized_of (l := recordLines) (sub := sub) (link := ⟨gLink, 219⟩)
    (stages := szLFull) (T := recordTable) (last := lastW) (codes1 := codesL)
    (codes2 := proofSizedFull.codes) (batch := proofSizedFull.batch)
    (by rw [h1, h2]; exact count_full)
    (by rw [h1, h2, linkShape_full, linkLoad_full]; exact link_solved)
    (by
      rw [h1]
      unfold lastGroupIn
      rw [lastK_at]
      exact L_stages)
    record_table rfl (by rw [hr]; rfl)
    (by rw [hr, h4]; exact prLin_returns)
  rw [e, h1]
  exact congrArg some (sameProof_eq whole_yes)

/-! ## 4 The two tests with code can say no -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- With one row more in the committed matrix the closing text's value is not the written one (as
typed, this half would hold of a refusal too); and with one position more at the links' group the
whole is not. -/
theorem yes_bends :
    ((linFinish recordSet (linLines recordLines 3076097 1 false) recordTable codesL prX2 prY2 prZ2
      szUFull szOFull szWFull).any
      fun p => sameLin p.1 proofSizedFull.batch && decide (p.2 = proofSizedFull.codes)) = false ∧
    sameProof (proofOfParts recordLines linksFull ⟨gLink, 220⟩ szLFull lastW proofSizedFull.batch
      proofSizedFull.codes) proofSizedFull = false := by
  decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.proofSized_of
#print axioms Johnson.AtFull.Made.count_full
#print axioms Johnson.AtFull.Made.finish_yes
#print axioms Johnson.AtFull.Made.prFinish
#print axioms Johnson.AtFull.Made.prLin_returns
#print axioms Johnson.AtFull.Made.whole_yes
#print axioms Johnson.AtFull.Made.maskRows_twelve
#print axioms Johnson.AtFull.Made.proofSized_returns
#print axioms Johnson.AtFull.Made.yes_bends
