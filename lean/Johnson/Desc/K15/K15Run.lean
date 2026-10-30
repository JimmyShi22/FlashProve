-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K15/K15Run.lean: K15, (L2) «HANDS ON»: THE PROOFS at the link's decision itself (the
statements: Johnson/Desc/K15/K15Says.lean); the silly members.
  HandsOnFold       the statement at the fold over blocks 0 to 5 · handsOnFold: its proof
  (Johnson/Desc/K15/K15Law.lean: k15_ran)
  HandsOnRun        **the statement at (descOf P plan ok).run** (linkDesc c is descOf (p15Of c) ‹the
  plan's entries›): where the decision says yes on
                    a view: LinkRanR between the first carried record and some d5; and from d5 the
                    format's fold over the link's two last
                    blocks (tailOf P: the proximity test; the chain's end) says yes on what is left,
                    with nothing left over: K12's law's
                    premise. ONE PREMISE IS LEFT: samples = 1 (over Block.lean,
                    whose roundsFit asks the positions' range). The tests on the
                    plan pay «the rounds can be said»
                    (entries_of_planOk); the test on the instance pays the two items' numbers.
                    handsOnRun: its proof.
  ran_turns_statement   the sharper tooth: the record holds between no two contexts with one
  statement
  ctxOf_start       the law's first context is the library's startCtx, by rfl
  ran_not_idle · silly_yes   the conclusion bites: it holds between no context and itself; the empty
  list of blocks, whose fold says yes to
                    every view and takes nothing, fails it
  foldBlocks_planOk · foldBlocks_append   general: the fold does not read a block's test on the
  plan; the fold over two lists in a row
  flat_fold         the chain's flat list is, for the fold, the front, the five, the test, the end
WHAT IS STILL BETWEEN THIS AND «SoundAt … decE» (OnBytes/Flat/LinkSib.lean; the named premise of
entrySoundOfFullD, Johnson/Flat/Dec/EntrySound.lean): (a) from LinkRanR to the typed statement
st4R's rows (the library's road behind linkSteps_invR: to be walked with this record in that
theorem's place) · (b) K12's law: the test's yes gives the
chain's Acc at these rows · (c) the reading of the compiled slot's view (skeletonOverBothExternalStrings … dec) as the view of
this file.
(Where this and lean/THEOREM.md differ, the page holds.) Nothing on soundness is claimed here.
-/
import Johnson.Desc.K15.K15Law
import Johnson.Desc.Link.CoreSays
import OnBytes.Slice.BlkTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
variable {S Cl : Type}

/-- The fold reads of a block its name, rounds and decide: not its test on the plan. -/
theorem foldBlocks_planOk (ft : Nat) (f : Block S Cl → Bool) : ∀ (l : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn),
    foldBlocks ft (l.map fun b => { b with planOk := f b }) s rs cols = foldBlocks ft l s rs cols
  | [], _, _, _ => rfl
  | b :: l, s, rs, cols => by
    simp only [List.map_cons]
    unfold foldBlocks
    simp only [List.splitAt_eq]
    have hstep : ∀ m, Block.step ft { b with planOk := f b } s m cols = Block.step ft b s m cols :=
        fun _ => rfl
    rw [hstep]
    split
    · rfl
    · split
      · rfl
      · exact foldBlocks_planOk ft f l _ _ _

/-- The fold over two lists in a row: the first list's fold, then the second's from where it ended.
-/
theorem foldBlocks_append (ft : Nat) (l₂ : List (Block S Cl)) : ∀ (l₁ : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
    foldBlocks ft (l₁ ++ l₂) s rs cols = .ok out →
    ∃ s₁ rs₁ cols₁, foldBlocks ft l₁ s rs cols = .ok (s₁, rs₁, cols₁) ∧
      foldBlocks ft l₂ s₁ rs₁ cols₁ = .ok out
  | [], s, rs, cols, out, h => ⟨s, rs, cols, by unfold foldBlocks; rfl, h⟩
  | b :: l₁, s, rs, cols, out, h => by
    obtain ⟨s', k, hl, hs, h'⟩ := foldBlocks_cons ft b (l₁ ++ l₂) s rs cols out h
    obtain ⟨s₁, rs₁, cols₁, h1, h2⟩ := foldBlocks_append ft l₂ l₁ _ _ _ _ h'
    refine ⟨s₁, rs₁, cols₁, ?_, h2⟩
    unfold foldBlocks
    simp only [List.splitAt_eq, hl, ne_eq, not_true_eq_false, if_false, hs]
    exact h1

end VerifiableInference.Desc

namespace Desc.K15
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (Block foldBlocks OneChainFileDescription OpenedColumn chainAt blocksOk)
open VerifiableInference.Desc.ChainEnd (chainEnd untestedL)

/-- The chain's flat list, but for the blocks' tests on the plan, which the fold does not read. -/
theorem flat_fold (P : P15) (s : St) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    foldBlocks 0 (chainOf P).blocksInOrder s rs cols =
      foldBlocks 0 ((frontBlock P :: blocksOr P) ++ tailOf P) s rs cols := by
  have e : (chainOf P).blocksInOrder = ((frontBlock P :: blocksOr P) ++ tailOf P).map
      fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } := by
    unfold VerifiableInference.Desc.Chain.blocksInOrder chainOf tailOf
    simp
  rw [e, VerifiableInference.Desc.foldBlocks_planOk]

/-- Where the tests on the plan pass, the five rounds in front of the test can be said. -/
theorem entries_of_planOk (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool)
    (h : (descOf P plan ok).planOk = true) :
    ∃ es5, entries P = some es5 := by
  cases he : entries P with
  | some es5 => exact ⟨es5, rfl⟩
  | none =>
    exfalso
    have hb := OneChainFileDescription.planOk_blocks _ h
    have hbad : blocksOr P =
        [{ VerifiableInference.Desc.roundlessBlock "the kind's rounds cannot be said" 1 none 1 .ok with
            planOk := false }] := by
      unfold blocksOr blocks
      simp [he]
    change blocksOk (chainOf P).blocksInOrder = true at hb
    unfold blocksOk VerifiableInference.Desc.Chain.blocksInOrder chainOf at hb
    rw [hbad] at hb
    simp at hb

/-- Where the tests on the plan pass, the link's front's own has passed: the public shape's
conditions hold AT THE PLAN's CODES. -/
theorem front_ok (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool)
    (h : (descOf P plan ok).planOk = true) :
    P.codes.lengthsOk = true ∧ linkOk P.codes P.S P.set.samples = true := by
  have hb := OneChainFileDescription.planOk_blocks _ h
  change blocksOk (chainOf P).blocksInOrder = true at hb
  unfold blocksOk at hb
  rw [List.all_eq_true] at hb
  have hm : ({ frontBlock P with planOk := (frontBlock P).planOk && (frontBlock P).hasNoClaimsAndNothingAfter } : Block St
      Unit) ∈
      (chainOf P).blocksInOrder := by
    unfold VerifiableInference.Desc.Chain.blocksInOrder chainOf
    simp
  have := hb _ hm
  simp only [Bool.and_eq_true] at this
  have h1 : (frontBlock P).planOk = true := this.1.1
  change (P.codes.lengthsOk && linkOk P.codes P.S P.set.samples) = true at h1
  simpa using h1

theorem handsOnFold : HandsOnFold :=
  fun P es5 es d d' rs rest cols cols' hs he hi0 hi1 kok h =>
    k15_ran P hs es5 he es d d' rs rest cols cols' hi0 hi1 kok h

theorem handsOnRun : HandsOnRun := by
  intro P plan ok es x v hs h
  unfold OneChainFileDescription.run OneChainFileDescription.runEnd at h
  simp only [bind, Except.bind, pure, Except.pure, VerifiableInference.Desc.need] at h
  cases hw : (descOf P plan ok).planWord with
  | some w => simp [hw, Except.isOk, Except.toBool] at h
  | none =>
    have hplan : (descOf P plan ok).planOk = true := by
      unfold OneChainFileDescription.planWord at hw
      by_contra hn
      simp [hn] at hw
    obtain ⟨es5, he⟩ := entries_of_planOk P plan ok hplan
    rw [hw] at h
    simp only at h
    by_cases hx : (descOf P plan ok).okStart x = true
    · simp only [hx, if_true] at h
      by_cases hv : VerifiableInference.Desc.viewWordsBelowPrime v = true
      · simp only [hv, if_true] at h
        cases hch : chainAt "the chain" 0 (descOf P plan ok).chain.blocksInOrder ((descOf P plan ok).start x)
            v with
        | error e => rw [hch] at h; simp [Except.isOk, Except.toBool] at h
        | ok dEnd =>
          clear h
          change chainAt "the chain" 0 (chainOf P).blocksInOrder (first P.codes x) v = .ok dEnd at hch
          unfold chainAt at hch
          split at hch
          · cases hch
          · rw [flat_fold] at hch
            split at hch
            · rename_i s' hfold
              injection hch with hch
              subst hch
              obtain ⟨d5, rest, cols', h1, h2⟩ :=
                VerifiableInference.Desc.foldBlocks_append 0 (tailOf P) _ _ _ _ _ hfold
              change (okKey 0 x.1 && okKey 1 x.2) = true at hx
              unfold okKey at hx
              simp only [Bool.and_eq_true, beq_iff_eq] at hx
              obtain ⟨X, D, hR, hgq, hmq⟩ := k15_ran P hs es5 he es (first P.codes x) d5 v.rounds
                  rest v.opened cols'
                hx.1.2 hx.2.2 (by
                  have := (front_ok P plan ok hplan).2; rw [hs] at this; exact this) h1
              exact ⟨X, D, d5, rest, cols', s', hR, hgq, hmq, h2, hx.1.2, hx.2.2, hv, hplan⟩
            · cases hch
            · cases hch
      · simp [hv, Except.isOk, Except.toBool] at h
    · simp [hx, Except.isOk, Except.toBool] at h

theorem handsOnLink : HandsOnLink :=
  fun c plan es x v hs h => handsOnRun (p15Of c) plan _ es x v hs h

/-- **plans_are_the_priced_plan, at the entry file**: where the tests on the plan of the link's
description pass: the entries of its declared rounds, block
by block in a row, ARE the rounds' entries of the finished plan whose prices its own public test has
tested; that test (entryOk, Johnson/Desc/MadeOk.lean) has
said yes; and the shape, the codes and the plan's entries that a reader of an entry file is handed
are the made ones. BY TESTS, not by a law on the planner. -/
theorem plans_priced (c : Model.Verify.Chains) (plan : List Fmt.DeclaredRound)
    (h : (linkDesc c plan).planOk = true) :
    (linkDesc c plan).roundsDeclaredByBlocks.map (·.entry) = c.made.entry.plan.rounds ∧
        VerifiableInference.Desc.entryOk c.made = true ∧
      c.link.given.plan.entries = c.made.entry.plan.entries ∧ c.link.link = (p15Of c).S ∧
          c.link.codes = (p15Of c).codes := by
  have hf : (VerifiableInference.Desc.entryOk c.made && tiesOk c plan) = true :=
      OneChainFileDescription.planOk_fileOk _ h
  have hd : ((linkDesc c plan).asFile.roundsDeclaredByBlocks.1 == (linkDesc c plan).asFile.plans.1) = true :=
      OneChainFileDescription.planOk_decl _ h
  have hd' : (linkDesc c plan).roundsDeclaredByBlocks = plan := by simpa using hd
  unfold tiesOk at hf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
  exact ⟨by rw [hd']; exact hf.2.1.1.1, hf.1, hf.2.1.1.2, hf.2.1.2, hf.2.2⟩

/-- **The conclusion bites**: the record of facts holds between no context and itself: it says that
five rounds were taken. So a
list of blocks that says yes and takes nothing (the silly member «yes to all») does not meet the
law's conclusion. -/
theorem ran_not_idle (S : LinkShape) (a b : TableKey) (c : Ctx) (X : LinkRun) (D : LinkDataR) :
    ¬ LinkRanR S a b c c X D := by
  intro h
  have h1 := h.pending
  rw [h.left] at h1
  have := congrArg List.length h1
  simp only [List.length_cons] at this
  omega

/-- **The sharper tooth**: the record of facts holds between no two contexts with one statement:
behind the five rounds the statement has a
group more. So a list of blocks that takes its five rounds, says yes and LAYS NOTHING does not meet
the conclusion either. -/
theorem ran_turns_statement (S : LinkShape) (a b : TableKey) (c c' : Ctx) (X : LinkRun)
    (D : LinkDataR)
    (h : LinkRanR S a b c c' X D) : c'.st ≠ c.st := by
  intro he
  have hg := linkSt_groupR S c.st D.places { D.row0 with target := D.y0 }
      { D.row1 with target := D.y1 } D.rec0 D.rec1
    D.rows0 D.rows1 D.rE
  rw [← h.st, he] at hg
  have hn : c.st.groups[c.st.groups.size]? = none := Array.getElem?_eq_none (Nat.le_refl _)
  rw [hn] at hg
  cases hg

/-- The first carried record with a view's rounds and columns IS the library's own first context at
that view: so
the library's lemmas that are stated at `startCtx` take the law's record as it stands. -/
theorem ctxOf_start (es : List Fmt.Entry) (K : Codes) (x : TableKey × TableKey) (v : Fmt.View) :
    ctxOf es (first K x) v.rounds v.opened =
      OnBytes.Slice.startCtx ⟨es, 1, 0, { codes := K, oracles := #[], groups := #[] },
          { trees := #[], place := #[] }⟩ v := rfl

/-- The like at the fold: at the empty list of blocks, whose fold says yes to every view and takes
nothing, the law's statement
fails wherever its premises can be met at all. -/
theorem silly_yes (P : P15) (es : List Fmt.Entry) (d : St) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    foldBlocks (Cl := Unit) 0 [] d rs cols = .ok (d, rs, cols) ∧
      ¬ ∃ X D, LinkRanR P.S d.loc.key0 d.loc.key1 (ctxOf es d rs cols) (ctxOf (es.drop 5) d rs cols)
          X D := by
  refine ⟨by unfold foldBlocks; rfl, ?_⟩
  rintro ⟨X, D, h⟩
  have h1 := h.pending
  have h2 := h.left
  change rs = _ at h1
  change rs = _ at h2
  rw [h2] at h1
  have := congrArg List.length h1
  simp only [List.length_cons] at this
  omega

end Desc.K15

#print axioms Desc.K15.ran_not_idle
#print axioms Desc.K15.silly_yes
#print axioms Desc.K15.ran_turns_statement
#print axioms Desc.K15.ctxOf_start
#print axioms Desc.K15.handsOnFold
#print axioms Desc.K15.handsOnRun
#print axioms Desc.K15.handsOnLink
#print axioms Desc.K15.plans_priced
#print axioms VerifiableInference.Desc.foldBlocks_planOk
#print axioms VerifiableInference.Desc.foldBlocks_append
