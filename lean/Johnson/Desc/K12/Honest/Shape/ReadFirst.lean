-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/ReadFirst.lean: at the first code switch of a proximity test, the
reading of the old rows accepts the groups of opened columns that the stages' term gives to that
switch. A code switch reads the symbols of the rows that the fold before it has returned (the old
rows, `SingleRows`) out of opened columns: `Tw.L9.readOld`, Johnson/Top/H0/Tw/L9/Switch.lean. The
stages' term is `stagesAll` (Johnson/Desc/K12/Honest/Stages.lean); its groups for a switch are
`aGroups`, here at the list of trees `groupTrees` (Johnson/Desc/K12/Honest/GroupState.lean). The
result is for the field `read` of `SwitchFront` (Johnson/Prover/Link/FormSwitch.lean), the structure
of hypotheses from which a switch's acceptance is proved (`switch5_yes`,
Johnson/Prover/Link/FormSwitchLaws.lean). It is derived from one test on the shape of the state
after the first fold (`readPubB`, ReadShape.lean in this folder) and from the library's plain data
of the group under test (`Plain`, Johnson/Desc/K12/Law/FirstOk.lean). The group's layout, the number
of trees that hold its oracle messages and the words in the columns are free, within the hypotheses
below. Three theorems with their proofs; no definition.

In the list: p holds the numbers of the place at which the test is (`P12`,
Johnson/Desc/K12/Frame.lean), and a is a stage (`Fmt.M1.Stage`), read as the place's stage number 0.
t and t₁ are the states before and after the first fold (`T12`, Johnson/Desc/K12/Join.lean); among a
state's fields are a statement, a book, a count of roots, and what passes to the next part. A book
(`TreeBook`, OnBytes/Iop/Ground.lean) lists the trees sent so far and, for each oracle message, its
place: its tree and its part of that tree. The shape of a state is `coreSh`
(Johnson/Desc/Ground/Shape/Core.lean) at its statement, book and count of roots. Dp is the plain
data, which `gpOf` makes from p, t, a and the group's layout L (`GroupLayout`). `Dp.ts` lists the
trees of the layout's members and of `Dp.fresh` by their indices in `Dp.book.trees`, each once,
rising. c u x is the column of tree u at position x. D n is what round number n sampled
(`Fmt.Drawn`). The sampled positions are those of D at o + 2 + (h + g), with h and g of `sgOf a`:
the switch's second round in the term (`aSwitch`, Stages.lean). dS and dC are the switch's two
declared rounds. A sending is a choice of the next stage n, the flag last, the second round rC, a
group number and a structure Dk (`Taken`, Johnson/Desc/K12/Law/SwDid.lean: what a switch has taken
from its two rounds and made on its way). `swIn` (FormSwitch.lean) is the reading's input at a
sending; it has the statement and the book after the switch has sent its new oracle messages, the
opened columns with their keys, and the old rows.

  `read_first_any`: under the hypotheses below, t₁ passes single rows with a group number, and at
    every sending whose round rC has the sampled positions, the reading at `swIn`, at these
    positions in the range 2 ^ `a.C.a`, accepts. It returns the book of `swIn` with one list more
    counted at each tree of `Dp.ts` (`bump`, Johnson/Desc/K12/Honest/ReadTrees.lean), no column left
    over, and some array of symbols y
  `read_first`: the same at one sending: at the group number that t₁ passes, at a Dk with
    `Dk.code.logN = a.C.a`, and at the positions `swPos rC Dk` (FormSwitch.lean). There are a book B
    and symbols y such that the reading returns (B, [], y). The field `read` has `Dk.y` where this
    statement has y. It is this statement at Dk with y put into that field, since `swIn` reads
    neither the field y of Dk nor what depends on it. That step is stated in Lean in TestSwitch.lean
    in this folder (`switchFacts_any`), not here
  `treesAt_plain`: where `Made p t a L Dp` holds (Johnson/Desc/K12/Law/FirstOkLaw.lean: what `gpOf`
    has made) and `places` are the places in `Dp.book` of the layout's members and then of
    `Dp.fresh.id`: the trees to be opened, `treesAt places`
    (Johnson/Desc/K12/Honest/ReadWhole.lean), are `Dp.ts`

By what. In `read_first_any`, `fold_exact` (Johnson/Desc/K12/Honest/FirstSeenExact.lean) writes out
the book of t₁ and the single rows that it passes; `length_aFold`
(Johnson/Desc/K12/Honest/Causal.lean) counts the fold's rounds for it. `made_of` and
`entered_of_case` (FirstOkLaw.lean) show that this book is `Dp.book`. `readPub_sh` (ReadShape.lean)
turns the "true" of `readPubB` into `ReadPub`, and `treesAt_plain` says which trees it speaks of.
`first_at`, whose two hypotheses on the trees' depths come from `keyAt_of` (both FirstOkLaw.lean),
and `OpensAre.keys` (Johnson/Desc/K12/Law/FirstSrc.lean) give the keys of the declared openings;
with them `readView_term` (Johnson/Desc/K12/Honest/ReadViewTerm.lean) gives `ReadView` at the term's
columns. The rest is in Johnson/Desc/K12/Honest/: `readAsks_of_halves` (ReadPub.lean) joins the two
into `ReadAsks` at the input before the sending (`frontIn`, ReadSwIn.lean), `readAsks_behind`
(ReadBehind.lean) carries `ReadAsks` over to `swIn`, and `read_yes_trees` (ReadWhole.lean)
concludes. `read_first` is `read_first_any` at one sending, with `swPos` unfolded. `treesAt_plain`
calls `array_mapM_inv` (OnBytes/Slice/BlkOpenN.lean) and `listOfT_eq` (OnBytes/Chain/Draws.lean).

Hypotheses of `read_first_any`. hp: t passes a claim: a batched row with the layout L. hD:
`gpOf p t a L` returns Dp. hok: every clause of the library's test on the plain data (`gpL`,
FirstOk.lean) passes at Dp. hhk: `a.h ≤ a.k`. hcu: `stageAt p 0 a` returns a stage cu. hw: at each
tree u of `Dp.ts` and each position x below 2 ^ `logAt Dp.book u`, the column c u x has
`widthAt Dp.book u` words. hf1: the first fold (`guardedProximityTestParts.fold p 0 a`,
Johnson/Desc/K12/JoinGuarded.lean), at the first 1 + `a.k` declared rounds of `laidS p`
(Johnson/Desc/K12/Law/ReadsK.lean), accepts from t the term's own rounds of the fold
(`rfAt K 0 a o t P D`, Johnson/Desc/K12/Honest/FirstYes.lean) without their digests, with no column,
and returns t₁. hr: every sampled position is below 2 ^ `a.C.a`. hcut: dS and dC are the next two
declared rounds of `laidS p`. hpub: `readPubB` is true at the shape of t₁, the shape of whatever
single rows t₁ passes (`singleSh`, Test.lean in this folder) and the range `a.C.a`. `read_first` has
two more. hlog: `Dk.code.logN = a.C.a`. hposs: rC has the sampled positions.

Limits. The first fold's acceptance (hf1) and the "true" of `readPubB` (hpub) are hypotheses. The
other fields of `SwitchFront` are not treated. `read_first` is called by nothing. The state t is a
free parameter: nothing says that a run reaches it. Nothing here shows that the hypotheses can be
met together. In the name `fold_exact`, "exact" means "as a term of the rounds": equations of
values, no statement on distributions. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.ReadShape
import Johnson.Desc.K12.Honest.ReadViewTerm
import Johnson.Desc.K12.Honest.ReadSwIn
import Johnson.Desc.K12.Honest.FirstReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.K12

/-- The trees to be opened, `treesAt places`, are the plain data's list `Dp.ts`. -/
theorem treesAt_plain (p : P12) (t : T12) (a : Fmt.M1.Stage) (L : GroupLayout) (Dp : Plain)
    (hm : Made p t a L Dp) (places : Array (ℕ × ℕ))
    (hpl : ((L.members.push Dp.fresh.id).mapM fun o => Dp.book.place[o]?) = some places) :
    treesAt places = Dp.ts := by
  obtain ⟨z1, z2⟩ := array_mapM_inv _ _ _ hpl
  have hsz : places.size = Dp.mems.length + 1 := by rw [z1, Array.size_push, hm.size]
  have hlist : (places.map (·.1)).toList = Dp.mems.map (·.t) ++ [Dp.fresh.t] := by
    refine List.ext_getElem (by simp [hsz]) fun i h1 h2 => ?_
    have hi : i < places.size := by simpa using h1
    have hi' : i < (L.members.push Dp.fresh.id).size := by rw [← z1]; exact hi
    have e := z2 i hi'
    rw [Array.getElem?_eq_getElem hi] at e
    have e0 : (places.map (·.1)).toList[i] = (places[i]).1 := by simp
    rw [e0]
    by_cases c : i < Dp.mems.length
    · have hiL : i < L.members.size := by rw [hm.size]; exact c
      rw [Array.getElem_push_lt hiL] at e
      have k := (hm.mem ⟨i, c⟩).1
      rw [Array.getElem?_eq_getElem hiL] at k
      rw [Option.some.inj k, (hm.mem ⟨i, c⟩).2.place] at e
      rw [← Option.some.inj e, List.getElem_append_left (by simpa using c)]
      simp
    · have ei : i = L.members.size := by rw [hm.size]; omega
      subst ei
      rw [Array.getElem_push_eq, hm.fresh.place] at e
      rw [← Option.some.inj e, List.getElem_append_right (by simp [hm.size])]
      simp [hm.size]
  unfold treesAt
  rw [hlist, listOfT_eq, hm.ts]

/-- **The first switch's reading accepts the term's own columns**, at every sending of the
switch. The first fold's acceptance (hf1) and the "true" of `readPubB` (hpub) are hypotheses. -/
theorem read_first_any (p : P12) (K : BCoins) (a : Fmt.M1.Stage) (o : ℕ) (t : T12) (P : PS)
    (D : ℕ → Fmt.Drawn) (row : GroupRow) (L : GroupLayout) (hp : t.pass = .claim row L)
    (Dp : Plain) (hD : gpOf p t a L = some Dp) (hok : ok (gpL p a row Dp) = true)
    (hhk : a.h ≤ a.k) (cu : IoppStage) (hcu : stageAt p 0 a = some cu)
    (c : ℕ → ℕ → List UInt64)
    (hw : ∀ u ∈ Dp.ts, ∀ x, x < 2 ^ logAt Dp.book u → (c u x).length = widthAt Dp.book u)
    (t₁ : T12)
    (hf1 : (guardedProximityTestParts.fold p 0 a (((laidS p).take (1 + a.k)).map (·.1))).decide t
      ((rfAt K 0 a o t P D).map noDigest) [] = .ok t₁)
    (hr : ∀ x ∈ (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss, x < 2 ^ a.C.a)
    (dS dC : Fmt.DeclaredRound) (hcut : (((laidS p).drop (1 + a.k)).take 2).map (·.1) = [dS, dC])
    (hpub : ∀ rows gp, t₁.pass = .single rows gp →
      readPubB (coreSh ⟨t₁.st, t₁.book, t₁.roots⟩) (singleSh rows) a.C.a = true) :
    ∃ rows gp, t₁.pass = .single rows gp ∧
      ∀ (n : IoppStage) (last : Bool) (rC : Fmt.RoundView) (gp' : ℕ) (Dk : Taken),
        rC.drawn.poss = (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss →
        ∃ y, Tw.L9.readOld (swIn p n last dS dC t₁ rC
            (aGroups a o (groupTrees Dp.ts (logAt Dp.book) c) D) rows gp' Dk)
            (Positions.ofDraws a.C.a rC.drawn.poss) =
          .ok (bump (swIn p n last dS dC t₁ rC
            (aGroups a o (groupTrees Dp.ts (logAt Dp.book) c) D) rows gp' Dk).book Dp.ts, [],
            y) := by
  have hm := made_of p t a L Dp hD
  have hkk : (sg a).h + (sg a).g = a.k := by
    show a.h + (a.k - a.h) = a.k
    omega
  have hck : cu.k = a.k ∧ cu.h = a.h := by
    unfold stageAt at hcu
    obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.1 hcu
    exact ⟨rfl, rfl⟩
  have hn : ((rfAt K 0 a o t P D).map noDigest).length = 1 + cu.k := by
    rw [List.length_map, length_aFold, hck.1]
    exact congrArg (1 + ·) hkk
  obtain ⟨id, st, book, n', hcase, -, -, hbk, hpass, -⟩ :=
    fold_exact p 0 a _ t t₁ _ row L cu hp hcu hn hf1
  obtain ⟨cu', hcu', hent⟩ := hm.ent
  obtain rfl : cu' = cu := Option.some.inj (hcu'.symm.trans hcu)
  have e := (entered_of_case p t cu' L id st book hcase).symm.trans hent
  obtain ⟨rfl, e'⟩ := Prod.mk.inj (Option.some.inj e)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
  obtain ⟨rows, gp, hpass, hids⟩ : ∃ rows gp, t₁.pass = .single rows gp ∧
      singleRowsOracles rows = L.members.push Dp.fresh.id := ⟨_, _, hpass, rfl⟩
  obtain ⟨places, Pb⟩ := readPub_sh (hpub rows gp hpass)
  rw [hbk] at Pb
  have hts : treesAt places = Dp.ts :=
    treesAt_plain p t a L Dp hm places (by rw [← hids]; exact Pb.placed)
  -- the keys of the declared openings
  have hlogM : ∀ i : Fin Dp.mems.length,
      logAt Dp.book (Dp.mems.get i).t = (Dp.mems.get i).tsh.logN :=
    fun i => (keyAt_of (F := 0) (hm.mem i).2).2
  have hlogF : logAt Dp.book Dp.fresh.t = Dp.fresh.tsh.logN := (keyAt_of (F := 0) hm.fresh).2
  obtain ⟨-, ⟨src, hsrc⟩, -, -, -⟩ := first_at p t a row L Dp hD hok hhk (fun _ => 0)
    (fun i => dBook Dp.book (Dp.mems.get i).t) (dBook Dp.book Dp.fresh.t)
    (fun i => congrArg (2 ^ ·) (hlogM i)) (congrArg (2 ^ ·) hlogF)
  have hkeys := hsrc.keys
  rw [hkk, show (((H2U.roundsOfNums p.nums).getD []).zip p.oracles).drop 1 = laidS p from rfl,
    show cutS (laidS p) a.k = [dS, dC] from hcut] at hkeys
  have hV := readView_term p [dS, dC] places a.C.a
    (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss (DataAt hok).key (logAt Dp.book) c
    (treeOf Dp.book) (by rw [hts]; exact hkeys) hr fun u hu => by
      obtain ⟨T, hT⟩ : ∃ T, Dp.book.trees[u]? = some T := ⟨_, (Pb.tree u hu).there⟩
      have eT : treeOf Dp.book u = T := by
        unfold treeOf
        rw [hT]
        rfl
      rw [eT]
      refine ⟨by unfold logAt; rw [hT]; rfl, ?_, fun x hx => ?_⟩
      · show _ = keyAt p.nums.firstTree Dp.book u
        unfold keyAt
        rw [hT]
        rfl
      · rw [hw u (hts ▸ hu) x hx]
        unfold widthAt
        rw [hT]
        rfl
  rw [hts] at hV
  have hA : ReadAsks
      (frontIn p dS dC t₁ (aGroups a o (groupTrees Dp.ts (logAt Dp.book) c) D) rows)
      (Positions.ofDraws a.C.a (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss) places
      (treeOf Dp.book)
      (dealtOf (DataAt hok).key (logAt Dp.book) c
        (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss) := by
    refine readAsks_of_halves _ _ places _ _ ?_ hV
    show ReadPub t₁.st t₁.book rows a.C.a places _
    rw [hbk]
    exact Pb
  refine ⟨rows, gp, hpass, fun n last rC gp' Dk hposs => ?_⟩
  have h := read_yes_trees _ _ places _ _
    (readAsks_behind (i' := swIn p n last dS dC t₁ rC
      (aGroups a o (groupTrees Dp.ts (logAt Dp.book) c) D) rows gp' Dk) hA Dk (swTarget p n)
      (othersOf last n) (sentOf (swTarget p n) (othersOf last n)) p.nums.firstTree t₁.roots rfl rfl
      rfl rfl rfl)
  rw [hts] at h
  rw [hposs]
  exact h

/-- The same at one sending with `Dk.code.logN = a.C.a`: the equation of the field `read` of
`SwitchFront`, with "there are B and y" where the field has the parameter B and `Dk.y`. -/
theorem read_first (p : P12) (K : BCoins) (a : Fmt.M1.Stage) (o : ℕ) (t : T12) (P : PS)
    (D : ℕ → Fmt.Drawn) (row : GroupRow) (L : GroupLayout) (hp : t.pass = .claim row L)
    (Dp : Plain) (hD : gpOf p t a L = some Dp) (hok : ok (gpL p a row Dp) = true)
    (hhk : a.h ≤ a.k) (cu : IoppStage) (hcu : stageAt p 0 a = some cu)
    (c : ℕ → ℕ → List UInt64)
    (hw : ∀ u ∈ Dp.ts, ∀ x, x < 2 ^ logAt Dp.book u → (c u x).length = widthAt Dp.book u)
    (t₁ : T12)
    (hf1 : (guardedProximityTestParts.fold p 0 a (((laidS p).take (1 + a.k)).map (·.1))).decide t
      ((rfAt K 0 a o t P D).map noDigest) [] = .ok t₁)
    (hr : ∀ x ∈ (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss, x < 2 ^ a.C.a)
    (dS dC : Fmt.DeclaredRound) (hcut : (((laidS p).drop (1 + a.k)).take 2).map (·.1) = [dS, dC])
    (hpub : ∀ rows gp, t₁.pass = .single rows gp →
      readPubB (coreSh ⟨t₁.st, t₁.book, t₁.roots⟩) (singleSh rows) a.C.a = true)
    (n : IoppStage) (last : Bool) (rC : Fmt.RoundView) (Dk : Taken) (hlog : Dk.code.logN = a.C.a)
    (hposs : rC.drawn.poss = (D (o + 2 + ((sgOf a).h + (sgOf a).g))).poss) :
    ∃ rows gp B y, t₁.pass = .single rows gp ∧
      Tw.L9.readOld (swIn p n last dS dC t₁ rC
        (aGroups a o (groupTrees Dp.ts (logAt Dp.book) c) D) rows gp Dk) (swPos rC Dk) =
        .ok (B, [], y) := by
  obtain ⟨rows, gp, hpass, h⟩ := read_first_any p K a o t P D row L hp Dp hD hok hhk cu hcu c hw t₁
    hf1 hr dS dC hcut hpub
  obtain ⟨y, hy⟩ := h n last rC gp Dk hposs
  exact ⟨rows, gp, _, y, hpass, by
    unfold swPos
    rw [hlog]
    exact hy⟩

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.treesAt_plain
#print axioms ProofFile.Honest.Sh.read_first_any
#print axioms ProofFile.Honest.Sh.read_first
