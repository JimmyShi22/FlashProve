-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/CoreText.lean: the text of a proximity test from the first
switch on, at given rows, and the same text at rows 0 with one item laid anew: under a written
change of the coins' letters the two show the same rounds, and the same columns at the positions
that the next reading round samples. Equations between texts, at letters on all numbers: no finite
type of coins, no law. Three definitions, and theorems. The main theorems hold at all numbers of a
place p (`P12`), at every list of two or more stages s :: next :: rest, and at all values of the
other parameters that meet the hypotheses below. `core_upTo` (Sim/CoreLaw.lean) calls `rest_view`,
`atStage_first` and `zeroTextK_congr`.

In this head: a text is a Lean term with a value in `BOut` (Johnson/Prover/Link/BodyAll.lean): the
rounds, `rs`; for each round the written column of the tree that it sends, `tr` (no word where it
sends none); groups of columns, `gs`. The text from the first switch on is `restText`
(Sim/Text.lean). The same text at rows 0 with one item laid anew is `zeroTextK` (Sim/Sims.lean):
`restText` at rows 0, with the last round but one, which is the last stage's first, replaced by a
round whose only item is `tauSim`. Rows are a prover's state at a stage (`PS`,
Johnson/Prover/Link/BodyState.lean). The given rows are P₀. At rows 0 every entry of the state is 0
(`zeroPS`, Sim/Sims.lean, which is `zPS`, Johnson/LinkSim/AtText/ShiftDefs.lean). The coins' letters
are a value of `BCoins` (BodyAll.lean): variables indexed by natural numbers, below called coin
variables; its field `W` holds the folds' coefficients. Kr is their value on the left side of the
equations. The written change is `shB` (ShiftDefs.lean), added entry by entry by `addB`
(Johnson/LinkSim/AtText/Defs.lean). A law is a distribution. A stage (`Fmt.M1.Stage`) that is not
the last has its fold's 1 + (h + g) rounds, with h and g from the stage's sizes (`sgOf`), and then
its switch's two rounds, the first of which sends a tree; the last stage has two rounds. A reading
round is a round whose challenge samples positions: a switch's second round, or the last stage's
second. D gives the challenges by the round's number; the first fold's first round has the number 1.
tB is a free parameter of type `T12` (Johnson/Desc/K12/Join.lean), the type of the verifier's state
inside a test. t₁ is `aRec1` (Johnson/Desc/K12/Honest/Stages.lean) at tB over the first fold's
rounds at P₀ and Kr: the state that the description's fold returns, or tB where it rejects. colR and
colF, "the column in front", are free parameters in the place of the written column of the tree that
holds the first stage's rows, on the left and on the right side. A tree's width is the length of its
column at position 0. The part in the limits is the second part of a test's prover (`restPart`,
Johnson/Desc/ProofFile/Honest/K12/Parts.lean): every switch, every later fold and the last stage.

  `rest_view`: what is shown from the first switch on, at the rows P₀, is what is shown of the text
    at rows 0 with the one item laid anew, at the letters more by the written change: where the
    positions asked of a tree are among those at which it is opened. In Lean, what is shown is
    `shownFrom` (Sim/Sims.lean), at every dep, n and asks that meet hasks
  `rest_rounds`: the rounds from the first switch on, at the rows P₀, are those of the text at rows
    0 with the one item laid anew, at the letters more by the written change
  `rest_trees`: the trees from the first switch on: one width; one column at each position at which
    they are opened
  `body_trees`: along the stages the two runs' trees have one width, and one column at each position
    at which they are opened. The two runs are `bodyAll` (BodyAll.lean) from any stage on, under
    `FitsBody` and `AtStage`
  `openedTr D rest cur o i`: a definition: the positions at which the tree that round number i of
    `bodyAll`'s rounds sends is opened: those that the next reading round samples, in the tree's
    range, each once; none where the round sends no tree
  `openedTr_zero`, `tr_cons`: `openedTr` at round number 0 is the empty list; the tree that round
    number i of `bodyAll`'s rounds sends, stage by stage
  `shownFrom_congr`: what is shown of two outputs is one, where the rounds are one, the trees have
    one width, and the columns are one at the positions asked
  `col_congr`: for two tables (`Table`, in the frame, Johnson/Desc/ProofFile/Honest/Frame.lean) made
    of written columns col and col' as `sendingOf` (Sim/Sims.lean) makes them: where `col 0` and
    `col' 0` have the same length and `col q = col' q`, the tables' columns at q are equal
  `virtK K Kr tB P₀ D`: a definition: the coin variables K, with the first fold's coefficients
    replaced by those of Kr plus `foldShift` (Johnson/LinkSim/AtText/Fold.lean) at the row of tB and
    the messages of P₀
  `virtK_same`, `zeroTextK_congr`: `virtK K Kr tB P₀ D` agrees with K from fold number 1 on
    (`SameFrom 1`, Sim/Text.lean); `zeroTextK` is the same at two values of the coin variables that
    agree so
  `atStage_first`, `add_zPS`: under hcol, `AtStage` (Johnson/LinkSim/AtText/SpecStage.lean) holds
    before the first stage, between the run at P₀ and Kr and the run at rows 0 and Kr plus `shB`,
    with the first fold's coefficients as in `virtK`; every state P is `addPS zPS P`
  `rounds_aux`, `trees_aux`: the rounds and the trees, for any coin variables Ks such that `AtStage`
    holds before the first stage between the run at P₀ and Kr and the run at rows 0 and Ks
  `toEnd`: a definition: the fields j, cur, o, t and P of a `BEnd`
    (Johnson/Prover/Link/BodyEnd.lean) as an `EndAt` (Sim/Text.lean)
  `fitAll_of_fits`: `FitsBody` (Johnson/LinkSim/AtText/SpecShift.lean) gives `FitAll` (Stages.lean)
  `stagesEnd_eq`, `body_cut`, `end_cut`: under `FitAll`, at one tree of the stage's depth:
    `stagesEnd` (Sim/Text.lean) is `toEnd` of `bodyEnd` (BodyEnd.lean); `bodyAll` from the first
    fold on is the first fold's rounds, and then `restText`; `restEnd` (Sim/Text.lean) is `toEnd` of
    `bodyEnd`
  `tauSim_eq`: `tauSim` (Sim/Sims.lean) at `toEnd e` is `tauStar` (Johnson/LinkSim/AtText/Defs.lean)
    at e
  `length_body`: `bodyAll` shows two rounds more than lie in front of the last stage
  `cut_set`, `getD_cut`: lemmas on lists: where A and A' have the same length, at most n, the
    equation A ++ C = (A' ++ C').set n v gives A = A' and C = C'.set (n - A'.length) v; where A has
    the length n, (A ++ C).getD (n + i) d = C.getD i d

By what. The shift of the coin variables, the induction along the stages and the step at the last
stage are those of Johnson/LinkSim/AtText/: `shB` (ShiftDefs.lean), `AtStage` (SpecStage.lean),
`bodyShiftOr`, whose proof calls the step at the last stage (`lastOut_same_or`, LastStepOr.lean),
`atStage_next`, `atSwitch_of` and `bodyEnd_o` (Induct.lean), `sCol_same`, `sT3_same` and `sRF_same`
(Step.lean). They are called, not proved anew. That induction starts before a fold and has the
hypothesis that the fold's coefficients differ by a written shift (`AtStage.foldW`). Here the first
fold's rounds are not among what is compared, and the text behind them reads none of its
coefficients (`restText_congr`, Sim/Text.lean): so the run at rows 0 is laid, for the call alone,
just the first coefficients that the premise asks (`virtK`). The terms of Sim/Text.lean are tied to
`bodyAll` and `bodyEnd` by `stages_eq`, `rec3_eq`, `col_eq`, `next_eq` and `fold_eq` (Stages.lean)
and by `stagesAll_cut` (Sim/Text.lean). Lengths come from `length_sRF`
(Johnson/Prover/Link/BodyCausal.lean) and `length_sCol` (Johnson/Prover/Link/LinkWidths.lean).

Hypotheses of `rest_view`. `rest_rounds` has the first three, `rest_trees` the first two. hF:
`FitsBody D (next :: rest) s 1`: at every stage, the reading round that opens the tree holding the
stage's rows samples, counted with repeats, no more positions than the tails of the stage's two
codes are long (`C.r`, `Z.r`); at every stage but the last, h + 2 g + 1 ≤ `Z.l` and the stage fits
the next (`CsFit`); at the last stage h = 0 and g = 0. hcol: colR and colF are equal at the
positions at which the first stage's tree is opened (`openedAt`, SpecStage.lean). hcl: at the last
stage of `bodyAll` at P₀, Kr and colR, the element that the stage's first round samples is 0
(`LamZero`, Johnson/LinkSim/AtText/SpecShiftIn.lean), or the claim that is left is true at the
prover's last message (`ClaimTrue`, Johnson/LinkSim/AtText/Defs.lean). hasks: for every i, each
position that asks lists for the first root of round number i, counted from the first switch on, is
in `openedTr` at that round.

Limits.
- Only one tree before the first switch, of the first stage's depth: the list of trees that
  `restText` takes is `[((sgOf s).C.a, colR)]`, and `[((sgOf s).C.a, colF)]` on the right side.
- The state behind the first fold is the one that the description's fold leaves from a letter tB
  over the text's own first fold's rounds, not any state.
- Columns: at the positions that the part's own next reading round samples, in the tree's range; at
  no other position.
- The claim that is left at the last stage of the text at the rows P₀ has to be true, or the last
  sampled element 0: the hypothesis hcl. No theorem here proves it. That element is the one that the
  last stage's first round samples; the stage's second round samples positions after it. `LamZero`
  reads it by `headD (0, 0, 0)`: it holds too where that round's challenge has no element. hcl is
  on the rows P₀ and on the coin variables Kr.
- The right sides are not free of the rows P₀: t₁ is made over the first fold's rounds at P₀ and Kr,
  and `shB` is computed from P₀, Kr, tB and colR.
- No hypothesis says that colR or colF is the column of a tree that holds the rows P₀.
- No theorem here ties `restText` to `restPart`.
- No property is claimed: t₁'s maker tB and the column in front are letters: no sentence on a
  simulator.
- Nothing on completeness, on soundness, or on any law.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.Sims
import Johnson.LinkSim.AtText.Induct
import Johnson.Prover.Link.LinkWidths
import Johnson.Prover.Link.BodyCausal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open OnBytes.LinkSim.AtText (zPS addPS addB shB AtStage FitsBody openedAt qNext oNext tNext dNext
  LamZero tauStar claimEnd bodyShiftOr atStage_next atSwitch_of sCol_same bodyEnd_o foldShift)

/-! ## 1 The ties to `bodyAll` and `bodyEnd` -/

/-- The values at the last stage as an `EndAt` (Sim/Text.lean), taken from the structure `BEnd`
(Johnson/Prover/Link/BodyEnd.lean): its fields j, cur, o, t and P. Its fields l and col are
dropped. -/
def toEnd (e : BEnd) : EndAt := ⟨e.j, e.cur, e.o, e.t, e.P⟩

theorem fitAll_of_fits {D : ℕ → Fmt.Drawn} : ∀ (rest : List Fmt.M1.Stage) (cur : Fmt.M1.Stage)
    (o : ℕ), FitsBody D rest cur o → FitAll cur rest
  | [], _, _, _ => trivial
  | _ :: rest, _, _, h => ⟨h.2.2.2.1, fitAll_of_fits rest _ _ h.2.2.2.2⟩

/-- Where each stage fits the next (`FitAll`) and one tree of the stage's depth holds the rows, the
values at the last stage (`stagesEnd`, Sim/Text.lean) are those of `bodyEnd`. -/
theorem stagesEnd_eq (p : P12) (K : BCoins) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (col : ℕ → List UInt64)
    (D : ℕ → Fmt.Drawn), FitAll cur rest →
    stagesEnd p K rest j cur l o t P [((sgOf cur).C.a, col)] D =
      toEnd (bodyEnd p K D rest j cur l o t P col)
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | next :: rest, j, cur, l, o, t, P, col, D, hf => by
    unfold stagesEnd bodyEnd
    simp only
    rw [stagesEnd_eq p K rest (j + 1) next _ _ _ _ _ D hf.2,
      ← rec3_eq p K rest.isEmpty j cur next l o t P col (rowOf t) D hf.1,
      ← col_eq K rest.isEmpty j cur next o P (rowOf t) D,
      ← next_eq K rest.isEmpty j cur next o P (rowOf t) D]

/-- `bodyAll` from the first fold on is the first fold's rounds, and then `restText`, at the state
that `aRec1` returns over these rounds. Hypothesis: each stage fits the next (`FitAll`). -/
theorem body_cut (p : P12) (K : BCoins) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (l : Laid) (tB : T12) (P : PS) (col : ℕ → List UInt64) (D : ℕ → Fmt.Drawn)
    (hf : FitAll s (next :: rest)) :
    bodyAll p K (next :: rest) 0 s l 1 tB P col D =
      ⟨aFold K 0 s 1 P (rowOf tB) D ++
          (restText p K s next rest l 1 (aRec1 p 0 s l tB (aFold K 0 s 1 P (rowOf tB) D)) P
            [((sgOf s).C.a, col)] D).rs,
        (aFold K 0 s 1 P (rowOf tB) D).map (fun _ _ => []) ++
          (restText p K s next rest l 1 (aRec1 p 0 s l tB (aFold K 0 s 1 P (rowOf tB) D)) P
            [((sgOf s).C.a, col)] D).tr,
        (restText p K s next rest l 1 (aRec1 p 0 s l tB (aFold K 0 s 1 P (rowOf tB) D)) P
          [((sgOf s).C.a, col)] D).gs⟩ := by
  rw [← stages_eq p K (next :: rest) 0 s l 1 tB P col D hf]
  exact stagesAll_cut p K s next rest l 1 tB P [((sgOf s).C.a, col)] D

theorem end_cut (p : P12) (K : BCoins) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (l : Laid) (tB : T12) (P : PS) (col : ℕ → List UInt64) (D : ℕ → Fmt.Drawn)
    (hf : FitAll s (next :: rest)) :
    restEnd p K s next rest l 1 (aRec1 p 0 s l tB (aFold K 0 s 1 P (rowOf tB) D)) P
        [((sgOf s).C.a, col)] D =
      toEnd (bodyEnd p K D (next :: rest) 0 s l 1 tB P col) := by
  rw [← stagesEnd_eq p K (next :: rest) 0 s l 1 tB P col D hf]
  rfl

/-- The element that replaces the one item (`tauSim`, Sim/Sims.lean), at `toEnd e`, is `tauStar`
(Johnson/LinkSim/AtText/Defs.lean) at e. -/
theorem tauSim_eq (p : P12) (e : BEnd) (D : ℕ → Fmt.Drawn) :
    tauSim p (toEnd e) D = tauStar p e D := by
  unfold tauSim tauStar tauSW claimAtEnd claimEnd toEnd
  simp only [toE_ofE]

/-! ## 2 Two small facts on lists -/

/-- `bodyAll` shows two rounds more than lie in front of the last stage. In Lean: the length of its
list `rs` is the number of the last stage's first round (the field o of `bodyEnd`), minus o, plus
2. -/
theorem length_body (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) : ∀ (rest : List Fmt.M1.Stage)
    (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (col : ℕ → List UInt64),
    (bodyAll p K rest j cur l o t P col D).rs.length =
      (bodyEnd p K D rest j cur l o t P col).o - o + 2
  | [], _, _, _, o, _, _, _ => by
    show 2 = o - o + 2
    omega
  | next :: rest, j, cur, l, o, t, P, col => by
    have ih := length_body p K D rest (j + 1) next (l.drop (cur.k + 3))
      (o + ((sgOf cur).h + (sgOf cur).g) + 3)
      (sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D)
      (sNext K rest.isEmpty j cur next o P (rowOf t) D)
      (sCol K rest.isEmpty j cur next o P (rowOf t) D)
    have hge := bodyEnd_o p K D rest (j + 1) next (l.drop (cur.k + 3))
      (o + ((sgOf cur).h + (sgOf cur).g) + 3)
      (sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D)
      (sNext K rest.isEmpty j cur next o P (rowOf t) D)
      (sCol K rest.isEmpty j cur next o P (rowOf t) D)
    show (sRF K j cur o P (rowOf t) D ++ sRS p K j cur next l o t P (rowOf t) D ++
      (bodyAll p K rest (j + 1) next _ _ _ _ _ D).rs).length =
      (bodyEnd p K D rest (j + 1) next _ _ _ _ _).o - o + 2
    rw [List.length_append, List.length_append, length_sRF, ih]
    show 1 + ((sgOf cur).h + (sgOf cur).g) + 2 + _ = _
    omega

theorem cut_set {α : Type} (A A' C C' : List α) (n : ℕ) (v : α) (hl : A.length = A'.length)
    (hn : A'.length ≤ n) (h : A ++ C = (A' ++ C').set n v) :
    A = A' ∧ C = C'.set (n - A'.length) v := by
  rw [List.set_append_right _ _ hn] at h
  exact List.append_inj h hl

/-! ## 3 The coin variables for the call -/

/-- The coin variables K with the first fold's coefficients replaced: `W σ 0` is that of Kr plus
`foldShift` (Johnson/LinkSim/AtText/Fold.lean) at the row of tB, the messages of P₀ and the
challenges from round number 1 on. All other entries are those of K. With this shift the first
fold's rounds at rows 0 are those at the rows P₀ and Kr: the first conjunct of `rounds_aux`, with
`atStage_first`, under their hypotheses. -/
def virtK (K Kr : BCoins) (tB : T12) (P₀ : PS) (D : ℕ → Fmt.Drawn) : BCoins :=
  { K with
    W := fun σ j =>
      match j with
      | 0 => Kr.W σ 0 + foldShift σ (vecG σ (rowOf tB)) (μOf σ P₀) fun n => D (1 + n)
      | j + 1 => K.W σ (j + 1) }

theorem virtK_same (K Kr : BCoins) (tB : T12) (P₀ : PS) (D : ℕ → Fmt.Drawn) :
    SameFrom 1 (virtK K Kr tB P₀ D) K :=
  ⟨fun _ j hj => by
    cases j with
    | zero => omega
    | succ j => rfl, rfl, rfl⟩

theorem add_zPS (P : PS) : P = addPS zPS P := by
  cases P
  simp only [addPS, zPS, zero_add]

/-- `AtStage` (Johnson/LinkSim/AtText/SpecStage.lean) holds before the first stage, between the run
at the rows P₀ and the coin variables Kr and the run at rows 0 and the coin variables Kr plus `shB`,
with the first fold's coefficients as `virtK` sets them. The difference of the two states is P₀.
Hypothesis hcol: colR and colF are equal at the positions at which the first stage's tree is
opened. -/
theorem atStage_first (p : P12) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid)
    (tB : T12) (P₀ : PS) (colR colF : ℕ → List UInt64) (D : ℕ → Fmt.Drawn) (Kr : BCoins)
    (hcol : ∀ x ∈ Fmt.listOf (openedAt D (next :: rest) s 1), colR x = colF x) :
    AtStage p D (next :: rest) 0 s l 1 tB Kr
      (virtK (addB Kr (shB p Kr D (next :: rest) 0 s l 1 tB P₀ colR P₀)) Kr tB P₀ D) P₀ zPS P₀
      colR colF where
  st := add_zPS P₀
  col := hcol
  foldW := fun _ => rfl
  word := fun h => absurd h (List.cons_ne_nil _ _)
  fr := fun _ _ => rfl
  new := fun _ _ => rfl
  W := fun _ i hi => by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hi
    rw [show 0 + n + 1 = n + 1 by omega]
    rfl

theorem zeroTextK_congr (p : P12) {K K' : BCoins} (h : SameFrom 1 K K') (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (l : Laid) (t₁ : T12) (trees : List Tree) (D : ℕ → Fmt.Drawn) :
    zeroTextK p K s next rest l t₁ trees D = zeroTextK p K' s next rest l t₁ trees D := by
  unfold zeroTextK
  rw [(restText_congr p h s next rest l 1 t₁ zeroPS trees D).1,
    (restText_congr p h s next rest l 1 t₁ zeroPS trees D).2]

/-! ## 4 The rounds -/

/-- The rounds, for two runs between which `AtStage` holds before the first stage, the second at
rows 0 and any coin variables Ks: the first fold's rounds are equal, and the rounds of `restText` at
P₀ and Kr are those of `zeroTextK` at Ks. Each side takes the state after the first fold over its
own first fold's rounds. Further hypotheses: hF and hcl, as in the head. -/
theorem rounds_aux (p : P12) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid)
    (tB : T12) (P₀ : PS) (colR colF : ℕ → List UInt64) (D : ℕ → Fmt.Drawn) (Kr Ks : BCoins)
    (hF : FitsBody D (next :: rest) s 1)
    (hA : AtStage p D (next :: rest) 0 s l 1 tB Kr Ks P₀ zPS P₀ colR colF)
    (hcl : LamZero D (bodyEnd p Kr D (next :: rest) 0 s l 1 tB P₀ colR) ∨
      OnBytes.LinkSim.AtText.ClaimTrue p (bodyEnd p Kr D (next :: rest) 0 s l 1 tB P₀ colR)) :
    aFold Kr 0 s 1 P₀ (rowOf tB) D = aFold Ks 0 s 1 zPS (rowOf tB) D ∧
      (restText p Kr s next rest l 1 (aRec1 p 0 s l tB (aFold Kr 0 s 1 P₀ (rowOf tB) D)) P₀
          [((sgOf s).C.a, colR)] D).rs =
        (zeroTextK p Ks s next rest l (aRec1 p 0 s l tB (aFold Ks 0 s 1 zPS (rowOf tB) D))
          [((sgOf s).C.a, colF)] D).rs := by
  have hf := fitAll_of_fits _ _ _ hF
  obtain ⟨-, h⟩ := bodyShiftOr p D (next :: rest) 0 s l 1 tB Kr Ks P₀ zPS P₀ colR colF hF hA hcl
  have hlen := length_body p Ks D (next :: rest) 0 s l 1 tB zPS colF
  have hge : 1 + ((sgOf s).h + (sgOf s).g) + 3 ≤
      (bodyEnd p Ks D (next :: rest) 0 s l 1 tB zPS colF).o :=
    bodyEnd_o p Ks D rest 1 next (l.drop (s.k + 3)) (1 + ((sgOf s).h + (sgOf s).g) + 3)
      (sT3 p Ks rest.isEmpty 0 s next l 1 tB zPS colF (rowOf tB) D)
      (sNext Ks rest.isEmpty 0 s next 1 zPS (rowOf tB) D)
      (sCol Ks rest.isEmpty 0 s next 1 zPS (rowOf tB) D)
  rw [body_cut p Kr s next rest l tB P₀ colR D hf, body_cut p Ks s next rest l tB zPS colF D hf]
    at h
  rw [body_cut p Ks s next rest l tB zPS colF D hf] at hlen
  have hlr : (aFold Kr 0 s 1 P₀ (rowOf tB) D).length = 1 + ((sgOf s).h + (sgOf s).g) :=
    length_sRF Kr 0 s 1 P₀ (rowOf tB) D
  have hls : (aFold Ks 0 s 1 zPS (rowOf tB) D).length = 1 + ((sgOf s).h + (sgOf s).g) :=
    length_sRF Ks 0 s 1 zPS (rowOf tB) D
  obtain ⟨h1, h2⟩ := cut_set _ _ _ _ _ _ (hlr.trans hls.symm) (by rw [hls]; omega) h
  refine ⟨h1, h2.trans ?_⟩
  simp only [List.length_append] at hlen
  have hidx : (bodyEnd p Ks D (next :: rest) 0 s l 1 tB zPS colF).o - 1 -
      (aFold Ks 0 s 1 zPS (rowOf tB) D).length =
      (restText p Ks s next rest l 1 (aRec1 p 0 s l tB (aFold Ks 0 s 1 zPS (rowOf tB) D)) zPS
        [((sgOf s).C.a, colF)] D).rs.length - 2 := by
    rw [hls] at hlen ⊢
    omega
  unfold zeroTextK
  rw [show (zeroPS : PS) = zPS from rfl, end_cut p Ks s next rest l tB zPS colF D hf]
  dsimp only
  rw [tauSim_eq, hidx]
  rfl

/-- **The rounds from the first switch on, at the rows P₀, are those of the text at rows 0 with the
one item laid anew, at the letters more by the written change.** Hypotheses hF, hcol and hcl: see
the head. Both sides take the state t₁ that is made over the first fold's rounds at P₀ and Kr. -/
theorem rest_rounds (p : P12) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid)
    (tB : T12) (P₀ : PS) (colR colF : ℕ → List UInt64) (D : ℕ → Fmt.Drawn) (Kr : BCoins)
    (hF : FitsBody D (next :: rest) s 1)
    (hcol : ∀ x ∈ Fmt.listOf (openedAt D (next :: rest) s 1), colR x = colF x)
    (hcl : LamZero D (bodyEnd p Kr D (next :: rest) 0 s l 1 tB P₀ colR) ∨
      OnBytes.LinkSim.AtText.ClaimTrue p (bodyEnd p Kr D (next :: rest) 0 s l 1 tB P₀ colR)) :
    (restText p Kr s next rest l 1 (aRec1 p 0 s l tB (aFold Kr 0 s 1 P₀ (rowOf tB) D)) P₀
        [((sgOf s).C.a, colR)] D).rs =
      (zeroTextK p (addB Kr (shB p Kr D (next :: rest) 0 s l 1 tB P₀ colR P₀)) s next rest l
        (aRec1 p 0 s l tB (aFold Kr 0 s 1 P₀ (rowOf tB) D)) [((sgOf s).C.a, colF)] D).rs := by
  obtain ⟨h1, h2⟩ := rounds_aux p s next rest l tB P₀ colR colF D Kr _ hF
    (atStage_first p s next rest l tB P₀ colR colF D Kr hcol) hcl
  rw [h2, ← h1, zeroTextK_congr p (virtK_same _ Kr tB P₀ D)]

/-! ## 5 The trees -/

/-- The positions at which the tree that round number i of `bodyAll`'s rounds sends is opened: those
that the next reading round samples, in the tree's range, each once; none where the round sends no
tree. cur: the stage at which `bodyAll` starts. o: the number of that stage's first round. -/
def openedTr (D : ℕ → Fmt.Drawn) : List Fmt.M1.Stage → Fmt.M1.Stage → ℕ → ℕ → List ℕ
  | [], _, _, _ => []
  | next :: rest, cur, o, i =>
    if i < 1 + ((sgOf cur).h + (sgOf cur).g) then []
    else if i = 1 + ((sgOf cur).h + (sgOf cur).g) then
      Fmt.listOf (qNext rest.isEmpty cur next o D)
    else openedTr D rest next (oNext cur o) (i - ((sgOf cur).h + (sgOf cur).g + 3))

theorem openedTr_zero (D : ℕ → Fmt.Drawn) (rest : List Fmt.M1.Stage) (cur : Fmt.M1.Stage) (o : ℕ) :
    openedTr D rest cur o 0 = [] := by
  cases rest with
  | nil => rfl
  | cons next rest =>
    unfold openedTr
    rw [if_pos (by omega)]

/-- The tree that round number i of `bodyAll`'s rounds sends, stage by stage. No word at the fold's
rounds and at the switch's second round; `sCol` at the switch's first round; after that, the tree of
`bodyAll` from the next stage on. -/
theorem tr_cons (p : P12) (K : BCoins) (next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (col : ℕ → List UInt64)
    (D : ℕ → Fmt.Drawn) (i : ℕ) :
    (bodyAll p K (next :: rest) j cur l o t P col D).tr.getD i (fun _ => []) =
      if i < 1 + ((sgOf cur).h + (sgOf cur).g) then fun _ => []
      else if i = 1 + ((sgOf cur).h + (sgOf cur).g) then
        sCol K rest.isEmpty j cur next o P (rowOf t) D
      else if i = 2 + ((sgOf cur).h + (sgOf cur).g) then fun _ => []
      else (bodyAll p K rest (j + 1) next (l.drop (cur.k + 3))
        (o + ((sgOf cur).h + (sgOf cur).g) + 3)
        (sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D)
        (sNext K rest.isEmpty j cur next o P (rowOf t) D)
        (sCol K rest.isEmpty j cur next o P (rowOf t) D) D).tr.getD
          (i - ((sgOf cur).h + (sgOf cur).g + 3)) fun _ => [] := by
  have hl : ((sRF K j cur o P (rowOf t) D).map fun _ (_ : ℕ) => ([] : List UInt64)).length =
      1 + ((sgOf cur).h + (sgOf cur).g) := by rw [List.length_map, length_sRF]
  show ((sRF K j cur o P (rowOf t) D).map (fun _ _ => []) ++
    [sCol K rest.isEmpty j cur next o P (rowOf t) D, fun _ => []] ++ _).getD i (fun _ => []) = _
  split_ifs with h1 h2 h3
  · rw [List.append_assoc, List.getD_append _ _ _ _ (by rw [hl]; exact h1),
      List.getD_eq_getElem _ _ (by rw [hl]; exact h1), List.getElem_map]
  · subst h2
    rw [List.append_assoc, List.getD_append_right _ _ _ _ (by rw [hl]), hl, Nat.sub_self]
    rfl
  · subst h3
    rw [List.append_assoc, List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl,
      show 2 + ((sgOf cur).h + (sgOf cur).g) - (1 + ((sgOf cur).h + (sgOf cur).g)) = 1 by omega]
    rfl
  · have hl2 : ((sRF K j cur o P (rowOf t) D).map (fun _ (_ : ℕ) => ([] : List UInt64)) ++
        [sCol K rest.isEmpty j cur next o P (rowOf t) D, fun _ => []]).length =
        (sgOf cur).h + (sgOf cur).g + 3 := by
      rw [List.length_append, hl]
      show 1 + ((sgOf cur).h + (sgOf cur).g) + 2 = _
      omega
    rw [List.getD_append_right _ _ _ _ (by rw [hl2]; omega), hl2]

/-- **Along the stages the two runs' trees have one width, and one column at each position at which
they are opened.** Hypotheses: `FitsBody` and `AtStage` at the stage at which the two runs start. -/
theorem body_trees (p : P12) (D : ℕ → Fmt.Drawn) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (Kr Ks : BCoins) (Pr Ps d : PS)
    (colr cols : ℕ → List UInt64), FitsBody D rest cur o →
    AtStage p D rest j cur l o t Kr Ks Pr Ps d colr cols → ∀ i,
    (((bodyAll p Kr rest j cur l o t Pr colr D).tr.getD i fun _ => []) 0).length =
        (((bodyAll p Ks rest j cur l o t Ps cols D).tr.getD i fun _ => []) 0).length ∧
      ∀ q ∈ openedTr D rest cur o i,
        ((bodyAll p Kr rest j cur l o t Pr colr D).tr.getD i fun _ => []) q =
          ((bodyAll p Ks rest j cur l o t Ps cols D).tr.getD i fun _ => []) q
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
  | next :: rest, j, cur, l, o, t, Kr, Ks, Pr, Ps, d, colr, cols, hF, hA, i => by
    have hS := atSwitch_of hF hA
    have ih := body_trees p D rest (j + 1) next (l.drop (cur.k + 3)) (oNext cur o)
      (tNext p Kr rest.isEmpty j cur next l o t Pr colr D) Kr Ks _ _ _ _ _ hF.2.2.2.2
      (atStage_next hF hA) (i - ((sgOf cur).h + (sgOf cur).g + 3))
    have hT : sT3 p Ks rest.isEmpty j cur next l o t Ps cols (rowOf t) D =
        tNext p Kr rest.isEmpty j cur next l o t Pr colr D :=
      (OnBytes.LinkSim.AtText.sT3_same hS).symm
    rw [tr_cons, tr_cons, hT]
    unfold openedTr
    split_ifs with h1 h2 h3
    · exact ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
    · exact ⟨by rw [length_sCol, length_sCol], fun q hq => sCol_same hS hq⟩
    · refine ⟨rfl, fun q hq => ?_⟩
      rw [h3, show 2 + ((sgOf cur).h + (sgOf cur).g) - ((sgOf cur).h + (sgOf cur).g + 3) = 0 by
        omega, openedTr_zero] at hq
    · exact ih

theorem getD_cut {α : Type} (A C : List α) (n i : ℕ) (d : α) (h : A.length = n) :
    (A ++ C).getD (n + i) d = C.getD i d := by
  rw [List.getD_append_right _ _ _ _ (by omega), h, Nat.add_sub_cancel_left]

/-- The trees, for two runs between which `AtStage` holds before the first stage: `restText` at P₀
and Kr, and `restText` at rows 0 and any coin variables Ks. Each side takes the state after the
first fold over its own first fold's rounds. Further hypothesis: hF, as in the head. -/
theorem trees_aux (p : P12) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid)
    (tB : T12) (P₀ : PS) (colR colF : ℕ → List UInt64) (D : ℕ → Fmt.Drawn) (Kr Ks : BCoins)
    (hF : FitsBody D (next :: rest) s 1)
    (hA : AtStage p D (next :: rest) 0 s l 1 tB Kr Ks P₀ zPS P₀ colR colF) (i : ℕ) :
    (((restText p Kr s next rest l 1 (aRec1 p 0 s l tB (aFold Kr 0 s 1 P₀ (rowOf tB) D)) P₀
        [((sgOf s).C.a, colR)] D).tr.getD i fun _ => []) 0).length =
      (((restText p Ks s next rest l 1 (aRec1 p 0 s l tB (aFold Ks 0 s 1 zPS (rowOf tB) D)) zPS
        [((sgOf s).C.a, colF)] D).tr.getD i fun _ => []) 0).length ∧
    ∀ q ∈ openedTr D (next :: rest) s 1 (1 + ((sgOf s).h + (sgOf s).g) + i),
      ((restText p Kr s next rest l 1 (aRec1 p 0 s l tB (aFold Kr 0 s 1 P₀ (rowOf tB) D)) P₀
        [((sgOf s).C.a, colR)] D).tr.getD i fun _ => []) q =
      ((restText p Ks s next rest l 1 (aRec1 p 0 s l tB (aFold Ks 0 s 1 zPS (rowOf tB) D)) zPS
        [((sgOf s).C.a, colF)] D).tr.getD i fun _ => []) q := by
  have hf := fitAll_of_fits _ _ _ hF
  have h := body_trees p D (next :: rest) 0 s l 1 tB Kr Ks P₀ zPS P₀ colR colF hF hA
    (1 + ((sgOf s).h + (sgOf s).g) + i)
  have hlr : ((aFold Kr 0 s 1 P₀ (rowOf tB) D).map fun _ (_ : ℕ) => ([] : List UInt64)).length =
      1 + ((sgOf s).h + (sgOf s).g) := by
    rw [List.length_map]
    exact length_sRF Kr 0 s 1 P₀ (rowOf tB) D
  have hls : ((aFold Ks 0 s 1 zPS (rowOf tB) D).map fun _ (_ : ℕ) => ([] : List UInt64)).length =
      1 + ((sgOf s).h + (sgOf s).g) := by
    rw [List.length_map]
    exact length_sRF Ks 0 s 1 zPS (rowOf tB) D
  rw [body_cut p Kr s next rest l tB P₀ colR D hf, body_cut p Ks s next rest l tB zPS colF D hf]
    at h
  dsimp only at h
  rw [getD_cut _ _ _ i _ hlr, getD_cut _ _ _ i _ hls] at h
  exact h

/-- **The trees from the first switch on**: one width; one column at each position at which they are
opened. i: the round's number from the first switch on. Hypotheses hF and hcol: see the head. -/
theorem rest_trees (p : P12) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid)
    (tB : T12) (P₀ : PS) (colR colF : ℕ → List UInt64) (D : ℕ → Fmt.Drawn) (Kr : BCoins)
    (hF : FitsBody D (next :: rest) s 1)
    (hcol : ∀ x ∈ Fmt.listOf (openedAt D (next :: rest) s 1), colR x = colF x) (i : ℕ) :
    (((restText p Kr s next rest l 1 (aRec1 p 0 s l tB (aFold Kr 0 s 1 P₀ (rowOf tB) D)) P₀
        [((sgOf s).C.a, colR)] D).tr.getD i fun _ => []) 0).length =
      (((zeroTextK p (addB Kr (shB p Kr D (next :: rest) 0 s l 1 tB P₀ colR P₀)) s next rest l
        (aRec1 p 0 s l tB (aFold Kr 0 s 1 P₀ (rowOf tB) D)) [((sgOf s).C.a, colF)] D).tr.getD i
          fun _ => []) 0).length ∧
    ∀ q ∈ openedTr D (next :: rest) s 1 (1 + ((sgOf s).h + (sgOf s).g) + i),
      ((restText p Kr s next rest l 1 (aRec1 p 0 s l tB (aFold Kr 0 s 1 P₀ (rowOf tB) D)) P₀
        [((sgOf s).C.a, colR)] D).tr.getD i fun _ => []) q =
      ((zeroTextK p (addB Kr (shB p Kr D (next :: rest) 0 s l 1 tB P₀ colR P₀)) s next rest l
        (aRec1 p 0 s l tB (aFold Kr 0 s 1 P₀ (rowOf tB) D)) [((sgOf s).C.a, colF)] D).tr.getD i
          fun _ => []) q := by
  have hA := atStage_first p s next rest l tB P₀ colR colF D Kr hcol
  have h := trees_aux p s next rest l tB P₀ colR colF D Kr _ hF hA i
  have h1 := (fold_eq Kr 0 s 1 P₀ (rowOf tB) D).symm.trans
    ((OnBytes.LinkSim.AtText.sRF_same (atSwitch_of hF hA)).trans
      (fold_eq _ 0 s 1 zPS (rowOf tB) D))
  rw [← h1] at h
  rw [← zeroTextK_congr p (virtK_same _ Kr tB P₀ D)]
  exact h

/-! ## 6 What is shown -/

/-- Two tables made of written columns col and col', as the parts' own moves make them (`sendingOf`,
`msgAt_eq`, Sim/Sims.lean): where `col 0` and `col' 0` have the same length and `col q = col' q`,
the tables' columns at q are equal. -/
theorem col_congr (a : ℕ) (col col' : ℕ → List UInt64) (q : ℕ)
    (h0 : (col 0).length = (col' 0).length) (hq : col q = col' q) :
    (⟨a, (col 0).length, fun x k => toF ((col x).getD k.val 0)⟩ : Table).col q =
      (⟨a, (col' 0).length, fun x k => toF ((col' x).getD k.val 0)⟩ : Table).col q := by
  unfold Table.col
  simp only
  rw [hq, List.ofFn_congr h0]
  rfl

/-- What is shown of two outputs is one, where the rounds are one, the trees have one width, and the
columns are one at the positions asked. The positions asked at round number i: those that asks lists
for the round's first root. -/
theorem shownFrom_congr (O O' : BOut) (dep : ℕ → Option ℕ) (n : ℕ) (asks : List (List (List ℕ)))
    (hrs : O.rs = O'.rs)
    (hw : ∀ i, ((O.tr.getD i fun _ => []) 0).length = ((O'.tr.getD i fun _ => []) 0).length)
    (hc : ∀ i, ∀ q ∈ (((asks[i]?).getD [])[0]?).getD [],
      (O.tr.getD i fun _ => []) q = (O'.tr.getD i fun _ => []) q) :
    shownFrom O dep n asks = shownFrom O' dep n asks := by
  unfold shownFrom
  refine List.map_congr_left fun i _ => ?_
  unfold shownAs sendingOf
  simp only [hrs]
  cases dep i with
  | none => rfl
  | some a =>
    simp only [Option.toList, List.map_cons, List.map_nil, List.zipIdx_cons, List.zipIdx_nil,
      Shown.mk.injEq, true_and, List.cons.injEq, and_true]
    exact List.map_congr_left fun q hq => by rw [col_congr a _ _ q (hw i) (hc i q hq)]

/-- **What is shown from the first switch on, at the rows P₀, is what is shown of the text at rows 0
with the one item laid anew, at the letters more by the written change**: where the positions asked
of a tree are among those at which it is opened. Hypotheses hF, hcol, hcl and hasks: see the
head. -/
theorem rest_view (p : P12) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid)
    (tB : T12) (P₀ : PS) (colR colF : ℕ → List UInt64) (D : ℕ → Fmt.Drawn) (Kr : BCoins)
    (dep : ℕ → Option ℕ) (n : ℕ) (asks : List (List (List ℕ)))
    (hF : FitsBody D (next :: rest) s 1)
    (hcol : ∀ x ∈ Fmt.listOf (openedAt D (next :: rest) s 1), colR x = colF x)
    (hcl : LamZero D (bodyEnd p Kr D (next :: rest) 0 s l 1 tB P₀ colR) ∨
      OnBytes.LinkSim.AtText.ClaimTrue p (bodyEnd p Kr D (next :: rest) 0 s l 1 tB P₀ colR))
    (hasks : ∀ i, ∀ q ∈ (((asks[i]?).getD [])[0]?).getD [],
      q ∈ openedTr D (next :: rest) s 1 (1 + ((sgOf s).h + (sgOf s).g) + i)) :
    shownFrom (restText p Kr s next rest l 1 (aRec1 p 0 s l tB (aFold Kr 0 s 1 P₀ (rowOf tB) D)) P₀
        [((sgOf s).C.a, colR)] D) dep n asks =
      shownFrom (zeroTextK p (addB Kr (shB p Kr D (next :: rest) 0 s l 1 tB P₀ colR P₀)) s next rest
        l (aRec1 p 0 s l tB (aFold Kr 0 s 1 P₀ (rowOf tB) D)) [((sgOf s).C.a, colF)] D) dep n
        asks :=
  shownFrom_congr _ _ dep n asks (rest_rounds p s next rest l tB P₀ colR colF D Kr hF hcol hcl)
    (fun i => (rest_trees p s next rest l tB P₀ colR colF D Kr hF hcol i).1)
    fun i q hq => (rest_trees p s next rest l tB P₀ colR colF D Kr hF hcol i).2 q (hasks i q hq)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.fitAll_of_fits
#print axioms ProofFile.Honest.K12.stagesEnd_eq
#print axioms ProofFile.Honest.K12.body_cut
#print axioms ProofFile.Honest.K12.end_cut
#print axioms ProofFile.Honest.K12.tauSim_eq
#print axioms ProofFile.Honest.K12.length_body
#print axioms ProofFile.Honest.K12.cut_set
#print axioms ProofFile.Honest.K12.virtK_same
#print axioms ProofFile.Honest.K12.add_zPS
#print axioms ProofFile.Honest.K12.atStage_first
#print axioms ProofFile.Honest.K12.zeroTextK_congr
#print axioms ProofFile.Honest.K12.rounds_aux
#print axioms ProofFile.Honest.K12.rest_rounds
#print axioms ProofFile.Honest.K12.openedTr_zero
#print axioms ProofFile.Honest.K12.tr_cons
#print axioms ProofFile.Honest.K12.body_trees
#print axioms ProofFile.Honest.K12.getD_cut
#print axioms ProofFile.Honest.K12.trees_aux
#print axioms ProofFile.Honest.K12.rest_trees
#print axioms ProofFile.Honest.K12.col_congr
#print axioms ProofFile.Honest.K12.shownFrom_congr
#print axioms ProofFile.Honest.K12.rest_view
#print axioms ProofFile.Honest.K12.toEnd
#print axioms ProofFile.Honest.K12.virtK
#print axioms ProofFile.Honest.K12.openedTr
