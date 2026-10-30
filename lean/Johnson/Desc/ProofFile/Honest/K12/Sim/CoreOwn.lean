-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/CoreOwn.lean: over the second part's own numbered coins,
sampled uniformly: what is shown of a proximity test's text from the first switch on at given rows,
and what is shown of the text at rows 0 with one item laid anew, have one law. An equation of two
texts' laws. No property is claimed, and it is no sentence on a simulator: the state tB, the first
fold's coefficients and the column in front are letters: nothing here says that they are made of
public things. The main theorem is `core_own`. It holds at all numbers of a place p (`P12`,
Johnson/Desc/K12/Frame.lean), at every list of two or more stages s :: next :: rest, and at all
values of the other parameters that meet the hypotheses below. Definitions and theorems.
Sim/ClaimBody.lean, which imports this file, calls `core_own`.

In this head: a text is a Lean term with a value in `BOut` (Johnson/Prover/Link/BodyAll.lean): the
rounds, for each round the written column of the tree that it sends, and groups of columns. The text
from the first switch on is `restText` (Sim/Text.lean). Rows are a prover's state at a stage (`PS`,
Johnson/Prover/Link/BodyState.lean). The given rows are P₀, and the real text is `restText` at P₀.
The text at rows 0 with one item laid anew is `zeroText` (Sim/Sims.lean): `restText` at the state
`zeroPS`, in which every entry is 0, with the last round but one replaced by a round whose only item
is `tauSim`. What is shown of a text is `shownFrom` (Sim/Sims.lean) at dep, n and asks: for each i
below n a `Shown` (the frame, Johnson/Desc/ProofFile/Honest/Frame.lean), which holds the items of
the text's round number i and, where `dep i` is a depth, the columns of the tree that this round
sends, at the positions in the first list of asks at i. `shownFrom` does not read the text's groups
of columns. The two views are `realOwn` and `zeroOwn`. A law is a distribution, here `PMF.map` of a
view over `Prob.unif`; the law, as the name of `core_own`, is the equation of the two. A stage is a
`Fmt.M1.Stage`, with codes C and Z and numbers k and h; its sizes are `sgOf` of it
(Johnson/Desc/K12/Law/ChainOf.lean), where g is k - h. A main row's tail has C.r entries, a mask
row's Z.r. Every stage but the last has a fold and then a switch to the next stage. A reading round
is a round whose challenge samples positions. D gives the challenges by the round's number; the
first fold's first round has the number 1. The second part is `restPart`
(Johnson/Desc/ProofFile/Honest/K12/Parts.lean): every switch, every later fold and the last stage.
Numbered coins, or coins by number, are a function c : ℕ → `GE`. Typed coins are a `Cs d` (the
frame), whose type states the count; `stretchOf` reads them by number and gives 0 from the count on.
The part's count is `dueFrom s (next :: rest)`. `stretchOf`, `coinsOf`, `hideAt`, `dueFrom` and
`dueRest` are defined in Johnson/Desc/ProofFile/Honest/K12/Coins.lean. The finite type is
`BodyK GE s (next :: rest)` (Johnson/Prover/Link/LinkCoin.lean). The two readers are two maps from
numbered coins to `BCoins` (BodyAll.lean), the random values that a text takes as a parameter:
`coinsOf`, and `toBody` (Sim/Bridge.lean) followed by `layBody` (Sim/CoreLaw.lean). Inside the
sizes: at the indices that `KSame` and `PSame` (Sim/Reads.lean) name. `budRest` is defined in
Sim/Row.lean. tB has the type `T12` (Johnson/Desc/K12/Join.lean): the state that the steps of a
test's description take and return. The first fold's coefficients are `hideW hide`. `entryOf`
(Sim/CoreLaw.lean) is `aRec1` (Johnson/Desc/K12/Honest/Stages.lean) at tB over the first fold's
rounds (`foldShown`, Johnson/Desc/K12/Honest/Fold.lean) at the row of tB, at P₀ and at `hideW hide`:
the state that the description's fold returns, or tB where it rejects. colR, on the left side, and
colF, on the right side, are in the place of the written column of the one tree that holds the first
stage's rows; colF is the column in front. A letter is a free parameter, or a field of a structure.
A premise is a hypothesis; it is asked where it is a hypothesis, and whoever pays it proves it. To
lay: to put or to make. To stand: to occur; how it stands to: how it compares with. To hold against:
to compare with. In front of, behind: before, after.

  `core_own`: the law (`dueFrom s (next :: rest)` is `dueRest (s :: next :: rest)`, by unfolding).
    In Lean: `PMF.map` of `realOwn` at `(stretchOf c).e` and `PMF.map` of `zeroOwn` at
    `(stretchOf c).e`, both over `Prob.unif (OwnCs s (next :: rest))`, are equal, under the five
    hypotheses below
  `own_reads`: neither view reads a coin from the part's count on. In Lean: where c and c' agree at
    every number below `dueFrom s (next :: rest)`, `realOwn` is the same at c and at c', and so is
    `zeroOwn`. Hypotheses: the last stage has h = 0; h ≤ k at every stage in next :: rest
  `realOwn`, `zeroOwn`, `endOwn`, `EndOk`, `real_own`, `zero_own`, `claim_own`, `claim_all`,
    `OwnCs`: the two views, the last stage's letters and the premise on the last claim, at coins by
    number; each carried over to the finite type; the typed coins. One by one in the next seven
    entries
  `realOwn`: a definition: what is shown of the text at the rows P₀, at coins by number. In Lean:
    `shownFrom` of `restText` at `coinsOf (s :: next :: rest) hide c`, at the state `entryOf`, at P₀
    and at the one tree `((sgOf s).C.a, colR)`
  `zeroOwn`: a definition: what is shown of the text at rows 0 with the one item laid anew, at coins
    by number. In Lean: `shownFrom` of `zeroText` at c, at the same state `entryOf` and at the one
    tree `((sgOf s).C.a, colF)`
  `endOwn`: a definition: `restEnd` (Sim/Text.lean) at the arguments of `restText` in `realOwn`. It
    is an `EndAt` (Sim/Text.lean): the last stage's number, the stage, the number o of its first
    round, and the two states there: t of type `T12`, P of type `PS`
  `EndOk`: a definition: the last sampled element, `toE ((D o).elems.headD (0, 0, 0))` at the o of
    `endOwn`, is 0, or `EndTrue` (Sim/Spec.lean) holds at `endOwn`: the claim that is left at the
    last stage is true on the last message. Both alternatives read a default: see the limits
  `OwnCs s rest`: a definition: the coins that the second part takes. In Lean:
    `Cs ⟨0, dueFrom s rest⟩`, no element of the base field and `dueFrom s rest` of the extension
    field
  `real_own`, `zero_own`: where the last stage has h = 0: `realOwn` at c is `realView`, and
    `zeroOwn` at c is `zeroView` (both Sim/CoreLaw.lean), at the coefficients `hideW hide` and at
    `toBody s (next :: rest) 0 c`
  `claim_own`, `claim_all`: where the last stage has h = 0 and each stage fits the next (`FitAll`,
    Stages.lean), `EndOk` at c gives the hypothesis hcl of `core_body` at
    `toBody s (next :: rest) 0 c`: `LamZero` or `ClaimTrue`
    (Johnson/LinkSim/AtText/SpecShiftIn.lean, Defs.lean) at `bodyEnd`
    (Johnson/Prover/Link/BodyEnd.lean); under hF, hlow and hcl below, the same at every k in the
    finite type
  `hideW hide σ`: a definition: `hideAt (σ.h + σ.g) hide`, which is the field `W σ 0` of
    `coinsOf stages hide c`
  `own_same`: for numbered coins c, where the last stage has h = 0:
    `coinsOf (s :: next :: rest) hide' c`, at any hide', and `layBody` at `hideW hide` and
    `toBody s (next :: rest) 0 c` meet `KSame` from switch number 0 on
  `lastZero`: under `FitsBody D rest cur o` the last stage of cur :: rest has h = 0
  `endTrue_same`, `claim_iff`: `EndTrue` at an `EndAt` e holds with the state Q for `e.P` if and
    only if it holds with Q', where Q and Q' meet `PSame (sgOf e.cur) true`; `ClaimTrue` at e is
    `EndTrue` at `toEnd e` (Sim/CoreText.lean), by `Iff.rfl`
  `csNonempty`: a local instance: `Cs d` is not empty

By what. It is `core_body` (Sim/CoreLaw.lean), carried from the finite type `BodyK` to the coins
that the part takes (`Cs ⟨0, dueRest stages⟩`, read by `coinsOf`): the two readers lay the same
inside the sizes (`bridge_same`, Sim/Bridge.lean); the text reads nothing else (`restText_same`,
`zeroTextK_same`, Sim/Reads.lean); the map between the two types of coins is one to one and onto
(`toBody_bij`, Sim/BridgeBij.lean), so it carries the uniform law to the uniform law. That last step
is `Prob.map_unif_of_bijective` (Prob/Linear.lean). `own_same` calls `bridge_same` at `laid_lay`
(Sim/CoreLaw.lean). `own_reads` calls `takes_body` (Sim/BridgeBij.lean). `claim_own` calls
`restEnd_same` (Sim/Reads.lean) and `end_cut` (Sim/CoreText.lean); `claim_all` calls `toBody_bij`,
`claim_own` and `fitAll_of_fits` (Sim/CoreText.lean).

Hypotheses of `core_own`.
- hF: `FitsBody D (next :: rest) s 1` (Johnson/LinkSim/AtText/SpecShift.lean). At every stage but
  the last: the list of positions that the second round of the stage's switch samples is no longer
  than C.r and no longer than Z.r; h + 2 g + 1 ≤ Z.l; the stage fits the next (`CsFit`). At the last
  stage: the list of positions that its second round samples is no longer than C.r and no longer
  than Z.r; h = 0 and g = 0.
- hlow: h ≤ k at every stage in next :: rest.
- hcol: colR and colF are equal at every position in `Fmt.listOf (openedAt D (next :: rest) s 1)`
  (`openedAt`, Johnson/LinkSim/AtText/SpecStage.lean): the positions that the second round of the
  first switch samples, taken modulo 2^a, a being the first stage's `C.a`.
- hcl: `EndOk` holds at `(stretchOf c).e`, for every c in `OwnCs s (next :: rest)`.
- hasks: for every i, each position in the first list of asks at i is in
  `openedTr D (next :: rest) s 1 (1 + (h + g) + i)` (Sim/CoreText.lean), with h and g from the first
  stage's sizes.

Limits.
- tB is a free parameter: no statement that this state is the verifier's. "The verifier's state"
  names below what the description's fold computes from tB.
- On the right side the rows P₀ and the first fold's coefficients still stand, through `entryOf`
  alone (Sim/CoreLaw.lean): the verifier's state behind the first fold, which is a function of tB
  and of the first fold's rounds as they are shown.
- The column colF is read just at the positions at which the premise makes it colR. This is read off
  `restText_trees` (Sim/Text.lean) and the definitions `aGroups` (Stages.lean) and `groupAt`
  (BodyAll.lean); no theorem of this file states it.
- How it stands to `Spec.core` (Sim/Spec.lean). No theorem says that it is an instance. It is
  narrower, or other, in these:
  the state behind the first fold is the one that the description's fold leaves from a letter tB
  over the text's own first fold's rounds ·
  one tree in front, of the first stage's depth ·
  the positions asked of a tree are among those that the next reading round samples, and these,
  counted with repeats, are no more than a row's tail is long: `budRest` allows more, and counts
  different points ·
  how many rounds are shown is a letter n, not the text's own count ·
  `FitsBody`'s first clause holds the first reading round's positions against the first stage's
  tails, which are no rows of this text's own trees, and it asks h = g = 0 at the last stage:
  neither stands among `Spec.core`'s premises.
- Under the hypothesis on sizes (`FitsBody`: each stage fits the next; no list of sampled positions
  is longer than a row's tail; the packing has room; the last stage has h = g = 0), and under h ≤ k
  at every stage after the first.
- The premise on the claim that is left at the real text's last stage is asked at every coin (or the
  last sampled element is 0); nothing says who pays it. `core_inv` (Sim/ClaimBody.lean) has another
  hypothesis in its place, also at every coin.
- `EndOk` holds by a default too. Where round number o of `endOwn` sampled no element, `headD` gives
  (0, 0, 0), `toE` of that is 0 (`toE_zeroE`, OnBytes/Slice/Field.lean), and the first alternative
  holds: it does not say that a 0 was sampled. `EndTrue` reads the claim by `claimAtEnd`
  (Sim/Text.lean): where `stageAt` or `claimAt` gives `none`, that is the claim with no
  coefficients and the target (0, 0, 0). Nothing in this file tests for either case. The texts read
  the element and the claim by the same two defaults (`lastOut`, BodyAll.lean; `tauSim`,
  Sim/Sims.lean).
- That the five hypotheses hold together at any values is not shown in this file. They have no
  values that meet them together in the library yet, and no file in the library shows that the two
  sides differ.
- Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.CoreLaw
import Johnson.Desc.ProofFile.Honest.K12.Sim.BridgeBij
import Johnson.Desc.ProofFile.Honest.K12.Sim.Spec
import Prob.Linear

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open OnBytes.LinkSim.AtText (FitsBody openedAt LamZero)

/-- Under the hypothesis on sizes (`FitsBody`) the last stage has h = 0. -/
theorem lastZero {D : ℕ → Fmt.Drawn} : ∀ (rest : List Fmt.M1.Stage) (cur : Fmt.M1.Stage) (o : ℕ),
    FitsBody D rest cur o → ∀ st, (cur :: rest).getLast? = some st → st.h = 0
  | [], cur, _, h, st, hst => by
    obtain rfl : cur = st := by simpa using hst
    exact h.2.2.1
  | next :: rest, _, _, h, st, hst =>
    lastZero rest next _ h.2.2.2.2 st (by simpa using hst)

/-- The first fold's coefficients as `coinsOf` reads them from hide: its field `W σ 0`. -/
def hideW (hide : ℕ → GE) (σ : Sg) : HIdx (sVars GE 2 (σ.h + σ.g)) → GE := hideAt (σ.h + σ.g) hide

/-- At coins by number c, where the last stage has h = 0: what `coinsOf` reads from c, and what
`layBody` builds from `toBody s (next :: rest) 0 c`, agree inside the sizes (`KSame`,
Sim/Reads.lean). -/
theorem own_same (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hide hide' c : ℕ → GE)
    (hz : ∀ st, (s :: next :: rest).getLast? = some st → st.h = 0) :
    KSame (coinsOf (s :: next :: rest) hide' c)
      (layBody s (next :: rest) (hideW hide) (toBody s (next :: rest) 0 c)) s (next :: rest) 0 :=
  bridge_same (s :: next :: rest) hide' c (next :: rest) s 0 _ rfl hz (laid_lay _ _)

/-- `EndTrue` reads the last state inside the sizes only: it holds at Q if and only if it holds at
Q', where the two agree there (`PSame`, Sim/Reads.lean). -/
theorem endTrue_same (p : P12) (e : EndAt) (Q Q' : PS) (h : PSame (sgOf e.cur) true Q Q') :
    EndTrue p { e with P := Q } ↔ EndTrue p { e with P := Q' } := by
  unfold EndTrue claimAtEnd
  simp only
  rw [h.mu]

theorem claim_iff (p : P12) (e : BEnd) :
    OnBytes.LinkSim.AtText.ClaimTrue p e ↔ EndTrue p (toEnd e) := Iff.rfl

section Own
variable (p : P12) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid) (tB : T12)
  (P₀ : PS) (hide : ℕ → GE) (colR colF : ℕ → List UInt64) (D : ℕ → Fmt.Drawn) (dep : ℕ → Option ℕ)
  (n : ℕ) (asks : List (List (List ℕ)))

/-- What is shown of the text at the rows P₀, at coins by number. -/
def realOwn (c : ℕ → GE) : List Shown :=
  shownFrom (restText p (coinsOf (s :: next :: rest) hide c) s next rest l 1
    (entryOf p s l tB P₀ (hideW hide) D) P₀ [((sgOf s).C.a, colR)] D) dep n asks

/-- What is shown of the text at rows 0 with the one item laid anew, at coins by number. -/
def zeroOwn (c : ℕ → GE) : List Shown :=
  shownFrom (zeroText p s next rest l (entryOf p s l tB P₀ (hideW hide) D) [((sgOf s).C.a, colF)] c
    D) dep n asks

/-- The values at the last stage (`EndAt`, Sim/Text.lean) of the text at the rows P₀, at coins by
number. -/
def endOwn (c : ℕ → GE) : EndAt :=
  restEnd p (coinsOf (s :: next :: rest) hide c) s next rest l 1
    (entryOf p s l tB P₀ (hideW hide) D) P₀ [((sgOf s).C.a, colR)] D

/-- The hypothesis on the last claim, at coins by number: the last sampled element is 0, or the
claim that is left at the last stage is true on the last message. The first alternative holds too
where that round sampled no element: `headD` then gives (0, 0, 0). The claim is `claimAtEnd`'s
(Sim/Text.lean), which has a default of its own. See the limits in the head of this file. -/
def EndOk (c : ℕ → GE) : Prop :=
  toE ((D (endOwn p s next rest l tB P₀ hide colR D c).o).elems.headD (0, 0, 0)) = 0 ∨
    EndTrue p (endOwn p s next rest l tB P₀ hide colR D c)

variable (hz : ∀ st, (s :: next :: rest).getLast? = some st → st.h = 0)

include hz in
theorem real_own (c : ℕ → GE) :
    realOwn p s next rest l tB P₀ hide colR D dep n asks c =
      realView p s next rest l tB P₀ (hideW hide) colR D dep n asks
        (toBody s (next :: rest) 0 c) := by
  unfold realOwn realView
  rw [restText_same p s next rest l 1 (entryOf p s l tB P₀ (hideW hide) D) P₀ P₀
    [((sgOf s).C.a, colR)] D (own_same s next rest hide hide c hz) (PSame.refl _ _ _)]

include hz in
theorem zero_own (c : ℕ → GE) :
    zeroOwn p s next rest l tB P₀ hide colF D dep n asks c =
      zeroView p s next rest l tB P₀ (hideW hide) colF D dep n asks
        (toBody s (next :: rest) 0 c) := by
  unfold zeroOwn zeroView zeroText
  rw [zeroTextK_same p s next rest l (entryOf p s l tB P₀ (hideW hide) D) [((sgOf s).C.a, colF)] D
    (own_same s next rest hide (fun _ => 0) c hz)]

include hz in
/-- **Neither view reads a coin from the part's count on.** -/
theorem own_reads (hlow : ∀ st ∈ next :: rest, st.h ≤ st.k) (c c' : ℕ → GE)
    (h : ∀ i, i < dueFrom s (next :: rest) → c i = c' i) :
    realOwn p s next rest l tB P₀ hide colR D dep n asks c =
        realOwn p s next rest l tB P₀ hide colR D dep n asks c' ∧
      zeroOwn p s next rest l tB P₀ hide colF D dep n asks c =
        zeroOwn p s next rest l tB P₀ hide colF D dep n asks c' := by
  have e := (takes_body s (next :: rest) hlow).congr 0 c c' fun i _ hi => h i (by omega)
  rw [real_own p s next rest l tB P₀ hide colR D dep n asks hz c,
    real_own p s next rest l tB P₀ hide colR D dep n asks hz c',
    zero_own p s next rest l tB P₀ hide colF D dep n asks hz c,
    zero_own p s next rest l tB P₀ hide colF D dep n asks hz c', e]
  exact ⟨rfl, rfl⟩

include hz in
/-- The hypothesis on the last claim, carried over to the finite type: `EndOk` at c gives `LamZero`
or `ClaimTrue` at `bodyEnd`, at `toBody s (next :: rest) 0 c`. -/
theorem claim_own (hf : FitAll s (next :: rest)) (c : ℕ → GE)
    (h : EndOk p s next rest l tB P₀ hide colR D c) :
    LamZero D (bodyEnd p (layBody s (next :: rest) (hideW hide) (toBody s (next :: rest) 0 c)) D
        (next :: rest) 0 s l 1 tB P₀ colR) ∨
      OnBytes.LinkSim.AtText.ClaimTrue p
        (bodyEnd p (layBody s (next :: rest) (hideW hide) (toBody s (next :: rest) 0 c)) D
          (next :: rest) 0 s l 1 tB P₀ colR) := by
  obtain ⟨Q, Q', hQ, e1, e2⟩ := restEnd_same p s next rest l 1
    (entryOf p s l tB P₀ (hideW hide) D) P₀ P₀ [((sgOf s).C.a, colR)] D
    (own_same s next rest hide hide c hz) (PSame.refl _ _ _)
  have e3 := end_cut p (layBody s (next :: rest) (hideW hide) (toBody s (next :: rest) 0 c)) s next
    rest l tB P₀ colR D hf
  have e4 : toEnd (bodyEnd p (layBody s (next :: rest) (hideW hide) (toBody s (next :: rest) 0 c)) D
      (next :: rest) 0 s l 1 tB P₀ colR) =
      { endOwn p s next rest l tB P₀ hide colR D c with P := Q' } := e3.symm.trans e2
  rcases h with h | h
  · left
    have e5 := congrArg EndAt.o e4
    exact (congrArg (fun o => toE ((D o).elems.headD (0, 0, 0))) e5).trans h
  · right
    have h1 : EndTrue p { endOwn p s next rest l tB P₀ hide colR D c with P := Q } :=
      Eq.mp (congrArg (EndTrue p) e1) h
    have h2 := (endTrue_same p (endOwn p s next rest l tB P₀ hide colR D c) Q Q' hQ).1 h1
    exact (claim_iff p _).2 (Eq.mpr (congrArg (EndTrue p) e4) h2)

end Own

section Law
variable (p : P12) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid) (tB : T12)
  (P₀ : PS) (hide : ℕ → GE) (colR colF : ℕ → List UInt64) (D : ℕ → Fmt.Drawn) (dep : ℕ → Option ℕ)
  (n : ℕ) (asks : List (List (List ℕ)))

/-- The coins that the second part takes. -/
abbrev OwnCs (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) : Type := Cs ⟨0, dueFrom s rest⟩

/-- The type `Cs d` is not empty. Stated as an instance with a name: under this file's imports the
search for it runs out of its limit. A local instance, not a global one: a file that imports this
one switches it on for itself. -/
local instance csNonempty (d : Due) : Nonempty (Cs d) := ⟨default⟩

variable (hF : FitsBody D (next :: rest) s 1) (hlow : ∀ st ∈ next :: rest, st.h ≤ st.k)
  (hcol : ∀ x ∈ Fmt.listOf (openedAt D (next :: rest) s 1), colR x = colF x)
  (hcl : ∀ c : OwnCs s (next :: rest), EndOk p s next rest l tB P₀ hide colR D (stretchOf c).e)
  (hasks : ∀ i, ∀ q ∈ (((asks[i]?).getD [])[0]?).getD [],
    q ∈ openedTr D (next :: rest) s 1 (1 + ((sgOf s).h + (sgOf s).g) + i))

include hF hlow hcl in
theorem claim_all (k : BodyK GE s (next :: rest)) :
    LamZero D (bodyEnd p (layBody s (next :: rest) (hideW hide) k) D (next :: rest) 0 s l 1 tB P₀
        colR) ∨
      OnBytes.LinkSim.AtText.ClaimTrue p
        (bodyEnd p (layBody s (next :: rest) (hideW hide) k) D (next :: rest) 0 s l 1 tB P₀
          colR) := by
  obtain ⟨c, rfl⟩ := (toBody_bij s (next :: rest) hlow).2 k
  exact claim_own p s next rest l tB P₀ hide colR D (lastZero (next :: rest) s 1 hF)
    (fitAll_of_fits _ _ _ hF) (stretchOf c).e (hcl c)

include hF hlow hcol hcl hasks in
/-- **The law, at the second part's own coins.** Hypotheses and limits: the head of this file. -/
theorem core_own :
    PMF.map (fun c : OwnCs s (next :: rest) =>
        realOwn p s next rest l tB P₀ hide colR D dep n asks (stretchOf c).e)
        (Prob.unif (OwnCs s (next :: rest))) =
      PMF.map (fun c : OwnCs s (next :: rest) =>
        zeroOwn p s next rest l tB P₀ hide colF D dep n asks (stretchOf c).e)
        (Prob.unif (OwnCs s (next :: rest))) := by
  letI := bodyFintype s (next :: rest)
  haveI := bodyNonempty s (next :: rest)
  have hz := lastZero (next :: rest) s 1 hF
  have hm := Prob.map_unif_of_bijective (toBody_bij s (next :: rest) hlow)
  have hc := core_body p s next rest l tB P₀ (hideW hide) colR colF D dep n asks hF hcol
    (claim_all p s next rest l tB P₀ hide colR D hF hlow hcl) hasks
  rw [← hm, PMF.map_comp, PMF.map_comp] at hc
  have e1 : (fun c : OwnCs s (next :: rest) =>
      realOwn p s next rest l tB P₀ hide colR D dep n asks (stretchOf c).e) =
      realView p s next rest l tB P₀ (hideW hide) colR D dep n asks ∘
        fun c : OwnCs s (next :: rest) => toBody s (next :: rest) 0 (stretchOf c).e :=
    funext fun c => real_own p s next rest l tB P₀ hide colR D dep n asks hz (stretchOf c).e
  have e2 : (fun c : OwnCs s (next :: rest) =>
      zeroOwn p s next rest l tB P₀ hide colF D dep n asks (stretchOf c).e) =
      zeroView p s next rest l tB P₀ (hideW hide) colF D dep n asks ∘
        fun c : OwnCs s (next :: rest) => toBody s (next :: rest) 0 (stretchOf c).e :=
    funext fun c => zero_own p s next rest l tB P₀ hide colF D dep n asks hz (stretchOf c).e
  rw [e1, e2]
  exact hc

end Law

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.lastZero
#print axioms ProofFile.Honest.K12.own_same
#print axioms ProofFile.Honest.K12.endTrue_same
#print axioms ProofFile.Honest.K12.claim_iff
#print axioms ProofFile.Honest.K12.real_own
#print axioms ProofFile.Honest.K12.zero_own
#print axioms ProofFile.Honest.K12.own_reads
#print axioms ProofFile.Honest.K12.claim_own
#print axioms ProofFile.Honest.K12.claim_all
#print axioms ProofFile.Honest.K12.core_own
#print axioms ProofFile.Honest.K12.hideW
#print axioms ProofFile.Honest.K12.realOwn
#print axioms ProofFile.Honest.K12.zeroOwn
#print axioms ProofFile.Honest.K12.endOwn
#print axioms ProofFile.Honest.K12.EndOk
#print axioms ProofFile.Honest.K12.OwnCs
#print axioms ProofFile.Honest.K12.csNonempty
