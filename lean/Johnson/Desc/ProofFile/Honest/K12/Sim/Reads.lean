-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/Reads.lean: the text of a proximity test's stages reads its
coins' letters and the prover's state inside the stages' sizes alone. The text is `stagesAll`
(Johnson/Desc/K12/Honest/Stages.lean): the rounds, the trees and the groups of columns of the stages
from a stage on. Its coins' letters are the fields of `BCoins` (Johnson/Prover/Link/BodyAll.lean),
the random values that it takes as a parameter. The prover's state at a stage is `PS`
(Johnson/Prover/Link/BodyState.lean). The theorems are equations between texts: at two values of
`BCoins` and at two states that agree inside the sizes, the text is the same. The same is proved of
`restText` (Sim/Text.lean), which begins at the first switch, and of `zeroTextK` (Sim/Sims.lean).
General in the list of stages and in every other argument of the text. Definitions and theorems.

For what. The fields of `BCoins` and of `PS` are functions on all natural numbers, `W` also on all
sizes. Two readers of coins can lay the same values inside the sizes and other things outside: one
lays written zeros (Johnson/Prover/Link/LinkCoin.lean), another whatever coin stands next
(Johnson/Desc/ProofFile/Honest/K12/Coins.lean). A reader of coins is here a map from coins to
`BCoins`: `coinsOf` in Coins.lean, and the field `body` of what `coinsOf` in LinkCoin.lean returns.
Whoever takes a statement on the text over from one of the two to the other needs that the text is
the same at both. Sim/CoreOwn.lean calls `restText_same`, `restEnd_same` and `zeroTextK_same` for
that.

In the list: a test has a list of stages (`Fmt.M1.Stage`). Every stage but the last has a fold and
then a switch, which leads to the next stage; both have the stage's number. The sizes σ of a stage s
are `sgOf s` (Johnson/Desc/K12/Law/ChainOf.lean; its type: `Sg`, OnBytes/Slice/Stage.lean): C and Z
are the codes of a main row and of a mask row, each with a message of l entries and a tail of r
entries; there are 2^(h+g) main rows and 2^h mask rows; g is k - h. K and K' are values of `BCoins`:
`W σ j` holds the coefficients from which fold number j sends its rounds; `new j` (a `PS`) and
`fr j` go into switch number j. P, P', Q, Q' are states.

  `stagesAll_same`: `stagesAll` from the stage cur (number j) on is the same at (K, P) and at
    (K', P'), under the three hypotheses below
  `restText_same`: `restText` is the same at (K, P) and at (K', P'), where `KSame K K'` holds from
    switch number 0 on and `PSame` at the first stage's sizes with last := false. No hypothesis is
    on the first fold's coefficients
  `zeroTextK_same`: `zeroTextK` is the same at K and at K', where `KSame K K'` holds from switch
    number 0 on. `zeroTextK` (Sim/Sims.lean) is `restText` at the state `zeroPS`, in which every
    entry is 0, with the last round but one replaced by a round whose one item is `tauSim`
  `stagesEnd_same`, `restEnd_same`: `stagesEnd` and `restEnd` (Sim/Text.lean) return the values at
    the last stage (`EndAt`): its number, the stage, the number of its first round, the verifier's
    state, the prover's state. Under the hypotheses of `stagesAll_same` (for `stagesEnd`) and of
    `restText_same` (for `restEnd`): at (K, P) and at (K', P') the first four are the same, and the
    two prover's states meet `PSame` at the last stage's sizes with last := true
  `tauSim_same`: `tauSim` (Sim/Sims.lean) is the same at two values of `EndAt` that differ in the
    prover's state only, where the two states meet `PSame` at the stage's sizes with last := true
  `PSame σ last P P'`: a definition: two states agree inside the sizes σ: both tables, all tails,
    the fresh table and its tails; at a last stage the masking word too. Field by field: the tables
    `tabM` below 2^(h+g) * C.l and `tabZ` below 2^h * Z.l; their rows' tails `tM` at rows below
    2^(h+g) and entries below C.r, and `tZ` at rows below 2^h and entries below Z.r; the fresh table
    `fM` at rows below 2^h and entries below Z.l, and its tails `fT` at rows below 2^h and entries
    below Z.r; where last = true, the masking word `sM` below C.l and its tail `sT` below C.r
  `PSame.refl`: a state meets `PSame` with itself
  `PSame.mu`, `PSame.rho`, `PSame.phi`, `PSame.psi`: under `PSame`, `μOf`, `ρOf`, `φOf` and `ψOf`
    (BodyState.lean), which read a state at the index types of σ, are the same at both states
  `SwSame σ σ' last fr fr' new new'`: a definition: the values `fr j` and `new j` of one switch
    agree inside the sizes. σ: the sizes before the switch; σ', with h', C', Z': after it; last: the
    stage after it is the last. `fr` at every i with `carriedN σ` ≤ i < 2^h' * Z'.l (`carriedN`,
    Johnson/LinkSim/AtText/Places.lean: how many entries of the new mask table hold what the fold
    leaves); `tM`, `tZ` and `fT` of `new` inside σ', as in `PSame`; where last = true, also `fM`,
    `sM` and `sT`. It has no clause on `tabM` and `tabZ` of `new`, nor, where last = false, on `fM`,
    `sM` and `sT`
  `KSame K K' cur rest j`: a definition, by recursion on rest, the list of the stages after cur:
    `SwSame` at every switch from number j on; and for every stage after cur but the last, `W` at
    that stage's sizes and number is the same in K and K'. At an empty list it is `True`. The
    coefficients of the fold of cur are not in it
  `next_same`: the states after a switch (`aNext`, Stages.lean) at (K, P) and at (K', P') meet
    `PSame` at the next stage's sizes. Hypotheses: P and P' meet `PSame` at the sizes of cur, with
    any second argument; `SwSame` at this switch; where the next stage is not the last, `W` at its
    sizes and number is the same
  `col_same`: the written column of the tree that a switch sends (`aCol`, Stages.lean) is the same
    at two states that meet `PSame` at the next stage's sizes
  `last_same`: what `lastAll` (Stages.lean) returns for the last stage is the same at two states
    that meet `PSame` with last := true
  `gMask_same`: `gMask` (Johnson/Prover/Link/SwitchMsg.lean: the new mask table, by index) at the
    index i is the same for fr and fr', if fr i = fr' i where `carriedN s` ≤ i
  `idx_lt`: r < k and j < l give r + k * j < k * l

By what. `stagesAll_same` and `stagesEnd_same` follow the recursion of `stagesAll`. At a stage that
is not the last, `PSame.mu` and the hypothesis on `W` give the fold's rounds, `next_same` gives
`PSame` of the two states after the switch, `col_same` the new tree's column, and `PSame.mu` at
these states the answer. At the last stage `stagesAll_same` calls `last_same`. `restText_same` and
`restEnd_same` treat the first switch in the same way and then call these two. `zeroTextK_same`
calls `restText_same`, `restEnd_same` and `tauSim_same`, at the state `zeroPS` (Sim/Sims.lean) and
`PSame.refl`. The congruences of a symbol, a form and a written list are called: `symG_congr`,
`formG_congr` (Johnson/Prover/Link/Base.lean); `wr_congr` (Johnson/LinkSim/AtText/Sym.lean);
`stageColW_congr`, `baseColW_congr` (Johnson/LinkSim/AtText/Cols.lean). `rowNo_lt`
(OnBytes/Slice/Cells.lean) bounds a row's number.

Hypotheses of `stagesAll_same`; `stagesEnd_same` has the same. `KSame K K' cur rest j`. Where rest
is not empty, `K.W (sgOf cur) j = K'.W (sgOf cur) j`: the coefficients of the fold of cur.
`PSame (sgOf cur) rest.isEmpty P P'`: its second argument says whether cur is the last stage.

Limits. Sufficient conditions; that the text reads every place inside the sizes is not said. No
property is claimed; nothing here speaks of a law or of a simulator. No statement here names `Sim`,
`firstSim` or `restSim`; `tauSim` and `zeroTextK`, of which two theorems here speak, are definitions
of which `restSim` (Sim/Sims.lean) is made. That two given values of `BCoins` meet `KSame` is not
shown here; `bridge_same` (Sim/Bridge.lean) is such a statement. The equations hold at all
arguments, also at such as no run reaches. Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.Sims
import Johnson.LinkSim.AtText.Places
import OnBytes.Slice.Cells

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open OnBytes.LinkSim.AtText (carriedN wr_congr stageColW_congr baseColW_congr)

/-! ## 1 Two states inside a stage's sizes -/

/-- Two states agree inside the sizes σ. last: the stage is the last: then the masking word too. -/
structure PSame (σ : Sg) (last : Bool) (P P' : PS) : Prop where
  tabM : ∀ i, i < 2 ^ (σ.h + σ.g) * σ.C.l → P.tabM i = P'.tabM i
  tabZ : ∀ i, i < 2 ^ σ.h * σ.Z.l → P.tabZ i = P'.tabZ i
  tM : ∀ b q, b < 2 ^ (σ.h + σ.g) → q < σ.C.r → P.tM b q = P'.tM b q
  tZ : ∀ b q, b < 2 ^ σ.h → q < σ.Z.r → P.tZ b q = P'.tZ b q
  fM : ∀ b i, b < 2 ^ σ.h → i < σ.Z.l → P.fM b i = P'.fM b i
  fT : ∀ b q, b < 2 ^ σ.h → q < σ.Z.r → P.fT b q = P'.fT b q
  sM : last = true → ∀ i, i < σ.C.l → P.sM i = P'.sM i
  sT : last = true → ∀ q, q < σ.C.r → P.sT q = P'.sT q

theorem PSame.refl (σ : Sg) (last : Bool) (P : PS) : PSame σ last P P :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem idx_lt {r k j l : ℕ} (hr : r < k) (hj : j < l) : r + k * j < k * l :=
  calc r + k * j < k + k * j := by omega
    _ = k * (j + 1) := by ring
    _ ≤ k * l := Nat.mul_le_mul_left k hj

variable {σ : Sg} {last : Bool} {P P' : PS}

theorem PSame.mu (h : PSame σ last P P') : μOf σ P = μOf σ P' := by
  funext x
  rcases x with x | x
  · exact h.tabM _ (idx_lt (rowNo_lt x.1) x.2.isLt)
  · exact h.tabZ _ (idx_lt (rowNo_lt x.1) x.2.isLt)

theorem PSame.rho (h : PSame σ last P P') : ρOf σ P = ρOf σ P' := by
  funext x
  rcases x with x | x
  · exact h.tM _ _ (rowNo_lt x.1) x.2.isLt
  · exact h.tZ _ _ (rowNo_lt x.1) x.2.isLt

theorem PSame.phi (h : PSame σ last P P') : φOf σ P = φOf σ P' :=
  funext fun x => h.fM _ _ (rowNo_lt x.1) x.2.isLt

theorem PSame.psi (h : PSame σ last P P') : ψOf σ P = ψOf σ P' :=
  funext fun x => h.fT _ _ (rowNo_lt x.1) x.2.isLt

/-! ## 2 The values of `BCoins` inside the sizes -/

/-- The values `fr j` and `new j` of one switch agree inside the sizes. σ: the sizes before the
switch; σ': after it. last: the stage after it is the last. -/
structure SwSame (σ σ' : Sg) (last : Bool) (fr fr' : ℕ → GE) (new new' : PS) : Prop where
  fr : ∀ i, carriedN σ ≤ i → i < 2 ^ σ'.h * σ'.Z.l → fr i = fr' i
  tM : ∀ b q, b < 2 ^ (σ'.h + σ'.g) → q < σ'.C.r → new.tM b q = new'.tM b q
  tZ : ∀ b q, b < 2 ^ σ'.h → q < σ'.Z.r → new.tZ b q = new'.tZ b q
  fT : ∀ b q, b < 2 ^ σ'.h → q < σ'.Z.r → new.fT b q = new'.fT b q
  fM : last = true → ∀ b i, b < 2 ^ σ'.h → i < σ'.Z.l → new.fM b i = new'.fM b i
  sM : last = true → ∀ i, i < σ'.C.l → new.sM i = new'.sM i
  sT : last = true → ∀ q, q < σ'.C.r → new.sT q = new'.sT q

/-- The same along the stages, from switch number j on: `SwSame` at each switch; each later fold's
coefficients (`W`) at its own stage's sizes. -/
def KSame (K K' : BCoins) : Fmt.M1.Stage → List Fmt.M1.Stage → ℕ → Prop
  | _, [], _ => True
  | cur, next :: rest, j =>
    SwSame (sgOf cur) (sgOf next) rest.isEmpty (K.fr j) (K'.fr j) (K.new j) (K'.new j) ∧
      (rest.isEmpty = false → K.W (sgOf next) (j + 1) = K'.W (sgOf next) (j + 1)) ∧
      KSame K K' next rest (j + 1)

/-! ## 3 Piece by piece -/

theorem gMask_same (s : Sg) (μ' : s.cMid.J → GE) (tl : s.cMid.Q → GE) (fr fr' : ℕ → GE) (i : ℕ)
    (h : carriedN s ≤ i → fr i = fr' i) : gMask s μ' tl fr i = gMask s μ' tl fr' i := by
  unfold gMask
  split_ifs with h1 h2 h3 h4 h5
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · refine h ?_
    unfold carriedN
    omega

section Stage
variable (p : P12) {K K' : BCoins} (lst : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (o : ℕ)
  (D : ℕ → Fmt.Drawn)

/-- The states after a switch (`aNext`) meet `PSame` at the next stage's sizes. -/
theorem next_same {b : Bool} (hP : PSame (sgOf cur) b P P')
    (hS : SwSame (sgOf cur) (sgOf next) lst (K.fr j) (K'.fr j) (K.new j) (K'.new j))
    (hW : lst = false → K.W (sgOf next) (j + 1) = K'.W (sgOf next) (j + 1)) :
    PSame (sgOf next) lst (aNext K lst j cur next o P D) (aNext K' lst j cur next o P' D) := by
  unfold aNext nextPS
  rw [hP.mu, hP.rho, hP.phi, hP.psi]
  cases lst with
  | true =>
    exact ⟨fun _ _ => rfl, fun i hi => gMask_same _ _ _ _ _ i fun hc => hS.fr i hc hi, hS.tM, hS.tZ,
      hS.fM rfl, hS.fT, fun _ => hS.sM rfl, fun _ => hS.sT rfl⟩
  | false =>
    refine ⟨fun _ _ => rfl, fun i hi => gMask_same _ _ _ _ _ i fun hc => hS.fr i hc hi, hS.tM,
      hS.tZ, fun b i _ _ => ?_, hS.fT, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
    show packedN (sgOf next) (K.W (sgOf next) (j + 1)) b i =
      packedN (sgOf next) (K'.W (sgOf next) (j + 1)) b i
    rw [hW rfl]

/-- The written column of the tree that a switch sends. `aCol` is the same at Q and Q'. -/
theorem col_same {Q Q' : PS} (h : PSame (sgOf next) lst Q Q') :
    aCol lst next Q = aCol lst next Q' := by
  funext x
  unfold aCol
  cases lst with
  | true =>
    show lastCol (sgOf next) Q x = lastCol (sgOf next) Q' x
    unfold lastCol
    rw [h.mu]
    refine congrArg words12 (baseColW_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x ?_ ?_ ?_ ?_)
    · exact symG_congr _ _ _ _ _ _ (fun _ _ => rfl) fun q hq => h.tM 0 q (Nat.two_pow_pos _) hq
    · exact symG_congr _ _ _ _ _ _ (h.sM rfl) (h.sT rfl)
    · exact symG_congr _ _ _ _ _ _ (fun _ _ => rfl) fun q hq => h.tZ 0 q (Nat.two_pow_pos _) hq
    · exact symG_congr _ _ _ _ _ _ (fun i hi => h.fM 0 i (Nat.two_pow_pos _) hi)
        fun q hq => h.fT 0 q (Nat.two_pow_pos _) hq
  | false =>
    show stageColW (sgOf next) Q.tabM Q.tabZ Q.tM Q.tZ Q.fM Q.fT x =
      stageColW (sgOf next) Q'.tabM Q'.tabZ Q'.tM Q'.tZ Q'.fM Q'.fT x
    refine stageColW_congr _ _ _ _ _ _ _ _ _ _ _ _ _ x (fun b hb => ?_) (fun b hb => ?_)
      fun b hb => ?_
    · exact symG_congr _ _ _ _ _ _ (fun i hi => h.tabM _ (idx_lt hb hi)) fun q hq => h.tM b q hb hq
    · exact symG_congr _ _ _ _ _ _ (fun i hi => h.tabZ _ (idx_lt hb hi)) fun q hq => h.tZ b q hb hq
    · exact symG_congr _ _ _ _ _ _ (fun i hi => h.fM b i hb hi) fun q hq => h.fT b q hb hq

end Stage

/-- The last stage: `lastAll` is the same at P and P'. -/
theorem last_same (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (o : ℕ) (t : T12) (trees : List Tree)
    (D : ℕ → Fmt.Drawn) (h : PSame (sgOf cur) true P P') :
    lastAll p j cur o t P trees D = lastAll p j cur o t P' trees D := by
  have h0 : (0 : ℕ) < 2 ^ ((sgOf cur).h + (sgOf cur).g) := Nat.two_pow_pos _
  have h1 : (0 : ℕ) < 2 ^ (sgOf cur).h := Nat.two_pow_pos _
  unfold lastAll lastOut tauSW shownAll
  simp only
  rw [h.mu, formG_congr _ _ P.sM P'.sM (h.sM rfl),
    formG_congr _ _ (P.fM 0) (P'.fM 0) fun i hi => h.fM 0 i h1 hi,
    wr_congr (sgOf cur).C.l _ _ fun i hi => by rw [h.sM rfl i hi],
    wr_congr (sgOf cur).Z.l _ _ fun i hi => by rw [h.fM 0 i h1 hi],
    wr_congr (sgOf cur).C.r _ _ fun q hq => by rw [h.sT rfl q hq, h.tM 0 q h0 hq],
    wr_congr (sgOf cur).Z.r _ _ fun q hq => by rw [h.fT 0 q h1 hq, h.tZ 0 q h1 hq]]

/-! ## 4 The whole text -/

/-- **The text from a stage on** is the same at values of `BCoins` and states that agree inside the
sizes. -/
theorem stagesAll_same (p : P12) {K K' : BCoins} : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P P' : PS) (trees : List Tree)
    (D : ℕ → Fmt.Drawn), KSame K K' cur rest j →
    (rest.isEmpty = false → K.W (sgOf cur) j = K'.W (sgOf cur) j) →
    PSame (sgOf cur) rest.isEmpty P P' →
    stagesAll p K rest j cur l o t P trees D = stagesAll p K' rest j cur l o t P' trees D
  | [], j, cur, _, o, t, _, _, trees, D, _, _, hP => last_same p j cur o t trees D hP
  | next :: rest, j, cur, l, o, t, P, P', trees, D, hK, hW, hP => by
    have hQ := next_same rest.isEmpty j cur next o D hP hK.1 hK.2.1
    unfold stagesAll
    simp only [aFold, hP.mu, hW rfl, col_same rest.isEmpty next hQ, aAns, hQ.mu]
    rw [stagesAll_same p rest (j + 1) next _ _ _ _ _ _ D hK.2.2 hK.2.1 hQ]

/-- The values at the last stage (`stagesEnd`, Sim/Text.lean): the same number, stage, number of the
first round and verifier's state; the prover's states agree inside the sizes. -/
theorem stagesEnd_same (p : P12) {K K' : BCoins} : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P P' : PS) (trees : List Tree)
    (D : ℕ → Fmt.Drawn), KSame K K' cur rest j →
    (rest.isEmpty = false → K.W (sgOf cur) j = K'.W (sgOf cur) j) →
    PSame (sgOf cur) rest.isEmpty P P' →
    ∃ Q Q', PSame (sgOf (stagesEnd p K rest j cur l o t P trees D).cur) true Q Q' ∧
      stagesEnd p K rest j cur l o t P trees D =
        { stagesEnd p K rest j cur l o t P trees D with P := Q } ∧
      stagesEnd p K' rest j cur l o t P' trees D =
        { stagesEnd p K rest j cur l o t P trees D with P := Q' }
  | [], _, _, _, _, _, P, P', _, _, _, _, hP => ⟨P, P', hP, rfl, rfl⟩
  | next :: rest, j, cur, l, o, t, P, P', trees, D, hK, hW, hP => by
    have hQ := next_same rest.isEmpty j cur next o D hP hK.1 hK.2.1
    have ih := stagesEnd_same p rest (j + 1) next (l.drop (cur.k + 3))
      (o + ((sgOf cur).h + (sgOf cur).g) + 3)
      (aRec3 p rest.isEmpty j cur next l o trees D
        (aRec1 p j cur l t (aFold K j cur o P (rowOf t) D))
        (aSwitch cur o D (aAns p j cur next o D (aRec1 p j cur l t (aFold K j cur o P (rowOf t) D))
          (aNext K rest.isEmpty j cur next o P D))))
      _ _ [((sgOf next).C.a, aCol rest.isEmpty next (aNext K rest.isEmpty j cur next o P D))] D
      hK.2.2 hK.2.1 hQ
    have e : stagesEnd p K' (next :: rest) j cur l o t P' trees D =
        stagesEnd p K' rest (j + 1) next (l.drop (cur.k + 3))
          (o + ((sgOf cur).h + (sgOf cur).g) + 3)
          (aRec3 p rest.isEmpty j cur next l o trees D
            (aRec1 p j cur l t (aFold K j cur o P (rowOf t) D))
            (aSwitch cur o D (aAns p j cur next o D
              (aRec1 p j cur l t (aFold K j cur o P (rowOf t) D))
              (aNext K rest.isEmpty j cur next o P D))))
          (aNext K' rest.isEmpty j cur next o P' D)
          [((sgOf next).C.a, aCol rest.isEmpty next (aNext K rest.isEmpty j cur next o P D))]
          D := by
      conv_lhs => unfold stagesEnd
      simp only [aFold, hP.mu, hW rfl, col_same rest.isEmpty next hQ, aAns, hQ.mu]
    rw [e]
    exact ih

/-! ## 5 From the first switch on -/

/-- **The text from the first switch on** (`restText`, Sim/Text.lean) is the same. No hypothesis is
on the first fold's coefficients. -/
theorem restText_same (p : P12) {K K' : BCoins} (cur next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (l : Laid) (o : ℕ) (t₁ : T12) (P P' : PS) (trees : List Tree)
    (D : ℕ → Fmt.Drawn) (hK : KSame K K' cur (next :: rest) 0) (hP : PSame (sgOf cur) false P P') :
    restText p K cur next rest l o t₁ P trees D =
      restText p K' cur next rest l o t₁ P' trees D := by
  have hQ := next_same rest.isEmpty 0 cur next o D hP hK.1 hK.2.1
  unfold restText
  simp only [col_same rest.isEmpty next hQ, aAns, hQ.mu]
  rw [stagesAll_same p rest 1 next _ _ _ _ _ _ D hK.2.2 hK.2.1 hQ]

theorem restEnd_same (p : P12) {K K' : BCoins} (cur next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (l : Laid) (o : ℕ) (t₁ : T12) (P P' : PS) (trees : List Tree)
    (D : ℕ → Fmt.Drawn) (hK : KSame K K' cur (next :: rest) 0) (hP : PSame (sgOf cur) false P P') :
    ∃ Q Q', PSame (sgOf (restEnd p K cur next rest l o t₁ P trees D).cur) true Q Q' ∧
      restEnd p K cur next rest l o t₁ P trees D =
        { restEnd p K cur next rest l o t₁ P trees D with P := Q } ∧
      restEnd p K' cur next rest l o t₁ P' trees D =
        { restEnd p K cur next rest l o t₁ P trees D with P := Q' } := by
  have hQ := next_same rest.isEmpty 0 cur next o D hP hK.1 hK.2.1
  have ih := stagesEnd_same p rest 1 next (l.drop (cur.k + 3))
    (o + ((sgOf cur).h + (sgOf cur).g) + 3)
    (aRec3 p rest.isEmpty 0 cur next l o trees D t₁
      (aSwitch cur o D (aAns p 0 cur next o D t₁ (aNext K rest.isEmpty 0 cur next o P D))))
    _ _ [((sgOf next).C.a, aCol rest.isEmpty next (aNext K rest.isEmpty 0 cur next o P D))] D
    hK.2.2 hK.2.1 hQ
  have e : restEnd p K' cur next rest l o t₁ P' trees D =
      stagesEnd p K' rest 1 next (l.drop (cur.k + 3)) (o + ((sgOf cur).h + (sgOf cur).g) + 3)
        (aRec3 p rest.isEmpty 0 cur next l o trees D t₁
          (aSwitch cur o D (aAns p 0 cur next o D t₁ (aNext K rest.isEmpty 0 cur next o P D))))
        (aNext K' rest.isEmpty 0 cur next o P' D)
        [((sgOf next).C.a, aCol rest.isEmpty next (aNext K rest.isEmpty 0 cur next o P D))] D := by
    unfold restEnd
    simp only [col_same rest.isEmpty next hQ, aAns, hQ.mu]
  rw [e]
  exact ih

/-- The element that is laid anew reads the last state inside the sizes alone. The element is
`tauSim` (Sim/Sims.lean). -/
theorem tauSim_same (p : P12) (e : EndAt) (Q Q' : PS) (h : PSame (sgOf e.cur) true Q Q')
    (D : ℕ → Fmt.Drawn) : tauSim p { e with P := Q } D = tauSim p { e with P := Q' } D := by
  unfold tauSim tauSW claimAtEnd
  simp only
  rw [h.mu, formG_congr _ _ _ _ fun i hi => by rw [h.sM rfl i hi],
    formG_congr (sgOf e.cur).Z.l _ _ _ fun i hi => by rw [h.fM 0 i (Nat.two_pow_pos _) hi]]

/-- **The text at rows 0 with the one item laid anew.** It is `zeroTextK` (Sim/Sims.lean), and it is
the same at K and K'. -/
theorem zeroTextK_same (p : P12) {K K' : BCoins} (s next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (l : Laid) (t₁ : T12) (trees : List Tree) (D : ℕ → Fmt.Drawn)
    (hK : KSame K K' s (next :: rest) 0) :
    zeroTextK p K s next rest l t₁ trees D = zeroTextK p K' s next rest l t₁ trees D := by
  obtain ⟨Q, Q', hQ, e1, e2⟩ := restEnd_same p s next rest l 1 t₁ zeroPS zeroPS trees D hK
    (PSame.refl _ _ _)
  unfold zeroTextK
  rw [← restText_same p s next rest l 1 t₁ zeroPS zeroPS trees D hK (PSame.refl _ _ _), e2]
  conv_lhs => rw [e1]
  simp only
  rw [tauSim_same p _ Q Q' hQ D]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.PSame.refl
#print axioms ProofFile.Honest.K12.idx_lt
#print axioms ProofFile.Honest.K12.PSame.mu
#print axioms ProofFile.Honest.K12.PSame.rho
#print axioms ProofFile.Honest.K12.PSame.phi
#print axioms ProofFile.Honest.K12.PSame.psi
#print axioms ProofFile.Honest.K12.gMask_same
#print axioms ProofFile.Honest.K12.next_same
#print axioms ProofFile.Honest.K12.col_same
#print axioms ProofFile.Honest.K12.last_same
#print axioms ProofFile.Honest.K12.stagesAll_same
#print axioms ProofFile.Honest.K12.stagesEnd_same
#print axioms ProofFile.Honest.K12.restText_same
#print axioms ProofFile.Honest.K12.restEnd_same
#print axioms ProofFile.Honest.K12.tauSim_same
#print axioms ProofFile.Honest.K12.zeroTextK_same
#print axioms ProofFile.Honest.K12.PSame
#print axioms ProofFile.Honest.K12.SwSame
#print axioms ProofFile.Honest.K12.KSame
