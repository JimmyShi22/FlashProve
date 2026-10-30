-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/Bridge.lean: two readers of a proximity test's coins from the
first switch on give the same values inside the stages' sizes. A reader is here a definition that
makes a `BCoins` (Johnson/Prover/Link/BodyAll.lean): the random values, as functions of numbers,
that `bodyAll` (same file) and `stagesAll` (Johnson/Desc/K12/Honest/Stages.lean) take as a
parameter. One reads numbered coins (`coinsOf`, Johnson/Desc/ProofFile/Honest/K12/Coins.lean); the
other a finite type, field by field (`BodyK`, Johnson/Prover/Link/LinkCoin.lean). `toBody` reads a
value of the finite type off numbered coins, and `bridge_same` compares what the two readers then
give. General in the list of stages, in the coins and in the switch at which the comparison starts.
Definitions, and equations between functions of numbers.

In the list: a stage is a `Fmt.M1.Stage`, and its sizes are `sgOf` of it
(Johnson/Desc/K12/Law/ChainOf.lean). Switch number j, counted from 0, is the code switch out of
stage number j of the list into stage number j + 1; cur and next are these two stages. c gives the
coins of all switches by number, elements of the extension field; hide gives the first fold's
coefficients. The second reader is `bodyFr`, `bodyNew` and `bodyW` (LinkCoin.lean): they make the
three fields `fr`, `new` and `W` of a `BCoins` from a value of `BodyK`. "Inside the sizes" is: at
the indices that `SwSame` (Sim/Reads.lean) names for `fr j` and for the fields of `new j`; the sizes
of cur and next bound them.

  `bridge_same`: under the three hypotheses below, `coinsOf stages hide c` and K' agree inside the
    sizes from switch number j on (`KSame`, Sim/Reads.lean): at each switch by `SwSame`, and in each
    later fold's coefficients at that fold's own stage's sizes
  `hideAt_eq`: the first reader's order of a hiding polynomial's coefficients is the second's
    (`wNo`, Johnson/Prover/Link/LinkCoinNo.lean). In Lean: `hideAt k c x = c (wNo k x)`, at every k
  `byName_eq`: the same for `byName` (Coins.lean) at the last k + 1 of k + 1 + a variables: the
    index x reads coin number 2 a + `wNo (k + 1) x`
  `toBody`: a definition: a value of `BodyK GE cur rest`, read off numbered coins from a number on,
    in the first reader's order. For each switch: `swOf`; then `rideOf` where a fold follows, and
    `wordOf` at the last switch
  `swOf`, `rideOf`, `wordOf`: definitions: the parts of that value, each from its first coin on: a
    `SwK`, a `RideK`, a `WordK` (LinkCoin.lean)
  `rideAt`: a definition: the number of the first coin that `rideOf` or `wordOf` reads at a switch
    whose first coin has the number off
  `startOf`: a definition: the number of the first coin of switch number j: the field `main` of
    `marksAt stages j` (Coins.lean)
  `startAt_zero`, `startAt_succ`, `startOf_succ`: where a switch's coins begin: switch number 0 at
    coin number 0; where `stages.drop j = cur :: next :: tl`, switch number j + 1 begins
    `dueSwitch cur next tl.isEmpty` coins after switch number j
  `marks_at`: where `stages.drop j = cur :: next :: tl`: the list has cur at j and next at j + 1, it
    has j + 2 + `tl.length` stages, and the four numbers of `marksAt stages j` are written out from
    `startOf stages j`; the fourth is `rideAt cur next (startOf stages j)`
  `free_in`: for `carriedN (sgOf cur)` ≤ i < 2 ^ h * Z.l, with h and Z those of `sgOf next`:
    `freeAt (swOf cur next off c) i` is `c (off + 2 ^ next.k * next.C.r + (i - carriedIn cur))`
  `sw_last`, `sw_mid`: `SwSame` at one switch: at the last, where next.h = 0; at one after which a
    fold follows
  `w_mid`: both readers give the same coefficients for the fold after such a switch, at the sizes of
    next
  `at2_in`, `onNat_in`: below the sizes, `at2` (LinkCoin.lean) and `onNat`
    (Johnson/Top/H/SwitchMaps.lean) give the finite function's value

By what. `byName_eq` goes by recursion on k and unfolds `byName` and `wNo`; `hideAt_eq` is its case
a = 0. `free_in` unfolds `freeAt` (LinkCoin.lean) and calls `onNat_in`. `sw_last` and `sw_mid`
unfold `coinsOf` and `bodyNew` and rewrite by `marks_at`, `free_in`, `at2_in` and, at the last
switch, `onNat_in`. `w_mid` unfolds `coinsOf` and `bodyW` and rewrites by `marks_at`, `hideAt_eq`
and `castW_self` (Johnson/LinkSim/AtText/CoinsAdd.lean). `bridge_same` goes by recursion along rest:
`sw_last` at the last switch, `sw_mid` and `w_mid` at every other, and for the step `startOf_succ`
and `laid_tail` (Johnson/LinkSim/AtText/CoinsPlaces.lean).

Hypotheses of `bridge_same`. First: `stages.drop j = cur :: rest`: cur is stage number j of the
list, and rest the stages after it. Second: the last stage of `cur :: rest` has h = 0. Third:
`LaidFrom` (CoinsPlaces.lean) at `toBody cur rest (startOf stages j) c`, j and K': from switch
number j on, K' equals what the second reader makes from that value (`W`: from number j + 1 on).

Limits. Where the last stage has h = 0: `bridge_same` and `sw_last` have that hypothesis. At the
last switch `bodyNew` gives 0 at every row of `fM` and `fT` but row 0, and `coinsOf` gives row 0's
values at every row; with h = 0 row 0 is the only row inside the sizes. That the map from numbered
coins to the finite type is one to one and onto is not here. Outside the sizes nothing is stated.
`SwSame` has no clause on `tabM` and `tabZ` of `new j`, and none on `fM`, `sM` and `sT` at a switch
that is not the last. `KSame` compares `W` from number j + 1 on: the coefficients of fold number j,
at j = 0 those that hide gives, are not compared. At an empty rest `KSame` is `True`. No hypothesis
compares h and k of a stage: the coins' numbers are computed from k, the sizes from h + (k - h). No
property is claimed; nothing here speaks of a law or of a simulator. Nothing on completeness or on
soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.Reads
import Johnson.LinkSim.AtText.CoinsPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open Johnson.Top.H (onNat)
open H2K.Pub (sgOf)
open OnBytes.LinkSim.AtText (carriedN LaidFrom laid_tail castW_self)

/-! ## 1 The order of a hiding polynomial's coefficients -/

theorem byName_eq (c : ℕ → GE) : ∀ (k a : ℕ) (x : HIdx (sVars GE 2 (k + 1))),
    byName (k + 1)
        (fun l t => c (if l + a < k + 1 + a then 2 * (l + a - 1) + (t - 1) else 2 * (k + a) + t))
        (c (2 * (k + a))) x =
      c (2 * a + wNo (k + 1) x)
  | 0, a, .inl t => by
    show c (if 1 + a < 0 + 1 + a then _ else 2 * (0 + a) + (t.val + 1)) = c (2 * a + (1 + t.val))
    rw [if_neg (by omega)]
    congr 1
    omega
  | 0, a, .inr _ => by
    show c (2 * (0 + a)) = c (2 * a + 0)
    congr 1
    omega
  | k + 1, a, .inl t => by
    show c (if 1 + a < k + 1 + 1 + a then 2 * (1 + a - 1) + (t.val + 1 - 1) else _) =
      c (2 * a + t.val)
    rw [if_pos (by omega)]
    congr 1
    omega
  | k + 1, a, .inr y => by
    have ih := byName_eq c k (a + 1) y
    show byName (k + 1) (fun l t => c (if l + 1 + a < k + 1 + 1 + a then
      2 * (l + 1 + a - 1) + (t - 1) else 2 * (k + 1 + a) + t)) (c (2 * (k + 1 + a))) y =
      c (2 * a + (2 + wNo (k + 1) y))
    have e1 : (fun l t => c (if l + 1 + a < k + 1 + 1 + a then
        2 * (l + 1 + a - 1) + (t - 1) else 2 * (k + 1 + a) + t)) =
        fun l t => c (if l + (a + 1) < k + 1 + (a + 1) then
          2 * (l + (a + 1) - 1) + (t - 1) else 2 * (k + (a + 1)) + t) := by
      funext l t
      congr 1
      split_ifs <;> omega
    rw [e1, show 2 * (k + 1 + a) = 2 * (k + (a + 1)) by omega, ih]
    congr 1
    omega

/-- **One order of the coefficients**: `hideAt k c` at the index x is coin number `wNo k x`. -/
theorem hideAt_eq (c : ℕ → GE) : ∀ (k : ℕ) (x : HIdx (sVars GE 2 k)), hideAt k c x = c (wNo k x)
  | 0, _ => rfl
  | k + 1, x => by
    have h := byName_eq c k 0 x
    simp only [Nat.add_zero, Nat.mul_zero, Nat.zero_add] at h
    unfold hideAt
    simp only [Nat.add_sub_cancel]
    exact h

/-! ## 2 A value of the finite type, read off numbered coins -/

/-- The message that a switch sends. off: its first coin. -/
def swOf (cur next : Fmt.M1.Stage) (off : ℕ) (c : ℕ → GE) : SwK GE (sgOf cur) (sgOf next) :=
  ⟨fun b q => c (off + b.val * next.C.r + q.val),
    fun i => c (off + 2 ^ next.k * next.C.r + i.val),
    fun b q => c (off + 2 ^ next.k * next.C.r + freeRoom cur next + b.val * next.Z.r + q.val)⟩

/-- The first coin of what goes with a switch's message. -/
def rideAt (cur next : Fmt.M1.Stage) (off : ℕ) : ℕ :=
  off + 2 ^ next.k * next.C.r + freeRoom cur next + 2 ^ next.h * next.Z.r

/-- The next fold's fresh table. off: its first coin. -/
def rideOf (next : Fmt.M1.Stage) (off : ℕ) (c : ℕ → GE) : RideK GE (sgOf next) :=
  ⟨fun n => c (off + n.val), fun b q => c (off + (2 * next.k + 1) + b.val * next.Z.r + q.val)⟩

/-- The masking word. off: its first coin. -/
def wordOf (next : Fmt.M1.Stage) (off : ℕ) (c : ℕ → GE) : WordK GE (sgOf next) :=
  ⟨fun q => c (off + q.val), fun i => c (off + next.C.r + i.val),
    fun i => c (off + next.C.r + next.C.l + i.val),
    fun q => c (off + next.C.r + next.C.l + next.Z.l + q.val)⟩

/-- A value of `BodyK`, read off the coins c along the stages. off: the first switch's first coin.
-/
def toBody : (cur : Fmt.M1.Stage) → (rest : List Fmt.M1.Stage) → ℕ → (ℕ → GE) → BodyK GE cur rest
  | _, [], _, _ => ()
  | cur, [next], off, c => (swOf cur next off c, wordOf next (rideAt cur next off) c)
  | cur, next :: n₂ :: rest, off, c =>
    (swOf cur next off c, rideOf next (rideAt cur next off) c,
      toBody next (n₂ :: rest) (off + dueSwitch cur next false) c)

/-! ## 3 Where a switch's coins begin -/

theorem startAt_zero (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) : startAt s rest 0 = 0 := by
  cases rest <;> rfl

theorem startAt_succ : ∀ (s : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur next : Fmt.M1.Stage) (tl : List Fmt.M1.Stage), (s :: rest).drop j = cur :: next :: tl →
    startAt s rest (j + 1) = startAt s rest j + dueSwitch cur next tl.isEmpty
  | _, [], 0, _, _, _, h => by simp at h
  | _, [], _ + 1, _, _, _, h => by simp at h
  | s, n₀ :: r₀, 0, cur, next, tl, h => by
    obtain ⟨rfl, rfl, rfl⟩ : s = cur ∧ n₀ = next ∧ r₀ = tl := by
      simpa using h
    show dueSwitch s n₀ r₀.isEmpty + startAt n₀ r₀ 0 = 0 + dueSwitch s n₀ r₀.isEmpty
    rw [startAt_zero]
    omega
  | s, n₀ :: r₀, j + 1, cur, next, tl, h => by
    have ih := startAt_succ n₀ r₀ j cur next tl h
    show dueSwitch s n₀ r₀.isEmpty + startAt n₀ r₀ (j + 1) =
      dueSwitch s n₀ r₀.isEmpty + startAt n₀ r₀ j + dueSwitch cur next tl.isEmpty
    rw [ih]
    omega

/-- The number of the first coin of switch number j of a list of stages. -/
def startOf (stages : List Fmt.M1.Stage) (j : ℕ) : ℕ := (marksAt stages j).main

/-- The `Marks` of switch number j, written out at the two stages of the list at j and j + 1. -/
theorem marks_at {stages : List Fmt.M1.Stage} {j : ℕ} {cur next : Fmt.M1.Stage}
    {tl : List Fmt.M1.Stage} (h : stages.drop j = cur :: next :: tl) :
    stages.getD j default = cur ∧ stages.getD (j + 1) default = next ∧
      stages.length = j + 2 + tl.length ∧
      marksAt stages j = ⟨startOf stages j, startOf stages j + 2 ^ next.k * next.C.r,
        startOf stages j + 2 ^ next.k * next.C.r + freeRoom cur next,
        rideAt cur next (startOf stages j)⟩ := by
  have h0 : stages.getD j default = cur := by
    have := congrArg (fun l => l.getD 0 default) h
    simpa [List.getD_eq_getElem?_getD, List.getElem?_drop] using this
  have h1 : stages.getD (j + 1) default = next := by
    have := congrArg (fun l => l.getD 1 default) h
    simpa [List.getD_eq_getElem?_getD, List.getElem?_drop] using this
  have h2 : stages.length = j + 2 + tl.length := by
    have := congrArg List.length h
    simp only [List.length_drop, List.length_cons] at this
    omega
  refine ⟨h0, h1, h2, ?_⟩
  unfold startOf rideAt marksAt
  simp only [h0, h1]

theorem startOf_succ {stages : List Fmt.M1.Stage} {j : ℕ} {cur next : Fmt.M1.Stage}
    {tl : List Fmt.M1.Stage} (h : stages.drop j = cur :: next :: tl) :
    startOf stages (j + 1) = startOf stages j + dueSwitch cur next tl.isEmpty := by
  cases stages with
  | nil => simp at h
  | cons s rest => exact startAt_succ s rest j cur next tl h

/-! ## 4 The two readers agree inside the sizes -/

theorem at2_in {m n : ℕ} (f : Fin m → Fin n → GE) {r q : ℕ} (h1 : r < m) (h2 : q < n) :
    at2 f r q = f ⟨r, h1⟩ ⟨q, h2⟩ := dif_pos ⟨h1, h2⟩

theorem onNat_in {n : ℕ} (f : Fin n → GE) {i : ℕ} (h : i < n) : onNat f i = f ⟨i, h⟩ := dif_pos h

/-- The free entries of a switch (`freeAt`), by the coin's number, at an index inside the sizes. -/
theorem free_in (cur next : Fmt.M1.Stage) (off : ℕ) (c : ℕ → GE) {i : ℕ}
    (h1 : carriedN (sgOf cur) ≤ i) (h2 : i < 2 ^ (sgOf next).h * (sgOf next).Z.l) :
    freeAt (swOf cur next off c) i = c (off + 2 ^ next.k * next.C.r + (i - carriedIn cur)) := by
  have h3 : i - maskUsed (sgOf cur) < Fmt.M1.fillOf (sgOf cur).st (sgOf next).st := by
    have e1 : carriedN (sgOf cur) = maskUsed (sgOf cur) := rfl
    have e2 : Fmt.M1.fillOf (sgOf cur).st (sgOf next).st =
        2 ^ (sgOf next).h * (sgOf next).Z.l - maskUsed (sgOf cur) := rfl
    omega
  unfold freeAt
  rw [if_pos (show maskUsed (sgOf cur) ≤ i from h1), onNat_in _ h3]
  rfl

section Switch
variable {stages : List Fmt.M1.Stage} {j : ℕ} {cur next : Fmt.M1.Stage} {tl : List Fmt.M1.Stage}
  (hide c : ℕ → GE)

/-- The two readers agree inside the sizes at the last switch, where the last stage has h = 0. -/
theorem sw_last (h : stages.drop j = [cur, next]) (hz : next.h = 0) :
    SwSame (sgOf cur) (sgOf next) true ((coinsOf stages hide c).fr j)
      (freeAt (swOf cur next (startOf stages j) c)) ((coinsOf stages hide c).new j)
      (bodyNew cur [next] (toBody cur [next] (startOf stages j) c) 0) := by
  obtain ⟨h0, h1, h2, hm⟩ := marks_at h
  have hl : (j + 2 == stages.length) = true := by
    rw [h2]
    simp
  have hb : ∀ b, b < 2 ^ (sgOf next).h → b = 0 := fun b hb => by
    have e : (sgOf next).h = 0 := hz
    rw [e] at hb
    omega
  refine ⟨fun i hi1 hi2 => ?_, fun b q hb' hq => ?_, fun b q hb' hq => ?_, fun b q hb' hq => ?_,
    fun _ b i hb' hi => ?_, fun _ i hi => ?_, fun _ q hq => ?_⟩
  · rw [free_in cur next _ c hi1 hi2]
    show c ((marksAt stages j).free + (i - carriedIn (stages.getD j default))) = _
    rw [hm, h0]
  · show c ((marksAt stages j).main + b * (stages.getD (j + 1) default).C.r + q) =
      at2 (swOf cur next (startOf stages j) c).mainTail b q
    rw [at2_in _ hb' hq, hm, h1]
    rfl
  · show c ((marksAt stages j).mask + b * (stages.getD (j + 1) default).Z.r + q) =
      at2 (swOf cur next (startOf stages j) c).maskTail b q
    rw [at2_in _ hb' hq, hm, h1]
    rfl
  · obtain rfl := hb b hb'
    show (if (j + 2 == stages.length) = true then
      c ((marksAt stages j).ride + (stages.getD (j + 1) default).C.r +
        (stages.getD (j + 1) default).C.l + (stages.getD (j + 1) default).Z.l + q) else _) =
      onNat (wordOf next (rideAt cur next (startOf stages j)) c).maskTail q
    rw [if_pos hl, onNat_in _ hq, hm, h1]
    rfl
  · obtain rfl := hb b hb'
    show (if (j + 2 == stages.length) = true then
      c ((marksAt stages j).ride + (stages.getD (j + 1) default).C.r +
        (stages.getD (j + 1) default).C.l + i) else 0) =
      onNat (wordOf next (rideAt cur next (startOf stages j)) c).mask i
    rw [if_pos hl, onNat_in _ hi, hm, h1]
    rfl
  · show c ((marksAt stages j).ride + (stages.getD (j + 1) default).C.r + i) =
      onNat (wordOf next (rideAt cur next (startOf stages j)) c).main i
    rw [onNat_in _ hi, hm, h1]
    rfl
  · show c ((marksAt stages j).ride + q) =
      onNat (wordOf next (rideAt cur next (startOf stages j)) c).mainTail q
    rw [onNat_in _ hq, hm]
    rfl

/-- The two readers agree inside the sizes at a switch after which a fold follows. -/
theorem sw_mid {n₂ : Fmt.M1.Stage} (h : stages.drop j = cur :: next :: n₂ :: tl) :
    SwSame (sgOf cur) (sgOf next) false ((coinsOf stages hide c).fr j)
      (freeAt (swOf cur next (startOf stages j) c)) ((coinsOf stages hide c).new j)
      (bodyNew cur (next :: n₂ :: tl) (toBody cur (next :: n₂ :: tl) (startOf stages j) c) 0) := by
  obtain ⟨h0, h1, h2, hm⟩ := marks_at h
  have hl : ¬ (j + 2 == stages.length) = true := by
    rw [h2]
    simp
  refine ⟨fun i hi1 hi2 => ?_, fun b q hb' hq => ?_, fun b q hb' hq => ?_, fun b q hb' hq => ?_,
    fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  · rw [free_in cur next _ c hi1 hi2]
    show c ((marksAt stages j).free + (i - carriedIn (stages.getD j default))) = _
    rw [hm, h0]
  · show c ((marksAt stages j).main + b * (stages.getD (j + 1) default).C.r + q) =
      at2 (swOf cur next (startOf stages j) c).mainTail b q
    rw [at2_in _ hb' hq, hm, h1]
    rfl
  · show c ((marksAt stages j).mask + b * (stages.getD (j + 1) default).Z.r + q) =
      at2 (swOf cur next (startOf stages j) c).maskTail b q
    rw [at2_in _ hb' hq, hm, h1]
    rfl
  · show (if (j + 2 == stages.length) = true then _ else
      c ((marksAt stages j).ride + (2 * (stages.getD (j + 1) default).k + 1) +
        b * (stages.getD (j + 1) default).Z.r + q)) =
      at2 (rideOf next (rideAt cur next (startOf stages j)) c).tail b q
    rw [if_neg hl, at2_in _ hb' hq, hm, h1]
    rfl

/-- Both readers give the same coefficients for the fold after such a switch, at its own sizes. -/
theorem w_mid {n₂ : Fmt.M1.Stage} (h : stages.drop j = cur :: next :: n₂ :: tl) :
    (coinsOf stages hide c).W (sgOf next) (j + 1) =
      bodyW cur (next :: n₂ :: tl) (toBody cur (next :: n₂ :: tl) (startOf stages j) c) (sgOf next)
        0 := by
  obtain ⟨-, -, -, hm⟩ := marks_at h
  funext x
  show hideAt ((sgOf next).h + (sgOf next).g)
      (if j + 1 = 0 then hide else fun i => c ((marksAt stages (j + 1 - 1)).ride + i)) x =
    castW (sgOf next) (sgOf next) (rideOf next (rideAt cur next (startOf stages j)) c).W x
  rw [if_neg (by omega), hideAt_eq, castW_self, Nat.add_sub_cancel, hm]
  rfl

end Switch

/-- **The `BCoins` that is read off numbered coins, and any `BCoins` that equals what is made from
the value of the finite type which is read off the same coins, agree inside the sizes.** From switch
number j on, where the last stage has h = 0. -/
theorem bridge_same (stages : List Fmt.M1.Stage) (hide c : ℕ → GE) : ∀ (rest : List Fmt.M1.Stage)
    (cur : Fmt.M1.Stage) (j : ℕ) (K' : BCoins), stages.drop j = cur :: rest →
    (∀ st, (cur :: rest).getLast? = some st → st.h = 0) →
    LaidFrom cur rest (toBody cur rest (startOf stages j) c) j K' →
    KSame (coinsOf stages hide c) K' cur rest j
  | [], _, _, _, _, _, _ => trivial
  | [next], cur, j, K', h, hz, hL => by
    have e1 := hL.1 0
    have e2 := hL.2.1 0
    rw [Nat.add_zero] at e1 e2
    refine ⟨?_, fun h => absurd h (by decide), trivial⟩
    rw [e1, e2]
    exact sw_last hide c h (hz next rfl)
  | next :: n₂ :: rest, cur, j, K', h, hz, hL => by
    have e1 := hL.1 0
    have e2 := hL.2.1 0
    have e3 := hL.2.2 (sgOf next) 0
    rw [Nat.add_zero] at e1 e2 e3
    have hd : stages.drop (j + 1) = next :: n₂ :: rest := by
      have := congrArg (List.drop 1) h
      simpa [List.drop_drop, Nat.add_comm] using this
    refine ⟨?_, fun _ => ?_, bridge_same stages hide c (n₂ :: rest) next (j + 1) K' hd
      (fun st hst => hz st (by simpa using hst)) ?_⟩
    · rw [e1, e2]
      exact sw_mid hide c h
    · rw [e3]
      exact w_mid hide c h
    · rw [startOf_succ h]
      exact laid_tail hL

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.byName_eq
#print axioms ProofFile.Honest.K12.hideAt_eq
#print axioms ProofFile.Honest.K12.startAt_zero
#print axioms ProofFile.Honest.K12.startAt_succ
#print axioms ProofFile.Honest.K12.marks_at
#print axioms ProofFile.Honest.K12.startOf_succ
#print axioms ProofFile.Honest.K12.at2_in
#print axioms ProofFile.Honest.K12.onNat_in
#print axioms ProofFile.Honest.K12.free_in
#print axioms ProofFile.Honest.K12.sw_last
#print axioms ProofFile.Honest.K12.sw_mid
#print axioms ProofFile.Honest.K12.w_mid
#print axioms ProofFile.Honest.K12.bridge_same
#print axioms ProofFile.Honest.K12.swOf
#print axioms ProofFile.Honest.K12.rideAt
#print axioms ProofFile.Honest.K12.rideOf
#print axioms ProofFile.Honest.K12.wordOf
#print axioms ProofFile.Honest.K12.toBody
#print axioms ProofFile.Honest.K12.startOf
