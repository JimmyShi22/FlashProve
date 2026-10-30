-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeAtFull.lean: NINETEEN GUARDS ON THE SHAPE OF THE KEY FILE's FIRST CHAIN, AT A SYNTHETIC
PUBLIC VALUE MADE OF THE LIBRARY's WRITTEN SIZES OF THE FULL SIZE (`keyFull`): THEIR RUN FROM ONE
CLOSED TERM RETURNS ANOTHER: AS A THEOREM, member by member, UNDER TWO NAMED PREMISES. Closed terms,
statements and proofs. Guards on shapes: NOTHING IS SHOWN OF ANY PROVER, and nothing of the
verifier's sub-protocols.

What for. The frame's rule `accepted_of_shape` (Johnson/Desc/ProofFile/Honest/Thread/Shape.lean)
asks one Bool a chain:
`Z.yes a₀ n = true`. Lean's evaluator finds it in seconds; Lean's kernel does not carry the run as
it stands. Here each of the nineteen guards has one theorem "at this term it returns that term",
paid by the kernel where it reduces, by a closed form with a law where an iteration is too deep
(Johnson/Desc/Ground/Shape/TakeMany.lean, E2E/KeyShapeCallerClosed.lean,
E2E/KeyShapeLinkClosed.lean), and by a theorem of the library where a clause on public values does
not reduce (`admitted_full`, `layout_full`).

  `oneF`, `QF`, `sentF`: the synthetic values. `nxt`, `ok_nxt`: what a guard returns, as a term.
  `admF`, `layF`, `blocksF`: three clauses on public values, by the library's theorems.
  `T0` … `T19`: the terms. `step0`, `step1`, `link0`, `link1`, `step14` … `step18`: one theorem a
    guard, or a link.
  `gsF`: the nineteen guards in a row. **`run_full`**: their run from `T0` returns `T19`.
  **`end_full`**: E2E/KeyShapeFirstEnd.lean's `firstEndS` accepts `T19`. `early_rejected`,
    **`one_early`**: negative tests: the seal and `firstEndS` reject `T2`; four more, each one term
      early.
  `run_take`, `run_runL`: the run of the shape of a list of guards is the guards in a row.
  **`yes_full`**: the Bool, at the shape of that list.
  `flat_range`: a function of the numbers alone, over a numbered list.

Limits.
- TWO NAMED PREMISES: at each lookup's place the rounds can be made (`entries.isSome`): a clause of
  that sub-protocol's own test on public values; the kernel did not carry it.
- THE PUBLIC VALUE IS SYNTHETIC, AND NO KEY FILE's PUBLIC VALUES ARE IT. `oneF` is put together
  here: the written sizes' codes, index-mask message, ranges and shape, and the setting's number of
  answers to an OOD sample; all else of the parameter bytes' own fields is empty or a default. The
  lists of groups told at the three sendings and the number of trees sent in front of the batching
  are guesses. What makes the theorems usable at a key file's public values is
  E2E/KeyShapeFullTies.lean: the guards read none of what is made up here.
- That `T0` is the start state's shape is not said here (E2E/KeyShapeFullTies.lean's `start_six`).
- The ranges' place is Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean's `nKRFull`.


-/
import E2E.KeyShapeFirstWhole
import E2E.KeyShapeLinkClosed
import E2E.KeyShapeFirstEnd
import Johnson.Desc.K12.Law.PlaceKeyRangesFull
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.AtFiles.Full
open OnBytes OnBytes.Params AtPublicFiles.AtFiles AtPublicFiles.KeyShape
open Lk6.AtPlan (keyFull keyX)
open H2K.Member (nKRFull)
open ProofFile.Honest (Shape)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.K3 (faceOfLkp)
open VerifiableInference.Desc.Key (FirstState pieces lookupPlace lookupsOf groupsTold rootsBefore
  rootsAt)

/-! ## The written values -/

/-- The one-time chain's public values at the written sizes: synthetic (see Limits). -/
def oneF : OneTime :=
  { given := { bytes := ByteArray.empty, cfg := ByteArray.empty, items := []
               plan := { field := Fmt.Fld.two, salt := 0, nonce := 0, posB := 0
                         samples := keyFull.set.samples, saved := 1, entries := [] } }
    indexMasks := keyFull.once.input, ranges := keyX
    binding := default, codes := CF, lin := SF }

def QF : Pub1 := ⟨oneF, keyFull.set⟩

/-- The trees sent in front of the batching: synthetic. -/
def sentF : Nat := 5

/-- What a guard returns; where it rejects: the shape in front. -/
def nxt (g : Sh₁B → Except String Sh₁B) (a : Sh₁B) : Sh₁B := ((g a).toOption).getD a

theorem ok_nxt {g : Sh₁B → Except String Sh₁B} {a : Sh₁B} (h : (g a).toOption.isSome = true) :
    g a = .ok (nxt g a) := by
  unfold nxt
  cases e : g a with
  | error w => rw [e] at h; cases h
  | ok t => rfl

theorem admF : Wf.admitted CF QF.one.ranges (Wf.matrixOf QF.one.lin) = true :=
  Lk6.AtPlan.admitted_full

theorem layF : Wf.layout QF.one.ranges.lookups
    (QF.one.codes.base.getD QF.one.ranges.message.shape.code default).ell =
    Wf.layFrom (2 ^ Lk6.AtPlan.keyRangesLines.group.logL) 0 0
      [⟨1, 0, 5, 18, 0, 0⟩, ⟨1, 32, 2, 15, 0, 0⟩, ⟨1, 36, 1, 14, 0, 0⟩, ⟨0, 0, 5, 13, 0, 0⟩,
        ⟨1, 38, 0, 13, 0, 0⟩, ⟨0, 32, 3, 11, 0, 0⟩] := Lk6.AtPlan.layout_full

theorem blocksF (i : Nat) (hi : i < 2) : blocksB QF.one i = true := by
  unfold blocksB AtPublicFiles.KeyLookup.blocksOf
  rw [layF]
  match i, hi with
  | 0, _ => decide +kernel
  | 1, _ => decide +kernel

/-! ## The two sendings in front -/

def T0 : Sh₁B := a₀ CF (backOf SF CF ([], #[], #[], none))
def g0 : Sh₁B → Except String Sh₁B := gIdx QF pieces [[]]
def T1 : Sh₁B := nxt g0 T0
theorem step0 : g0 T0 = .ok T1 := ok_nxt (by decide +kernel)

def g1 : Sh₁B → Except String Sh₁B := gMsg QF pieces [[], []]
def T1s : Sh₁B := nxt (gSend (parMsg QF pieces [[], []])) T1
def T2 : Sh₁B := nxt (gOpenA QF true) T1s
theorem step1s : gSend (parMsg QF pieces [[], []]) T1 = .ok T1s := ok_nxt (by decide +kernel)
theorem codes1s : T1s.1.st.codes = CF := by decide +kernel
theorem step1o : gOpen QF T1s = .ok T2 := by
  show gOpenA QF (Wf.admitted T1s.1.st.codes QF.one.ranges (Wf.matrixOf QF.one.lin)) T1s = _
  rw [codes1s, admF]
  exact ok_nxt (by decide +kernel)
theorem step1 : g1 T1 = .ok T2 := by
  show (gSend (parMsg QF pieces [[], []]) T1).bind (gOpen QF) = _
  rw [step1s]
  exact step1o

/-! ## The two links -/

theorem get_some {α : Type} [Inhabited α] (l : List α) (i : Nat) (h : (l[i]?).isSome = true) :
    l[i]? = some ((l[i]?).getD default) := by
  cases e : l[i]? with
  | none => rw [e] at h; cases h
  | some x => rfl

/-- The own message's ledger and the index-mask message's, behind the two sendings. -/
def L1 : Ledger := ((T2.1.st.oracles[1]?).bind (·.ledger)).getD default
def L0 : Ledger := ((T2.1.st.oracles[0]?).bind (·.ledger)).getD default

/-- How many entries of the own message, and of the index-mask message, lookup i's hidden values
get.
-/
def nOwn (i : Nat) : Nat :=
  (faceOfLkp (lookAt QF.one i)).slots - 2 * (faceOfLkp (lookAt QF.one i)).parts.length
def nIdx (i : Nat) : Nat := 2 * (faceOfLkp (lookAt QF.one i)).parts.length

/-- The homes of the hidden values that lookup i's claims on keys name: two a part, of the
index-mask message, in a row. -/
def slF (i : Nat) : List (List Slot) :=
  (List.range 12).map fun p => [⟨0, 24 * i + 2 * p⟩, ⟨0, 24 * i + 2 * p + 1⟩]

def W0 : WfLookup := (QF.one.ranges.lookups[0]?).getD default
def W1 : WfLookup := (QF.one.ranges.lookups[1]?).getD default

theorem step_L1 : InStep L1 0 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem step_L0 : InStep L0 0 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def T8 : Sh₁B := linkT QF 0 T2 L1 0 L0 0 (slF 0)

/-- **The first link.** hes: the rounds of the lookup's place can be made. -/
theorem link0 (hes : (lookupPlace QF.set 0 (lookAt QF.one 0)).entries.isSome = true) :
    runL (gLink QF 0) T2 = .ok T8 :=
  link_closed QF 0 T2 L1 0 L0 0 W0 (slF 0) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) step_L1
    (by decide +kernel) (by decide +kernel) step_L0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hes (by decide +kernel)
    (get_some _ 0 (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (blocksF 0 (by decide)) (by decide +kernel) (by decide +kernel)

/-- The two ledgers behind the first link. -/
def B1 : Ledger := behind L1 0 (nOwn 0)
def B0 : Ledger := behind L0 0 (nIdx 0)

def T14 : Sh₁B := linkT QF 1 T8 B1 (0 + nOwn 0) B0 (0 + nIdx 0) (slF 1)

/-- **The second link.** -/
theorem link1 (hes : (lookupPlace QF.set 1 (lookAt QF.one 1)).entries.isSome = true) :
    runL (gLink QF 1) T8 = .ok T14 :=
  link_closed QF 1 T8 B1 (0 + nOwn 0) B0 (0 + nIdx 0) W1 (slF 1) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (behind_step L1 0 (nOwn 0) step_L1) (by decide +kernel) (by decide +kernel)
    (behind_step L0 0 (nIdx 0) step_L0)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hes (by decide +kernel)
    (get_some _ 1 (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (blocksF 1 (by decide)) (by decide +kernel) (by decide +kernel)

/-! ## Behind the links -/

def T15 : Sh₁B := nxt (gLayRows QF) T14
theorem step14 : gLayRows QF T14 = .ok T15 := ok_nxt (by decide +kernel)

def T16 : Sh₁B := nxt (gRng QF nKRFull) T15
theorem step15 : gRng QF nKRFull T15 = .ok T16 := ok_nxt (by decide +kernel)

def T17 : Sh₁B := nxt (gBattA QF CF true pieces sentF) T16
theorem codes16 : T16.1.st.codes = CF := by decide +kernel
theorem step16 : gBatt QF CF pieces sentF T16 = .ok T17 := by
  show gBattA QF CF (Wf.admitted T16.1.st.codes QF.one.ranges (Wf.matrixOf QF.one.lin)) pieces
    sentF T16 = _
  rw [codes16, admF]
  exact ok_nxt (by decide +kernel)

def T18 : Sh₁B := nxt (gSendW QF pieces [[], []]) T17
theorem step17 : gSendW QF pieces [[], []] T17 = .ok T18 := ok_nxt (by decide +kernel)

def T19 : Sh₁B := nxt gSealB T18
theorem step18 : gSealB T18 = .ok T19 := ok_nxt (by decide +kernel)

/-! ## The run -/

/-- The nineteen guards, in the order of the chain's blocksInOrder list. -/
def gsF : List (Sh₁B → Except String Sh₁B) :=
  g0 :: [g1] ++ (gLink QF 0 ++ gLink QF 1) ++
    [gLayRows QF, gRng QF nKRFull, gBatt QF CF pieces sentF, gSendW QF pieces [[], []]] ++ [gSealB]

/-- **The nineteen guards' run from `T0` returns `T19`**, under the two named premises. -/
theorem run_full (h0 : (lookupPlace QF.set 0 (lookAt QF.one 0)).entries.isSome = true)
    (h1 : (lookupPlace QF.set 1 (lookAt QF.one 1)).entries.isSome = true) :
    runL gsF T0 = .ok T19 := by
  have a : runL (g0 :: [g1]) T0 = .ok T2 := by
    rw [runL_cons _ _ _ _ step0, runL_cons _ _ _ _ step1]
    rfl
  have b : runL (gLink QF 0 ++ gLink QF 1) T2 = .ok T14 := by
    rw [runL_append _ _ _ _ (link0 h0)]
    exact link1 h1
  have c : runL [gLayRows QF, gRng QF nKRFull, gBatt QF CF pieces sentF,
      gSendW QF pieces [[], []]] T14 = .ok T18 := by
    rw [runL_cons _ _ _ _ step14, runL_cons _ _ _ _ step15, runL_cons _ _ _ _ step16,
      runL_cons _ _ _ _ step17]
    rfl
  unfold gsF
  rw [runL_append _ _ _ T18 (by
    rw [runL_append _ _ _ T14 (by rw [runL_append _ _ _ _ a]; exact b)]
    exact c), runL_cons _ _ _ _ step18]
  rfl

/-- **The first chain's part of the file's last test accepts the last term.** -/
theorem end_full : firstEndS QF T19 = true := by decide +kernel

/-- A negative test: the seal rejects the shape behind the two sendings; so does the first chain's
part of the file's last test. -/
theorem early_rejected : (gSealB T2).toOption.isSome = false ∧ firstEndS QF T2 = false :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- **Negative tests, each one term early**: "rng.0.rows" with one lookup through; "w.1.send" in
front of "batt.1.batt"; the seal, and the first chain's part of the file's last test, in front of
"w.1.send": all reject. (The like at the second sending and at "batt.1.batt" did not reduce in
Lean's kernel; at the ranges' test: E2E/KeyShapeFirstMore.lean's `rng_early`.) -/
theorem one_early : (gLayRows QF T8).toOption.isSome = false ∧
    (gSendW QF pieces [[], []] T16).toOption.isSome = false ∧
    (gSealB T17).toOption.isSome = false ∧ firstEndS QF T17 = false :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The run of the shape of a list of guards, over the first n. -/
theorem run_take {S Sh : Type} (sh : S → Sh) (gs : List (Sh → Except String Sh))
    (v : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) (a : Sh) :
    ∀ n, n ≤ gs.length → (ZL sh gs v).run n a = runL (gs.take n) a
  | 0, _ => rfl
  | n + 1, h => by
    have hn : n < gs.length := h
    show ((ZL sh gs v).run n a).bind ((gs[n]?).getD _) = _
    rw [run_take sh gs v a n (Nat.le_of_lt hn), List.getElem?_eq_getElem hn, Option.getD_some,
      List.take_add_one, List.getElem?_eq_getElem hn]
    unfold runL
    rw [List.foldl_append]
    rfl

theorem run_runL {S Sh : Type} (sh : S → Sh) (gs : List (Sh → Except String Sh))
    (v : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) (a : Sh) :
    (ZL sh gs v).run gs.length a = runL gs a := by
  rw [run_take sh gs v a gs.length (Nat.le_refl _), List.take_length]

/-- The Bool of the frame's rule, at the letters made of the list of the nineteen guards (not at the
chain's own letters: E2E/KeyShapeFullTies.lean), under the two named premises. -/
theorem yes_full (v : Nat → FirstState → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (h0 : (lookupPlace QF.set 0 (lookAt QF.one 0)).entries.isSome = true)
    (h1 : (lookupPlace QF.set 1 (lookAt QF.one 1)).entries.isSome = true) :
    (ZL (sh₁B QF CF) gsF v).yes T0 19 = true := by
  show ((ZL (sh₁B QF CF) gsF v).run gsF.length T0).toOption.isSome = true
  rw [run_runL, run_full h0 h1]
  rfl

/-- A function of the numbers alone, over a numbered list. -/
theorem flat_range {α β : Type} (F : Nat → List β) : ∀ (l : List α) (k : Nat),
    (l.zipIdx k).flatMap (fun x => F x.2) = (List.range' k l.length).flatMap F
  | [], _ => rfl
  | _ :: l, k => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.length_cons, List.range'_succ,
      List.flatMap_cons, flat_range F l (k + 1)]

end AtPublicFiles.AtFiles.Full

#print axioms AtPublicFiles.AtFiles.Full.ok_nxt
#print axioms AtPublicFiles.AtFiles.Full.admF
#print axioms AtPublicFiles.AtFiles.Full.layF
#print axioms AtPublicFiles.AtFiles.Full.blocksF
#print axioms AtPublicFiles.AtFiles.Full.step0
#print axioms AtPublicFiles.AtFiles.Full.step1s
#print axioms AtPublicFiles.AtFiles.Full.codes1s
#print axioms AtPublicFiles.AtFiles.Full.step1o
#print axioms AtPublicFiles.AtFiles.Full.step1
#print axioms AtPublicFiles.AtFiles.Full.get_some
#print axioms AtPublicFiles.AtFiles.Full.step_L1
#print axioms AtPublicFiles.AtFiles.Full.step_L0
#print axioms AtPublicFiles.AtFiles.Full.link0
#print axioms AtPublicFiles.AtFiles.Full.link1
#print axioms AtPublicFiles.AtFiles.Full.step14
#print axioms AtPublicFiles.AtFiles.Full.step15
#print axioms AtPublicFiles.AtFiles.Full.codes16
#print axioms AtPublicFiles.AtFiles.Full.step16
#print axioms AtPublicFiles.AtFiles.Full.step17
#print axioms AtPublicFiles.AtFiles.Full.step18
#print axioms AtPublicFiles.AtFiles.Full.run_full
#print axioms AtPublicFiles.AtFiles.Full.end_full
#print axioms AtPublicFiles.AtFiles.Full.early_rejected
#print axioms AtPublicFiles.AtFiles.Full.one_early
#print axioms AtPublicFiles.AtFiles.Full.run_take
#print axioms AtPublicFiles.AtFiles.Full.run_runL
#print axioms AtPublicFiles.AtFiles.Full.yes_full
#print axioms AtPublicFiles.AtFiles.Full.flat_range
