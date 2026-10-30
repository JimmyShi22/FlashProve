-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/WordsAtQ.lean: THE 24 EQUATIONS "READER AND OWNER READ ONE ARRAY" (`OneWord`, `HeadWord`,
Johnson/Goal/Meaning/HidOwn.lean | HidHead.lean) AT THE TOWER'S OWN READING OF A WITNESS (`ownQ`,
CellQ.lean), AT EVERY WITNESS, FROM CONDITIONS ON PUBLIC LETTERS ALONE. What MeansQ.lean's docstring
on `hidAtSeat` names as owed. A JOINING of `words_of_fitF`
(Johnson/Goal/Meaning/HidFamily.lean: the 24 at a FAMILY of readings, under "reader's and owner's
readings agree": `ReadsOne`) with `readAt_agree` (Johnson/Desc/Sound/ReadAt.lean: two segments'
readings of one message agree outside the pads, since all copies of a message share one component of
the witness).
  `PadFree … k k' a`: ON PUBLIC LETTERS: no place that segment k's seats name for its matrix a,
    within its sizes, is a pad's place of segment k's or of segment k''s own copy of that message.
  `agreeAt_readAt`: one seat at the pair (`SeatAt`), the seats named, the groups seated and
    `PadFree` give
    `AgreeAt` at the two segments' readings of ANY witness.
  `PadsFree`: `PadFree` at the 24 pairs. `readsOne_readAt`: then `ReadsOne` at fun k => readAt … k
  w. **`words_ownQ`**: with the test on sizes: `OneWord X (ownQ … w) ∧ HeadWord X (ownQ … w)`, for
every w. Limits. `SeatsOne`, `sizesFit`, `PadsFree`, `SeatsNamed`, `GroupsSeated` are conditions on
the plan's letters: met at no plan here; `PadsFree` has no test with code yet. The full size alone
(HidFamily.lean's 24 pairs). Limits: that file's. A joining of rules: no member is known. Nothing on
hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Meaning.HidFamily
import Johnson.P5J.CellQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road
open OnBytes.Model.Layer (matIx)
open Cb.Pv.Tail (Size)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (readAt readAt_agree OffPad SeatsNamed GroupsSeated MsgT Mem)

variable {Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers)
  (s : ℕ → Size) (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)

/-- No place that segment k's seats name for its matrix a is a pad's place of k's or of k''s own
copy. -/
def PadFree (k k' a : ℕ) : Prop :=
  ∀ (h : a < (s k).NM), ∀ i < Alg.symRows ((s k).m a), ∀ c < (s k).k a,
    OffPad cs arr ms N k (seat k ⟨a, h⟩ i c).1 (seat k ⟨a, h⟩ i c).2.1 (seat k ⟨a, h⟩ i c).2.2 ∧
      OffPad cs arr ms N k' (seat k ⟨a, h⟩ i c).1 (seat k ⟨a, h⟩ i c).2.1 (seat k ⟨a, h⟩ i c).2.2

/-- **At one pair the two segments' readings of any witness agree.** hs: the owner's entry has the
reader's sizes (the test on sizes gives it). -/
theorem agreeAt_readAt (k k' a a' : ℕ) (o : SeatAt (s k) (s k') (seat k) (seat k') a a')
    (hs : ∀ (_ : a < (s k).NM) (_ : a' < (s k').NM),
      (s k').m a' = (s k).m a ∧ (s k').k a' = (s k).k a)
    (hN : SeatsNamed arr N s seat) (hG : GroupsSeated ms N) (hP : PadFree cs arr ms N s seat k k' a)
    (w : Wit Cells Tok MsgT) :
    AgreeAt (s k) (s k') (seat k) (seat k') (readAt cs arr ms N k w) (readAt cs arr ms N k' w) a
      a' := by
  intro h h' i hi c hc
  have e := o h h' i hi c hc
  have n1 := hN k ⟨a, h⟩ i c hi hc
  have n2 := hN k' ⟨a', h'⟩ i c (by rw [(hs h h').1]; exact hi) (by rw [(hs h h').2]; exact hc)
  rw [← e] at n2 ⊢
  exact readAt_agree cs arr ms N k k' _ _ _ w n1 n2 hG (hP h i hi c hc).1 (hP h i hi c hc).2

/-- `PadFree` at the 24 pairs. -/
structure PadsFree (X : Model.Verify.Public) : Prop where
  ff : ∀ g, 0 < g → g < 12 → PadFree cs arr ms N s seat (2 * g) (2 * (g - 1)) (matIx X.y).iXI
  att : ∀ g < 12, PadFree cs arr ms N s seat (2 * g + 1) (2 * g) ((Hd.shapeA X g).cf.NAs + 3)
  head : PadFree cs arr ms N s seat 24 22 (X.hS.NHf + 3)

/-- The test on sizes at a pair: the owner's entry has the reader's rows and columns. -/
theorem sizes_of_sizeAt {t t' : Size} {a a' : ℕ} (f : sizeAt t t' a a' = true) :
    t'.m a' = t.m a ∧ t'.k a' = t.k a := by
  unfold sizeAt at f
  simp only [Bool.and_eq_true, decide_eq_true_eq] at f
  exact ⟨f.1.1.1.2.symm, f.1.1.2.symm⟩

variable {cs arr ms N s seat}

/-- **Reader's and owner's readings of any witness agree, at the 24 pairs.** -/
theorem readsOne_readAt {X : Model.Verify.Public} (f : sizesFit X s = true)
    (o : SeatsOne X s seat) (hN : SeatsNamed arr N s seat) (hG : GroupsSeated ms N)
    (hP : PadsFree cs arr ms N s seat X) (w : Wit Cells Tok MsgT) :
    ReadsOne X s seat fun k => readAt cs arr ms N k w := by
  obtain ⟨fa, fb⟩ := sizes_of_fit f
  have fc : sizeAt (s 24) (s 22) (X.hS.NHf + 3) (matIx X.y).iXO = true := by
    unfold sizesFit at f
    rw [Bool.and_eq_true] at f
    exact f.2
  exact ⟨fun g h0 hg => agreeAt_readAt cs arr ms N s seat _ _ _ _ (o.ff g h0 hg)
      (fun _ _ => sizes_of_sizeAt (fa g h0 hg)) hN hG (hP.ff g h0 hg) w,
    fun g hg => agreeAt_readAt cs arr ms N s seat _ _ _ _ (o.att g hg)
      (fun _ _ => sizes_of_sizeAt (fb g hg)) hN hG (hP.att g hg) w,
    agreeAt_readAt cs arr ms N s seat _ _ _ _ o.head (fun _ _ => sizes_of_sizeAt fc) hN hG hP.head
      w⟩

/-- **THE 24 EQUATIONS AT THE TOWER's OWN READING, AT EVERY WITNESS.** -/
theorem words_ownQ {X : Model.Verify.Public} (f : sizesFit X s = true) (o : SeatsOne X s seat)
    (hN : SeatsNamed arr N s seat) (hG : GroupsSeated ms N) (hP : PadsFree cs arr ms N s seat X)
    (w : Wit Cells Tok MsgT) :
    OneWord X (ownQ cs arr ms N s seat w) ∧ HeadWord X (ownQ cs arr ms N s seat w) :=
  words_of_fitF f (readsOne_readAt f o hN hG hP w)

end P5J

#print axioms P5J.agreeAt_readAt
#print axioms P5J.readsOne_readAt
#print axioms P5J.words_ownQ
