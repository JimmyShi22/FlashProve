-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/HidesOfEight.lean: THE OUTPUT HEAD'S OWN ROUNDS: WHERE THE
VERIFIER'S ONE HEARING RETURNS ON EIGHT PIECES OF THE FORM BELOW, THE STRUCTURE HidesTables
(Johnson/Desc/K6/Honest/TruthOfTables.lean) HOLDS OF THE PROVER'S CELLS, THE MASK ROW, WHAT WAS
HEARD AND THE LEDGER THAT THE HEARING RETURNS. Of its fourteen clauses nine say that a variable of
what was heard is worth, in the world of that ledger and that mask row, a value that the functions
of Johnson/Desc/K6/Honest/Tables.lean compute of the cells; four say that the four sumchecks' own
forms are worth 0; one is on canonical writing.
"Hides" in this name is the ledger's word: a slot is worth a value behind a mask entry (said = value
+ mask). It is no claim that anything is hidden from a verifier.
THE EIGHT PIECES. Four are what sumPart says, played ALONE (SumLaw/Terms.lean: alone) at the four
jobs of Honest/K6/Part.lean, each at the state that has heard the challenges in front of it, under
any names of runs. The two rounds of scalars are terms written out in the premise on the hearing.
The two rounds in which nothing is meant to be sent are letters: of the first its challenges alone
are asked, of the second its length alone. NO STATEMENT HERE NAMES headParts, quietPart OR
scalarsPart: that a run of the frame yields just these pieces is another file's.
WHAT IT IS NOT. CONDITIONAL THROUGHOUT. THAT THE HEARING RETURNS IS A PREMISE. THE LETTERS g AT
WHICH THE HEARING IS READ MUST BE a.given p hd0, THOSE THAT THE PROVER'S SMALL INPUT MAKES: that the
verifier's own letters at its state are these, word for word, is owed by whoever calls this at a
state. Premises too: that the mask row, from the ledger's next number on, reads as the row's coins
in the order in which the parts spend them (headSpent: typed here; tied here to no text of the
frame's); the test on the challenges' counts at the four sumchecks; that the lookup's point on the
positions has lt coordinates (a matter of the lookup's point alone); that the ledger in front of the
hearing is well laid (hW); that there are at least as many challenges as the sub-protocol has rounds
(hlen); that the hearing leaves no round. Nothing on whether the verifier accepts, on soundness, on
completeness or on what a proof hides. Thirteen of the fourteen clauses are equations in the field.
No example in this file.
AN EXAMPLE LIES APART, BY EVALUATION: Honest/K6/ToyHides.lean asks HidesTables' fourteen clauses,
written out a second time with code (nothing ties them to the structure's text),
and the premise on the mask row at the coins that the frame's lendRow lends at the example's book,
at the sessions of Honest/K6/Toy2.lean. Neither file is in the library.
  headStateAt, headShare   the state in front of part number i; its share of the challenges.
  headTiedFrom, tied_append   the mask row reads as a list of coins from a number on; a list in two.
  headSpent                the row's coins in the order of spending.
  own_at, front_at, pv_at, elem_at, share_one   what Ask.lean's readers of the challenges heard
                           return at headStateAt.
  coinsE_length, first_length, end_length, both_length, ties_of   from headTiedFrom at a sumcheck's
                           two stretches of coins to the three ties that SumTruth.lean's laws ask.
  said_batch               a round of scalars as scalarsPart says it, through LaidLaw.lean's
                           batch_truth.
  hides_of_eight           THE MAIN STATEMENT. Derived inside, no premises: the point on the
                           positions and the two batching elements are the same words on both sides;
                           the three ties on the mask row at each sumcheck; that point's size.
CALLED: Johnson/Desc/Kinds/Law/K06HearEight.lean (hear_eight, point_spec), SumTruth.lean (call_eq,
level_truth, sumcheck_truth), LaidLaw.lean (batch_truth), HidesOfParts.lean (hides_of_parts),
TablesLaw.lean (lg_vars); of SumLaw/: rounds_count, ownSlots_callAt, scalars_rvSaid, map_getD,
addL_getD, padTo_getD, canon_gl; of the library: batch_one, zS_size, own_callOf, getD_zero,
sumcheck_okEnds, roundOf_spec.
-/
import Mathlib
import Johnson.Desc.ProofFile.Honest.K6.SumTruth
import Johnson.Desc.K6.Honest.HidesOfParts
import Johnson.Desc.Kinds.Law.K06HearEight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes (E zeroE)
open OnBytes.Model (Aff Fork Reading)
open OnBytes.PscRun (Later Sized)
open VerifiableInference.Desc.Part.MaskedSum (Call Var ownSlots)
open VerifiableInference.Desc.Kinds (Point Form Hid Sum sumcheck level sendThenBatch Head.Par
  Head.Given Head.HeardAll FinalNorm.zt halves Norm.lPd Norm.squaresStart)
open VerifiableInference.Desc.Kinds.Head.Law (rd worldE noEnt WellLaid callOf zS zS_size point_spec
  batch_one hear_eight getD_zero sumcheck_okEnds)
open VerifiableInference.Desc.Kinds.Head.Law.Came (val)
open VerifiableInference.Desc.Kinds.Head.Honest (PairSum wScalars pScalars sqSum prSum nmSum lgSum
  prLead nmLead lgLead lg_vars hides_of_parts)
open SumLaw (alone SumCoins firstRun endRun frontOf drawsOk varsOf hidingCoin rvSaid)

variable {V W X : Type}

/-! ## 1 The terms -/

/-- The state in front of part number i: it has heard hd0, and the sub-protocol's own challenges in
front of the part. -/
def headStateAt (p : Head.Par) (a : HeadAsk) (hd0 ds : List Fmt.Drawn) (i : Nat) :
    State HeadAsk Unit := ⟨a, hd0 ++ ds.take (headInFront p i), ()⟩

/-- Part number i's share of the sub-protocol's challenges. -/
def headShare (p : Head.Par) (ds : List Fmt.Drawn) (i : Nat) : List Fmt.Drawn :=
  (ds.drop (headInFront p i)).take ((headCut p).getD i 0)

/-- From the number first on, the mask row reads as the list l. -/
def headTiedFrom (mask : Nat → E) (first : Nat) (l : List E) : Prop :=
  ∀ j, j < l.length → rd (mask (first + j)) = rd (l.getD j zeroE)

theorem tied_append (mask : Nat → E) (first : Nat) (a b : List E)
    (h : headTiedFrom mask first (a ++ b)) :
    headTiedFrom mask first a ∧ headTiedFrom mask (first + a.length) b := by
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · rw [h j (by rw [List.length_append]; omega), List.getD_append _ _ _ _ hj]
  · rw [Nat.add_assoc, h (a.length + j) (by rw [List.length_append]; omega),
      List.getD_append_right _ _ _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-! ## 2 What the readers of the challenges heard return -/

theorem own_at (p : Head.Par) (i : Nat) (hd0 ds : List Fmt.Drawn)
    (h : headInFront p i ≤ ds.length) :
    headOwn p i (hd0 ++ ds.take (headInFront p i)) = ds.take (headInFront p i) := by
  unfold headOwn
  rw [List.length_append, List.length_take, Nat.min_eq_left h, Nat.add_sub_cancel, List.drop_left]

theorem front_at (p : Head.Par) (i : Nat) (hd0 ds : List Fmt.Drawn)
    (h : headInFront p i ≤ ds.length) :
    headFront p i (hd0 ++ ds.take (headInFront p i)) = hd0 := by
  unfold headFront
  rw [List.length_append, List.length_take, Nat.min_eq_left h, Nat.add_sub_cancel, List.take_left]

theorem pv_at (ds : List Fmt.Drawn) (k : Nat) (d0 : Fmt.Drawn) (h0 : ds.head? = some d0)
    (hk : 0 < k) : headPV (ds.take k) = (d0.elems.map E.ofTriple).toArray := by
  unfold headPV
  rw [List.head?_take, if_neg (by omega), h0]
  rfl

theorem elem_at (ds : List Fmt.Drawn) (k m : Nat) (d : Fmt.Drawn) (hm : m < k)
    (hd : ds[m]? = some d) : elemOf (ds.take k) m = SumLaw.elemOf d := by
  unfold elemOf SumLaw.elemOf elemsOf
  rw [List.getElem?_take, if_pos hm, hd]
  show ((d.elems.map E.ofTriple).head?).getD zeroE = _
  rw [List.head?_map]

theorem share_one (ds : List Fmt.Drawn) (k : Nat) (d : Fmt.Drawn)
    (h : (ds.drop k).take 1 = [d]) : ds[k]? = some d := by
  have e := congrArg (fun l : List Fmt.Drawn => l[0]?) h
  simpa [List.getElem?_take, List.getElem?_drop] using e

/-! ## 3 The coins -/

theorem coinsE_length {d : Due} (c : Cs d) : (coinsE c).length = d.e := by
  unfold coinsE
  rw [List.length_ofFn]

theorem first_length (name endName : String) (lead n e : Nat) (sumAt : W → Front X → PairSum)
    (leadAt : W → Front X → List E)
    (c : SumCoins name endName (pairJob (pointShape lead n e) sumAt leadAt)) (w : W) (fr : Front X)
    (z : Point)
    (hk : (pairJob (pointShape lead n e) sumAt leadAt).callAt w fr = callOf lead z e) :
    (firstRun c).length = lead + ownSlots (callOf lead z e).all := by
  unfold firstRun
  rw [coinsE_length, ← hk, SumLaw.ownSlots_callAt]
  rfl

theorem end_length (name endName : String) (lead n e : Nat) (sumAt : W → Front X → PairSum)
    (leadAt : W → Front X → List E)
    (c : SumCoins name endName (pairJob (pointShape lead n e) sumAt leadAt)) :
    (endRun c).length = e := by
  show (coinsE c.2.1.2.1).length = e
  rw [coinsE_length]

/-- **From the mask row at a sumcheck's two stretches of coins to the three ties.** -/
theorem ties_of (name endName : String) (lead n e : Nat) (sumAt : W → Front X → PairSum)
    (leadAt : W → Front X → List E)
    (c : SumCoins name endName (pairJob (pointShape lead n e) sumAt leadAt)) (w : W) (fr : Front X)
    (z : Point)
    (hk : (pairJob (pointShape lead n e) sumAt leadAt).callAt w fr = callOf lead z e)
    (mask : Nat → E) (first : Nat) (h : headTiedFrom mask first (firstRun c ++ endRun c)) :
    (∀ i, i < lead → rd (mask (first + i)) = rd ((firstRun c).getD i zeroE)) ∧
    (∀ i, i < ownSlots (callOf lead z e).all → rd (mask (first + lead + i)) = hidingCoin c i) ∧
    (∀ j, j < e → rd (mask (first + lead + ownSlots (callOf lead z e).all + j)) =
      rd ((endRun c).getD j zeroE)) := by
  obtain ⟨h1, h2⟩ := tied_append mask first _ _ h
  have l1 := first_length name endName lead n e sumAt leadAt c w fr z hk
  have l2 := end_length name endName lead n e sumAt leadAt c
  refine ⟨fun i hi => h1 i (by rw [l1]; omega), fun i hi => ?_, fun j hj => ?_⟩
  · rw [Nat.add_assoc]
    exact h1 (lead + i) (by rw [l1]; omega)
  · rw [l1, ← Nat.add_assoc] at h2
    exact h2 j (by rw [l2]; exact hj)

/-! ## 4 A round of scalars -/

/-- **A round of scalars as scalarsPart says it**: each value plus its coin, laid into words: each
of its n variables is worth its value, in the world of every later ledger. CONDITIONAL on a
well-laid ledger in front, on the return of sendThenBatch, and on the mask row's tie to the coins.
-/
theorem said_batch (n rows : Nat) (vals : List E) (u : Cs ⟨0, n⟩) (d : Fmt.Drawn)
    {F0 F1 G : Fork} {A : Array Hid} {g : E} (hW : WellLaid F0)
    (h : sendThenBatch n rows F0 [rvSaid (addL (padTo n vals) (coinsE u)) d] =
      some ((A, g), F1, []))
    (hL : Later F1 G) (mask : Nat → E) (hm : headTiedFrom mask F0.next (coinsE u)) :
    ∀ i, i < n → val (worldE G mask noEnt) (A.getD i {}).var = rd (vals.getD i zeroE) := by
  have hlen : (coinsE u).length = n := coinsE_length u
  intro i hi
  rw [VerifiableInference.Desc.Kinds.Head.Honest.batch_truth hW h hL mask vals
    (fun r v gs hp hr i hi => ?_) i hi, VerifiableInference.Desc.Kinds.Head.Law.getD_zero]
  obtain rfl : rvSaid (addL (padTo n vals) (coinsE u)) d = r := (List.cons.inj hp).1
  have hs := (VerifiableInference.Desc.Part.MaskedSum.roundOf_spec hr).1
  rw [SumLaw.scalars_rvSaid] at hs
  obtain rfl := Option.some.inj hs
  rw [VerifiableInference.Desc.Kinds.Head.Law.getD_zero, hm i (by rw [hlen]; exact hi)]
  show Reading.gl.val _ = Reading.gl.val _ + Reading.gl.val _
  rw [SumLaw.map_getD Reading.gl SumLaw.canon SumLaw.canon_gl, SumLaw.addL_getD,
    SumLaw.padTo_getD, if_pos hi]

/-! ## 5 The main statement -/

/-- The two stretches of a sumcheck's coins are as many as the numbers that the verifier's text
takes. -/
theorem both_length (name endName : String) (lead n e : Nat) (sumAt : W → Front X → PairSum)
    (leadAt : W → Front X → List E)
    (c : SumCoins name endName (pairJob (pointShape lead n e) sumAt leadAt)) (w : W) (fr : Front X)
    (z : Point)
    (hk : (pairJob (pointShape lead n e) sumAt leadAt).callAt w fr = callOf lead z e) :
    (firstRun c ++ endRun c).length = lead + ((2 * z.size + 3) + e) := by
  rw [List.length_append, first_length name endName lead n e sumAt leadAt c w fr z hk,
    end_length, VerifiableInference.Desc.Kinds.Head.Law.own_callOf]
  omega

/-- **The row's coins, in the order in which the parts spend them**: the nine scalars'; the squares'
sumcheck's two stretches; the seven scalars'; the three other sumchecks' two stretches each. -/
def headSpent {n2 e2 n5 e5 n6 e6 n7 e7 : String} {p : Head.Par} (u1 : Cs ⟨0, 9⟩)
    (c2 : SumCoins n2 e2 (headSquaresJob p)) (u4 : Cs ⟨0, 7⟩)
    (c5 : SumCoins n5 e5 (headProductsJob p)) (c6 : SumCoins n6 e6 (headNormedJob p))
    (c7 : SumCoins n7 e7 (headLogitsJob p)) : List E :=
  coinsE u1 ++ ((firstRun c2 ++ endRun c2) ++ (coinsE u4 ++ ((firstRun c5 ++ endRun c5) ++
    ((firstRun c6 ++ endRun c6) ++ (firstRun c7 ++ endRun c7)))))

open VerifiableInference.Desc.Kinds.Head.Honest (HidesTables) in
/-- **WHERE THE ONE HEARING RETURNS ON THE EIGHT PIECES, HidesTables HOLDS OF THE CELLS, THE MASK
ROW, WHAT WAS HEARD AND THE LEDGER THAT IT RETURNS.**
g: the letters in front of the hearing, made of the small input and of what was heard before the
sub-protocol began. q0, q3: letters for the two rounds in which nothing is meant to be sent: of q0
its challenges alone are asked, of q3 its length alone. The two rounds of scalars are written out;
d1, d4: their challenges, the members number 1 and headInFront p 4 of ds. q2, q5, q6,
q7: the four sumchecks' rounds, each part played alone. -/
theorem hides_of_eight [g : Head.Given] (p : Head.Par) (a : HeadAsk) (hd0 ds : List Fmt.Drawn)
    (hg : g = a.given p hd0) {n2 e2 n5 e5 n6 e6 n7 e7 : String} (u1 : Cs ⟨0, 9⟩)
    (c2 : SumCoins n2 e2 (headSquaresJob p)) (u4 : Cs ⟨0, 7⟩)
    (c5 : SumCoins n5 e5 (headProductsJob p)) (c6 : SumCoins n6 e6 (headNormedJob p))
    (c7 : SumCoins n7 e7 (headLogitsJob p)) (s2 s5 s6 s7 : Seen)
    (q0 q2 q3 q5 q6 q7 : List Fmt.RoundView)
    (d1 d4 : Fmt.Drawn) (F G : Fork) (H : Head.HeardAll) (mask : Nat → E)
    (hlen : headInFront p 8 ≤ ds.length)
    (hq0 : q0.map (·.drawn) = headShare p ds 0) (hd1 : headShare p ds 1 = [d1])
    (l3 : q3.length = 1) (hd4 : headShare p ds 4 = [d4])
    (ok2 : drawsOk ((headSquaresJob p).callAt (headStateAt p a hd0 ds 2).input
      (frontOf (headStateAt p a hd0 ds 2) s2)) (headShare p ds 2) = true)
    (ha2 : alone (sumPart (V := Unit) n2 e2 (headSquaresJob p)) c2 (headStateAt p a hd0 ds 2) s2
      (headShare p ds 2) = some q2)
    (ok5 : drawsOk ((headProductsJob p).callAt (headStateAt p a hd0 ds 5).input
      (frontOf (headStateAt p a hd0 ds 5) s5)) (headShare p ds 5) = true)
    (ha5 : alone (sumPart (V := Unit) n5 e5 (headProductsJob p)) c5 (headStateAt p a hd0 ds 5) s5
      (headShare p ds 5) = some q5)
    (ok6 : drawsOk ((headNormedJob p).callAt (headStateAt p a hd0 ds 6).input
      (frontOf (headStateAt p a hd0 ds 6) s6)) (headShare p ds 6) = true)
    (ha6 : alone (sumPart (V := Unit) n6 e6 (headNormedJob p)) c6 (headStateAt p a hd0 ds 6) s6
      (headShare p ds 6) = some q6)
    (ok7 : drawsOk ((headLogitsJob p).callAt (headStateAt p a hd0 ds 7).input
      (frontOf (headStateAt p a hd0 ds 7) s7)) (headShare p ds 7) = true)
    (ha7 : alone (sumPart (V := Unit) n7 e7 (headLogitsJob p)) c7 (headStateAt p a hd0 ds 7) s7
      (headShare p ds 7) = some q7)
    (hW : WellLaid F)
    (hh : VerifiableInference.Desc.Kinds.Head.hear F
      (q0 ++ ([rvSaid (addL (padTo 9 (headNine p a (headStateAt p a hd0 ds 1).heard)) (coinsE u1))
          d1] ++ (q2 ++ (q3 ++
        ([rvSaid (addL (padTo 7 (headSeven p a (headStateAt p a hd0 ds 4).heard)) (coinsE u4))
          d4] ++ (q5 ++ (q6 ++ q7))))))) = some (H, G, []))
    (hzt : (VerifiableInference.Desc.Kinds.FinalNorm.zt).size =
      VerifiableInference.Desc.Kinds.Norm.lt)
    (hM : headTiedFrom mask F.next (headSpent u1 c2 u4 c5 c6 c7)) :
    HidesTables a.cells mask H G := by
  subst hg
  letI : Head.Given := a.given p hd0
  -- the numbers of rounds in front of the parts
  have v1 : headInFront p 1 = 1 := rfl
  have v2 : headInFront p 2 = 2 := rfl
  have v4 : headInFront p 4 = headLPd p + headLt p + 6 := by
    show 0 + 1 + 1 + (headLPd p + headLt p + 3) + 1 = _
    omega
  have v5 : headInFront p 5 = headLPd p + headLt p + 7 := by
    show 0 + 1 + 1 + (headLPd p + headLt p + 3) + 1 + 1 = _
    omega
  have v6 : headInFront p 6 = headLPd p + headLt p + 7 + (headLt p + 3) := by
    show 0 + 1 + 1 + (headLPd p + headLt p + 3) + 1 + 1 + (headLt p + 3) = _
    omega
  have v7 : headInFront p 7 = headLPd p + headLt p + 7 + (headLt p + 3) + (headLt p + 3) := by
    show 0 + 1 + 1 + (headLPd p + headLt p + 3) + 1 + 1 + (headLt p + 3) + (headLt p + 3) = _
    omega
  have v8 : headInFront p 7 ≤ headInFront p 8 := by
    show headInFront p 7 ≤ 0 + 1 + 1 + (headLPd p + headLt p + 3) + 1 + 1 + (headLt p + 3) +
      (headLt p + 3) + (headLt p + headLPd p + 3)
    omega
  -- the pieces' lengths
  have l0 : q0.length = 1 := by
    have e := congrArg List.length hq0
    rw [List.length_map] at e
    rw [e]
    show ((ds.drop 0).take 1).length = 1
    rw [List.length_take, List.length_drop]
    omega
  have l2 : q2.length = headLPd p + headLt p + 3 := by
    rw [SumLaw.rounds_count (V := Unit) n2 e2 _ c2 _ s2 _ q2 ha2]
    show (List.replicate (headLPd p + headLt p) _).length + 3 = _
    rw [List.length_replicate]
  have l5 : q5.length = headLt p + 3 := by
    rw [SumLaw.rounds_count (V := Unit) n5 e5 _ c5 _ s5 _ q5 ha5]
    show (List.replicate (headLt p) _).length + 3 = _
    rw [List.length_replicate]
  have l6 : q6.length = headLt p + 3 := by
    rw [SumLaw.rounds_count (V := Unit) n6 e6 _ c6 _ s6 _ q6 ha6]
    show (List.replicate (headLt p) _).length + 3 = _
    rw [List.length_replicate]
  obtain ⟨Fa, Fb, Fc, Fd, Fe, h0, h1, h2, h3, h4, h5, h6, ⟨wa, wb, wc, wd, we⟩,
    ⟨na, nb, nc, nd, ne⟩, ⟨ka, kb, kc, kd, ke⟩, sPV⟩ :=
    hear_eight hW hh l0 rfl l2 l3 rfl l5
      (by rw [l6, hzt]; rfl)
  obtain ⟨line, rfl⟩ := List.length_eq_one_iff.mp l3
  -- the challenges
  obtain ⟨r0, e0, hpv, _⟩ := point_spec h0
  have g0 : ds.head? = some r0.drawn := by
    rw [e0] at hq0
    have e : (ds.drop 0).take 1 = [r0.drawn] := hq0.symm
    rw [List.head?_eq_getElem?]
    exact share_one ds 0 r0.drawn e
  have g1 : ds[1]? = some d1 := share_one ds 1 d1 hd1
  have g4 : ds[headInFront p 4]? = some d4 := share_one ds _ d4 hd4
  have b1 : headInFront p 1 ≤ ds.length := by omega
  have b2 : headInFront p 2 ≤ ds.length := by omega
  have b4 : headInFront p 4 ≤ ds.length := by omega
  have b5 : headInFront p 5 ≤ ds.length := by omega
  have b6 : headInFront p 6 ≤ ds.length := by omega
  have b7 : headInFront p 7 ≤ ds.length := by omega
  -- the letters that the prover reads off the challenges are the verifier's
  have pvAt : ∀ i, 0 < headInFront p i → headInFront p i ≤ ds.length →
      headPV (headOwn p i (hd0 ++ ds.take (headInFront p i))) = H.1.pV := fun i c1 c2 => by
    rw [own_at p i hd0 ds c2, pv_at ds _ r0.drawn g0 c1, hpv]
  obtain ⟨r1, x1, er1, ex1, eg1, _⟩ := batch_one h1
  have hgam : SumLaw.elemOf d1 = H.1.gam := by
    obtain rfl := (List.cons.inj er1).1
    have e : d1.elems = [x1] := ex1
    unfold SumLaw.elemOf
    rw [e]
    exact eg1
  obtain ⟨r4, x4, er4, ex4, eg4, _⟩ := batch_one h3
  have hom : SumLaw.elemOf d4 = H.1.om := by
    obtain rfl := (List.cons.inj er4).1
    have e : d4.elems = [x4] := ex4
    unfold SumLaw.elemOf
    rw [e]
    exact eg4
  have gamAt : headGam (headOwn p 2 (hd0 ++ ds.take (headInFront p 2))) = H.1.gam := by
    rw [own_at p 2 hd0 ds b2]
    unfold headGam
    rw [elem_at ds _ 1 d1 (by rw [v2]; omega) g1, hgam]
  have omAt : headOm p (headOwn p 5 (hd0 ++ ds.take (headInFront p 5))) = H.1.om := by
    rw [own_at p 5 hd0 ds b5]
    unfold headOm
    rw [elem_at ds _ _ d4 (by rw [v4, v5]; omega) g4, hom]
  -- the values and the sums at these letters
  have eN : headNine p a (headStateAt p a hd0 ds 1).heard = wScalars a.cells H.1.pV := by
    show wScalars a.cells (headPV (headOwn p 1 (hd0 ++ ds.take (headInFront p 1)))) = _
    rw [pvAt 1 (by omega) b1]
  have eS : headSeven p a (headStateAt p a hd0 ds 4).heard = pScalars a.cells H.1.pV := by
    show pScalars a.cells (headPV (headOwn p 4 (hd0 ++ ds.take (headInFront p 4)))) = _
    rw [pvAt 4 (by omega) b4]
  have eq2 : headSquaresSum p (headStateAt p a hd0 ds 2).input
      (frontOf (headStateAt p a hd0 ds 2) s2).heard = sqSum a.cells H.1.pV H.1.gam := by
    show sqSum a.cells (headPV (headOwn p 2 (hd0 ++ ds.take (headInFront p 2))))
      (headGam (headOwn p 2 (hd0 ++ ds.take (headInFront p 2)))) = _
    rw [pvAt 2 (by omega) b2, gamAt]
  have eq5 : headProductsSum p (headStateAt p a hd0 ds 5).input
      (frontOf (headStateAt p a hd0 ds 5) s5).heard = prSum a.cells H.1.pV H.1.om := by
    show prSum a.cells (headPV (headOwn p 5 (hd0 ++ ds.take (headInFront p 5))))
      (headOm p (headOwn p 5 (hd0 ++ ds.take (headInFront p 5)))) = _
    rw [pvAt 5 (by omega) b5, omAt]
  have ld5 : headProductsLead p (headStateAt p a hd0 ds 5).input
      (frontOf (headStateAt p a hd0 ds 5) s5).heard = prLead a.cells H.1.pV H.1.om := by
    show prLead a.cells (headPV (headOwn p 5 (hd0 ++ ds.take (headInFront p 5))))
      (headOm p (headOwn p 5 (hd0 ++ ds.take (headInFront p 5)))) = _
    rw [pvAt 5 (by omega) b5, omAt]
  have eq6 : headNormedSum p (headStateAt p a hd0 ds 6).input
      (frontOf (headStateAt p a hd0 ds 6) s6).heard = nmSum a.cells := by
    show headNormedSumAt (a.given p (headFront p 6 (hd0 ++ ds.take (headInFront p 6)))) a.cells = _
    rw [front_at p 6 hd0 ds b6]
    rfl
  have ld6 : headNormedLead p (headStateAt p a hd0 ds 6).input
      (frontOf (headStateAt p a hd0 ds 6) s6).heard = nmLead a.cells := by
    show headNormedLeadAt (a.given p (headFront p 6 (hd0 ++ ds.take (headInFront p 6)))) a.cells = _
    rw [front_at p 6 hd0 ds b6]
    rfl
  have eq7 : headLogitsSum p (headStateAt p a hd0 ds 7).input
      (frontOf (headStateAt p a hd0 ds 7) s7).heard = lgSum a.cells.toCells := by
    show headLogitsSumAt (a.given p (headFront p 7 (hd0 ++ ds.take (headInFront p 7)))) a.cells = _
    rw [front_at p 7 hd0 ds b7]
    rfl
  have ld7 : headLogitsLead p (headStateAt p a hd0 ds 7).input
      (frontOf (headStateAt p a hd0 ds 7) s7).heard = lgLead a.cells.toCells := by
    show headLogitsLeadAt (a.given p (headFront p 7 (hd0 ++ ds.take (headInFront p 7)))) a.cells = _
    rw [front_at p 7 hd0 ds b7]
    rfl
  -- the four points, word for word, and their sizes
  have hz2 : (zS H.1.pV).toList = (headSquaresSum p (headStateAt p a hd0 ds 2).input
      (frontOf (headStateAt p a hd0 ds 2) s2).heard).z := by rw [eq2]; rfl
  have hn2 : (zS H.1.pV).size = headLPd p + headLt p := zS_size H.1.pV sPV
  have hz5 : H.1.pV.toList = (headProductsSum p (headStateAt p a hd0 ds 5).input
      (frontOf (headStateAt p a hd0 ds 5) s5).heard).z := by rw [eq5]; rfl
  have hz6 : (FinalNorm.zt).toList = (headNormedSum p (headStateAt p a hd0 ds 6).input
      (frontOf (headStateAt p a hd0 ds 6) s6).heard).z := by rw [eq6]; rfl
  have hz7 : (FinalNorm.zt ++ halves Norm.lPd).toList =
      (headLogitsSum p (headStateAt p a hd0 ds 7).input
        (frontOf (headStateAt p a hd0 ds 7) s7).heard).z := by rw [eq7]; rfl
  have hn7 : (FinalNorm.zt ++ halves Norm.lPd).size =
      headLt p + headLPd p := by
    rw [← Array.length_toList]
    exact (lg_vars a.cells.toCells).trans (by rw [hzt]; rfl)
  have hk2 := call_eq 0 (headLPd p + headLt p) 2 (fun a fr => headSquaresSum p a fr.heard)
    (fun _ _ => []) (headStateAt p a hd0 ds 2).input (frontOf (headStateAt p a hd0 ds 2) s2)
    (zS H.1.pV) hz2 hn2
  have hk5 := call_eq 1 (headLt p) 4 (fun a fr => headProductsSum p a fr.heard)
    (fun a fr => [headProductsLead p a fr.heard]) (headStateAt p a hd0 ds 5).input
    (frontOf (headStateAt p a hd0 ds 5) s5) H.1.pV hz5 sPV
  have hk6 := call_eq 1 (headLt p) 2 (fun a fr => headNormedSum p a fr.heard)
    (fun a fr => [headNormedLead p a fr.heard]) (headStateAt p a hd0 ds 6).input
    (frontOf (headStateAt p a hd0 ds 6) s6) FinalNorm.zt hz6 hzt
  have hk7 := call_eq 1 (headLt p + headLPd p) 2 (fun a fr => headLogitsSum p a fr.heard)
    (fun a fr => [headLogitsLead p a fr.heard]) (headStateAt p a hd0 ds 7).input
    (frontOf (headStateAt p a hd0 ds 7) s7) (FinalNorm.zt ++ halves Norm.lPd)
    hz7 hn7
  -- the mask row, part by part
  obtain ⟨m1, t1⟩ := tied_append mask F.next _ _ hM
  rw [coinsE_length] at t1
  have t1' : headTiedFrom mask (F.next + 9) _ := t1
  rw [← na] at t1'
  obtain ⟨m2, t2⟩ := tied_append mask Fa.next _ _ t1'
  have bl2 : (firstRun c2 ++ endRun c2).length = 0 + ((2 * (zS H.1.pV).size + 3) + 2) :=
    both_length n2 e2 0 _ 2 _ _ c2 _ _ _ hk2
  rw [bl2, ← nb] at t2
  obtain ⟨m4, t4⟩ := tied_append mask Fb.next _ _ t2
  rw [coinsE_length] at t4
  have t4' : headTiedFrom mask (Fb.next + 7) _ := t4
  rw [← nc] at t4'
  obtain ⟨m5, t5⟩ := tied_append mask Fc.next _ _ t4'
  have bl5 : (firstRun c5 ++ endRun c5).length = 1 + ((2 * H.1.pV.size + 3) + 4) :=
    both_length n5 e5 1 _ 4 _ _ c5 _ _ _ hk5
  rw [bl5, ← nd] at t5
  obtain ⟨m6, m7⟩ := tied_append mask Fd.next _ _ t5
  have bl6 : (firstRun c6 ++ endRun c6).length = 1 + ((2 * (FinalNorm.zt).size + 3) + 2) :=
    both_length n6 e6 1 _ 2 _ _ c6 _ _ _ hk6
  rw [bl6, ← ne] at m7
  obtain ⟨_, o2, x2⟩ := ties_of n2 e2 0 _ 2 _ _ c2 _ _ _ hk2 mask Fa.next m2
  obtain ⟨y5, o5, x5⟩ := ties_of n5 e5 1 _ 4 _ _ c5 _ _ _ hk5 mask Fc.next m5
  obtain ⟨y6, o6, x6⟩ := ties_of n6 e6 1 _ 2 _ _ c6 _ _ _ hk6 mask Fd.next m6
  obtain ⟨y7, o7, x7⟩ := ties_of n7 e7 1 _ 2 _ _ c7 _ _ _ hk7 mask Fe.next m7
  -- the six parts
  have hm2 : (headSquaresSum p (headStateAt p a hd0 ds 2).input
      (frontOf (headStateAt p a hd0 ds 2) s2).heard).maps.length = 2 := by rw [eq2]; rfl
  have hm5 : (headProductsSum p (headStateAt p a hd0 ds 5).input
      (frontOf (headStateAt p a hd0 ds 5) s5).heard).maps.length = 4 := by rw [eq5]; rfl
  have hm6 : (headNormedSum p (headStateAt p a hd0 ds 6).input
      (frontOf (headStateAt p a hd0 ds 6) s6).heard).maps.length = 2 := by rw [eq6]; rfl
  have hm7 : (headLogitsSum p (headStateAt p a hd0 ds 7).input
      (frontOf (headStateAt p a hd0 ds 7) s7).heard).maps.length = 2 := by rw [eq7]; rfl
  have A1 := said_batch 9 9 _ u1 d1 hW h1 ka mask m1
  have A4 := said_batch 7 7 _ u4 d4 wb h3 kc mask m4
  obtain ⟨_, B3, B4⟩ := level_truth (V := Unit) n2 e2 (headLPd p + headLt p)
    (fun a fr => headSquaresSum p a fr.heard) (fun _ _ => []) c2 (headStateAt p a hd0 ds 2) s2
    (headShare p ds 2) q2 line (zS H.1.pV) (Norm.squaresStart H.1.W H.1.gam #[])
    Fa Fb G H.1.squares mask hz2 hn2 hm2 ok2 ha2 wa h2 kb o2 x2
  obtain ⟨_, C2, C3, C4⟩ := sumcheck_truth (V := Unit) n5 e5 (headLt p) 4
    (fun a fr => headProductsSum p a fr.heard) (fun a fr => [headProductsLead p a fr.heard]) c5
    (headStateAt p a hd0 ds 5) s5 (headShare p ds 5) q5 H.1.pV Fc Fd G H.1.products mask hz5 sPV
    hm5 ok5 ha5 wc h4 kd (y5 0 (by omega)) o5 x5
  obtain ⟨_, D2, D3, D4⟩ := sumcheck_truth (V := Unit) n6 e6 (headLt p) 2
    (fun a fr => headNormedSum p a fr.heard) (fun a fr => [headNormedLead p a fr.heard]) c6
    (headStateAt p a hd0 ds 6) s6 (headShare p ds 6) q6 FinalNorm.zt Fd Fe G H.2.1.normed
    mask hz6 hzt hm6 ok6 ha6 wd h5 ke (y6 0 (by omega)) o6 x6
  obtain ⟨_, E2, E3, E4⟩ := sumcheck_truth (V := Unit) n7 e7 (headLt p + headLPd p) 2
    (fun a fr => headLogitsSum p a fr.heard) (fun a fr => [headLogitsLead p a fr.heard]) c7
    (headStateAt p a hd0 ds 7) s7 (headShare p ds 7) q7
    (FinalNorm.zt ++ halves Norm.lPd) Fe G G H.2.2.logits mask hz7 hn7
    hm7 ok7 ha7 we h6 (Later.refl G) (y7 0 (by omega)) o7 x7
  rw [eN] at A1
  rw [eS] at A4
  rw [eq2] at B3 B4
  rw [eq5] at C3 C4
  rw [eq6] at D3 D4
  rw [eq7] at E3 E4
  rw [List.getD_cons_zero, ld5] at C2 C4
  rw [List.getD_cons_zero, ld6] at D2 D4
  rw [List.getD_cons_zero, ld7] at E2 E4
  exact hides_of_parts a.cells mask H G sPV hzt
    (fun s hs => (A1 s hs).trans (getD_zero _ _).symm)
    (fun n hn => (A4 n hn).trans (getD_zero _ _).symm) B3 B4 C2 C3 C4 D2 D3 D4 E2 E3 E4
    (sumcheck_okEnds h6 1)

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.tied_append
#print axioms ProofFile.Honest.K6.own_at
#print axioms ProofFile.Honest.K6.front_at
#print axioms ProofFile.Honest.K6.pv_at
#print axioms ProofFile.Honest.K6.elem_at
#print axioms ProofFile.Honest.K6.share_one
#print axioms ProofFile.Honest.K6.coinsE_length
#print axioms ProofFile.Honest.K6.first_length
#print axioms ProofFile.Honest.K6.end_length
#print axioms ProofFile.Honest.K6.ties_of
#print axioms ProofFile.Honest.K6.said_batch
#print axioms ProofFile.Honest.K6.both_length
#print axioms ProofFile.Honest.K6.hides_of_eight
#print axioms ProofFile.Honest.K6.headStateAt
#print axioms ProofFile.Honest.K6.headShare
#print axioms ProofFile.Honest.K6.headTiedFrom
#print axioms ProofFile.Honest.K6.headSpent
