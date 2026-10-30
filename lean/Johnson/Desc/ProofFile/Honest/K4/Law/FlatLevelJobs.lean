-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/FlatLevelJobs.lean: CONDITIONAL.

What is here. AT THE THREE PRODUCT LEVELS OF THE FEED-FORWARD LAYERS' ROUNDS THE ROW THAT THE
VERIFIER's FLAT TEXT LEAVES IS WORTH 0 ON THE HONEST PART's ROUNDS. Where `Fl.levelIn`
(OnBytes/K/Kc/Flat.lean) returns on a tape that holds what the honest part of the masked sumcheck
has played, at the maker's number of variables, point and order, its row (`Level.row`) is worth 0.
Statements and proofs.

  `prod_flat_zero`   a job that is summed at a point, whose summand is the product of two end values
  `level_flat_zero`   a product level of two tables
  `squares_flat_zero`, `gated_flat_zero`, `gated2_flat_zero`   **the three**

Limits. At the reading `Reading.gl` alone. THE START IS A PREMISE, AND IT IS THE JOB's OWN CONTENT:
the claimed form is worth the reading of the cube's total. At the squares that is an identity on the
sums of limb products; at the two gated products the claimed form names end values of the batched
sumcheck, on which nothing is shown. The other premises: the flat function RETURNS, from a sized
ledger; the part's text `hear` returns on the same rounds, from the same ledger and at the same
claimed form (FlatTops.lean takes this premise away); the challenges have the call's shape and the
part's moves answer; THE TAPE HOLDS WHAT THE ROUNDS HOLD (`TapeIs`, FlatCore.lean); THE WORLD HOLDS
THE PART's COINS UNDER THE SUMCHECK's OWN SLOTS (a level lays these slots itself: so from the
level's return on they are worth the mask row's entries; that these entries are the part's coins is
not shown here); the job's maker returns at the run's input; for a gated product the run's cube
fits. THE FLAT FUNCTION IS TYPED AT THE MAKER's NUMBER OF VARIABLES, POINT AND ORDER: that the
verifier runs its level at these is not shown. It stands on FlatLevel.lean, SumEndJobs.lean and
SumPoints.lean beside this file. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatLevel
import Johnson.Desc.ProofFile.Honest.K4.Law.SumEndJobs
import Johnson.Desc.ProofFile.Honest.K4.Law.SumPoints

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E F mulE zeroE oneE)
open OnBytes.Model (Reading Aff Fork World Level orderRange orderDefault)
open OnBytes.Model.Layer (downFrom normsStart)
open OnBytes.Slice (GE)
open OnBytes.K.Kc (Fl Tape)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw
open VerifiableInference.Desc.Part.MaskedSum (Call Var Ends Heard hear rowForm ownSlots scalars)
open ProofFile.Honest.SumLaw

variable {V W X : Type}

/-- **A job of mu variables that is summed at a point, whose summand on end values is the product of
the first two.** tp: the tape. L: what the flat function of a product level hands back. -/
theorem prod_flat_zero (name endName : String) (mu : ℕ) (job : W → Front X → Option Job)
    (c : SumCoins name endName (k4SumJob (k4LevelShape mu) job)) (st : State W X)
    (seen : Seen) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G : Fork)
    (h : Heard) (Wd : World GE) (j : Job) (rho : Array E)
    (hd : drawsOk ((k4SumJob (k4LevelShape mu) job).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (k4SumJob (k4LevelShape mu) job)) c st seen ds =
      some rounds)
    (hh : hear C ((k4SumJob (k4LevelShape mu) job).callAt st.input (frontOf st seen)) F rounds =
      some (h, G))
    (hs : ∀ i,
      i < ownSlots ((k4SumJob (k4LevelShape mu) job).callAt st.input (frontOf st seen)).all →
      Wd.slot (h.first + i) = hidingCoin c i)
    (hσ : C.value Reading.gl Wd = Reading.gl.val j.cube.total)
    (hj : job st.input (frontOf st seen) = some j) (hfit : SumShape (k4LevelShape mu) j)
    (hw : j.cube.way = .point rho) (hdY : j.dY = 2)
    (hat : ∀ rs e, j.atEnds rs e = mulE (e.getD 0 zeroE) (e.getD 1 zeroE))
    (hn : (j.ends (h.r.take j.cube.n)).length = 2)
    (hE : Reading.gl.val ((j.ends (h.r.take j.cube.n)).getD 0 zeroE) *
        Reading.gl.val ((j.ends (h.r.take j.cube.n)).getD 1 zeroE) =
      Reading.gl.val (j.cube.summandAt (h.r.take j.cube.n)))
    {tp u : Tape} {G2 : Fork} {L : Level}
    (hF : Fl.levelIn mu rho C j.cube.order F tp = some (L, G2, u))
    (hS : OnBytes.PscRun.Sized F) (hT : TapeIs tp rounds) :
    L.row.value Reading.gl Wd = 0 := by
  have hmu : j.cube.n = mu := by
    rw [hfit.2.1]
    show (List.replicate mu _).length = mu
    rw [List.length_replicate]
  have hk := point_weights (k4LevelShape mu) mu rfl job st.input (frontOf st seen) j rho hj hw hmu
    (by rw [(fitsP j.cube hfit.1).len, hmu])
  obtain ⟨rv, s, a1, a2, a3⟩ := level_row_worth Reading.gl Wd hF hS _ hk hh hT
  obtain ⟨r', s', b1, b2, _, b4⟩ := prod_rowForm_sent (V := V) name endName (k4LevelShape mu) job c
    st seen ds rounds C F G h {} Wd j ⟨2, 2⟩ hd ha hh hs hσ hj hfit rfl hdY hat hn hE
  have e1 : rv = r' := Option.some.inj (a1.symm.trans b1)
  rw [e1] at a2
  have e2 : s = s' := Option.some.inj (a2.symm.trans b2)
  rw [a3, e2, b4, Aff.value_empty, mul_zero]

/-- **The squares' level: its row is worth 0.** The level's point does not read the slot that
`normsStart` takes: it is typed at 0 here, as the maker has it. -/
theorem squares_flat_zero (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (squaresSum Q)) (st : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G : Fork) (h : Heard)
    (Wd : World GE)
    (hd : drawsOk ((squaresSum Q).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (squaresSum Q)) c st seen ds = some rounds)
    (hh : hear C ((squaresSum Q).callAt st.input (frontOf st seen)) F rounds = some (h, G))
    (hs : ∀ i, i < ownSlots ((squaresSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (h.first + i) = hidingCoin c i)
    (j : Job) (hj : jobSquares Q st.input (ptsOf Q st.input st.heard) = some j)
    (hσ : C.value Reading.gl Wd = Reading.gl.val j.cube.total)
    {tp u : Tape} {G2 : Fork} {L : Level}
    (hF : Fl.levelIn Q.P.rd.muV (normsStart Q.P.y 0 (ptsOf Q st.input st.heard).gp
      (ptsOf Q st.input st.heard).rhoI (ptsOf Q st.input st.heard).PV).2 C
      (orderDefault Q.P.rd.muV) F tp = some (L, G2, u))
    (hS : OnBytes.PscRun.Sized F) (hT : TapeIs tp rounds) :
    L.row.value Reading.gl Wd = 0 := by
  have hj' := hj
  rw [jobSquares_eq] at hj'
  split at hj'
  · rename_i hf
    obtain rfl := Option.some.inj hj'
    exact prod_flat_zero (V := V) name endName Q.P.rd.muV
      (fun w fr => jobSquares Q w (ptsOf Q w fr.heard)) c st seen ds rounds C F G h Wd _ _ hd ha hh
      hs hσ hj (jobFits_parts (sqJob_jobFits _ _ _ hf)) rfl rfl (fun _ _ => rfl) rfl (by
        rw [summandAt_read]
        show _ = Reading.gl.val oneE * _ + 0
        rw [Reading.gl.one, one_mul, add_zero]
        rfl) hF hS hT
  · cases hj'

/-- A product level of two tables, where its cube fits. -/
theorem level_flat_zero (name endName : String) (mu : ℕ) (job : W → Front X → Option Job)
    (c : SumCoins name endName (k4SumJob (k4LevelShape mu) job)) (st : State W X)
    (seen : Seen) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G : Fork)
    (h : Heard) (Wd : World GE) (order : List ℕ) (rho : Array E) (tb : Tab × Tab)
    (hd : drawsOk ((k4SumJob (k4LevelShape mu) job).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (k4SumJob (k4LevelShape mu) job)) c st seen ds =
      some rounds)
    (hh : hear C ((k4SumJob (k4LevelShape mu) job).callAt st.input (frontOf st seen)) F rounds =
      some (h, G))
    (hs : ∀ i,
      i < ownSlots ((k4SumJob (k4LevelShape mu) job).callAt st.input (frontOf st seen)).all →
      Wd.slot (h.first + i) = hidingCoin c i)
    (hj : job st.input (frontOf st seen) = some (levelJob mu order rho tb))
    (hfit : (levelJob mu order rho tb).cube.fits = true)
    (hσ : C.value Reading.gl Wd = Reading.gl.val (levelJob mu order rho tb).cube.total)
    {tp u : Tape} {G2 : Fork} {L : Level}
    (hF : Fl.levelIn mu rho C order F tp = some (L, G2, u)) (hS : OnBytes.PscRun.Sized F)
    (hT : TapeIs tp rounds) : L.row.value Reading.gl Wd = 0 :=
  prod_flat_zero (V := V) name endName mu job c st seen ds rounds C F G h Wd
    (levelJob mu order rho tb) rho hd ha hh hs hσ hj
    (jobFits_parts (levelJob_jobFits mu order rho tb hfit)) rfl rfl (fun _ _ => rfl)
    (by
      show ((levelJob mu order rho tb).cube.valuesAt _).toList.length = 2
      rw [Array.length_toList, valuesAt_size]
      rfl)
    (level_ends mu order rho tb _) hF hS hT

/-- **The first gated product's level: its row is worth 0.** -/
theorem gated_flat_zero (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (gatedSum Q)) (st : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G : Fork) (h : Heard)
    (Wd : World GE)
    (hd : drawsOk ((gatedSum Q).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (gatedSum Q)) c st seen ds = some rounds)
    (hh : hear C ((gatedSum Q).callAt st.input (frontOf st seen)) F rounds = some (h, G))
    (hs : ∀ i, i < ownSlots ((gatedSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (h.first + i) = hidingCoin c i)
    (tb : Tab × Tab) (ht : gatedTabs Q st.input = some tb)
    (hfit : (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
      (downFrom (ptsOf Q st.input st.heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++
        ztOf Q (ptsOf Q st.input st.heard)) tb).cube.fits = true)
    (hσ : C.value Reading.gl Wd = Reading.gl.val (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
      (downFrom (ptsOf Q st.input st.heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++
        ztOf Q (ptsOf Q st.input st.heard)) tb).cube.total)
    {tp u : Tape} {G2 : Fork} {L : Level}
    (hF : Fl.levelIn Q.P.rd.muH
      (downFrom (ptsOf Q st.input st.heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++
        ztOf Q (ptsOf Q st.input st.heard)) C (orderRange Q.P.rd.muH) F tp = some (L, G2, u))
    (hS : OnBytes.PscRun.Sized F) (hT : TapeIs tp rounds) :
    L.row.value Reading.gl Wd = 0 :=
  level_flat_zero (V := V) name endName Q.P.rd.muH
    (fun w fr => jobGated Q w (ptsOf Q w fr.heard)) c st seen ds rounds C F G h Wd _ _ tb hd ha hh
    hs (by show (gatedTabs Q st.input).map _ = _; rw [ht]; rfl) hfit hσ hF hS hT

/-- **The second gated product's level: its row is worth 0.** -/
theorem gated2_flat_zero (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (gated2Sum Q)) (st : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G : Fork) (h : Heard)
    (Wd : World GE)
    (hd : drawsOk ((gated2Sum Q).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (gated2Sum Q)) c st seen ds = some rounds)
    (hh : hear C ((gated2Sum Q).callAt st.input (frontOf st seen)) F rounds = some (h, G))
    (hs : ∀ i, i < ownSlots ((gated2Sum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (h.first + i) = hidingCoin c i)
    (tb : Tab × Tab) (ht : gatedTabs2 Q st.input = some tb)
    (hfit : (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
      ((ptsOf Q st.input st.heard).rhoM ++ downFrom (ptsOf Q st.input st.heard).rs Q.P.y.lfe ++
        (ptsOf Q st.input st.heard).rt) tb).cube.fits = true)
    (hσ : C.value Reading.gl Wd = Reading.gl.val (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
      ((ptsOf Q st.input st.heard).rhoM ++ downFrom (ptsOf Q st.input st.heard).rs Q.P.y.lfe ++
        (ptsOf Q st.input st.heard).rt) tb).cube.total)
    {tp u : Tape} {G2 : Fork} {L : Level}
    (hF : Fl.levelIn Q.P.rd.muH2
      ((ptsOf Q st.input st.heard).rhoM ++ downFrom (ptsOf Q st.input st.heard).rs Q.P.y.lfe ++
        (ptsOf Q st.input st.heard).rt) C (orderRange Q.P.rd.muH2) F tp = some (L, G2, u))
    (hS : OnBytes.PscRun.Sized F) (hT : TapeIs tp rounds) :
    L.row.value Reading.gl Wd = 0 :=
  level_flat_zero (V := V) name endName Q.P.rd.muH2
    (fun w fr => jobGated2 Q w (ptsOf Q w fr.heard)) c st seen ds rounds C F G h Wd _ _ tb hd ha hh
    hs (by show (gatedTabs2 Q st.input).map _ = _; rw [ht]; rfl) hfit hσ hF hS hT

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.prod_flat_zero
#print axioms ProofFile.Honest.K4.squares_flat_zero
#print axioms ProofFile.Honest.K4.level_flat_zero
#print axioms ProofFile.Honest.K4.gated_flat_zero
#print axioms ProofFile.Honest.K4.gated2_flat_zero
