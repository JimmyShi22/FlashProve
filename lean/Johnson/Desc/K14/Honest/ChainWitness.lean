--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/ChainWitness.lean: the premises under which the functions of the eight
sub-protocols of the linear claim's shared rounds return are met together: there is a key and a
view, written out, at which the eight return one behind the other.

The theorems that the eight return (Johnson/Desc/K14/Honest/YesChain.lean: eight_return) and that
what the statement claims is kept (ChainHolds.lean) have premises on the instance's key and on the
view. A theorem whose premises nothing meets says nothing. This file exhibits a key and a view.

The witness. The key: every seed at the point 0 with the factor 1; every answer 0. The sampled
points: all coordinates 0. The sampled seeds of the two sendings: every element the one whose words
are 1, 0, 0. The OOD answers shown: 0. The sampled locations: all 0, with one column of words 0. The
scalar: 0. The committed table's rows: 0.

Main names:
  keyW, rvElems, rvVals, rvPoss, colsW, firstW, pointW, zetaW, seedsW, zerosW   the witness
  key_fits, key_beta  the two premises on the key
  fits_send           a sending's two rounds have the stated form (roundsFit)
  rec_zero, col_zero  each answer of the key is its row's own; each opened column holds the rows'
                      own symbols: at rows that are 0
  rounds8_met         Rounds8
  ReturnedW           Returned at the witness's key, challenges and column, whatever the two
                      sendings' second rounds and "SPLIT"'s round show
  returned_met        **the eight return at the witness**
  planOwn_of          the two sendings pass their kind's test on the plan, off K14Cond
  returned_real, returned_key   **so at the two typed shapes**

What is assumed, as premises (returned_met): PlanFacts; the two sendings pass their kind's test on
the plan. At the two typed shapes: nothing.

What is not claimed. THE WITNESS IS NO HONEST PROVER's VIEW: the answers and the scalar shown are 0,
whatever the messages hold; the eight test no equation, so their functions return. "returned_real"
says that of a view of zeros at a typed shape; it says nothing of a real proof. That the laid
constraints hold of any words at the witness is not said here (an honest run: ChainMet.lean). The
witness key is no committer's: its seeds follow from no table's name by the hash; and its item is 0,
so that it passes the chain's own test on the instance (the key's item is the plan's) at the item 0
alone. With rows that are 0 the constraints of "(rec_gamma)" and "LOC" say 0 = 0; all locations are
one, so that one column is read. Nothing on soundness, on completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.ChainHolds
import Johnson.Desc.K14.Honest.YesRounds
import Johnson.Desc.K14.Honest.YesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params OnBytes.Params.Prices OnBytes.Plan Johnson.G Desc.Plain
open OnBytes.Slice (rdE)
open VerifiableInference.Desc (roundsFit drawsMarkedNonzeroHaveNonzeroWords itemOf)
open VerifiableInference.Desc.Own (keyFits allZero)
open VerifiableInference.Desc.K1 (planOkOwn seedEntry answerEntry realSized)
open Lk6.AtPlan (keyFull)
open Desc.K14.Law (locations genK K14Cond parU parO)

/-! ## The witness -/

/-- A key whose sizes fit: every seed at the point 0 with the factor 1; every answer 0. -/
def keyW (s : IndexShape) : TableKey :=
  { record := Array.replicate (s.rows * s.answers) zeroE
    seeds := List.replicate s.answers ⟨List.replicate s.cubeBits zeroE, oneE⟩ }

/-- A round in which n elements were sampled, all t, and nothing is shown. -/
def rvElems (n : Nat) (t : Fmt.Ext) : Fmt.RoundView := ⟨[], ⟨List.replicate n t, [], [], none⟩⟩

/-- A round in which nothing was sampled. -/
def rvVals (v : List Fmt.ItemValue) : Fmt.RoundView := ⟨v, ⟨[], [], [], none⟩⟩

/-- A round in which n locations were sampled, all 0. -/
def rvPoss (n : Nat) : Fmt.RoundView := ⟨[], ⟨[], List.replicate n 0, [], none⟩⟩

/-- One column at the location 0: words 0. -/
def colsW (rows : Nat) : List (Nat × List UInt64) := [(0, List.replicate rows 0)]

/-- The shared chain's first state at the witness key. -/
abbrev firstW (P : P14) : St := first P.codes (keyW P.par.S.fold.index)

/-- The round of "LIN point": all coordinates 0. -/
abbrev pointW (P : P14) : Fmt.RoundView := rvElems P.par.S.kCol (0, 0, 0)

/-- The round of "LIN zeta": all coordinates 0. -/
abbrev zetaW (P : P14) : Fmt.RoundView := rvElems P.par.S.kRow (0, 0, 0)

/-- A sending's first round: every sampled element the one whose words are 1, 0, 0. -/
abbrev seedsW (Q : VerifiableInference.Desc.K1.Par) : Fmt.RoundView :=
  rvElems (Q.seeds * (Q.coordinates + 1)) (1, 0, 0)

/-- A sending's second round: as many answers 0 as the place has. -/
abbrev zerosW (Q : VerifiableInference.Desc.K1.Par) : Fmt.RoundView :=
  rvVals (List.replicate Q.answers (.answer (0, 0, 0)))

/-! ## The key -/

/-- The witness key's sizes fit. -/
theorem key_fits (s : IndexShape) : keyFits (keyW s) s = true := by
  refine (VerifiableInference.Desc.Own.keyFits_iff _ _).2
    ⟨Array.size_replicate, List.length_replicate, fun x hx => ?_⟩
  rw [List.eq_of_mem_replicate hx]
  exact List.length_replicate

/-- No seed of the witness key has the factor 0. -/
theorem key_beta (s : IndexShape) : ((keyW s).seeds.all (!allZero ·.beta)) = true := by
  rw [List.all_eq_true]
  intro x hx
  rw [List.eq_of_mem_replicate hx]
  rfl

/-! ## A sending's two rounds -/

/-- **A sending's two rounds have the stated form.** vals: what the second round shows: as many
answers as the place has. -/
theorem fits_send (Q : VerifiableInference.Desc.K1.Par) (vals : List Fmt.ItemValue)
    (hv : vals.map itemOf = List.replicate Q.answers .answer) :
    roundsFit (VerifiableInference.Desc.K1.rounds Q) [seedsW Q, rvVals vals] = true := by
  have i1 : (Fmt.DeclaredRound.items { entry := seedEntry Q }).filter (· != .root) = [] := by
    simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, seedEntry]
  have i2 : (Fmt.DeclaredRound.items { entry := answerEntry Q }).filter (· != .root) =
      List.replicate Q.answers .answer := by
    simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, answerEntry]
  have n1 : drawsMarkedNonzeroHaveNonzeroWords { entry := seedEntry Q } (seedsW Q) = true := by
    have hk : Fmt.kindOf (seedEntry Q).name = some .seeds := by
      show Fmt.kindOf "SEND seed" = some .seeds
      decide
    unfold drawsMarkedNonzeroHaveNonzeroWords
    rw [hk, Option.any_some, List.all_eq_true]
    intro x hx
    have h2 : x.2 ∈ List.replicate (Q.seeds * (Q.coordinates + 1)) ((1, 0, 0) : Fmt.Ext) :=
      (List.of_mem_zip (a := x.1) (b := x.2) hx).2
    rw [List.eq_of_mem_replicate h2]
    simp
  have n2 : drawsMarkedNonzeroHaveNonzeroWords { entry := answerEntry Q } (rvVals vals) = true := by
    obtain ⟨k, hk⟩ : ∃ k, Fmt.kindOf (answerEntry Q).name = some k := by
      show ∃ k, Fmt.kindOf "SEND answer" = some k
      exact Option.isSome_iff_exists.1 (by decide)
    unfold drawsMarkedNonzeroHaveNonzeroWords
    rw [hk, Option.any_some]
    simp [rvVals]
  simp only [VerifiableInference.Desc.K1.rounds, roundsFit, Bool.and_eq_true, beq_iff_eq,
    i1, i2, n1, n2]
  simpa [rvElems, rvVals, seedEntry, answerEntry] using hv

/-- As many answers 0 as are asked. -/
theorem items_zero (n : Nat) :
    (List.replicate n (Fmt.ItemValue.answer (0, 0, 0))).map itemOf = List.replicate n .answer := by
  rw [List.map_replicate]
  rfl

/-! ## The committed table's rows: 0 -/

/-- Each answer of the key is its row's own, at rows that are 0. -/
theorem rec_zero (s : IndexShape) : ∀ x ∈ (keyW s).seeds.zipIdx, ∀ r < s.rows,
    RowAnswer s (x.1.z.map rdE.val) (rdE.val x.1.beta) (fun t => rdE.val (thetaE t)) x.2
      (fun _ => (0 : Cb.Gl.E)) (rdE.val ((keyW s).record.getD (r * s.answers + x.2) zeroE)) := by
  intro x _ r _
  have e : (keyW s).record.getD (r * s.answers + x.2) zeroE = zeroE := by
    unfold keyW
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  unfold RowAnswer
  rw [e, rdE.zero]
  simp

/-- Each opened column holds the rows' own symbols, at rows that are 0. -/
theorem col_zero (p : Par) (r : Fmt.RoundView) : ∀ x ∈ locations p r, ∀ col,
    (colsW p.S.fold.index.rows).lookup x = some col → ∀ q < p.S.fold.index.rows,
      rdE.val (ofF (col.toArray.getD q 0)) = genK rdE p.S.fold x (fun _ => (0 : Cb.Gl.E)) := by
  intro x _ col hc q _
  have hcol : col = List.replicate p.S.fold.index.rows 0 := by
    unfold colsW at hc
    simp only [List.lookup_cons, List.lookup_nil] at hc
    split at hc
    · exact (Option.some.inj hc).symm
    · cases hc
  have e : col.toArray.getD q 0 = 0 := by
    rw [hcol]
    simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_replicate]
    split <;> rfl
  rw [e]
  unfold genK
  simp only [mul_zero, Finset.sum_const_zero, add_zero]
  exact rdE.zero

/-! ## The view -/

/-- **Rounds8 at the witness.** -/
theorem rounds8_met (P : P14) (sentU : Array OracleNotice) (layO : TreeLay)
    (hP : PlanFacts P.par P.codes sentU layO) (hBU : planOkOwn (parU P sentU) = true)
    (hBO : planOkOwn (parO P) = true) :
    Rounds8 P.par (parU P sentU) (parO P) (pointW P) (seedsW (parU P sentU))
      (zerosW (parU P sentU)) (rvPoss P.par.S.fold.columns) (seedsW (parO P)) (zerosW (parO P))
      (zetaW P) (rvVals [.e (0, 0, 0)]) (colsW P.par.S.fold.index.rows) := by
  have hlen : P.codes.lengthsOk = true := hP.lengths
  have fU := fits_send (parU P sentU) _ (items_zero (parU P sentU).answers)
  have fO := fits_send (parO P) _ (items_zero (parO P).answers)
  refine ⟨?_, seeds_nz _ _ _ fU, fitB_of_rounds _ _ _ hBU hlen fU, ?_, seeds_nz _ _ _ fO,
    fitB_of_rounds _ _ _ hBO hlen fO, ?_, ⟨_, rfl⟩⟩
  · simp [drawn, rvElems]
  · intro x hx
    have hx0 : x = 0 := List.eq_of_mem_replicate hx
    subst hx0
    exact ⟨List.replicate P.par.S.fold.index.rows 0, by simp [colsW], List.length_replicate⟩
  · simp [drawn, rvElems]

/-- Returned at the witness's key, challenges and column. r2b, r5b: the two sendings' second rounds;
r8: the round of "SPLIT". -/
abbrev ReturnedW (P : P14) (sentU : Array OracleNotice) (r2b r5b r8 : Fmt.RoundView)
    (rs3 rs6 : List Fmt.RoundView) (d1 d2 d3 d4 d5 d6 d7 d8 : St) (x2 x5 : DState (Array Nat))
    (ids2 ids5 : Array Nat) : Prop :=
  Returned P sentU (firstW P) (pointW P) (seedsW (parU P sentU)) r2b (rvPoss P.par.S.fold.columns)
    (seedsW (parO P)) r5b (zetaW P) r8 (colsW P.par.S.fold.index.rows) rs3 rs6
    d1 d2 d3 d4 d5 d6 d7 d8 x2 x5 ids2 ids5

/-- **The eight return at the witness**: a view of zeros, no honest prover's. -/
theorem returned_met (P : P14) (sentU : Array OracleNotice) (layO : TreeLay)
    (hP : PlanFacts P.par P.codes sentU layO) (hBU : planOkOwn (parU P sentU) = true)
    (hBO : planOkOwn (parO P) = true) (rs3 rs6 : List Fmt.RoundView) :
    ∃ d1 d2 d3 d4 d5 d6 d7 d8 x2 x5 ids2 ids5,
      ReturnedW P sentU (zerosW (parU P sentU)) (zerosW (parO P)) (rvVals [.e (0, 0, 0)]) rs3 rs6
        d1 d2 d3 d4 d5 d6 d7 d8 x2 x5 ids2 ids5 :=
  eight_return P sentU layO hP (firstW P) rfl rfl (key_fits _) (key_beta _) _ _ _ _ _ _ _ _ _
    (rounds8_met P sentU layO hP hBU hBO) rs3 rs6

/-! ## At the two typed shapes -/

/-- The two sendings pass their kind's test on the plan: the sub-protocols' own tests on the plan
ask it. -/
theorem planOwn_of {f : Nat} {P : P14} {W : Rounds} {sentU : Array OracleNotice}
    (hC : K14Cond f P W) (hU : withU P.S = some sentU) :
    planOkOwn (parU P sentU) = true ∧ planOkOwn (parO P) = true := by
  obtain ⟨bs, hb, _, hplan, _⟩ := hC.blocks
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hb
  obtain ⟨sentU', hU', rfl⟩ := hb
  obtain rfl : sentU = sentU' := Option.some.inj (hU.symm.trans hU')
  have p2 := hplan _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have p5 := hplan _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self))))
  have q2 : ((VerifiableInference.Desc.Block.inside _ _ _).planOk &&
      VerifiableInference.OnPublicFiles.OkD.At.sending P.codes
        (VerifiableInference.OnPublicFiles.OkD.At.withU P.S) && _) = true := p2
  have q5 : ((VerifiableInference.Desc.Block.inside _ _ _).planOk &&
      VerifiableInference.OnPublicFiles.OkD.At.sending P.codes (linMessageOmega P.S) && _) = true := p5
  simp only [Bool.and_eq_true] at q2 q5
  have u2 : (planOkOwn (parU P sentU) && (VerifiableInference.Desc.K1.sendOwn (Cl := Unit)
      (parU P sentU)).claims.isEmpty && (VerifiableInference.Desc.K1.sendOwn (Cl := Unit)
      (parU P sentU)).after.isEmpty) = true := q2.1.1
  have u5 : (planOkOwn (parO P) && (VerifiableInference.Desc.K1.sendOwn (Cl := Unit)
      (parO P)).claims.isEmpty && (VerifiableInference.Desc.K1.sendOwn (Cl := Unit)
      (parO P)).after.isEmpty) = true := q5.1.1
  simp only [Bool.and_eq_true] at u2 u5
  exact ⟨u2.1.1, u5.1.1⟩

/-- **At the typed sizes of a key of full size the eight return at the witness**: a view of
zeros. -/
theorem returned_key : ∃ sentU : Array OracleNotice, withU keyFull.once.shape = some sentU ∧
    ∀ (item : Nat) (bp : List (Nat × Nat)), bp ≠ [] → ∀ rs3 rs6 : List Fmt.RoundView,
    ∃ d1 d2 d3 d4 d5 d6 d7 d8 x2 x5 ids2 ids5,
      ReturnedW ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩ sentU
        (zerosW (parU ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩ sentU))
        (zerosW (parO ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩))
        (rvVals [.e (0, 0, 0)]) rs3 rs6 d1 d2 d3 d4 d5 d6 d7 d8 x2 x5 ids2 ids5 := by
  obtain ⟨sentU, layO, hf⟩ := planFacts_key
  refine ⟨sentU, (hf 0 [(0, 0)] (by simp)).goes, fun item bp hbp rs3 rs6 => ?_⟩
  obtain ⟨hBU, hBO⟩ := planOwn_of (Law.k14_key item bp hbp) (hf item bp hbp).goes
  exact returned_met _ sentU layO (hf item bp hbp) hBU hBO rs3 rs6

/-- **At the typed sizes over a proof file's own codes the eight return at the witness**: a view of
zeros. -/
theorem returned_real : ∃ (x : LinSized) (sentU : Array OracleNotice),
    realSized = some (x, codesFull2) ∧ withU x.shape = some sentU ∧
    ∀ (item : Nat) (bp : List (Nat × Nat)), bp ≠ [] → ∀ rs3 rs6 : List Fmt.RoundView,
    ∃ d1 d2 d3 d4 d5 d6 d7 d8 x2 x5 ids2 ids5,
      ReturnedW ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩ sentU
        (zerosW (parU ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩ sentU))
        (zerosW (parO ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩))
        (rvVals [.e (0, 0, 0)]) rs3 rs6 d1 d2 d3 d4 d5 d6 d7 d8 x2 x5 ids2 ids5 := by
  obtain ⟨x, sentU, layO, a1, _, hf⟩ := planFacts_real
  obtain ⟨x', b1, _, hC⟩ := Law.k14_real
  obtain rfl : x = x' := congrArg Prod.fst (Option.some.inj (a1.symm.trans b1))
  refine ⟨x, sentU, a1, (hf 0 [(0, 0)] (by simp)).goes, fun item bp hbp rs3 rs6 => ?_⟩
  obtain ⟨hBU, hBO⟩ := planOwn_of (hC item bp hbp) (hf item bp hbp).goes
  exact returned_met _ sentU layO (hf item bp hbp) hBU hBO rs3 rs6

end Desc.K14.Honest

#print axioms Desc.K14.Honest.key_fits
#print axioms Desc.K14.Honest.key_beta
#print axioms Desc.K14.Honest.fits_send
#print axioms Desc.K14.Honest.items_zero
#print axioms Desc.K14.Honest.rec_zero
#print axioms Desc.K14.Honest.col_zero
#print axioms Desc.K14.Honest.rounds8_met
#print axioms Desc.K14.Honest.returned_met
#print axioms Desc.K14.Honest.planOwn_of
#print axioms Desc.K14.Honest.returned_key
#print axioms Desc.K14.Honest.returned_real
