-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/LayAgrees.lean
(kind K9): THEOREMS OF AGREEMENT, AT ALL ARGUMENTS: K9's OWN TEXT OF HOW THE
TERMS OF THE ONE EQUATION BECOME A ROW (Batch/Lay.lean) AGAINST verify-on-bytes's FUNCTIONS.
Tests and plain values, as equations:
  everyFrom_eq, everyBelow_eq   allFrom, allBelow (OnBytes/Model/FormF.lean)
  arrayLaid_eq, rowFormFits_eq  laidAs, rowFormOK (OnBytes/Model/Trees.lean)
  messageNow_eq                 ReqFrame.whereIs (OnBytes/Iop/Req.lean)
  noTwice_eq, tensorFits_eq     distinctNats, Tensor.ok (OnBytes/Iop/Tensor.lean)
  aligned_eq, blockFits_eq      laidAligned, laidBlockOk (OnBytes/Iop/ReqRows.lean)
Functions that can refuse, as equations between the own text's answer, its refusal's name forgotten
(Except.toOption), and the value of verify-on-bytes's function (all OnBytes/Iop/ReqRows.lean):
  aboveBlock_older   IndexWeights.above
  bitVar_older, bitVars_older   LaidDraft.pushBit, pushBits
  blockTensor_older  laidTensor
  blocksForm_older   laidForm
  termsRow_older     **(termsRow R.layout f S ts row).toOption = R.addTerms f S ts row**
  termsRow_ok        a yes of the own text is a yes of `addTerms`, with the same row.
Nothing is stricter and nothing looser. So every law that is proved of these functions holds
of K9's own text.

-/
import Johnson.Desc.First.Batch.Law.AddAgrees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open OnBytes.Params (LaidBlock ReqArray ReqLayout)
open VerifiableInference.Desc.K9 (Ans everyFrom everyBelow arrayLaid rowFormFits messageNow aligned
  blockFits aboveBlock bitVar bitVars noTwice tensorFits blockTensor blocksForm termsRow)

/-! ## Tests and plain values -/

theorem everyFrom_eq (p : Nat → Bool) : ∀ count i, everyFrom p count i = allFrom p count i
  | 0, _ => rfl
  | n + 1, i => by rw [everyFrom, allFrom, everyFrom_eq p n (i + 1)]

theorem everyBelow_eq (n : Nat) (p : Nat → Bool) : everyBelow n p = allBelow n p :=
  everyFrom_eq p n 0

theorem arrayLaid_eq (c : ChainCheck) (born : Nat) (name : String) (R K : Nat) :
    arrayLaid c.rows.layout born name R K = laidAs c born name R K := rfl

theorem rowFormFits_eq (X : HTree) (r : HRow) : rowFormFits X r = rowFormOK X r := rfl

theorem messageNow_eq (f : ReqFrame) (born message : Nat) :
    messageNow f born message = f.whereIs born message := rfl

theorem noTwice_eq : ∀ l : List Nat, noTwice l = distinctNats l
  | [] => rfl
  | a :: l => by rw [noTwice, distinctNats, noTwice_eq l]

theorem tensorFits_eq (v : Tensor) : tensorFits v = v.ok := by
  unfold tensorFits Tensor.ok
  rw [noTwice_eq]

theorem aligned_eq (first bits : Nat) : aligned first bits = laidAligned first bits := rfl

theorem blockFits_eq (b : LaidBlock) (r p : Nat) : blockFits b r p = laidBlockOk b r p := rfl

/-! ## An answer with its refusal's name forgotten: more small laws -/

theorem toOption_pure {α : Type} (a : α) : (pure a : Ans α).toOption = some a := rfl

theorem toOption_there {α : Type} (n : String) (o : Option α) : (K9.there n o).toOption = o := by
  cases o <;> rfl

theorem toOption_map {α β : Type} (f : α → β) (x : Ans α) :
    (x.map f).toOption = x.toOption.map f := by
  cases x <;> rfl

/-! ## Functions that can refuse -/

theorem aboveBlock_older (w : IndexWeights) (first bits : Nat) :
    (aboveBlock w first bits).toOption = w.above first bits := by
  unfold aboveBlock IndexWeights.above IndexWeights.writtenOut
  cases w.values.isSome with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, if_false]
    rw [toOption_need]
    cases (decide (w.lo.size < 64) && first / 2 ^ w.lo.size != 0) <;> rfl

theorem bitVar_core (d : LaidDraft) (w : IndexWeights) (bit : Nat) :
    Except.toOption (if w.values.isSome then
        (pure { t := d.t.push oneE oneE, dense := d.dense ++ [(bit, d.t.vars)] } : Ans LaidDraft)
      else
        match w.lo[bit]?, w.hi[bit]? with
        | some l, some h => pure { d with t := d.t.push l h }
        | _, _ => .error "K9.weights-have-the-bit") =
      if w.writtenOut then some { t := d.t.push oneE oneE, dense := d.dense ++ [(bit, d.t.vars)] }
      else
        match w.lo[bit]?, w.hi[bit]? with
        | some l, some h => some { d with t := d.t.push l h }
        | _, _ => none := by
  unfold IndexWeights.writtenOut
  cases w.values.isSome with
  | true => rfl
  | false => cases w.lo[bit]? <;> cases w.hi[bit]? <;> rfl

theorem bitVar_older (d : LaidDraft) (b : LaidBlock) (onI onC : IndexWeights) (x : Nat) :
    (bitVar d b onI onC x).toOption = d.pushBit b onI onC x :=
  bitVar_core d _ _

theorem bitVars_older (b : LaidBlock) (onI onC : IndexWeights) :
    ∀ (xs : List Nat) (d : LaidDraft), (bitVars d b onI onC xs).toOption = d.pushBits b onI onC xs
  | [], _ => rfl
  | x :: xs, d => by
    rw [bitVars, LaidDraft.pushBits]
    show ((bitVar d b onI onC x) >>= fun e => bitVars e b onI onC xs).toOption = _
    rw [toOption_bind, bitVar_older]
    cases d.pushBit b onI onC x with
    | none => rfl
    | some e => exact bitVars_older b onI onC xs e

/-- The last test of blockTensor against laidTensor's. -/
theorem fits_last (u : Tensor) : Except.toOption
    (K9.need "K9.tensor-fits" (tensorFits u) >>= fun _ => (pure u : Ans Tensor)) =
    if u.ok then some u else none := by
  rw [toOption_need, tensorFits_eq]
  rfl

theorem blockTensor_older (b : LaidBlock) (R P : Nat) (onI onC : IndexWeights) (scalar : E) :
    (blockTensor b R P onI onC scalar).toOption = laidTensor b R P onI onC scalar := by
  unfold blockTensor laidTensor
  dsimp only
  simp only [toOption_need, blockFits_eq, IndexWeights.writtenOut, IndexWeights.ok]
  cases laidBlockOk b R P <;> cases (onI.values.isSome && onC.values.isSome) <;>
    cases (onI.lo.size == onI.hi.size) <;> cases (onC.lo.size == onC.hi.size) <;> try rfl
  simp only [Bool.not_true, Bool.not_false, Bool.and_true, Bool.or_self,
    Bool.false_eq_true, if_false, if_true, pure_bind]
  rw [toOption_bind, bitVars_older]
  cases LaidDraft.pushBits { t := { scalar := scalar } } b onI onC
      ((List.range b.rowBits).map (· + b.placeBits)) with
  | none => rfl
  | some d1 =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [toOption_bind, bitVars_older]
    cases LaidDraft.pushBits
        ⟨d1.t.insertChoice d1.t.vars (R - b.rowBits) (b.firstRow / 2 ^ b.rowBits), d1.dense⟩
        b onI onC (List.range b.placeBits) with
    | none => rfl
    | some d3 =>
      simp only [Option.bind_some]
      rw [toOption_bind, aboveBlock_older]
      cases onI.above b.firstI b.bitsI with
      | none => rfl
      | some aI =>
        simp only [Option.bind_some]
        rw [toOption_bind, aboveBlock_older]
        cases onC.above b.firstC b.bitsC with
        | none => rfl
        | some aC =>
          simp only [Option.bind_some]
          rcases Bool.eq_false_or_eq_true onI.values.isSome with hI | hI <;>
            simp only [hI, Bool.false_eq_true, if_false, if_true]
          · cases onI.values with
            | none =>
              dsimp only
              exact fits_last _
            | some values =>
              dsimp only
              cases d3.dense.isEmpty with
              | false =>
                simp only [Bool.false_eq_true, if_false]
                exact fits_last _
              | true =>
                simp only [if_true]
                rw [toOption_bind, toOption_map, toOption_there]
                cases values[b.firstI]? with
                | none => rfl
                | some v =>
                  simp only [Option.map_some, Option.bind_some]
                  exact fits_last _
          · cases onC.values with
            | none =>
              dsimp only
              exact fits_last _
            | some values =>
              dsimp only
              cases d3.dense.isEmpty with
              | false =>
                simp only [Bool.false_eq_true, if_false]
                exact fits_last _
              | true =>
                simp only [if_true]
                rw [toOption_bind, toOption_map, toOption_there]
                cases values[b.firstC]? with
                | none => rfl
                | some v =>
                  simp only [Option.map_some, Option.bind_some]
                  exact fits_last _

theorem blocksForm_older (blocks : List LaidBlock) (R P : Nat) (onI onC : IndexWeights)
    (scalar : E) : (blocksForm blocks R P onI onC scalar).toOption =
      laidForm blocks R P onI onC scalar := by
  unfold blocksForm laidForm
  exact foldlM_older (fun (f : Form) b => (blockTensor b R P onI onC scalar).map f.add)
    (fun (f : Form) b => (laidTensor b R P onI onC scalar).map f.add)
    (fun f b => by rw [toOption_map, blockTensor_older]) blocks {}

/-- **The terms as a row: the own text against `addTerms`, at all arguments.** -/
theorem termsRow_older (Rr : ReqRows) (f : ReqFrame) (S : Statement) :
    ∀ (ts : List ReqTerm) (row : OnBytes.Row),
      (termsRow Rr.layout f S ts row).toOption = Rr.addTerms f S ts row
  | [], _ => rfl
  | t :: ts, row => by
    rw [termsRow, ReqRows.addTerms, toOption_bind, toOption_there]
    show Option.bind (reqArray Rr.layout t.born t.array) _ = _
    cases reqArray Rr.layout t.born t.array with
    | none => rfl
    | some a =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [toOption_bind, toOption_there, messageNow_eq]
      cases f.whereIs t.born a.message with
      | none => rfl
      | some o =>
        simp only [Option.bind_some]
        rw [toOption_bind, blocksForm_older]
        cases laidForm a.blocks (S.rowBits o .main) (S.placeBits o .main) t.onRows t.onColumns
            t.scale with
        | none => rfl
        | some c =>
          simp only [Option.bind_some]
          exact termsRow_older Rr f S ts (row.addForm o c)

/-- A yes of the own text is a yes of `addTerms`, with the same row. -/
theorem termsRow_ok (Rr : ReqRows) (f : ReqFrame) (S : Statement) (ts : List ReqTerm)
    (row row' : OnBytes.Row) (h : termsRow Rr.layout f S ts row = .ok row') :
    Rr.addTerms f S ts row = some row' := by
  rw [← termsRow_older, h]
  rfl

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.everyBelow_eq
#print axioms VerifiableInference.Desc.K9L.tensorFits_eq
#print axioms VerifiableInference.Desc.K9L.aboveBlock_older
#print axioms VerifiableInference.Desc.K9L.bitVars_older
#print axioms VerifiableInference.Desc.K9L.blockTensor_older
#print axioms VerifiableInference.Desc.K9L.blocksForm_older
#print axioms VerifiableInference.Desc.K9L.termsRow_older
#print axioms VerifiableInference.Desc.K9L.termsRow_ok
