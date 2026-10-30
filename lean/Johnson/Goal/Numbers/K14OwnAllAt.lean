-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/K14OwnAllAt.lean: the shared chain's own errors as ONE function over all twelve
blocks, and the ledger's clause on them (Desc/Sound/SharedJointCountLedger.lean: EachOwnBelow 128)
over the WHOLE list, at the release's numbers.

Johnson/Goal/Numbers/K14OwnAt.lean proves the ledger's clause at the entries 2 to 8 and 11, from the
stretches' ties to the written list (`eachOwnBelow_ours`; `ours_real`, `ours_key`), and leaves a
letter, rest, at 0, 1, 9 and 10. Here the letter is laid:
  at 1, "LIN point": ownPt S N: ONE list: the key's part once and a slot's part N times: (vecMaps d
      kCol).err (efReal q ^ kLo + N (kCol q ^ (kCol - 1)), ())
  at 9 and 10, the two proximity tests: two letters r9, r10, functions of the stretch: another
      kind's
  at 0, the front, and wherever a stretch has another form: no error
  restAll, ownAll: the function
  own_one: at a stretch of one round the entry at 1 IS Err.add εK (Err.times N εO), εK and εO the
      two lists at which the law of that block is stated (Johnson/Goal/Numbers/K14PointCap.lean)
  leadsBN_own_one: so from LeadsB at these two lists: LeadsBN for N slots at the entry itself
  ownPt_below: the entry at 1 is below 2^-128, for every N ≤ 64, at the written round
  eachOwnBelow_all: EachOwnBelow 128 (ownAll …) 0 [x0, …, x11], from the ties of the stretches to
      the written list and from Err.Below of r9 and r10 at their stretches
  AllAt, all_real, all_key: in a proof file, in a key file

What is not claimed. THE LAWS at these errors: at 0, 3, 6, 8 and 11 they are taken as hypotheses AT
ERROR 0.
Err.Below of r9 and r10: a premise. That 64 is the plan's number of requests. What the heads of
Johnson/Goal/Numbers/K14OwnAt.lean and K14PointCap.lean do not claim. Nothing on soundness of a
verifier, on an honest prover or on hiding.

-/
import Johnson.Goal.Numbers.K14OwnAt
import Johnson.Goal.Numbers.K14PointCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Params.Prices OnBytes.Plan OnBytes.Slice Desc.Plain
open Johnson.G
open Iop Run OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block Wit)
open VerifiableInference.Desc.K1 (condPort realSized)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open Lk6.AtPlan (keyFull)
open scoped ENNReal

variable {P₁ Cl Cells Tok : Type} {Fr : Frame}

/-- The entry at "LIN point": one list. -/
noncomputable def ownPt (S : LinShape) (N : ℕ) : (ds : List RDT) → Err (uLT (ckP .two) ds)
  | [d] => (vecMaps d S.kCol).err
      ((efReal * Fintype.card GE ^ S.kLo + N * (S.kCol * Fintype.card GE ^ (S.kCol - 1)), ()) :
        ℕ × Unit)
  | _ => errZero _

/-- What stands at 0, 1, 9 and 10. -/
noncomputable def restAll (S : LinShape) (N : ℕ)
    (r9 r10 : (ds : List RDT) → Err (uLT (ckP .two) ds)) :
    OwnErrs (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT) := fun k x =>
  if k = 1 then ownPt S N x.ds else if k = 9 then r9 x.ds else if k = 10 then r10 x.ds
  else errZero _

/-- **The shared chain's own errors, all twelve.** -/
noncomputable abbrev ownAll (Q : P14) (sentU : Array OracleNotice) (rad2 rad5 : ℕ → ℕ) (N : ℕ)
    (r9 r10 : (ds : List RDT) → Err (uLT (ckP .two) ds)) :
    OwnErrs (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT) :=
  ownAt Q sentU rad2 rad5 (restAll Q.S N r9 r10)

section
variable (Q : P14) (sentU : Array OracleNotice) (rad2 rad5 : ℕ → ℕ) (N : ℕ)
  (r9 r10 : (ds : List RDT) → Err (uLT (ckP .two) ds))
  (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))

theorem ownAll_zero : ownAll Q sentU rad2 rad5 N r9 r10 0 x = errZero _ := rfl

theorem ownAll_one : ownAll Q sentU rad2 rad5 N r9 r10 1 x = ownPt Q.S N x.ds := rfl

theorem ownAll_nine : ownAll Q sentU rad2 rad5 N r9 r10 9 x = r9 x.ds := rfl

theorem ownAll_ten : ownAll Q sentU rad2 rad5 N r9 r10 10 x = r10 x.ds := rfl

end

/-- **The entry at 1 is the key's list and N times a slot's.** -/
theorem own_one (S : LinShape) (N : ℕ) (d : RDT) :
    ownPt S N [d] =
      Err.add ((vecMaps d S.kCol).err ((efReal * Fintype.card GE ^ S.kLo, ()) : ℕ × Unit))
        (Err.times N ((vecMaps d S.kCol).err
          ((S.kCol * Fintype.card GE ^ (S.kCol - 1), ()) : ℕ × Unit))) :=
  (err_add_times d S.kCol _ _ N).symm

/-- **From the law in two parts to the law for N slots at the entry itself.** K: any reduction over
the one written round. -/
theorem leadsBN_own_one (S : LinShape) (N : ℕ) (d : RDT) {A B κ : Type} (K : Reduction A B)
    (hs : K.shape = uLT (ckP .two) [d]) (key : A → κ) (on : A → Prop) (Q : A → B → Prop)
    (hL : K.LeadsB key on Q
      (hs ▸ (vecMaps d S.kCol).err ((efReal * Fintype.card GE ^ S.kLo, ()) : ℕ × Unit))
      (hs ▸ (vecMaps d S.kCol).err ((S.kCol * Fintype.card GE ^ (S.kCol - 1), ()) : ℕ × Unit))) :
    K.LeadsBN key on Q N (hs ▸ ownPt S N [d]) := by
  obtain ⟨sh, out⟩ := K
  dsimp only at hs
  subst hs
  refine ⟨_, _, ?_, hL⟩
  rw [own_one]
  exact Err.le_refl _

/-- **The entry at 1 is below 2^-128**, for every N ≤ 64, at the written round. -/
theorem ownPt_below {S : LinShape} {Wr : Rounds} {rad work : ℕ}
    (h : K14Rounds S Wr rad cMax work) (ht : pointNB S Wr cMax64 64 = true) (N : ℕ) (hN : N ≤ 64)
    (ds : List RDT) (hd : ∀ d, ds = [d] → atW Wr 0 = some (d.entry, d.kind)) :
    Err.Below (ownPt S N ds) ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  unfold ownPt
  split
  · rename_i d
    have hw := hd d rfl
    unfold pointNB at ht
    rw [hw, Option.any_some] at ht
    refine vec_brick d _ _ (h.point d hw).1 (roundB_mono ?_ ht)
    have h64 := efReal_le64
    rw [card_GE_num] at h64 ⊢
    exact count_mono efReal cMax64 cardGl S.kLo _ N h64 hN
  · exact errZero_below _ _

/-- **The ledger's clause over the whole list.** -/
theorem eachOwnBelow_all {Q : P14} {Wr : Rounds} {sentU : Array OracleNotice} {rad2 rad5 : ℕ → ℕ}
    {rad work : ℕ} (h : OursBelow Q Wr sentU rad2 rad5) (hr : K14Rounds Q.S Wr rad cMax work)
    (ht : pointNB Q.S Wr cMax64 64 = true) (N : ℕ) (hN : N ≤ 64)
    (r9 r10 : (ds : List RDT) → Err (uLT (ckP .two) ds))
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 :
      Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (t1 : ∀ d, x1.ds = [d] → atW Wr 0 = some (d.entry, d.kind))
    (t2 : Ties Wr 2 x2.ds) (t4 : Ties Wr 4 x4.ds) (t5 : Ties Wr 5 x5.ds) (t7 : Ties Wr 7 x7.ds)
    (h9 : Err.Below (r9 x9.ds) ((2 : ℝ≥0∞)⁻¹ ^ 128))
    (h10 : Err.Below (r10 x10.ds) ((2 : ℝ≥0∞)⁻¹ ^ 128)) :
    EachOwnBelow 128 (ownAll Q sentU rad2 rad5 N r9 r10) 0
      [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] := by
  obtain ⟨⟨a2, a3, a4, a5, a6, a7, a8, -⟩, a11⟩ :=
    eachOwnBelow_ours h (restAll Q.S N r9 r10) x2 x3 x4 x5 x6 x7 x8 x11 t2 t4 t5 t7
  exact ⟨errZero_below _ _, ownPt_below hr ht N hN x1.ds t1, a2, a3, a4, a5, a6, a7, a8, h9, h10,
    a11, trivial⟩

/-- What is had at parameters Q and a written list. -/
def AllAt (Q : P14) (Wr : Rounds) : Prop :=
  ∃ (sentU : Array OracleNotice) (rad2 rad5 : ℕ → ℕ), withU Q.S = some sentU ∧
    condPort (parU Q sentU) rad2 = true ∧ condPort (parO Q) rad5 = true ∧
    ∀ (P₁ Cl Cells Tok : Type) (Fr : Frame) (N : ℕ), N ≤ 64 →
    ∀ (r9 r10 : (ds : List RDT) → Err (uLT (ckP .two) ds))
      (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 :
        Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)),
      (∀ d, x1.ds = [d] → atW Wr 0 = some (d.entry, d.kind)) →
      Ties Wr 2 x2.ds → Ties Wr 4 x4.ds → Ties Wr 5 x5.ds → Ties Wr 7 x7.ds →
      Err.Below (r9 x9.ds) ((2 : ℝ≥0∞)⁻¹ ^ 128) → Err.Below (r10 x10.ds) ((2 : ℝ≥0∞)⁻¹ ^ 128) →
      EachOwnBelow 128 (ownAll Q sentU rad2 rad5 N r9 r10) 0
        [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11]

theorem allAt_of {Q : P14} {Wr : Rounds} {rad work : ℕ} (h : OursAt Q Wr)
    (hr : K14Rounds Q.S Wr rad cMax work) (ht : pointNB Q.S Wr cMax64 64 = true) :
    AllAt Q Wr := by
  obtain ⟨sentU, rad2, rad5, a1, a2, a3, a4⟩ := h
  exact ⟨sentU, rad2, rad5, a1, a2, a3,
    fun P₁ Cl Cells Tok Fr N hN r9 r10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t1 t2 t4 t5 t7 h9
        h10 =>
      eachOwnBelow_all a4 hr ht N hN r9 r10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t1 t2 t4 t5 t7
        h9 h10⟩

/-- **In a proof file.** -/
theorem all_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧ AtRecord x ∧
    ∀ (item : ℕ) (bp : List (ℕ × ℕ)), bp ≠ [] →
      AllAt ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩ dryProofFull.2.1 := by
  obtain ⟨x, a1, a2, a3⟩ := ours_real
  obtain ⟨x', b1, -, -, b4⟩ := k14_rounds_real
  obtain rfl : x = x' := congrArg Prod.fst (Option.some.inj (a1.symm.trans b1))
  have h := real_test64
  rw [a1, Option.any_some] at h
  exact ⟨x, a1, a2, fun item bp hbp => allAt_of (a3 item bp hbp) b4 h⟩

/-- **In a key file.** -/
theorem all_key (item : ℕ) (bp : List (ℕ × ℕ)) (hbp : bp ≠ []) :
    AllAt ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩ dryKeyFull.2.1 :=
  allAt_of (ours_key item bp hbp) k14_rounds_key key_test64

end Desc.K14.Law
