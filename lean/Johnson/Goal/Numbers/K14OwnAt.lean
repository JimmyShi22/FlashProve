-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/K14OwnAt.lean: of the shared chain's twelve blocks' own errors, in the ledger's
own terms (K14/Law/LedgerForms.lean: ownK, ownDs, errZero; Desc/Sound/SharedJointCountLedger.lean:
EachOwnBelow), every entry that falls to K14's files is a share of at most 2^-128 of the written
round's challenges, at the release's numbers: so, by the ledger's own rule (eachLawsBN_atCap), the
laws at these files' own errors are laws at the cap.

The ledger's users ask "EachOwnBelow 128 own 0 (the twelve pieces)" as a premise. ownK has K14's
files' four written counts at the blocks 2, 4, 5 and 7 (send o_u, LOC, send o_omega, LIN zeta),
zero at 3, 6, 8 and 11, and a letter, rest, at 0, 1, 9 and 10.
  errZero_below: no error is below every bound
  ownDs_below, ownK_below: at letters: from the four bricks, each asked only at the form of the
      stretch at which ownDs bears it
  seed_brick, pos_brick, vec_brick: the bricks: Err.Below of (seedMaps …).err, (posMaps …).err and
      (vecMaps …).err, from K1/Law/PowB.lean's powB and Johnson/Goal/Numbers/K14RoundsAt.lean's
      roundB
  Ties Wr k ds: the stretch's written rounds have the entries and kinds of the written list's
      rounds: at block 2 the round 1, at 4 the round 3, at 5 the round 4, at 7 the round 6
  OursBelow Q Wr sentU rad2 rad5: for every rest, every number k other than 0, 1, 9, 10 and every
      piece x with Ties Wr k x.ds: Err.Below (ownK … rest k x) (2⁻¹ ^ 128), at c2 | c5 the two
      places' coordinates, e2 | e5 := errPort there, e4 := (2 ^ logN - 2852142980 - 1) ^ columns, e7
      := kRow q ^ (kRow - 1): the lower bounds he2, he4, he5, he7 of share_filled and once_filled
      WITH EQUALITY
  eachOwnBelow_ours: so EachOwnBelow 128 (ownK … rest) 2 [x2, …, x8], and the entry at 11
  ours_le_cap, ours_le_err: so each such entry is at most the cap, and at most the piece's own error
      where that is the cap
  ours_real, ours_key: in a proof file, in a key file: there are the messages sent with o_u and the
      records' radii, with condPort at both places, such that OursBelow holds

What is not claimed. The entries at 0, 1, 9 and 10: other files' (at 1, "LIN point":
Johnson/Goal/Numbers/K14JointAt.lean's Point64 is a brick). That the typed numbers are the
parameters at a description's own place. The laws themselves. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Goal.Numbers.K14RoundsAt
import Johnson.Desc.K14.Law.LedgerForms
import Johnson.Desc.K1.Law.PowB
import Iop.ErrCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Params.Prices (AtRecord)
open Johnson.G (dryProofFull dryKeyFull codesFull2 sendsFullLit packFullLit)
open Iop Run OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block Wit)
open VerifiableInference.Desc.K1 (seedMaps seedMaps_ok condPort errPort seedEntry seed_draws radFrom
  realSized litAt powB powB_cmp nVals_seed seeds_pos PlaceOk)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open Lk6.AtPlan (keyFull)
open scoped ENNReal

variable {P₁ Cl Cells Tok : Type} {Fr : Frame}

/-! ## At letters -/

theorem errZero_below (ε : ℝ≥0∞) : ∀ s : Iop.Shape, Err.Below (errZero s) ε
  | [] => trivial
  | _ :: s => ⟨by simp, errZero_below ε s⟩

/-- **K14's files' own errors, by the block's number and the stretch's form.** -/
theorem ownDs_below (c2 e2 logN n e4 c5 e5 kRow e7 : ℕ) (ε : ℝ≥0∞) (k : ℕ) (ds : List RDT)
    (h2 : ∀ d₁ d₂, k = 2 → ds = [d₁, d₂] →
      Err.Below ((seedMaps d₁ d₂ c2).err ((e2, ()) : ℕ × Unit)) ε)
    (h4 : ∀ d, k = 4 → ds = [d] → Err.Below ((posMaps d logN n).err ((e4, ()) : ℕ × Unit)) ε)
    (h5 : ∀ d₁ d₂, k = 5 → ds = [d₁, d₂] →
      Err.Below ((seedMaps d₁ d₂ c5).err ((e5, ()) : ℕ × Unit)) ε)
    (h7 : ∀ d, k = 7 → ds = [d] → Err.Below ((vecMaps d kRow).err ((e7, ()) : ℕ × Unit)) ε) :
    Err.Below (ownDs c2 e2 logN n e4 c5 e5 kRow e7 k ds) ε := by
  unfold ownDs
  split
  · exact h2 _ _ rfl rfl
  · exact h4 _ rfl rfl
  · exact h5 _ _ rfl rfl
  · exact h7 _ rfl rfl
  · exact errZero_below ε _

theorem ownK_below (c2 e2 logN n e4 c5 e5 kRow e7 : ℕ)
    (rest : OwnErrs (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (ε : ℝ≥0∞) (k : ℕ)
    (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (hk : ¬ (k < 2 ∨ k = 9 ∨ k = 10))
    (h : Err.Below (ownDs c2 e2 logN n e4 c5 e5 kRow e7 k x.ds) ε) :
    Err.Below (ownK c2 e2 logN n e4 c5 e5 kRow e7 rest k x) ε := by
  unfold ownK
  rw [if_neg hk]
  exact h

/-! ## The bricks -/

theorem seed_brick (P : VerifiableInference.Desc.K1.Par) (h1 : P.seeds = 1) (rad : ℕ → ℕ)
    (h : powB P rad 128 = true) (d₁ d₂ : RDT) (he : d₁.entry = seedEntry P)
    (hk : d₁.kind = .seeds) :
    Err.Below ((seedMaps d₁ d₂ P.coordinates).err ((errPort P rad, ()) : ℕ × Unit))
      ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := seed_draws P h1 d₁ he hk
  refine Maps.below_pow (seedMaps d₁ d₂ P.coordinates) (seedMaps_ok d₂ a1 a2 a3 a4 a5)
    ((errPort P rad, ()) : ℕ × Unit) ⟨⟨errPort P rad,
      Fintype.card ((Fin P.coordinates → GE) × GEˣ), seeds_pos P.coordinates, ?_,
      powB_cmp P h1 rad 128 h d₁ he hk⟩, trivial⟩
  rw [nVals_seed P h1 d₁ he hk]

theorem pos_brick (d : RDT) (a t e : ℕ) {ns : ℕ} (hd : SendsDraws (toRD d) ns 0 t a)
    (h : roundB d.entry d.kind e 128 = true) :
    Err.Below ((posMaps d a t).err ((e, ()) : ℕ × Unit)) ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  unfold roundB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact Maps.below_pow (posMaps d a t) (posMaps_ok hd) ((e, ()) : ℕ × Unit)
    ⟨⟨e, nVals (Fmt.dsOf d.entry d.kind), h.1, Nat.le_refl _, h.2⟩, trivial⟩

theorem vec_brick (d : RDT) (n e : ℕ) {ns a : ℕ} (hd : SendsDraws (toRD d) ns n 0 a)
    (h : roundB d.entry d.kind e 128 = true) :
    Err.Below ((vecMaps d n).err ((e, ()) : ℕ × Unit)) ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  unfold roundB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact Maps.below_pow (vecMaps d n) (vecMaps_ok hd) ((e, ()) : ℕ × Unit)
    ⟨⟨e, nVals (Fmt.dsOf d.entry d.kind), h.1, Nat.le_refl _, h.2⟩, trivial⟩

/-! ## The member -/

/-- The stretch's written rounds have the entries and kinds of the written list's rounds. -/
def Ties (Wr : Rounds) (k : ℕ) (ds : List RDT) : Prop :=
  (∀ d₁ d₂, k = 2 → ds = [d₁, d₂] → atW Wr 1 = some (d₁.entry, d₁.kind)) ∧
  (∀ d, k = 4 → ds = [d] → atW Wr 3 = some (d.entry, d.kind)) ∧
  (∀ d₁ d₂, k = 5 → ds = [d₁, d₂] → atW Wr 4 = some (d₁.entry, d₁.kind)) ∧
  ∀ d, k = 7 → ds = [d] → atW Wr 6 = some (d.entry, d.kind)

/-- K14's files' own errors at the parameters Q, at the laws' own lower bounds. -/
noncomputable abbrev ownAt (Q : P14) (sentU : Array OracleNotice) (rad2 rad5 : ℕ → ℕ)
    (rest : OwnErrs (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) :
    OwnErrs (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT) :=
  ownK (parU Q sentU).coordinates (errPort (parU Q sentU) rad2) Q.S.fold.index.code.logN
    Q.S.fold.columns ((2 ^ Q.S.fold.index.code.logN - recordRadius - 1) ^ Q.S.fold.columns)
    (parO Q).coordinates (errPort (parO Q) rad5) Q.S.kRow
    (Q.S.kRow * Fintype.card GE ^ (Q.S.kRow - 1)) rest

/-- **Every entry that falls to K14's files is below 2^-128.** -/
def OursBelow (Q : P14) (Wr : Rounds) (sentU : Array OracleNotice) (rad2 rad5 : ℕ → ℕ) : Prop :=
  ∀ (P₁ Cl Cells Tok : Type) (Fr : Frame)
    (rest : OwnErrs (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (k : ℕ)
    (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)),
    ¬ (k < 2 ∨ k = 9 ∨ k = 10) → Ties Wr k x.ds →
      Err.Below (ownAt Q sentU rad2 rad5 rest k x) ((2 : ℝ≥0∞)⁻¹ ^ 128)

/-- So the ledger's clause on the blocks 2 to 8, and the entry at 11. -/
theorem eachOwnBelow_ours {Q : P14} {Wr : Rounds} {sentU : Array OracleNotice} {rad2 rad5 : ℕ → ℕ}
    (h : OursBelow Q Wr sentU rad2 rad5)
    (rest : OwnErrs (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (x2 x3 x4 x5 x6 x7 x8 x11 : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (t2 : Ties Wr 2 x2.ds) (t4 : Ties Wr 4 x4.ds) (t5 : Ties Wr 5 x5.ds) (t7 : Ties Wr 7 x7.ds) :
    EachOwnBelow 128 (ownAt Q sentU rad2 rad5 rest) 2 [x2, x3, x4, x5, x6, x7, x8] ∧
      Err.Below (ownAt Q sentU rad2 rad5 rest 11 x11) ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have free : ∀ (k : ℕ) (ds : List RDT), k ≠ 2 → k ≠ 4 → k ≠ 5 → k ≠ 7 → Ties Wr k ds :=
    fun k ds a b c d => ⟨fun _ _ e => absurd e a, fun _ e => absurd e b, fun _ _ e => absurd e c,
      fun _ e => absurd e d⟩
  exact ⟨⟨h _ _ _ _ _ rest 2 x2 (by decide) t2,
    h _ _ _ _ _ rest 3 x3 (by decide) (free 3 _ (by decide) (by decide) (by decide) (by decide)),
    h _ _ _ _ _ rest 4 x4 (by decide) t4, h _ _ _ _ _ rest 5 x5 (by decide) t5,
    h _ _ _ _ _ rest 6 x6 (by decide) (free 6 _ (by decide) (by decide) (by decide) (by decide)),
    h _ _ _ _ _ rest 7 x7 (by decide) t7,
    h _ _ _ _ _ rest 8 x8 (by decide) (free 8 _ (by decide) (by decide) (by decide) (by decide)),
    trivial⟩,
    h _ _ _ _ _ rest 11 x11 (by decide)
      (free 11 _ (by decide) (by decide) (by decide) (by decide))⟩

/-- **At the cap**, entry by entry: two calls (Iop/ErrCap.lean: Err.le_cap_of_below_inv;
the ledger's le_err_of_capped). -/
theorem ours_le_cap {Q : P14} {Wr : Rounds} {sentU : Array OracleNotice} {rad2 rad5 : ℕ → ℕ}
    (h : OursBelow Q Wr sentU rad2 rad5)
    (rest : OwnErrs (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (k : ℕ)
    (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (hk : ¬ (k < 2 ∨ k = 9 ∨ k = 10)) (ht : Ties Wr k x.ds) :
    Err.le (ownAt Q sentU rad2 rad5 rest k x) (Err.cap 128 (uLT (ckP .two) x.ds)) :=
  Err.le_cap_of_below_inv 128 _ (h _ _ _ _ _ rest k x hk ht)

/-- Where the piece's own errors are the cap: K14's files' own errors are at most the piece's. -/
theorem ours_le_err {Q : P14} {Wr : Rounds} {sentU : Array OracleNotice} {rad2 rad5 : ℕ → ℕ}
    (h : OursBelow Q Wr sentU rad2 rad5)
    (rest : OwnErrs (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (k : ℕ)
    (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (hk : ¬ (k < 2 ∨ k = 9 ∨ k = 10)) (ht : Ties Wr k x.ds)
    (hc : x.err = Err.cap 128 (uLT (ckP .two) x.ds)) :
    Err.le (ownAt Q sentU rad2 rad5 rest k x) x.err :=
  le_err_of_capped 128 x _ hc (h _ _ _ _ _ rest k x hk ht)

/-- The two places do not hang on the item or on the messages fixed before the point. -/
theorem parU_free (set : Setting) (scope : Scope) (codes : Codes) (S : LinShape) (item : ℕ)
    (bp : List (ℕ × ℕ)) (sent : Array OracleNotice) :
    parU ⟨set, scope, codes, S, item, bp⟩ sent = parU ⟨set, scope, codes, S, 0, [(1, 0)]⟩ sent :=
  rfl

theorem parO_free (set : Setting) (scope : Scope) (codes : Codes) (S : LinShape) (item : ℕ)
    (bp : List (ℕ × ℕ)) :
    parO ⟨set, scope, codes, S, item, bp⟩ = parO ⟨set, scope, codes, S, 0, [(1, 0)]⟩ := rfl

/-- The test with code on the two sendings: the written rounds 1 and 4 are their rounds of seeds,
and the comparison powB holds at 128 at the records' radii. -/
def sendsLB (fl : ℕ) (Q : P14) (Wr : Rounds) : Bool :=
  (withU Q.S).all (fun s => decide (atW Wr 1 = some (seedEntry (parU Q s), .seeds))) &&
  decide (atW Wr 4 = some (seedEntry (parO Q), .seeds)) &&
  ((litAt sendsFullLit packFullLit fl 1)[0]?).all (fun y => (withU Q.S).all fun s =>
    powB (parU Q s) (radFrom (parU Q s) y.2.l) 128) &&
  ((litAt sendsFullLit packFullLit fl 1)[1]?).all fun y =>
    powB (parO Q) (radFrom (parO Q) y.2.l) 128

/-- **From the conditions and the two tests.** -/
theorem ours_at {fl work : ℕ} {set : Setting} {scope : Scope} {codes : Codes} {S : LinShape}
    {Wr : Rounds} (item : ℕ) (bp : List (ℕ × ℕ))
    (hc : K14Cond fl ⟨set, scope, codes, S, item, bp⟩ Wr)
    (hR : k14RB S Wr recordRadius cMax work = true)
    (hs : sendsLB fl ⟨set, scope, codes, S, 0, [(1, 0)]⟩ Wr = true) :
    ∃ (sentU : Array OracleNotice) (rad2 rad5 : ℕ → ℕ), withU S = some sentU ∧
      condPort (parU ⟨set, scope, codes, S, item, bp⟩ sentU) rad2 = true ∧
      condPort (parO ⟨set, scope, codes, S, item, bp⟩) rad5 = true ∧
      OursBelow ⟨set, scope, codes, S, item, bp⟩ Wr sentU rad2 rad5 := by
  obtain ⟨sentU, hU, ⟨yU, hrU, -, hCU⟩, h1U⟩ := hc.sendU
  obtain ⟨⟨yO, hrO, -, hCO⟩, h1O⟩ := hc.sendO
  have hU' : withU S = some sentU := hU
  unfold sendsLB at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨s1, s2⟩, s3⟩, s4⟩ := hs
  rw [hU', Option.all_some] at s1
  rw [hrU, Option.all_some, hU', Option.all_some] at s3
  rw [hrO, Option.all_some] at s4
  have s1' := of_decide_eq_true s1
  have s2' := of_decide_eq_true s2
  unfold k14RB at hR
  simp only [Bool.and_eq_true] at hR
  obtain ⟨⟨-, r3⟩, r6⟩ := hR
  refine ⟨sentU, _, _, hU', hCU, hCO, ?_⟩
  intro P₁ Cl Cells Tok Fr rest k x hk ht
  refine ownK_below _ _ _ _ _ _ _ _ _ rest _ k x hk (ownDs_below _ _ _ _ _ _ _ _ _ _ k x.ds
    (fun d₁ d₂ e1 e2 => ?_) (fun d e1 e2 => ?_) (fun d₁ d₂ e1 e2 => ?_) (fun d e1 e2 => ?_))
  · have e := Option.some.inj ((ht.1 d₁ d₂ e1 e2).symm.trans s1')
    rw [parU_free set scope codes S item bp sentU]
    exact seed_brick _ h1U _ s3 d₁ d₂ (congrArg Prod.fst e) (congrArg Prod.snd e)
  · have w := ht.2.1 d e1 e2
    rw [w] at r3
    simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at r3
    obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, -⟩, a6⟩ := r3
    have sd := sends_of d a1
    rw [a2, a3, a4] at sd
    exact pos_brick d _ _ _ sd a6
  · have e := Option.some.inj ((ht.2.2.1 d₁ d₂ e1 e2).symm.trans s2')
    rw [parO_free set scope codes S item bp]
    exact seed_brick _ h1O _ s4 d₁ d₂ (congrArg Prod.fst e) (congrArg Prod.snd e)
  · have w := ht.2.2.2 d e1 e2
    rw [w] at r6
    simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at r6
    obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, -⟩, a5⟩ := r6
    have sd := sends_of d a1
    rw [a2, a3] at sd
    refine vec_brick d _ _ sd ?_
    rw [card_GE_num]
    exact a5

/-! ## A proof file, a key file -/

theorem real_testL : (realSized.any fun p =>
    sendsLB 2 ⟨recordSet, .shared, p.2, p.1.shape, 0, [(1, 0)]⟩ dryProofFull.2.1) = true := by
  decide +kernel

theorem key_testL :
    sendsLB 0 ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, 0, [(1, 0)]⟩ dryKeyFull.2.1 =
      true := by
  decide +kernel

/-- What is had at parameters Q and a written list. -/
def OursAt (Q : P14) (Wr : Rounds) : Prop :=
  ∃ (sentU : Array OracleNotice) (rad2 rad5 : ℕ → ℕ), withU Q.S = some sentU ∧
    condPort (parU Q sentU) rad2 = true ∧ condPort (parO Q) rad5 = true ∧
    OursBelow Q Wr sentU rad2 rad5

/-- **In a proof file.** -/
theorem ours_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧ AtRecord x ∧
    ∀ (item : ℕ) (bp : List (ℕ × ℕ)), bp ≠ [] →
      OursAt ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩ dryProofFull.2.1 := by
  obtain ⟨x, a1, a2, a3⟩ := k14_real
  have hR := real_testR
  have hL := real_testL
  rw [a1, Option.any_some] at hR hL
  exact ⟨x, a1, a2, fun item bp hbp => ours_at item bp (a3 item bp hbp) hR hL⟩

/-- **In a key file.** -/
theorem ours_key (item : ℕ) (bp : List (ℕ × ℕ)) (hbp : bp ≠ []) :
    OursAt ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩ dryKeyFull.2.1 :=
  ours_at item bp (k14_key item bp hbp) key_testR key_testL

end Desc.K14.Law
