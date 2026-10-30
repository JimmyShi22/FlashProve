-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/HokFold.lean: the hypothesis `hok` of the gathering
(`owesS_frames`, GatherFrames.lean) from the lemmas on single cells. `hok` is the column `hR` at the
places that are not of the kind `frame`: an item that is open before a sub-protocol, is not closed
there and is not owed again there passes over it (`RidesPastAtS`, SharesS.lean), for every pair of
place and item that the table `rideOkF` (Law/NoHouse/RideOkFrame.lean) admits. The invariant's
`keeps` is `kpBy fHeadH` (FHeadH.lean). No definition.

  1  `foldEnds_full`, `foldEnds_control`   a closed test by Lean's kernel on the written lists:
     after a place of the kind K13 the item `pile` is not open, and before a place of the kind K2
     other than number 339 no item `constr m lookCallsHeard` is open. The negative test: with K12
     for K13 it fails
  2  `kinds_row`, `kinds_formsT`, `kinds_forms`, `kinds_wo`, `kinds_carry`, `kinds_pile`   what the
     table's lists of kinds say, as alternatives
  3  `head_hok`   the fold

Left as hypotheses of `head_hok`, three families of cells, each asked where the item is open before
the sub-protocol and is not closed there:
  * `hcar`: `carry m` at the places of the kinds K7 and K9;
  * `hwor`: `worth m k r` at the place of the kind K11;
  * `hf11`: `forms m k r` at the place of the kind K11. K11FormsCell.lean proves it where what is
    said before the chain is `SaidOk` and `P11` is the plan's own; `head_hok` is general in both.

Where the cells come from. CellsByKindB.lean, CellsByKindC.lean: `unmarked`, `pinI`, `pin`, `pinW`,
`constr`, `pile`, `row`. FHeadH.lean: `pile` at K2, K7, K12. K5CellsAll.lean: every item at K5.
FormsCellsWhole.lean: `forms` at K1, K3, K8. K4FormsTCell.lean, K6FormsTCell.lean: `formsT`.
CellsByKind.lean: `wo`. ConstrHeardCell.lean: `constr m lookCallsHeard` at number 339.
PinKeptCells.lean: `pinKept`.

Limits.
  * That `keeps` := `fHeadH` holds after a sub-protocol's accepting step is not proved here.
  * Nothing here shows that an item's statement holds at any state of a run.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.CellsByKindB
import Johnson.Desc.ProofFile.Honest.Thread.CellsByKindC
import Johnson.Desc.ProofFile.Honest.Thread.FHeadH
import Johnson.Desc.ProofFile.Honest.Thread.K5CellsAll
import Johnson.Desc.ProofFile.Honest.Thread.FormsCellsWhole
import Johnson.Desc.ProofFile.Honest.Thread.K4FormsTCell
import Johnson.Desc.ProofFile.Honest.Thread.K6FormsTCell
import Johnson.Desc.ProofFile.Honest.Thread.ConstrHeardCell
import Johnson.Desc.ProofFile.Honest.Thread.NoK14K15
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.RideOkFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item RowClass)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T parts4)

/-! ## 1 A closed test -/

set_option maxRecDepth 1000000 in
/-- After K13's place `pile` is not open; before K2's places other than number 339 no item
`constr m lookCallsHeard` is open. -/
theorem foldEnds_full :
    ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
      (!(p.kind == KindName.K13) ||
        !((IM.openAt P5J.At.links P5J.At.ps (b + 1)).contains Item.pile)) &&
      (!(p.kind == KindName.K2) || b == 339 ||
        (IM.openAt P5J.At.links P5J.At.ps b).all fun i =>
          match i with
          | .constr _ .lookCallsHeard => false
          | _ => true)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with K12 in the place of K13 the same test fails. -/
theorem foldEnds_control :
    ((List.range 358).all fun b => (P5J.At.ps[b]?).all fun p =>
      (!(p.kind == KindName.K12) ||
        !((IM.openAt P5J.At.links P5J.At.ps (b + 1)).contains Item.pile)) &&
      (!(p.kind == KindName.K2) || b == 339 ||
        (IM.openAt P5J.At.links P5J.At.ps b).all fun i =>
          match i with
          | .constr _ .lookCallsHeard => false
          | _ => true)) = false := by
  decide +kernel

/-- The test at a place of the kind K13. -/
theorem fold_k13 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K13) : Item.pile ∉ IM.openAt P5J.At.links P5J.At.ps (b + 1) := by
  have t := List.all_eq_true.1 foldEnds_full b (List.mem_range.2 hb)
  rw [hp, Option.all_some, hk] at t
  have t1 : (!((IM.openAt P5J.At.links P5J.At.ps (b + 1)).contains Item.pile)) = true :=
    (Bool.and_eq_true_iff.1 t).1
  intro hm
  rw [List.contains_iff_mem.2 hm] at t1
  exact absurd t1 (by decide)

/-- The test at a place of the kind K2. -/
theorem fold_k2 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K2) {m : Nat}
    (ho : Item.constr m .lookCallsHeard ∈ IM.openAt P5J.At.links P5J.At.ps b) : b = 339 := by
  have t := List.all_eq_true.1 foldEnds_full b (List.mem_range.2 hb)
  rw [hp, Option.all_some, hk] at t
  have t2 : (b == 339 ||
      (IM.openAt P5J.At.links P5J.At.ps b).all fun i =>
        match i with
        | .constr _ .lookCallsHeard => false
        | _ => true) = true := (Bool.and_eq_true_iff.1 t).2
  rcases Bool.or_eq_true_iff.1 t2 with e | e
  · exact eq_of_beq e
  · exact absurd (show false = true from List.all_eq_true.1 e _ ho) (by decide)

/-! ## 2 The table's lists of kinds -/

theorem kinds_row (κ : KindName) :
    [KindName.K1, .K3, .K4, .K5, .K6, .K8, .K9, .K11, .frame].contains κ = true →
      κ ≠ KindName.frame →
      κ = .K1 ∨ (κ = .K3 ∨ κ = .K4 ∨ κ = .K6 ∨ κ = .K8) ∨ κ = .K5 ∨ κ = .K9 ∨ κ = .K11 := by
  cases κ <;> decide

theorem kinds_formsT (κ : KindName) :
    [KindName.K4, .K5, .K6].contains κ = true → κ = .K4 ∨ κ = .K5 ∨ κ = .K6 := by
  cases κ <;> decide

theorem kinds_forms (κ : KindName) :
    [KindName.K1, .K3, .K8, .K11].contains κ = true →
      κ = .K1 ∨ κ = .K3 ∨ κ = .K8 ∨ κ = .K11 := by
  cases κ <;> decide

theorem kinds_wo (κ : KindName) :
    [KindName.K1, .K3, .K8, .K9, .K10, .frame].contains κ = true → κ ≠ KindName.frame →
      κ = .K1 ∨ κ = .K3 ∨ κ = .K8 ∨ κ = .K9 ∨ κ = .K10 := by
  cases κ <;> decide

theorem kinds_carry (κ : KindName) :
    [KindName.K7, .K9, .frame].contains κ = true → κ ≠ KindName.frame → κ = .K7 ∨ κ = .K9 := by
  cases κ <;> decide

theorem kinds_pile (κ : KindName) :
    κ ≠ KindName.frame → (κ != KindName.K14 && κ != KindName.K15) = true →
      κ = .K1 ∨ (κ = .K2 ∨ κ = .K7 ∨ κ = .K12) ∨ (κ = .K3 ∨ κ = .K4 ∨ κ = .K6 ∨ κ = .K8) ∨
        κ = .K5 ∨ κ = .K9 ∨ κ = .K10 ∨ κ = .K11 ∨ κ = .K13 := by
  cases κ <;> decide

/-! ## 3 The fold -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- **The hypothesis `hok` of the gathering, from the cells.** -/
theorem head_hok
    (hcar : ∀ b p m, P5J.At.ps[b]? = some p → p.kind = KindName.K7 ∨ p.kind = KindName.K9 →
      Item.carry m ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b →
      Item.carry m ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.carry m))
    (hwor : ∀ b p m k ρ, P5J.At.ps[b]? = some p → p.kind = KindName.K11 →
      Item.worth m k ρ ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b →
      Item.worth m k ρ ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.worth m k ρ))
    (hf11 : ∀ b p m k ρ, P5J.At.ps[b]? = some p → p.kind = KindName.K11 →
      Item.forms m k ρ ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b →
      Item.forms m k ρ ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.forms m k ρ)) :
    ∀ b p i, P5J.At.ps[b]? = some p → p.kind ≠ KindName.frame →
      i ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b →
      i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts →
      i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).owes →
      rideOkF p i = true →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b i := by
  intro b p i hp hk hi h1 h2 hr
  rw [rideOkF_else hk] at hr
  have hb : b < 358 := by
    have e := (List.getElem?_eq_some_iff.1 hp).1
    have e' : IM.placesW = P5J.At.ps := HashBuild.placesW_full
    rw [← e', IM.places_len] at e
    exact e
  by_cases h5 : p.kind = KindName.K5
  · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
      (cell_k5 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp h5 hi h1 h2)
  cases i with
  | unmarked =>
    exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
      (cell_unmarked h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hp hk)
  | pinW =>
    exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
      (cell_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said b)
  | pinI =>
    exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
      (cell_pinI h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp hk)
  | pin m t =>
    exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
      (cell_pin h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp hk m t)
  | constr m q =>
    cases q with
    | idn =>
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_constr4 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said b m
          (by decide))
    | lookCalls =>
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_constr4 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said b m
          (by decide))
    | rider =>
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_constr4 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said b m
          (by decide))
    | small =>
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_constr4 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said b m
          (by decide))
    | lookDigits =>
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_constr_digits h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said b m)
    | lookCallsHeard =>
      have hk2 : p.kind = KindName.K2 := eq_of_beq (show (p.kind == KindName.K2) = true from hr)
      obtain ⟨ho, -⟩ := head_open_both h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hb hi h1 (fun e => by cases e)
      obtain rfl := fold_k2 hb hp hk2 ho
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
          (kpBy (fHead Zp cF G take P11 p12 P13)) w
          (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
          (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
          (ridesPastAtS_of _ _
            (constr_cell_339 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 m)))
  | pile =>
    have hn := List.all_eq_true.1 places_no_k14_k15 p (List.mem_of_getElem? hp)
    rcases kinds_pile p.kind hk hn with e | e | e | e | e | e | e | e
    · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_pile_k1 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e hi h1)
    · exact cellH_pile h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e
    · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_pile_quiet h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hp e)
    · exact absurd e h5
    · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_pile_k9 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e)
    · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_pile_k10 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e)
    · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_pile_k11 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hp e)
    · obtain ⟨-, ho'⟩ := head_open_both h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hb hi h1 (fun e => by cases e)
      exact absurd ho' (fold_k13 hb hp e)
  | row m c =>
    rcases kinds_row p.kind hr hk with e | e | e | e | e
    · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_row_k1 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e hi h1)
    · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_row_quiet h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hp e m c)
    · exact absurd e h5
    · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_row_k9 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e hi h1)
    · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_row_k11 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hp e m c)
  | formsT m k ρ =>
    rcases kinds_formsT p.kind hr with e | e | e
    · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_formsT_k4 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e hi
          h1)
    · exact absurd e h5
    · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_formsT_k6 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e hi
          h1)
  | forms m k ρ =>
    rcases kinds_forms p.kind hr with e | e | e | e
    · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cellW_forms_k1 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e hi
          h1)
    · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cellW_forms_k3 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e hi
          h1)
    · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cellW_forms_k8 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e hi
          h1)
    · exact hf11 b p m k ρ hp e hi h1
  | wo m =>
    rcases kinds_wo p.kind hr hk with e | e | e | e | e
    · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_wo_k1 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e hi h1)
    · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_wo_k3 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e hi h1)
    · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_wo_k8 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hp e m)
    · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_wo_k9 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e m)
    · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_wo_k10 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e m)
  | carry m =>
    exact hcar b p m hp (kinds_carry p.kind hr hk) hi h1
  | pinKept m =>
    rcases kinds_carry p.kind hr hk with e | e
    · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
          (kpBy (fHead Zp cF G take P11 p12 P13)) w
          (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
          (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
          (ridesPastAtS_of _ _ (pinKept_cell_k7 h H Q test carryX item n₁ n₂ b₀ Vd Rd
            (fHead Zp cF G take P11 p12 P13) w rfl hp e m)))
    · exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
          (kpBy (fHead Zp cF G take P11 p12 P13)) w
          (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
          (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
          (ridesPastAtS_of _ _ (pinKept_cell_k9 h H Q test carryX item n₁ n₂ b₀ Vd Rd
            (fHead Zp cF G take P11 p12 P13) w rfl hb hp e m)))
  | worth m k ρ =>
    exact hwor b p m k ρ hp (eq_of_beq (show (p.kind == KindName.K11) = true from hr)) hi h1
  | pileOne =>
    exact absurd (eq_of_beq (show (p.kind == KindName.frame) = true from hr)) hk
  | pinV =>
    exact absurd (eq_of_beq (show (p.kind == KindName.frame) = true from hr)) hk
  | wrow =>
    exact absurd (eq_of_beq (show (p.kind == KindName.frame) = true from hr)) hk
  | tie m =>
    exact absurd (show false = true from hr) (by decide)
  | totalB m =>
    exact absurd (show false = true from hr) (by decide)
  | total m =>
    exact absurd (show false = true from hr) (by decide)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.foldEnds_full
#print axioms ProofFile.Honest.FirstThread.foldEnds_control
#print axioms ProofFile.Honest.FirstThread.fold_k13
#print axioms ProofFile.Honest.FirstThread.fold_k2
#print axioms ProofFile.Honest.FirstThread.kinds_row
#print axioms ProofFile.Honest.FirstThread.kinds_formsT
#print axioms ProofFile.Honest.FirstThread.kinds_forms
#print axioms ProofFile.Honest.FirstThread.kinds_wo
#print axioms ProofFile.Honest.FirstThread.kinds_carry
#print axioms ProofFile.Honest.FirstThread.kinds_pile
#print axioms ProofFile.Honest.FirstThread.head_hok
