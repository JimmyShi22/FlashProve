-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/HokFoldF.lean: the hypothesis `hok` of the gathering from the
cells (`head_hok`, HokFold.lean) once more, for every condition `keeps` := `kpBy f` that implies
`kpBy fHeadH`. No definition.

Why. `head_hok` is stated at `fHeadH`. It takes the cells of the item `carry` at the kinds K7 and K9
as one hypothesis `hcar` at `fHeadH`. At K7 that cell can be proved only at a stronger `keeps`
(`fHeadI`, K7CarryCell.lean). So `head_hok` cannot be called there. With the general form every
later layer of `keeps` is an instance.

  1  `head_hokF`   `head_hok` with `kpBy f` in the place of `kpBy fHeadH` at all fifteen places,
     under `hle`: `kpBy f` implies `kpBy fHeadH`. The three hypotheses `hcar`, `hwor`, `hf11` are
     asked at `kpBy f`
  2  `head_hok_of_F`   a control: the statement of `head_hok`, by one call at `f := fHeadH`

How it was made. The statement and the proof of `head_hokF` are those of `head_hok`, changed by a
program: the fifteen places; two binders in front; one `have` behind the first line of the proof
(`up`: a cell at `fHeadH` is one at `kpBy f`, by `head_ridesPastAtS_mono`, KeepsMono.lean); and
`refine up ?_` in front of each of the 33 lines that call `cellH_of_G` or `cellH_pile`. So the proof
stands twice in the library.

Limits.
  * Those of HokFold.lean: the three hypotheses are asked only where the item is open and not shut;
    nothing is said on whether an item's statement holds at any state of a run.
  * That the item `pinW` still holds after a step is proved here through `cell_pinW`
    (Honest/Thread/CellsByKindC.lean), which is `ridesPastAt_pinW` (Honest/Thread/HeadPinW.lean);
    its proof returns its hypothesis unchanged: at these parameters the decoder of the stored table
    is a constant, so the item says nothing about the stored table, nor about the committed weights:
    it is no step toward correctness of extraction.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.HokFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (Item RowClass)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T parts4)

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

/-- **The hypothesis `hok` of the gathering, from the cells, at every `keeps` that implies
`kpBy fHeadH`.** -/
theorem head_hokF (f : KindName → Place → TS → TS → Prop)
    (hle : ∀ p s s', kpBy f p s s' →
      kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD) p s s')
    (hcar : ∀ b p m, P5J.At.ps[b]? = some p → p.kind = KindName.K7 ∨ p.kind = KindName.K9 →
      Item.carry m ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy f) w).thread.opened b →
      Item.carry m ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy f) w).thread.row b).shuts →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy f) w).thread Said
      b (Item.carry m))
    (hwor : ∀ b p m k ρ, P5J.At.ps[b]? = some p → p.kind = KindName.K11 →
      Item.worth m k ρ ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy f) w).thread.opened b →
      Item.worth m k ρ ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy f) w).thread.row b).shuts →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy f) w).thread Said
      b (Item.worth m k ρ))
    (hf11 : ∀ b p m k ρ, P5J.At.ps[b]? = some p → p.kind = KindName.K11 →
      Item.forms m k ρ ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy f) w).thread.opened b →
      Item.forms m k ρ ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy f) w).thread.row b).shuts →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy f) w).thread Said
      b (Item.forms m k ρ)) :
    ∀ b p i, P5J.At.ps[b]? = some p → p.kind ≠ KindName.frame →
      i ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy f) w).thread.opened b →
      i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy f) w).thread.row b).shuts →
      i ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy f) w).thread.row b).owes →
      rideOkF p i = true →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy f) w).thread Said
      b i := by
  intro b p i hp hk hi h1 h2 hr
  have up : ∀ {b : Nat} {i : Item},
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said b i →
      RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy f) w).thread Said b i :=
    fun hc => head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w (kpBy f) hle Said hc
  rw [rideOkF_else hk] at hr
  have hb : b < 358 := by
    have e := (List.getElem?_eq_some_iff.1 hp).1
    have e' : IM.placesW = P5J.At.ps := HashBuild.placesW_full
    rw [← e', IM.places_len] at e
    exact e
  by_cases h5 : p.kind = KindName.K5
  · refine up ?_
    exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
      (cell_k5 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp h5 hi h1 h2)
  cases i with
  | unmarked =>
    refine up ?_
    exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
      (cell_unmarked h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hp hk)
  | pinW =>
    refine up ?_
    exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
      (cell_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said b)
  | pinI =>
    refine up ?_
    exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
      (cell_pinI h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp hk)
  | pin m t =>
    refine up ?_
    exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
      (cell_pin h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp hk m t)
  | constr m q =>
    cases q with
    | idn =>
      refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_constr4 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said b m
          (by decide))
    | lookCalls =>
      refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_constr4 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said b m
          (by decide))
    | rider =>
      refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_constr4 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said b m
          (by decide))
    | small =>
      refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_constr4 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said b m
          (by decide))
    | lookDigits =>
      refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_constr_digits h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said b m)
    | lookCallsHeard =>
      have hk2 : p.kind = KindName.K2 := eq_of_beq (show (p.kind == KindName.K2) = true from hr)
      obtain ⟨ho, -⟩ := head_open_both h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy f) w hb hi h1 (fun e => by cases e)
      obtain rfl := fold_k2 hb hp hk2 ho
      refine up ?_
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
    · refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_pile_k1 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e hi h1)
    · refine up ?_
      exact cellH_pile h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e
    · refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_pile_quiet h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hp e)
    · exact absurd e h5
    · refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_pile_k9 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e)
    · refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_pile_k10 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e)
    · refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_pile_k11 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hp e)
    · obtain ⟨-, ho'⟩ := head_open_both h H Q test carryX item n₁ n₂ b₀ Vd Rd
        (kpBy f) w hb hi h1 (fun e => by cases e)
      exact absurd ho' (fold_k13 hb hp e)
  | row m c =>
    rcases kinds_row p.kind hr hk with e | e | e | e | e
    · refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_row_k1 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e hi h1)
    · refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_row_quiet h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hp e m c)
    · exact absurd e h5
    · refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_row_k9 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e hi h1)
    · refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_row_k11 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hp e m c)
  | formsT m k ρ =>
    rcases kinds_formsT p.kind hr with e | e | e
    · refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_formsT_k4 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e hi
          h1)
    · exact absurd e h5
    · refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_formsT_k6 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e hi
          h1)
  | forms m k ρ =>
    rcases kinds_forms p.kind hr with e | e | e | e
    · refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cellW_forms_k1 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e hi
          h1)
    · refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cellW_forms_k3 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e hi
          h1)
    · refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cellW_forms_k8 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e hi
          h1)
    · exact hf11 b p m k ρ hp e hi h1
  | wo m =>
    rcases kinds_wo p.kind hr hk with e | e | e | e | e
    · refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_wo_k1 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e hi h1)
    · refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_wo_k3 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e hi h1)
    · refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_wo_k8 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hp e m)
    · refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_wo_k9 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e m)
    · refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (cell_wo_k10 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said hb hp e m)
  | carry m =>
    exact hcar b p m hp (kinds_carry p.kind hr hk) hi h1
  | pinKept m =>
    rcases kinds_carry p.kind hr hk with e | e
    · refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
        (head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
          (kpBy (fHead Zp cF G take P11 p12 P13)) w
          (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD))
          (fun p s s' hk => kpBy_fHeadF _ _ _ _ _ _ p s s' (kpBy_fHeadG _ _ _ _ _ _ p s s' hk)) Said
          (ridesPastAtS_of _ _ (pinKept_cell_k7 h H Q test carryX item n₁ n₂ b₀ Vd Rd
            (fHead Zp cF G take P11 p12 P13) w rfl hp e m)))
    · refine up ?_
      exact cellH_of_G h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
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

/-- A control: `head_hok` (HokFold.lean), statement for statement, by one call at `f := fHeadH`. -/
theorem head_hok_of_F
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
      b i :=
  head_hokF h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take P11 p12 P13 Said
    (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD) (fun _ _ _ hk => hk) hcar hwor hf11

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.head_hokF
#print axioms ProofFile.Honest.FirstThread.head_hok_of_F
