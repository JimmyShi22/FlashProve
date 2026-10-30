-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Readable/FeedForward.lean: the feed-forward block of IntegerModel/Model.lean (its part
5, and the conditions of part 7 on it) shown equal to UNIT.*, FF.* of Inst/Model/Program.lean, under
the hypotheses of the statements: ff_out (the block's result), feedForwardOk_iff (the range
conditions).
-/
import IntegerModel.Readable.Helpers

set_option autoImplicit false

namespace IntegerModel.Readable

open Inst.Model IntegerModel.Runnable

/-! ## The hidden units of one block (and the router's keys) -/

theorem clamp_bd {c : ℤ} (hc : 0 ≤ c) (a : ℤ) : -c ≤ clamp c a ∧ clamp c a ≤ c :=
  ⟨le_min (le_max_right _ _) (by omega), min_le_right _ _⟩

theorem lowByte_bd (a : ℤ) : -128 ≤ lowByte a ∧ lowByte a ≤ 127 := by unfold lowByte; omega

/-- bounds on 256 gc + g0, the key into SiLU's table (the library reads at this number + 2^15) -/
theorem siluKey_bd (d : ℕ) (z wg : Vec) (k : ℕ) :
    -32640 ≤ 256 * UNIT.gc d z wg k + UNIT.g0 d z wg k ∧
    256 * UNIT.gc d z wg k + UNIT.g0 d z wg k ≤ 32639 := by
  have b1 := clamp_bd (c := 127) (by norm_num) (UNIT.gh d z wg k)
  have b2 := lowByte_bd (UNIT.gw d z wg k)
  unfold UNIT.gc UNIT.g0
  omega

/-- bounds on every expert's lr; the largest lr is the key into the sigmoid's table (the library
reads at it + 2^15) -/
theorem sigmKey_bd (P : Params) (w : LayerW) (x : ℕ → Vec) (i e : ℕ) :
    -16376 ≤ FF.lr P w x i e ∧ FF.lr P w x i e ≤ 16383 := by
  have b1 := clamp_bd (c := 2047) (by norm_num) (FF.ly P w x i e)
  have b2 : 0 ≤ FF.l3 P w x i e ∧ FF.l3 P w x i e ≤ 7 := by unfold FF.l3; omega
  unfold FF.lr
  omega

section Units
variable (tb : Tables) (d : ℕ) (z : Vec) (wg wu : ℕ → Vec) (h kg ku : ℕ)

/-- the library's values of h hidden units (unit j has the columns wg j, wu j), as the model's
record -/
def unitsRec : IntegerTransformer.HiddenUnits :=
  { wideGate := tabl h fun j => UNIT.gw d z (wg j) kg,
    lowByte := tabl h fun j => UNIT.g0 d z (wg j) kg,
    highPart := tabl h fun j => UNIT.gh d z (wg j) kg,
    clampedHigh := tabl h fun j => UNIT.gc d z (wg j) kg,
    key := tabl h fun j => 256 * UNIT.gc d z (wg j) kg + UNIT.g0 d z (wg j) kg,
    activation := tabl h fun j => UNIT.sl tb d z (wg j) kg,
    up := tabl h fun j => UNIT.up d z (wu j) ku }

theorem hiddenUnits_eq (tables : IntegerTransformer.Tables)
    (hsilu : ∀ key : ℤ, -32640 ≤ key → key ≤ 32639 → tables.silu.read key = tb.SILU (key + 2 ^ 15))
    (G : IntegerTransformer.GatedWeights)
    (hg : ∀ a < d, ∀ j < h, (((G.gate.entry a)).entry j) = wg j a)
    (hu : ∀ a < d, ∀ j < h, (((G.up.entry a)).entry j) = wu j a) :
    IntegerTransformer.hiddenUnits tables G h kg ku (tabl d z) = unitsRec tb d z wg wu h kg ku := by
  have e1 : (IntegerTransformer.product (tabl d z) G.gate h).map
        (fun e => IntegerTransformer.roundShift e kg) =
      tabl h fun j => UNIT.gw d z (wg j) kg := by
    rw [product_same d z G.gate h (fun a j => wg j a) hg, tabl_map]; rfl
  have e2 : (tabl h fun j => UNIT.gw d z (wg j) kg).map IntegerTransformer.balancedLowByte =
      tabl h fun j => UNIT.g0 d z (wg j) kg := tabl_map _ _ _
  have e3 : IntegerTransformer.tabulate h (fun j =>
        (((tabl h fun j => UNIT.gw d z (wg j) kg).entry j) -
            ((tabl h fun j => UNIT.g0 d z (wg j) kg).entry j)) / 256) =
      tabl h fun j => UNIT.gh d z (wg j) kg := by
    rw [tabulate_eq]
    exact tabl_congr fun j hj => by rw [tabl_entry _ hj, tabl_entry _ hj]; rfl
  have e4 : (tabl h fun j => UNIT.gh d z (wg j) kg).map
        (fun gh => IntegerTransformer.clamp gh 127) =
      tabl h fun j => UNIT.gc d z (wg j) kg := tabl_map _ _ _
  have e5 : IntegerTransformer.tabulate h (fun j =>
        256 * ((tabl h fun j => UNIT.gc d z (wg j) kg).entry j) +
          ((tabl h fun j => UNIT.g0 d z (wg j) kg).entry j)) =
      tabl h fun j => 256 * UNIT.gc d z (wg j) kg + UNIT.g0 d z (wg j) kg := by
    rw [tabulate_eq]
    exact tabl_congr fun j hj => by rw [tabl_entry _ hj, tabl_entry _ hj]
  have e6 : (tabl h fun j => 256 * UNIT.gc d z (wg j) kg + UNIT.g0 d z (wg j) kg).map
        tables.silu.read =
      tabl h fun j => UNIT.sl tb d z (wg j) kg := by
    rw [tabl_map]
    refine tabl_congr fun j _ => ?_
    exact hsilu _ (siluKey_bd d z (wg j) kg).1 (siluKey_bd d z (wg j) kg).2
  have e7 : (IntegerTransformer.product (tabl d z) G.up h).map
        (fun e => IntegerTransformer.roundShift e ku) =
      tabl h fun j => UNIT.up d z (wu j) ku := by
    rw [product_same d z G.up h (fun a j => wu j a) hu, tabl_map]; rfl
  unfold IntegerTransformer.hiddenUnits unitsRec
  simp only [e1, e2, e3, e4, e5, e6, e7]

theorem unitsOk_iff :
    IntegerTransformer.unitsOk (unitsRec tb d z wg wu h kg ku) = true ↔
    ∀ j < h, UNIT.OK d z (wg j) (wu j) kg ku := by
  unfold IntegerTransformer.unitsOk unitsRec
  rw [Bool.and_eq_true, fits16_tabl, tabl_all]
  constructor
  · rintro ⟨a, b⟩ j hj
    have := a j hj
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at this
    exact ⟨⟨by norm_num; exact this.1, by norm_num; omega⟩, b j hj⟩
  · intro a
    refine ⟨fun j hj => ?_, fun j hj => (a j hj).2⟩
    have := (a j hj).1
    norm_num at this
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨this.1, by omega⟩

theorem downSum_eq (D : Array (Array ℤ)) (k : ℕ) (wd : Vec)
    (hD : ∀ j < h, (((D.entry j)).entry k) = wd j) :
    IntegerTransformer.downSum (unitsRec tb d z wg wu h kg ku) D k =
      ∑ j ∈ Finset.range h, UNIT.hh tb d z (wg j) (wu j) kg ku * wd j := by
  show IntegerTransformer.sumOver (tabl h fun j => UNIT.up d z (wu j) ku).size
      (fun j =>
        ((tabl h fun j => UNIT.sl tb d z (wg j) kg).entry j) *
          ((tabl h fun j => UNIT.up d z (wu j) ku).entry j) * (((D.entry j)).entry k)) = _
  rw [sumOver_eq, tabl_size]
  exact Finset.sum_congr rfl fun j hj => by
    have hj' := Finset.mem_range.1 hj
    rw [tabl_entry _ hj', tabl_entry _ hj', hD j hj']
    rfl

end Units

/-! ## The library's down projection and its units' conditions, by kind of layer -/

section Block
variable (P : Params) (tb : Tables) (w : LayerW) (L : ℕ) (x : ℕ → Vec) (i : ℕ)

theorem Ad_dense (hE : ¬ hasExperts L) (c : ℕ) :
    FF.Ad P tb w L x i c =
      ∑ j ∈ Finset.range P.f,
        UNIT.hh tb P.d (FF.m P x i) (fun a => w.Wg a j) (fun a => w.Wu a j) P.kg P.ku *
          w.Wd j c := by
  have hr : ∀ j, ¬ FF.routed P L j := fun j h => hE h.1
  unfold FF.Ad
  rw [show FF.units P L = P.f from if_neg hE]
  exact Finset.sum_congr rfl fun j _ => by rw [hh_plain P tb w L x i (hr j), if_neg (hr j)]

theorem Ad_exp (hE : hasExperts L) (c : ℕ) :
    FF.Ad P tb w L x i c =
      ∑ j ∈ Finset.range P.fe,
          UNIT.hh tb P.d (FF.m P x i) (fun a => w.Wg a j) (fun a => w.Wu a j) P.kg P.ku * w.Wd j c +
        ∑ j ∈ Finset.range P.fe,
          UNIT.hh tb P.d (FF.xr P tb w x i) (fun a => w.Eg (FF.es P w x i) a j)
              (fun a => w.Eu (FF.es P w x i) a j) P.kg' P.ku' *
            w.Ed (FF.es P w x i) j c := by
  have hp : ∀ j < P.fe, ¬ FF.routed P L j := fun j hj h => absurd h.2 (not_le.2 hj)
  have hr : ∀ j, FF.routed P L (P.fe + j) := fun j => ⟨hE, Nat.le_add_right _ _⟩
  unfold FF.Ad
  rw [show FF.units P L = P.fe + P.fe from (if_pos hE).trans (Nat.two_mul _), Finset.sum_range_add]
  congr 1
  · exact Finset.sum_congr rfl fun j hj => by
      rw [hh_plain P tb w L x i (hp j (Finset.mem_range.1 hj)),
        if_neg (hp j (Finset.mem_range.1 hj))]
  · exact Finset.sum_congr rfl fun j _ => by
      rw [hh_routed P tb w L x i (hr j), if_pos (hr j), Nat.add_sub_cancel_left]

theorem units_dense (hE : ¬ hasExperts L) :
    (∀ j < FF.units P L,
      UNIT.OK P.d (FF.z P tb w L x i j) (FF.wg P w L x i j) (FF.wu P w L x i j)
        (FF.kG P L j) (FF.kU P L j)) ↔
    ∀ j < P.f, UNIT.OK P.d (FF.m P x i) (fun a => w.Wg a j) (fun a => w.Wu a j) P.kg P.ku := by
  rw [show FF.units P L = P.f from if_neg hE]
  exact forall₂_congr fun j _ => ok_plain P tb w L x i fun h => hE h.1

theorem units_exp (hE : hasExperts L) :
    (∀ j < FF.units P L,
      UNIT.OK P.d (FF.z P tb w L x i j) (FF.wg P w L x i j) (FF.wu P w L x i j)
        (FF.kG P L j) (FF.kU P L j)) ↔
    (∀ j < P.fe, UNIT.OK P.d (FF.m P x i) (fun a => w.Wg a j) (fun a => w.Wu a j) P.kg P.ku) ∧
    ∀ j < P.fe, UNIT.OK P.d (FF.xr P tb w x i) (fun a => w.Eg (FF.es P w x i) a j)
      (fun a => w.Eu (FF.es P w x i) a j) P.kg' P.ku' := by
  have hp : ∀ j < P.fe, ¬ FF.routed P L j := fun j hj h => absurd h.2 (not_le.2 hj)
  have hr : ∀ j, FF.routed P L (P.fe + j) := fun j => ⟨hE, Nat.le_add_right _ _⟩
  rw [show FF.units P L = P.fe + P.fe from (if_pos hE).trans (Nat.two_mul _)]
  constructor
  · intro h
    exact ⟨fun j hj => (ok_plain P tb w L x i (hp j hj)).1 (h j (by omega)),
      fun j hj => (ok_routed P tb w L x i (hr j)).1 (h (P.fe + j) (by omega))⟩
  · rintro ⟨a, b⟩ j hj
    by_cases hlt : j < P.fe
    · exact (ok_plain P tb w L x i (hp j hlt)).2 (a j hlt)
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hlt)
      exact (ok_routed P tb w L x i (hr k)).2 (b k (by omega))

/-! ## The router and the block -/

/-- the library's values of the router and the routed expert at position i, as the model's record -/
def routedRec : IntegerTransformer.Routed :=
  { wide := tabl P.nexp (FF.lw P w x i), high := tabl P.nexp (FF.ly P w x i),
    low := tabl P.nexp (FF.l3 P w x i), logits := tabl P.nexp (FF.lr P w x i),
    chosen := FF.es P w x i, scale := FF.sc P tb w x i, input := tabl P.d (FF.xr P tb w x i),
    units := unitsRec tb P.d (FF.xr P tb w x i) (fun j a => w.Eg (FF.es P w x i) a j)
        (fun j a => w.Eu (FF.es P w x i) a j) P.fe P.kg' P.ku' }

variable (hn : 0 < P.nexp) (Tmax : ℕ) (s : IntegerTransformer.Settings) (hs : SameSizes P Tmax s)
  (p : IntegerTransformer.LayerSettings) (hp : SameScales L p P.scale)
  (tables : IntegerTransformer.Tables) (hT : SameTables P Tmax s p tables tb L P.expRows)
  (W : IntegerTransformer.LayerWeights) (hW : SameLayer P L W w)

include hn in
theorem es_lt : FF.es P w x i < P.nexp := lt_of_le_of_lt (argTo_spec _ _).1 (by omega)

include hn hs hp hT hW in
theorem routedExpert_eq (hE : hasExperts L) :
    IntegerTransformer.routedExpert s p tables W (tabl P.d (FF.m P x i)) =
      routedRec P tb w x i := by
  have hlt := es_lt P w x i hn
  have e1 : (IntegerTransformer.product (tabl P.d (FF.m P x i)) W.router P.nexp).map
        (fun e => IntegerTransformer.roundShift e p.routerShift) =
      tabl P.nexp (FF.lw P w x i) := by
    rw [product_same _ _ _ _ w.Wr (hW.Wr hE), tabl_map, hp.kr hE]; rfl
  have e2 : (tabl P.nexp (FF.lw P w x i)).map (fun lw => lw / 8) = tabl P.nexp (FF.ly P w x i) := by
    rw [tabl_map]
    exact tabl_congr fun e _ => by unfold FF.ly FF.l3; omega
  have e3 : (tabl P.nexp (FF.lw P w x i)).map (fun lw => lw % 8) = tabl P.nexp (FF.l3 P w x i) :=
    tabl_map _ _ _
  have e4 : IntegerTransformer.tabulate P.nexp (fun e =>
        8 * IntegerTransformer.clamp ((tabl P.nexp (FF.ly P w x i)).entry e) 2047 +
          ((tabl P.nexp (FF.l3 P w x i)).entry e)) =
      tabl P.nexp (FF.lr P w x i) := by
    rw [tabulate_eq]
    exact tabl_congr fun e he => by rw [tabl_entry _ he, tabl_entry _ he]; rfl
  have e5 : IntegerTransformer.firstArgmax
        (fun e => ((tabl P.nexp (FF.lr P w x i)).entry e)) P.nexp =
      FF.es P w x i := by
    rw [firstArgmax_eq]
    exact argTo_congr _ fun j hj => tabl_entry _ (by omega)
  have e6 : tables.sigmoid.read ((tabl P.nexp (FF.lr P w x i)).entry (FF.es P w x i)) =
      FF.sc P tb w x i := by
    rw [tabl_entry _ hlt]
    exact hT.sigm _ (sigmKey_bd P w x i _).1 (sigmKey_bd P w x i _).2
  have e7 : (tabl P.d (FF.m P x i)).map
        (fun mk => IntegerTransformer.roundShift (FF.sc P tb w x i * mk) 16) =
      tabl P.d (FF.xr P tb w x i) := tabl_map _ _ _
  have e8 := hiddenUnits_eq tb P.d (FF.xr P tb w x i) (fun j a => w.Eg (FF.es P w x i) a j)
    (fun j a => w.Eu (FF.es P w x i) a j) P.fe P.kg' P.ku' tables hT.silu
    (W.routed.entry (FF.es P w x i)) (fun a ha j hj => hW.Eg hE _ hlt a ha j hj)
    (fun a ha j hj => hW.Eu hE _ hlt a ha j hj)
  unfold IntegerTransformer.routedExpert routedRec
  simp only [hs.experts, hs.expertHidden, hp.kgR hE, hp.kuR hE, e1, e2, e3, e4, e5, e6, e7]
  rw [show P.scale.kg' = P.kg' from rfl, show P.scale.ku' = P.ku' from rfl, e8]

include hs hp hT hW in
theorem feedForward_dense (hE : ¬ hasExperts L) :
    IntegerTransformer.feedForward s p tables W false (tabl P.d (x i)) =
      { norm := normRec P.n2 P.d (x i),
        shared := unitsRec tb P.d (FF.m P x i) (fun j a => w.Wg a j)
            (fun j a => w.Wu a j) P.f P.kg P.ku,
        routed := IntegerTransformer.noRoute,
        addition := tabl P.d fun c => rhu (FF.Ad P tb w L x i c) P.kd,
        out := tabl P.d (FF.x'' P tb w L x i) } := by
  have hf : (if hasExperts L then P.fe else P.f) = P.f := if_neg hE
  have hWg := hW.Wg
  have hWu := hW.Wu
  have hWd := hW.Wd
  rw [hf] at hWg hWu hWd
  have e0 := rmsNorm_eq P.n2 P.d (x i) hp.M2 hp.K2 hp.eps2
  have e1 := hiddenUnits_eq tb P.d (FF.m P x i) (fun j a => w.Wg a j) (fun j a => w.Wu a j)
    P.f P.kg P.ku tables hT.silu W.shared hWg hWu
  have e2 : IntegerTransformer.tabulate P.d (fun k =>
        IntegerTransformer.roundShift
          (IntegerTransformer.downSum
            (unitsRec tb P.d (FF.m P x i) (fun j a => w.Wg a j) (fun j a => w.Wu a j) P.f P.kg P.ku)
            W.shared.down k) P.kd) =
      tabl P.d fun c => rhu (FF.Ad P tb w L x i c) P.kd := by
    rw [tabulate_eq]
    exact tabl_congr fun c hc => by rw [downSum_eq _ _ _ _ _ _ _ _ _ _ (fun j => w.Wd j c) fun j hj => hWd j hj c hc, Ad_dense P tb w L x i hE]; rfl
  unfold IntegerTransformer.feedForward
  simp only [e0, hs.hidden, hs.width, hp.kg, hp.ku, hp.kd, Bool.false_eq_true, if_false]
  show ({
    norm := _,
      shared := IntegerTransformer.hiddenUnits
          tables W.shared P.f P.kg P.ku (tabl P.d (FF.m P x i)),
      routed := IntegerTransformer.noRoute,
    addition := IntegerTransformer.tabulate P.d (fun k =>
      IntegerTransformer.roundShift
        (IntegerTransformer.downSum
          (IntegerTransformer.hiddenUnits tables W.shared P.f P.kg P.ku (tabl P.d (FF.m P x i)))
          W.shared.down k) P.kd),
    out := IntegerTransformer.addVectors (tabl P.d (x i)) (IntegerTransformer.tabulate P.d (fun k => IntegerTransformer.roundShift (IntegerTransformer.downSum (IntegerTransformer.hiddenUnits tables W.shared P.f P.kg P.ku (tabl P.d (FF.m P x i))) W.shared.down k) P.kd)) } : IntegerTransformer.FeedForward) = _
  rw [e1, e2, addVec_tabl]
  rfl

include hn hs hp hT hW in
theorem feedForward_exp (hE : hasExperts L) :
    IntegerTransformer.feedForward s p tables W true (tabl P.d (x i)) =
      { norm := normRec P.n2 P.d (x i),
        shared := unitsRec tb P.d (FF.m P x i) (fun j a => w.Wg a j)
            (fun j a => w.Wu a j) P.fe P.kg P.ku,
        routed := routedRec P tb w x i,
        addition := tabl P.d fun c => rhu (FF.Ad P tb w L x i c) P.kd,
        out := tabl P.d (FF.x'' P tb w L x i) } := by
  have hlt := es_lt P w x i hn
  have hf : (if hasExperts L then P.fe else P.f) = P.fe := if_pos hE
  have hWg := hW.Wg
  have hWu := hW.Wu
  have hWd := hW.Wd
  rw [hf] at hWg hWu hWd
  have e0 := rmsNorm_eq P.n2 P.d (x i) hp.M2 hp.K2 hp.eps2
  have e1 := hiddenUnits_eq tb P.d (FF.m P x i) (fun j a => w.Wg a j) (fun j a => w.Wu a j)
    P.fe P.kg P.ku tables hT.silu W.shared hWg hWu
  have e3 := routedExpert_eq P tb w L x i hn Tmax s hs p hp tables hT W hW hE
  have e2 : IntegerTransformer.tabulate P.d (fun k =>
        IntegerTransformer.roundShift
          (IntegerTransformer.downSum
              (unitsRec tb P.d (FF.m P x i) (fun j a => w.Wg a j)
                (fun j a => w.Wu a j) P.fe P.kg P.ku)
              W.shared.down k +
            IntegerTransformer.downSum
              (routedRec P tb w x i).units (W.routed.entry ((routedRec P tb w x i).chosen)).down k)
          P.kd) =
      tabl P.d fun c => rhu (FF.Ad P tb w L x i c) P.kd := by
    rw [tabulate_eq]
    refine tabl_congr fun c hc => ?_
    rw [downSum_eq _ _ _ _ _ _ _ _ _ _ (fun j => w.Wd j c) fun j hj => hWd j hj c hc]
    show IntegerTransformer.roundShift
        (_ + IntegerTransformer.downSum
            (unitsRec tb P.d (FF.xr P tb w x i) (fun j a => w.Eg (FF.es P w x i) a j)
              (fun j a => w.Eu (FF.es P w x i) a j) P.fe P.kg' P.ku')
            (W.routed.entry (FF.es P w x i)).down c) P.kd = _
    rw [downSum_eq _ _ _ _ _ _ _ _ _ _ (fun j => w.Ed (FF.es P w x i) j c) fun j hj =>
          hW.Ed hE _ hlt j hj c hc,
      Ad_exp P tb w L x i hE]
    rfl
  unfold IntegerTransformer.feedForward
  simp only [e0, hs.expertHidden, hs.width, hp.kg, hp.ku, hp.kd, if_true]
  show ({
    norm := _,
      shared := IntegerTransformer.hiddenUnits
          tables W.shared P.fe P.kg P.ku (tabl P.d (FF.m P x i)),
      routed := IntegerTransformer.routedExpert s p tables W (tabl P.d (FF.m P x i)),
    addition := IntegerTransformer.tabulate P.d (fun k =>
      IntegerTransformer.roundShift
        (IntegerTransformer.downSum
          (IntegerTransformer.hiddenUnits tables W.shared P.fe P.kg P.ku (tabl P.d (FF.m P x i)))
          W.shared.down k
      + IntegerTransformer.downSum (IntegerTransformer.routedExpert s p tables W (tabl P.d (FF.m P x i))).units (W.routed.entry ((IntegerTransformer.routedExpert s p tables W (tabl P.d (FF.m P x i))).chosen)).down k) P.kd),
    out := IntegerTransformer.addVectors (tabl P.d (x i))
      (IntegerTransformer.tabulate P.d (fun k =>
        IntegerTransformer.roundShift
          (IntegerTransformer.downSum
            (IntegerTransformer.hiddenUnits tables W.shared P.fe P.kg P.ku (tabl P.d (FF.m P x i)))
            W.shared.down k
      + IntegerTransformer.downSum (IntegerTransformer.routedExpert s p tables W (tabl P.d (FF.m P x i))).units (W.routed.entry ((IntegerTransformer.routedExpert s p tables W (tabl P.d (FF.m P x i))).chosen)).down k) P.kd)) } : IntegerTransformer.FeedForward) = _
  rw [e1, e3, e2, addVec_tabl]
  rfl

include hn hs in
theorem isMixture_iff : s.isMixture L = true ↔ hasExperts L := by
  unfold IntegerTransformer.Settings.isMixture hasExperts
  rw [hs.experts, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨fun h => h.2, fun h => ⟨hn, h⟩⟩

include hn hs hp hT hW in
/-- the block at one position: its result -/
theorem ff_out :
    (IntegerTransformer.feedForward s p tables W (s.isMixture L) (tabl P.d (x i))).out =
      tabl P.d (FF.x'' P tb w L x i) := by
  by_cases hE : hasExperts L
  · rw [(isMixture_iff P L hn Tmax s hs).2 hE,
      feedForward_exp P tb w L x i hn Tmax s hs p hp tables hT W hW hE]
  · rw [Bool.eq_false_iff.2 fun h => hE ((isMixture_iff P L hn Tmax s hs).1 h),
      feedForward_dense P tb w L x i Tmax s hs p hp tables hT W hW hE]

include hn hs hp hT hW in
/-- the block at one position: its conditions -/
theorem feedForwardOk_iff :
    IntegerTransformer.feedForwardOk
        p (IntegerTransformer.feedForward s p tables W (s.isMixture L) (tabl P.d (x i))) = true ↔
    NORM.OK P.n2 P.d (x i) ∧
    (hasExperts L → ∀ e < P.nexp, Fits16 (FF.ly P w x i e)) ∧
    ∀ j < FF.units P L,
      UNIT.OK P.d (FF.z P tb w L x i j) (FF.wg P w L x i j) (FF.wu P w L x i j)
        (FF.kG P L j) (FF.kU P L j) := by
  by_cases hE : hasExperts L
  · rw [(isMixture_iff P L hn Tmax s hs).2 hE,
      feedForward_exp P tb w L x i hn Tmax s hs p hp tables hT W hW hE, units_exp P tb w L x i hE]
    show (IntegerTransformer.normOk p.feedForwardEps (normRec P.n2 P.d (x i)) &&
          IntegerTransformer.unitsOk
            (unitsRec tb P.d (FF.m P x i) (fun j a => w.Wg a j)
              (fun j a => w.Wu a j) P.fe P.kg P.ku) &&
          IntegerTransformer.fits16 (tabl P.nexp (FF.ly P w x i)) &&
          IntegerTransformer.unitsOk
            (unitsRec tb P.d (FF.xr P tb w x i) (fun j a => w.Eg (FF.es P w x i) a j)
              (fun j a => w.Eu (FF.es P w x i) a j) P.fe P.kg' P.ku')) = true ↔
      _
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, normOk_iff P.n2 P.d (x i) hp.eps2,
      unitsOk_iff, unitsOk_iff, fits16_tabl]
    exact ⟨fun ⟨⟨⟨a, b⟩, c⟩, d⟩ => ⟨a, fun _ => c, b, d⟩, fun ⟨a, c, b, d⟩ => ⟨⟨⟨a, b⟩, c hE⟩, d⟩⟩
  · rw [Bool.eq_false_iff.2 fun h => hE ((isMixture_iff P L hn Tmax s hs).1 h),
      feedForward_dense P tb w L x i Tmax s hs p hp tables hT W hW hE, units_dense P tb w L x i hE]
    show (IntegerTransformer.normOk p.feedForwardEps (normRec P.n2 P.d (x i)) &&
          IntegerTransformer.unitsOk
            (unitsRec tb P.d (FF.m P x i) (fun j a => w.Wg a j)
              (fun j a => w.Wu a j) P.f P.kg P.ku) &&
          IntegerTransformer.fits16 IntegerTransformer.noRoute.high &&
          IntegerTransformer.unitsOk IntegerTransformer.noRoute.units) = true ↔
      _
    rw [show IntegerTransformer.fits16 IntegerTransformer.noRoute.high =
          true by simp [IntegerTransformer.fits16, IntegerTransformer.noRoute],
      show IntegerTransformer.unitsOk IntegerTransformer.noRoute.units =
        true by
          simp [IntegerTransformer.unitsOk, IntegerTransformer.fits16, IntegerTransformer.noRoute],
      Bool.and_true, Bool.and_true, Bool.and_eq_true,
      normOk_iff P.n2 P.d (x i) hp.eps2, unitsOk_iff]
    exact ⟨fun ⟨a, b⟩ => ⟨a, fun h => absurd h hE, b⟩, fun ⟨a, _, b⟩ => ⟨a, b⟩⟩

end Block

end IntegerModel.Readable
