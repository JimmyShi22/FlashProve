-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Runnable/FeedForward.lean: the feed-forward block of the array program (ArrayProgram,
IntegerModel/Runnable/ArrayModel.lean) compared with the library's FF.x'' and FF.OK
(Inst/Model/Program.lean). feedForward_is: under TabRel, SameLayer and 0 < P.nexp the block gives
some (FF.x'') if FF.OK holds, else none.
-/
import IntegerModel.Runnable.Small

set_option autoImplicit false

namespace IntegerModel.Runnable

open Inst.Model

/-! ## The program's text once more, cut into steps ("feedForward_eq": the same term, by unfolding alone) -/

section Steps
variable (S : ArrayProgram.Shape) (t : ArrayProgram.Tables) (s : ArrayProgram.LayerScales)
  (w : ArrayProgram.LayerWeights) (xi m : Array ℤ)

def ffDense : Option (Array ℤ) :=
  ((Array.range S.ffDense).mapM fun j =>
        ArrayProgram.unit t m (w.Wgate · j) (w.Wup · j) s.kg s.ku).bind fun hidden =>
    some (ArrayProgram.row S.d fun c =>
      xi[c]! + ArrayProgram.shiftRound (ArrayProgram.dot hidden (w.Wdown · c)) s.kd)

def ffExp3 (e : ℕ) (scaled : Array ℤ) : Option (Array ℤ) :=
  ((Array.range S.ffExpert).mapM fun j =>
        ArrayProgram.unit t m (w.Wgate · j) (w.Wup · j) s.kg s.ku).bind fun shared =>
    ((Array.range S.ffExpert).mapM fun j =>
          ArrayProgram.unit t scaled (w.Egate e · j) (w.Eup e · j) s.kgR s.kuR).bind fun routed =>
      some (ArrayProgram.row S.d fun c =>
        xi[c]! + ArrayProgram.shiftRound
            (ArrayProgram.dot shared (w.Wdown · c) + ArrayProgram.dot routed (w.Edown e · c)) s.kd)

def ffExp2 (e : ℕ) (scale : ℤ) : Option (Array ℤ) :=
  ffExp3 S t s w xi m e (m.map fun v => ArrayProgram.shiftRound (scale * v) 16)

def ffExp1 (logit : Array ℤ) : Option (Array ℤ) :=
  ffExp2 S t s w xi m (ArrayProgram.argmaxFirst logit)
    (t.sigmoid (logit[ArrayProgram.argmaxFirst logit]! + 2 ^ 15))

def ffExp0 (wide : Array ℤ) : Option (Array ℤ) :=
  if (!(wide.all fun l => ArrayProgram.fits16 ((l - l % 8) / 8))) = true then none
  else ffExp1 S t s w xi m (wide.map fun l => 8 * ArrayProgram.clamp 2047 ((l - l % 8) / 8) + l % 8)

def ffRow (L : ℕ) (xi : Array ℤ) : Option (Array ℤ) :=
  (ArrayProgram.rmsNorm s.norm2 xi).bind fun m =>
    if ArrayProgram.hasExperts L = true then
      ffExp0 S t s w xi m (ArrayProgram.project m w.Wrouter S.experts s.kr)
    else ffDense S t s w xi m

theorem feedForward_eq (L : ℕ) (x : Array (Array ℤ)) :
    ArrayProgram.feedForward S t s w L x = x.mapM (ffRow S t s w L) := rfl

/-- the block's output depends on a layer's scales through its second norm and three shifts alone,
and in a layer with experts three more -/
theorem feedForward_scales (L : ℕ) (s' : ArrayProgram.LayerScales) (h1 : s.norm2 = s'.norm2)
    (h2 : s.kg = s'.kg) (h3 : s.ku = s'.ku) (h4 : s.kd = s'.kd)
    (h5 : ArrayProgram.hasExperts L = true → s.kr = s'.kr ∧ s.kgR = s'.kgR ∧ s.kuR = s'.kuR) :
    ArrayProgram.feedForward S t s w L = ArrayProgram.feedForward S t s' w L := by
  funext x
  rw [feedForward_eq, feedForward_eq]
  congr 1
  funext xi
  by_cases hE : ArrayProgram.hasExperts L = true
  · obtain ⟨a, b, c⟩ := h5 hE
    simp only [ffRow, ffExp0, ffExp1, ffExp2, ffExp3, if_pos hE, h1, h2, h3, h4, a, b, c]
  · simp only [ffRow, ffDense, if_neg hE, h1, h2, h3, h4]

end Steps

/-! ## The library's hidden units, by kind; then the block -/

section Block
variable (P : Params) (tb : Tables) (w : LayerW) (L : ℕ) (x : ℕ → Vec) (i : ℕ)

theorem wg_plain {j : ℕ} (h : ¬ FF.routed P L j) : FF.wg P w L x i j = fun a => w.Wg a j := by
  funext a; simp only [FF.wg, if_neg h]
theorem wu_plain {j : ℕ} (h : ¬ FF.routed P L j) : FF.wu P w L x i j = fun a => w.Wu a j := by
  funext a; simp only [FF.wu, if_neg h]
theorem wg_routed {j : ℕ} (h : FF.routed P L (P.fe + j)) :
    FF.wg P w L x i (P.fe + j) = fun a => w.Eg (FF.es P w x i) a j := by
  funext a; simp only [FF.wg, if_pos h, Nat.add_sub_cancel_left]
theorem wu_routed {j : ℕ} (h : FF.routed P L (P.fe + j)) :
    FF.wu P w L x i (P.fe + j) = fun a => w.Eu (FF.es P w x i) a j := by
  funext a; simp only [FF.wu, if_pos h, Nat.add_sub_cancel_left]

theorem hh_plain {j : ℕ} (h : ¬ FF.routed P L j) :
    FF.hh P tb w L x i j =
      UNIT.hh tb P.d (FF.m P x i) (fun a => w.Wg a j) (fun a => w.Wu a j) P.kg P.ku := by
  simp only [FF.hh, FF.z, wg_plain P w L x i h, wu_plain P w L x i h, FF.kG, FF.kU, if_neg h]

theorem ok_plain {j : ℕ} (h : ¬ FF.routed P L j) :
    UNIT.OK P.d (FF.z P tb w L x i j) (FF.wg P w L x i j) (FF.wu P w L x i j)
      (FF.kG P L j) (FF.kU P L j) ↔
    UNIT.OK P.d (FF.m P x i) (fun a => w.Wg a j) (fun a => w.Wu a j) P.kg P.ku := by
  simp only [FF.z, wg_plain P w L x i h, wu_plain P w L x i h, FF.kG, FF.kU, if_neg h]

theorem hh_routed {j : ℕ} (h : FF.routed P L (P.fe + j)) :
    FF.hh P tb w L x i (P.fe + j) =
      UNIT.hh tb P.d (FF.xr P tb w x i) (fun a => w.Eg (FF.es P w x i) a j)
        (fun a => w.Eu (FF.es P w x i) a j) P.kg' P.ku' := by
  simp only [FF.hh, FF.z, wg_routed P w L x i h, wu_routed P w L x i h, FF.kG, FF.kU, if_pos h]

theorem ok_routed {j : ℕ} (h : FF.routed P L (P.fe + j)) :
    UNIT.OK P.d (FF.z P tb w L x i (P.fe + j)) (FF.wg P w L x i (P.fe + j))
      (FF.wu P w L x i (P.fe + j)) (FF.kG P L (P.fe + j)) (FF.kU P L (P.fe + j)) ↔
    UNIT.OK P.d (FF.xr P tb w x i) (fun a => w.Eg (FF.es P w x i) a j)
      (fun a => w.Eu (FF.es P w x i) a j) P.kg' P.ku' := by
  simp only [FF.z, wg_routed P w L x i h, wu_routed P w L x i h, FF.kG, FF.kU, if_pos h]

theorem hasExperts_iff : ArrayProgram.hasExperts L = true ↔ hasExperts L := by
  unfold ArrayProgram.hasExperts hasExperts
  exact beq_iff_eq

variable (Tmax : ℕ) (t : ArrayProgram.Tables) (rows : ℤ) (hT : TabRel t tb L rows)
  (W : ArrayProgram.LayerWeights) (hW : SameLayer P L W w)
include hT hW

/-- a dense layer, one position -/
theorem ffDense_is (hE : ¬ hasExperts L) :
    Is (ffDense (shapeOf P Tmax) t (lsOf P) W (tabl P.d (x i)) (tabl P.d (FF.m P x i)))
      (∀ j < FF.units P L,
        UNIT.OK P.d (FF.z P tb w L x i j) (FF.wg P w L x i j) (FF.wu P w L x i j)
          (FF.kG P L j) (FF.kU P L j))
      (tabl P.d (FF.x'' P tb w L x i)) := by
  have hr : ∀ j, ¬ FF.routed P L j := fun j h => hE h.1
  have hu : FF.units P L = P.f := if_neg hE
  have hf : (if hasExperts L then P.fe else P.f) = P.f := if_neg hE
  have hWg := hW.Wg
  have hWu := hW.Wu
  have hWd := hW.Wd
  rw [hf] at hWg hWu hWd
  have h1 := Is.mapM_range (n := P.f) fun j hj =>
    unit_is t tb hT.silu P.d (FF.m P x i) (fun a => w.Wg a j) (fun a => w.Wu a j)
      P.kg P.ku (wg' := (W.Wgate · j)) (wu' := (W.Wup · j))
      (fun a ha => hWg a ha j hj) (fun a ha => hWu a ha j hj)
  have h0 : Is
      (ffDense (shapeOf P Tmax) t (lsOf P) W (tabl P.d (x i)) (tabl P.d (FF.m P x i))) _ _ :=
    Is.bind h1 (Is.pure _)
  refine (h0.iff ?_).val fun _ => ?_
  · rw [hu, and_true]
    exact forall₂_congr fun j _ => (ok_plain P tb w L x i (hr j)).symm
  · refine tabl_congr (n := P.d) fun c hc => ?_
    rw [tabl_get _ hc, dot_tabl, dot_congr fun j hj => hWd j hj c hc]
    show x i c + rhu (∑ j ∈ Finset.range P.f, _) P.kd =
      x i c + rhu (∑ j ∈ Finset.range (FF.units P L), _) P.kd
    rw [hu]
    congr 2
    exact Finset.sum_congr rfl fun j _ => by rw [hh_plain P tb w L x i (hr j), if_neg (hr j)]

/-- a layer with experts, one position, after the router's test -/
theorem ffExp3_is (hn : 0 < P.nexp) (hE : hasExperts L) :
    Is (ffExp3 (shapeOf P Tmax) t (lsOf P) W (tabl P.d (x i)) (tabl P.d (FF.m P x i))
        (FF.es P w x i) (tabl P.d (FF.xr P tb w x i)))
      (∀ j < FF.units P L,
        UNIT.OK P.d (FF.z P tb w L x i j) (FF.wg P w L x i j) (FF.wu P w L x i j)
          (FF.kG P L j) (FF.kU P L j))
      (tabl P.d (FF.x'' P tb w L x i)) := by
  have hp : ∀ j < P.fe, ¬ FF.routed P L j := fun j hj h => absurd h.2 (not_le.2 hj)
  have hr : ∀ j, FF.routed P L (P.fe + j) := fun j => ⟨hE, Nat.le_add_right _ _⟩
  have hu : FF.units P L = P.fe + P.fe := (if_pos hE).trans (Nat.two_mul _)
  have hf : (if hasExperts L then P.fe else P.f) = P.fe := if_pos hE
  have hWg := hW.Wg
  have hWu := hW.Wu
  have hWd := hW.Wd
  rw [hf] at hWg hWu hWd
  have hlt : FF.es P w x i < P.nexp := lt_of_le_of_lt (argTo_spec _ _).1 (by omega)
  have h1 := Is.mapM_range (n := P.fe) fun j hj =>
    unit_is t tb hT.silu P.d (FF.m P x i) (fun a => w.Wg a j) (fun a => w.Wu a j)
      P.kg P.ku (wg' := (W.Wgate · j)) (wu' := (W.Wup · j))
      (fun a ha => hWg a ha j hj) (fun a ha => hWu a ha j hj)
  have h2 := Is.mapM_range (n := P.fe) fun j hj =>
    unit_is t tb hT.silu P.d (FF.xr P tb w x i) (fun a => w.Eg (FF.es P w x i) a j)
      (fun a => w.Eu (FF.es P w x i) a j) P.kg' P.ku'
      (wg' := (W.Egate (FF.es P w x i) · j)) (wu' := (W.Eup (FF.es P w x i) · j))
      (fun a ha => hW.Eg hE _ hlt a ha j hj) (fun a ha => hW.Eu hE _ hlt a ha j hj)
  have h0 : Is
      (ffExp3 (shapeOf P Tmax) t (lsOf P) W (tabl P.d (x i)) (tabl P.d (FF.m P x i))
        (FF.es P w x i) (tabl P.d (FF.xr P tb w x i)))
      _ _ :=
    Is.bind h1 (Is.bind h2 (Is.pure _))
  refine (h0.iff ?_).val fun _ => ?_
  · rw [hu, and_true]
    constructor
    · rintro ⟨a, b⟩ j hj
      by_cases hlt : j < P.fe
      · exact (ok_plain P tb w L x i (hp j hlt)).2 (a j hlt)
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hlt)
        exact (ok_routed P tb w L x i (hr k)).2 (b k (by omega))
    · intro h
      exact ⟨fun j hj => (ok_plain P tb w L x i (hp j hj)).1 (h j (by omega)),
        fun j hj => (ok_routed P tb w L x i (hr j)).1 (h (P.fe + j) (by omega))⟩
  · refine tabl_congr (n := P.d) fun c hc => ?_
    rw [tabl_get _ hc, dot_tabl, dot_tabl, dot_congr fun j hj => hWd j hj c hc,
      dot_congr fun j hj => hW.Ed hE _ hlt j hj c hc]
    show x i c + rhu (∑ j ∈ Finset.range P.fe, _ + ∑ j ∈ Finset.range P.fe, _) P.kd =
      x i c + rhu (∑ j ∈ Finset.range (FF.units P L), _) P.kd
    rw [hu, Finset.sum_range_add]
    congr 3
    · exact Finset.sum_congr rfl fun j hj => by
        rw [hh_plain P tb w L x i (hp j (Finset.mem_range.1 hj)),
          if_neg (hp j (Finset.mem_range.1 hj))]
    · exact Finset.sum_congr rfl fun j _ => by
        rw [hh_routed P tb w L x i (hr j), if_pos (hr j), Nat.add_sub_cancel_left]

/-- a layer with experts, one position -/
theorem ffExp0_is (hn : 0 < P.nexp) (hE : hasExperts L) :
    Is (ffExp0 (shapeOf P Tmax) t (lsOf P) W (tabl P.d (x i))
        (tabl P.d (FF.m P x i)) (tabl P.nexp (FF.lw P w x i)))
      ((∀ e < P.nexp, Fits16 (FF.ly P w x i e)) ∧
        ∀ j < FF.units P L,
          UNIT.OK P.d (FF.z P tb w L x i j) (FF.wg P w L x i j) (FF.wu P w L x i j)
            (FF.kG P L j) (FF.kU P L j))
      (tabl P.d (FF.x'' P tb w L x i)) := by
  have hlr : (tabl P.nexp (FF.lw P w x i)).map
        (fun l => 8 * ArrayProgram.clamp 2047 ((l - l % 8) / 8) + l % 8) =
      tabl P.nexp (FF.lr P w x i) := tabl_map _ _ _
  have hes : ArrayProgram.argmaxFirst (tabl P.nexp (FF.lr P w x i)) = FF.es P w x i :=
    argmax_tabl _ _
  have hlt : FF.es P w x i < P.nexp := lt_of_le_of_lt (argTo_spec _ _).1 (by omega)
  have hxr : (tabl P.d (FF.m P x i)).map
        (fun v => ArrayProgram.shiftRound (FF.sc P tb w x i * v) 16) =
      tabl P.d (FF.xr P tb w x i) := tabl_map _ _ _
  have h3 := ffExp3_is P tb w L x i Tmax t rows hT W hW hn hE
  have e1 : ffExp1 (shapeOf P Tmax) t (lsOf P) W (tabl P.d (x i))
        (tabl P.d (FF.m P x i)) (tabl P.nexp (FF.lr P w x i)) =
      ffExp3 (shapeOf P Tmax) t (lsOf P) W (tabl P.d (x i)) (tabl P.d (FF.m P x i))
        (FF.es P w x i) (tabl P.d (FF.xr P tb w x i)) := by
    unfold ffExp1 ffExp2
    rw [hes, tabl_get _ hlt, hT.sigm, ← hxr]
    rfl
  have hall : ((tabl P.nexp (FF.lw P w x i)).all fun l => ArrayProgram.fits16 ((l - l % 8) / 8)) =
        true ↔
      ∀ e < P.nexp, Fits16 (FF.ly P w x i e) :=
    (tabl_all _ _ _).trans (forall₂_congr fun e _ => fits16_iff _)
  unfold ffExp0
  rw [hlr, e1]
  by_cases ha : ∀ e < P.nexp, Fits16 (FF.ly P w x i e)
  · rw [if_neg (by rw [hall.2 ha]; simp)]
    exact h3.iff ⟨fun h => ⟨ha, h⟩, fun h => h.2⟩
  · have hb : ((tabl P.nexp (FF.lw P w x i)).all fun l => ArrayProgram.fits16 ((l - l % 8) / 8)) =
        false := by
      rw [← Bool.not_eq_true]; exact fun h => ha (hall.1 h)
    rw [if_pos (by rw [hb]; rfl)]
    exact ⟨fun h => absurd h.1 ha, fun _ => rfl⟩

/-- The feed-forward block: under hT, hW (the `variable` line above) and hn the array program
computes the library's formulas. -/
theorem feedForward_is (hn : 0 < P.nexp) :
    Is (ArrayProgram.feedForward (shapeOf P Tmax) t (lsOf P) W L (tabl P.T fun i => tabl P.d (x i)))
      (FF.OK P tb w L x) (tabl P.T fun i => tabl P.d (FF.x'' P tb w L x i)) := by
  rw [feedForward_eq]
  refine Is.mapM_tabl
    (p := fun i =>
        NORM.OK P.n2 P.d (x i) ∧
        (hasExperts L → ∀ e < P.nexp, Fits16 (FF.ly P w x i e)) ∧
        ∀ j < FF.units P L,
          UNIT.OK P.d (FF.z P tb w L x i j) (FF.wg P w L x i j) (FF.wu P w L x i j)
            (FF.kG P L j) (FF.kU P L j)) fun i _ => ?_
  refine Is.bind (rmsNorm_is P.n2 P.d (x i)) ?_
  show Is (if ArrayProgram.hasExperts L = true then _ else _) _ _
  by_cases hE : hasExperts L
  · rw [if_pos ((hasExperts_iff L).2 hE)]
    have h := ffExp0_is P tb w L x i Tmax t rows hT W hW hn hE
    have e : ArrayProgram.project (tabl P.d (NORM.out P.n2 P.d (x i))) W.Wrouter
          (shapeOf P Tmax).experts (lsOf P).kr =
        tabl P.nexp (FF.lw P w x i) :=
      (project_tabl _ _ _ _ _).trans
        (tabl_congr fun e he => congrArg (rhu · P.kr) (dot_congr fun j hj => hW.Wr hE j hj e he))
    rw [e]
    exact h.iff ⟨fun a => ⟨fun _ => a.1, a.2⟩, fun a => ⟨a.1 hE, a.2⟩⟩
  · rw [if_neg fun h => hE ((hasExperts_iff L).1 h)]
    exact (ffDense_is P tb w L x i Tmax t rows hT W hW hE).iff
      ⟨fun a => ⟨fun h => absurd h hE, a⟩, fun a => a.2⟩

end Block

end IntegerModel.Runnable
