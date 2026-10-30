-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/PlanesFormsInT.lean: THE TABLE OF JOINTS' PUBLIC TEST formsInT
(Johnson/Desc/First/Batch/FormsIn.lean) AT THE LOOKUP's RUN "planes", AT THE BORDER RIGHT BEHIND THE
OUTPUT HEAD's OWN SUB-PROTOCOL, WHERE THE READER IS THE SILENT ONE: IT SAYS YES. The like of
Law/K6FormsInT.lean's k6_formsInT for the fifth name. Definitions, statements and proofs.

  SlotsAt Q f      every slot that the form f names has the property Q; slotsAt_addMul, _slot,
                   _addSlots, _rowForm, _fold: the forms' operations (by Law/SlotsFilled.lean's
                   addMul_slots).
  planeForms_slots which slots the three forms name: the hiding polynomial's of the sumcheck over
                   the leaves; its starting form's; the slot of the bits' value; the caller's
                   forms'.
  late_some, lateOk_front, slotIn_late   a slot that the run itself fills is LATE, and passes the
                   table's two tests on late slots at the ledger in front of the run.
  planes_formsInT  MAIN: at a state at which the tables can be made.
  planes_formsInT_behind   the same behind the accept of the head's own sub-protocol.

WHAT IT IS NOT. An implication. NAMED PREMISES THAT NOBODY PAYS HERE: Law/SilentAll.lean's · the
slots of the starting form of the sumcheck over the leaves, and the slot of the bits' value, are
filled (NOT CHECKED HERE: THE FIRST STANDS IN NO FIELD OF THE LOOKUP's ITEM left: a fact
along the fold) · hEnt (the table's test on an entry says yes at the reads' array, row 0, below its
width) · hMask (the mask row's seat is there) · hFree (no slot of the merge is laid yet). The proof
of planes_formsInT repeats some forty lines of Law/SilentAll.lean's planes_answers: a near
twin inside a proof. Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Desc.Kinds.Law.SilentAll
import Johnson.Desc.Kinds.Law.SlotsFilled

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE subE)
open OnBytes.Model (Fork Aff HTree)
open VerifiableInference.Desc.First (S HeadOwn)
open Planes

/-- Every slot that the form names has the property Q. -/
def SlotsAt (Q : Nat → Prop) (f : Aff) : Prop := ∀ x ∈ f.slots.toList, Q x.1

theorem slotsAt_of_empty (Q : Nat → Prop) {f : Aff} (h : f.slots = #[]) : SlotsAt Q f := by
  intro x hx
  rw [h] at hx
  exact absurd hx (by simp)

theorem slotsAt_slot {Q : Nat → Prop} {j : Nat} (h : Q j) : SlotsAt Q (Aff.slot j) := by
  intro x hx
  obtain rfl : x = (j, oneE) := by simpa [Aff.slot] using hx
  exact h

theorem slotsAt_addMul {Q : Nat → Prop} {a b : Aff} (ha : SlotsAt Q a) (hb : SlotsAt Q b)
    (k : E) : SlotsAt Q (Aff.addMul a b k) := by
  intro x hx
  rw [addMul_slots] at hx
  rcases List.mem_append.mp hx with h | h
  · exact ha x h
  · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp h
    exact hb z hz

theorem slotsAt_addSlots {Q : Nat → Prop} {a : Aff} (ha : SlotsAt Q a) (first : Nat)
    (form : Array E) (hw : ∀ i, i < form.size → Q (first + i)) :
    SlotsAt Q (OnBytes.Model.addSlots a first form) := by
  unfold OnBytes.Model.addSlots
  rw [← Array.foldl_toList]
  have key : ∀ (l : List E) (p : Nat × Aff), SlotsAt Q p.2 → (∀ i, i < l.length → Q (p.1 + i)) →
      SlotsAt Q (l.foldl OnBytes.Model.addSlot p).2 := by
    intro l
    induction l with
    | nil => exact fun _ h _ => h
    | cons y l ih =>
      intro p hp hq
      rw [List.foldl_cons]
      refine ih _ (slotsAt_addMul hp (slotsAt_slot (by simpa using hq 0 (by simp))) y)
        fun i hi => ?_
      have := hq (i + 1) (by simpa using hi)
      show Q (p.1 + 1 + i)
      rwa [Nat.add_assoc, Nat.add_comm 1 i]
  exact key _ _ ha (by simpa using hw)

theorem slotsAt_rowForm {Q : Nat → Prop} (p : OnBytes.Model.Psc) (S0 : E) {kept : Aff}
    (hw : ∀ i, i < p.walk.1.length → Q (p.first + i)) (hs : SlotsAt Q p.start)
    (hk : SlotsAt Q kept) : SlotsAt Q (p.rowForm S0 kept) := by
  unfold OnBytes.Model.Psc.rowForm
  exact slotsAt_addMul (slotsAt_addMul
    (slotsAt_addSlots (slotsAt_of_empty Q rfl) _ _ (by simpa using hw))
    (slotsAt_addMul (slotsAt_of_empty Q rfl) hs _) _) hk _

theorem slotsAt_fold {Q : Nat → Prop} (step : Aff → Nat → Aff) (n : Nat)
    (hstep : ∀ f col, col < n → SlotsAt Q f → SlotsAt Q (step f col)) {a : Aff}
    (ha : SlotsAt Q a) : SlotsAt Q ((List.range n).foldl step a) := by
  induction n with
  | zero => exact ha
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    exact hstep _ n (Nat.lt_succ_self n)
      (ih fun f col hc => hstep f col (Nat.lt_succ_of_lt hc))

/-- **WHICH SLOTS THE THREE FORMS OF "planes" NAME**: those of the hiding polynomial of the sumcheck
over the leaves; those of its starting form; the slot of the bits' value; the caller's forms'. -/
theorem planeForms_slots {Q : Nat → Prop} (g : OnBytes.Model.Forest.Heard) (lm : Nat)
    (bit : Nat → Nat → Aff) (pin : Nat → Aff)
    (hw : ∀ i, i < g.leaves.walk.1.length → Q (g.leaves.first + i))
    (hs : SlotsAt Q g.leaves.start) (hB : Q g.sBit)
    (hb : ∀ e col, col < nCols g lm → SlotsAt Q (bit e col))
    (hp : ∀ col, col < nCols g lm → SlotsAt Q (pin col)) :
    ∀ f ∈ (planeForms g lm bit pin).toList, SlotsAt Q f := by
  have hat : ∀ e, SlotsAt Q (atForm g lm e bit) := fun e =>
    slotsAt_fold _ _ (fun f col hc hf => slotsAt_addMul hf (hb e col hc) _)
      (slotsAt_of_empty Q rfl)
  intro f hf
  unfold planeForms at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact slotsAt_rowForm _ _ hw hs (slotsAt_addMul (slotsAt_of_empty Q rfl) (hat 0) _)
  · exact slotsAt_addMul (slotsAt_slot hB) (hat 1) _
  · exact slotsAt_fold _ _ (fun f col hc hf => slotsAt_addMul hf (hp col hc) _)
      (slotsAt_of_empty Q rfl)

/-- A slot that is free in front and filled behind, below the number of slots, is late. -/
theorem late_some {F G : Fork} {j : Nat} (hj : j < G.ns) (h0 : F.gotF.getD j false = false)
    (h1 : G.gotF.getD j false = true) : (K9.lateAt (K9.lateOf F G) j).isSome = true := by
  unfold K9.lateAt
  rw [Option.isSome_map, List.find?_isSome]
  refine ⟨(j, G.vp.getD j zeroE, G.mf.getD j zeroE), ?_, by simp⟩
  unfold K9.lateOf
  refine List.mem_filterMap.2 ⟨j, List.mem_range.2 hj, ?_⟩
  rw [if_pos (by simp [h0, h1])]

/-- Every late slot of such a list passes the table's test on late slots, at the ledger in front. -/
theorem lateOk_front (a : K9.Part) (G : Fork) (hns : G.ns = a.F.ns) :
    K9.lateOk (K9.lateOf a.F G) a = true := by
  unfold K9.lateOk
  refine List.all_eq_true.2 fun x hx => ?_
  unfold K9.lateOf at hx
  obtain ⟨j, hj, hx'⟩ := List.mem_filterMap.1 hx
  by_cases hc : (!(a.F.gotF.getD j false) && G.gotF.getD j false) = true
  · rw [if_pos hc] at hx'
    obtain rfl := Option.some.inj hx'
    have h1 : a.F.gotF.getD j false = false := by
      simpa using (Eq.mp (Bool.and_eq_true _ _) hc).1
    have h2 : j < a.F.ns := by
      rw [← hns]
      exact List.mem_range.1 hj
    simp [h1, h2]
  · rw [if_neg hc] at hx'
    exact nomatch hx'

/-- A late slot passes the table's test on slots. -/
theorem slotIn_late (own : List (Nat × Nat)) (late : List (Nat × E × E)) (a : K9.Part) (j : Nat)
    (hj : j < a.F.ns) (hM : (K9.maskSeat own a).isSome = true)
    (hl : (K9.lateAt late j).isSome = true) : K9.slotIn own none late a j = true := by
  unfold K9.slotIn
  simp [hj, hM, hl]

/-- **THE TABLE OF JOINTS' PUBLIC TEST formsInT AT THE RUN "planes" SAYS YES**, at a verifier's
state t at which the tables can be made (e) and the reader is the silent one. -/
theorem planes_formsInT (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH) (b : Nat)
    (states : Nat → List (K9.RunOf S)) (hSt : PlanesStates (readsOf W) P.h.lmbH states b)
    (hBk : PlanesBack (readsOf W) P.h.lmbH states b) (Rd : K9.Readers) (own : List (Nat × Nat))
    (t e : S) (a : K9.Part) (ha : K9.segAt? t = some a)
    (hRd : Rd.forms b "planes" t = k6Silent P states b "planes" t)
    (he : withTables P t = some e) (tr : HTree) (htr : a.F.trees[readsOf W]? = some tr)
    (hK : tr.K ≠ 0) (hwide : P.hp.nU.getD 2 0 ≤ tr.K) (hR1 : tr.R = 1) (hWL : WellLaid a.F)
    (gk : OnBytes.Model.Forest.Heard) (hgk : e.lookHeard? = some gk) (hL : LeavesReady gk a.F)
    (hok : First.Look.planesOk gk.shape P.h.lmbH = true)
    (hlen : nCols gk P.h.lmbH ≤ (P.hp.tl.mats.getD (P.h.NHf + 1 + 1) {}).k *
      ((P.hp.tl.mats.getD (P.h.NHf + 1 + 1) {}).m / 2 ^ P.h.lmbH))
    (hbare : gk.leaves.start.ents = #[])
    (hstart : ∀ x ∈ gk.leaves.start.slots.toList, OnBytes.PscRun.Filled a.F x.1)
    (hsBit : OnBytes.PscRun.Filled a.F gk.sBit)
    (hEnt : ∀ x : OnBytes.Model.Ent, x.tree = readsOf W → x.row = 0 → x.idx < tr.K →
      K9.entInT own a x = true)
    (hMask : (K9.maskSeat own a).isSome = true) (hFree : K9.mergeOf t = none) :
    K9.formsInT Rd own b "planes" t = true := by
  have hF : e.fork? = some a.F := (fork_withTables he).1.trans (seg_fork ha)
  obtain ⟨run, hf, _⟩ := hSt
  obtain ⟨a0, cov, x0, tt, ha0, _, _, _, htab, hee⟩ := (withTables_iff P t e).1 he
  have ho : e.here = .head { a0 with t := some tt } := by rw [hee]
  obtain ⟨_, _, e0, e1, eP, _, _, h0, h1, hP, l0, l1, lP, _⟩ := tables_planes htab
  have hB := below_of_width P t (readsOf W) (fun e' F2 tr2 he' hF2 htr2 => by
    obtain rfl := Option.some.inj (he.symm.trans he')
    obtain rfl : a.F = F2 := Option.some.inj (hF.symm.trans hF2)
    obtain rfl : tr = tr2 := Option.some.inj (htr.symm.trans htr2)
    exact hwide) e _ tt a.F tr he ho rfl hF htr
  have hr := planesAt_readers (readsOf W) ho hF rfl htr hK
  have hcols : ((a.F.trees[readsOf W]?).map (·.K)).getD 1 = tr.K := by
    rw [htr]
    rfl
  rw [hcols] at hr
  -- each reader's form: there, on row 0 of the reads' array, and it names no slot
  have one : ∀ (xr : PlaneRead) (u : String × Nat × Nat) (col : Nat),
      tt.tab.find? (fun e => e.1 == (match xr with
        | .bits0 => "bH-bits-0" | .bits1 => "bH-bits-1" | .pin => "bH-pin")) = some u →
      col < u.2.2 →
      (planeEntry tt.tab (readsOf W) tr.K xr col).isSome = true ∧
        Row0 (readsOf W) tr.K ((planeEntry tt.tab (readsOf W) tr.K xr col).getD {}) ∧
        ((planeEntry tt.tab (readsOf W) tr.K xr col).getD {}).slots = #[] := by
    intro xr u col hfind hi
    have hm := hB u (List.mem_of_find?_eq_some hfind)
    rw [planeEntry_at hfind hi]
    exact ⟨rfl, row0_entryAt _ _ _ (by omega), rfl⟩
  have hb : ∀ q col, col < nCols gk P.h.lmbH →
      (planeEntry tt.tab (readsOf W) tr.K (if q == 0 then .bits0 else .bits1) col).isSome = true ∧
        Row0 (readsOf W) tr.K ((planeEntry tt.tab (readsOf W) tr.K
          (if q == 0 then .bits0 else .bits1) col).getD {}) ∧
        ((planeEntry tt.tab (readsOf W) tr.K
          (if q == 0 then .bits0 else .bits1) col).getD {}).slots = #[] := by
    intro q col hc
    by_cases hq : (q == 0) = true
    · rw [if_pos hq]
      exact one .bits0 e0 col h0 (by rw [l0]; omega)
    · rw [if_neg hq]
      exact one .bits1 e1 col h1 (by rw [l1]; omega)
  have hp : ∀ col, col < nCols gk P.h.lmbH →
      (planeEntry tt.tab (readsOf W) tr.K .pin col).isSome = true ∧
        Row0 (readsOf W) tr.K ((planeEntry tt.tab (readsOf W) tr.K .pin col).getD {}) ∧
        ((planeEntry tt.tab (readsOf W) tr.K .pin col).getD {}).slots = #[] :=
    fun col hc => one .pin eP col hP (by rw [lP]; omega)
  obtain ⟨G, hrun, hM⟩ := Part.MaskedSum.hideRun_returns a.F gk.leaves.first
    (Array.replicate gk.leaves.walk.1.length zeroE) (subE zeroE oneE)
    (by rw [Array.size_replicate]; exact hL.free)
  rw [Array.size_replicate] at hM
  have hy := planesRun_answers P.h.lmbH (callerReaders (planesAt (readsOf W))) 0 e a.F G gk _ hF
    hgk hL.planes hr hok (fun q col hc => (hb q col hc).1) (fun col hc => (hp col hc).1) hL.flags
    hrun
  have hs := hBk run hf 0 e _ hy
  have hrow := planeForms_ents (Q := fun tree row idx => tree = readsOf W ∧ row = 0 ∧ idx < tr.K)
    gk P.h.lmbH _ _ hbare (fun q col hc => (hb q col hc).2.1) (fun col hc => (hp col hc).2.1)
  -- the slots
  have hslot := planeForms_slots
    (Q := fun j => K9.slotIn own none (K9.lateOf a.F (G.paid gk.owedPlanes)) a j = true)
    gk P.h.lmbH _ _
    (fun i hi => by
      have hfr := hL.free
      have hj : gk.leaves.first + i < a.F.ns := by
        have := hfr.1
        omega
      refine slotIn_late own _ a _ hj hMask (late_some (by
        show gk.leaves.first + i < G.ns
        rw [hM.1]
        exact hj) ?_ ?_)
      · have h0' := hfr.2.2 (gk.leaves.first + i) (by omega) (by omega)
        have hsz : gk.leaves.first + i < a.F.gotF.size := by
          rw [hfr.2.1]
          exact hj
        simp only [Array.getD, hsz, dif_pos] at h0' ⊢
        exact h0'
      · show G.gotF.getD (gk.leaves.first + i) false = true
        rw [hM.2.2.2, if_pos ⟨by omega, by omega⟩])
    (fun x hx => slotIn_filled own _ a x.1 hWL hMask (hstart x hx))
    (slotIn_filled own _ a gk.sBit hWL hMask hsBit)
    (fun q col hc => slotsAt_of_empty _ (hb q col hc).2.2)
    (fun col hc => slotsAt_of_empty _ (hp col hc).2.2)
  -- the reader's answer, written out
  have hR : k6Silent P states b "planes" t = some
      { forms := ((planeForms gk P.h.lmbH
          (fun q col => (planeEntry tt.tab (readsOf W) tr.K
            (if q == 0 then .bits0 else .bits1) col).getD {})
          fun col => (planeEntry tt.tab (readsOf W) tr.K .pin col).getD {}).toList.map
            asClaim).map (·.form)
        late := K9.lateOf a.F (G.paid gk.owedPlanes) } := by
    unfold k6Silent
    rw [he]
    show K9.readerOf states b "planes" e = _
    unfold K9.readerOf
    rw [hf]
    simp only [Option.bind_some]
    rw [hs, hF]
    simp only
    rw [VerifiableInference.OnPublicFiles.fork_putFork e a.F _ hF]
    simp only [Option.bind_some]
    rw [if_pos]
    rw [List.all_eq_true]
    intro c hc
    obtain ⟨f, hfm, rfl⟩ := List.mem_map.1 hc
    have h1' : f.ents.all (K9.ownRow a.F) = true := ownRow_of_row0 (hrow f hfm) htr hR1
    show ((asClaim f).runs.isEmpty && (asClaim f).eqFirst.isNone &&
      f.ents.all (K9.ownRow a.F)) = true
    rw [h1']
    rfl
  unfold K9.formsInT
  rw [ha, hRd, hR]
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨lateOk_front a _ hM.1, fun f hfm => ?_⟩
  rw [List.map_map] at hfm
  obtain ⟨f', hf', rfl⟩ := List.mem_map.1 hfm
  show K9.affInT own (K9.mergeOf t) _ a f' = true
  unfold K9.affInT
  rw [hFree]
  simp only [Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun x hx => hEnt x (hrow f' hf' x hx).1 (hrow f' hf' x hx).2.1 (hrow f' hf' x hx).2.2,
    fun x hx => hslot f' hf' x hx⟩

/-- **THE SAME BEHIND THE ACCEPT OF THE HEAD's OWN SUB-PROTOCOL**: s: the verifier's state in front;
t: behind. What is asked of the lookup's leavings is asked at s. -/
theorem planes_formsInT_behind (W : OnBytes.Model.Verify.Public) (l : Nat)
    (blk : VerifiableInference.Desc.Block S Unit) (hb : blockOf W l = some blk) (s t : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (Sound.below blk).decide s rs gs = .ok t) (hOn : K6On W s) (P : K8.ReadsQuiet.PH)
    (hP : P.h = W.hS) (hB : tabsPlanB P.h P.L P.hp = true) (hRB : readsPlanB P.h P.hp = true)
    (hcov : ∃ cov, t.covered P.h.T P.h.V = .ok cov) (a : K9.Part) (ha : K9.segAt? t = some a)
    (tr : HTree) (htr : a.F.trees[readsOf W]? = some tr) (hK : tr.K ≠ 0)
    (hwide : P.hp.nU.getD 2 0 ≤ tr.K) (hR1 : tr.R = 1) (bP : Nat)
    (states : Nat → List (K9.RunOf S)) (hSt : PlanesStates (readsOf W) P.h.lmbH states bP)
    (hBk : PlanesBack (readsOf W) P.h.lmbH states bP) (Rd : K9.Readers) (own : List (Nat × Nat))
    (hRd : Rd.forms bP "planes" t = k6Silent P states bP "planes" t) (Fs : Fork)
    (hFs : s.fork? = some Fs) (gk : OnBytes.Model.Forest.Heard) (hgk : s.lookHeard? = some gk)
    (hL : LeavesReady gk Fs) (hzj : W.hS.ls ≤ (OnBytes.Model.Head.zjOf P.L gk 0).size)
    (hok : First.Look.planesOk gk.shape W.hS.lmbH = true)
    (hlen : nCols gk P.h.lmbH ≤ (P.hp.tl.mats.getD (P.h.NHf + 1 + 1) {}).k *
      ((P.hp.tl.mats.getD (P.h.NHf + 1 + 1) {}).m / 2 ^ P.h.lmbH))
    (hlv : gk.leaves.start.ents = #[])
    (hstart : ∀ x ∈ gk.leaves.start.slots.toList, OnBytes.PscRun.Filled Fs x.1)
    (hsBit : OnBytes.PscRun.Filled Fs gk.sBit)
    (hEnt : ∀ x : OnBytes.Model.Ent, x.tree = readsOf W → x.row = 0 → x.idx < tr.K →
      K9.entInT own a x = true)
    (hMask : (K9.maskSeat own a).isSome = true) (hFree : K9.mergeOf t = none) :
    K9.formsInT Rd own bP "planes" t = true := by
  have hF : t.fork? = some a.F := seg_fork ha
  obtain ⟨Fs', Ft, f1, f2, hLat, hWt, hh⟩ := below_ledgers W l blk hb s t rs gs h hOn
  obtain rfl : Fs' = Fs := Option.some.inj (f1.symm.trans hFs)
  obtain rfl : Ft = a.F := Option.some.inj (f2.symm.trans hF)
  have hgt : t.lookHeard? = some gk := hh.trans hgk
  obtain ⟨hcan, hd⟩ := canonical_of_below blk s t rs gs h
  have hok' : 5 ≤ W.hS.lmbH ∧ W.hS.lmbH ≤ gk.shape.kT + 5 := by
    unfold First.Look.planesOk at hok
    simpa using hok
  have one : ∀ g', s.lookHeard? = some g' → g' = gk := fun g' hg' =>
    Option.some.inj (hg'.symm.trans hgk)
  obtain ⟨i, hu, rfl⟩ := Option.map_eq_some_iff.mp hb
  have hr : readsOf W = i := by
    unfold readsOf
    rw [hu]
    rfl
  subst hr
  have e1 : (seatAt W.hS (readsOf W)).ledger s = Fs' := by
    show s.fork?.getD {} = _
    rw [hFs]
    rfl
  have e2 : (seatAt W.hS (readsOf W)).ledger t = a.F := by
    show t.fork?.getD {} = _
    rw [hF]
    rfl
  have hLt : LeavesReady gk a.F := by
    have hW : WellLaid Fs' := by
      have h0 : WellLaid ((seatAt W.hS (readsOf W)).ledger s) := hOn.1
      rw [e1] at h0
      exact h0
    obtain ⟨n, _, T⟩ := blockAt_takes W.hS (readsOf W) (workOf W) l s t rs gs
      (by rw [e1]; exact ⟨hW.2.1, hW.2.2, hW.1⟩) hd
    have ho := blockAt_owed W.hS (readsOf W) (workOf W) l s t rs gs hd
    rw [e1, e2] at T ho
    exact hL.takes T ho
  obtain ⟨e, v, he, _, _, hlk, _⟩ := letters_behind W l hd hOn.1 hcan hOn.2.1 P hP hB hRB hcov
    hOn.2.2.1 (fun g' hg' => by rw [one g' hg']; exact hzj) hok'.1
    (fun g' hg' => by rw [one g' hg']; exact hok'.2) a.F tr hF htr hK hwide
  exact planes_formsInT W P bP states hSt hBk Rd own t e a ha hRd he tr htr hK hwide hR1 hWt gk
    (hlk.trans hgt) hLt (by rw [hP]; exact hok) hlen hlv
    (fun x hx => (hLat.keep x.1 (hstart x hx)).1) (hLat.keep gk.sBit hsBit).1 hEnt hMask hFree

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.planes_formsInT_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.planes_formsInT
#print axioms VerifiableInference.Desc.Kinds.Head.Law.planeForms_slots
