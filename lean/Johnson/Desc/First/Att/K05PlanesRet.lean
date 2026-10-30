-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05PlanesRet.lean: kind K5: FOUR GENERAL LAWS ON THE LOOKUP ARGUMENT's RUN OF CLAIMS "planes" (K3.planesRun, Johnson/Desc/First/Look/K3Runs.lean), for the public test that is tied to it at the verifier's state after the kind's sub-protocol.
Main names:
  planesRun_ret: THE RUN RETURNS where a ledger is open, something was received, the claims are not yet made, the caller's readers return, and the three claims' own text (planeClaimsOwn) returns. The last is a premise: the lookup argument's files' to show.
  planes_cov: EVERY ENTRY THAT A CLAIM OF THE RUN NAMES LIES IN THE TABLES' PART (Cov, Att/Claims/Covered.lean) where the caller's forms on the columns do and the start form of the leaves' sumcheck is bare. planes_rowsIn
    (Johnson/Top/H/Keep/PlanesRowsIn.lean) is general in a property of (array, row); the public test also asks the entry's index: so the same walk, by the cuts of the run that that file's proof calls (planesRun_cut, Johnson/Top/H/K3RunsLaw.lean; planes_heard, Johnson/Top/H/Keep/K3Inv.lean), at a predicate that holds the index.
  planes_ns: the run keeps the number of slots (from a ledger with its sizes).
  lateOk_front: the public test lateOk AT THE LEDGER IN FRONT OF A RUN, at the list of the slots that are free in front and filled behind: it holds where the run adds no slot. (Johnson/Desc/First/Batch/ReaderOf.lean's lateOk_lateOf speaks at the ledger behind.)

IS IT EMPTY HERE? Implications.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.PlanesRowsIn
import Johnson.Desc.First.Att.Claims.Covered
import Johnson.Desc.First.Batch.ReaderOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Road.Rows (Bare)
open Cb.Fo.PlaneClaims (planesAff countAff)
open VerifiableInference.Desc.K3 (Readers planesRun unpaid)
open VerifiableInference.Desc.First.Look (planeClaimsOwn planesAddedF paidF)
open VerifiableInference.Desc.K9 (lateOk lateOf)
open VerifiableInference.OnPublicFiles (planesRun_cut planes_heard quiet_need)
open _root_.Fo.Tp (got)
open K5Law (Cov cov_ofConst cov_slot cov_addMul cov_add cov_sub cov_scale)

/-! ## The run returns -/

/-- **The run returns.** A TWIN, IN CONTENT, OF THE LAST STEP OF planesRun_answers (Johnson/Desc/Kinds/Law/SilentPlanes.lean), which names the run's value and stands at the seat K3.seatCalls asClaim. KEPT, BECAUSE IT IS GENERAL IN THE SEAT: the maker of claims at the seated link is a
letter where this is called (Att/K05PlanesIn.lean); that it is asClaim is shown by nobody. -/
theorem planesRun_ret {S Cl : Type} (seat : VerifiableInference.Desc.K3.Seat S Cl) (lm : ℕ) (readers : Readers S) (n : ℕ) {s : S} {F : Fork} {g : Forest.Heard}
    {r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)} (hf : seat.fork s = some F) (hg : seat.heard s = some g)
    (hu : unpaid F g.owedPlanes = true) (hr : readers s = some r)
    (hc : ∃ z, planeClaimsOwn g lm (fun e col => Fl.need (r.1 e col)) (fun col => Fl.need (r.2 col)) F [] = some z) :
    ∃ cl s', planesRun seat lm readers n s = .ok (cl, s') := by
  obtain ⟨⟨fs, G, u⟩, hz⟩ := hc
  refine ⟨fs.toList.map seat.claim, seat.mark s (G.paid g.owedPlanes), ?_⟩
  unfold planesRun
  simp only [hf, hg, hu, hr, VerifiableInference.Desc.named, VerifiableInference.Desc.need, bind, Except.bind, if_true, Fl.andThen, hz,
    planesAddedF, paidF, Fl.change, Option.map_some, pure, Fl.ret, Except.pure]

/-! ## The entries -/

section Cov
variable {t K nW : ℕ}

theorem cov_bare {f : Aff} (h : Bare f) : Cov t K nW f := fun e he => (h (fun _ _ => False) e he).elim

theorem cov_empty : Cov t K nW ({} : Aff) := by
  intro e he
  cases he

theorem cov_foldl {α : Type} (step : Aff → α → Aff) (h : ∀ f c, Cov t K nW f → Cov t K nW (step f c)) :
    ∀ (l : List α) (f0 : Aff), Cov t K nW f0 → Cov t K nW (l.foldl step f0)
  | [], _, h0 => h0
  | c :: l, f0, h0 => cov_foldl step h l (step f0 c) (h f0 c h0)

theorem cov_got (o : Option Aff) (h : ∀ f, o = some f → Cov t K nW f) (F : Fork) (c : Tape) : Cov t K nW (got (Fl.need o) F c) := by
  cases o with
  | none => exact cov_empty
  | some f => exact h f rfl

theorem cov_addSlots {a : Aff} (first : ℕ) (form : Array E) (ha : Cov t K nW a) : Cov t K nW (addSlots a first form) := by
  unfold addSlots
  rw [← Array.foldl_toList]
  have key : ∀ (l : List E) (s : ℕ × Aff), Cov t K nW s.2 → Cov t K nW (l.foldl addSlot s).2 := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons x l ih => exact fun s hs => ih _ (cov_addMul hs (cov_slot _) _)
  exact key _ _ ha

theorem cov_rowForm (p : Psc) (S0 : E) {kept : Aff} (hs : Cov t K nW p.start) (hk : Cov t K nW kept) : Cov t K nW (p.rowForm S0 kept) := by
  unfold Psc.rowForm
  exact cov_addMul (cov_addMul (cov_addSlots _ _ (cov_ofConst _)) (cov_sub (cov_ofConst _) hs) _) hk _

/-- **Every entry that a claim of the run names lies in the tables' part.** -/
theorem planes_cov {S Cl : Type} (seat : VerifiableInference.Desc.K3.Seat S Cl) (form : Cl → Aff) (hform : ∀ a, form (seat.claim a) = a) (lm : ℕ)
    (readers : Readers S) {n : ℕ} {s s' : S} {cl : List Cl} {g : Forest.Heard} (hg : seat.heard s = some g)
    (hrun : planesRun seat lm readers n s = .ok (cl, s')) (hs : Bare g.leaves.start)
    (hb : ∀ r, readers s = some r → ∀ e col f, r.1 e col = some f → Cov t K nW f)
    (hp : ∀ r, readers s = some r → ∀ col f, r.2 col = some f → Cov t K nW f) :
    ∀ c ∈ cl, Cov t K nW (form c) := by
  obtain ⟨F, g1, e1, e2⟩ := planes_heard seat lm readers hrun
  obtain rfl : g = g1 := Option.some.inj (hg.symm.trans e2)
  obtain ⟨r, rows, G, u, hr, h1, rfl, _⟩ := planesRun_cut seat lm readers e1 e2 hrun
  obtain ⟨_, row, p', h2, rfl⟩ := _root_.Fo.Tp.planeClaims_run g lm _ _ (fun _ _ => quiet_need _)
    (fun _ => quiet_need _) F G [] u rows h1
  obtain ⟨-, -, -, -, -, -, rfl, -⟩ := _root_.Fo.Tp.pscRow_ok _ _ _ _ _ _ _ _ _ h2
  have b0 : ∀ e, Cov t K nW (planesAff g lm e fun col => got (Fl.need (r.1 e col)) F []) := by
    intro e
    unfold planesAff
    exact cov_foldl _ (fun f col hf => cov_addMul hf (cov_got _ (hb r hr e col) F []) _) _ _ (cov_ofConst _)
  have c0 : Cov t K nW (countAff g lm fun col => got (Fl.need (r.2 col)) F []) := by
    unfold countAff
    exact cov_foldl _ (fun f col hf => cov_add hf (cov_got _ (hp r hr col) F [])) _ _ (cov_ofConst _)
  intro c hc
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hc
  rw [hform]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact cov_rowForm _ _ (cov_bare hs) (cov_scale (b0 0) _)
  · exact cov_sub (cov_slot _) (b0 1)
  · exact c0

end Cov

/-! ## The number of slots; the late slots -/

/-- **The run keeps the number of slots.** G': the ledger that the run's mark lays. -/
theorem planes_ns {S Cl : Type} (seat : VerifiableInference.Desc.K3.Seat S Cl) (lm : ℕ) (readers : Readers S) {n : ℕ} {s s' : S} {cl : List Cl} {F : Fork}
    {g : Forest.Heard} (hf : seat.fork s = some F) (hg : seat.heard s = some g) (hz : PscRun.Sized F)
    (hrun : planesRun seat lm readers n s = .ok (cl, s')) : ∃ G', s' = seat.mark s G' ∧ G'.ns = F.ns := by
  obtain ⟨r, rows, G, u, hr, h1, _, es⟩ := planesRun_cut seat lm readers hf hg hrun
  obtain ⟨_, row, p', h2, _⟩ := _root_.Fo.Tp.planeClaims_run g lm _ _ (fun _ _ => quiet_need _)
    (fun _ => quiet_need _) F G [] u rows h1
  obtain ⟨-, -, -, -, -, hh, -, -⟩ := _root_.Fo.Tp.pscRow_ok _ _ _ _ _ _ _ _ _ h2
  exact ⟨_, es, (PscRun.hideRun_ok F G _ _ _ hz hh).1.ns⟩

/-- **lateOk at the ledger in front of a run.** -/
theorem lateOk_front (a : VerifiableInference.Desc.K9.Part) (G' : Fork) (h : G'.ns ≤ a.F.ns) : lateOk (lateOf a.F G') a = true := by
  unfold lateOk
  refine List.all_eq_true.2 fun x hx => ?_
  unfold lateOf at hx
  obtain ⟨j, hj, hx'⟩ := List.mem_filterMap.1 hx
  by_cases hc : (!(a.F.gotF.getD j false) && G'.gotF.getD j false) = true
  · rw [if_pos hc] at hx'
    obtain rfl := Option.some.inj hx'
    have h1 : (!(a.F.gotF.getD j false)) = true := (Bool.and_eq_true _ _ ▸ hc).1
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨Nat.lt_of_lt_of_le (List.mem_range.1 hj) h, Or.inl h1⟩
  · rw [if_neg hc] at hx'
    cases hx'

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.planesRun_ret
#print axioms VerifiableInference.Desc.First.Att.P.planes_cov
#print axioms VerifiableInference.Desc.First.Att.P.planes_ns
#print axioms VerifiableInference.Desc.First.Att.P.lateOk_front
