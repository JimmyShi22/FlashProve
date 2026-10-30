-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/InT/FormsInTOwn.lean: THE SENTENCE `FormsInTOwn` (InT/Statement.lean), PROVED:
BEHIND AN ACCEPT OF K4's SUB-PROTOCOL THE TABLE OF JOINTS' PUBLIC TEST formsInT IS TRUE AT K4's TWO
RUNS, at the verifier's state that the accept leaves, under the premises that the statement names.
Statements and proofs: calls.

  `filled_lt`: in a ledger with arrays of the right sizes a filled slot lies below the number of
    slots.
  `entInT_of_reads`: where `readsThereB A iU3 n` accepts, an entry of array iU3, row 0, index below
    n, passes the test on an entry in front of the second sending.
  `ownRow_of_one`: where `oneRowB F iU3` accepts, such an entry names row 0 of an array with one
    own row.
  `reader_pointwise`: where the seat's tie holds at s (`StatesAt`), the reader at the seat's states
    is the reader at K4's sub-protocol's own list.
  `inT_of`: THE TEST's CLAUSES OUT OF THEIR PIECES (`InTAt`), for one run: the reader's answer
    (forms ff, the slots that are late from F to G₁) · every entry as above · every slot filled in
    G₁ and not the merge's.
  **`inT_ofStates`** : `InTOfStates` · **`inT_ofLink`** : `InTOfLink`: the public test itself, at
    the generic readers and at a segment's.
  `kept_open`: `KeptAtS` opened: the link in front, the link behind, the hearing.
  **`formsInT_own`** : `FormsInTOwn`: the returns: the totality law (Total/RunsReturnLaw.lean) · the
    readers' answers, the late slots, a slot's test, the merge's slot, the segment's part:
    InT/ReaderAtK4.lean · row 0 and the index: Reads/RowZeroNamed.lean · filled behind the run:
    Slots/RunsThereNamed.lean, RunsThere.lean · not the merge's slot: Total/NotFree.lean.

Limits. ALL PREMISES OF THE STATEMENT STAND: the member (a run shows it, no theorem) · the lookup's
law's · three tests with code on the verifier's state, which have run nowhere as they stand ·
`StatesAt`, the seat's tie, typed by nobody. AT THE VERIFIER's STATE RIGHT BEHIND THE YES. K04_law,
the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.

-/
import Johnson.Road.K4.InT.Statement
import Johnson.Road.K4.InT.ReaderAtK4
import Johnson.Road.K4.Total.NotFree
import Johnson.Road.K4.Reads.RowZeroNamed
import Johnson.Road.K4.Slots.RunsThereNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.InT

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub Own)
open OnBytes.PscRun (Filled Later)
open OnBytes.Desc.First.K4 (Par blockAtC frontOf formsBack formsFrontWith hearFl)
open OnBytes.Desc.First.K4.Slots (SlotsIn LookFilled front_there_named back_there)
open OnBytes.Desc.First.K4.Reads (front_row0_named back_row0_named)
open OnBytes.Desc.First.K4.Total (KeptAsks runs_return_behind frontOf_eq run_pub front_not_sFv
  back_not_sFv)
open OnBytes.Desc.First.K4.InT (find_of_lookup reader_front reader_back lateOk_late slotIn_of
mergeOf_lay
segAt_lay)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc (K9.Part K9.RunOf K9.Readers K9.formsInT K9.segAt? K9.maskSeat
  K9.atMoment1 K9.entInT K9.ownRow K9.affInT K9.lateOf K9.readerOf K9.mergeOf K9.Read
  K9.statesOfLink
  K9.readersOfLink)

/-- A filled slot lies below the number of slots. -/
theorem filled_lt {F : Fork} (hF : PscRun.Sized F) {j : ℕ} (h : Filled F j) : j < F.ns := by
  rw [← hF.2.2]
  by_contra hc
  have e : F.gotF.getD j false = false := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    rfl
  have h' : F.gotF.getD j false = true := h
  rw [e] at h'
  cases h'

/-- An entry of the reads' array passes the test in front of the second sending. -/
theorem entInT_of_reads (own : List (ℕ × ℕ)) {A : K9.Part} {iU3 n : ℕ}
    (h : readsThereB A iU3 n = true) {x : Ent} (h1 : x.tree = iU3) (h2 : x.row = 0)
    (h3 : x.idx < n) : K9.entInT own A x = true := by
  unfold readsThereB at h
  unfold K9.entInT
  rw [h1]
  cases hb : A.L.arrayOf[iU3]? with
  | none => simp [hb] at h
  | some b =>
    simp only [hb] at h ⊢
    cases hr : reqArray A.L.check.rows.layout b.1 b.2 with
    | none => simp [hr] at h
    | some Ar =>
      simp only [hr, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      rw [Bool.or_eq_true]
      refine Or.inr ?_
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h.1, by omega, by omega⟩

/-- Such an entry names row 0 of an array with one own row. -/
theorem ownRow_of_one {F : Fork} {iU3 : ℕ} (h : oneRowB F iU3 = true) {x : Ent}
    (h1 : x.tree = iU3) (h2 : x.row = 0) : K9.ownRow F x = true := by
  unfold oneRowB at h
  unfold K9.ownRow
  rw [h1]
  cases ht : F.trees[iU3]? with
  | none => simp [ht] at h
  | some T =>
    simp only [ht, Option.any_some] at h ⊢
    simp [h, h2]

/-- Where the seat's tie holds at s, the reader at the seat's states is the reader at K4's
sub-protocol's
own
list. -/
theorem reader_pointwise {states : ℕ → List (K9.RunOf S)} {b : ℕ} {p : Par} {name : String} {s : S}
    (h : StatesAt states b p name s) :
    K9.readerOf states b name s = K9.readerOf (fun _ => (blockAtC p).claims) b name s := by
  obtain ⟨r, runC, hfind, hC, hpt⟩ := h
  unfold K9.readerOf
  rw [hfind, find_of_lookup _ _ _ hC]
  simp only [Option.bind_some]
  rw [hpt]

/-- **The test's clauses out of their pieces**, for one run. -/
theorem inT_of {own : List (ℕ × ℕ)} {states : ℕ → List (K9.RunOf S)} {b : ℕ} {name : String}
    {s : S} {A : K9.Part} {ff : Array Aff} {G₁ : Fork} {iU3 n sFv : ℕ}
    (hseg : K9.segAt? s = some A)
    (hrd : K9.readerOf states b name s = some { forms := ff.toList, late := K9.lateOf A.F G₁ })
    (hmg : K9.mergeOf s = some sFv) (hS : PscRun.Sized A.F) (hS1 : PscRun.Sized G₁)
    (hns : G₁.ns = A.F.ns)
    (hm : (K9.maskSeat own A).isSome = true) (hreads : readsThereB A iU3 n = true)
    (hents : ∀ f ∈ ff.toList, ∀ y ∈ f.ents.toList, y.tree = iU3 ∧ y.row = 0 ∧ y.idx < n)
    (hfil : ∀ f ∈ ff.toList, SlotsIn (Filled G₁) f)
    (hne : ∀ f ∈ ff.toList, SlotsIn (fun j => j ≠ sFv) f) : InTAt states own b name s := by
  refine ⟨A, _, hseg, hrd, lateOk_late A G₁ hns, fun f hf => ?_⟩
  unfold K9.affInT
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun y hy => ?_, fun x hx => ?_⟩
  · obtain ⟨e1, e2, e3⟩ := hents f hf y hy
    exact entInT_of_reads own hreads e1 e2 e3
  · have f1 : Filled G₁ x.1 := hfil f hf x hx
    refine slotIn_of (by rw [← hns]; exact filled_lt hS1 f1) hm ?_ f1 hS hns
    rw [hmg]
    intro e
    exact hne f hf x hx (Option.some.inj e).symm

/-- The test at the generic readers. -/
theorem inT_ofStates : InTOfStates := by
  intro states own b name s h
  obtain ⟨A, R, hseg, hrd, h1, h2⟩ := h
  unfold K9.formsInT
  have hrd' : (K9.Readers.ofStates states).forms b name s = some R := hrd
  rw [hseg, hrd']
  simp only [Bool.and_eq_true, List.all_eq_true]
  exact ⟨h1, h2⟩

/-- The test at a segment's readers. -/
theorem inT_ofLink : InTOfLink := by
  intro H l own b name s hn h
  obtain ⟨A, R, hseg, hrd, h1, h2⟩ := h
  unfold K9.formsInT
  have hrd' : (K9.readersOfLink H l).forms b name s = some R := by
    show (if name == "K8.equations" then H.small s
      else match K9.readerOf (K9.statesOfLink l) b name s with
        | some R => some R
        | Option.none => H.silent b name s) = some R
    rw [hn, hrd]
    rfl
  rw [hseg, hrd']
  simp only [Bool.and_eq_true, List.all_eq_true]
  exact ⟨h1, h2⟩

/-- `KeptAtS` opened. -/
theorem kept_open {p : Par} {s s' : S} (K : KeptAtS p s s') :
    ∃ (a a' : LayOwn) (fo : Forest.Heard) (o : Own) (G : Fork) (t u : Tape),
      s.here = .lay a ∧ a.fo = some fo ∧ s'.here = .lay a' ∧ a'.F = G ∧ a'.own = some o ∧
      s'.own? = some o ∧ s'.fork? = some G ∧
      hearFl { p.P with tokv := s.tokv } p.hp p.g fo a.F t = some (o, G, u) := by
  obtain ⟨a, fo, o, G, ha, hfo, h3, _, h5, _, _, _, hR, _, _, t, u, hh⟩ := K
  obtain ⟨a', ha', _⟩ := hR.here a ha
  have eF : a'.F = G := by
    have : s'.fork? = some a'.F := by simp [S.fork?, ha']
    exact Option.some.inj (this.symm.trans h3)
  have eo : a'.own = some o := by
    have : s'.own? = a'.own := by simp [S.own?, ha']
    rw [← this]
    exact h5
  exact ⟨a, a', fo, o, G, t, u, ha, hfo, ha', eF, eo, h5, h3, hh⟩

/-- **THE SENTENCE, PROVED.** -/
theorem formsInT_own : FormsInTOwn := by
  intro own p s s' P₀ o₀ states K A I hstF hstB
  obtain ⟨a, a', fo, o, G, t, u, ha, hfo, ha', eF, eo, ho', hG', hh⟩ := kept_open K
  obtain ⟨l1, l2, l3⟩ := A.leaves a fo ha hfo
  have hF := A.sized a ha
  have hfree := A.free a ha
  obtain ⟨⟨ff, G₁, hf, _⟩, fb, G₂, hb⟩ := runs_return_behind (rows := !p.k3Runs) (Pr := p.P)
    (P₀ := P₀) (o₀ := o₀) hh rfl rfl
    ⟨hF, l1, l2, A.skel o ho', A.y₀, A.rd₀, A.member⟩ hfree l3
  -- the run at the hearing's own public parameters: the same run
  have hf0 : formsFrontWith (!p.k3Runs) { p.P with tokv := s.tokv } p.g o G = some (ff, G₁) := by
    rw [run_pub (!p.k3Runs) p.P { p.P with tokv := s.tokv } p.g o G rfl rfl]
    exact hf
  have efo : o.H.fo = fo := OnBytes.Desc.First.K4.Slots.own_fo hh
  have N : _root_.Fo.Tp.PadNames o.H.fo a.F := by rw [efo]; exact I.names a fo ha hfo
  have NL : LookFilled (!p.k3Runs) fo a.F := by
    have N' := I.names a fo ha hfo
    exact ⟨fun _ f hf' => (N'.rows f hf').filledA, N'.sBit.filledA, N'.start.filledA⟩
  have hL : Later a.F G := OnBytes.Desc.First.K4.hearFl_later hh
  have sG : PscRun.Sized G := hL.sized hF
  obtain ⟨A', hseg, eAF, _⟩ := segAt_lay ha'
  have eAG : A'.F = G := eAF.trans eF
  have hmg := mergeOf_lay ha' eo
  have hK := I.hK o ho'
  have hone := I.oneRow G o hG' ho'
  have hreads := I.reads A' o hseg ho'
  have hm := I.mask A' hseg
  have r1 := front_row0_named hh hK N hf0
  have r2 := back_row0_named hh hK N hb
  have L1 : Later G G₁ := OnBytes.Desc.First.K4.formsFrontWith_later hf
  have L2 : Later G G₂ := OnBytes.Desc.First.K4.formsBack_later hb
  refine ⟨?_, ?_⟩
  · refine inT_of (G₁ := G₁) (ff := ff) hseg ?_ hmg (by rw [eAG]; exact sG) (L1.sized sG)
      (by rw [eAG]; exact L1.ns) hm hreads r1
      (front_there_named hF hh (fun _ h => h) sG N hf0) (front_not_sFv hF hfree NL l2 hh hf0)
    rw [eAG, ← eF, reader_pointwise hstF]
    refine reader_front rfl ha' eo (by rw [frontOf_eq, eF]; exact hf) fun f hf' => ?_
    rw [Array.all_eq_true_iff_forall_mem]
    intro y hy
    obtain ⟨e1, e2, _⟩ := r1 f hf' y (Array.mem_toList_iff.mpr hy)
    exact ownRow_of_one (by rw [eF]; exact hone) e1 e2
  · refine inT_of (G₁ := G₂) (ff := fb) hseg ?_ hmg (by rw [eAG]; exact sG) (L2.sized sG)
      (by rw [eAG]; exact L2.ns) hm hreads r2
      (back_there hF hh (fun _ h => h) sG hb) (back_not_sFv hF hfree hh hb)
    rw [eAG, ← eF, reader_pointwise hstB]
    refine reader_back rfl ha' eo (by rw [eF]; exact hb) fun f hf' => ?_
    rw [Array.all_eq_true_iff_forall_mem]
    intro y hy
    obtain ⟨e1, e2, _⟩ := r2 f hf' y (Array.mem_toList_iff.mpr hy)
    exact ownRow_of_one (by rw [eF]; exact hone) e1 e2

end OnBytes.Road.K4.InT

#print axioms OnBytes.Road.K4.InT.inT_of
#print axioms OnBytes.Road.K4.InT.inT_ofStates
#print axioms OnBytes.Road.K4.InT.inT_ofLink
#print axioms OnBytes.Road.K4.InT.formsInT_own
