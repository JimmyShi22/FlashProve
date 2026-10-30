-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/FormsKept.lean: THE JOIN forms_line (Johnson/Road/K4/FormsLine.lean) WITH ITS
PREMISES TAKEN OUT OF WHAT K4's SUB-PROTOCOL LEAVES WHERE IT ACCEPTS: from two structures under
which the table of joints' public test on K4's two runs is proved (KeptAtS,
Johnson/Road/K4/KeptAtS.lean; KeptAsks, Johnson/Road/K4/Total/AtKept.lean), what the lookup has
heard, and ONE TEST WITH CODE on the verifier's state (readsArrayB,
Johnson/Road/K4/ReadsArrayAt.lean), to the sentence FormsT of the statement of K4's law
(Johnson/Desc/Plain/K04Plain.lean), at the verifier's state that it leaves there.

  `same_trees`, `front_trees`, `back_trees`: K4's two runs leave the ledger's arrays as they are.
  `there_of`: thereAt out of its two halves: each named slot is filled; each entry is there.
  `forms_kept`: THE JOIN.
No new argument: the payers are called as in formsInT_own (Johnson/Road/K4/InT/FormsInTOwn.lean):
runs_return_behind, front_row0_named, back_row0_named, front_there_named, back_there; and
readsArray_gives.
Limits. THE CONCLUSION IS AT semQ, WHICH HANGS ON THE VERIFIER's STATE: no filling of the law's
letter Sem: formsT_sem carries it on (Johnson/Road/K4/FormsOfItem.lean). PREMISES of forms_kept:
  K, A: the two structures. A holds THE MEMBER of the law that both listings return and three lines
    of the lookup's law. Not paid here.
  hN: PadNames of what the lookup has heard, in front of K4's sub-protocol: the lookup's promise.
  hB: the one test on the state that K4's sub-protocol leaves where it accepts: it gives the reads'
    array's name, that it is of the second sending, the line on the public parameters (their length
    of the reads is at most the array's number of columns), one own row, and THE ENTRIES' HALF OF
    thereAt (readsArray_gives). No item of the table holds the test yet.
  hs1, hs2: the seat's tie, pointwise (StatesAt): statesAt_guarded (InT/SeatTie.lean) has it at a
    guarded seat.
  hk: the place's parameters let the lookup state its own claims.
  X: StatedAt at the reads' array's name, below the public parameters' length of the reads.
  Item: the table's sentence formsTQ at both runs.
M and tl are letters. NOT HERE: that the forms are worth 0 anywhere. Met through Lean at no member.
K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.FormsLine
import Johnson.Road.K4.ReadsArrayAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub Own)
open OnBytes.PscRun (Filled Later Same hideRun_ok)
open OnBytes.Desc.First.K4 (Par seatS formsBack formsFrontWith hearFl formsBack_some
  formsFrontWith_some)
open OnBytes.Desc.First.K4.Slots (SlotsIn front_there_named back_there)
open OnBytes.Desc.First.K4.Reads (front_row0_named back_row0_named)
open OnBytes.Desc.First.K4.Total (KeptAsks runs_return_behind run_pub)
open OnBytes.Desc.First.K4.InT (segAt_lay)
open OnBytes.Road.K4.InT (StatesAt kept_open)
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.K9 (segAt? LinkHoles statesOfLink readersOfLink)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated second dataQ formsTQ)
open VerifiableInference.Desc.Plain.K04 (thereAt FormsT frontRun)

/-- Two ledgers that differ at most in what lies under the slots have the same arrays. -/
theorem same_trees {F G : Fork} (h : Same F G) : G.trees = F.trees := by
  rw [h]

/-- The run "front" leaves the ledger's arrays, where the ledger's arrays have the right sizes (hF).
-/
theorem front_trees {rows : Bool} {P : Pub} {g : ℕ} {o : Own} {F G : Fork} {fs : Array Aff}
    (hF : PscRun.Sized F) (h : formsFrontWith rows P g o F = some (fs, G)) : G.trees = F.trees := by
  obtain ⟨_, _, _, F1, F2, _, _, _, _, r1, r2, rfl⟩ := formsFrontWith_some h
  obtain ⟨s1, z1, _, _⟩ := hideRun_ok F F1 _ _ _ hF r1
  obtain ⟨s2, _, _, _⟩ := hideRun_ok F1 F2 _ _ _ z1 r2
  have e : F2.trees = F.trees := (same_trees s2).trans (same_trees s1)
  cases rows
  · exact e
  · exact e

/-- The run "back" leaves the ledger's arrays, where the ledger's arrays have the right sizes (hF).
-/
theorem back_trees {o : Own} {F G : Fork} {fs : Array Aff} (hF : PscRun.Sized F)
    (h : formsBack o F = some (fs, G)) : G.trees = F.trees := by
  obtain ⟨F1, _, r1, rfl⟩ := formsBack_some h
  show F1.trees = F.trees
  exact same_trees (hideRun_ok F F1 _ _ _ hF r1).1

/-- thereAt out of its two halves. -/
theorem there_of {G : Fork} {f : Aff} (h1 : SlotsIn (Filled G) f)
    (h2 : ∀ y ∈ f.ents.toList, Fork.hasEnt G.trees y = true) : thereAt G f = true := by
  unfold thereAt
  refine Eq.mpr (Bool.and_eq_true _ _) ⟨?_, ?_⟩
  · exact Array.all_eq_true_iff_forall_mem.mpr fun x hx => h1 x (Array.mem_toList_iff.mpr hx)
  · exact Array.all_eq_true_iff_forall_mem.mpr fun y hy => h2 y (Array.mem_toList_iff.mpr hy)

/-- **THE JOIN, OUT OF WHAT K4's SUB-PROTOCOL LEAVES WHERE IT ACCEPTS**, under K A hN hB · hs1 hs2
hk · X · Item. -/
theorem forms_kept {Wt : Type} {St : Stated} (M : S → Bound GQ → Mats GQ) (H : LinkHoles)
    (l : Link S Claim) (own : List (ℕ × ℕ)) (rd : Wt → ℕ × ℕ → MsgQ) (w : Wt) {p : Par} {s s' : S}
    {P₀ : Pub} {o₀ : Own} {tl : HTailF2} (K : KeptAtS p s s') (A : KeptAsks p s s' P₀ o₀)
    (hN : ∀ a fo, s.here = .lay a → a.fo = some fo → _root_.Fo.Tp.PadNames fo a.F)
    (hB : readsArrayB p.hp s' = true) (hs1 : StatesAt (statesOfLink l) 2 p "front" s')
    (hs2 : StatesAt (statesOfLink l) 2 p "back" s') (hk : p.k3Runs = true)
    (X : ∀ A' o c, segAt? s' = some A' → s'.own? = some o → A'.L.arrayOf[o.v.iU3]? = some c →
      second s' c = true → StatedAt St M s' tl o c (p.hp.nU.getD 2 0) (dataQ own A' (rd w)))
    (Item : ∀ q ∈ [(2, "front"), (2, "back")],
      formsTQ (readersOfLink H l) St own q.1 q.2 s' (rd w)) :
    ∃ A', segAt? s' = some A' ∧
      FormsT seatS (semQ tl M s' fun w => dataQ own A' (rd w)) (frontRun p) formsBack s' w := by
  obtain ⟨a, a', fo, o, G, t, u, ha, hfo, ha', eF, eo, ho', hG', hh⟩ := kept_open K
  obtain ⟨l1, l2, l3⟩ := A.leaves a fo ha hfo
  have hF := A.sized a ha
  have hfree := A.free a ha
  obtain ⟨⟨ff, G₁, hf, fb', G₂', hb₁⟩, fb, G₂, hb⟩ := runs_return_behind (rows := !p.k3Runs)
    (Pr := p.P) (P₀ := P₀) (o₀ := o₀) hh rfl rfl
    ⟨hF, l1, l2, A.skel o ho', A.y₀, A.rd₀, A.member⟩ hfree l3
  have hf0 : formsFrontWith (!p.k3Runs) { p.P with tokv := s.tokv } p.g o G = some (ff, G₁) := by
    rw [run_pub (!p.k3Runs) p.P { p.P with tokv := s.tokv } p.g o G rfl rfl]
    exact hf
  have efo : o.H.fo = fo := OnBytes.Desc.First.K4.Slots.own_fo hh
  have N : _root_.Fo.Tp.PadNames o.H.fo a.F := by
    rw [efo]
    exact hN a fo ha hfo
  have hL : Later a.F G := OnBytes.Desc.First.K4.hearFl_later hh
  have sG : PscRun.Sized G := hL.sized hF
  have L1 : Later G G₁ := OnBytes.Desc.First.K4.formsFrontWith_later hf
  have S1 : PscRun.Sized G₁ := L1.sized sG
  obtain ⟨A', hseg, _, eAL⟩ := segAt_lay ha'
  have R : ReadsArrayIs p.hp s' a' o := readsArray_gives hh ha' hB
  have hK := R.cols
  obtain ⟨c, hc', h2⟩ := R.name
  have r1 := front_row0_named hh hK N hf0
  have r2 := back_row0_named hh hK N hb
  have e2 : fb' = fb := (back_two sG S1 L1 hb hb₁).1
  rw [e2] at hb₁
  have t1 : G₁.trees = G.trees := front_trees sG hf
  have tb : G₂.trees = G.trees := back_trees sG hb
  have t2 : G₂'.trees = G.trees := (back_trees S1 hb₁).trans t1
  have hfr : frontRun p o a'.F = some (ff, G₁) := by
    rw [eF]
    have : formsFrontWith (!p.k3Runs) p.P p.g o G = frontRun p o G := by
      rw [hk]
      rfl
    rw [← this]
    exact hf
  have hrow : ∀ (fs : Array Aff), (∀ f ∈ fs.toList, ∀ y ∈ f.ents.toList,
      y.tree = o.v.iU3 ∧ y.row = 0 ∧ y.idx < p.hp.nU.getD 2 0) →
      ∀ f ∈ fs.toList, f.ents.all (VerifiableInference.Desc.K9.ownRow a'.F) = true := by
    intro fs r f hf'
    rw [Array.all_eq_true_iff_forall_mem]
    intro y hy
    obtain ⟨e1, e3, _⟩ := r f hf' y (Array.mem_toList_iff.mpr hy)
    have := R.ownRow y.idx y.coef
    rw [← e1, ← e3] at this
    exact this
  have hent : ∀ (G' : Fork), G'.trees = G.trees → ∀ (fs : Array Aff),
      (∀ f ∈ fs.toList, ∀ y ∈ f.ents.toList,
        y.tree = o.v.iU3 ∧ y.row = 0 ∧ y.idx < p.hp.nU.getD 2 0) →
      ∀ f ∈ fs.toList, ∀ y ∈ f.ents.toList, Fork.hasEnt G'.trees y = true :=
    fun G' hG'' fs r f hf' y hy => by
      obtain ⟨e1, e3, e4⟩ := r f hf' y hy
      have := R.ents_same (F' := G') (by rw [hG'', eF]) y.idx y.coef e4
      rw [← e1, ← e3] at this
      exact this
  have hc : A'.L.arrayOf[o.v.iU3]? = some c := by
    rw [eAL]
    exact hc'
  refine forms_line M H l own rd w hs1 hs2 hk ha' eo hc'
    (fun A'' hA'' => X A'' o c hA'' ho' (by
      obtain rfl : A'' = A' := Option.some.inj (hA''.symm.trans hseg)
      exact hc) h2)
    (by rw [eF]; exact sG) hfr (by rw [eF]; exact hb) hb₁ (by rw [eF]; exact L1) S1
    (fun f hf' => there_of (front_there_named hF hh (fun _ h => h) sG N hf0 f hf')
      (hent G₁ t1 ff r1 f hf'))
    (fun f hf' => there_of (back_there hF hh (fun _ h => h) sG hb f hf') (hent G₂ tb fb r2 f hf'))
    (fun f hf' => there_of (back_there hF hh (fun j h => (L1.keep j h).1) S1 hb₁ f hf')
      (hent G₂' t2 fb r2 f hf'))
    r1 r2 (hrow ff r1) (hrow fb r2) Item

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.same_trees
#print axioms OnBytes.Road.K4.front_trees
#print axioms OnBytes.Road.K4.back_trees
#print axioms OnBytes.Road.K4.there_of
#print axioms OnBytes.Road.K4.forms_kept
