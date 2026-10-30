-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ArmKept.lean: K4's FILES' HALF OF THE EXCHANGE AT A LAYERS' SEGMENT's SECOND
SENDING (armCell_lay, Johnson/Road/K4/ArmLay.lean) AT K4's OWN TWO RUNS, at the verifier's state
that K4's sub-protocol leaves where it accepts: the premise hE of armCell_lay (each entry that a
form of the reader's answer names has the reads' number, row 0, a place below the public parameters'
length of the reads, and an owner among the tables that K4 has heard) is no premise here.

  `ents_front`, `ents_back`: hE for one run's list of forms, out of the laws on row 0
    (Johnson/Road/K4/Reads/RowZeroNamed.lean) and on owned places (Johnson/Road/K4/OwnedForms.lean).
  `armCell_kept`: ArmCell at the readers of a link, at (2, "front") and at (2, "back"), at K4's arm
    uLay tl M.
No new argument: the opening is forms_kept's (Johnson/Road/K4/FormsKept.lean); the readers' answers
are had as in forms_line (Johnson/Road/K4/FormsLine.lean).
Limits. PREMISES of armCell_kept, none paid here:
  K, As, hN, hB, hs1, hs2, hk: as in forms_kept.
  hm, hg, htm, hNM: four lines on the public parameters, which the laws on owned places ask: the
    group's list of matrices has the layout's rows and columns; the group's number is below the
    number of groups; tl's list of matrices likewise; tl's number of matrices is its list's size.
  T: the approximate range proof's tie at the closed structure tl' and a table of cells A.
  hfun, htab, hu3: what the step that closes the list of tables leaves
    (Johnson/Road/K4/ClosedTurns.lean), with "the public parameters' number of the reads is K4's".
  hAc: below that length, A's row 0 of the reads is the data's cell behind the sending.
  hM: inside the ranges the matrices M at the data IN FRONT of the sending are cellA at A: where A
    reads the state BEHIND the sending this wants "the first sending's cells stay across the
    second sending": a lemma in other files: not called here.
Met through Lean at no member. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED: K4's row
spends formsT; this serves the row of the second sending. Nothing on soundness.


-/
import Johnson.Road.K4.ArmLay
import Johnson.Road.K4.FormsKept
import Johnson.Road.K4.OwnedForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub Own HPlan2)
open OnBytes.PscRun (Later)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open OnBytes.Desc.First.K4 (Par formsBack formsFrontWith hearFl frontOf)
open OnBytes.Desc.First.K4.Reads (front_row0_named back_row0_named inTab_bare)
open OnBytes.Desc.First.K4.Total (KeptAsks runs_return_behind run_pub frontOf_eq)
open OnBytes.Desc.First.K4.InT (segAt_lay reader_front reader_back)
open OnBytes.Road.K4.InT (StatesAt kept_open reader_pointwise)
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.K8 (TieOf)
open VerifiableInference.Desc.K9 (segAt? LinkHoles statesOfLink readersOfLink)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ dataQ ArmCell)
open Meaning.Reads (cellA)
open _root_.Fo.Tp (PadNames bare_ents)

variable {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F0 G0 F' F G : Fork} {t u : Tape}
  {o : Own} {fs : Array Aff}

/-- An owned place of row 0, in the words of armCell_lay. -/
theorem owner_row0 {tl : HTailF2} {y : Ent} (h0 : y.row = 0)
    (h : ownedAt tl o y.tree y.row y.idx) :
    ∃ z : HFun × ℕ × ℕ, z.1 ∈ o.funs ∧ tl.tabAt z.1 z.2.1 z.2.2 = some y.idx := by
  obtain ⟨_, z, hz, hp'⟩ := h
  rw [h0, Nat.zero_mul, Nat.zero_add] at hp'
  exact ⟨z, hz, hp'⟩

/-- hE for the list of the run "front", as the seat runs it. -/
theorem ents_front (hh : hearFl P hp g fo F0 t = some (o, G0, u)) (hK : hp.nU.getD 2 0 ≤ o.v.K3)
    (N : PadNames o.H.fo F') (h : formsFrontWith false P g o F = some (fs, G)) (tl : HTailF2)
    (hm : ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR P.y g) (hg : g < P.y.NGr)
    (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR P.y g) (hNM : tl.NM = tl.mats.size) :
    ∀ f ∈ fs.toList, ∀ x ∈ f.ents.toList, x.tree = o.v.iU3 ∧ x.row = 0 ∧ x.idx < hp.nU.getD 2 0 ∧
      ∃ z : HFun × ℕ × ℕ, z.1 ∈ o.funs ∧ tl.tabAt z.1 z.2.1 z.2.2 = some x.idx := by
  intro f hf x hx
  obtain ⟨e1, e2, e3⟩ := front_row0_named hh hK N h f hf x hx
  exact ⟨e1, e2, e3, owner_row0 e2
    (front_owned_seated hh h (inTab_bare o.v N.start.1) tl hm hg htm hNM f hf x hx)⟩

/-- hE for the list of the run "back". -/
theorem ents_back (hh : hearFl P hp g fo F0 t = some (o, G0, u)) (hK : hp.nU.getD 2 0 ≤ o.v.K3)
    (N : PadNames o.H.fo F') (he : fo.cEnd.ents = #[]) (h : formsBack o F = some (fs, G))
    (tl : HTailF2)
    (hm : ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR P.y g) (hg : g < P.y.NGr)
    (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR P.y g) (hNM : tl.NM = tl.mats.size) :
    ∀ f ∈ fs.toList, ∀ x ∈ f.ents.toList, x.tree = o.v.iU3 ∧ x.row = 0 ∧ x.idx < hp.nU.getD 2 0 ∧
      ∃ z : HFun × ℕ × ℕ, z.1 ∈ o.funs ∧ tl.tabAt z.1 z.2.1 z.2.2 = some x.idx := by
  intro f hf x hx
  obtain ⟨e1, e2, e3⟩ := back_row0_named hh hK N h f hf x hx
  exact ⟨e1, e2, e3, owner_row0 e2 (back_owned hh he h tl hm hg htm hNM f hf x hx)⟩

/-- **K4's FILES' HALF OF THE EXCHANGE AT K4's TWO RUNS**, under K As hN hB hs1 hs2 hk · hm hg htm
hNM · T hfun htab hu3 hAc hM. -/
theorem armCell_kept (H : LinkHoles) (l : Link S Claim) (own own' : List (ℕ × ℕ))
    (b : VerifiableInference.Desc.K9.Part) (rd : ℕ × ℕ → MsgQ) {p : Par} {s s' : S} {P₀ : Pub}
    {o₀ : Own} {tl tl' : HTailF2} {M : S → Bound GQ → Mats GQ} {A : ℕ → ℕ → ℕ → Cb.Gl.E}
    (K : KeptAtS p s s') (As : KeptAsks p s s' P₀ o₀)
    (hN : ∀ a fo, s.here = .lay a → a.fo = some fo → PadNames fo a.F)
    (hB : readsArrayB p.hp s' = true) (hs1 : StatesAt (statesOfLink l) 2 p "front" s')
    (hs2 : StatesAt (statesOfLink l) 2 p "back" s') (hk : p.k3Runs = true)
    (hm : ((p.P.tails.getD p.g {}).mats.map fun M => (M.m, M.k)) = matsR p.P.y p.g)
    (hg : p.g < p.P.y.NGr) (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR p.P.y p.g)
    (hNM : tl.NM = tl.mats.size) (T : TieOf tl' A)
    (hfun : ∀ o, s'.own? = some o → tl'.funs = o.funs)
    (htab : ∀ Fn c sg, tl.tabAt Fn c sg = tl'.tabAt Fn c sg)
    (hu3 : ∀ o, s'.own? = some o → u3Of tl' = o.v.iU3)
    (hAc : ∀ (o : Own) (a' : LayOwn) c, s'.own? = some o → s'.here = .lay a' →
      a'.L.arrayOf[o.v.iU3]? = some c → ∀ i, i < p.hp.nU.getD 2 0 →
      A o.v.iU3 0 i = (dataQ own' b rd).cell c.1 c.2 0 i)
    (hM : ∀ A', segAt? s' = some A' → InRange tl' (M s' (dataQ own A' rd)) (cellA tl' A)) :
    ∃ A', segAt? s' = some A' ∧
      ArmCell (readersOfLink H l) own own' 2 "front" s' A' b rd (uLay tl M) ∧
      ArmCell (readersOfLink H l) own own' 2 "back" s' A' b rd (uLay tl M) := by
  obtain ⟨a, a', fo, o, G, t, u, ha, hfo, ha', eF, eo, ho', hG', hh⟩ := kept_open K
  obtain ⟨l1, l2, l3⟩ := As.leaves a fo ha hfo
  have hF := As.sized a ha
  have hfree := As.free a ha
  obtain ⟨⟨ff, G₁, hf, _⟩, fb, G₂, hb⟩ := runs_return_behind (rows := !p.k3Runs)
    (Pr := p.P) (P₀ := P₀) (o₀ := o₀) hh rfl rfl
    ⟨hF, l1, l2, As.skel o ho', As.y₀, As.rd₀, As.member⟩ hfree l3
  have hf0 : formsFrontWith false { p.P with tokv := s.tokv } p.g o G = some (ff, G₁) := by
    have e := run_pub (!p.k3Runs) p.P { p.P with tokv := s.tokv } p.g o G rfl rfl
    rw [hk] at e hf
    exact e.trans hf
  have efo : o.H.fo = fo := OnBytes.Desc.First.K4.Slots.own_fo hh
  have N0 := hN a fo ha hfo
  have N : PadNames o.H.fo a.F := by
    rw [efo]
    exact N0
  have R : ReadsArrayIs p.hp s' a' o := readsArray_gives hh ha' hB
  obtain ⟨A', hseg, _, eAL⟩ := segAt_lay ha'
  have E1 := ents_front hh R.cols N hf0 tl hm hg htm hNM
  have E2 := ents_back hh R.cols N (bare_ents N0.cEnd.1) hb tl hm hg htm hNM
  have hrow : ∀ (fs : Array Aff), (∀ f ∈ fs.toList, ∀ x ∈ f.ents.toList,
      x.tree = o.v.iU3 ∧ x.row = 0 ∧ x.idx < p.hp.nU.getD 2 0 ∧
        ∃ z : HFun × ℕ × ℕ, z.1 ∈ o.funs ∧ tl.tabAt z.1 z.2.1 z.2.2 = some x.idx) →
      ∀ f ∈ fs.toList, f.ents.all (VerifiableInference.Desc.K9.ownRow a'.F) = true := by
    intro fs r f hf'
    rw [Array.all_eq_true_iff_forall_mem]
    intro y hy
    obtain ⟨e1, e3, _⟩ := r f hf' y (Array.mem_toList_iff.mpr hy)
    have := R.ownRow y.idx y.coef
    rw [← e1, ← e3] at this
    exact this
  have hf' : frontOf p o a'.F = some (ff, G₁) := by
    rw [eF, frontOf_eq]
    exact hf
  have r1 := readers_some H l (b := 2) (name := "front") (by decide)
    ((reader_pointwise hs1).trans (reader_front rfl ha' eo hf' (hrow ff E1)))
  have r2 := readers_some H l (b := 2) (name := "back") (by decide)
    ((reader_pointwise hs2).trans (reader_back rfl ha' eo (by rw [eF]; exact hb) (hrow fb E2)))
  refine ⟨A', hseg, ?_, ?_⟩
  · refine armCell_lay (readersOfLink H l) own own' 2 "front" A' b rd ha' eo eAL
      (fun R' hR' f hf'' x hx => ?_) T (hfun o ho') htab (hu3 o ho')
      (fun c hc => hAc o a' c ho' ha' hc) (hM A' hseg)
    obtain rfl : _ = R' := Option.some.inj (r1.symm.trans hR')
    exact E1 f hf'' x hx
  · refine armCell_lay (readersOfLink H l) own own' 2 "back" A' b rd ha' eo eAL
      (fun R' hR' f hf'' x hx => ?_) T (hfun o ho') htab (hu3 o ho')
      (fun c hc => hAc o a' c ho' ha' hc) (hM A' hseg)
    obtain rfl : _ = R' := Option.some.inj (r2.symm.trans hR')
    exact E2 f hf'' x hx

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.owner_row0
#print axioms OnBytes.Road.K4.ents_front
#print axioms OnBytes.Road.K4.ents_back
#print axioms OnBytes.Road.K4.armCell_kept
