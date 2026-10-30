-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/EqK4.lean: FOR THE ITEM "totalB": AT THE FEED-FORWARD KIND's TWO RUNS, "front" AND
"back": THE TERMS' COEFFICIENTS ARE THE WORTHS OF THE ITEM's FORMS: `ItemEq` (Honest/K9/EqItem.lean). Statements and
proofs over the sealed library's laws; no goal is stated.
  **`eq_back`**, **`eq_front`**   `ItemEq` at an entry whose run stands under the kind's own block's run of that name,
      the table of terms there being `plainTm (valsBack …)`, `plainTm (valsFront …)` at `entUnit`
THE TWO PROOFS ARE THE LIBRARY's OWN PROOFS OF `item_back`, `item_front` (Johnson/Desc/First/Link/Law/HitemsK4.lean),
CUT BY PROGRAM OFF THAT FILE: these lay the entry's own run, though their statement (`ItemAt`) does not say so.
Struck: the premises on the order's membership, the numbers' table and the frame's strings; the state is a letter of
its own; the witness's letter (rdW w is a letter rd); the end is stated with the entry's own terms named. No member.
Called by Honest/K9/EqAt.lean.
WHAT IS NOT CLAIMED. Any premise at any state or link. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.EqItem
import Johnson.Desc.First.Link.Law.HitemsK4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference
open OnBytes.Model.Layer (Own)
open OnBytes.PscRun (Later Filled Sized hideRun_ok hideRun_keeps paid_later)
open OnBytes.Desc.First.K4 (Par blockAtC claimOf Wrote frontAtC backAtC formsBack_some
  formsFrontWith_some)
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.K4Values (InWin LaidAt winOf backForms frontForms frontWins
  front_forms laid_of_run)
open VerifiableInference.Desc.K4Run (valsBack valsFront frontOf_eq)
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc

variable {α : Type}

/-- **The equation at the run "back".** -/
theorem eq_back (H : Desc.K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (Ok : α × Option Pub9 → Prop)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (o : ℕ × String)
    (hne : (o.2 == "K8.equations") = false)
    (run r : ℕ → S → Except String (List Claim × S)) (hAt : At L o run) (p : Par)
    (hr : (blockAtC p).claims.lookup "back" = some r) (hu : Under run r) (π : α → Option Own)
    (hπ : ∀ s a, s.here = .lay a → π (φ s) = a.own)
    (hOk : ∀ q o u, Ok q → π q.1 = some o → q.2 = some u → Sized u.F ∧
      ∀ f ∈ backForms o, ∀ x ∈ f.slots.toList,
        InWin (winOf o.wo.toWsMerged.p) x.1 ∨ Filled u.F x.1)
    (ht : tmOf o = plainTm (valsBack Reading.gl π entUnit))
    (s : S) (b : Desc.K9.Part) (hb : atS.get? s = some b)
    (hf : Fx9 φ Ok (fixed9 φ s) s) (hsil : H.silent o.1 o.2 s = none)
    (hin : Desc.K9.formsIn (Desc.K9.readersOfLink H L) own o.1 o.2 s = true) :
    ItemEq φ tmOf (Desc.K9.readersOfLink H L) own rd o s b := by
  obtain ⟨R, hR⟩ := reader_of_formsIn _ own o.1 o.2 s hin
  obtain ⟨⟨c, s'⟩, G0, G', hz, h0, hG', _, rfl⟩ := run_of_reader H L o hne run hAt s hsil R hR
  obtain rfl : G0 = b.F := Option.some.inj (h0.symm.trans (Desc.K9.get_fork s b hb))
  obtain ⟨al, ow, fs, G, hown, hfb, rfl, hw⟩ := backAtC hr (hu 0 s c s' hz)
  obtain ⟨e1, e2⟩ := fork_wrote hw
  obtain rfl : G' = G := Option.some.inj (hG'.symm.trans e2)
  have f4 : b.F = al.F := Option.some.inj (h0.symm.trans e1)
  have hq : (fixed9 φ s).2 = some (pubOf b) := by
    show (atS.get? s).map pubOf = _
    rw [hb]
    rfl
  have hq1 : π (fixed9 φ s).1 = some ow := by
    show π (φ s) = _
    rw [hπ s al hw.1, hown]
  obtain ⟨hsz, hsl⟩ := hOk _ ow (pubOf b) hf.1 hq1 hq
  rw [← f4] at hfb
  obtain ⟨F1, rfl, h1, rfl⟩ := formsBack_some hfb
  obtain ⟨hlaid, hwin⟩ := window_later (Later.refl b.F) (show Sized b.F from hsz) h1
    (paid_later F1 _)
  refine ⟨_, hR, fun n => ?_⟩
  have he := named_of_formsIn (Desc.K9.readersOfLink H L) own o.1 o.2 s b _ hb hR hin
  rw [ht]
  show (Desc.K9L.numbered n (valsBack Reading.gl π entUnit (fixed9 φ s) (dataQ own b rd))).map (·.2) = _
  rw [numbered_snd]
  simp only [valsBack, hq1, hq]
  have efs : ((backForms ow).toArray.toList.map claimOf).map (·.form) = backForms ow := by
    rw [List.toList_toArray, List.map_map]
    exact List.map_id' _
  show _ = List.map _ (((backForms ow).toArray.toList.map claimOf).map (·.form))
  rw [efs]
  refine List.map_congr_left fun f hf' => ?_
  refine value_meets_windows b _ [winOf ow.wo.toWsMerged.p] (dataQ own b rd)
    (fixed9 φ s) hq f (he f (by
      show f ∈ ((backForms ow).toArray.toList.map claimOf).map (·.form)
      rw [efs]
      exact hf')) fun x hx => ?_
  by_cases hw' : InWin (winOf ow.wo.toWsMerged.p) x.1
  · obtain ⟨k1, k2, k3⟩ := hwin x.1 hw'
    exact Or.inl ⟨_, List.mem_singleton.2 rfl, hw', hlaid, k1, k2, k3⟩
  · refine Or.inr ⟨?_, (hsl f hf' x hx).resolve_left hw'⟩
    rintro ⟨w', hw'', hj⟩
    obtain rfl := List.mem_singleton.1 hw''
    exact hw' hj

/-- **The equation at the run "front".** -/
theorem eq_front (H : Desc.K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (Ok : α × Option Pub9 → Prop)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (o : ℕ × String)
    (hne : (o.2 == "K8.equations") = false)
    (run r : ℕ → S → Except String (List Claim × S)) (hAt : At L o run) (p : Par)
    (hr : (blockAtC p).claims.lookup "front" = some r) (hu : Under run r) (π : α → Option Own)
    (hπ : ∀ s a, s.here = .lay a → π (φ s) = a.own)
    (hOk : ∀ q o u, Ok q → π q.1 = some o → q.2 = some u → Sized u.F ∧
      (∀ i, i < 4 * p.P.y.NI → Filled u.F (o.H.tV.sEnd + i)) ∧
      ∀ l, frontForms (!p.k3Runs) p.P p.g o u.F = some l → ∀ f ∈ l, ∀ x ∈ f.slots.toList,
        (∃ w ∈ frontWins o, InWin w x.1) ∨ Filled u.F x.1)
    (ht : tmOf o = plainTm (valsFront Reading.gl p π entUnit))
    (s : S) (b : Desc.K9.Part) (hb : atS.get? s = some b)
    (hf : Fx9 φ Ok (fixed9 φ s) s) (hsil : H.silent o.1 o.2 s = none)
    (hin : Desc.K9.formsIn (Desc.K9.readersOfLink H L) own o.1 o.2 s = true) :
    ItemEq φ tmOf (Desc.K9.readersOfLink H L) own rd o s b := by
  obtain ⟨R, hR⟩ := reader_of_formsIn _ own o.1 o.2 s hin
  obtain ⟨⟨c, s'⟩, G0, G', hz, h0, hG', _, rfl⟩ := run_of_reader H L o hne run hAt s hsil R hR
  obtain rfl : G0 = b.F := Option.some.inj (h0.symm.trans (Desc.K9.get_fork s b hb))
  obtain ⟨al, ow, fs, G, hown, hff, rfl, hw⟩ := frontAtC hr (hu 0 s c s' hz)
  obtain ⟨e1, e2⟩ := fork_wrote hw
  obtain rfl : G' = G := Option.some.inj (hG'.symm.trans e2)
  have f4 : b.F = al.F := Option.some.inj (h0.symm.trans e1)
  have hq : (fixed9 φ s).2 = some (pubOf b) := by
    show (atS.get? s).map pubOf = _
    rw [hb]
    rfl
  have hq1 : π (fixed9 φ s).1 = some ow := by
    show π (φ s) = _
    rw [hπ s al hw.1, hown]
  obtain ⟨hsz, hsh, hsl⟩ := hOk _ ow (pubOf b) hf.1 hq1 hq
  rw [← f4, frontOf_eq] at hff
  have hl : frontForms (!p.k3Runs) p.P p.g ow b.F = some fs.toList :=
    front_forms hff (Later.refl b.F) hsh
  obtain ⟨sh, pp, l, F1, F2, -, -, -, -, h1, h2, eG⟩ := formsFrontWith_some hff
  have hF1 : Sized F1 := (hideRun_ok b.F F1 _ _ _ hsz h1).2.1
  have hG2 : Later F2 G' := by
    rw [eG]
    cases (!p.k3Runs)
    · exact paid_later _ _
    · exact (paid_later _ _).trans (paid_later _ _)
  obtain ⟨hlaid1, hwin1⟩ := window_later (Later.refl b.F) (show Sized b.F from hsz) h1
    ((hideRun_keeps h2).trans hG2)
  obtain ⟨hlaid2, hwin2⟩ := window_later (hideRun_keeps h1) hF1 h2 hG2
  refine ⟨_, hR, fun n => ?_⟩
  have he := named_of_formsIn (Desc.K9.readersOfLink H L) own o.1 o.2 s b _ hb hR hin
  rw [ht]
  show (Desc.K9L.numbered n (valsFront Reading.gl p π entUnit (fixed9 φ s) (dataQ own b rd))).map (·.2) = _
  rw [numbered_snd]
  have hl' : frontForms (!p.k3Runs) p.P p.g ow (pubOf b).F = some fs.toList := hl
  simp only [valsFront, hq1, hq, hl']
  have efs : (fs.toList.map claimOf).map (·.form) = fs.toList := by
    rw [List.map_map]
    exact List.map_id' _
  show _ = List.map _ ((fs.toList.map claimOf).map (·.form))
  rw [efs]
  refine List.map_congr_left fun f hf' => ?_
  refine value_meets_windows b G' (frontWins ow) (dataQ own b rd) (fixed9 φ s) hq f
    (he f (by
      show f ∈ (fs.toList.map claimOf).map (·.form)
      rw [efs]
      exact hf')) fun x hx => ?_
  by_cases hw' : ∃ w ∈ frontWins ow, InWin w x.1
  · obtain ⟨w', hm, hj⟩ := hw'
    simp only [frontWins, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · obtain ⟨k1, k2, k3⟩ := hwin1 x.1 hj
      exact Or.inl ⟨_, List.mem_cons_self, hj, hlaid1, k1, k2, k3⟩
    · obtain ⟨k1, k2, k3⟩ := hwin2 x.1 hj
      exact Or.inl ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hj, hlaid2, k1, k2, k3⟩
  · exact Or.inr ⟨hw', (hsl _ hl f hf' x hx).resolve_left hw'⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.eq_back
#print axioms ProofFile.Honest.K9.eq_front
