-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/HitemsK4.lean: `TableOwes.hitems` (LinkTable.lean), ONE ITEM's CLAUSE AT
EACH OF THE LAYERS' OWN KIND's TWO RUNS, «front» and «back»: runs that lay windows of the ledger. At
the readers of the link itself (`K9.readersOfLink`). Theorems, over HitemsMerge.lean,
LateWindows.lean and K4Run.lean.

What is said.
  `window_later`: what a run of hiding slots leaves, read between an earlier ledger and a later one.
    `fork_wrote`: the ledgers in front of and behind a writing of the layers' kind. `item_back`,
    `item_front`: **`ItemAt` at an entry of the order whose run stands under the kind's block's run
    of that name**, the table of terms there being `plainTm (valsBack …)`, `plainTm (valsFront …)`
    at `entUnit`; from, at the statement: a part is there; the state goes on from what is fixed; the
    reader's second hole says nothing; the table's public test says yes; and the run's law's own
    premises on φ and on Ok.

Limits. Two items. As in HitemsStill.lean: the hole's silence is a premise; whether the public test
says yes at a real record is a run's to show. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.HitemsMerge
import Johnson.Desc.First.Link.Law.K4Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.PscRun (Later Filled Sized hideRun_ok hideRun_keeps paid_later)
open OnBytes.Desc.First.K4 (Par blockAtC claimOf Wrote frontAtC backAtC formsBack_some
  formsFrontWith_some)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.K4Values (InWin LaidAt winOf backForms frontForms frontWins
  front_forms laid_of_run)
open VerifiableInference.Desc.K4Run (valsBack valsFront frontOf_eq)
open VerifiableInference.Desc.EntryUnit (entUnit)

variable {α W : Type} {F : Frame}

/-- What a run of hiding slots leaves, read between an earlier ledger and a later one. -/
theorem window_later {U0 U G B : Fork} {first n : ℕ} (h0 : Later U0 U) (hU : Sized U)
    (h : U.hideRun first (Array.replicate n zeroE) (subE zeroE oneE) = some G) (hB : Later G B) :
    LaidAt B (first, n) ∧ ∀ j, InWin (first, n) j →
      j < B.ns ∧ U0.gotF.getD j false = false ∧ B.gotF.getD j false = true := by
  obtain ⟨_, hw⟩ := window_of_run hU h
  refine ⟨laid_of_run hU h hB, fun j hj => ?_⟩
  obtain ⟨k1, k2, k3⟩ := hw j hj
  refine ⟨by rw [hB.ns]; exact k1, ?_, (hB.keep j k3).1⟩
  cases e : U0.gotF.getD j false with
  | false => rfl
  | true =>
    have := (h0.keep j e).1
    rw [show Filled U j = (U.gotF.getD j false = true) from rfl, k2] at this
    exact nomatch this

/-- The ledgers in front of and behind a writing of the layers' kind. -/
theorem fork_wrote {s s' : S} {a : LayOwn} {G : Fork} (h : Wrote s a G s') :
    s.fork? = some a.F ∧ s'.fork? = some G := by
  refine ⟨?_, by rw [h.2]; rfl⟩
  unfold S.fork?
  rw [h.1]

/-- **ONE ITEM's CLAUSE AT THE RUN «back».** -/
theorem item_back (H : K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (Ok : α × Option Pub9 → Prop)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ)
    (o : ℕ × String) (ho : o ∈ L.order) (hne : (o.2 == "K8.equations") = false)
    (run r : ℕ → S → Except String (List Claim × S)) (hAt : At L o run) (p : Par)
    (hr : (blockAtC p).claims.lookup "back" = some r) (hu : Under run r) (π : α → Option Own)
    (hπ : ∀ s a, s.here = .lay a → π (φ s) = a.own)
    (hOk : ∀ q o u, Ok q → π q.1 = some o → q.2 = some u → Sized u.F ∧
      ∀ f ∈ backForms o, ∀ x ∈ f.slots.toList,
        InWin (winOf o.wo.toWsMerged.p) x.1 ∨ Filled u.F x.1)
    (ht : tmOf o = plainTm (valsBack Reading.gl π entUnit))
    (a : S × F.E.Str) (w : W) (b : K9.Part) (hb : atS.get? a.1 = some b)
    (hf : Fx9 φ Ok (fixed9 φ a.1) a.1) (hsil : H.silent o.1 o.2 a.1 = none)
    (hin : K9.formsIn (K9.readersOfLink H L) own o.1 o.2 a.1 = true) :
    ItemAt L φ tmOf lenOf (K9.readersOfLink H L) own rdW a w o := by
  obtain ⟨R, hR⟩ := reader_of_formsIn _ own o.1 o.2 a.1 hin
  obtain ⟨⟨c, s'⟩, G0, G', hz, h0, hG', _, rfl⟩ := run_of_reader H L o hne run hAt a.1 hsil R hR
  obtain rfl : G0 = b.F := Option.some.inj (h0.symm.trans (K9.get_fork a.1 b hb))
  obtain ⟨al, ow, fs, G, hown, hfb, rfl, hw⟩ := backAtC hr (hu 0 a.1 c s' hz)
  obtain ⟨e1, e2⟩ := fork_wrote hw
  obtain rfl : G' = G := Option.some.inj (hG'.symm.trans e2)
  have f4 : b.F = al.F := Option.some.inj (h0.symm.trans e1)
  have hq : (fixed9 φ a.1).2 = some (pubOf b) := by
    show (atS.get? a.1).map pubOf = _
    rw [hb]
    rfl
  have hq1 : π (fixed9 φ a.1).1 = some ow := by
    show π (φ a.1) = _
    rw [hπ a.1 al hw.1, hown]
  obtain ⟨hsz, hsl⟩ := hOk _ ow (pubOf b) hf.1 hq1 hq
  rw [← f4] at hfb
  obtain ⟨F1, rfl, h1, rfl⟩ := formsBack_some hfb
  obtain ⟨hlaid, hwin⟩ := window_later (Later.refl b.F) (show Sized b.F from hsz) h1
    (paid_later F1 _)
  refine ⟨b, _, [(⟨(o.2, run), tmOf o, lenOf o⟩, valsBack Reading.gl π entUnit)], hb, ?_, hR, hin,
    ?_⟩
  · intro x hx
    obtain rfl := List.mem_singleton.1 hx
    refine ⟨List.mem_filterMap.2 ⟨o, ho, ?_⟩, fun n y => ?_⟩
    · rw [show ((L.hear[o.1]?).bind fun b => b.claims.lookup o.2) = some run from hAt]
      rfl
    · show ((tmOf o n (fixed9 φ a.1) y).map (·.2)) = _
      rw [ht]
      exact numbered_snd _ n
  · have he := named_of_formsIn (K9.readersOfLink H L) own o.1 o.2 a.1 b _ hb hR hin
    show valsBack Reading.gl π entUnit (fixed9 φ a.1) (dataQ own b (rdW w)) ++ [] = _
    rw [List.append_nil]
    simp only [valsBack, hq1, hq]
    have efs : ((backForms ow).toArray.toList.map claimOf).map (·.form) = backForms ow := by
      rw [List.toList_toArray, List.map_map]
      exact List.map_id' _
    show _ = List.map _ (((backForms ow).toArray.toList.map claimOf).map (·.form))
    rw [efs]
    refine List.map_congr_left fun f hf' => ?_
    refine value_meets_windows b _ [winOf ow.wo.toWsMerged.p] (dataQ own b (rdW w))
      (fixed9 φ a.1) hq f (he f (by
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

/-- **ONE ITEM's CLAUSE AT THE RUN «front».** -/
theorem item_front (H : K9.LinkHoles) (L : Link S Claim) (φ : S → α)
    (Ok : α × Option Pub9 → Prop)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ)
    (o : ℕ × String) (ho : o ∈ L.order) (hne : (o.2 == "K8.equations") = false)
    (run r : ℕ → S → Except String (List Claim × S)) (hAt : At L o run) (p : Par)
    (hr : (blockAtC p).claims.lookup "front" = some r) (hu : Under run r) (π : α → Option Own)
    (hπ : ∀ s a, s.here = .lay a → π (φ s) = a.own)
    (hOk : ∀ q o u, Ok q → π q.1 = some o → q.2 = some u → Sized u.F ∧
      (∀ i, i < 4 * p.P.y.NI → Filled u.F (o.H.tV.sEnd + i)) ∧
      ∀ l, frontForms (!p.k3Runs) p.P p.g o u.F = some l → ∀ f ∈ l, ∀ x ∈ f.slots.toList,
        (∃ w ∈ frontWins o, InWin w x.1) ∨ Filled u.F x.1)
    (ht : tmOf o = plainTm (valsFront Reading.gl p π entUnit))
    (a : S × F.E.Str) (w : W) (b : K9.Part) (hb : atS.get? a.1 = some b)
    (hf : Fx9 φ Ok (fixed9 φ a.1) a.1) (hsil : H.silent o.1 o.2 a.1 = none)
    (hin : K9.formsIn (K9.readersOfLink H L) own o.1 o.2 a.1 = true) :
    ItemAt L φ tmOf lenOf (K9.readersOfLink H L) own rdW a w o := by
  obtain ⟨R, hR⟩ := reader_of_formsIn _ own o.1 o.2 a.1 hin
  obtain ⟨⟨c, s'⟩, G0, G', hz, h0, hG', _, rfl⟩ := run_of_reader H L o hne run hAt a.1 hsil R hR
  obtain rfl : G0 = b.F := Option.some.inj (h0.symm.trans (K9.get_fork a.1 b hb))
  obtain ⟨al, ow, fs, G, hown, hff, rfl, hw⟩ := frontAtC hr (hu 0 a.1 c s' hz)
  obtain ⟨e1, e2⟩ := fork_wrote hw
  obtain rfl : G' = G := Option.some.inj (hG'.symm.trans e2)
  have f4 : b.F = al.F := Option.some.inj (h0.symm.trans e1)
  have hq : (fixed9 φ a.1).2 = some (pubOf b) := by
    show (atS.get? a.1).map pubOf = _
    rw [hb]
    rfl
  have hq1 : π (fixed9 φ a.1).1 = some ow := by
    show π (φ a.1) = _
    rw [hπ a.1 al hw.1, hown]
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
  refine ⟨b, _, [(⟨(o.2, run), tmOf o, lenOf o⟩, valsFront Reading.gl p π entUnit)], hb, ?_, hR,
    hin, ?_⟩
  · intro x hx
    obtain rfl := List.mem_singleton.1 hx
    refine ⟨List.mem_filterMap.2 ⟨o, ho, ?_⟩, fun n y => ?_⟩
    · rw [show ((L.hear[o.1]?).bind fun b => b.claims.lookup o.2) = some run from hAt]
      rfl
    · show ((tmOf o n (fixed9 φ a.1) y).map (·.2)) = _
      rw [ht]
      exact numbered_snd _ n
  · have he := named_of_formsIn (K9.readersOfLink H L) own o.1 o.2 a.1 b _ hb hR hin
    show valsFront Reading.gl p π entUnit (fixed9 φ a.1) (dataQ own b (rdW w)) ++ [] = _
    rw [List.append_nil]
    have hl' : frontForms (!p.k3Runs) p.P p.g ow (pubOf b).F = some fs.toList := hl
    simp only [valsFront, hq1, hq, hl']
    have efs : (fs.toList.map claimOf).map (·.form) = fs.toList := by
      rw [List.map_map]
      exact List.map_id' _
    show _ = List.map _ ((fs.toList.map claimOf).map (·.form))
    rw [efs]
    refine List.map_congr_left fun f hf' => ?_
    refine value_meets_windows b G' (frontWins ow) (dataQ own b (rdW w)) (fixed9 φ a.1) hq f
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

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.window_later
#print axioms VerifiableInference.Desc.LinkJoin.fork_wrote
#print axioms VerifiableInference.Desc.LinkJoin.item_back
#print axioms VerifiableInference.Desc.LinkJoin.item_front
