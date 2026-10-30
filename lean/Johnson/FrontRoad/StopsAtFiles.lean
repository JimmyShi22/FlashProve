-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/StopsAtFiles.lean: the proofs of the seven statements of
Johnson/FrontRoad/StopsAtFilesSpec.lean: the statements of Johnson/FrontRoad/StopsReadCellsSpec.lean
joined at the letters of the implications on the field sessionStops.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  The step   frame_free: hn, which is typed on the rows G.first, says the same of provG's first
      halves: the halves keep the rows' places (first_provG, Johnson/FrontRoad/SessionHid.lean).
  The seven proofs   first_chain_agree_at, tests_strays, private_stops_read_cells,
      session_stops_read_cells, last_member_escapes_the_pin, stray_half_escapes,
      second_half_escapes.

How it fits. private_stops_read_cells: ready's return gives readyTests' (ready_ok,
Johnson/Desc/ProofFile/Honest/Law/Run.lean); that gives that no half is a stray (tests_strays) and
no two stand at one place (tests_twice, Johnson/Desc/ProofFile/Honest/Law/Rule/FileOkOf.lean);
tests_strays is that lemma's sister, on readyTests' first test where that one is on its second, and
its proof goes as that of tests_twice there, line by line; agree_all
(Johnson/FrontRoad/StopsReadCells.lean) then carries first_chain_agree_at and stops_read_cells to
every part of every half. All limits: the head of Johnson/FrontRoad/StopsAtFilesSpec.lean. Not one
of the release's goal statements.
-/
import Johnson.FrontRoad.StopsAtFilesSpec
import Johnson.FrontRoad.StopsReadCells
import Johnson.Desc.ProofFile.Honest.Law.Run

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open AtPublicFiles.AtFiles AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (RecFull)
open OnBytes.Params (Lines missedInTheChecks clog2)
open OnBytes.Maker (WholeD)
open OnBytes.Model.Verify (publicOf)
open OnBytes.HonestTrace (Tr cellsC cellsSmall_cellOf ServesAt theTrace meetsAll_theTrace
  servesAt_iff_in_scope TraceHinge)
open Inst.Model (Instance ppref)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First.K8 (Par)
open ProofFile.Honest (Prover ProverCoinCounts Sides Ready Coins ready Placed Local Cells Face chainStopAt)
open ProofFile.Honest.K9 (quietStop)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)
open P5J

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) nonemptyPadZ_stopsAtFiles : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_stopsAtFiles {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

/-- hn, of provG's first halves. -/
theorem frame_free (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl) {Tr' X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr' X₀ Xh)
    (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr' X₀ Xh)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame) :
    ∀ g ∈ (provG Z Zp Np cF B G H).first, g.place.kind ≠ KindName.frame := by
  intro g hg
  rw [first_provG] at hg
  obtain ⟨L', hL, rfl⟩ := List.mem_map.1 hg
  exact hn L' hL

theorem first_chain_agree_at : Spec.first_chain_agree_at := by
  intro Z Zp Np cF scope pp hr D r L W₀ Rc Xi Tr' X par cells hs u v h hn hS b hb g hg
  have hA := stops_read_cells par cells hs _ u v h hS
  have hl := (k8_places_front Z Zp Np cF scope hr L).2
  obtain ⟨bl, hbl, hk⟩ := Option.map_eq_some_iff.1 hl
  have hfl : (descZ Zp Np cF).first.blocksInOrder.dropLast ++ [bl] = (descZ Zp Np cF).first.blocksInOrder :=
    List.dropLast_append_getLast? bl hbl
  rw [← hfl] at hb
  rcases List.mem_append.1 hb with hb | hb
  · exact hA b hb g hg
  · obtain rfl := List.mem_singleton.1 hb
    have hp : g.place = b.place := by simpa using List.find?_some hg
    exact absurd (hp ▸ hk) (hn g (List.mem_of_find?_eq_some hg))

theorem tests_strays : Spec.tests_strays := by
  intro W₀ Rc Xi Ky Tr' X₀ X F B H w₀ h
  unfold ProofFile.Honest.readyTests at h
  split at h
  · cases h
  rename_i h1
  have e : ProofFile.Honest.strays F.first.blocksInOrder H.first ++ ProofFile.Honest.strays F.shared.blocksInOrder H.shared ++
      ProofFile.Honest.strays F.second.blocksInOrder H.second = [] := by
    simpa using h1
  obtain ⟨e12, e3⟩ := List.append_eq_nil_iff.1 e
  obtain ⟨e1, e2⟩ := List.append_eq_nil_iff.1 e12
  exact ⟨e1, e2, e3⟩

theorem private_stops_read_cells : Spec.private_stops_read_cells := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ Tr' X₀ Xh B G H scope pp hr D r L w₀ rc x₀ k₀ R hR hn par
    cells' h₁ h₃ u v hS
  have ht := (ProofFile.Honest.ready_ok hR).1
  obtain ⟨s1, -, s3⟩ := tests_strays _ B _ w₀ ht
  obtain ⟨t1, -, t3⟩ := ProofFile.Honest.tests_twice ht
  exact ⟨agree_all _ _ u v s1 t1
      (first_chain_agree_at Z Zp Np cF scope hr L par cells' _ u v ((pin_iff _ cells' _ _).1 h₁).2
        (frame_free Z Zp Np cF B G H hn) hS),
    agree_all _ _ u v s3 t3
      (stops_read_cells (fun _ => none) cells' _ _ u v ((pin_iff _ cells' _ _).1 h₃).2 hS)⟩

theorem session_stops_read_cells : Spec.session_stops_read_cells := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ Tr' X₀ Xh B G H scope pp hr D r L hn par cells' h₁ h₃
    u v hS
  exact ⟨chainStop_of_agree _ _ u v
      (first_chain_agree_at Z Zp Np cF scope hr L par cells' _ u v ((pin_iff _ cells' _ _).1 h₁).2
        (frame_free Z Zp Np cF B G H hn) hS),
    pinned_stops_read_cells (fun _ => none) cells' _ _ u v h₃ hS⟩

theorem last_member_escapes_the_pin : Spec.last_member_escapes_the_pin := by
  intro S Cl Rc Xi Tr' X par cells bl sh rc x tr hs
  refine ⟨fun b hb => ?_, ?_, ?_, rfl, (index_reader_fails par cells bl sh rc x tr).2.1⟩
  · cases hb
  · simp [hs, ProofFile.Honest.strays]
  · simp [hs, ProofFile.Honest.twice]

theorem stray_half_escapes : Spec.stray_half_escapes := by
  intro S Cl Rc Xi Tr' X par cells a sh rc x tr hs
  refine ⟨fun b hb => ?_, fun b hb => ?_, ?_, ?_, fun h => ?_⟩
  · cases hb
  · cases hb
  · simp [hs, ProofFile.Honest.strays]
  · simp [hs, ProofFile.Honest.twice]
  · have e : (some "" : Option String) = none :=
      h _ List.mem_cons_self _ List.mem_cons_self [] []
    cases e

theorem second_half_escapes : Spec.second_half_escapes := by
  intro S Cl Rc Xi Tr' X par cells b sh rc x tr hp hs
  have hfind : (hs.find? fun g => g.place == b.place) = some ⟨b.place, []⟩ :=
    List.find?_cons_of_pos (beq_self_eq_true _)
  refine ⟨fun b' hb' => ?_, fun b' hb' g hg p hpp => ?_, ?_, ?_, fun h => ?_⟩
  · obtain rfl := List.mem_singleton.1 hb'
    rw [hp]
    intro g hg p hpp
    rw [hfind] at hg
    obtain rfl := Option.some.inj hg
    cases hpp
  · obtain rfl := List.mem_singleton.1 hb'
    rw [hfind] at hg
    obtain rfl := Option.some.inj hg
    cases hpp
  · simp [hs, ProofFile.Honest.strays]
  · simp [hs, ProofFile.Honest.twice, List.eraseDups_cons]
  · have e : (some "" : Option String) = none :=
      h _ (List.mem_cons_of_mem _ List.mem_cons_self) _ List.mem_cons_self [] []
    cases e

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_stopsAtFiles
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_stopsAtFiles
#print axioms OnBytes.FrontRoad.frame_free
#print axioms OnBytes.FrontRoad.tests_strays
#print axioms OnBytes.FrontRoad.private_stops_read_cells
#print axioms OnBytes.FrontRoad.session_stops_read_cells
#print axioms OnBytes.FrontRoad.last_member_escapes_the_pin
#print axioms OnBytes.FrontRoad.first_chain_agree_at
#print axioms OnBytes.FrontRoad.stray_half_escapes
#print axioms OnBytes.FrontRoad.second_half_escapes
