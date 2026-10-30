-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/TablesAtHead.lean: IN FRONT OF THE READS' PLACE OF THE OUTPUT HEAD's SEGMENT
(number 342 of the proof file's first chain) NO TABLES ARE LAID, AT EVERY REACHED STATE: FROM THE
GOALS' SCOPE ALONE. So the one premise that `tablesOk_at_rch`
(Johnson/Desc/AtSeats/TablesAtRchAll.lean) left falls. Statements with their proofs: a walk of
five steps, each a call. The segment's order: 337 "laid"; 338 K7 with "opened" joined behind; 339
K2; 340 K3; 341 K6; 342 K1 (the reads). `no_tables_338`: behind "laid" the state stands between
  two segments (`layFront_ok`): no head, so no tables. `no_tables_339` … `no_tables_342`: one step
  each: the sub-protocol at the number is the lot's own at its seat (`frames_sit`,
  `lot_K7`, `k2_head_of`, `k3_of`, `k6_of`), and each lot's own leaves what tables are laid
  (`k7Block_tk`, `opened_tk`, `k2Is_tk`, `theStated_tk`, `seatedClaims_tk`,
  Johnson/Desc/K1/Law/TablesWalkHead.lean). `tables_342`: so `TablesOk` there, along `RchAt`.
  `tablesOk_at_rch_all`: **all hundred borders: THE PREMISES: THE SCOPE ALONE** (hS, hR, O).
What is not claimed. That the scope can be met. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.AtSeats.TablesAtRchAll
import Johnson.Desc.K1.Law.TablesWalkHead
import Johnson.IMR.FrameYes
import Johnson.IMR.K3Seat
import Johnson.IMR.K6Seat
import Johnson.Top.H0.Walk.FrameLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Johnson.Desc.First.Walk.Tied (Reach RchAt rchAt_raw stepYes_decide)
open VerifiableInference.Desc (Block Chain FileDescription KindName)
open VerifiableInference.Desc.First (S Numbers Meaning flatPlacesOf kindsBeforeBatching)
open VerifiableInference.Desc.Sound (linksFull onQ Frame)
open IM (Open k1Ix subAt)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- Behind "laid": between two segments. -/
theorem no_tables_338 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (337 + 1) a) : NoTables a.2 := by
  obtain ⟨fs, _, hh⟩ := IM.frames_sit hS hR O
  obtain ⟨f, _, _, bL, _, _, _, _, hlay, iL, yL, _⟩ := hh 24 (by omega)
  cases h with
  | @succ _ z s s' b' _ hb' hy =>
    obtain rfl : bL = b' := Option.some.inj (iL.symm.trans hb')
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    have h1 := yL _ rs gs s' hd
    rw [hlay] at h1
    obtain ⟨rfl, hb, _, _⟩ := Johnson.Desc.First.Walk.Law.layFront_ok h1
    exact noTables_between _ hb

/-- Behind K7's place, with "opened" joined behind it. -/
theorem no_tables_339 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (338 + 1) a) : NoTables a.2 := by
  obtain ⟨fs, hfs, hh⟩ := IM.frames_sit hS hR O
  obtain ⟨f, _, k, _, b, b', _, hf, _, _, _, _, _, iB, hk, ⟨L, hL, hb'⟩, ep, hj, _, _, _⟩ :=
    hh 24 (by omega)
  have h0 : (kindsBeforeBatching (subAt 24) (24 == 0))[0]? = some KindName.K7 := rfl
  obtain rfl : KindName.K7 = k := Option.some.inj (h0.symm.trans hk)
  obtain ⟨sz, -⟩ := IM.ground_gets hS hR O.pub O.blank
  obtain ⟨x, hm, rfl⟩ := IM.lot_K7 hL hb' (by rw [ep])
  unfold ProofFile.h1Own at hm
  rw [sz] at hm
  obtain rfl := List.mem_singleton.1 hm
  cases h with
  | @succ _ z s s' b₁ h1 hb₁ hy =>
    obtain rfl : b = b₁ := Option.some.inj (iB.symm.trans hb₁)
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    obtain ⟨fs', f', m, hfs', hf', d1, _, d2, _, _⟩ := hj.yes hd
    exact (opened_tk hfs' f' (List.mem_of_getElem? hf') m s' d2).no
      (((k7Block_tk Bs.G₀.W 24).1 s _ _ m d1).no (no_tables_338 hS hR O (z, s) h1))

/-- Behind K2's place. -/
theorem no_tables_340 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (339 + 1) a) : NoTables a.2 := by
  obtain ⟨Lk, b, x, e1, e2, _, hla, his⟩ := IM.k2_head_of hS hR O
  have iB := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 1] at iB
  cases h with
  | @succ _ z s s' b₁ h1 hb₁ hy =>
    obtain rfl : b = b₁ := Option.some.inj (iB.symm.trans hb₁)
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    exact (k2Is_tk his rfl s rs gs s'
      ((IM.yes_alone hla (fun e => nomatch e) s s' rs gs).1 hd).1).no
      (no_tables_339 hS hR O (z, s) h1)

/-- Behind K3's place. -/
theorem no_tables_341 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (340 + 1) a) : NoTables a.2 := by
  obtain ⟨Lk, b, b', e1, e2, h3, hla⟩ := IM.k3_of hS hR O 24 (by omega) false
  have iB := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) (IM.k3Ix 24 false)] at iB
  cases h with
  | @succ _ z s s' b₁ h1 hb₁ hy =>
    obtain rfl : b = b₁ := Option.some.inj (iB.symm.trans hb₁)
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    exact noTables_of (theStated_tk _ _ _ _ _ _ h3).1
      ((IM.yes_alone hla (fun e => nomatch e) s s' rs gs).1 hd).1
      (no_tables_340 hS hR O (z, s) h1)

/-- **Behind K6's place: in front of the reads'.** -/
theorem no_tables_342 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (341 + 1) a) : NoTables a.2 := by
  obtain ⟨Lk, b, b', ms, e1, e2, _, h6, hla, _⟩ := IM.k6_of hS hR O
  have iB := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 3] at iB
  cases h with
  | @succ _ z s s' b₁ h1 hb₁ hy =>
    obtain rfl : b = b₁ := Option.some.inj (iB.symm.trans hb₁)
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    exact noTables_of (seatedClaims_tk h6).1
      ((IM.yes_alone hla (fun e => nomatch e) s s' rs gs).1 hd).1
      (no_tables_341 hS hR O (z, s) h1)

/-- So the invariant there, along "reached at the description's first chain". -/
theorem tables_342 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Str : Type}
    (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z)
      c) 342 a) : TablesOk Bs.G₀.W.hS Bs.G₀.W.HLy Bs.G₀.W.H a.1.2 :=
  tablesOk_of_no _ _ _ _ (no_tables_342 hS hR O a.1 (rchAt_raw h))

/-- **ALL HUNDRED BORDERS, FROM THE SCOPE ALONE.** -/
theorem tablesOk_at_rch_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {W : Type} {Fr : Frame}
    (N : Numbers) (Mg : Meaning ProofFile.InstPub W) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ j,
      (j = 14 * l + k1Ix l d + 2 ∨ j = 14 * l + k1Ix l d + 2 + 1) →
      ∀ a : (ProofFile.InstPub × S) × Fr.E.Str,
      RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
        j a →
      onQ N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) j a → a.1.2.failed = none →
      TablesOk Bs.G₀.W.hS Bs.G₀.W.HLy Bs.G₀.W.H a.1.2 :=
  tablesOk_at_rch hS hR O N Mg fun a h _ => tables_342 hS hR O a h

end

end VerifiableInference.Desc.K1
