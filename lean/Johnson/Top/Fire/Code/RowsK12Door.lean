-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/RowsK12Door.lean: THE KEY FILE: ROWS 2.9 · 2.10 · 3.2 (the three proximity
  tests behind the first chain): TWO THINGS THAT CARRY NO DEBT, BENEATH THE CALLS
  (RowsK12AtName.lean).
  some_rounds₂ | some_rounds₃   the maker's piece number n of the shared | last chain, where the
      n-th sub-protocol declares a round and is not the last: its stretch is dB :: dt and nothing is
      put behind.
  hrow_29 | hrow_210 | hrow_32   (i) IN SCOPE: the premise hrow (of pays_29_name |
      pays_210_name | pays_32_name) at the row's own look-up, at ANY sub-protocol b that the look-up
      names: no letter is left.
  r2_9_of_pays | r2_10_of_pays | r3_2_of_pays   (ii) THE DOOR's LAST MILE, GENERAL IN hpay: from a
      premise whose type is pays_29_name | pays_32_name's conclusion to the letter, to The21's field
      r2_9 | r3_2 at The21Off's written terms: keepsAt_U | keepsAt_own (K12AtField.lean), then the
      join of on9 | on32 ("the invariant; at the row's border the history") with On₂' |
      On₃' ("the invariant and the history at every border").
WHAT IT IS NOT. hpay is a premise: nothing is paid. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.Rows2AtNameB
import Johnson.Top.Fire.Code.KeyAtOff
import Johnson.RunOne.Law.K12AtField
import Johnson.RunOne.Law.StepSide2
import Johnson.RunOne.Law.K12Pays29Name
import Johnson.RunOne.Law.K12Pays32Name
import Johnson.RunOne.Law.K12Pays210Name

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace LPFD
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃
    seam₁_at_fk seam₂_at_fk ends_at_fk)
open Johnson.RunOne.KeyRows1 (FirstLetters firstOn_of firstClaim_of CollCell ReadsL open₁ plan₁)
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₂ open₃)
open Johnson.RunOne.KeyRows23 (p14At shared_flat names_blocks fileOk_all bareB)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope shared_lin_in_scope)
open VerifiableInference.Desc.Key.Fill (six OmAt symsW)
open Johnson.RunOne.KeyRows23 (numSix atSix kreadFam baseK)

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ :
        Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ :
        List (Block (Fk X N P).S₃ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m :
            Johnson.G.OfPlan.Made}

open Johnson.RunOne.Law.K12AtField (Pays keepsAt_U keepsAt_own)
open Johnson.RunOne.Law.K12Pays29Name (pi9 B9 on9)
open Johnson.RunOne.Law.K12Pays32Name (pi32 B32 on32)
open Johnson.RunOne.Law.K12Pays210Name (pi10 B10 on10)
open Johnson.RunOne.Law.K12AtField (keepsAt_O)

/-- **The maker's piece number n of the shared chain: its stretch has a first round and nothing is
  put behind**, where the n-th sub-protocol declares a round and is not the last. -/
theorem some_rounds₂ (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (q₂ : (Fk X N
    P).shared.blocksInOrder = c₂ :: k₂) (n : ℕ) (hn : n < k₂.length)
    (b : Block (Fk X N P).S₂ (Fk X N P).Cl) (base : ℕ) (ds : List RDT) (back : List _root_.Fmt.RoundView)
        (hb : (c₂ :: k₂)[n]? = some b) (hl : 0 < b.rounds.length)
    (hrow : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
        capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
        (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂)[n]? = some (pieceOf
        (held b) base ds back (capRest n ds))) :
    ∃ dB dt, ds = dB :: dt ∧ back = [] := by
  obtain ⟨b', -, e⟩ := rowAt₂ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest
      capRest capRest () () n _ hrow
  have e1 : ds = cutDs (DK.at frS.P.T.a).ds₂ (held c₂ : Block (((Fk X N P).XiPub × (Fk X N P).S₁) ×
      (Fk X N P).S₂) (Fk X N P).Cl) (k₂.map held) n := congrArg (·.ds) e
  have e2 : back = cutPut [] (k₂.map (held (P := ((Fk X N P).XiPub × (Fk X N P).S₁)))) n := congrArg
      (·.back) e
  have hlen : ds.length = b.rounds.length := by
    rw [e1, cutDs_held k₂ n _ c₂]
    exact stretch_len₂ (Fk X N P) "key file" (DK.at frS.P.T.a) hdata c₂ k₂ q₂ n b hb
  obtain ⟨dB, dt, hd⟩ := List.exists_cons_of_length_pos (by omega : 0 < ds.length)
  exact ⟨dB, dt, hd, e2.trans (cutPut_inner [] _ n (by rw [List.length_map]; exact hn))⟩

/-- **The like at the last chain.** -/
theorem some_rounds₃ (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (q₃ : (Fk X N
    P).second.blocksInOrder = c₃ :: k₃) (n : ℕ) (hn : n < k₃.length)
    (b : Block (Fk X N P).S₃ (Fk X N P).Cl) (base : ℕ) (ds : List RDT) (back : List _root_.Fmt.RoundView)
        (hb : (c₃ :: k₃)[n]? = some b) (hl : 0 < b.rounds.length)
    (hrow : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
        capRest capRest capRest () ())).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
        (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₃)[n]? = some (pieceOf
        (held b) base ds back (capRest n ds))) :
    ∃ dB dt, ds = dB :: dt ∧ back = [] := by
  obtain ⟨b', -, e⟩ := rowAt₃ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest
      capRest capRest () () n _ hrow
  have e1 : ds = cutDs (DK.at frS.P.T.a).ds₃ (held c₃ : Block (((Fk X N P).XiPub × (Fk X N P).S₁ ×
      (Fk X N P).S₂) × (Fk X N P).S₃) (Fk X N P).Cl) (k₃.map held) n := congrArg (·.ds) e
  have e2 : back = cutPut [] (k₃.map (held (P := ((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N
      P).S₂)))) n := congrArg (·.back) e
  have hlen : ds.length = b.rounds.length := by
    rw [e1, cutDs_held k₃ n _ c₃]
    exact stretch_len₃ (Fk X N P) "key file" (DK.at frS.P.T.a) hdata c₃ k₃ q₃ n b hb
  obtain ⟨dB, dt, hd⟩ := List.exists_cons_of_length_pos (by omega : 0 < ds.length)
  exact ⟨dB, dt, hd, e2.trans (cutPut_inner [] _ n (by rw [List.length_map]; exact hn))⟩

/-- **(i) hrow AT ROWS 2.9 | 2.10, IN SCOPE**: at n = 9 | 10, at whatever sub-protocol the look-up
  names. -/
theorem hrow_2 (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf
             Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk
             = true) (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at
             frS.P.T.a)) (n : ℕ) (hn : n = 9 ∨ n = 10)
    (b : Block (Fk X N P).S₂ (Fk X N P).Cl) (base : ℕ) (ds : List RDT) (back : List _root_.Fmt.RoundView)
    (hrow : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
        capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
        (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂)[n]? = some (pieceOf
        (held b) base ds back (capRest n ds))) :
    ∃ dB dt, ds = dB :: dt ∧ back = [] := by
  obtain ⟨b', hb', e⟩ := rowAt₂ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest
      capRest capRest () () n _ hrow
  obtain ⟨hr, hk⟩ := rounds₂_at X N P c₂ k₂ q₂ hZ hP hm hX hp hwant n b' hb'
  have hl : 0 < b'.rounds.length := by
    rcases hn with rfl | rfl
    · have h : 35 = b'.rounds.length := Option.some.inj hr
      omega
    · have h : 24 = b'.rounds.length := Option.some.inj hr
      omega
  have e1 : ds = cutDs (DK.at frS.P.T.a).ds₂ (held c₂ : Block (((Fk X N P).XiPub × (Fk X N P).S₁) ×
      (Fk X N P).S₂) (Fk X N P).Cl) (k₂.map held) n := congrArg (·.ds) e
  have e2 : back = cutPut [] (k₂.map (held (P := ((Fk X N P).XiPub × (Fk X N P).S₁)))) n := congrArg
      (·.back) e
  have hlen : ds.length = b'.rounds.length := by
    rw [e1, cutDs_held k₂ n _ c₂]
    exact stretch_len₂ (Fk X N P) "key file" (DK.at frS.P.T.a) hdata c₂ k₂ q₂ n b' hb'
  obtain ⟨dB, dt, hd⟩ := List.exists_cons_of_length_pos (by omega : 0 < ds.length)
  exact ⟨dB, dt, hd, e2.trans (cutPut_inner [] _ n (by rw [List.length_map]; rcases hn with rfl |
      rfl <;> omega))⟩

/-- **(i) hrow AT ROW 3.2, IN SCOPE.** -/
theorem hrow_32 (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃) (hZ : VerifierAndGoals.InScope Zp = true) (hP :
             ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N
             P).planOk = true) (hwant : (Fk X N P).wantedOk = true) (hdata : (Fk X N P).data "key file" = .ok
             (DK.at frS.P.T.a))
    (b : Block (Fk X N P).S₃ (Fk X N P).Cl) (base : ℕ) (ds : List RDT) (back : List _root_.Fmt.RoundView)
    (hrow : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
        capRest capRest capRest () ())).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
        (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₃)[2]? = some (pieceOf
        (held b) base ds back (capRest 2 ds))) :
    ∃ dB dt, ds = dB :: dt ∧ back = [] := by
  obtain ⟨b', hb', e⟩ := rowAt₃ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest
      capRest capRest () () 2 _ hrow
  have h2 := (rounds_in_scope hZ hP hm hX hp hwant).2.2
  have h3 := (lengths_in_scope hZ hP hm hX hp hwant).2.2
  rw [q₃] at h2 h3
  have hk : k₃.length = 3 := by simpa using h3
  have hr : roundsW₃[2]? = some b'.rounds.length := by
    rw [← h2, List.getElem?_map, hb']
    rfl
  have hl : 30 = b'.rounds.length := Option.some.inj hr
  have e1 : ds = cutDs (DK.at frS.P.T.a).ds₃ (held c₃ : Block (((Fk X N P).XiPub × (Fk X N P).S₁ ×
      (Fk X N P).S₂) × (Fk X N P).S₃) (Fk X N P).Cl) (k₃.map held) 2 := congrArg (·.ds) e
  have e2 : back = cutPut [] (k₃.map (held (P := ((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N
      P).S₂)))) 2 := congrArg (·.back) e
  have hlen : ds.length = b'.rounds.length := by
    rw [e1, cutDs_held k₃ 2 _ c₃]
    exact stretch_len₃ (Fk X N P) "key file" (DK.at frS.P.T.a) hdata c₃ k₃ q₃ 2 b' hb'
  obtain ⟨dB, dt, hd⟩ := List.exists_cons_of_length_pos (by omega : 0 < ds.length)
  exact ⟨dB, dt, hd, e2.trans (cutPut_inner [] _ 2 (by rw [List.length_map]; omega))⟩

/-- **(ii) THE DOOR's LAST MILE AT ROW 2.9, GENERAL IN hpay.** -/
theorem r2_9_of_pays (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₂ : (Fk X N P).shared.blocksInOrder
    = c₂ :: k₂) (hp : (Fk X N P).planOk = true)
    (hpay : ∀ (base : ℕ) (ds : List RDT) (back : List _root_.Fmt.RoundView),
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
          capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
          (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂)[9]? = some
          (pieceOf (held (B9 P)) base ds back (capRest 9 ds)) →
      Pays (W := Unit) (fr₂ (DK.at frS.P.T.a)) (pi9 P) (fun s t =>
          VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask) s = .ok t) (fun s t s' =>
          VerifiableInference.Desc.K12.Seat.leave s t = .ok s') (held (B9 P))
        (on9 X N P (DK.at frS.P.T.a) tabN enc rad off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN
            recBack) atSix (readAt tabN) enc rad) 9 base ds back (capRest 9 ds)) :
    KeepsAt (On₂' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad collN
        off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad)
        ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
        capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
        (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 9 := by
  have h8 : (Johnson.RunOne.Law.K12SeatsAt.tableBlocks X P).length = 8 :=
      Johnson.RunOne.Law.StepSide2.table_eight X N P hp
  have K : KeepsAt (on9 X N P (DK.at frS.P.T.a) tabN enc rad off₂N) (Cl₂ X N P (DK.at frS.P.T.a)
      (baseAt X decN recBack) atSix (readAt tabN) enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two)
      (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc
      (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest
      capRest () ())).l₂) 9 := by
    have K0 := keepsAt_U (W := Unit) X N P (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest
        capRest () () (on9 X N P (DK.at frS.P.T.a) tabN enc rad off₂N) (Cl₂ X N P (DK.at frS.P.T.a)
        (baseAt X decN recBack) atSix (readAt tabN) enc rad) q₂
    rw [h8] at K0
    exact K0 hpay
  intro p hpp
  exact Iop.Reduction.Leads.conseq ((KeepsAt.reached _ _ (rowBlocksF₂ q₂ 9) K) p hpp) (fun _ hx =>
      ⟨⟨hx.1, fun _ => hx.2⟩, hx.2⟩) (fun _ _ _ _ _ hq => ⟨⟨hq.1.1.1, hq.1.2⟩, hq.2⟩)

/-- **(ii) THE DOOR's LAST MILE AT ROW 2.10, GENERAL IN hpay.** -/
theorem r2_10_of_pays (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ) (q₂ : (Fk X N P).shared.blocksInOrder
    = c₂ :: k₂) (hp : (Fk X N P).planOk = true) (nO : H2U.PlaceNums) (hO : P.O = some nO)
    (hpay : ∀ (base : ℕ) (ds : List RDT) (back : List _root_.Fmt.RoundView),
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
          capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
          (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂)[10]? = some
          (pieceOf (held (B10 nO)) base ds back (capRest 10 ds)) →
      Pays (W := Unit) (fr₂ (DK.at frS.P.T.a)) (pi10 nO) (fun s t =>
          VerifiableInference.Desc.K12.Seat.enter (·.gOmega) (fun _ => none) s = .ok t) (fun s t s'
          => VerifiableInference.Desc.K12.Seat.leave s t = .ok s') (held (B10 nO))
        (on10 X N P (DK.at frS.P.T.a) tabN enc rad off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X
            decN recBack) atSix (readAt tabN) enc rad) 10 base ds back (capRest 10 ds)) :
    KeepsAt (On₂' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad collN
        off₂N) (Cl₂ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) enc rad)
        ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
        capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
        (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂) 10 := by
  have h8 : (Johnson.RunOne.Law.K12SeatsAt.tableBlocks X P).length = 8 :=
      Johnson.RunOne.Law.StepSide2.table_eight X N P hp
  have K : KeepsAt (on10 X N P (DK.at frS.P.T.a) tabN enc rad off₂N) (Cl₂ X N P (DK.at frS.P.T.a)
      (baseAt X decN recBack) atSix (readAt tabN) enc rad) ((atDesc (Fk X N P) (piecesAt (ckP .two)
      (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc
      (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest
      capRest () ())).l₂) 10 := by
    have K0 := keepsAt_O (W := Unit) X N P (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest
        capRest () () (on10 X N P (DK.at frS.P.T.a) tabN enc rad off₂N) (Cl₂ X N P (DK.at frS.P.T.a)
        (baseAt X decN recBack) atSix (readAt tabN) enc rad) q₂ nO hO
    rw [h8] at K0
    exact K0 hpay
  intro p hpp
  exact Iop.Reduction.Leads.conseq ((KeepsAt.reached _ _ (rowBlocksF₂ q₂ 10) K) p hpp) (fun _ hx =>
      ⟨⟨hx.1, fun _ => hx.2⟩, hx.2⟩) (fun _ _ _ _ _ hq => ⟨⟨hq.1.1.1, hq.1.2⟩, hq.2⟩)

/-- **(ii) THE DOOR's LAST MILE AT ROW 3.2, GENERAL IN hpay.** -/
theorem r3_2_of_pays (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hpay : ∀ (base : ℕ) (ds : List RDT) (back : List _root_.Fmt.RoundView),
      ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
          capRest capRest capRest () ())).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
          (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₃)[2]? = some
          (pieceOf (held (B32 P)) base ds back (capRest 2 ds)) →
      Pays (W := Unit) (fr₃ X N P (DK.at frS.P.T.a)) (pi32 P) (fun s t =>
          VerifiableInference.Desc.K12.Seat.enterOwn s = .ok t) (fun s t s' =>
          VerifiableInference.Desc.K12.Seat.leaveOwn s t = .ok s') (held (B32 P))
        (on32 X N P (DK.at frS.P.T.a) tabN off₂N off₃N) (Cl₃ X N P (DK.at frS.P.T.a) (baseAt X decN
            recBack) atSix (readAt tabN)) 2 base ds back (capRest 2 ds)) :
    KeepsAt (On₃' X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN) collN off₂N
        off₃N) (Cl₃ X N P (DK.at frS.P.T.a) (baseAt X decN recBack) atSix (readAt tabN)) ((atDesc
        (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest
        capRest capRest () ())).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at
        frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₃) 2 := by
  have K : KeepsAt (on32 X N P (DK.at frS.P.T.a) tabN off₂N off₃N) (Cl₃ X N P (DK.at frS.P.T.a)
      (baseAt X decN recBack) atSix (readAt tabN)) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N
      P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₃ :: (atDesc (Fk X N
      P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest
      () ())).l₃) 2 :=
    keepsAt_own (W := Unit) X N P (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ()
        (on32 X N P (DK.at frS.P.T.a) tabN off₂N off₃N) (Cl₃ X N P (DK.at frS.P.T.a) (baseAt X decN
        recBack) atSix (readAt tabN)) q₃ hpay
  intro p hpp
  exact Iop.Reduction.Leads.conseq ((KeepsAt.reached _ _ (rowBlocksF₃ q₃ 2) K) p hpp) (fun _ hx =>
      ⟨⟨hx.1, fun _ => hx.2⟩, hx.2⟩) (fun _ _ _ _ _ hq => ⟨⟨hq.1.1.1, hq.1.2⟩, hq.2⟩)

end

end LPFD

#print axioms LPFD.some_rounds₂
#print axioms LPFD.some_rounds₃
#print axioms LPFD.hrow_2
#print axioms LPFD.hrow_32
#print axioms LPFD.r2_9_of_pays
#print axioms LPFD.r2_10_of_pays
#print axioms LPFD.r3_2_of_pays
