-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerRowOfCut.lean: WHAT THE LEDGER AT THE CAP ASKS OF ITS ROW OF PIECES, HAD
FROM
THE MAKER's CUT, AT ANY TYPES OF RECORDS: so that it can be called at the ledger's own letters
(records P₁ × St), where a description F enters ONLY by its data and its declared rounds.
  front_of_tiled   hf1 ∧ hfb AT A PIECE: a piece that holds a block that says "ok" and declares no
                   round, below and lifted, and tiles with what follows: its yes keeps the record,
                   and
                   the next piece has its base. (frontByMake's own proof,
                   Johnson/Desc/Sound/SharedJointCountFront.lean, with the description taken out.)
  row_of_cut       T any Three at the data D of a description F, cut by the maker at blocks whose
                   declared rounds are F's: (1) the shared row holds these blocks (2) it tiles
                   (3) it opens no tree below D.t₁ (4) at AtCap rest₂ each piece's errors are the
                   cap
                   (5) each piece's written rounds are its block's declared rounds' data
                   (6) its first piece's base is D.t₁
  sends_declare    the kind's second and fifth blocks declare the sending kind's own two rounds
  send_facts       so at a piece's two written rounds along them: the first has the seed's entry and
                   the kind "seeds" (the ledger's he12 · hk12 | he15 · hk15)
  none_opened      at a written round along a declared round of one of the eight: no tree is opened
                   (the ledger's ho4): own_opens_none (Johnson/Desc/K14/Law/OpensNone.lean), called
USER     ledger_by_make (Johnson/Desc/K14/Law/LedgerByMakeTop.lean)
What is not claimed. That the seated description's T is the maker's at the cap. Nothing on
soundness.

-/
import Johnson.Desc.K14.Law.LedgerRowAlong
import Johnson.Desc.Sound.TilesDataProofs
import Johnson.Desc.Sound.TilesCutProofs
import Johnson.Desc.K14.Law.OpensNone

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Shared

/-! ## 1 The front, at a piece -/

theorem front_of_tiled {C : CK} {Fr : Frame} {P S Cl W : Type} (f pt : Piece C Fr (P × S) Cl W)
    (m : List (Piece C Fr (P × S) Cl W)) (fb : Block S Cl)
    (hbk : f.b = (below fb).lift Prod.snd fun (t : P × S) (s : S) => (t.1, s))
    (ht : Tiled f (pt :: m)) (hok : ∀ s rs gs, fb.decide s rs gs = .ok s) (hr : fb.rounds = []) :
    (∀ a τ b, f.ior.red.out a τ = some b → b.1 = a.1) ∧ pt.base = f.base := by
  refine ⟨fun a τ b hb => ?_, ?_⟩
  · have k1 : f.b.Leaves fun t => id (Prod.snd t) := by
      rw [hbk]
      exact leavesLiftIn _ _ _ _ id Prod.snd _ (below fb) (fun _ _ => rfl)
        (leavesBelow _ _ _ id fb (leaves_id_of_ok fb hok))
    have k2 : f.b.Leaves Prod.fst := by
      rw [hbk]
      exact leavesLift _ _ _ _ Prod.fst Prod.snd _ (below fb) fun _ _ => rfl
    exact Prod.ext (leavesOutOfBlock _ _ _ _ C _ Prod.fst _ k2 a τ b hb)
      (leavesOutOfBlock _ _ _ _ C _ _ _ k1 a τ b hb)
  · have ho : f.ds.length + f.back.length = f.b.rounds.length := ht.1.1
    have hr' : f.b.rounds = [] := by
      rw [hbk]
      exact hr
    rw [hr'] at ho
    have hds : f.ds = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_add_eq_zero_right ho)
    have h0 : f.trees = 0 := by
      unfold Piece.trees
      rw [hds]
      rfl
    rw [ht.2.2.2.1, h0, Nat.add_zero]

/-! ## 2 The row, at the maker's cut -/

theorem row_of_cut {Xi : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (hD : F.data file = .ok D) (hs : F.sealLast = true) {C : CK}
    {Y S₁ S₂ S₃ X₁ X₂ Cl W : Type} (T : Three C D (allOf D) Y S₁ S₂ S₃ X₁ X₂ Cl W)
    (b₁ : Block S₁ Cl) (l₁ : List (Block S₁ Cl)) (b₂ : Block S₂ Cl) (l₂ : List (Block S₂ Cl))
    (b₃ : Block S₃ Cl) (l₃ : List (Block S₃ Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₁ T.ft₁) S₁ W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₂ T.ft₂) S₂ W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₃ T.ft₃) S₃ W ds)
    (r : Fmt.RoundView) (g₁ : (b₁ :: l₁).map (·.rounds) = F.first.blocksInOrder.map (·.rounds))
    (g₂ : (b₂ :: l₂).map (·.rounds) = F.shared.blocksInOrder.map (·.rounds))
    (g₃ : (b₃ :: l₃).map (·.rounds) = F.second.blocksInOrder.map (·.rounds))
    (hcut : T.IsCut b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r) (hc : AtCap rest₂) :
    (T.p₂ :: T.l₂).map (·.b) = b₂ :: l₂ ∧ Tiled T.p₂ T.l₂ ∧
      (∀ x ∈ T.p₂ :: T.l₂, ∀ d₀ ∈ x.ds, ∀ j ∈ d₀.opens, D.t₁ ≤ j) ∧
      EachCapped 128 (T.p₂ :: T.l₂) ∧
      (∀ p ∈ T.p₂ :: T.l₂, Along (RoundIs (numAt D.t₁ D.t₂ 1)) p.b.rounds p.ds) ∧
      T.p₂.base = D.t₁ := by
  have hf : T.Fits := fitsOfData Xi F file D hD hs C Y S₁ S₂ S₃ X₁ X₂ Cl W T b₁ l₁ b₂ l₂ b₃ l₃ rest₁
    rest₂ rest₃ r g₁ g₂ g₃ hcut
  have h1 : T.p₂ = _ := congrArg Prod.fst hcut.c₂
  have h2 : T.l₂ = _ := congrArg Prod.snd hcut.c₂
  refine ⟨?_, hf.tiled₂, hop_of_own T hf (hown_of_data F file D hD),
    hcap_of_cut T b₂ l₂ rest₂ hcut.c₂ hc,
    (stretchOfData Xi F file D hD C Y S₁ S₂ S₃ X₁ X₂ Cl W T b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r g₁
      g₂ g₃ hcut).2.1, hf.base₂⟩
  rw [h1, h2]
  exact cutBlocks _ _ _ _ _ rest₂ [] l₂ b₂ 0 D.t₁ D.ds₂

/-! ## 3 Along the spelled pieces -/

section
variable (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
  (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
include hbl

theorem sends_declare (sentU : Array OracleNotice) (hU : withU Q.S = some sentU) :
    b2.rounds = VerifiableInference.Desc.K1.rounds (parK1 Q 2 "o_u and the first mask" sentU) ∧
      b5.rounds =
        VerifiableInference.Desc.K1.rounds (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) := by
  unfold blocks at hbl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hbl
  obtain ⟨s, hs, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbl
  obtain rfl : s = sentU := Option.some.inj (hs.symm.trans hU)
  exact ⟨rfl, rfl⟩

omit hbl in
/-- Two written rounds along a sending's declared rounds. -/
theorem send_facts (P : VerifiableInference.Desc.K1.Par) (num : Fmt.TreeSource → ℕ) (d₁ d₂ : RDT)
    (h : Along (RoundIs num) (VerifiableInference.Desc.K1.rounds P) [d₁, d₂]) :
    d₁.entry = VerifiableInference.Desc.K1.seedEntry P ∧ d₁.kind = .seeds := by
  have h1 : RoundIs num { entry := VerifiableInference.Desc.K1.seedEntry P } d₁ := h.1
  refine ⟨h1.1, ?_⟩
  have h2 : Fmt.kindOf "SEND seed" = some d₁.kind := h1.2.1
  exact (Option.some.inj h2).symm

/-- A written round along a declared round of one of the eight opens no tree. -/
theorem none_opened (x : Block St Unit) (hx : x ∈ [b1, b2, b3, b4, b5, b6, b7, b8])
    (num : Fmt.TreeSource → ℕ) (r : Fmt.DeclaredRound) (hr : x.rounds = [r]) (d : RDT)
    (h : Along (RoundIs num) x.rounds [d]) : d.opens = [] := by
  have ho : r.opens = [] := own_opens_none Q b1 b2 b3 b4 b5 b6 b7 b8 hbl x hx r
    (by rw [hr]; exact List.mem_singleton.2 rfl)
  rw [hr] at h
  have h1 : RoundIs num r d := h.1
  rw [h1.2.2.2.2.1, ho]
  rfl

end

end Desc.K14.Law
