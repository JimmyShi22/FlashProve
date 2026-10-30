-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/KeepsAtRows.lean: THE
PLAIN LAW "Keeps" AT THE MAKER'S OWN PIECES OF THE KIND'S BLOCK AND OF THE LAYER OF ROWS (seats 1.4,
1.5, 1.10 and 1.11 of the key file's first chain), BETWEEN THE LINKS' ROWS AT THE FILLING FROM THE
TABLE'S LETTERS (rowT, TieStated.lean), at the very row of pieces at which the frame LPFD.The21
states its fields. The layer: its tie (layerJ_tie, JoinKeyD.lean), lifted as a family, held, and
carried to the plain form by keeps_of_tie (Johnson/Desc/Sound/KeyKeepsOfSeats.lean).
The kind's block: the seat's "good" (fk_link_low, LinkAtLow.lean) at a list of rows written out,
carried by keeps_of_good; its second premise, that the promise behind is kept for certain, from the
record's step (k3_walk, Walk.lean) and from what the decoder's condition reads.

Main names:
  keeps_layer: at piece 2 + 6 l + 3 of the maker's row:
    Keeps (rowT l 3).on (rowT l 4).on (rowT l 3).rel (rowT l 4).rel, at the piece's own errors.
  keyRowAt_pad: a list of rows that has seven given rows from a given border on.
  keeps_k3: at piece 2 + 6 l + 2: Keeps (rowT l 2).on (rowT l 3).on (rowT l 2).rel (rowT l 3).rel,
    where the first chain's rests have the cap at 128 as their errors.

Object: Key.layer and the kind's own block at their places in Key.descriptionFromSource X N P's first chain.
User: FieldR14.lean and FieldR110.lean call keeps_k3; FieldsLayer.lean calls keeps_layer.
Letters: the table's B, at_, R, coll; the frame's heads, tails and rests. Premises: the plan's tests
· the flat lists' heads and tails · the data · NO TWO TREES OF THE FRAME HAVE ONE NUMBER · the
pulled-back decoder and condition read below the piece's place (LowDec: shown of this filling by
nobody yet)
(Where this and lean/THEOREM.md differ, the page
holds.) · for the kind's block besides: target = 128 · LookHeld · the cap · a value of the
riding part's type · a witness.

Limits. Between the links' rows (rowT), not the table's. Nothing on soundness.

-/
import Johnson.RunOne.Law.PiecesSame
import Johnson.RunOne.Law.TiePromise
import Johnson.Desc.Sound.KeyKeepsOfSeats
import Iop.ErrCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.KeepsAtRows
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat OnBytes.Slice
open _root_.Run (ckP)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Claim Source KRead Where)
open Johnson.RunOne.Sound (FK fk_link_at fk_K3_at)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.PromKeyD
open Johnson.RunOne.Law.SeatsAtFK
open Johnson.RunOne.Law.LinkSeats
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtFK
open Johnson.RunOne.Law.LinkAtCut
open Johnson.RunOne.Law.LinkAtLow
open Johnson.RunOne.Law.LinkPriced
open Johnson.RunOne.Law.LettersAt
open Johnson.RunOne.Law.Walk
open Johnson.RunOne.Law.TieStated

variable {W Cells Mm Smp Rec : Type} (X : Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces) (D : WholeD) (B : BaseSt Cells Mm Smp Rec)
  (at_ : Where) (R : KRead Cells Mm) (coll : Strs → Rec → Prop)
  (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
  (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl) (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl))
  (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) ((Fk X N P).XiPub × (Fk X N P).S₁) W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0)
    (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt D (allOf D) D.key₃ (Fk X N P).lastChainFirstTreeNumber)
      (((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N P).S₂) × (Fk X N P).S₃) W ds)
  (dW wEnd : W)

/-- **The layer's piece keeps, between the links' rows.** -/
theorem keeps_layer (hp : (FK X N P).planOk = true) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hnd : ((fr₁ D).all.map (·.no)).Nodup) (l : ℕ)
    (hl : l < X.Y.k.oneTime.ranges.lookups.length) (p)
    (hq : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃
        dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁)[2 + 6 * l + 3]? = some p)
    (hlow : LowDec (fun a : TK Xi × (fr₁ D).E.Str => decT X N P D B at_ (pullK a.1, a.2))
      (fun a : TK Xi × (fr₁ D).E.Str => condT X N P D B at_ coll (pullK a.1, a.2)) p.base) :
    p.ior.red.Keeps (rowT X N P D B at_ R coll l 3).on (rowT X N P D B at_ R coll l 4).on
      (rowT X N P D B at_ R coll l 3).rel (rowT X N P D B at_ R coll l 4).rel p.err := by
  have hW := fk_admitted X N P hp
  have hid : X.Y.k.oneTime.ranges.messageId ≠ 0 := by
    rw [fk_messageId X N P hp]
    exact Nat.one_ne_zero
  obtain ⟨b, base, ds, back, hb, rfl⟩ := LPFD.rowGet₁ (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃
    rest₁ rest₂ rest₃ dW wEnd (2 + 6 * l + 3) p hq
  rw [← q₁, Nat.add_assoc] at hb
  obtain ⟨c0, c4, c5, hF, -, -, -⟩ := link_flat X.Y.k.oneTime X.set l
    (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime
        l))
  have hc := (fk_link_at X N P l 3 (by omega) _ (look_at X.Y.k.oneTime l hl)).symm.trans hb
  rw [hF] at hc
  obtain rfl := Option.some.inj hc
  refine keeps_of_tie _ (rowT X N P D B at_ R coll l 3) (rowT X N P D B at_ R coll l 4)
    (quietTie_held _ _ _ (quietOwn_upF fun p₀ => layerJ_tie (p₀ := p₀)
      (promise_ledgers hid (kept_true _ _ _ _)) l
      (Lk6.adm_of_tests _ _ _ (tests_at hW hl).2.1 (tests_at hW hl).2.2) (tests_at hW hl).2.1
      (tests_at hW hl).2.2 (tests_at hW hl).1 (layout_of_admitted hW))) hnd ?_ ?_
  · exact (low_upF fun _ => low_andQ _ (low_row3 (low_R l _ hlow))).1
  · exact (low_upF fun _ => low_andQ _ (low_row3 (low_R l _ hlow))).2

/-- A list of rows that has the seven rows f 0 … f 6 from border a + 1 on. -/
theorem keyRowAt_pad {S : Type} {F : Frame} (A : JointRow S F) (f : ℕ → JointRow S F) (a j : ℕ)
    (hj : j ≤ 6) :
    keyRowAt A (List.replicate a A ++ (List.range 7).map f) (a + 1 + j) = f j := by
  unfold keyRowAt
  have e : a + 1 + j = (a + j) + 1 := by omega
  rw [e, List.getElem?_cons_succ, List.getElem?_append_right (by simp)]
  simp only [List.length_replicate, Nat.add_sub_cancel_left, List.getElem?_map]
  rw [List.getElem?_range (by omega)]
  rfl

set_option maxHeartbeats 1600000 in
/-- **The piece of the kind's own block keeps, between the links' rows**, where the rests' errors
are the cap at 128. -/
theorem keeps_k3 (hp : (FK X N P).planOk = true) (file : String)
    (hD : (FK X N P).data file = .ok D) (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂) (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
    (hnd : ((fr₁ D).all.map (·.no)).Nodup) (ht : X.set.target = 128) (l : ℕ)
    (hl : l < X.Y.k.oneTime.ranges.lookups.length)
    (hL : LookHeld X.set (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId
      (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l))))
    (hcap : ∀ n ds, (rest₁ n ds).err = Iop.Err.cap 128 (uLT (ckP .two) ds))
    (st0 : TK Xi) (hw : Nonempty (Wit Cells Unit Mm × Unit))
    (hlow : ∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂
        rest₃ dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁)[2]? = some p →
      LowDec (fun a : TK Xi × (fr₁ D).E.Str => decT X N P D B at_ (pullK a.1, a.2))
        (fun a : TK Xi × (fr₁ D).E.Str => condT X N P D B at_ coll (pullK a.1, a.2)) p.base) (p)
    (hq : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃
        dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁)[2 + 6 * l + 2]? = some p)
    (hlowp : LowDec (fun a : TK Xi × (fr₁ D).E.Str => decT X N P D B at_ (pullK a.1, a.2))
      (fun a : TK Xi × (fr₁ D).E.Str => condT X N P D B at_ coll (pullK a.1, a.2)) p.base) :
    p.ior.red.Keeps (rowT X N P D B at_ R coll l 2).on (rowT X N P D B at_ R coll l 3).on
      (rowT X N P D B at_ R coll l 2).rel (rowT X N P D B at_ R coll l 3).rel p.err := by
  haveI : Inhabited W := ⟨dW⟩
  have herr : ∀ (n : ℕ) (q : Piece (ckP .two) (frameAt D (allOf D) D.key₁ 0)
      ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl W), ((atDesc (Fk X N P) (piecesAt (ckP .two)
          (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁
      rest₂ rest₃ dW
      wEnd)).p₁ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
      wEnd)).l₁)[n]? = some q → q.err = Iop.Err.cap 128 (uLT (ckP .two) q.ds) := by
    intro n q hn
    obtain ⟨b, base, ds, back, -, rfl⟩ := LPFD.rowGet₁ (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃
      rest₁ rest₂ rest₃ dW wEnd n q hn
    exact hcap n ds
  have hr : ∀ j ≤ 6, keyRowAt (rowT X N P D B at_ R coll l 0)
      (List.replicate (1 + 6 * l) (rowT X N P D B at_ R coll l 0) ++
        (List.range 7).map (rowT X N P D B at_ R coll l)) (2 + 6 * l + j) =
      rowT X N P D B at_ R coll l j := by
    intro j hj
    have e : 2 + 6 * l + j = 1 + 6 * l + 1 + j := by omega
    rw [e]
    exact keyRowAt_pad _ _ _ j hj
  have seats := fk_link_low X N P hp file D hD c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ rest₁ rest₂ rest₃ dW wEnd
    l hl ((2 : ENNReal)⁻¹ ^ 128) _ _ (Nat.zero_ne_one) (kept_true _ _ _ _) hr
    (blind_pull (decT X N P D B at_) (condT X N P D B at_ coll) (OthT X R)) st0 hw hlow
    (fun j _ q hn => by rw [herr _ q hn]; exact Iop.Err.cap_below_inv 128 _)
    (fun q hn hds => by
      rw [herr _ q hn]
      refine Iop.Err.le_cap_of_below_inv 128 _ ?_
      exact ht ▸ fk_k3_below X N P hp file D hD c₁ k₁ c₂ k₂ c₃ k₃ q₁ q₂ q₃ rest₁ rest₂ rest₃ dW
        wEnd l hl hL st0 q hn hds) 2 (by omega) p (by rw [← Nat.add_assoc]; exact hq)
  have hgood := seats.1
  have e2 : 2 + (6 * l + 2) = 2 + 6 * l + 2 := by omega
  have e3 : 2 + (6 * l + 2) + 1 = 2 + 6 * l + 3 := by omega
  rw [e3, e2] at hgood
  erw [hr 2 (by omega), hr 3 (by omega)] at hgood
  refine keeps_of_good p _ _ hgood fun a τ b ha hb => ?_
  have hW := fk_admitted X N P hp
  have hid : X.Y.k.oneTime.ranges.messageId ≠ 0 := by
    rw [fk_messageId X N P hp]
    exact Nat.one_ne_zero
  have hpb : p.b = held (lookupKind VerifiableInference.Desc.Key.lookupSeat [(1, 0), (1, 1)] 0 []
      (VerifiableInference.Desc.Key.lookupPlace X.set l
        (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
          (Lof X.Y.k.oneTime l)))) := by
    have h1 := LPFD.rowBlocks₁ (ckP .two) (Fk X N P) D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd
      (2 + 6 * l + 2) p hq
    have h2 : (c₁ :: k₁)[2 + 6 * l + 2]? =
        some (lookupKind VerifiableInference.Desc.Key.lookupSeat [(1, 0), (1, 1)] 0 []
          (VerifiableInference.Desc.Key.lookupPlace X.set l
            (Wf.lookupOf X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
              (Lof X.Y.k.oneTime l)))) := by
      rw [← q₁, Nat.add_assoc]
      exact fk_K3_at X N P l _ (look_at X.Y.k.oneTime l hl)
    rw [List.getElem?_map, h2] at h1
    exact (Option.some.inj h1).symm
  obtain ⟨⟨p₀, s⟩, y⟩ := a
  obtain ⟨⟨p₁, s'⟩, y'⟩ := b
  have hd := piece_decides_at p ((p₀, s), y) τ ((p₁, s'), y') hb
  rw [hpb] at hd
  obtain ⟨e1, hd'⟩ := VerifiableInference.Desc.Plain.held_decide _ _ _ _ _ hd
  obtain rfl : p₀ = p₁ := e1.symm
  obtain rfl : y' = p.ior.imp y τ := congrArg Prod.snd (out_imp p _ _ τ hb)
  have ha' : (rowT X N P D B at_ R coll l 2).on ((p₀, s), y) := ha
  unfold rowT at ha'
  have hon := (rows7_on (Fr := fr₁ D) _ _ _ _ _ _ _ _ _ p₀ _ _ _ _ _ _ l 2 (by omega) s y).1
    ((upF_on (Fr := fr₁ D) _ p₀ s y).1 ha')
  have hrec := k3_walk (set := X.set) X.Y.k.oneTime.ranges.lookups.length
    (promise_ledgers hid (kept_true _ _ _ _)) l
    (Lk6.adm_of_tests _ _ _ (tests_at hW hl).2.1 (tests_at hW hl).2.2)
    (d_le (tests_at hW hl).2.1) s s' _ _ hon.2 hd'
  obtain ⟨F, g, G, es, -, -, -, -, -, rfl⟩ := block_law _ _ _ _ _ hd'
  have hrb : ReadsBelow p.base (fun t : (Xi × FirstState) × (fr₁ D).E.Str =>
      condT X N P D B at_ coll (pullK (stK t.1.1 l t.1.2), t.2)) :=
    fun t y y' h1 h2 => propext (hlowp _ y y' h1 h2).2
  show (rowT X N P D B at_ R coll l 3).on _
  unfold rowT
  refine (upF_on (Fr := fr₁ D) _ p₀ _ _).2
    ((rows7_on (Fr := fr₁ D) _ _ _ _ _ _ _ _ _ p₀ _ _ _ _ _ _ l 3 (by omega) _ _).2 ⟨?_, hrec⟩)
  have e := hrb.imp hnd p (Nat.le_refl _) (p₀, s) y τ
  exact e.symm ▸ hon.1

end Johnson.RunOne.Law.KeepsAtRows

#print axioms Johnson.RunOne.Law.KeepsAtRows.keeps_layer
#print axioms Johnson.RunOne.Law.KeepsAtRows.keeps_k3
