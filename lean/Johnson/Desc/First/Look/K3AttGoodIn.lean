-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3AttGoodIn.lean: THE CLOSING FILE OF A SECOND CHAIN: the lookup on the
CALLS of an attention link, WITH ITS RIDER: from the law on the kind's decide and the closed caller
(Johnson/Desc/First/Look/K3CallerAtt.lean) to the form that the rule of composition asks of a block
(Piece.GoodIn), by the rule's own carriage (pieceGoodIn). After the pattern of
Johnson/Desc/First/Look/K3DigitsGoodIn.lean. Definitions, and one theorem at letters for the kind's
decide and the record's two readers. NO SOUNDNESS OF THE PROTOCOL IS CLAIMED: the premises that are
not theorems are premises.

THE END THEOREM k3_att_goodIn_of: the piece p has GoodIn between
  on   AttOn: Own holds of the carried record; no oracle message of the signature has a collision at
       its sample's seed (CfSig at all members); the record's ledger has its sizes;
  RA   AttFront: every oracle message of the signature is shown and decodes, with its sample, to the
       witness's message (PinSig at all members), AND (AttSays) EVERY KEY OF THE FOUR VECTORS,
       computed from the cells behind the symbols that the witness's messages hold, IS A ROW OF ITS
       TABLE, AND IDENTITY at3 IS 0 AT EVERY VALID INDEX (the denominator is the row's sum);
  on'  AttOn': Own and CfSig of the statement behind; a ledger F' WITH ITS SIZES and what was heard,
       g, stand in the record behind, and stand for some rounds (K3Stands): so what the condition
       in front asks of the ledger is promised again behind;
  RB   AttBehind: WHAT THE LATER BLOCKS OWE: PinSig still; THE ROW OUT (K3Out,
       Johnson/Top/H/K3RowOut.lean) at the record's g and F', at the same witness's entries; AND ITS
       FOURTH ITEM (K3OutRider, Johnson/Top/H/K3RowOutRider.lean): whatever rounds the heard record
       stands for, at3's multilinear extension is 0 at the chosen places of their key point, at the
       same witness's messages.
  err  the least written errors that bear the proved block's (bearT). The rider adds nothing to them
       (lookupCR_eps, Johnson/Top/H/LookupCRide.lean).

WHAT DIFFERS FROM THE DIGITS. The caller has one rider (the library's crDen). The signature's list
holds the kept messages of earlier links, then the link's own of moment 0. The planes' matrix has
2 ^ x.lm rows, not 2 ^ 5. Behind the block the proved joint has a clause on the rider: it is met by
the fourth item, through lookKindR_view (the out-statement by name) and lookRider_at.

WHERE THE RIDER IS, AND WHERE IT IS NOT. THE RIDER IS IN THE CHAIN ON THE
PROVED BLOCK's SIDE, AND NOWHERE ON THE TEXT's: the theorem is of the text's decide and of THE
LIBRARY's rider. No premise and none of the four relations names the text's list of guests: the
theorem holds at every list, the empty one among them (Johnson/Desc/First/Look/K3AttInst.lean:
k3_att_noGuests is the end theorem at guests := []). That decide does not read the list is not shown
here; the block's test on the plan (planOk) does read it.

Limits. Those of K3DigitsGoodIn.lean and of K3CallerAtt.lean. fork, heard, decide are letters. WHO
GIVES RB's FOURTH ITEM is owed with the laws of the kind "attention", and who gives
the three others is owed at the batching's front. Own, smp, seatT, arr, G stay letters, with laws.
The extractor is the identity.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3DigitsGoodIn
import Johnson.Desc.First.Look.K3CallerAtt
import Johnson.Top.H.K3RowOutRider

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

theorem att_foOk {set : Params.Setting} {x : Desc.First.Look.Place} {A : Attention.Shape}
    {tl : HTailF2} {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ}
    (H : AttOK set x A tl D rad) : FoNums.ok x.fs = true := by
  obtain ⟨h₀, a, b, e⟩ := shape_made H.shape
  rw [e]
  exact Cb.Fo.shape_ok a b

section
variable {S Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  (x : Desc.First.Look.Place) (A : Attention.Shape) (tl : HTailF2) (D : Desc.First.Look.Sent)
  (rad : OracleShape → ℕ)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : S → (i : Fin (sigListCalls D rad x.link).length) → Option ((attSg x D rad).om i).Smp)
  (fork : S → Option Fork) (heard : S → Option Forest.Heard) (Own : S → Prop)

local notation "𝐫" => attRider x A tl D rad extNone Unit
local notation "𝐋" => attLay A x.fs x.lm x.F.next x.ns tl
local notation "𝐥" => sigListCalls D rad x.link

/-- The witness's messages, as the signature's tuple. -/
def attMs (w : Desc.Wit Cells Tok MsgT) : (attSg x D rad).Msg := msgsOf D.codes 𝐥 seatT arr w

/-- The entries, read off the witness's messages by the caller's msg₀. -/
def attMu (w : Desc.Wit Cells Tok MsgT) : JAtt x.ns tl → Cb.Gl.E :=
  msgAtt D.codes 𝐥 (Desc.First.Look.seatCalls D x.link) tl x.ns (attMs x D rad seatT arr w)

/-- The reading of the places: a mask, a cell of the planes' matrix. -/
def attNu (w : Desc.Wit Cells Tok MsgT) (q : _root_.Fo.Pl) : Cb.Gl.E :=
  zext (attMu x tl D rad seatT arr w)
    (placeOf (enMask x.ns tl) (enCell x.ns tl (A.cf.NAs + 2)) q)

/-- **What the joint in front says of a tuple of messages** (att_says' right side). -/
def AttSays (m : (attSg x D rad).Msg) : Prop :=
  (∀ k < x.fs.NC, ∀ b < 2 ^ Cb.LdLkp.Port.nOf x.fs k, ∃ u < 2 ^ Cb.LdLkp.Port.kOf x.fs k,
    𝐋.K () (msgAtt D.codes 𝐥 (Desc.First.Look.seatCalls D x.link) tl x.ns m) k b =
      ((FoNums.tauN x.fs k u : ℕ) : Cb.Gl.E)) ∧
  ∀ b g i, Inst.Model.AttSeg.Idn.Valid (Road.L5.dimOf A) (.at3 b g i) →
    Inst.Model.AttSeg.idnVal (Road.L5.dimOf A) (attCells x A tl D rad m) (.at3 b g i) = 0

/-- **The condition in front.** -/
def AttOn (a : S × Fr.E.Str) : Prop :=
  Own a.1 ∧ CfSig G D.codes 𝐥 seatT smp (fun _ => True) a.1 (strsOf Fr a.2) ∧
    ∃ Fk, fork a.1 = some Fk ∧ OnBytes.PscRun.Sized Fk

/-- **The promise behind.** -/
def AttOn' (a : S × Fr.E.Str) : Prop :=
  Own a.1 ∧ CfSig G D.codes 𝐥 seatT smp (fun _ => True) a.1 (strsOf Fr a.2) ∧
    ∃ (g : Forest.Heard) (F' : Fork), fork a.1 = some F' ∧ heard a.1 = some g ∧
      OnBytes.PscRun.Sized F' ∧ K3Stands x.fs x.lm x.F.next Reading.gl g F'

/-- **The relation in front.** -/
def AttFront (a : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT) : Prop :=
  PinSig G D.codes 𝐥 seatT smp arr (fun _ => True) a.1 (strsOf Fr a.2) w ∧
    AttSays x A tl D rad (attMs x D rad seatT arr w)

/-- **The relation behind: what the later blocks owe.** -/
def AttBehind (a : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT) : Prop :=
  PinSig G D.codes 𝐥 seatT smp arr (fun _ => True) a.1 (strsOf Fr a.2) w ∧
    ∃ (g : Forest.Heard) (F' : Fork), fork a.1 = some F' ∧ heard a.1 = some g ∧
      K3Out x.fs x.lm x.F.next (attNu x A tl D rad seatT arr w)
        (forK Cb.Gl.E 𝐋 () (zext (attMu x tl D rad seatT arr w))) Reading.gl g F' ∧
      K3OutRider 𝐫 x.lm x.F.next () (attMs x D rad seatT arr w) g F'

/-- The statement of the proved block that is read off the statement in front. -/
def attRd (σ₀ : (attSg x D rad).Smp) (a : S × Fr.E.Str) :
    (Unit × (attSg x D rad).Smp) × (extNone.prod (attSg x D rad).ext).Str :=
  (((), fun i => (smp a.1 i).getD (σ₀ i)), ((), wordsOf G D.codes 𝐥 seatT (strsOf Fr a.2)))

/-- The proved block's witness that is read off the rule's. -/
def attRw (w : Desc.Wit Cells Tok MsgT) : (attSg x D rad).Wit × Unit :=
  (fun i => (attMs x D rad seatT arr w i, fun _ => 0), ())

variable {x A tl D rad}

/-- **THE END THEOREM, at letters for the kind's decide and the record's two readers.** -/
theorem k3_att_goodIn_of {set : Params.Setting}
    (p : Piece (ckP .two) Fr S Cl (Desc.Wit Cells Tok MsgT)) (H : AttOK set x A tl D rad)
    (decide : S → List Fmt.RoundView → List (List (ℕ × List UInt64)) → Except String S)
    (hext : ∀ a τ w, p.ext a τ w = w)
    (hr : (Desc.First.Look.P.ofPlace set false x).entries.isSome = true)
    (hd : ∀ d ∈ p.ds, Fo.Peel.Plain (toRD d)) (hA : ∀ d ∈ p.ds, NoAns d.items)
    (he : p.ds.map (·.entry) = (Desc.First.Look.P.ofPlace set false x).rounds.map (·.entry))
    (hε : bearT p.ds _ ((kLookupCRN [𝐫]).ε 𝐫) = some p.err)
    (hCut : PieceHears p decide)
    (hD : K3DecideHears fork heard (Desc.First.Look.P.ofPlace set false x).calls
      (Desc.First.Look.P.ofPlace set false x).pub (Desc.First.Look.P.ofPlace set false x).lid
      decide)
    (hsmp : ∀ s rs cols s', decide s rs cols = .ok s' → smp s' = smp s)
    (hOwn : ∀ s rs cols s', decide s rs cols = .ok s' → Own s → Own s')
    (hnext : ∀ s rs cols s' Fk, decide s rs cols = .ok s' → fork s = some Fk →
      Fk.next = x.F.next)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) :
    p.GoodIn (AttOn G x D rad seatT smp fork Own) (AttOn' G x D rad seatT smp fork heard Own)
      (AttFront G x A tl D rad seatT arr smp)
      (AttBehind G x A tl D rad seatT arr smp fork heard) := by
  have hM := att_meets H hr p.ds hd he
  have hrm : 𝐫 ∈ (kLookupCRN [𝐫]).sizes := List.mem_singleton.2 rfl
  have hKA := lookupCRN_knowAt [𝐫] (att_ok extNone Unit H) (att_sel extNone Unit H)
  refine pieceGoodIn S Cl _ _ Fr p _ _ _ _ ((kLookupCRN [𝐫]).toKind.block 𝐫).R.red
    (fun _ => lookCarryT x.fs 𝐋 extNone p.ds hM.length_eq) ((kLookupCRN [𝐫]).ε 𝐫)
    (attRd G x D rad seatT smp σ₀) _ _ ((kLookupCRN [𝐫]).toKind.src 𝐫).on
    ((kLookupCRN [𝐫]).toKind.dst 𝐫).on _ _ ((kLookupCRN [𝐫]).toKind.src 𝐫).relR
    ((kLookupCRN [𝐫]).toKind.dst 𝐫).relR ((kLookupCRN [𝐫]).toKind.block 𝐫).ext
    (fun _ => lookCarryT_fits x.fs 𝐋 extNone p.ds hM _ _ (bearT_bears _ _ _ _ hε)) ?_ ?_
    (knowInOfCarry _ _ _ _ _ _ _ _ _ _ _
      (fun a τ b ha hb =>
        BaseKind.onOut_toKind (BaseKind.onOut_of_knowAt hKA) 𝐫 hrm a τ b hb ha)
      (BaseKind.know_toKind (BaseKind.know_of_knowAt hKA) 𝐫 hrm))
  · -- the condition in front gives the proved block's
    rintro a ⟨-, hCf, -⟩
    obtain ⟨σ, hσ, hcf⟩ := cfSig_over G D.codes 𝐥 seatT smp a.1 _ hCf
    refine (att_src_on extNone Unit (attRd G x D rad seatT smp σ₀ a)).2 ?_
    have e : (attRd G x D rad seatT smp σ₀ a).1.2 = σ := funext fun i => by
      show (smp a.1 i).getD (σ₀ i) = σ i
      rw [hσ i]
      rfl
    show (attSg x D rad).CF (attRd G x D rad seatT smp σ₀ a).1.2 _
    rw [e]
    exact hcf
  · -- the block's yes
    rintro ⟨s, y⟩ τ ⟨s', y'⟩ ⟨hOw, hCf, Fk, hFk, hSz⟩ ho
    obtain ⟨hp, e2, hw, cols, hdec⟩ := hCut _ τ _ ho
    have e2' : y' = behind (ckP .two) Fr p.base p.ds y τ := e2
    subst e2'
    have hCf1 : CfSig G D.codes 𝐥 seatT smp (fun _ => True) s (strsOf Fr y) := hCf
    have hdec1 : decide s ((rvT (ckP .two) p.ds τ).map Desc.noDigest) cols = .ok s' := hdec
    have hs' : smp s' = smp s := hsmp _ _ _ _ hdec1
    have hnx : Fk.next = x.F.next := hnext _ _ _ _ _ hdec1 hFk
    -- (L1) at the closed caller
    obtain ⟨X, hx, hiff⟩ := out_iff_items [𝐫] 𝐫 (att_foOk H) x.lm x.F.next (att_lm H).1
      (att_lm H).2 (enMask x.ns tl) (enCell x.ns tl (A.cf.NAs + 2))
      (fun t => att_mkS extNone Unit t) (fun t k j _ => att_bc extNone Unit t k j) p.ds hM hA
      (attRd G x D rad seatT smp σ₀ (s, y)) τ
    -- the out-statement by name: for the rider's clause
    have eX := out_is_lookOutE [𝐫] 𝐫 (att_foOk H) x.lm x.F.next (enMask x.ns tl)
      (enCell x.ns tl (A.cf.NAs + 2)) (fun t => att_mkS extNone Unit t)
      (fun t k j _ => att_bc extNone Unit t k j) p.ds hM hA
      (attRd G x D rad seatT smp σ₀ (s, y)) τ X hx
    rw [mapsT_view] at hx
    -- (L2a): what was heard stands for the transcript's rounds
    obtain ⟨F1, F2, g, d1, d2, d3, -, hlaw⟩ := hD Cb.Gl.E Reading.gl x.lm s s' _ cols hw hdec1
    obtain rfl : Fk = F1 := Option.some.inj (Eq.trans (Eq.symm hFk) d1)
    obtain ⟨hSh, hPad, hI⟩ := hlaw hSz
    have hg : g.shape = x.fs := by
      obtain ⟨h0, a0, -, a2⟩ := hSh
      obtain ⟨h1, b0, -, b2⟩ := shape_made H.shape
      have e : h0 = h1 := Except.ok.inj (a0.symm.trans b0)
      rw [a2, b2, e]
    rw [hg, hnx, viewRounds_noDigest] at hI
    refine ⟨lookImgT x.fs 𝐋 extNone p.ds τ, _,
      lookCarryT_pass x.fs 𝐋 extNone p.ds hM.length_eq τ hp, hx,
      fun _ => ⟨hOwn _ _ _ _ hdec1 hOw, fun i _ =>
        (pinStays (Cells := Unit) (Tok := Unit) G D.codes 𝐥 seatT smp arr
          (ckP .two) Fr p.base p.ds s' y τ ⟨(), (), fun _ _ _ _ => 0, fun _ _ _ _ _ => 0⟩ i
          (hseat i)).2.2
          (by
            have h0 := hCf1 i trivial
            unfold CfAt at h0 ⊢
            rw [hs']
            exact h0),
        g, F2, d2, d3, hPad.fit, _, hI⟩, ?_⟩
    rintro w ⟨⟨hSF, hPA⟩, g', F'', f1', f2', ⟨k1, k2, k3⟩, k4⟩
    obtain rfl : g = g' := Option.some.inj (Eq.trans (Eq.symm d3) f2')
    obtain rfl : F2 = F'' := Option.some.inj (Eq.trans (Eq.symm d2) f1')
    -- the pins, carried back to the statement in front
    have hpin0 : PinSig G D.codes 𝐥 seatT smp arr (fun _ => True) s (strsOf Fr y) w :=
      ⟨hSF, fun i _ => by
        have h0 := (pinStays G D.codes 𝐥 seatT smp arr (ckP .two) Fr p.base p.ds
          s' y τ w i (hseat i)).1.1 (hPA i trivial)
        unfold PinAt at h0 ⊢
        rw [hs'] at h0
        exact h0⟩
    obtain ⟨σ, hσ, hdecs⟩ := pinSig_over G D.codes 𝐥 seatT smp arr s _ w hpin0
    have e : (attRd G x D rad seatT smp σ₀ (s, y)).1.2 = σ := funext fun i => by
      show (smp s i).getD (σ₀ i) = σ i
      rw [hσ i]
      rfl
    have hout := (hiff (attMu x tl D rad seatT arr w)).2 ⟨k1 _ hI, k2 _ hI, k3 _ hI⟩
    have htgt : (𝐫).tgt (attMs x D rad seatT arr w) (X, ()) := by
      rw [eX]
      exact tgt_of_rider 𝐫 x.lm x.F.next _ () (attMs x D rad seatT arr w) g F2 _ () hI k4
    refine ⟨attRw x D rad seatT arr w, ⟨?_, ⟨⟨trivial, hout⟩, htgt⟩⟩, fun hRA => ?_⟩
    · intro i
      show (attSg x D rad).decs (attRd G x D rad seatT smp σ₀ (s, y)).1.2 _ i = _
      rw [e]
      exact hdecs i
    · rw [hext]
      exact ⟨hpin0, (att_says extNone Unit H ((), ()) (attMs x D rad seatT arr w, ())).1
        ((att_src_relR extNone Unit (attRd G x D rad seatT smp σ₀ (s, y))
          (attRw x D rad seatT arr w)).1 hRA).2⟩

end

#print axioms k3_att_goodIn_of

end VerifiableInference.OnPublicFiles
