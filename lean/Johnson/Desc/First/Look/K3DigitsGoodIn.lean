-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3DigitsGoodIn.lean: the lookup on the digits of a link's smallness test:
from the law on the kind's decide and the closed caller to the form that the rule of composition
asks of a block (Piece.GoodIn), BY THE RULE's OWN CARRIAGE (pieceGoodIn), WITHOUT A READER OF THE
STATEMENT BEHIND. Definitions, and one theorem at letters for the kind's decide and the record's two
readers. NO SOUNDNESS OF THE PROTOCOL IS CLAIMED: some premises are theorems of nobody yet.

THE END THEOREM k3_digits_goodIn_of: the piece p has GoodIn between
  on   DigOn: Own holds of the carried record · no oracle message of the link has a collision at its
       sample's seed (CfSig at all members, Johnson/Desc/Sound/MsgSig.lean: member by member: the
       record holds the sample, every leaf is shown, no OMsg.Clash at the seed) · the record's
       ledger has its sizes;
  RA   DigFront: the seats fit, and every oracle message of the link is shown and decodes, with its
       sample, to the witness's message (PinSig at all members), AND EVERY DIGIT, READ OFF THE
       WITNESS's MESSAGES AT ITS SEAT, IS A ROW OF ITS TABLE (DgP.DigIn at the caller's msg₀);
  on'  DigOn': Own, and CfSig, of the statement behind; a ledger F' and what was heard, g, stand in
       the record behind; F' HAS ITS SIZES (what the condition in front asks is handed on); AND g,
       F' STAND FOR SOME ROUNDS (K3Stands);
  RB   DigBehind: WHAT THE LATER BLOCKS OWE, SAID OUTRIGHT: PinSig still; and THE ROW OUT (K3Out,
       Johnson/Top/H/K3RowOut.lean) at the record's g and F': WHATEVER ROUNDS rs THE HEARD RECORD
       STANDS FOR (HeardIs g F' at the end values of rs), at THE SAME WITNESS's ENTRIES (the masks
       at mkOf, the planes' cells at plV, the layout's key vectors): the forms that the hearing
       left are worth 0 · planes-at-points · keys-at-points: together: every member of the
       library's list claimsOf is 0.
  err  the least written errors that bear the proved block's (bearT, K3CallerErr.lean). How small
       they are: K3CallerErrW.lean, K3CallerErr128.lean.

HOW IT GOES. The piece's yes gives decide's yes at the transcript's rounds without the sealed
digest, with the words below the prime, the work passed, and behind it the oracles that the stage
leaves (PieceHears, K3PieceSays.lean). decide's yes gives what was heard, and that it stands for the
transcript's own rounds (K3DecideHears' HeardIs). So the row out speaks at these rounds, and by
out_iff_items, at the closed caller's two equations, it is the proved block's out-claim at the
statement that the block puts out at the transcript's image. The proved block is knowledge sound
between its joints at the closed caller (lookupCRN_knowAt over dig_okR, dig_sel). The joint in front
unfolds (dig_src_relR). The words of trees sent in front of the stretch stay (pinStays).

Limits. fork, heard, decide are letters: nothing in this file sets them to a text that runs. WHO
GIVES RB: the four claims behind the digits' lookup are laid by the smallness test's run (eqKeys,
eqCounts), not by the lookup's own runs «planes» and «join»; THAT THESE CLAIMS, JUDGED BEHIND THE
RUNS, ARE WORTH THE LIST's MEMBERS AND ARE 0 IS OWED AT THE BATCHING's FRONT, BY NO THEOREM HERE;
under which premises they give RB: K3DigitsPay.lean. Own, smp, seatT, arr, G stay letters, with
laws: decide's yes turns neither smp nor Own, and is given only where the ledger stands at the
place's first slot; every tree of seatT is sent in front of the stretch. σ₀ is a sample that stands
where the record holds none: under DigOn it is never read. The extractor is the identity.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3RowOut
import Johnson.Desc.Sound.MsgSig
import Johnson.Desc.Sound.KnowInProofs
import Johnson.Desc.First.Look.K3PieceSays
import Johnson.Desc.First.Look.K3Caller
import Johnson.Desc.First.Look.K3CallerErr
import OnBytes.Tie.Pv.Lookup.Peel.FoPeelMapsT

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

section
variable {S Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  (x : Desc.First.Look.Place) (tl : HTailF2) (D : Desc.First.Look.Sent) (rad : OracleShape → ℕ)
  (seatT : Fin (digList x D rad).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : S → (i : Fin (digList x D rad).length) → Option ((digSg x D rad).om i).Smp)
  (fork : S → Option Fork) (heard : S → Option Forest.Heard) (Own : S → Prop)

local notation "𝐫" => noRider (digCaller x tl D rad extNone Unit)
local notation "𝐋" => DgP.digL5 Cb.Gl.E tl (enOf x.arrays) (mkOf x.arrays) x.F.next Unit

/-- The entries, read off the witness's messages by the caller's msg₀. -/
def digMu (w : Desc.Wit Cells Tok MsgT) : Option x.arrays.J → Cb.Gl.E :=
  digMsg x D rad (msgsOf D.codes (digList x D rad) seatT arr w)

/-- The reading of the places: a mask, a cell of the planes' matrix. -/
def digNu (w : Desc.Wit Cells Tok MsgT) (q : _root_.Fo.Pl) : Cb.Gl.E :=
  zext (digMu x D rad seatT arr w) (placeOf (mkOf x.arrays) (DgP.plV tl (enOf x.arrays)) q)

/-- **The condition in front.** -/
def DigOn (a : S × Fr.E.Str) : Prop :=
  Own a.1 ∧ CfSig G D.codes (digList x D rad) seatT smp (fun _ => True) a.1 (strsOf Fr a.2) ∧
    ∃ Fk, fork a.1 = some Fk ∧ OnBytes.PscRun.Sized Fk

/-- **The promise behind.** -/
def DigOn' (a : S × Fr.E.Str) : Prop :=
  Own a.1 ∧ CfSig G D.codes (digList x D rad) seatT smp (fun _ => True) a.1 (strsOf Fr a.2) ∧
    ∃ (g : Forest.Heard) (F' : Fork), fork a.1 = some F' ∧ heard a.1 = some g ∧
      OnBytes.PscRun.Sized F' ∧ K3Stands tl.f9 5 x.F.next Reading.gl g F'

/-- **The relation in front.** -/
def DigFront (a : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT) : Prop :=
  PinSig G D.codes (digList x D rad) seatT smp arr (fun _ => True) a.1 (strsOf Fr a.2) w ∧
    DgP.DigIn tl (enOf x.arrays) (digMu x D rad seatT arr w)

/-- **The relation behind: what the later blocks owe.** -/
def DigBehind (a : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT) : Prop :=
  PinSig G D.codes (digList x D rad) seatT smp arr (fun _ => True) a.1 (strsOf Fr a.2) w ∧
    ∃ (g : Forest.Heard) (F' : Fork), fork a.1 = some F' ∧ heard a.1 = some g ∧
      K3Out tl.f9 5 x.F.next (digNu x tl D rad seatT arr w)
        (forK Cb.Gl.E 𝐋 () (zext (digMu x D rad seatT arr w))) Reading.gl g F'

/-- The statement of the proved block that is read off the statement in front. -/
def digRd (σ₀ : (digSg x D rad).Smp) (a : S × Fr.E.Str) :
    (Unit × (digSg x D rad).Smp) × (extNone.prod (digSg x D rad).ext).Str :=
  (((), fun i => (smp a.1 i).getD (σ₀ i)),
    ((), wordsOf G D.codes (digList x D rad) seatT (strsOf Fr a.2)))

/-- The proved block's witness that is read off the rule's. -/
def digRw (w : Desc.Wit Cells Tok MsgT) : (digSg x D rad).Wit × Unit :=
  (fun i => (msgsOf D.codes (digList x D rad) seatT arr w i, fun _ => 0), ())

variable {x tl D rad}

/-- **THE END THEOREM, at letters for the kind's decide and the record's two readers.** -/
theorem k3_digits_goodIn_of {set : Params.Setting} {pp : ℕ}
    (p : Piece (ckP .two) Fr S Cl (Desc.Wit Cells Tok MsgT)) (H : DigOK set x tl D rad pp)
    (decide : S → List Fmt.RoundView → List (List (ℕ × List UInt64)) → Except String S)
    (hext : ∀ a τ w, p.ext a τ w = w)
    (hd : ∀ d ∈ p.ds, Fo.Peel.Plain (toRD d)) (hA : ∀ d ∈ p.ds, NoAns d.items)
    (he : p.ds.map (·.entry) = (Desc.First.Look.P.ofPlace set true x).rounds.map (·.entry))
    (hε : bearT p.ds _ ((kLookupCRN [𝐫]).ε 𝐫) = some p.err)
    (hCut : PieceHears p decide)
    (hD : K3DecideHears fork heard (Desc.First.Look.P.ofPlace set true x).calls
      (Desc.First.Look.P.ofPlace set true x).pub (Desc.First.Look.P.ofPlace set true x).lid decide)
    (hsmp : ∀ s rs cols s', decide s rs cols = .ok s' → smp s' = smp s)
    (hOwn : ∀ s rs cols s', decide s rs cols = .ok s' → Own s → Own s')
    (hnext : ∀ s rs cols s' Fk, decide s rs cols = .ok s' → fork s = some Fk →
      Fk.next = x.F.next)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (digSg x D rad).Smp) :
    p.GoodIn (DigOn G x D rad seatT smp fork Own) (DigOn' G x tl D rad seatT smp fork heard Own)
      (DigFront G x tl D rad seatT arr smp) (DigBehind G x tl D rad seatT arr smp fork heard) := by
  have hM := dig_meets H p.ds hd he
  have hr : 𝐫 ∈ (kLookupCRN [𝐫]).sizes := List.mem_singleton.2 rfl
  have hKA := lookupCRN_knowAt [𝐫] (dig_okR extNone Unit H) (dig_sel extNone Unit)
  refine pieceGoodIn S Cl _ _ Fr p _ _ _ _ ((kLookupCRN [𝐫]).toKind.block 𝐫).R.red
    (fun _ => lookCarryT tl.f9 𝐋 extNone p.ds hM.length_eq) ((kLookupCRN [𝐫]).ε 𝐫)
    (digRd G x D rad seatT smp σ₀) _ _ ((kLookupCRN [𝐫]).toKind.src 𝐫).on
    ((kLookupCRN [𝐫]).toKind.dst 𝐫).on _ _ ((kLookupCRN [𝐫]).toKind.src 𝐫).relR
    ((kLookupCRN [𝐫]).toKind.dst 𝐫).relR ((kLookupCRN [𝐫]).toKind.block 𝐫).ext
    (fun _ => lookCarryT_fits tl.f9 𝐋 extNone p.ds hM _ _ (bearT_bears _ _ _ _ hε)) ?_ ?_
    (knowInOfCarry _ _ _ _ _ _ _ _ _ _ _
      (fun a τ b ha hb =>
        BaseKind.onOut_toKind (BaseKind.onOut_of_knowAt hKA) 𝐫 hr a τ b hb ha)
      (BaseKind.know_toKind (BaseKind.know_of_knowAt hKA) 𝐫 hr))
  · -- the condition in front gives the proved block's
    rintro a ⟨-, hCf, -⟩
    obtain ⟨σ, hσ, hcf⟩ := cfSig_over G D.codes (digList x D rad) seatT smp a.1 _ hCf
    refine (dig_src_on extNone Unit (digRd G x D rad seatT smp σ₀ a)).2 ?_
    have e : (digRd G x D rad seatT smp σ₀ a).1.2 = σ := funext fun i => by
      show (smp a.1 i).getD (σ₀ i) = σ i
      rw [hσ i]
      rfl
    show (digSg x D rad).CF (digRd G x D rad seatT smp σ₀ a).1.2 _
    rw [e]
    exact hcf
  · -- the block's yes
    rintro ⟨s, y⟩ τ ⟨s', y'⟩ ⟨hOw, hCf, Fk, hFk, hSz⟩ ho
    obtain ⟨hp, e2, hw, cols, hdec⟩ := hCut _ τ _ ho
    have e2' : y' = behind (ckP .two) Fr p.base p.ds y τ := e2
    subst e2'
    have hCf1 : CfSig G D.codes (digList x D rad) seatT smp (fun _ => True) s (strsOf Fr y) := hCf
    have hdec1 : decide s ((rvT (ckP .two) p.ds τ).map Desc.noDigest) cols = .ok s' := hdec
    have hs' : smp s' = smp s := hsmp _ _ _ _ hdec1
    have hnx : Fk.next = x.F.next := hnext _ _ _ _ _ hdec1 hFk
    -- (L1) at the closed caller
    obtain ⟨X, hx, hiff⟩ := out_iff_items [𝐫] 𝐫 (dig_foOk H) 5 x.F.next (le_refl 5)
      (Nat.le_add_left 5 _) (mkOf x.arrays) (DgP.plV tl (enOf x.arrays))
      (fun t => dig_mkS extNone Unit t) (fun t k j _ => dig_bc extNone Unit t k j) p.ds hM hA
      (digRd G x D rad seatT smp σ₀ (s, y)) τ
    rw [mapsT_view] at hx
    -- (L2a): what was heard stands for the transcript's rounds
    obtain ⟨F1, F2, g, d1, d2, d3, -, hlaw⟩ := hD Cb.Gl.E Reading.gl 5 s s' _ cols hw hdec1
    obtain rfl : Fk = F1 := Option.some.inj (Eq.trans (Eq.symm hFk) d1)
    obtain ⟨hSh, hPad, hI⟩ := hlaw hSz
    have hg : g.shape = tl.f9 := by
      obtain ⟨h0, a0, -, a2⟩ := hSh
      obtain ⟨h1, b0, -, b2⟩ := shape_made H.shape
      have e : h0 = h1 := Except.ok.inj (a0.symm.trans b0)
      rw [a2, b2, e]
    rw [hg, hnx, viewRounds_noDigest] at hI
    refine ⟨lookImgT tl.f9 𝐋 extNone p.ds τ, _,
      lookCarryT_pass tl.f9 𝐋 extNone p.ds hM.length_eq τ hp, hx,
      fun _ => ⟨hOwn _ _ _ _ hdec1 hOw, fun i _ =>
        (pinStays (Cells := Unit) (Tok := Unit) G D.codes (digList x D rad) seatT smp arr
          (ckP .two) Fr p.base p.ds s' y τ ⟨(), (), fun _ _ _ _ => 0, fun _ _ _ _ _ => 0⟩ i
          (hseat i)).2.2
          (by
            have h0 := hCf1 i trivial
            unfold CfAt at h0 ⊢
            rw [hs']
            exact h0),
        g, F2, d2, d3, hPad.fit, _, hI⟩, ?_⟩
    rintro w ⟨⟨hSF, hPA⟩, g', F'', f1', f2', k1, k2, k3⟩
    obtain rfl : g = g' := Option.some.inj (Eq.trans (Eq.symm d3) f2')
    obtain rfl : F2 = F'' := Option.some.inj (Eq.trans (Eq.symm d2) f1')
    -- the pins, carried back to the statement in front
    have hpin0 : PinSig G D.codes (digList x D rad) seatT smp arr (fun _ => True) s (strsOf Fr y)
        w :=
      ⟨hSF, fun i _ => by
        have h0 := (pinStays G D.codes (digList x D rad) seatT smp arr (ckP .two) Fr p.base p.ds
          s' y τ w i (hseat i)).1.1 (hPA i trivial)
        unfold PinAt at h0 ⊢
        rw [hs'] at h0
        exact h0⟩
    obtain ⟨σ, hσ, hdecs⟩ := pinSig_over G D.codes (digList x D rad) seatT smp arr s _ w hpin0
    have e : (digRd G x D rad seatT smp σ₀ (s, y)).1.2 = σ := funext fun i => by
      show (smp s i).getD (σ₀ i) = σ i
      rw [hσ i]
      rfl
    have hout := (hiff (digMu x D rad seatT arr w)).2 ⟨k1 _ hI, k2 _ hI, k3 _ hI⟩
    refine ⟨digRw x D rad seatT arr w, ⟨?_, ⟨⟨trivial, hout⟩, fun e => Empty.elim e⟩⟩,
      fun hRA => ?_⟩
    · intro i
      show (digSg x D rad).decs (digRd G x D rad seatT smp σ₀ (s, y)).1.2 _ i = _
      rw [e]
      exact hdecs i
    · rw [hext]
      exact ⟨hpin0,
        ((dig_src_relR extNone Unit H.tail (digRd G x D rad seatT smp σ₀ (s, y))
          (digRw x D rad seatT arr w)).1 hRA).2⟩

end

/-- The kind whose joint behind says the number of rows has the errors of the kind without. -/
theorem lookupCRN_eps (L : List LookupCRCaller) : (kLookupCRN L).ε = (kLookupCR L).ε := rfl

#print axioms k3_digits_goodIn_of

end VerifiableInference.OnPublicFiles
