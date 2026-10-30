-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3LayGoodIn.lean: THE CLOSING FILE OF A THIRD CHAIN: the lookup on the CALLS
of a LAYERS' link, WITH ITS RIDER: from the law on the kind's decide and the closed caller
(Johnson/Desc/First/Look/K3CallerLay.lean: layRider) to the form that the rule of composition asks
of a block (Piece.GoodIn): an instance of k3_goodIn_calls
(Johnson/Desc/First/Look/K3GoodInCalls.lean). Definitions, and one theorem with two corollaries. NO
SOUNDNESS OF THE PROTOCOL IS CLAIMED: the premises that are not theorems are premises.

WHAT DIFFERS FROM ATTENTION (Johnson/Desc/First/Look/K3AttGoodIn.lean). THE KEYS READ THE WEIGHTS:
the caller's signature has ONE MEMBER MORE than the first chain's messages: the stored table's
oracle message oW. So the statement and the witness have three readers more, ALL LETTERS:
  smpW : the record's sample of the stored table · strW : the stored table's word among the
  statement's oracles · msgW : the stored table's message, off the witness.
LayCond asks, beside attention's two clauses, that the record holds a sample of the stored table at
whose seed its word has no collision; LayPin, beside PinSig, that the word decodes, with that
sample, to msgW w. Two laws on the letters: a yes of decide does not turn smpW (hsmpW); the stretch
does not turn strW (hstrW). WHO FILLS THEM is not said here: it is owed with the laws on the stored
table and on the key file (the like is said of the caller's own letters in
K3CallerLay.lean).

THE END THEOREM k3_lay_goodIn_any: at a piece p that holds "below b", b any block whose decide says
yes only where K3.block's does at the calls' seat and the place x: p has GoodIn between
  on   LayOn: LayCond; the record's ledger is open and has its sizes;
  RA   LayFront: LayPin, AND (LaySays) EVERY ENTRY OF THE EIGHT KEY VECTORS, computed from the cells
       behind the committed symbols AND FROM THE STORED TABLE's MESSAGE, IS A ROW OF ITS TABLE, AND
       IDENTITY j10 IS 0 AT EVERY VALID INDEX (a router's selector has entries that sum to 1);
  on'  LayOn': LayCond behind; a ledger with its sizes and what was heard stand in the record, and
       stand for some rounds;
  RB   LayBehind: LayPin still; THE ROW OUT (K3Out); AND ITS FOURTH ITEM (K3OutRider) at the
       library's crHot.
  err  the least written errors that bear the proved block's; k3_lay_err: each ≤ 2^-157.

THE RIDER IS IN THE CHAIN ON THE PROVED BLOCK's SIDE, AND NOWHERE ON THE TEXT's: "guests" is a
letter: the theorem holds at every list, and none of the four relations names it. The block's test
on the plan (planOk) does read the list.

Limits. Those of K3GoodInCaller.lean, K3AttGoodIn.lean and K3CallerLay.lean: IT SPEAKS OF THE FULL
SIZE ALONE (LayOK.sizes | tabs stand at the library's reference sizes): by a run, no theorem,
its test of LayOK, run on the public files of the two shipped example sets, says yes at the twelve
layers' links of the full-size set and no at the small set's two. oW, wOf, nr, nc are letters. THE
PLANES' CELLS AND THE MASK ENTRIES ARE READ AS 0 WHERE THEY LIE OUTSIDE THE LIST's MATRIX OR THE
MASK ROW: the public tests that shut this (Johnson/Desc/First/Look/K3CallerCellsIn.lean: planesAtB,
masksAtB) are no premise here: they stand beside. WHO GIVES RB is owed, as at attention.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3GoodInCalls
import Johnson.Desc.First.Look.K3CallerLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Cb.Fo.Pin
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open Inst.Model.All (DF)
open Inst.Model.FFSeg (Idn idnVal)

section
variable {S Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  (x : Desc.First.Look.Place) (q : LayPub) (tl : HTailF2) (D : Desc.First.Look.Sent)
  (rad : OracleShape → ℕ) (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : S → (i : Fin (sigListCalls D rad x.link).length) → Option ((attSg x D rad).om i).Smp)
  (smpW : S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg)
  (fork : S → Option Fork) (heard : S → Option Forest.Heard) (Own : S → Prop)

local notation "𝐫" => layRider x q tl D rad oW wOf nr nc extNone Unit
local notation "𝐥" => sigListCalls D rad x.link

/-- The proved block's witness that is read off the rule's: the stored table's message, then the
first chain's. -/
def layWt (w : Desc.Wit Cells Tok MsgT) : (laySg x D rad oW).Wit × Unit :=
  ((attSg x D rad).cons (T := fun o => o.Wit) oW (msgW w, fun _ => 0)
    (fun i => (msgsOf D.codes 𝐥 seatT arr w i, fun _ => 0)), ())

/-- The witness's messages, as the signature's tuple. -/
def layMs (w : Desc.Wit Cells Tok MsgT) : (laySg x D rad oW).Msg :=
  (laySg x D rad oW).msgs (layWt x D rad oW seatT arr msgW w).1

theorem layMs_none (w : Desc.Wit Cells Tok MsgT) :
    layMs x D rad oW seatT arr msgW w none = msgW w := rfl

theorem layMs_some (w : Desc.Wit Cells Tok MsgT) (i : Fin 𝐥.length) :
    layMs x D rad oW seatT arr msgW w (some i) = msgsOf D.codes 𝐥 seatT arr w i := rfl

/-- The samples and the words of the caller's signature, read off the statement. -/
def laySm (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp) (a : S × Fr.E.Str) :
    (laySg x D rad oW).Smp :=
  (attSg x D rad).cons (T := fun o => o.Smp) oW ((smpW a.1).getD σW₀)
    (fun i => (smp a.1 i).getD (σ₀ i))

def layWd (a : S × Fr.E.Str) : (laySg x D rad oW).ext.Str :=
  (attSg x D rad).cons (T := fun o => o.Str) oW (strW a.2)
    (wordsOf G D.codes 𝐥 seatT (strsOf Fr a.2))

/-- **What is asked of a statement beside the ledger.** -/
def LayCond (a : S × Fr.E.Str) : Prop :=
  Own a.1 ∧ CfSig G D.codes 𝐥 seatT smp (fun _ => True) a.1 (strsOf Fr a.2) ∧
    ∃ σW, smpW a.1 = some σW ∧ ¬ oW.Clash (strW a.2) σW.1

/-- **What ties a statement to a witness.** -/
def LayPin (a : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT) : Prop :=
  PinSig G D.codes 𝐥 seatT smp arr (fun _ => True) a.1 (strsOf Fr a.2) w ∧
    ∃ σW, smpW a.1 = some σW ∧ oW.dec (strW a.2) σW = some (msgW w)

/-- **What the joint in front says of a tuple of messages** (lay_says' right side). -/
def LaySays (m : (laySg x D rad oW).Msg) : Prop :=
  (∀ k < x.fs.NC, ∀ b < 2 ^ Cb.LdLkp.Port.nOf x.fs k, ∃ u < 2 ^ Cb.LdLkp.Port.kOf x.fs k,
    (layLay q x.fs x.lm x.F.next x.ns tl nr nc).K () (msgLay x tl D rad oW wOf nr nc m) k b =
      ((FoNums.tauN x.fs k u : ℕ) : Cb.Gl.E)) ∧
  ∀ (emb : ℕ → ℕ → Cb.Gl.E) (tok : ℕ → ℕ) (first : Bool) (l i : ℕ),
    (Idn.j10 l i).Valid DF first →
      idnVal (scl := Road.sclOf q.h q.sc q.g 4) DF (layCells x q tl D rad oW wOf nr nc m) emb
        tok (.j10 l i) = 0

/-- The entries, read off the witness's messages by the caller's msg₀. -/
def layMu (w : Desc.Wit Cells Tok MsgT) : JLay x.ns tl nr nc → Cb.Gl.E :=
  msgLay x tl D rad oW wOf nr nc (layMs x D rad oW seatT arr msgW w)

/-- The reading of the places: a mask, a cell of the planes' matrix. -/
def layNu (w : Desc.Wit Cells Tok MsgT) (pq : _root_.Fo.Pl) : Cb.Gl.E :=
  zext (layMu x tl D rad oW wOf nr nc seatT arr msgW w)
    (placeOf (lyMask x.ns tl nr nc) (lyCell x.ns tl nr nc (Model.Layer.matIx q.y).iB) pq)

/-- **The condition in front.** -/
def LayOn (a : S × Fr.E.Str) : Prop :=
  LayCond G x D rad oW seatT smp smpW strW Own a ∧
    ∃ Fk, fork a.1 = some Fk ∧ OnBytes.PscRun.Sized Fk

/-- **The promise behind.** -/
def LayOn' (a : S × Fr.E.Str) : Prop :=
  LayCond G x D rad oW seatT smp smpW strW Own a ∧
    ∃ (g : Forest.Heard) (F' : Fork), fork a.1 = some F' ∧ heard a.1 = some g ∧
      OnBytes.PscRun.Sized F' ∧ K3Stands x.fs x.lm x.F.next Reading.gl g F'

/-- **The relation in front.** -/
def LayFront (a : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT) : Prop :=
  LayPin G x D rad oW seatT arr smp smpW strW msgW a w ∧
    LaySays x q tl D rad oW wOf nr nc (layMs x D rad oW seatT arr msgW w)

/-- **The relation behind: what the later blocks owe.** -/
def LayBehind (a : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT) : Prop :=
  LayPin G x D rad oW seatT arr smp smpW strW msgW a w ∧
    ∃ (g : Forest.Heard) (F' : Fork), fork a.1 = some F' ∧ heard a.1 = some g ∧
      K3Out x.fs x.lm x.F.next (layNu x q tl D rad oW wOf nr nc seatT arr msgW w)
        (forK Cb.Gl.E (layLay q x.fs x.lm x.F.next x.ns tl nr nc) ()
          (zext (layMu x tl D rad oW wOf nr nc seatT arr msgW w))) Reading.gl g F' ∧
      K3OutRider 𝐫 x.lm x.F.next () (layMs x D rad oW seatT arr msgW w) g F'

end

/-! ### the four laws on the signature with the stored table: for every caller over laySg -/

section
variable {S Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {x : Desc.First.Look.Place} {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ}
  {oW : Cb.OMsg Cb.Gl.E}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : S → (i : Fin (sigListCalls D rad x.link).length) → Option ((attSg x D rad).om i).Smp)
  (smpW : S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg) (Own : S → Prop)

local notation "𝐥" => sigListCalls D rad x.link

/-- **LayCond gives: no member of the signature has a collision at its sample's seed.** -/
theorem layCond_cf (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp) (a : S × Fr.E.Str)
    (h : LayCond G x D rad oW seatT smp smpW strW Own a) :
    (laySg x D rad oW).CF (laySm x D rad oW smp smpW σ₀ σW₀ a)
      (layWd G x D rad oW seatT strW a) := by
  obtain ⟨-, hCf, σW, hW, hcl⟩ := h
  obtain ⟨σ, hσ, hcf⟩ := cfSig_over G D.codes 𝐥 seatT smp a.1 _ hCf
  rintro (_ | i)
  · show ¬ oW.Clash (strW a.2) ((smpW a.1).getD σW₀).1
    rw [hW]
    exact hcl
  · show ¬ ((attSg x D rad).om i).Clash
      (wordsOf G D.codes 𝐥 seatT (strsOf Fr a.2) i) ((smp a.1 i).getD (σ₀ i)).1
    rw [hσ i]
    exact hcf i

/-- **LayPin gives: every member decodes, with its sample, to the witness's message.** -/
theorem layPin_decs (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp) (a : S × Fr.E.Str)
    (w : Desc.Wit Cells Tok MsgT)
    (h : LayPin G x D rad oW seatT arr smp smpW strW msgW a w) (i : (laySg x D rad oW).O) :
    (laySg x D rad oW).decs (laySm x D rad oW smp smpW σ₀ σW₀ a)
      (layWd G x D rad oW seatT strW a) i =
        some ((layWt x D rad oW seatT arr msgW w).1 i).1 := by
  obtain ⟨hP, σW, hW, hdc⟩ := h
  obtain ⟨σ, hσ, hdecs⟩ := pinSig_over G D.codes 𝐥 seatT smp arr a.1 _ w hP
  rcases i with _ | i
  · show oW.dec (strW a.2) ((smpW a.1).getD σW₀) = some (msgW w)
    rw [hW]
    exact hdc
  · show ((attSg x D rad).om i).dec (wordsOf G D.codes 𝐥 seatT (strsOf Fr a.2) i)
      ((smp a.1 i).getD (σ₀ i)) = some (msgsOf D.codes 𝐥 seatT arr w i)
    rw [hσ i]
    exact hdecs i

variable (base : ℕ) (ds : List RDT) (hseat : ∀ i, (seatT i).1 < base) (s s' : S) (y : Fr.E.Str)
  (τ : Tr (uLT (ckP .two) ds)) (hs' : smp s' = smp s) (hsW : smpW s' = smpW s)
  (hstr : strW (behind (ckP .two) Fr base ds y τ) = strW y)
include hseat hs' hsW hstr

/-- **LayCond stays over the stretch**, where Own stays and the three readers have not turned. -/
theorem layCond_stays (hO : Own s → Own s')
    (h : LayCond G x D rad oW seatT smp smpW strW Own (s, y)) :
    LayCond G x D rad oW seatT smp smpW strW Own (s', behind (ckP .two) Fr base ds y τ) := by
  obtain ⟨h1, hCf, σW, hW, hcl⟩ := h
  refine ⟨hO h1, cfSig_stays G D 𝐥 seatT smp base ds hseat s s' y τ hs' hCf, σW,
    hsW.trans hW, ?_⟩
  show ¬ oW.Clash (strW (behind (ckP .two) Fr base ds y τ)) σW.1
  rw [hstr]
  exact hcl

/-- **LayPin goes back over the stretch.** -/
theorem layPin_back (w : Desc.Wit Cells Tok MsgT)
    (h : LayPin G x D rad oW seatT arr smp smpW strW msgW
      (s', behind (ckP .two) Fr base ds y τ) w) :
    LayPin G x D rad oW seatT arr smp smpW strW msgW (s, y) w := by
  obtain ⟨hP, σW, hW, hdc⟩ := h
  refine ⟨pinSig_back G D 𝐥 seatT arr smp base ds hseat s s' y τ hs' w hP, σW,
    hsW.symm.trans hW, ?_⟩
  have h1 : oW.dec (strW (behind (ckP .two) Fr base ds y τ)) σW = some (msgW w) := hdc
  rw [hstr] at h1
  exact h1

end

section
variable {Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {x : Desc.First.Look.Place} {q : LayPub} {tl : HTailF2} {D : Desc.First.Look.Sent}
  {rad : OracleShape → ℕ} {oW : Cb.OMsg Cb.Gl.E} {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : ℕ}
  {set : Params.Setting}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  (smpW : Desc.First.S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg)

local notation "𝐫" => layRider x q tl D rad oW wOf nr nc extNone Unit
local notation "𝐥" => sigListCalls D rad x.link

/-- **THE END THEOREM OF THE CALLS' CHAIN AT A LAYERS' LINK, at any block whose decide says yes only
where K3.block's does.** -/
theorem k3_lay_goodIn_any (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (b : Desc.Block Desc.First.S Cl)
    (hyes : ∀ s rs cols s', b.decide s rs cols = .ok s' →
      (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
        (Desc.First.Look.P.ofPlace set false x) guests).decide s rs cols = .ok s')
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) (hb : p.b = below b)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w) (H : LayOK set x)
    (hp : (Forest.planeCols x.fs x.lm).toBool = true)
    (hr : (Desc.First.Look.P.ofPlace set false x).entries.isSome = true)
    (hR : List.Forall₂ SameAs p.ds (Desc.First.Look.P.ofPlace set false x).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [𝐫]).ε 𝐫) = some p.err)
    (hsmp : ∀ s rs cols s', b.decide s rs cols = .ok s' → smp s' = smp s)
    (hsmpW : ∀ s rs cols s', b.decide s rs cols = .ok s' → smpW s' = smpW s)
    (hstrW : ∀ y (τ : Tr (uLT (ckP .two) p.ds)),
      strW (behind (ckP .two) Fr p.base p.ds y τ) = strW y)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp) :
    p.GoodIn
      (LayOn G x D rad oW seatT smp smpW strW (Desc.K3.seatCalls claim).fork (OwnIs D x.link))
      (LayOn' G x D rad oW seatT smp smpW strW (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link))
      (LayFront G x q tl D rad oW wOf nr nc seatT arr smp smpW strW msgW)
      (LayBehind G x q tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard) :=
  k3_goodIn_calls (r := 𝐫) (mk := lyMask x.ns tl nr nc)
    (pl := lyCell x.ns tl nr nc (Model.Layer.matIx q.y).iB) (st := fun _ => ()) (y₀ := ())
    (sm := laySm x D rad oW smp smpW σ₀ σW₀) (wd := layWd G x D rad oW seatT strW)
    (wt := layWt x D rad oW seatT arr msgW)
    (Cond := LayCond G x D rad oW seatT smp smpW strW (OwnIs D x.link))
    (Pin := LayPin G x D rad oW seatT arr smp smpW strW msgW)
    (Says := fun _ w => LaySays x q tl D rad oW wOf nr nc (layMs x D rad oW seatT arr msgW w))
    claim piece laid before guests b hyes p hb hback hext (lay_sel extNone Unit H) H.shape
    (by
      show 1 < x.fs.NC
      rw [H.eight]
      decide)
    hp (fun _ => rfl) (fun _ _ _ _ => rfl) hr hR hε (fun _ _ _ _ _ _ _ => rfl)
    (fun a h => ⟨layCond_cf G seatT smp smpW strW (OwnIs D x.link) σ₀ σW₀ a h, trivial⟩)
    (fun s y τ rs cols s' hd h =>
      layCond_stays G seatT smp smpW strW (OwnIs D x.link) p.base p.ds hseat s s' y τ
        (hsmp s rs cols s' hd) (hsmpW s rs cols s' hd) (hstrW y τ)
        (ownIs_calls claim piece laid before _ guests D x.link s s' rs cols
          (hyes s rs cols s' hd)) h)
    (fun s y τ rs cols s' w hd h =>
      layPin_back G seatT arr smp smpW strW msgW p.base p.ds hseat s s' y τ
        (hsmp s rs cols s' hd) (hsmpW s rs cols s' hd) (hstrW y τ) w h)
    (fun a w h i => layPin_decs G seatT arr smp smpW strW msgW σ₀ σW₀ a w h i)
    (fun _ _ ho ht => ⟨⟨trivial, ho⟩, ht⟩)
    (fun _ w h => (lay_says extNone Unit ((), ())
      (layMs x D rad oW seatT arr msgW w, ())).1 h)

/-- **At K3.block's own text.** -/
theorem k3_lay_goodIn (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    (hb : p.b = below (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) guests))
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w) (H : LayOK set x)
    (hp : (Forest.planeCols x.fs x.lm).toBool = true)
    (hr : (Desc.First.Look.P.ofPlace set false x).entries.isSome = true)
    (hR : List.Forall₂ SameAs p.ds (Desc.First.Look.P.ofPlace set false x).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [𝐫]).ε 𝐫) = some p.err)
    (hsmp : ∀ s rs cols s', (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) guests).decide s rs cols = .ok s' → smp s' = smp s)
    (hsmpW : ∀ s rs cols s', (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) guests).decide s rs cols = .ok s' →
        smpW s' = smpW s)
    (hstrW : ∀ y (τ : Tr (uLT (ckP .two) p.ds)),
      strW (behind (ckP .two) Fr p.base p.ds y τ) = strW y)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp) :
    p.GoodIn
      (LayOn G x D rad oW seatT smp smpW strW (Desc.K3.seatCalls claim).fork (OwnIs D x.link))
      (LayOn' G x D rad oW seatT smp smpW strW (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link))
      (LayFront G x q tl D rad oW wOf nr nc seatT arr smp smpW strW msgW)
      (LayBehind G x q tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard) :=
  k3_lay_goodIn_any G seatT arr smp smpW strW msgW claim piece laid before guests _
    (fun _ _ _ _ h => h) p hb hback hext H hp hr hR hε hsmp hsmpW hstrW hseat σ₀ σW₀

/-- **The end theorem's errors, as a number.** -/
theorem k3_lay_err (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    (H : LayOK set x)
    (hr : (Desc.First.Look.P.ofPlace set false x).entries.isSome = true)
    (hR : List.Forall₂ SameAs p.ds (Desc.First.Look.P.ofPlace set false x).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [𝐫]).ε 𝐫) = some p.err) :
    Iop.Err.Below p.err ((2 : ENNReal)⁻¹ ^ 157) :=
  k3_calls_err (r := 𝐫) p H.shape
    (by
      show 1 < x.fs.NC
      rw [H.eight]
      decide)
    hr hR hε

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.layCond_cf
#print axioms VerifiableInference.OnPublicFiles.layPin_decs
#print axioms VerifiableInference.OnPublicFiles.layCond_stays
#print axioms VerifiableInference.OnPublicFiles.layPin_back
#print axioms VerifiableInference.OnPublicFiles.k3_lay_goodIn_any
#print axioms VerifiableInference.OnPublicFiles.k3_lay_goodIn
#print axioms VerifiableInference.OnPublicFiles.k3_lay_err
