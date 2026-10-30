-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
ridesAtR_digits_full: no parameters Dm and no place are shown here at
which its premises hold together.
Johnson/Desc/Sound/MgAt/K3RidesDigFull.lean: the kind "lookup" (K3) AT THE COMPOSED MEANING mgAll:
WHAT RIDES PAST A SEATED LOOKUP ON THE DIGITS, SECOND FORM: THE PREMISE bSmall OF
ridesAtR_digits_tight (Johnson/Desc/Sound/MgAt/K3RidesDigTight.lean) IS PAID: a sentence "forms"
with a run that is read ahead ("small": its text is formsQA) goes back over K3Pass too: by the
library's own rider formsQA_back (Johnson/Desc/Sound/FormsAhead.lean): between the two states
nothing is sent, so the data, with what is ahead read by the plan, are the same. Statements and
proofs. Ties of texts: no error term. NO SOUNDNESS IS CLAIMED.

SO hFwd IS ASKED, AND SPENT, AT EVERY RUN OF EVERY SENTENCE forms THAT RIDES: also at
"K8.equations".

OBJECT: Sound.formsQA | dataQA; the composed meaning's field forms; RidesAtR; DigOwedR.rides.
Used by K3RidesDigStep.lean (Johnson/Desc/Sound/MgAt/), which calls mgAll_forms_back_any. No other
  file in this library calls ridesAtR_digits_full.
LETTERS: Dm, Mg, seats; Rch, k, l, q, b', a.
IMPORTS:
  Johnson/Desc/Sound/MgAt/K3RidesDigTight.lean;
  Johnson/Desc/Sound/FormsAhead.lean.
  Compiled with the whole library.

Main names:
  `dataQA_same`: the data with what is ahead read the link's context, the statement and the book
    alone.
  `k3_formsQA_back`: THE SISTER OF k3_forms_back AT formsQA.
  `mgAll_formsInA_at`: what the tied public test says at a run that is read ahead.
  `mgAll_forms_back_any`: the composed sentence goes back, whichever of its runs are read ahead.
  `ridesAtR_digits_full`: THE END; and an example in which Lean lays it into DigOwedR.rides.

WHAT IS LEFT: the place · q.back = [] · hRel · hj · hReq · hHead · hLed · hFwd · hWt.
Limits. At the digits alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3RidesDigTight
import Johnson.Desc.Sound.FormsAhead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice Fo.Peel
open _root_.Run (ckP)
open VerifiableInference.Desc.First (ModelPart Item Pub Meaning Numbers start openSets flatPlacesOf)
open VerifiableInference.OnPublicFiles (SameBut relOf RidesAtR digitsPartK3 DigOwedR K3Pass
        k3_forms_back)
open VerifiableInference.Desc.First.Look (digList digSg)
open VerifiableInference.Desc.K9 (segAt? Readers formsInA aheadIn aheadOf)
open VerifiableInference.Reads.Pass (Fwd)
open Johnson.Desc.First.Walk.Tied (Stays)

local notation "PS" => flatPlacesOf linksFull true

/-- The data, with what is ahead read by the plan, read the link's context, the statement and the
book alone. -/
theorem dataQA_same (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ)) {a b : K9.Part}
    (hL : b.L = a.L) (hst : b.d.st = a.d.st) (hbk : b.d.book = a.d.book) (rd : ℕ × ℕ → MsgQ) :
    dataQA sent own b rd = dataQA sent own a rd := by
  unfold dataQA dataQ aheadIn aheadOf
  rw [hL, hst, hbk]

/-- **THE SENTENCE WITH WHAT IS AHEAD GOES BACK OVER K3Pass.** -/
theorem k3_formsQA_back {s s' : First.S} {F G : OnBytes.Model.Fork} (Pp : K3Pass s s' F G)
    (Rd : Readers) (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String)
    (rd : ℕ × ℕ → MsgQ) (hf : Fwd Rd piece run s s')
    (hin : formsInA Rd sent own piece run s = true)
    (h : formsQA sent own Rd piece run s' rd) : formsQA sent own Rd piece run s rd := by
  cases ha : segAt? s with
  | none =>
    unfold formsInA at hin
    rw [ha] at hin
    cases hin
  | some a =>
    obtain ⟨b, hb, eL, -, -, est, ebk⟩ := Pp.part ha
    cases hR : Rd.forms piece run s with
    | none =>
      unfold formsInA at hin
      rw [ha, hR] at hin
      cases hin
    | some R₀ =>
      have hl : Rd.forms piece run s' = Rd.forms piece run s := by rw [hR, hf R₀ hR]
      have eD := dataQA_same sent own eL est ebk rd
      exact formsQA_back sent own Rd piece run s s' a b rd ha hb hl hin
        (Pp.rides own ha hb).arrays (Pp.rides own ha hb).filled
        (fun _ _ _ _ _ _ _ _ => by rw [eD]) (fun _ _ _ _ _ _ => by rw [eD]) h

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
variable (Dm : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- What the tied test says at the composed meaning, at a run that is read ahead. -/
theorem mgAll_formsInA_at {l kk : ℕ} {r : String} {a : P × First.S}
    (h : (mgAll Dm Mg).pub (.formsIn l kk r) a = true) {p : ℕ × String}
    (hp : p ∈ Dm.runs l kk r) (hah : Dm.ah p.1 p.2 = true) :
    formsInA (Dm.Rd l) (Dm.N.sent l) (Dm.N.group l) p.1 p.2 a.2 = true := by
  rw [mgAll_pub, First.pubAll_formsIn] at h
  have h1 := List.all_eq_true.1 h p hp
  have e : Dm.pubD.ah p.1 p.2 = true := hah
  rw [e] at h1
  exact h1

/-- **THE COMPOSED SENTENCE "forms" GOES BACK OVER K3Pass**, whichever of its runs are read
ahead. -/
theorem mgAll_forms_back_any {l kk : ℕ} {r : String} {s s' : First.S}
    {F G : OnBytes.Model.Fork} (Pp : K3Pass s s' F G) (z : P) (y y' : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT)
    (hFwd : ∀ p ∈ Dm.runs l kk r, Fwd (Dm.Rd l) p.1 p.2 s s')
    (hin : (mgAll Dm Mg).pub (.formsIn l kk r) (z, s) = true)
    (hWt : r = "weights" → Dm.wt l (z, s') y' w → Dm.wt l (z, s) y w)
    (h : (mgAll Dm Mg).forms l kk r (z, s') y' w) : (mgAll Dm Mg).forms l kk r (z, s) y w := by
  rw [mgAll_forms] at h ⊢
  refine ⟨fun p hp => ?_, fun e => hWt e (h.2 e)⟩
  have h1 := h.1 p hp
  by_cases e : Dm.ah p.1 p.2 = true
  · rw [if_pos e] at h1 ⊢
    exact k3_formsQA_back Pp (Dm.Rd l) (Dm.N.sent l) (Dm.N.group l) p.1 p.2 _ (hFwd p hp)
      (mgAll_formsInA_at Dm Mg hin hp e) h1
  · rw [if_neg e] at h1 ⊢
    have e' : Dm.ah p.1 p.2 = false := by
      cases h0 : Dm.ah p.1 p.2 with
      | false => rfl
      | true => exact absurd h0 e
    exact k3_forms_back Pp (Dm.Rd l) (Dm.N.group l) p.1 p.2 _ (hFwd p hp)
      (mgAll_formsIn_at Dm Mg hin hp e') h1

/-- **WHAT RIDES PAST A LOOKUP ON THE DIGITS: bSmall PAID.** -/
theorem ridesAtR_digits_full {Cl : Type} {Fr : Frame} (seats : List (ℕ × ℕ))
    (es : Dm.smp = smpNamed Dm.cs seats) (hD : Dm.digitsPart = digitsPartK3 X Dm.sent Dm.l3)
    (hd : ∀ c (y y' : P × First.S), y'.1 = y.1 → Dm.decT c y' = Dm.decT c y)
    (Rch : ℕ → (P × First.S) × Fr.E.Str → Prop) (k l : ℕ)
    (q : Piece (ckP .two) Fr (P × First.S) Cl (Wit (CellsQ rows cols) Tok MsgT))
    (b' : Block First.S Cl) {a : Place} (ha : PS[k]? = some a) (hK : a.kind = .K3)
    (hp : 7 ≤ a.piece) (hl : a.link = some l) (hback : q.back = [])
    (hRel : ∀ B', SeatOf b' B' → ∀ u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr First.S Cl (Wit (CellsQ rows cols) Tok MsgT)).ior.red.out u τ =
          some v → PassRel u.1 v.1)
    (hj : Dm.N.index.1 < q.base)
    (hReq : ∀ (z : P) s s', SameBut s s' → Dm.H.req (z, s) = Dm.H.req (z, s'))
    (hHead : ∀ p i, GoesBack (relOf SameBut q.base) (Dm.headPart p i))
    (hLed : ∀ (z : P) (u : First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      ¬ u.1.failed ≠ none → ∃ F, u.1.fork? = some F ∧ OnBytes.PscRun.Sized F)
    (hFwd : ∀ kk r,
      openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) k
        (.forms l kk r) →
      ¬ insQ linksFull PS k (.forms l kk r) →
      ∀ (z : P) (u v : First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      ¬ u.1.failed ≠ none → onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      PassRel u.1 v.1 →
      ∀ p ∈ Dm.runs l kk r, Fwd (Dm.Rd l) p.1 p.2 u.1 v.1)
    (hWt : ∀ kk,
      openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) k
        (.forms l kk "weights") →
      ¬ insQ linksFull PS k (.forms l kk "weights") →
      ∀ (z : P) (u v : First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      ¬ u.1.failed ≠ none → onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      PassRel u.1 v.1 →
      ∀ w, Dm.wt l (z, v.1) (strsOf Fr v.2) w → Dm.wt l (z, u.1) (strsOf Fr u.2) w) :
    RidesAtR Dm.N (mgAll Dm Mg) Rch k q b' := by
  have hk : k ≤ (flatPlacesOf linksFull true).length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.1 ha).1
  refine ridesAtR_digits_tight Dm Mg seats es hD hd Rch k l q b' ha hK hp hl hback hRel hj hReq
    hHead hLed ?_ (fun kk r ho hn _ => hFwd kk r ho hn) hWt
  intro kk r ho hn _ z u v hu hr hm hv hR _ w h
  obtain ⟨F, hF, hSz⟩ := hLed z u hu hr hm
  obtain ⟨G, Pp⟩ := hR.2.2 F hF hSz
  have hu0 : u.1.failed = none := Classical.not_not.1 hm
  exact mgAll_forms_back_any Dm Mg Pp z _ _ w (hFwd kk r ho hn z u v hu hr hm hv hR)
    (onQ_tied_formsIn hu hu0 (open_of_rider hk ho))
    (fun e => by
      subst e
      exact hWt kk ho hn z u v hu hr hm hv hR w) h

/-- **Lean holds the theorem against the field**: it is laid into a given DigOwedR, at the ledger's
own letters, in the place of that structure's own rides. (The example proves nothing new: its end is
its premise T's.) -/
example {Cl : Type} {Fr : Frame} (seats : List (ℕ × ℕ))
    (es : Dm.smp = smpNamed Dm.cs seats) (hD : Dm.digitsPart = digitsPartK3 X Dm.sent Dm.l3)
    (hd : ∀ c (y y' : P × First.S), y'.1 = y.1 → Dm.decT c y' = Dm.decT c y)
    (Rch : ℕ → (P × First.S) × Fr.E.Str → Prop) (k l : ℕ)
    (q : Piece (ckP .two) Fr (P × First.S) Cl (Wit (CellsQ rows cols) Tok MsgT))
    (b' : Block First.S Cl) {a : Place} (ha : PS[k]? = some a) (hK : a.kind = .K3)
    (hp : 7 ≤ a.piece) (hl : a.link = some l) (hback : q.back = [])
    (hRel : ∀ B', SeatOf b' B' → ∀ u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr First.S Cl (Wit (CellsQ rows cols) Tok MsgT)).ior.red.out u τ =
          some v → PassRel u.1 v.1)
    (hj : Dm.N.index.1 < q.base)
    (hReq : ∀ (z : P) s s', SameBut s s' → Dm.H.req (z, s) = Dm.H.req (z, s'))
    (hHead : ∀ p i, GoesBack (relOf SameBut q.base) (Dm.headPart p i))
    (hLed : ∀ (z : P) (u : First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      ¬ u.1.failed ≠ none → ∃ F, u.1.fork? = some F ∧ OnBytes.PscRun.Sized F)
    (hFwd : ∀ kk r,
      openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) k
        (.forms l kk r) →
      ¬ insQ linksFull PS k (.forms l kk r) →
      ∀ (z : P) (u v : First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      ¬ u.1.failed ≠ none → onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      PassRel u.1 v.1 →
      ∀ p ∈ Dm.runs l kk r, Fwd (Dm.Rd l) p.1 p.2 u.1 v.1)
    (hWt : ∀ kk,
      openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) k
        (.forms l kk "weights") →
      ¬ insQ linksFull PS k (.forms l kk "weights") →
      ∀ (z : P) (u v : First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      ¬ u.1.failed ≠ none → onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      PassRel u.1 v.1 →
      ∀ w, Dm.wt l (z, v.1) (strsOf Fr v.2) w → Dm.wt l (z, u.1) (strsOf Fr u.2) w)
    (claim : OnBytes.Model.Aff → Cl) (a' : Place) (sub : ModelPart) (x : First.Look.Place)
    (tl : OnBytes.Model.HTailF2)
    (smp : First.S → (i : Fin (digList x Dm.sent Dm.l3.rad).length) →
      Option ((digSg x Dm.sent Dm.l3.rad).om i).Smp)
    (told : List (List Oracle))
    (T : DigOwedR Dm.G X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) Rch claim Dm.ms a a' k l sub x tl smp q
      b' told) :
    DigOwedR Dm.G X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) Rch claim Dm.ms a a' k l sub x tl smp q b'
      told :=
  { T with
    rides := ridesAtR_digits_full Dm Mg seats es hD hd Rch k l q b' ha hK hp hl hback hRel hj
      hReq hHead hLed hFwd hWt }

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.dataQA_same
#print axioms VerifiableInference.Desc.Sound.k3_formsQA_back
#print axioms VerifiableInference.Desc.Sound.mgAll_formsInA_at
#print axioms VerifiableInference.Desc.Sound.mgAll_forms_back_any
#print axioms VerifiableInference.Desc.Sound.ridesAtR_digits_full
