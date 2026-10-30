-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
ridesAtR_digits_tight: no parameters Dm and no place are shown here at
which its premises hold together.
Johnson/Desc/Sound/MgAt/K3RidesDigTight.lean: the kind "lookup" (K3) AT THE COMPOSED MEANING
mgAll: WHAT RIDES PAST A SEATED LOOKUP ON THE DIGITS, SECOND FORM: THE TIGHT LIST. IT TAKES THE
PLACE OF ridesAtR_digits_mgAll AND ridesAtR_digits_ledger
(Johnson/Desc/Sound/MgAt/K3RidesDig.lean, K3RidesDigLedger.lean) AS THE ROW's STATEMENT: these two
ask their premise hFwd at EVERY sentence forms that rides, also at the one whose run is read ahead
("small"), where their proofs do not spend it: here hFwd is asked only of a sentence none of whose
runs is read ahead. Under the kind's ledger's own sentences on Dm (es, hD, hd). One theorem,
proved anew from ridesAtR_of_sorted (Johnson/Desc/First/Look/K3RidesDigR.lean) and
K3RidesDig.lean's and K3Rides.lean's lemmas; and an example in which Lean lays it into the field
rides of a given DigOwedR at the ledger's own letters. No error term. NO SOUNDNESS IS CLAIMED.

WHAT IS LEFT: the place · q.back = [] · hRel (digits_seated_passRel pays it at the value of
K3.theStated) · hj · hReq · hHead · hLed (meant payer: led_mgAll, K3RidesLed.lean, at the border
k3K l true) · bSmall: the sentence with a run that is read ahead: ONE premise, apart · hFwd: at
the other sentences, by run · hWt.

OBJECT: the composed meaning's fields; RidesAtR; DigOwedR.rides.
Used by K3RidesDigFull.lean (Johnson/Desc/Sound/MgAt/).
LETTERS: Dm, Mg, seats; Rch, k, l, q, b', a.
IMPORTS: Johnson/Desc/Sound/MgAt/K3RidesDig.lean,
  K3Owed.lean;
  Johnson/Desc/Sound/SmpNamed.lean;
  Johnson/Desc/First/Look/K3FillDigits.lean.
  Compiled with the whole library.
Limits. At the digits alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3RidesDig
import Johnson.Desc.Sound.MgAt.K3Owed
import Johnson.Desc.Sound.SmpNamed
import Johnson.Desc.First.Look.K3FillDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice Fo.Peel
open _root_.Run (ckP)
open VerifiableInference.Desc.First (ModelPart Item Pub Meaning Numbers start openSets flatPlacesOf)
open VerifiableInference.OnPublicFiles (SameBut relOf RidesAtR ridesAtR_of_sorted digitsPartK3 DigOwedR)
open VerifiableInference.Desc.First.Look (digList digSg)
open VerifiableInference.Reads.Pass (Fwd)
open Johnson.Desc.First.Walk.Tied (Stays)

local notation "PS" => flatPlacesOf linksFull true

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
variable (Dm : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **WHAT RIDES PAST A LOOKUP ON THE DIGITS: THE TIGHT LIST.** -/
theorem ridesAtR_digits_tight {Cl : Type} {Fr : Frame} (seats : List (ℕ × ℕ))
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
    (bSmall : ∀ kk r,
      openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) k
        (.forms l kk r) →
      ¬ insQ linksFull PS k (.forms l kk r) →
      (∃ p ∈ Dm.runs l kk r, Dm.ah p.1 p.2 = true) →
      ∀ (z : P) (u v : First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      ¬ u.1.failed ≠ none → onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      PassRel u.1 v.1 →
      Stays q.base (strsOf Fr u.2) (strsOf Fr v.2) → ∀ w,
      (mgAll Dm Mg).forms l kk r (z, v.1) (strsOf Fr v.2) w →
      (mgAll Dm Mg).forms l kk r (z, u.1) (strsOf Fr u.2) w)
    (hFwd : ∀ kk r,
      openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) k
        (.forms l kk r) →
      ¬ insQ linksFull PS k (.forms l kk r) →
      (∀ p ∈ Dm.runs l kk r, Dm.ah p.1 p.2 = false) →
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
  have hDec : ∀ c (z : P) s s', SameBut s s' → Dm.decT c (z, s) = Dm.decT c (z, s') :=
    fun c z s s' _ => hd c (z, s') (z, s) rfl
  have hSmp : ∀ (z : P) s s', SameBut s s' → ∀ x ∈ Dm.ms,
      SitsAt x Dm.N.index.1 Dm.N.index.2 → Dm.smp (z, s') x.1 x.2 = Dm.smp (z, s) x.1 x.2 :=
    fun z s s' hs x _ _ => by
      rw [es]
      unfold smpNamed
      rw [hs.st]
  have hDig : ∀ m, GoesBack (relOf SameBut q.base) (Dm.digitsPart m) := fun m => by
    rw [hD]
    exact fun _ _ _ _ _ _ h => h
  have hk : k ≤ (flatPlacesOf linksFull true).length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.1 ha).1
  refine ridesAtR_of_sorted Dm.N (mgAll Dm Mg) Rch k l q b' ha hK hp hl hback PassRel hRel
    ((mgAll_pile_back Dm Mg q.base).mono (relOf_pass q.base))
    ((mgAll_pin_back Dm Mg q.base _ _ hj hSmp).mono (relOf_pass q.base))
    ((mgAll_pinW_back Dm Mg q.base hDec).mono (relOf_pass q.base))
    (fun m c => (mgAll_row_back Dm Mg q.base m c).mono (relOf_pass q.base))
    (fun m p _ _ =>
      (mgAll_constr_back Dm Mg q.base hDec hReq m p (hDig m) (hHead p)).mono (relOf_pass q.base))
    (fun _ _ z u v w _ _ _ _ hR hy =>
      mgAll_wo_back Dm Mg q.base l (z, u.1) (strsOf Fr u.2) (z, v.1) (strsOf Fr v.2) w
        ⟨rfl, hR, hy⟩) ?_
  intro kk r ho hn z u v w hu hr hm hv hR hy h
  by_cases hA : ∃ p ∈ Dm.runs l kk r, Dm.ah p.1 p.2 = true
  · exact bSmall kk r ho hn hA z u v hu hr hm hv hR hy w h
  · obtain ⟨F, hF, hSz⟩ := hLed z u hu hr hm
    obtain ⟨G, Pp⟩ := hR.2.2 F hF hSz
    have hu0 : u.1.failed = none := Classical.not_not.1 hm
    have hNo : ∀ p ∈ Dm.runs l kk r, Dm.ah p.1 p.2 = false := fun p hp => by
      cases e : Dm.ah p.1 p.2 with
      | false => rfl
      | true => exact absurd ⟨p, hp, e⟩ hA
    refine mgAll_forms_back_dig Dm Mg Pp z _ _ w hNo
      (hFwd kk r ho hn hNo z u v hu hr hm hv hR)
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
    (bSmall : ∀ kk r,
      openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) k
        (.forms l kk r) →
      ¬ insQ linksFull PS k (.forms l kk r) →
      (∃ p ∈ Dm.runs l kk r, Dm.ah p.1 p.2 = true) →
      ∀ (z : P) (u v : First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      ¬ u.1.failed ≠ none → onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      PassRel u.1 v.1 →
      Stays q.base (strsOf Fr u.2) (strsOf Fr v.2) → ∀ w,
      (mgAll Dm Mg).forms l kk r (z, v.1) (strsOf Fr v.2) w →
      (mgAll Dm Mg).forms l kk r (z, u.1) (strsOf Fr u.2) w)
    (hFwd : ∀ kk r,
      openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) k
        (.forms l kk r) →
      ¬ insQ linksFull PS k (.forms l kk r) →
      (∀ p ∈ Dm.runs l kk r, Dm.ah p.1 p.2 = false) →
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
    rides := ridesAtR_digits_tight Dm Mg seats es hD hd Rch k l q b' ha hK hp hl hback hRel hj
      hReq hHead hLed bSmall hFwd hWt }

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.ridesAtR_digits_tight
