-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
ridesAtR_digits_rel, ridesAtR_digits_step: no parameters Dm and no place
are shown here at which their premises hold together.
Johnson/Desc/Sound/MgAt/K3RidesDigStep.lean: the kind "lookup" (K3) AT THE COMPOSED MEANING mgAll:
WHAT RIDES PAST A SEATED LOOKUP ON THE DIGITS, SECOND FORM: THE ROW's STATEMENT: its premises by
run (hFwd, hWt) ARE HANDED THE SUB-PROTOCOL's OWN ACCEPT: StepRel b' u.1 v.1: "there are rounds
and columns at which b' decides from u.1 to v.1". Why: ridesAtR_digits_tight | _full
(K3RidesDigTight.lean, K3RidesDigFull.lean) hand these premises PassRel alone, while the lemmas
that could pay them start from that accept. Statements and proofs. Ties of texts: no error term.
NO SOUNDNESS IS CLAIMED.

OBJECT: the composed meaning's fields; RidesAtR; the value of K3.theStated at a digits' place.
Used by K3RidesDigFwd.lean, K3RidesDigFwd2.lean and K3RidesDigFwd3.lean
  (Johnson/Desc/Sound/MgAt/) and others.
LETTERS: Dm, Mg, seats; Rel; Rch, k, l, q, b', a; claim, readers, codes, shape, x, hs.
IMPORTS:
  Johnson/Desc/Sound/MgAt/K3RidesDigFull.lean;
  Johnson/Desc/First/Look/K3DigitsStep.lean.
  Compiled with the whole library.

Main names:
  `ridesAtR_digits_rel`: THE END, GENERAL IN THE RELATION Rel, under hPass: Rel gives PassRel.
  `StepRel`, `stepRel_of_seated`, `stepRel_pass`: the accept itself; who gives it; it gives PassRel.
  `ridesAtR_digits_step`: THE ROW: at Rel := StepRel b': hRel and hPass are paid.

WHAT IS LEFT: the place · q.back = [] · the value of K3.theStated and its four facts · hj · hReq ·
hHead · hLed · hFwd · hWt.
Limits. At the digits alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3RidesDigFull
import Johnson.Desc.First.Look.K3DigitsStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice Fo.Peel
open _root_.Run (ckP)
open VerifiableInference.Desc.First (ModelPart Item Pub Meaning Numbers start openSets flatPlacesOf)
open VerifiableInference.OnPublicFiles (SameBut relOf RidesAtR ridesAtR_of_sorted digitsPartK3 DigOwedR
        K3Pass)
open VerifiableInference.Desc.First.Look (digList digSg)
open VerifiableInference.Reads.Pass (Fwd)
open Johnson.Desc.First.Walk.Tied (Stays)

local notation "PS" => flatPlacesOf linksFull true

/-! ## 1 The accept itself -/

/-- There are rounds and columns at which B decides from s to s'. -/
def StepRel {Cl : Type} (B : Block First.S Cl) (s s' : First.S) : Prop :=
  ∃ rs gs, B.decide s rs gs = .ok s'

section
variable {Cl P W : Type} {Fr : Frame}

/-- **An accepting of the seated piece gives it.** -/
theorem stepRel_of_seated (Bst : Block First.S Cl) (q : Piece (ckP .two) Fr (P × First.S) Cl W)
    (hback : q.back = []) :
    ∀ B', SeatOf Bst B' → ∀ u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr First.S Cl W).ior.red.out u τ = some v → StepRel Bst u.1 v.1 := by
  intro B' hS u τ v hv
  obtain ⟨-, -, -, cols, hd⟩ := piece_below_plain (⟨below B', q.base, q.ds, q.back,
    fun _ _ w => w, q.err⟩ : Piece (ckP .two) Fr First.S Cl W) B' rfl hback u v τ hv
  exact ⟨_, cols, hS.1.2 _ _ _ _ hd⟩

/-- **At the value of K3.theStated at a digits' place it gives PassRel.** -/
theorem stepRel_pass (claim : OnBytes.Model.Aff → Cl)
    (readers : ℕ → Option (K3.Readers First.S)) (X : OnBytes.Model.Verify.Public)
    (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape) (a : Place)
    (Bst : Block First.S Cl) (h : K3.theStated claim readers X codes shape a = some Bst)
    (hOk : Bst.planOk = true) (i : ℕ) (hl : a.link = some i)
    (hpc : a.piece = K3.pieceAt X i true) {x : First.Look.Place}
    (hlook : First.Look.lookAt X i true = some x) {hs : OnBytes.Model.Forest.Shape}
    (hsh : (First.Look.P.ofPlace (OnBytes.Params.settingOf X.P.frame) true x).shape = some hs)
    (s s' : First.S) (hR : StepRel Bst s s') : PassRel s s' := by
  obtain ⟨rs, gs, hd⟩ := hR
  exact ⟨(VerifiableInference.OnPublicFiles.k3_digits_step_turns claim readers X codes shape a Bst h hOk
      i hl hpc hlook hsh s s' rs gs hd).1,
    VerifiableInference.OnPublicFiles.digits_step_leftOf claim readers X codes shape a Bst h hOk i hl
      hpc hlook hsh s s' rs gs hd,
    fun F hF hSz => VerifiableInference.OnPublicFiles.k3_digits_step_pass claim readers X codes shape a
      Bst h hOk i hl hpc s s' rs gs hd hF hSz⟩

end

/-! ## 2 The end, general in the relation -/

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
variable (Dm : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **WHAT RIDES PAST A LOOKUP ON THE DIGITS, GENERAL IN THE RELATION.** -/
theorem ridesAtR_digits_rel {Cl : Type} {Fr : Frame} (Rel : First.S → First.S → Prop)
    (hPass : ∀ s s', Rel s s' → PassRel s s') (seats : List (ℕ × ℕ))
    (es : Dm.smp = smpNamed Dm.cs seats) (hD : Dm.digitsPart = digitsPartK3 X Dm.sent Dm.l3)
    (hd : ∀ c (y y' : P × First.S), y'.1 = y.1 → Dm.decT c y' = Dm.decT c y)
    (Rch : ℕ → (P × First.S) × Fr.E.Str → Prop) (k l : ℕ)
    (q : Piece (ckP .two) Fr (P × First.S) Cl (Wit (CellsQ rows cols) Tok MsgT))
    (b' : Block First.S Cl) {a : Place} (ha : PS[k]? = some a) (hK : a.kind = .K3)
    (hp : 7 ≤ a.piece) (hl : a.link = some l) (hback : q.back = [])
    (hRel : ∀ B', SeatOf b' B' → ∀ u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr First.S Cl (Wit (CellsQ rows cols) Tok MsgT)).ior.red.out u τ =
          some v → Rel u.1 v.1)
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
      Rel u.1 v.1 →
      ∀ p ∈ Dm.runs l kk r, Fwd (Dm.Rd l) p.1 p.2 u.1 v.1)
    (hWt : ∀ kk,
      openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) k
        (.forms l kk "weights") →
      ¬ insQ linksFull PS k (.forms l kk "weights") →
      ∀ (z : P) (u v : First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      ¬ u.1.failed ≠ none → onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      Rel u.1 v.1 →
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
  have hmono : ∀ (a : P × First.S) y (b : P × First.S) y', relOf Rel q.base a y b y' →
      relOf SameBut q.base a y b y' :=
    fun a y b y' h => relOf_pass q.base a y b y' ⟨h.1, hPass _ _ h.2.1, h.2.2⟩
  refine ridesAtR_of_sorted Dm.N (mgAll Dm Mg) Rch k l q b' ha hK hp hl hback Rel hRel
    ((mgAll_pile_back Dm Mg q.base).mono hmono)
    ((mgAll_pin_back Dm Mg q.base _ _ hj hSmp).mono hmono)
    ((mgAll_pinW_back Dm Mg q.base hDec).mono hmono)
    (fun m c => (mgAll_row_back Dm Mg q.base m c).mono hmono)
    (fun m p _ _ => (mgAll_constr_back Dm Mg q.base hDec hReq m p (hDig m) (hHead p)).mono hmono)
    (fun _ _ z u v w _ _ _ _ hR hy =>
      mgAll_wo_back Dm Mg q.base l (z, u.1) (strsOf Fr u.2) (z, v.1) (strsOf Fr v.2) w
        ⟨rfl, hPass _ _ hR, hy⟩) ?_
  intro kk r ho hn z u v w hu hr hm hv hR _ h
  obtain ⟨F, hF, hSz⟩ := hLed z u hu hr hm
  obtain ⟨G, Pp⟩ := (hPass _ _ hR).2.2 F hF hSz
  have hu0 : u.1.failed = none := Classical.not_not.1 hm
  exact mgAll_forms_back_any Dm Mg Pp z _ _ w (hFwd kk r ho hn z u v hu hr hm hv hR)
    (onQ_tied_formsIn hu hu0 (open_of_rider hk ho))
    (fun e => by
      subst e
      exact hWt kk ho hn z u v hu hr hm hv hR w) h

/-! ## 3 The row -/

/-- **WHAT RIDES PAST A LOOKUP ON THE DIGITS: THE PREMISES BY RUN ARE HANDED THE ACCEPT ITSELF.** -/
theorem ridesAtR_digits_step {Cl : Type} {Fr : Frame} (seats : List (ℕ × ℕ))
    (es : Dm.smp = smpNamed Dm.cs seats) (hD : Dm.digitsPart = digitsPartK3 X Dm.sent Dm.l3)
    (hd : ∀ c (y y' : P × First.S), y'.1 = y.1 → Dm.decT c y' = Dm.decT c y)
    (Rch : ℕ → (P × First.S) × Fr.E.Str → Prop) (k l : ℕ)
    (q : Piece (ckP .two) Fr (P × First.S) Cl (Wit (CellsQ rows cols) Tok MsgT))
    (b' : Block First.S Cl) {a : Place} (ha : PS[k]? = some a) (hK : a.kind = .K3)
    (hp : 7 ≤ a.piece) (hl : a.link = some l) (hback : q.back = [])
    (claim : OnBytes.Model.Aff → Cl) (readers : ℕ → Option (K3.Readers First.S))
    (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (h : K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
    (hpc : a.piece = K3.pieceAt X l true) {x : First.Look.Place}
    (hlook : First.Look.lookAt X l true = some x) {hs : OnBytes.Model.Forest.Shape}
    (hsh : (First.Look.P.ofPlace (OnBytes.Params.settingOf X.P.frame) true x).shape = some hs)
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
      StepRel b' u.1 v.1 →
      ∀ p ∈ Dm.runs l kk r, Fwd (Dm.Rd l) p.1 p.2 u.1 v.1)
    (hWt : ∀ kk,
      openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) k
        (.forms l kk "weights") →
      ¬ insQ linksFull PS k (.forms l kk "weights") →
      ∀ (z : P) (u v : First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      ¬ u.1.failed ≠ none → onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k + 1) v →
      StepRel b' u.1 v.1 →
      ∀ w, Dm.wt l (z, v.1) (strsOf Fr v.2) w → Dm.wt l (z, u.1) (strsOf Fr u.2) w) :
    RidesAtR Dm.N (mgAll Dm Mg) Rch k q b' :=
  ridesAtR_digits_rel Dm Mg (StepRel b')
    (stepRel_pass claim readers X codes shape a b' h hOk l hl hpc hlook hsh) seats es hD hd Rch k
    l q b' ha hK hp hl hback (stepRel_of_seated b' q hback) hj hReq hHead hLed hFwd hWt

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.stepRel_of_seated
#print axioms VerifiableInference.Desc.Sound.stepRel_pass
#print axioms VerifiableInference.Desc.Sound.ridesAtR_digits_rel
#print axioms VerifiableInference.Desc.Sound.ridesAtR_digits_step
