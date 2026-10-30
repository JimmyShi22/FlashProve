-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
ridesAtR_digits_mgAll: no parameters Dm and no place are shown here at
which its premises hold together.
Johnson/Desc/Sound/MgAt/K3RidesDig.lean: the kind "lookup" (K3) AT THE COMPOSED MEANING mgAll:
WHAT RIDES PAST A SEATED LOOKUP ON THE DIGITS OF A LINK's APPROXIMATE RANGE PROOF, SECOND FORM:
the premises of the tight rule (ridesAtR_of_sorted, Johnson/Desc/First/Look/K3RidesDigR.lean)
against the composed meaning's own texts, over PassRel: "the two states are SameBut; what is left
for the link's pending row is the same; from every well-laid ledger in front there is one behind
at which the two states are K3Pass (Johnson/Top/H/Keep/FormsPassK3.lean)". Statements and proofs.
Ties of texts: no error term. NO SOUNDNESS IS CLAIMED.

WHAT IS PAID. The five plain sorts: by Johnson/Desc/Sound/MgAt/K3Rides.lean (PassRel holds
SameBut) · of a sentence "forms l kk r" whose runs are not read ahead: the public test in front
(it is tied to the open item: the promise in front holds it) and the going back (k3_forms_back) ·
"wo l" · that an accepting of the seated piece gives PassRel (digits_seated_passRel: by
k3_digits_seated_turns, digits_step_leftOf, k3_digits_step_pass).
WHAT STAYS A NAMED PREMISE. hLed: inside the promise in front the state holds a well-laid ledger
(the public test "ledger l" is open there) · hFwd: what the segment's reader answers at a run in
front it answers behind (run by run: left to that run's files) · hWt: at r = "weights" Dm.wt l goes
back · bSmall: the sentence forms l kk r WITH A RUN THAT IS READ AHEAD ("K8.equations": the item
"small"): there the text is formsQA: no lemma in hand: it is left to the link's first hole's files
(Where this and lean/THEOREM.md differ, the page
holds.) · and K3Rides.lean's premises on Dm's letters.

OBJECT: the composed meaning's fields; RidesAtR.
Used by K3RidesDigTight.lean, K3RidesDigFull.lean, K3RidesDigStep.lean and K3RidesDigFwd.lean
  (Johnson/Desc/Sound/MgAt/), which call its lemmas. No other file in this library calls
  ridesAtR_digits_mgAll or digits_seated_passRel.
LETTERS: Dm, Mg; Rch, k, l, q, b', a.
IMPORTS: Johnson/Desc/First/Look/K3RidesDigR.lean;
  Johnson/Desc/Sound/MgAt/K3Rides.lean;
  Johnson/Top/H/Keep/FormsPassK3.lean;
  Johnson/Desc/First/Look/K3DigitsPass.lean,
  K3DigitsOwnStays.lean;
  Johnson/Desc/First/PubAllAt.lean.
  Compiled with the whole library.
Main names:
  `PassRel`, `relOf_pass`: the relation; it gives relOf SameBut. `digits_seated_passRel`: who gives
    it.
  `open_of_rider`: a rider stands in the table's list of open items.
  `onQ_tied_formsIn`: the promise holds the public test that is tied to an open item forms.
  `mgAll_formsIn_at`: what that test says at the composed meaning, run by run.
  `mgAll_forms_back_dig`: THE SENTENCE GOES BACK. `mgAll_wo_back`: so does "wo".
  `ridesAtR_digits_mgAll`: THE END.

Limits. At the digits alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3RidesDigR
import Johnson.Desc.Sound.MgAt.K3Rides
import Johnson.Top.H.Keep.FormsPassK3
import Johnson.Desc.First.Look.K3DigitsPass
import Johnson.Desc.First.Look.K3DigitsOwnStays
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice Fo.Peel
open _root_.Run (ckP)
open VerifiableInference.Desc.First (ModelPart Item Pub Meaning Numbers start openSets flatPlacesOf
  pubOfItems)
open VerifiableInference.OnPublicFiles (SameBut relOf RidesAtR ridesAtR_of_sorted K3Pass k3_forms_back
        readsOpen_full rowsApart_full)
open VerifiableInference.Reads.Pass (Fwd)
open Johnson.Desc.First.Walk.Tied (Stays)

local notation "PS" => flatPlacesOf linksFull true

/-- The two states are SameBut; what the open link's sub-protocols have left for its pending row is
the same; and from every well-laid ledger in front there is a ledger behind at which the two states
are K3Pass. -/
def PassRel (s s' : First.S) : Prop :=
  SameBut s s' ∧
    Johnson.Desc.First.Walk.Law.leftOf s' = Johnson.Desc.First.Walk.Law.leftOf s ∧
    ∀ F, s.fork? = some F → OnBytes.PscRun.Sized F → ∃ G, K3Pass s s' F G

/-- It gives the relation over SameBut. -/
theorem relOf_pass {P : Type} (base : ℕ) (a : P × First.S) (y : Strs) (b : P × First.S)
    (y' : Strs) (h : relOf PassRel base a y b y') : relOf SameBut base a y b y' := by
  obtain ⟨e, ⟨hs, -, -⟩, hy⟩ := h
  exact ⟨e, hs, hy⟩

/-- A rider stands in the table's list of open items. -/
theorem open_of_rider {k : ℕ} (hk : k ≤ (flatPlacesOf linksFull true).length) {i : Item}
    (ho : openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) k i) :
    i ∈ (openSets linksFull PS (start linksFull))[k]?.getD [] := by
  have hu : Item.unmarked ∈ start linksFull := List.mem_append_left _ (List.mem_cons_self)
  have hL : i ∈ openL (insL linksFull PS) (outsL linksFull PS) (start linksFull) k :=
    (openIsList Item (insL linksFull PS) (outsL linksFull PS) (start linksFull) k i).1 ho
  exact (openL_iff_openSets linksFull PS (start linksFull) readsOpen_full rowsApart_full hu k hk
    i).1 hL

section
variable {Cl P W : Type} {Fr : Frame}

/-- **AT A LINK's LOOKUP ON THE DIGITS AN ACCEPTING OF THE SEATED PIECE GIVES PassRel.** -/
theorem digits_seated_passRel (claim : OnBytes.Model.Aff → Cl)
    (readers : ℕ → Option (K3.Readers First.S)) (X : OnBytes.Model.Verify.Public)
    (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape) (a : Place)
    (Bst : Block First.S Cl) (h : K3.theStated claim readers X codes shape a = some Bst)
    (hOk : Bst.planOk = true) (i : ℕ) (hl : a.link = some i)
    (hpc : a.piece = K3.pieceAt X i true) {x : First.Look.Place}
    (hlook : First.Look.lookAt X i true = some x) {hs : OnBytes.Model.Forest.Shape}
    (hsh : (First.Look.P.ofPlace (OnBytes.Params.settingOf X.P.frame) true x).shape = some hs)
    (q : Piece (ckP .two) Fr (P × First.S) Cl W) (hback : q.back = []) :
    ∀ B', SeatOf Bst B' → ∀ u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr First.S Cl W).ior.red.out u τ = some v → PassRel u.1 v.1 := by
  intro B' hS u τ v hv
  obtain ⟨-, -, -, cols, hd⟩ := piece_below_plain (⟨below B', q.base, q.ds, q.back,
    fun _ _ w => w, q.err⟩ : Piece (ckP .two) Fr First.S Cl W) B' rfl hback u v τ hv
  have hd' := hS.1.2 _ _ _ _ hd
  exact ⟨(VerifiableInference.OnPublicFiles.k3_digits_seated_turns claim readers X codes shape a Bst B'
      h hOk hS.1 i hl hpc hlook hsh (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr First.S Cl W) rfl hback u v τ hv).1,
    VerifiableInference.OnPublicFiles.digits_step_leftOf claim readers X codes shape a Bst h hOk i hl
      hpc hlook hsh u.1 v.1 _ cols hd',
    fun F hF hSz => VerifiableInference.OnPublicFiles.k3_digits_step_pass claim readers X codes shape a
      Bst h hOk i hl hpc u.1 v.1 _ cols hd' hF hSz⟩

end

section
variable {P W : Type} {Fr : Frame} {N : Numbers} {Mg : Meaning P W} {z : P} {k : ℕ}

/-- The promise holds the public test that is tied to an open item forms. -/
theorem onQ_tied_formsIn {u : First.S × Fr.E.Str}
    (h : onQ N Mg linksFull PS (fun s => (z, s)) k u) (hu : u.1.failed = none) {l kk : ℕ}
    {r : String}
    (hO : Item.forms l kk r ∈ (openSets linksFull PS (start linksFull))[k]?.getD []) :
    Mg.pub (.formsIn l kk r) (z, u.1) = true := by
  obtain ⟨-, hm | ⟨h1, -⟩⟩ := h
  · exact absurd hu hm
  · simp only [Bool.and_eq_true] at h1
    have hp := h1.1.2
    unfold First.pubHeld at hp
    rw [List.all_eq_true] at hp
    refine hp _ (List.mem_append_right _ ?_)
    unfold pubOfItems
    exact List.mem_flatMap.2 ⟨_, hO, List.mem_singleton.2 rfl⟩

end

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
variable (Dm : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- What the tied test says at the composed meaning, at a run that is not read ahead. -/
theorem mgAll_formsIn_at {l kk : ℕ} {r : String} {a : P × First.S}
    (h : (mgAll Dm Mg).pub (.formsIn l kk r) a = true) {p : ℕ × String}
    (hp : p ∈ Dm.runs l kk r) (hah : Dm.ah p.1 p.2 = false) :
    K9.formsIn (Dm.Rd l) (Dm.N.group l) p.1 p.2 a.2 = true := by
  rw [mgAll_pub, First.pubAll_formsIn] at h
  have h1 := List.all_eq_true.1 h p hp
  have e : Dm.pubD.ah p.1 p.2 = false := hah
  rw [e] at h1
  exact h1

/-- **THE SENTENCE "forms" GOES BACK OVER K3Pass**, where none of its runs is read ahead. -/
theorem mgAll_forms_back_dig {l kk : ℕ} {r : String} {s s' : First.S} {F G : OnBytes.Model.Fork}
    (Pp : K3Pass s s' F G) (z : P) (y y' : Strs) (w : Wit (CellsQ rows cols) Tok MsgT)
    (hah : ∀ p ∈ Dm.runs l kk r, Dm.ah p.1 p.2 = false)
    (hFwd : ∀ p ∈ Dm.runs l kk r, Fwd (Dm.Rd l) p.1 p.2 s s')
    (hin : (mgAll Dm Mg).pub (.formsIn l kk r) (z, s) = true)
    (hWt : r = "weights" → Dm.wt l (z, s') y' w → Dm.wt l (z, s) y w)
    (h : (mgAll Dm Mg).forms l kk r (z, s') y' w) : (mgAll Dm Mg).forms l kk r (z, s) y w := by
  rw [mgAll_forms] at h ⊢
  refine ⟨fun p hp => ?_, fun e => hWt e (h.2 e)⟩
  have h1 := h.1 p hp
  rw [if_neg (by rw [hah p hp]; exact Bool.false_ne_true)] at h1 ⊢
  exact k3_forms_back Pp (Dm.Rd l) (Dm.N.group l) p.1 p.2 _ (hFwd p hp)
    (mgAll_formsIn_at Dm Mg hin hp (hah p hp)) h1

/-- **"wo" GOES BACK**: it reads what is left for the pending row, "out", the statement and the
book. -/
theorem mgAll_wo_back (base m : ℕ) : GoesBack (relOf PassRel base) ((mgAll Dm Mg).wo m) := by
  rw [mgAll_wo]
  intro a y b y' w hr hb
  obtain ⟨-, ⟨hs, hleft, -⟩, -⟩ := hr
  have e1 : Johnson.Desc.First.Walk.Law.rowAt Dm.d1.lay (Dm.d1.ncl m) Dm.d1.lin b.2 =
      Johnson.Desc.First.Walk.Law.rowAt Dm.d1.lay (Dm.d1.ncl m) Dm.d1.lin a.2 := by
    unfold Johnson.Desc.First.Walk.Law.rowAt Johnson.Desc.First.Walk.Law.rowBy
    rw [hleft, hs.out, hs.st]
  have e2 : Dm.rw13 b = Dm.rw13 a := by
    funext w'
    unfold MgData.rw13 K13.Law.rwBook
    rw [hs.st, hs.book]
  unfold First.FillP1.woAt at hb ⊢
  intro r hrow
  have h1 := hb r (by rw [e1]; exact hrow)
  rw [e2] at h1
  exact h1

variable (hDec : ∀ c (z : P) s s', SameBut s s' → Dm.decT c (z, s) = Dm.decT c (z, s'))
include hDec

/-- **WHAT RIDES PAST A LOOKUP ON THE DIGITS, SECOND FORM, AT THE COMPOSED MEANING.** -/
theorem ridesAtR_digits_mgAll {Cl : Type} {Fr : Frame}
    (Rch : ℕ → (P × First.S) × Fr.E.Str → Prop) (k l : ℕ)
    (q : Piece (ckP .two) Fr (P × First.S) Cl (Wit (CellsQ rows cols) Tok MsgT))
    (b' : Block First.S Cl) {a : Place} (ha : PS[k]? = some a) (hK : a.kind = .K3)
    (hp : 7 ≤ a.piece) (hl : a.link = some l) (hback : q.back = [])
    (hRel : ∀ B', SeatOf b' B' → ∀ u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr First.S Cl (Wit (CellsQ rows cols) Tok MsgT)).ior.red.out u τ =
          some v → PassRel u.1 v.1)
    (hj : Dm.N.index.1 < q.base)
    (hSmp : ∀ (z : P) s s', SameBut s s' → ∀ x ∈ Dm.ms, SitsAt x Dm.N.index.1 Dm.N.index.2 →
      Dm.smp (z, s') x.1 x.2 = Dm.smp (z, s) x.1 x.2)
    (hReq : ∀ (z : P) s s', SameBut s s' → Dm.H.req (z, s) = Dm.H.req (z, s'))
    (hDig : ∀ m, GoesBack (relOf SameBut q.base) (Dm.digitsPart m))
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
    refine mgAll_forms_back_dig Dm Mg Pp z _ _ w
      (fun p hp => by
        cases e : Dm.ah p.1 p.2 with
        | false => rfl
        | true => exact absurd ⟨p, hp, e⟩ hA)
      (hFwd kk r ho hn z u v hu hr hm hv hR)
      (onQ_tied_formsIn hu hu0 (open_of_rider hk ho))
      (fun e => by
        subst e
        exact hWt kk ho hn z u v hu hr hm hv hR w) h

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.relOf_pass
#print axioms VerifiableInference.Desc.Sound.digits_seated_passRel
#print axioms VerifiableInference.Desc.Sound.open_of_rider
#print axioms VerifiableInference.Desc.Sound.onQ_tied_formsIn
#print axioms VerifiableInference.Desc.Sound.mgAll_formsIn_at
#print axioms VerifiableInference.Desc.Sound.mgAll_forms_back_dig
#print axioms VerifiableInference.Desc.Sound.mgAll_wo_back
#print axioms VerifiableInference.Desc.Sound.ridesAtR_digits_mgAll
