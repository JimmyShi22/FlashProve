-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
fwd_step_layers, ridesAtR_digits_layers: no parameters Dm and no state
are shown here at which its premises hold together.
Johnson/Desc/Sound/MgAt/K3RidesDigFwd.lean: the kind "lookup" (K3) AT THE COMPOSED MEANING mgAll:
THE PREMISE hFwd OF ridesAtR_digits_step (Johnson/Desc/Sound/MgAt/K3RidesDigStep.lean), IN ITS OWN
TEXT, AT THE DIGITS' BORDER k3K l true OF A LAYERS' SEGMENT. First: WHICH SENTENCES forms RIDE
THERE, by sort of segment: a written list held against the table by Lean's kernel at all
twenty-five segments. Then, run by run: "objects", "guests": the lookups' own (objects_fwd,
guests_fwd: Johnson/Top/H/Keep/FormsPassOurs.lean) · "K8.equations": small_fwd
(Johnson/Top/H/Keep/FormsAheadPassK3.lean) · "planes", "join" stand for no run at a layers'
segment · "front", "back" (the table's name "own"): the calling kind's: a named premise. AND THE
ROW AT SUCH A SEGMENT: ridesAtR_digits_layers: this theorem laid into hFwd, led_mgAll
(K3RidesLed.lean) into hLed, and hWt paid (no sentence "weights" rides there): so three payers
have met the premises' own texts. Statements and proofs; one evaluation by Lean's kernel. No error
term. NO SOUNDNESS IS CLAIMED.

OBJECT: the table of joints' own functions; K9.readersOfLink H lk at the runs' names.
Used by K3RidesDigFwd2.lean and K3RidesDigFwd3.lean (Johnson/Desc/Sound/MgAt/) and
  K03RidesDigAt.lean (Johnson/P5J/).
LETTERS: Dm, Mg, Rch; H, lk; claim, readers, codes, shape, a, b'; l.
IMPORTS: Johnson/Desc/Sound/MgAt/K3RidesDigStep.lean,
  K3RidesLed.lean, Runs.lean;
  Johnson/Top/H/Keep/FormsPassOurs.lean,
  FormsAheadPassK3.lean.
  Compiled with the whole library.

Main names:
  `earlyOf`, `formsOkB`, `ridersFormsB`, `ridersForms_full`, `forms_rider_in`: the list, the test,
    the evaluation, and what it gives at a rider. `ridersForms_empty`: a negative test: at empty
    lists the test says false.
  `fwd_step_layers`: THE PAYMENT. `ridesAtR_digits_layers`: THE ROW AT A LAYERS' SEGMENT.

WHAT IS LEFT, EACH A NAMED PREMISE. TERMS OF Dm: hM · hlinks · hRd (Dm.Rd l = readersOfLink H lk)
· hA · hfO, hfG (the run that the link states under the name is the lookup's own). ON THE STATE IN
FRONT, WITH THE PREMISES: hsO, hsG (the link's second hole is silent at the run). LEFT TO OTHER
FILES, WITH THE PREMISES: hOwn ("front", "back") · hSm (what the link's first hole answered in
front it answers behind).
Limits. A layers' segment alone: attention's and the head's follow.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3RidesDigStep
import Johnson.Desc.Sound.MgAt.K3RidesLed
import Johnson.Desc.Sound.MgAt.Runs
import Johnson.Top.H.Keep.FormsPassOurs
import Johnson.Top.H.Keep.FormsAheadPassK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Meaning runsOf start openSets)
open VerifiableInference.Desc.K9 (readersOfLink statesOfLink LinkHoles)
open VerifiableInference.Reads.Pass (Fwd)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-! ## 1 Which sentences forms ride past the digits' lookup -/

/-- The written list, by sort of segment. -/
def earlyOf : ModelPart → List (ℕ × String)
  | .layers => [(2, "objects"), (2, "planes"), (2, "join"), (3, "own"), (5, "small")]
  | .attention => [(2, "objects"), (2, "planes"), (2, "join"), (3, "own"), (5, "small")]
  | .head => [(3, "objects"), (3, "planes"), (4, "join"), (4, "own"), (4, "weights"), (6, "small")]

/-- A sentence forms of segment l stands in the list E. -/
def formsOkB (l : ℕ) (E : List (ℕ × String)) : Item → Bool
  | .forms m kk r => !(m == l) || E.contains (kk, r)
  | _ => true

/-- At every segment: the digits' border lies within the list of places, and every rider there that
is a sentence forms of the segment stands in the list that `lists` gives for its sort. -/
def ridersFormsB (lists : ModelPart → List (ℕ × String)) : Bool :=
  (List.range 25).all fun l => (linksFull[l]?).any fun sub =>
    decide (k3K l true ≤ (PS).length) &&
      ((openSets linksFull PS (start linksFull))[k3K l true]?.getD []).all fun i =>
        ((((PS)[k3K l true]?.map (Desc.First.rowOf linksFull)).getD {}).ins ++
          (((PS)[k3K l true]?.map (Desc.First.rowOf linksFull)).getD {}).ctx ++
          [Item.unmarked]).contains i || formsOkB l (lists sub) i

set_option maxRecDepth 100000 in
theorem ridersForms_full : ridersFormsB earlyOf = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- A negative test. -/
theorem ridersForms_empty : ridersFormsB (fun _ => []) = false := by decide +kernel

/-- **What the evaluation gives at a rider.** -/
theorem forms_rider_in {l : ℕ} (hl : l < 25) {sub : ModelPart} (hs : linksFull[l]? = some sub)
    {kk : ℕ} {r : String}
    (ho : openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) (k3K l true)
      (.forms l kk r))
    (hn : ¬ insQ linksFull PS (k3K l true) (.forms l kk r)) : (kk, r) ∈ earlyOf sub := by
  have h := List.all_eq_true.1 ridersForms_full l (List.mem_range.2 hl)
  rw [hs, Option.any_some, Bool.and_eq_true] at h
  have hO := open_of_rider (of_decide_eq_true h.1) ho
  have h4 := List.all_eq_true.1 h.2 _ hO
  rcases Eq.mp (Bool.or_eq_true _ _) h4 with h5 | h5
  · refine absurd ?_ hn
    show Item.forms l kk r ∈ (rowQ linksFull PS (k3K l true)).ins ++
      (rowQ linksFull PS (k3K l true)).ctx ++ [.unmarked]
    exact List.contains_iff_mem.1 h5
  · have h6 : (earlyOf sub).contains (kk, r) = true := by simpa [formsOkB] using h5
    exact List.contains_iff_mem.1 h6

/-! ## 2 The payment at a layers' segment -/

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)
  (H : LinkHoles) (lk : Desc.Link Desc.First.S Desc.Claim)
  (claim : Aff → Desc.Claim) (readers : ℕ → Option (Desc.K3.Readers Desc.First.S))
  (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place)
  (b' : Desc.Block Desc.First.S Desc.Claim)
  (h : Desc.K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
  {l : ℕ} (hi : a.link = some l) (hpc : a.piece = Desc.K3.pieceAt X l true)
  (hM : Mg.more = {}) (hlinks : Dm.links = linksFull) (hl : l < 25)
  (hsub : linksFull[l]? = some ModelPart.layers) (hRd : Dm.Rd l = readersOfLink H lk)
  (hA : AtS2 (Desc.K3.seatCalls claim))
include h hOk hi hpc hM hlinks hl hsub hRd hA

/-- **hFwd OF ridesAtR_digits_step, IN ITS OWN TEXT, AT A LAYERS' SEGMENT.** -/
theorem fwd_step_layers
    (hfO : ∀ n r, (statesOfLink lk 1).find? (fun x => x.1 == "objects") = some (n, r) →
      r = objectsRun (Desc.K3.seatCalls claim))
    (hfG : ∀ n r, (statesOfLink lk 1).find? (fun x => x.1 == "guests") = some (n, r) →
      r = guestsRun ([] : List (Desc.First.Look.Guest Desc.First.S Desc.Claim)))
    (hsO : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      H.silent 1 "objects" u.1 = none)
    (hsG : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      H.silent 1 "guests" u.1 = none)
    (hOwn : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(2, "front"), (2, "back")], Fwd (Dm.Rd l) p.1 p.2 u.1 v.1)
    (hSm : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ R, H.small u.1 = some R → H.small v.1 = some R) :
    ∀ kk r,
      openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) (k3K l true)
        (.forms l kk r) →
      ¬ insQ linksFull PS (k3K l true) (.forms l kk r) →
      ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ Dm.runs l kk r, Fwd (Dm.Rd l) p.1 p.2 u.1 v.1 := by
  intro kk r ho hn z u v hu hr hm hv hR p hp
  have hin := forms_rider_in hl hsub ho hn
  have e : Dm.runs l kk r = runsOf .layers kk r := by
    show runsAt Dm.links l kk r = runsOf .layers kk r
    rw [hlinks]
    exact runsAt_of linksFull l .layers hsub kk r
  rw [e] at hp
  obtain ⟨F, hF, hSz⟩ := led_mgAll Dm Mg Rch hM hl hsub z u hu hr hm
  obtain ⟨rs, gs, hd⟩ := id hR
  obtain ⟨G, Q⟩ := k3_digits_step_pass claim readers X codes shape a b' h hOk l hi hpc u.1 v.1 rs
    gs hd hF hSz
  obtain ⟨-, -, -, -, hLk, -, -⟩ :=
    k3_digits_step_leaves claim readers X codes shape a b' h hOk l hi hpc u.1 v.1 rs gs hd
  simp only [earlyOf, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hin
  rcases hin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [runs_layers.1] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rw [hRd]
    rcases hp with rfl | rfl
    · exact objects_fwd H lk 1 (Desc.K3.seatCalls claim) hA Q hLk (hsO z u v hu hr hm hv hR) hfO
    · exact guests_fwd H lk 1 Q (hsG z u v hu hr hm hv hR) hfG
  · rw [runs_layers.2.2.2.2.1] at hp
    cases hp
  · rw [runs_layers.2.2.2.2.2] at hp
    cases hp
  · rw [runs_layers.2.1] at hp
    exact hOwn z u v hu hr hm hv hR p hp
  · rw [runs_layers.2.2.1] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    rw [hRd]
    exact small_fwd H lk 4 (hSm z u v hu hr hm hv hR)

/-- **THE ROW AT A LAYERS' SEGMENT: hLed, hFwd AND hWt OF ridesAtR_digits_step ARE PAID**: three
payers meet the premises' own texts. ("weights" rides at no layers' segment: by the evaluation.) -/
theorem ridesAtR_digits_layers (seats : List (ℕ × ℕ)) (es : Dm.smp = smpNamed Dm.cs seats)
    (hD : Dm.digitsPart = digitsPartK3 X Dm.sent Dm.l3)
    (hd : ∀ c (y y' : P × Desc.First.S), y'.1 = y.1 → Dm.decT c y' = Dm.decT c y)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Desc.Claim (Desc.Wit (CellsQ rows cols) Tok MsgT))
    (ha : (PS)[k3K l true]? = some a) (hK : a.kind = .K3) (hp7 : 7 ≤ a.piece)
    (hback : q.back = []) {x : Desc.First.Look.Place} (hlook : lookAt X l true = some x)
    {hs : Forest.Shape}
    (hsh : (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) true x).shape = some hs)
    (hj : Dm.N.index.1 < q.base)
    (hReq : ∀ (z : P) s s', SameBut s s' → Dm.H.req (z, s) = Dm.H.req (z, s'))
    (hHead : ∀ p i, GoesBack (relOf SameBut q.base) (Dm.headPart p i))
    (hfO : ∀ n r, (statesOfLink lk 1).find? (fun x => x.1 == "objects") = some (n, r) →
      r = objectsRun (Desc.K3.seatCalls claim))
    (hfG : ∀ n r, (statesOfLink lk 1).find? (fun x => x.1 == "guests") = some (n, r) →
      r = guestsRun ([] : List (Desc.First.Look.Guest Desc.First.S Desc.Claim)))
    (hsO : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      H.silent 1 "objects" u.1 = none)
    (hsG : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      H.silent 1 "guests" u.1 = none)
    (hOwn : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(2, "front"), (2, "back")], Fwd (Dm.Rd l) p.1 p.2 u.1 v.1)
    (hSm : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ R, H.small u.1 = some R → H.small v.1 = some R) :
    RidesAtR Dm.N (mgAll Dm Mg) Rch (k3K l true) q b' :=
  ridesAtR_digits_step Dm Mg seats es hD hd Rch (k3K l true) l q b' ha hK hp7 hi hback claim
    readers codes shape h hOk hpc hlook hsh hj hReq hHead (led_mgAll Dm Mg Rch hM hl hsub)
    (fwd_step_layers Dm Mg Rch H lk claim readers codes shape a b' h hOk hi hpc hM hlinks hl hsub
      hRd hA hfO hfG hsO hsG hOwn hSm)
    fun kk ho hn => absurd (forms_rider_in hl hsub ho hn) (by simp [earlyOf])

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.ridersForms_full
#print axioms VerifiableInference.OnPublicFiles.ridersForms_empty
#print axioms VerifiableInference.OnPublicFiles.forms_rider_in
#print axioms VerifiableInference.OnPublicFiles.fwd_step_layers
#print axioms VerifiableInference.OnPublicFiles.ridesAtR_digits_layers
