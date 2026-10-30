-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
fwd_step_att, fwd_step_head, ridesAtR_digits_att, ridesAtR_digits_head:
no parameters Dm and no state are shown here at which their premises hold together.
Johnson/Desc/Sound/MgAt/K3RidesDigFwd2.lean: the kind "lookup" (K3) AT THE COMPOSED MEANING mgAll:
THE PREMISE hFwd OF ridesAtR_digits_step (Johnson/Desc/Sound/MgAt/K3RidesDigStep.lean), IN ITS OWN
TEXT, AT THE DIGITS' BORDER OF AN ATTENTION SEGMENT AND OF THE OUTPUT HEAD's; after
K3RidesDigFwd.lean (a layers' segment). Run by run: "objects", "guests", "planes", and at
attention "join": the lookups' own (objects_fwd, guests_fwd, planes_fwd', join_fwd':
Johnson/Top/H/Keep/FormsPassOurs.lean), with the calling kinds' readers and keys carried across
the whole seated accept (k3_digits_step_attReaders, k3_digits_step_attKeys,
k3_digits_step_headReaders: Johnson/Desc/First/Look/K3DigitsCallersStay.lean) · "K8.equations":
small_fwd, with "the reader's answer is the same across the whole seated accept"
(k3_digits_step_smallReader: Johnson/Desc/Sound/MgAt/K3DigitsFormsSmall.lean) · the table's name
"own", and the head's "join": the calling kinds' own runs: named premises. AT THE HEAD THE PREMISE
"the link's second hole is silent" IS NOT ASKED (by reading it is false there): in its place:
hr: the run itself answers at the state in front (Johnson/Top/H/Keep/FormsPassRun.lean). AND THE
ROWS: ridesAtR_digits_att, ridesAtR_digits_head. Statements and proofs: joinings. No error term.
NO SOUNDNESS IS CLAIMED.

OBJECT: K9.readersOfLink H lk at the runs' names; RidesAtR.
Used by K03RidesDigAt2.lean (Johnson/P5J/) and K3RidesDigFwd3.lean (Johnson/Desc/Sound/MgAt/).
LETTERS: Dm, Mg, Rch; H, lk; claim, readers, codes, shape, a, b'; l; A | iU3, lm.
IMPORTS:
  Johnson/Desc/Sound/MgAt/K3RidesDigFwd.lean;
  Johnson/Desc/First/Look/K3DigitsCallersStay.lean;
  Johnson/Desc/Sound/MgAt/K3DigitsFormsSmall.lean;
  Johnson/Top/H/Keep/FormsPassRun.lean.
  Compiled with the whole library.

Main names: `fwd_of_noSilent`; `fwd_step_att`, `ridesAtR_digits_att`; `fwd_step_head`,
  `ridesAtR_digits_head`.

WHAT IS LEFT, BESIDE K3RidesDigFwd.lean's LIST. hHs: the link's first hole is smallReader (in
hSm's place: a term) · hfP, hfJ, hsP, hsJ: as hfO, hsO at "planes", "join" · hHere: inside the
promise in front the open link is of the segment's sort · hWin: the window of the sumcheck over
the leaves is free in the ledger in front and ends at or below its next slot (meant payer:
hwin_of_onOut, Johnson/Top/H/Keep/CallersStay.lean) · AT THE HEAD: hrO, hrG, hrP (in hsO, hsG,
hsP's place) · hJoin (the run "join" is the calling kind's own there) · hWt: Dm.wt l goes back
(the sentence forms l 4 "weights" rides there).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3RidesDigFwd
import Johnson.Desc.First.Look.K3DigitsCallersStay
import Johnson.Desc.Sound.MgAt.K3DigitsFormsSmall
import Johnson.Top.H.Keep.FormsPassRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Meaning runsOf start openSets)
open VerifiableInference.Desc.K9 (readersOfLink statesOfLink LinkHoles readerOf smallReader)
open VerifiableInference.Desc.First.Att.P (readersOfO keysOfO)
open VerifiableInference.Desc.Kinds.Head (planesAt callerReaders)
open VerifiableInference.Reads.Pass (Fwd)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-! ## 0 A tool: the way forward, where the run itself answers in front -/

/-- Under hr a link's reader goes forward whatever its second hole holds, if it does so with that
hole emptied. -/
theorem fwd_of_noSilent (H : LinkHoles) (lk : Desc.Link Desc.First.S Desc.Claim) (b : ℕ)
    {name : String} {s s' : Desc.First.S} (hn : (name == "K8.equations") = false)
    (hr : (readerOf (statesOfLink lk) b name s).isSome = true)
    (hf : Fwd (readersOfLink (noSilent H) lk) b name s s') :
    Fwd (readersOfLink H lk) b name s s' := by
  intro R hR
  have hr' := hr_fwd H lk b hn hf hr
  rw [forms_run H lk b hn hr] at hR
  have h1 := hf R (by rw [forms_run (noSilent H) lk b hn hr]; exact hR)
  rw [forms_run (noSilent H) lk b hn hr'] at h1
  rw [forms_run H lk b hn hr']
  exact h1

/-! ## 1 An attention segment -/

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
  (hsub : linksFull[l]? = some ModelPart.attention) (hRd : Dm.Rd l = readersOfLink H lk)
  (hA : AtS2 (Desc.K3.seatCalls claim))
include h hOk hi hpc hM hlinks hl hsub hRd hA

/-- **hFwd OF ridesAtR_digits_step, IN ITS OWN TEXT, AT AN ATTENTION SEGMENT.** -/
theorem fwd_step_att
    (A : Attention.Plan) (lm : ℕ)
    (hfO : ∀ n r, (statesOfLink lk 1).find? (fun x => x.1 == "objects") = some (n, r) →
      r = objectsRun (Desc.K3.seatCalls claim))
    (hfG : ∀ n r, (statesOfLink lk 1).find? (fun x => x.1 == "guests") = some (n, r) →
      r = guestsRun ([] : List (Desc.First.Look.Guest Desc.First.S Desc.Claim)))
    (hfP : ∀ n r, (statesOfLink lk 1).find? (fun x => x.1 == "planes") = some (n, r) →
      r = Desc.K3.planesRun (Desc.K3.seatCalls claim) lm (readersOfO A))
    (hfJ : ∀ n r, (statesOfLink lk 2).find? (fun x => x.1 == "join") = some (n, r) →
      r = Desc.K3.joinRun (Desc.K3.seatCalls claim) (keysOfO A))
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
    (hsP : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      H.silent 1 "planes" u.1 = none)
    (hsJ : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      H.silent 2 "join" u.1 = none)
    (hHere : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∃ w₀, u.1.here = .att w₀)
    (hWin : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ F, u.1.fork? = some F → ∀ g, (Desc.K3.seatCalls claim).heard u.1 = some g →
        g.leaves.first + lvLen g ≤ F.next ∧ g.leaves.first + lvLen g ≤ F.ns ∧
        ∀ j, g.leaves.first ≤ j → j < g.leaves.first + lvLen g → ¬ OnBytes.PscRun.Filled F j)
    (hOwn : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(2, "first"), (2, "keys"), (2, "second")], Fwd (Dm.Rd l) p.1 p.2 u.1 v.1)
    (hHs : H.small = smallReader) :
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
  have e : Dm.runs l kk r = runsOf .attention kk r := by
    show runsAt Dm.links l kk r = runsOf .attention kk r
    rw [hlinks]
    exact runsAt_of linksFull l .attention hsub kk r
  rw [e] at hp
  obtain ⟨F, hF, hSz⟩ := led_mgAll Dm Mg Rch hM hl hsub z u hu hr hm
  obtain ⟨rs, gs, hd⟩ := id hR
  obtain ⟨G, Q⟩ := k3_digits_step_pass claim readers X codes shape a b' h hOk l hi hpc u.1 v.1 rs
    gs hd hF hSz
  obtain ⟨-, -, -, -, hLk, -, -⟩ :=
    k3_digits_step_leaves claim readers X codes shape a b' h hOk l hi hpc u.1 v.1 rs gs hd
  simp only [earlyOf, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hin
  obtain ⟨w₀, hw⟩ := hHere z u v hu hr hm hv hR
  have eF : w₀.F = F := by
    have h0 := hF
    simp only [Desc.First.S.fork?, hw] at h0
    exact Option.some.inj h0
  have hSw : OnBytes.PscRun.Sized w₀.F := by rw [eF]; exact hSz
  rcases hin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [runs_attention.1] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rw [hRd]
    rcases hp with rfl | rfl
    · exact objects_fwd H lk 1 (Desc.K3.seatCalls claim) hA Q hLk (hsO z u v hu hr hm hv hR) hfO
    · exact guests_fwd H lk 1 Q (hsG z u v hu hr hm hv hR) hfG
  · rw [runs_attention.2.1] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    rw [hRd]
    exact planes_fwd' H lk 1 (Desc.K3.seatCalls claim) hA Q hLk lm (readersOfO A)
      (k3_digits_step_attReaders claim readers X codes shape a b' h hOk l hi hpc u.1 v.1 rs gs hd
        hw hSw A)
      (hWin z u v hu hr hm hv hR F hF) (hsP z u v hu hr hm hv hR) hfP
  · rw [runs_attention.2.2.1] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    rw [hRd]
    exact join_fwd' H lk 2 (Desc.K3.seatCalls claim) hA Q hLk (keysOfO A)
      (k3_digits_step_attKeys claim readers X codes shape a b' h hOk l hi hpc u.1 v.1 rs gs hd hw
        hSw A)
      (hsJ z u v hu hr hm hv hR) hfJ
  · rw [runs_attention.2.2.2.1] at hp
    exact hOwn z u v hu hr hm hv hR p hp
  · rw [runs_attention.2.2.2.2.1] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    rw [hRd]
    exact small_fwd H lk 4 fun R hR0 => by
      rw [hHs] at hR0 ⊢
      rw [k3_digits_step_smallReader claim readers X codes shape a b' h hOk l hi hpc u.1 v.1 rs gs
        hd]
      exact hR0

/-- **THE ROW AT AN ATTENTION SEGMENT.** ("weights" rides at no attention segment: by the
evaluation.) -/
theorem ridesAtR_digits_att (seats : List (ℕ × ℕ)) (es : Dm.smp = smpNamed Dm.cs seats)
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
    (A : Attention.Plan) (lm : ℕ)
    (hfO : ∀ n r, (statesOfLink lk 1).find? (fun x => x.1 == "objects") = some (n, r) →
      r = objectsRun (Desc.K3.seatCalls claim))
    (hfG : ∀ n r, (statesOfLink lk 1).find? (fun x => x.1 == "guests") = some (n, r) →
      r = guestsRun ([] : List (Desc.First.Look.Guest Desc.First.S Desc.Claim)))
    (hfP : ∀ n r, (statesOfLink lk 1).find? (fun x => x.1 == "planes") = some (n, r) →
      r = Desc.K3.planesRun (Desc.K3.seatCalls claim) lm (readersOfO A))
    (hfJ : ∀ n r, (statesOfLink lk 2).find? (fun x => x.1 == "join") = some (n, r) →
      r = Desc.K3.joinRun (Desc.K3.seatCalls claim) (keysOfO A))
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
    (hsP : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      H.silent 1 "planes" u.1 = none)
    (hsJ : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      H.silent 2 "join" u.1 = none)
    (hHere : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∃ w₀, u.1.here = .att w₀)
    (hWin : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ F, u.1.fork? = some F → ∀ g, (Desc.K3.seatCalls claim).heard u.1 = some g →
        g.leaves.first + lvLen g ≤ F.next ∧ g.leaves.first + lvLen g ≤ F.ns ∧
        ∀ j, g.leaves.first ≤ j → j < g.leaves.first + lvLen g → ¬ OnBytes.PscRun.Filled F j)
    (hOwn : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(2, "first"), (2, "keys"), (2, "second")], Fwd (Dm.Rd l) p.1 p.2 u.1 v.1)
    (hHs : H.small = smallReader) :
    RidesAtR Dm.N (mgAll Dm Mg) Rch (k3K l true) q b' :=
  ridesAtR_digits_step Dm Mg seats es hD hd Rch (k3K l true) l q b' ha hK hp7 hi hback claim
    readers codes shape h hOk hpc hlook hsh hj hReq hHead (led_mgAll Dm Mg Rch hM hl hsub)
    (fwd_step_att Dm Mg Rch H lk claim readers codes shape a b' h hOk hi hpc hM hlinks hl hsub
      hRd hA A lm hfO hfG hfP hfJ hsO hsG hsP hsJ hHere hWin hOwn hHs)
    fun kk ho hn => absurd (forms_rider_in hl hsub ho hn) (by simp [earlyOf])

end

/-! ## 2 The output head's segment -/

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
  (hsub : linksFull[l]? = some ModelPart.head) (hRd : Dm.Rd l = readersOfLink H lk)
  (hA : AtS2 (Desc.K3.seatCalls claim))
include h hOk hi hpc hM hlinks hl hsub hRd hA

/-- **hFwd OF ridesAtR_digits_step, IN ITS OWN TEXT, AT THE OUTPUT HEAD's SEGMENT.** -/
theorem fwd_step_head
    (iU3 lm : ℕ)
    (hfO : ∀ n r, (statesOfLink lk 2).find? (fun x => x.1 == "objects") = some (n, r) →
      r = objectsRun (Desc.K3.seatCalls claim))
    (hfG : ∀ n r, (statesOfLink lk 2).find? (fun x => x.1 == "guests") = some (n, r) →
      r = guestsRun ([] : List (Desc.First.Look.Guest Desc.First.S Desc.Claim)))
    (hfP : ∀ n r, (statesOfLink lk 2).find? (fun x => x.1 == "planes") = some (n, r) →
      r = Desc.K3.planesRun (Desc.K3.seatCalls claim) lm (callerReaders (planesAt iU3)))
    (hrO : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      (readerOf (statesOfLink lk) 2 "objects" u.1).isSome = true)
    (hrG : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      (readerOf (statesOfLink lk) 2 "guests" u.1).isSome = true)
    (hrP : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      (readerOf (statesOfLink lk) 2 "planes" u.1).isSome = true)
    (hHere : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∃ o, u.1.here = .head o)
    (hWin : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ F, u.1.fork? = some F → ∀ g, (Desc.K3.seatCalls claim).heard u.1 = some g →
        g.leaves.first + lvLen g ≤ F.next ∧ g.leaves.first + lvLen g ≤ F.ns ∧
        ∀ j, g.leaves.first ≤ j → j < g.leaves.first + lvLen g → ¬ OnBytes.PscRun.Filled F j)
    (hJoin : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      Fwd (Dm.Rd l) 3 "join" u.1 v.1)
    (hOwn : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(3, "norm"), (3, "policy"), (3, "logits")], Fwd (Dm.Rd l) p.1 p.2 u.1 v.1)
    (hHs : H.small = smallReader) :
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
  have e : Dm.runs l kk r = runsOf .head kk r := by
    show runsAt Dm.links l kk r = runsOf .head kk r
    rw [hlinks]
    exact runsAt_of linksFull l .head hsub kk r
  rw [e] at hp
  obtain ⟨F, hF, hSz⟩ := led_mgAll Dm Mg Rch hM hl hsub z u hu hr hm
  obtain ⟨rs, gs, hd⟩ := id hR
  obtain ⟨G, Q⟩ := k3_digits_step_pass claim readers X codes shape a b' h hOk l hi hpc u.1 v.1 rs
    gs hd hF hSz
  obtain ⟨-, -, -, -, hLk, -, -⟩ :=
    k3_digits_step_leaves claim readers X codes shape a b' h hOk l hi hpc u.1 v.1 rs gs hd
  simp only [earlyOf, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hin
  obtain ⟨o, hw⟩ := hHere z u v hu hr hm hv hR
  rcases hin with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [runs_head.1] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rw [hRd]
    rcases hp with rfl | rfl
    · exact fwd_of_noSilent H lk 2 (by decide) (hrO z u v hu hr hm hv hR)
        (objects_fwd (noSilent H) lk 2 (Desc.K3.seatCalls claim) hA Q hLk rfl hfO)
    · exact fwd_of_noSilent H lk 2 (by decide) (hrG z u v hu hr hm hv hR)
        (guests_fwd (noSilent H) lk 2 Q rfl hfG)
  · rw [runs_head.2.1] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    rw [hRd]
    refine fwd_of_noSilent H lk 2 (by decide) (hrP z u v hu hr hm hv hR)
      (planes_fwd' (noSilent H) lk 2 (Desc.K3.seatCalls claim) hA Q hLk lm
        (callerReaders (planesAt iU3)) (fun r hr0 => ?_) (hWin z u v hu hr hm hv hR F hF) rfl hfP)
    rw [k3_digits_step_headReaders claim readers X codes shape a b' h hOk l hi hpc u.1 v.1 rs gs hd
      hw hF hSz iU3]
    exact hr0
  · rw [runs_head.2.2.1] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact hJoin z u v hu hr hm hv hR
  · rw [runs_head.2.2.2.1] at hp
    exact hOwn z u v hu hr hm hv hR p hp
  · rw [runs_head.2.2.2.2.1] at hp
    cases hp
  · rw [runs_head.2.2.2.2.2.1] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    rw [hRd]
    exact small_fwd H lk 5 fun R hR0 => by
      rw [hHs] at hR0 ⊢
      rw [k3_digits_step_smallReader claim readers X codes shape a b' h hOk l hi hpc u.1 v.1 rs gs
        hd]
      exact hR0

/-- **THE ROW AT THE OUTPUT HEAD's SEGMENT.** -/
theorem ridesAtR_digits_head (seats : List (ℕ × ℕ)) (es : Dm.smp = smpNamed Dm.cs seats)
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
    (iU3 lm : ℕ)
    (hfO : ∀ n r, (statesOfLink lk 2).find? (fun x => x.1 == "objects") = some (n, r) →
      r = objectsRun (Desc.K3.seatCalls claim))
    (hfG : ∀ n r, (statesOfLink lk 2).find? (fun x => x.1 == "guests") = some (n, r) →
      r = guestsRun ([] : List (Desc.First.Look.Guest Desc.First.S Desc.Claim)))
    (hfP : ∀ n r, (statesOfLink lk 2).find? (fun x => x.1 == "planes") = some (n, r) →
      r = Desc.K3.planesRun (Desc.K3.seatCalls claim) lm (callerReaders (planesAt iU3)))
    (hrO : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      (readerOf (statesOfLink lk) 2 "objects" u.1).isSome = true)
    (hrG : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      (readerOf (statesOfLink lk) 2 "guests" u.1).isSome = true)
    (hrP : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      (readerOf (statesOfLink lk) 2 "planes" u.1).isSome = true)
    (hHere : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∃ o, u.1.here = .head o)
    (hWin : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ F, u.1.fork? = some F → ∀ g, (Desc.K3.seatCalls claim).heard u.1 = some g →
        g.leaves.first + lvLen g ≤ F.next ∧ g.leaves.first + lvLen g ≤ F.ns ∧
        ∀ j, g.leaves.first ≤ j → j < g.leaves.first + lvLen g → ¬ OnBytes.PscRun.Filled F j)
    (hJoin : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      Fwd (Dm.Rd l) 3 "join" u.1 v.1)
    (hOwn : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(3, "norm"), (3, "policy"), (3, "logits")], Fwd (Dm.Rd l) p.1 p.2 u.1 v.1)
    (hHs : H.small = smallReader)
    (hWt : ∀ kk,
      openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) (k3K l true)
        (.forms l kk "weights") →
      ¬ insQ linksFull PS (k3K l true) (.forms l kk "weights") →
      ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ w, Dm.wt l (z, v.1) (strsOf Fr v.2) w → Dm.wt l (z, u.1) (strsOf Fr u.2) w) :
    RidesAtR Dm.N (mgAll Dm Mg) Rch (k3K l true) q b' :=
  ridesAtR_digits_step Dm Mg seats es hD hd Rch (k3K l true) l q b' ha hK hp7 hi hback claim
    readers codes shape h hOk hpc hlook hsh hj hReq hHead (led_mgAll Dm Mg Rch hM hl hsub)
    (fwd_step_head Dm Mg Rch H lk claim readers codes shape a b' h hOk hi hpc hM hlinks hl hsub
      hRd hA iU3 lm hfO hfG hfP hrO hrG hrP hHere hWin hJoin hOwn hHs)
    hWt

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.fwd_of_noSilent
#print axioms VerifiableInference.OnPublicFiles.fwd_step_att
#print axioms VerifiableInference.OnPublicFiles.ridesAtR_digits_att
#print axioms VerifiableInference.OnPublicFiles.fwd_step_head
#print axioms VerifiableInference.OnPublicFiles.ridesAtR_digits_head
