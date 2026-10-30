-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
fwd_step_head_hole, ridesAtR_digits_head_hole: no parameters Dm and no
state are shown here at which their premises hold together.
Johnson/Desc/Sound/MgAt/K3RidesDigFwd3.lean: the kind "lookup" (K3) AT THE COMPOSED MEANING mgAll:
THE PREMISE hFwd OF ridesAtR_digits_step, IN ITS OWN TEXT, AT THE DIGITS' BORDER OF THE OUTPUT
HEAD's SEGMENT, A SECOND TIME: fwd_step_head (K3RidesDigFwd2.lean) WITHOUT ITS PREMISE hrP ("the
run planes itself answers at the state in front"): at the description's own holes (H = holesAt X
mH l lk) the run "planes" goes forward whichever of the run and the hole answers: planes_fwd_head
(Johnson/Top/H/Keep/HeadHoleFwd.lean), with SamePlanes across the whole seated accept
(k3_digits_step_samePlanes: Johnson/Desc/First/Look/K3DigitsCallersStay.lean). Statements and
proofs: joinings. No error term. NO SOUNDNESS IS CLAIMED.

OBJECT, LETTERS: those of K3RidesDigFwd2.lean; mH.
Used by K03RidesDigHeadHole.lean (Johnson/P5J/).
IMPORTS:
  Johnson/Desc/Sound/MgAt/K3RidesDigFwd2.lean;
  Johnson/Top/H/Keep/HeadHoleFwd.lean.
  Compiled with the whole library.

Main names: `fwd_step_head_hole`, `ridesAtR_digits_head_hole`.

WHAT COMES IN hrP's PLACE: hmH, hH: terms (hH pays hHs too: the first hole of holesAt is
smallReader by its make) · hOb: what the ledger behind still owes the ledger in front owed: WITH
THE PREMISES: across the whole seated accept IT IS NOT SHOWN (at the kind's own decision:
k3_digits_hob, HeadHoleFwd.lean). (Where this and
lean/THEOREM.md differ, the page holds.) All else as in K3RidesDigFwd2.lean.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3RidesDigFwd2
import Johnson.Top.H.Keep.HeadHoleFwd

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Meaning runsOf start openSets)
open VerifiableInference.Desc.K9 (readersOfLink statesOfLink LinkHoles readerOf smallReader holesAt)
open VerifiableInference.Desc.First.Att.P (readersOfO keysOfO)
open VerifiableInference.Desc.Kinds.Head (planesAt callerReaders)
open VerifiableInference.Reads.Pass (Fwd)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-! ## The output head's segment, with the description's own holes -/

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
theorem fwd_step_head_hole
    (mH : ℕ) (hmH : (l == mH) = true) (hH : H = holesAt X mH l lk) (iU3 lm : ℕ)
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
    (hOb : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ F G, K3Pass u.1 v.1 F G → ∀ i, Desc.K3.unpaid G i = true → Desc.K3.unpaid F i = true)
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
      ∀ p ∈ [(3, "norm"), (3, "policy"), (3, "logits")], Fwd (Dm.Rd l) p.1 p.2 u.1 v.1) :
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
  have hHs : H.small = smallReader := by
    rw [hH]
    rfl
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
    rw [hH]
    exact planes_fwd_head X mH l hmH lk 2 claim hA Q
      (k3_digits_step_samePlanes claim readers X codes shape a b' h hOk l hi hpc u.1 v.1 rs gs hd)
      hLk (hOb z u v hu hr hm hv hR F G Q) lm iU3 (hWin z u v hu hr hm hv hR F hF) hfP hw
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
theorem ridesAtR_digits_head_hole (seats : List (ℕ × ℕ)) (es : Dm.smp = smpNamed Dm.cs seats)
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
    (mH : ℕ) (hmH : (l == mH) = true) (hH : H = holesAt X mH l lk) (iU3 lm : ℕ)
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
    (hOb : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ F G, K3Pass u.1 v.1 F G → ∀ i, Desc.K3.unpaid G i = true → Desc.K3.unpaid F i = true)
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
    (fwd_step_head_hole Dm Mg Rch H lk claim readers codes shape a b' h hOk hi hpc hM hlinks hl hsub
      hRd hA mH hmH hH iU3 lm hfO hfG hfP hrO hrG hOb hHere hWin hJoin hOwn)
    hWt

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.fwd_step_head_hole
#print axioms VerifiableInference.OnPublicFiles.ridesAtR_digits_head_hole
