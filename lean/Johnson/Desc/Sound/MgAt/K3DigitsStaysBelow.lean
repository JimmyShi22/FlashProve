-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/Sound/MgAt/K3DigitsStaysBelow.lean: THE LOOKUP ON THE DIGITS OF A LAYERS' LINK: A
JOINING OF K3's AND K4's LAWS: (1) an accept of the whole seated sub-protocol gives
K4StaysBelow (Johnson/Road/K4/InT/RunsSameK4.lean): the state behind stands in a layers' link with
the same "what K4's hearing returned" (k3_digits_step_layStays,
Johnson/Desc/First/Look/K3DigitsOwnStays.lean), its ledger is a later one over the same arrays
(K3Pass's later, sizedG, trees: Johnson/Top/H/Keep/FormsPassK3.lean, over k3_digits_step_pass,
Johnson/Desc/First/Look/K3DigitsPass.lean), nothing turns below the next slot in front
(k3_digits_step_sameBelow, Johnson/Desc/First/Look/K3DigitsSameBelow.lean); that the state in front
stands in a layers' link, and that K4's three windows lie below its next slot, are premises. (2) THE
PREMISE hOwn OF ridesAtR_digits_layers (Johnson/Desc/Sound/MgAt/K3RidesDigFwd.lean), IN ITS OWN
TEXT, at the composed meaning mgAll: K4's runs "front" and "back" go forward over the accept: by
link_fwd, k4_runSame_below (both in files named in (1)). By calls alone. NO SOUNDNESS IS CLAIMED.

OBJECT: K3.theStated's block at the digits' address of a layers' link; the readers of the link's
  runs "front" and "back".
Used by K03OwnFwdLayAt.lean (Johnson/P5J/) and K3DigitsStaysBelowFront.lean
  (Johnson/Desc/Sound/MgAt/).
LETTERS: those of MgAt/K3RidesDigFwd.lean; al: the layers' part of the state in front; o: what K4's
  hearing returned.

WHAT IS LEFT, BOOKED: fold fact, at the border in front of the digits: hWin: THE CONCLUSION OF
  wins_reached (Johnson/Road/K4/InT/WinsReached.lean) TO THE LETTER [read]: a layers' link
  is open, what K4's hearing returned is there, the ledger has its sizes, two of the three windows
  end at or below its next slot, and what was heard of the lookup on the calls is what K4's
  hearing holds · on the state in front: hsil (the link's second hole is silent at the two runs) ·
  term: hSt (StatesAt, Johnson/Road/K4/InT/Statement.lean, at the link's
  sub-protocol number 2, at "front" and "back", at every state: THE CONCLUSION OF
  statesAt_guarded, Johnson/Road/K4/InT/SeatTie.lean, TO THE LETTER [both read]; that theorem's own
  premises hb, hcl, hsame are the seat's), hRd, hM · test: hp7, the sort. PAID HERE: the two items
  on the lookup on the calls that hwin_of_onOut spends for the third window
  (callsItems_front_dig).

Main names: `closedRow_full`, `closedRow_head` (hi, hp7 tried by the kernel at the ledger's own
  place, with a negative test) · `runSame_congr` · `k4StaysBelow_of_digits` · `windows_of_leaves` ·
  `callsItems_front_dig` · `hOwn_of_below`.

Limits. A layers' link. At Cl := Desc.Claim in hOwn_of_below. closedRowB l is true for an empty
reason at every l at which the written list has no layers' link; closedRow_head shows that the
piece is not 7 at link 24, not that any link is a layers' link.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Road.K4.InT.RunsSameK4
import Johnson.Desc.First.Look.K3DigitsSameBelow
import Johnson.Desc.First.Look.K3DigitsOwnStays
import Johnson.Desc.First.Look.K3DigitsPass
import Johnson.Top.H.Keep.CallersStay
import Johnson.Desc.Sound.MgAt.K3RidesDigStep
import Johnson.Desc.Sound.MgAt.K3DigitsPlanesIt
import Johnson.Desc.Sound.MgAt.K3CallsOthers

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Pub Meaning pubSets shift)
open VerifiableInference.Desc.K9 (readersOfLink statesOfLink LinkHoles)
open VerifiableInference.Reads.Pass (Fwd)
open OnBytes.Road.K4.InT (K4StaysBelow k4_runSame_below StatesAt)
open OnBytes.Desc.First.K4 (Par)

/-- THE PREMISES ON CLOSED LETTERS, TRIED: at every layers' link of the written list the digits'
place (the ledger's own term) bears the link's number and the piece 7. -/
def closedRowB (l : ℕ) : Bool :=
  linksFull[l]? != some ModelPart.layers ||
    (decide ((IM.k3Place l true).link = some l) && decide ((IM.k3Place l true).piece = 7))

set_option maxRecDepth 100000 in
theorem closedRow_full : (List.range 25).all closedRowB = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- A negative test: at the output head's link the piece is not 7. -/
theorem closedRow_head : decide ((IM.k3Place 24 true).piece = 7) = false := by decide +kernel

/-- RunSame reads a run at its first number, at the two states, alone. -/
theorem runSame_congr {r r' : ℕ → Desc.First.S → Except String (List Desc.Claim × Desc.First.S)}
    {s s' : Desc.First.S} (he : r 0 s = r' 0 s) (he' : r 0 s' = r' 0 s') (h : RunSame r' s s') :
    RunSame r s s' := by
  intro cl t F G h1 h2 h3
  rw [he] at h1
  obtain ⟨t', F', G', q1, q⟩ := h cl t F G h1 h2 h3
  exact ⟨t', F', G', by rw [he']; exact q1, q⟩

/-- **An accept of the whole seated sub-protocol at a layers' link gives K4StaysBelow.** -/
theorem k4StaysBelow_of_digits {Cl : Type} (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : Verify.Public) (codes : Codes)
    (shape : Params.ReqShape) (a : Desc.Place) (B : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hi : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i true)
    (s s₂ : Desc.First.S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (hd : B.decide s rs gs = .ok s₂)
    {al : Desc.First.LayOwn} (ha : s.here = .lay al) (hS : OnBytes.PscRun.Sized al.F)
    (hW : ∀ o, al.own = some o →
      o.H.tV.p.first + o.H.tV.p.walk.1.length ≤ al.F.next ∧
      o.H.fo.leaves.first + o.H.fo.leaves.walk.1.length ≤ al.F.next ∧
      o.wo.toWsMerged.p.first + o.wo.toWsMerged.p.walk.1.length ≤ al.F.next) :
    K4StaysBelow s s₂ := by
  have hF : s.fork? = some al.F := by simp [Desc.First.S.fork?, ha]
  obtain ⟨a', ha', hk⟩ :=
    k3_digits_step_layStays claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd al ha
  obtain ⟨G, Q⟩ :=
    k3_digits_step_pass claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd hF hS
  obtain ⟨G', hG', hB⟩ :=
    k3_digits_step_sameBelow claim readers X codes shape a B h hOk i hi hpc s s₂ rs gs hd hF hS
  have hFa : s₂.fork? = some a'.F := by simp [Desc.First.S.fork?, ha']
  obtain rfl : G = a'.F := Option.some.inj (Q.behind.symm.trans hFa)
  obtain rfl : G' = a'.F := Option.some.inj (hG'.symm.trans hFa)
  have hown : a'.own = al.own := congrArg (·.own) (hk al.tl al.F)
  exact ⟨⟨al, a', ha, ha', hown, hS,
    ⟨Q.later.next, Q.later.ns, fun _ => Q.sizedG, Q.later.keep⟩, Q.trees, hB, hW⟩⟩

/-- **The three windows, the leaves' one from K3's own law.** hTie: what K4's hearing
returned holds the very lookup that the state keeps as heard. pc: the parameters of the lookup on
the calls. -/
theorem windows_of_leaves {pc : Desc.First.Look.P} (hdc : pc.digits = false) {s : Desc.First.S}
    {al : Desc.First.LayOwn} (ha : s.here = .lay al) (hO : Desc.K3.k3OnOut pc s = true)
    (hL : k3LeftOnItem pc s)
    (hTie : ∀ o, al.own = some o → s.lookHeard? = some o.H.fo)
    (hW2 : ∀ o, al.own = some o →
      o.H.tV.p.first + o.H.tV.p.walk.1.length ≤ al.F.next ∧
      o.wo.toWsMerged.p.first + o.wo.toWsMerged.p.walk.1.length ≤ al.F.next) :
    ∀ o, al.own = some o →
      o.H.tV.p.first + o.H.tV.p.walk.1.length ≤ al.F.next ∧
      o.H.fo.leaves.first + o.H.fo.leaves.walk.1.length ≤ al.F.next ∧
      o.wo.toWsMerged.p.first + o.wo.toWsMerged.p.walk.1.length ≤ al.F.next := by
  intro o ho
  have hF : s.fork? = some al.F := by simp [Desc.First.S.fork?, ha]
  exact ⟨(hW2 o ho).1, (hwin_of_onOut hdc hF hO hL o.H.fo (hTie o ho)).1, (hW2 o ho).2⟩

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)
  (H : LinkHoles) (lk : Desc.Link Desc.First.S Desc.Claim)
  (claim : Aff → Desc.Claim) (readers : ℕ → Option (Desc.K3.Readers Desc.First.S))
  (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place)
  (b' : Desc.Block Desc.First.S Desc.Claim) (pK : Par)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- **The two items on the lookup on the calls, in front of the digits' place of a link of any
sort**: off the promise in front: lookOut is among the items whose test holds there and leftOn
among those whose sentence holds there (planesFront_mgMore, by the kernel:
Johnson/Desc/Sound/MgAt/K3DigitsPlanesIt.lean, in whose hPlanesIt_dig these steps stand inline); at
mgAll the two are the kind's own (K3At's lookOut, pLeftOn). -/
theorem callsItems_front_dig (hM : Mg.more = {}) {l : ℕ} (hl : l < 25) {sub : ModelPart}
    (hsub : linksFull[l]? = some sub) (hX : Desc.K3.pieceAt X l true = 7 + shift sub) (z : P)
    (u : Desc.First.S × Fr.E.Str)
    (hu : onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u)
    (hun : u.1.failed = none) :
    ∃ pc : Desc.First.Look.P, pc.digits = false ∧ Desc.K3.k3OnOut pc u.1 = true ∧
      k3LeftOnItem pc u.1 := by
  have eM : (mgAll Dm Mg).more = mgMore := mgAll_more_closed Dm Mg hM
  have hQ : ∀ p ∈ (pubSets (mgAll Dm Mg).more linksFull PS)[k3K l true]?.getD [],
      (mgAll Dm Mg).pubP p (z, u.1) := by
    obtain ⟨-, hm | ⟨-, -, -, h4⟩⟩ := hu
    · exact absurd hun hm
    · exact h4
  have hfront := onQ_front hu hun
  rw [eM] at hfront
  have hFr := List.all_eq_true.1 planesFront_mgMore l (List.mem_range.2 hl)
  unfold planesFrontRowB at hFr
  rw [Bool.and_eq_true] at hFr
  have m1 : Pub.lookOut l (IM.k3Place l false).piece ∈ frontDig mgMore l := by
    simpa using hFr.1
  have m2 : Pub.leftOn l ∈ (pubSets mgMore linksFull PS)[k3K l true]?.getD [] := by
    simpa using hFr.2
  have ePc : (IM.k3Place l false).piece = Desc.K3.pieceAt X l false := by
    have a1 := pieceAt_calls X l
    obtain ⟨s2, hs2, a2, -⟩ := K3Lot.k03_sub_full l hl
    obtain rfl : s2 = sub := Option.some.inj (hs2.symm.trans hsub)
    omega
  have hLfAt : k3LeftOnItemAt X l u.1 := by
    have h0 := hQ _ (by rw [eM]; exact m2)
    rw [(k3At_mgAll Dm Mg).pLeftOn] at h0
    exact h0
  obtain ⟨pc, hpcAt, hLf⟩ := hLfAt
  have hO : Desc.K3.k3OnOut pc u.1 = true := by
    have h0 := hfront _ m1
    rw [ePc, (k3At_mgAll Dm Mg).lookOut] at h0
    unfold k3OnOutAt at h0
    rw [hpcAt] at h0
    exact h0
  have hdc : pc.digits = false := by
    unfold placeAt at hpcAt
    obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 hpcAt
    rfl
  exact ⟨pc, hdc, hO, hLf⟩

/-- **hOwn, in its own text.** hWin: wins_reached's conclusion, to the letter, at the
states that the promise and Rch name. -/
theorem hOwn_of_below
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
    {l : ℕ} (hi : a.link = some l) (hpc : a.piece = Desc.K3.pieceAt X l true)
    (hp7 : a.piece = 7) (hM : Mg.more = {}) (hl : l < 25)
    (hsub : linksFull[l]? = some ModelPart.layers) (hRd : Dm.Rd l = readersOfLink H lk)
    (hWin : ∀ (z : P) (u : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      ∃ (al : Desc.First.LayOwn) (o : OnBytes.Model.Layer.Own), u.1.here = .lay al ∧
        al.own = some o ∧ OnBytes.PscRun.Sized al.F ∧
        o.H.tV.p.first + o.H.tV.p.walk.1.length ≤ al.F.next ∧
        o.wo.toWsMerged.p.first + o.wo.toWsMerged.p.walk.1.length ≤ al.F.next ∧
        u.1.lookHeard? = some o.H.fo)
    (hsil : ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(2, "front"), (2, "back")], H.silent p.1 p.2 u.1 = none)
    (hSt : ∀ name, name = "front" ∨ name = "back" → ∀ t, StatesAt (statesOfLink lk) 2 pK name t) :
    ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(2, "front"), (2, "back")], Fwd (Dm.Rd l) p.1 p.2 u.1 v.1 := by
  intro z u v hu hr hm hv hR p hp
  obtain ⟨al, o, hal, ho, hSz, w1, w3, hT⟩ := hWin z u hu hr hm
  obtain ⟨pc, hdc, hO, hL⟩ := callsItems_front_dig Dm Mg hM hl hsub
    (show Desc.K3.pieceAt X l true = 7 + shift ModelPart.layers from hpc.symm.trans hp7) z u hu
    (Classical.not_not.1 hm)
  have hW := windows_of_leaves hdc hal hO hL
    (fun o' ho' => by
      obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
      exact hT)
    (fun o' ho' => by
      obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
      exact ⟨w1, w3⟩)
  obtain ⟨rs, gs, hd⟩ := id hR
  have K := k4StaysBelow_of_digits claim readers X codes shape a b' h hOk l hi hpc u.1 v.1 rs gs hd
    hal hSz hW
  have hs := hsil z u v hu hr hm hv hR p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rw [hRd]
  rcases hp with rfl | rfl
  · exact link_fwd H lk 2 (by decide) hs fun nm r hfr => by
      obtain ⟨y, runC, hy, hC, e1⟩ := hSt "front" (Or.inl rfl) u.1
      obtain ⟨y', runC', hy', hC', e2⟩ := hSt "front" (Or.inl rfl) v.1
      obtain rfl : y = (nm, r) := Option.some.inj (hy.symm.trans hfr)
      obtain rfl : y' = (nm, r) := Option.some.inj (hy'.symm.trans hfr)
      obtain rfl : runC' = runC := Option.some.inj (hC'.symm.trans hC)
      exact runSame_congr e1 e2 (k4_runSame_below (Or.inl rfl) hC K)
  · exact link_fwd H lk 2 (by decide) hs fun nm r hfr => by
      obtain ⟨y, runC, hy, hC, e1⟩ := hSt "back" (Or.inr rfl) u.1
      obtain ⟨y', runC', hy', hC', e2⟩ := hSt "back" (Or.inr rfl) v.1
      obtain rfl : y = (nm, r) := Option.some.inj (hy.symm.trans hfr)
      obtain rfl : y' = (nm, r) := Option.some.inj (hy'.symm.trans hfr)
      obtain rfl : runC' = runC := Option.some.inj (hC'.symm.trans hC)
      exact runSame_congr e1 e2 (k4_runSame_below (Or.inr rfl) hC K)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.closedRow_full
#print axioms VerifiableInference.OnPublicFiles.closedRow_head
#print axioms VerifiableInference.OnPublicFiles.runSame_congr
#print axioms VerifiableInference.OnPublicFiles.k4StaysBelow_of_digits
#print axioms VerifiableInference.OnPublicFiles.windows_of_leaves
#print axioms VerifiableInference.OnPublicFiles.callsItems_front_dig
#print axioms VerifiableInference.OnPublicFiles.hOwn_of_below
