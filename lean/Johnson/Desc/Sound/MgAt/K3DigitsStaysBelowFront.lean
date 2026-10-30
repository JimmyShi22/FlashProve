-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/Sound/MgAt/K3DigitsStaysBelowFront.lean: THE LOOKUP ON THE DIGITS OF A LAYERS' LINK:
K4's RUNS "front" AND "back" GO FORWARD OVER AN ACCEPT OF THE WHOLE SEATED SUB-PROTOCOL, WITHOUT THE
PROMISE BEHIND AMONG THE HANDS. hOwn_of_below (Johnson/Desc/Sound/MgAt/K3DigitsStaysBelow.lean) ends
in the text of the premise hOwn of ridesAtR_digits_layers, which hands over the table's promise at
the border behind; its proof spends that hand only to call its own premise hsil. Whoever SHOWS the
promise behind (the ledger's items on the forms) has no such hand. Here: hOwn_of_below_front: the
same end, its hands the promise IN FRONT, Rch, "no mark", the accept, and "the link's second hole is
silent at the two runs at the state in front" as a hand on that state; hOwn_of_below_holes: that
last hand struck where the holes are the description's own off the output head's link
(holesAt_silent_none, Johnson/Desc/Sound/MgAt/K3DigitsFormsPlanes.lean); hOwn_of_below_again: THE
ELDER THEOREM's OWN STATEMENT, TO THE LETTER, AS A COROLLARY: so that Lean holds that nothing is
lost. By calls alone. NO SOUNDNESS IS CLAIMED.

OBJECT: K3.theStated's block at the digits' address of a layers' link; the readers of the link's
  runs "front" and "back".
Used by K03OwnFwdLayFront.lean (Johnson/P5J/).
LETTERS: those of MgAt/K3DigitsStaysBelow.lean; mH: the output head's link's number.

WHAT IS LEFT, BOOKED: as in MgAt/K3DigitsStaysBelow.lean: hWin (fold fact) · hSt, hRd, hM (terms) ·
hp7,
  the sort (tests: tried there by the kernel) · in hOwn_of_below_holes: hne ((l == mH) = false).

Main names: `hOwn_of_below_front` · `hOwn_of_below_holes` · `hOwn_of_below_again`.

Limits. A layers' link. At Cl := Desc.Claim.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3DigitsStaysBelow
import Johnson.Desc.Sound.MgAt.K3DigitsFormsPlanes

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
open VerifiableInference.Desc.K9 (readersOfLink statesOfLink LinkHoles holesAt)
open VerifiableInference.Reads.Pass (Fwd)
open OnBytes.Road.K4.InT (K4StaysBelow k4_runSame_below StatesAt)
open OnBytes.Desc.First.K4 (Par)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  {Fr : VerifiableInference.Desc.Sound.Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)
  (H : LinkHoles) (lk : Desc.Link Desc.First.S Desc.Claim)
  (claim : Aff → Desc.Claim) (readers : ℕ → Option (Desc.K3.Readers Desc.First.S))
  (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place)
  (b' : Desc.Block Desc.First.S Desc.Claim) (pK : Par)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- **The two runs go forward: no promise behind among the hands.** -/
theorem hOwn_of_below_front
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
    (hSt : ∀ name, name = "front" ∨ name = "back" → ∀ t, StatesAt (statesOfLink lk) 2 pK name t) :
    ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none → StepRel b' u.1 v.1 →
      (∀ p ∈ [(2, "front"), (2, "back")], H.silent p.1 p.2 u.1 = none) →
      ∀ p ∈ [(2, "front"), (2, "back")], Fwd (Dm.Rd l) p.1 p.2 u.1 v.1 := by
  intro z u v hu hr hm hR hsil p hp
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
  have hs := hsil p hp
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

/-- **The same where the holes are the description's own, off the output head's link: the hand on
the second hole struck.** -/
theorem hOwn_of_below_holes {mH : ℕ}
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
    {l : ℕ} (hi : a.link = some l) (hpc : a.piece = Desc.K3.pieceAt X l true)
    (hp7 : a.piece = 7) (hM : Mg.more = {}) (hl : l < 25)
    (hsub : linksFull[l]? = some ModelPart.layers) (hne : (l == mH) = false)
    (hRd : Dm.Rd l = readersOfLink (holesAt X mH l lk) lk)
    (hWin : ∀ (z : P) (u : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      ∃ (al : Desc.First.LayOwn) (o : OnBytes.Model.Layer.Own), u.1.here = .lay al ∧
        al.own = some o ∧ OnBytes.PscRun.Sized al.F ∧
        o.H.tV.p.first + o.H.tV.p.walk.1.length ≤ al.F.next ∧
        o.wo.toWsMerged.p.first + o.wo.toWsMerged.p.walk.1.length ≤ al.F.next ∧
        u.1.lookHeard? = some o.H.fo)
    (hSt : ∀ name, name = "front" ∨ name = "back" → ∀ t, StatesAt (statesOfLink lk) 2 pK name t) :
    ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none → StepRel b' u.1 v.1 →
      ∀ p ∈ [(2, "front"), (2, "back")], Fwd (Dm.Rd l) p.1 p.2 u.1 v.1 :=
  fun z u v hu hr hm hR =>
    hOwn_of_below_front Dm Mg Rch (holesAt X mH l lk) lk claim readers codes shape a b' pK h hOk hi
      hpc hp7 hM hl hsub hRd hWin hSt z u v hu hr hm hR
      fun p _ => holesAt_silent_none X hne lk p.1 p.2 u.1

/-- **The elder theorem's own statement, to the letter, as a corollary.** -/
theorem hOwn_of_below_again
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
      ∀ p ∈ [(2, "front"), (2, "back")], Fwd (Dm.Rd l) p.1 p.2 u.1 v.1 :=
  fun z u v hu hr hm hv hR =>
    hOwn_of_below_front Dm Mg Rch H lk claim readers codes shape a b' pK h hOk hi hpc hp7 hM hl hsub
      hRd hWin hSt z u v hu hr hm hR (hsil z u v hu hr hm hv hR)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hOwn_of_below_front
#print axioms VerifiableInference.OnPublicFiles.hOwn_of_below_holes
#print axioms VerifiableInference.OnPublicFiles.hOwn_of_below_again
