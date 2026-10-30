-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/Sound/MgAt/K3CallsObjIn.lean: THE LOOKUP ON A LINK's CALLS AT THE COMPOSED MEANING
mgAll: THE ONE NEW PUBLIC TEST BEHIND THE LOOKUP ON THE CALLS THAT IS NEITHER THE KIND's OWN NOR A
CALLER's: formsInT l 2 "objects" (the premise hObj of othersPub_att_mgAll, othersPub_lay_mgAll:
Johnson/Desc/Sound/MgAt/K3CallsOthers.lean), out of objects_formsInT
(Johnson/Top/H/Keep/FormsInTObjects.lean): at mgAll the test is the forms' layer's (pubAll_formsInT:
rfl); what was heard, its rows' names and the ledger's sizes behind the accept are k3_calls_made's
and decide_named's; that the state behind has a part is the writers' text. By calls alone. NO
SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: the composed public test pubAll at formsInT l 2 "objects".
Used by K3CallsObjInPc.lean, K3CallsPaid.lean, K3DigitsObjIn.lean (Johnson/Desc/Sound/MgAt/): the
  two small lemmas alone. objIn_mgAll has no caller.
LETTERS: those of MgAt/K3CallsOthers.lean and of K3CallsObjects.lean (pr, H, lk, pass).

WHAT IS LEFT, BOOKED: test or term: hruns (mgAll's map of names sends the run to itself
alone)
  · term: hA, hlink, hpass, hfind · accept with a fold fact: hmask (the mask row's message is sent
  and the book seats it among the link's own) · accept: hmerge (no kept row names the slot of the
  merge's end value) · onIn (the kind's test in front: paid in K3CallsOthers.lean's way).

Main names: `link_some_of_fork`, `tl_some_of_fork` · `objIn_mgAll`.

Limits. At Cl := Desc.Claim. The piece 2 (not the head's).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3CallsMean
import Johnson.Desc.First.Look.K3CallsMade
import Johnson.Top.H.Keep.FormsInTObjects
import Johnson.Top.H.Keep.FormsPassK3
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look.Stored (oWc wOfC msgWc smpWc strWc)
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn pubFit shift sameStand bookFit pubStep pubRowM stepOpen pubOfItems)
open VerifiableInference.Desc (Link)
open VerifiableInference.Desc.K9 (segAt? readersOfLink statesOfLink LinkHoles maskSeat mergeOf)
open VerifiableInference.Desc.First (pubAll)
open _root_.Meaning (linkTieB BaseSegF seatBy fLay hidAtF ReadsOne sizesFit)

/-- Where a ledger is open, a link's context is. -/
theorem link_some_of_fork {s : Desc.First.S} {F : Fork} (h : s.fork? = some F) :
    ∃ L, s.link? = some L := by
  unfold Desc.First.S.fork? at h
  unfold Desc.First.S.link?
  cases hh : s.here with
  | lay a => exact ⟨_, rfl⟩
  | att a => exact ⟨_, rfl⟩
  | head a =>
    rw [hh] at h
    by_cases ho : a.opened = true
    · exact ⟨a.L, if_pos ho⟩
    · have h' : (if a.opened = true then some a.F else none) = some F := h
      rw [if_neg ho] at h'
      cases h'
  | between => rw [hh] at h; cases h
  | fin _ => rw [hh] at h; cases h
  | mem _ => rw [hh] at h; cases h

/-- And the approximate range proof's parameters are. -/
theorem tl_some_of_fork {s : Desc.First.S} {F : Fork} (h : s.fork? = some F) :
    s.tl?.isSome = true := by
  unfold Desc.First.S.fork? at h
  unfold Desc.First.S.tl?
  cases hh : s.here with
  | lay a => rfl
  | att a => rfl
  | head a =>
    rw [hh] at h
    by_cases ho : a.opened = true
    · show (if a.opened = true then some a.tl else none).isSome = true
      rw [if_pos ho]
      rfl
    · have h' : (if a.opened = true then some a.F else none) = some F := h
      rw [if_neg ho] at h'
      cases h'
  | between => rw [hh] at h; cases h
  | fin _ => rw [hh] at h; cases h
  | mem _ => rw [hh] at h; cases h

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (claim : Aff → Desc.Claim)
  (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes) (shape : Params.ReqShape)
  {k l : ℕ} {x : Desc.First.Look.Place} {a : Desc.Place}
  {b' : Desc.Block Desc.First.S Desc.Claim}
  {q : Piece (ckP .two) Fr (P × Desc.First.S) Desc.Claim
    (Desc.Wit (CellsQ rows cols) Tok MsgT)}
  {pr : ℕ} {H : LinkHoles} {lk : Link Desc.First.S Desc.Claim}
  {pass : Desc.First.S → Desc.First.S → Prop}

local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **formsInT l 2 "objects" holds behind.** -/
theorem objIn_mgAll
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
    (hback : q.back = []) (hla : a.link = some l)
    (hpcX : a.piece = Desc.K3.pieceAt X l false) (hlook : lookAt X l false = some x)
    (hsP : (theP).shape = some x.fs)
    (onIn : ∀ (z : P) (u : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → Desc.K3.k3OnIn theP u.1 = true)
    (hruns : Dm.runs l 2 "objects" = [(pr, "objects")])
    (hA : AtS2 (Desc.K3.seatCalls claim)) (hlink : Dm.Rd l = readersOfLink H lk)
    (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink lk pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun (Desc.K3.seatCalls claim)))
    (hmask : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      ∀ c, segAt? v.1 = some c → (maskSeat (Dm.N.sent l 0) c).isSome = true)
    (hmerge : ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      ∀ g, v.1.lookHeard? = some g → ∀ f ∈ g.rows.toList, ∀ y ∈ f.slots.toList,
        mergeOf v.1 ≠ some y.1) :
    ∀ B', SeatOf b' B' → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      (mgAll Dm Mg).pub (.formsInT l 2 "objects") (z, v.1) = true := by
  intro B' hB z u v hu hr hf hy _
  have e : placeAt X l false = some theP := by
    unfold placeAt
    rw [hlook]
    rfl
  obtain ⟨piece, laid, before, guests, rs, cols, -, hd⟩ :=
    seat_yes claim readers codes shape h hOk hla hpcX e hback B' hB u v hy
  obtain ⟨F, F', g, rs', hF, hz, -, -, -, -, hF', hg, L, -⟩ :=
    k3_calls_made claim piece laid before theP guests u.1 v.1 rs cols hsP hd (onIn z u hu hr hf)
  obtain ⟨F1, y, hF1, hn1, e1, hN⟩ :=
    decide_named (Desc.K3.seatCalls claim) piece laid before theP guests u.1 v.1 rs cols hd
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans hF1)
  have hsome : ((Desc.K3.seatCalls claim).fork u.1).isSome = true := by
    rw [hF1]
    rfl
  have hg1 : (Desc.K3.seatCalls claim).heard v.1 = some y.1 := by
    rw [e1]
    exact Desc.K3.seatCalls_reads claim _ _ _ hsome hn1
  have hF1' : (Desc.K3.seatCalls claim).fork v.1 = some y.2 := by
    rw [e1]
    exact seatCalls_keeps claim _ _ _ hsome hn1
  have ey1 : y.1 = g := Option.some.inj (hg1.symm.trans hg)
  have ey2 : y.2 = F' := Option.some.inj (hF1'.symm.trans hF')
  have hNm := (hN hz).rows
  rw [ey1, ey2] at hNm
  obtain ⟨Lc, hLc⟩ := link_some_of_fork hF'
  obtain ⟨c, hc, -, hcF, -, -⟩ := segAt_make hLc hF' (tl_some_of_fork hF')
  show pubAll Dm.pubD Mg.pub (.formsInT l 2 "objects") (z, v.1) = true
  show ((Dm.runs l 2 "objects").all fun p =>
    Desc.K9.formsInT (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 v.1) = true
  rw [hruns, hlink]
  show (Desc.K9.formsInT (readersOfLink H lk) (Dm.N.sent l 0) pr "objects" v.1 && true) = true
  rw [Bool.and_true]
  exact objects_formsInT H lk pr (Dm.N.sent l 0) (Desc.K3.seatCalls claim) hA pass hpass hfind hc
    hg (by rw [hcF]; exact hNm) (by rw [hcF]; exact L.padLeft.fit)
    (hmask B' hB z u v hu hr hf hy c hc) (hmerge B' hB z u v hu hr hf hy g hg)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.link_some_of_fork
#print axioms VerifiableInference.OnPublicFiles.tl_some_of_fork
#print axioms VerifiableInference.OnPublicFiles.objIn_mgAll
