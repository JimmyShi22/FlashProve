-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
No place of a stored set is known at which all premises hold together.
Johnson/Desc/Sound/MgAt/K3DigitsFormsLive.lean: the lookup on the digits of a segment's approximate
range proof: OF THE TESTS formsIn THAT STAND BEHIND THE DIGITS' SUB-PROTOCOL (keptDigits, newDigits:
MgAt/K3DigitsSorted.lean) THREE ARE IDLE AT THE COMPOSED MEANING: the table's name stands for no run
of the driver's, so the test is true outright: formsIn l 2 "planes" and formsIn l 2 "join" at a
layers' segment, formsIn l 4 "weights" at the output head's. So the builder's one proof debt hForms
is asked at the live items alone. NO RESULT ON THE PROTOCOL.

Main names.
  formsIn_idle: where the table's map of names lists no run (runsOf sub k r = []), the composed test
    at formsIn l k r is true at every state.
  liveForms l sub: the items formsIn of the two written lists whose name stands for a run: four at a
    layers' segment, six at an attention segment, six at the output head's.
  forms_of_live: the tests at liveForms give the tests at all formsIn items of the two lists.
  digOwed_live: digOwed_forms (MgAt/K3DigitsOwedForms.lean) with hForms asked at liveForms alone.
HOW. runsAt_of, runs_layers, runs_head (Johnson/Desc/Sound/MgAt/Runs.lean);
pubAll_formsIn.
OBJECT. The composed public test at formsIn; the table's map of names.
Used by K3DigitsFormsJoin.lean and K3DigitsOwedSeven.lean (Johnson/Desc/Sound/MgAt/) and 1 more.
LETTERS. Those of digOwed_forms.


Compiled with the whole library.


The ledger's two texts othersPub, othersP at the digits bear two premises behind the promise in
front: «reached» (Rch k ((z, u.1), u.2)) and «no mark» (u.1.failed = none).

Limits. A rule over letters. Nothing on the live items.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3DigitsOwedForms
import Johnson.Desc.Sound.MgAt.Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open Cb.Fo.Pin
open VerifiableInference.Desc.First (ModelPart Pub Meaning shift pubFit pubSets pubStep pubRowM pubOfItems
  stepOpen openSets start sampledIn bookFit runsOf pubAll_formsIn)
open VerifiableInference.Desc.K9 (readersOfLink statesOfLink LinkHoles)

/-- The items formsIn of the two written lists whose name stands for a run. -/
def liveForms (l : ℕ) : ModelPart → List Pub
  | .layers => [.formsIn l 2 "objects", .formsIn l 3 "own", .formsIn l 5 "small",
      .formsIn l 7 "objects"]
  | .attention => [.formsIn l 2 "objects", .formsIn l 2 "planes", .formsIn l 2 "join",
      .formsIn l 3 "own", .formsIn l 5 "small", .formsIn l 7 "objects"]
  | .head => [.formsIn l 3 "objects", .formsIn l 3 "planes", .formsIn l 4 "join",
      .formsIn l 4 "own", .formsIn l 6 "small", .formsIn l 8 "objects"]

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

local notation "WT" => Desc.Wit (CellsQ rows cols) Tok MsgT
local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- **An idle name's test is true.** -/
theorem formsIn_idle (hlinks : Dm.links = linksFull) {l : ℕ} {sub : ModelPart}
    (hsub : linksFull[l]? = some sub) {k : ℕ} {r : String} (he : runsOf sub k r = [])
    (a : P × Desc.First.S) : (mgAll Dm Mg).pub (.formsIn l k r) a = true := by
  rw [mgAll_pub, pubAll_formsIn]
  have e : Dm.pubD.runs l k r = [] := by
    show runsAt Dm.links l k r = []
    rw [hlinks, runsAt_of linksFull l sub hsub k r]
    exact he
  rw [e]
  rfl

/-- **The live items give all.** -/
theorem forms_of_live (hlinks : Dm.links = linksFull) {l : ℕ} {sub : ModelPart}
    (hsub : linksFull[l]? = some sub) (a : P × Desc.First.S)
    (h : ∀ r ∈ liveForms l sub, (mgAll Dm Mg).pub r a = true) :
    ∀ r ∈ keptDigits l sub ++ newDigits l sub, (∃ pc nm, r = .formsIn l pc nm) →
      (mgAll Dm Mg).pub r a = true := by
  intro r hr hf
  cases sub with
  | layers =>
    simp only [keptDigits, newDigits, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    · obtain ⟨_, _, e⟩ := hf
      cases e
    · obtain ⟨_, _, e⟩ := hf
      cases e
    · obtain ⟨_, _, e⟩ := hf
      cases e
    · obtain ⟨_, _, e⟩ := hf
      cases e
    · obtain ⟨_, _, e⟩ := hf
      cases e
    · obtain ⟨_, _, e⟩ := hf
      cases e
    · exact h _ (by simp [liveForms])
    · exact formsIn_idle Dm Mg hlinks hsub runs_layers.2.2.2.2.1 a
    · exact formsIn_idle Dm Mg hlinks hsub runs_layers.2.2.2.2.2 a
    · exact h _ (by simp [liveForms])
    · exact h _ (by simp [liveForms])
    · exact h (.formsIn l 7 "objects") (by simp [liveForms])
  | attention =>
    simp only [keptDigits, newDigits, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    · obtain ⟨_, _, e⟩ := hf
      cases e
    · obtain ⟨_, _, e⟩ := hf
      cases e
    · obtain ⟨_, _, e⟩ := hf
      cases e
    · obtain ⟨_, _, e⟩ := hf
      cases e
    · obtain ⟨_, _, e⟩ := hf
      cases e
    · obtain ⟨_, _, e⟩ := hf
      cases e
    · obtain ⟨_, _, e⟩ := hf
      cases e
    · exact h _ (by simp [liveForms])
    · exact h _ (by simp [liveForms])
    · exact h _ (by simp [liveForms])
    · exact h _ (by simp [liveForms])
    · exact h _ (by simp [liveForms])
    · exact h (.formsIn l 7 "objects") (by simp [liveForms])
  | head =>
    simp only [keptDigits, newDigits, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    · obtain ⟨_, _, e⟩ := hf
      cases e
    · obtain ⟨_, _, e⟩ := hf
      cases e
    · obtain ⟨_, _, e⟩ := hf
      cases e
    · obtain ⟨_, _, e⟩ := hf
      cases e
    · exact h _ (by simp [liveForms])
    · exact h _ (by simp [liveForms])
    · exact h _ (by simp [liveForms])
    · exact h _ (by simp [liveForms])
    · exact formsIn_idle Dm Mg hlinks hsub runs_head.2.2.2.2.1 a
    · exact h _ (by simp [liveForms])
    · exact h (.formsIn l 8 "objects") (by simp [liveForms])

/-- **INTO THE LEDGER's OWN STRUCTURE, hForms AT THE LIVE ITEMS ALONE.** -/
theorem digOwed_live (codes : Codes) (shape : Params.ReqShape) (hM : Mg.more = {}) {l : ℕ}
    (hl : l < 25) {sub : ModelPart} (hsub : linksFull[l]? = some sub) {x : Desc.First.Look.Place}
    {tl : HTailF2} (hx : digAt X l = some (x, tl))
    (smp : Desc.First.S → (i : Fin (digList x Dm.sent Dm.l3.rad).length) →
      Option ((digSg x Dm.sent Dm.l3.rad).om i).Smp)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) ProofFile.Cl WT)
    (b' : Desc.Block Desc.First.S ProofFile.Cl) (hb : k3Const X codes shape l true = some b')
    (hOk : b'.planOk = true) (hback : q.back = []) (told : List (List Desc.Oracle))
    (hbf : bookFit Dm.N PS told = true)
    (hn : told[(k3K l true)]? = some [])
    (hbaseS : ∀ e ∈ sampledIn Dm.N
        ((openSets linksFull PS (start linksFull))[(k3K l true)]?.getD []),
      e.1 < q.base)
    (hlinks : Dm.links = linksFull)
    (hBase : ∀ r (z : P) (s s' : Desc.First.S), Mg.pub r (z, s') = Mg.pub r (z, s))
    (hForms : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
        ∀ r ∈ liveForms l sub, (mgAll Dm Mg).pub r (z, v.1) = true)
    (othersP : ∀ B', SeatOf b' B' → ∀ (z : P) u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S ProofFile.Cl WT).ior.red.out u τ = some v →
      SameBut u.1 v.1 → DigLeft u.1 v.1 →
      onQ (Fr := Fr) Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) (k3K l true) u →
      Rch (k3K l true) ((z, u.1), u.2) → u.1.failed = none →
      ∀ r ∈ pubStep ((pubSets (mgAll Dm Mg).more linksFull PS)[(k3K l true)]?.getD [])
          (pubRowM (mgAll Dm Mg).more linksFull (IM.k3Place l true)),
      (∀ m, r ≠ .left m) → (∀ m, r ≠ .leftOn m) → (mgAll Dm Mg).pubP r (z, v.1))
    (rides : RidesAtR Dm.N (mgAll Dm Mg) Rch (k3K l true) q b')
    (hSome : ∀ i, ∃ y ∈ Dm.ms,
      Alike y ⟨digSending x Dm.sent Dm.l3.rad (fun j => Dm.l3.seat x.link true j.1), i⟩)
    (hSent : ∀ i : Fin (digList x Dm.sent Dm.l3.rad).length,
      ∃ t ∈ [2, 0, 1], Dm.l3.seat x.link true i.1 ∈ Dm.N.sent l t)
    (hFits : Desc.Sound.SeatFits Dm.G Dm.sent.codes (digList x Dm.sent Dm.l3.rad)
      fun j => Dm.l3.seat x.link true j.1)
    (hB : maskB Dm.sent (digList x Dm.sent Dm.l3.rad) x.link x.arrays.ns = true)
    (pr : ℕ) (H : LinkHoles) (lk : Desc.Link Desc.First.S Desc.Claim)
    (hrun : (pr, "objects") ∈ Dm.runs l (7 + shift sub) "objects")
    (hah : Dm.ah pr "objects" = false) (hlink : Dm.Rd l = readersOfLink H lk)
    (pass : Desc.First.S → Desc.First.S → Prop) (hpass : ∀ t G, pass t (t.putFork G))
    (hfind : ∃ nm run, (statesOfLink lk pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun (Desc.K3.seatDigits K3Lot.ofForm)))
    {nos : Array ℕ} {n : ℕ} {Ld : Desc.K12.Door.Laid} {M : List OracleShape}
    (hLive : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → a.1.live.frame.shape = Dm.sent.shape)
    (hGroups : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → a.1.live.frame.groups = reqGroups a.1.live.frame.shape)
    (hLink : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → a.1.live.frame.link = x.link)
    (hNext : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → a.1.live.frame.next = .laterOrClose)
    (hOwn : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → a.1.live.frame.own = nos)
    (hSeats : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → Desc.K12.Door.atFirstSeats Ld a.1 = true)
    (hShapes : ∀ (z : P) (a : Desc.First.S × Fr.E.Str), Rch (k3K l true) ((z, a.1), a.2) →
      a.1.failed = none → Desc.K12.Door.atFirstShapes M a.1 = true)
    (pubFree : ∀ (z : P) s, (mgAll Dm Mg).pub (.freeAbove l) (z, s) = true →
      H2K5.Door.freeAboveB n s = true)
    (hnS : n ≤ x.arrays.ns)
    (hTests : maskTestsB (maskOwnIx Dm.sent x.link) 0 nos Dm.N PS[k3K l true + 1]? Ld M
      (Dm.N.group l) (Dm.l3.seat x.link true) = true)
    (h6 : oneShapeB Dm.ms = true) :
    DigOwedR Dm.G X Dm.sent Dm.l3 Dm.N (mgAll Dm Mg) Rch K3Lot.ofForm Dm.ms (IM.k3Place l true)
      (MgAt.nextOf l true) (k3K l true) l sub x tl smp q b' told :=
  digOwed_forms Dm Mg Rch codes shape hM hl hsub hx smp q b' hb hOk hback told hbf hn hbaseS hlinks
    hBase
    (fun B' hN z u τ v hout T DL hu hR hun =>
      forms_of_live Dm Mg hlinks hsub (z, v.1) (hForms B' hN z u τ v hout T DL hu hR hun))
    othersP rides hSome hSent hFits hB pr H lk hrun hah hlink pass hpass hfind hLive hGroups hLink
    hNext hOwn hSeats hShapes pubFree hnS hTests h6

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.formsIn_idle
#print axioms VerifiableInference.OnPublicFiles.forms_of_live
#print axioms VerifiableInference.OnPublicFiles.digOwed_live
