-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MgAt/K3CallsObjInPc.lean: THE LOOKUP ARGUMENT ON A SEGMENT's CALLS: BEHIND AN
ACCEPT THE PUBLIC TEST formsInT l pc "objects" HOLDS (UNDER SEVENTEEN PREMISES, hmask AND hmerge
AMONG THEM), WITH THE PIECE A LETTER pc, AT BOTH RUNS FOR
WHICH THE TABLE's NAME "objects" STANDS. One theorem.
CREDIT. `objIn_pc` IS MADE BY PROGRAM FROM THE TEXT OF THE LOOKUPS' AUTHORS' `objIn_mgAll`
(Johnson/Desc/Sound/MgAt/K3CallsObjIn.lean), statement and proof. IT PARTS FROM THAT TEXT AT JUST
THESE PLACES: (1) the numeral 2 of the piece is the letter pc (five places) · (2) hruns stands at
the PAIR [(pr, "objects"), (pr, "guests")] · (3) two premises more: hsame (pass t t) and hfindG (the
link's run "guests" is the run without a guest) · (4) the last lines end in both lemmas
`objects_formsInT` and `guests_formsInT` (Johnson/Top/H/Keep/FormsInTObjects.lean). WHY (2)–(4). The
table of joints lets "objects" stand for two runs (`First.runsOf`, Johnson/Desc/First/Borders.lean:
[(1 + o, "objects"), (1 + o, "guests")] at the calls' piece): at parameters whose runs are the
table's, their hruns (a list of one) is false: Lean's `decide` said so at all three sorts of
segment. USER: Johnson/P5J/K03ObjInAt.lean, at all 25 segments (pc 2; at the output head's 3).
Limits. As theirs. Nothing on soundness.

-/
import Johnson.Desc.Sound.MgAt.K3CallsObjIn

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

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop) (claim : Aff → Desc.Claim)
  (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (codes : Codes) (shape : Params.ReqShape)
  {k l pc : ℕ} {x : Desc.First.Look.Place} {a : Desc.Place}
  {b' : Desc.Block Desc.First.S Desc.Claim}
  {q : Piece (ckP .two) Fr (P × Desc.First.S) Desc.Claim
    (Desc.Wit (CellsQ rows cols) Tok MsgT)}
  {pr : ℕ} {H : LinkHoles} {lk : Link Desc.First.S Desc.Claim}
  {pass : Desc.First.S → Desc.First.S → Prop}

local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **formsInT l pc "objects" holds behind.** -/
theorem objIn_pc
    (h : Desc.K3.theStated claim readers X codes shape a = some b') (hOk : b'.planOk = true)
    (hback : q.back = []) (hla : a.link = some l)
    (hpcX : a.piece = Desc.K3.pieceAt X l false) (hlook : lookAt X l false = some x)
    (hsP : (theP).shape = some x.fs)
    (onIn : ∀ (z : P) (u : Desc.First.S × Fr.E.Str),
      onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      u.1.failed = none → Desc.K3.k3OnIn theP u.1 = true)
    (hruns : Dm.runs l pc "objects" = [(pr, "objects"), (pr, "guests")])
    (hA : AtS2 (Desc.K3.seatCalls claim)) (hlink : Dm.Rd l = readersOfLink H lk)
    (hpass : ∀ t G, pass t (t.putFork G)) (hsame : ∀ t, pass t t)
    (hfind : ∃ nm run, (statesOfLink lk pr).find? (fun r => r.1 == "objects") = some (nm, run) ∧
      RunOver pass run (objectsRun (Desc.K3.seatCalls claim)))
    (hfindG : ∃ nm run, (statesOfLink lk pr).find? (fun r => r.1 == "guests") = some (nm, run) ∧
      RunOver pass run (guestsRun ([] : List (Desc.First.Look.Guest Desc.First.S Desc.Claim))))
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
      (mgAll Dm Mg).pub (.formsInT l pc "objects") (z, v.1) = true := by
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
  show pubAll Dm.pubD Mg.pub (.formsInT l pc "objects") (z, v.1) = true
  show ((Dm.runs l pc "objects").all fun p =>
    Desc.K9.formsInT (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 v.1) = true
  rw [hruns, hlink]
  show (Desc.K9.formsInT (readersOfLink H lk) (Dm.N.sent l 0) pr "objects" v.1 &&
    (Desc.K9.formsInT (readersOfLink H lk) (Dm.N.sent l 0) pr "guests" v.1 && true)) = true
  rw [Bool.and_true, Bool.and_eq_true]
  refine ⟨?_, guests_formsInT H lk pr (Dm.N.sent l 0) pass hsame hfindG hc⟩
  exact objects_formsInT H lk pr (Dm.N.sent l 0) (Desc.K3.seatCalls claim) hA pass hpass hfind hc
    hg (by rw [hcF]; exact hNm) (by rw [hcF]; exact L.padLeft.fit)
    (hmask B' hB z u v hu hr hf hy c hc) (hmerge B' hB z u v hu hr hf hy g hg)

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.objIn_pc
