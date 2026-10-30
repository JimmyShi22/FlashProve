-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/FillAt.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: THE FIELD
`here` OF `K8Fill` AT THE DESCRIPTION'S OWN 25 PLACES, FROM THE PAYERS THAT LIE.
NO SOUNDNESS.

`K8Fill.here` says nine things of a reached statement inside the promise, without a mark. Here five
of them are PAID, in the goals' scope, at the written list of segments, at each link l ≤ 24:
  the smallness test's part and the link are there, and `Named.namedB` says yes: `namedB_of_reach`
    (Johnson/P1K8R/NamedOfReach.lean), under the description's `planOk` and the test `namesDoorB`;
  `frontB`: `k8Front_of_test` (Johnson/P1K8R/PlanFitsTest.lean), under the test `planFitsAllB`;
  the ledger is there: `fork_of_onQ` (Johnson/Desc/First/K8/ForkPromise.lean);
  "no collision" at the two sendings' seats: `noColl_of_onQ`, `pins_open_full`
    (Johnson/Desc/First/K8/TiePromise.lean);
  `K8Sits`' field `sent`: `sent_of_joined`
    (Johnson/Desc/First/K8/MsgsOfFrame.lean).
What is left stands in ONE structure:
  `HereOwes`: the filling's "no collision" is the table's over the plan's members; its reader of OOD
    samples hangs on entry and seat alone; and, at such a statement (`atFold`): the frame's two
    lists are members of the group that it names, which is the segment's listed group; every member
    of the state's list has an alike member in the plan's; the seats fit the description; the fence;
    `CellsIn` at the early arrays alone.
  `k08_here`: **`HereOwes` gives `K8Fill.here`'s sentence, to the letter**, at G := the description,
    links := `linksFull`, k := `drawAt l`, m := l, p := the lot's own parameters at the link, Rch :=
    ANY CONDITION THAT GIVES `RchAt` (`HereOwes.atFold` is
    asked along that condition alone).
Limits. `HereOwes` is shown at no filling. AT `OnBytes.secondHashFunction` ALONE. Nothing on soundness.

-/
import Johnson.P1K8R.OwesAt
import Johnson.P1K8R.PlanFitsTest
import Johnson.P1K8R.NamedOfReach
import Johnson.Desc.First.K8.MsgsOfFrame
import Johnson.Desc.First.K8.ForkPromise

set_option autoImplicit false
set_option maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open Inst.Model
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Model.Stages (LinkH)
open OnBytes.Tie.Pv.Tail (early)
open VerifiableInference.Desc (Block Chain FileDescription Place Claim Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Ready (frontB planFitsAllB)
open Johnson.Desc.First.Walk.Tied (RchAt)
open ProofFile (Cl)

/-- The draw's number, in the two spellings. -/
theorem drawAt_place (l : ℕ) : drawAt l = 14 * l + (if l = 24 then 5 else 4) + 2 := by
  unfold drawAt
  split
  · subst_vars
    rfl
  · rfl

section
variable {Cells Tok : Type} {Fr : Frame} (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat)
  (c : Chain S Cl) (cs : OnBytes.Codes)
  (smpT : ProofFile.InstPub × S → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (N : Numbers) (Mg : Meaning ProofFile.InstPub (Wit Cells Tok MsgT))
  (rad : OracleShape → ℕ) (l base₀ : ℕ) (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop)

/-- The description. -/
abbrev FD : FileDescription ProofFile.Inst :=
  ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c

/-- **What is left of the field `here` at link l.** -/
structure HereOwes : Prop where
  noColl : ∀ j t a y, Mg.noColl j t a y → noCollJT cs (FD Z A B c) smpT ms j t a y
  bySeat : SmpBySeat cs smpT
  atFold : ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str) (tl : HTailF2) (L : LinkCtx),
    onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) (drawAt l) a →
    Rch (drawAt l) ((z, a.1), a.2) → a.1.failed = none → a.1.tl? = some tl →
    a.1.link? = some L →
    FrameJoined a.1.st L.check.frame ∧ L.check.frame.group = N.groupAt l ∧
      (∀ i, ∃ y ∈ ms, Alike y ⟨⟨lA rad a.1 tl L, sA rad a.1 tl L⟩, i⟩) ∧
      SeatFits (FD Z A B c) cs (lA rad a.1 tl L) (sA rad a.1 tl L) ∧
      (∀ i, (sA rad a.1 tl L i).1 < base₀) ∧
      ∀ t r c o, early tl (.cell t r c) = true → Named.msgNow L t = some o →
        CellsIn cs (lA rad a.1 tl L) (sA rad a.1 tl L) ms N l a.1 t o

end

section
variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat} {Cells Tok : Type} {Fr : Frame} {cs : OnBytes.Codes}
  {smpT : ProofFile.InstPub × S → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf cs s.l).om i).Smp}
  {ms : List Mem} {N : Numbers} {Mg : Meaning ProofFile.InstPub (Wit Cells Tok MsgT)}
  {rad : OracleShape → ℕ} {l base₀ : ℕ} {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}

unseal lA sA in
/-- The seats of the state's list, in the library's spelling. -/
theorem sent_sA {s : S} {tl : HTailF2} {L : LinkCtx}
    (h : ∀ i, ∃ t ∈ [0, 1], Named.seatFn rad s.st s.book tl L i ∈ N.sent l t) :
    ∀ i, ∃ t ∈ [0, 1], sA rad s tl L i ∈ N.sent l t := h

/-- **THE FIELD `here`, AT THE DESCRIPTION'S OWN PLACE AT LINK l.** -/
theorem k08_here (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hP : F.planOk = true)
    (hD : namesDoorB F = true) (hW : planFitsAllB Bs.G₀.W = true) (hl : l ≤ 24) {Xl : LinkH}
    (e3 : Bs.G₀.built[l]? = some Xl)
    (hRch : ∀ k a, Rch k a → RchAt (FD Z A B c) k a)
    (H : HereOwes Z A B c cs smpT ms N Mg rad l base₀ Rch) (z : ProofFile.InstPub)
    (a : S × Fr.E.Str)
    (ha : onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) (drawAt l) a)
    (hr : Rch (drawAt l) ((z, a.1), a.2)) (hm : ¬ a.1.failed ≠ none) :
    ∃ tl L F', a.1.tl? = some tl ∧ a.1.link? = some L ∧ a.1.fork? = some F' ∧
      frontB a.1 = true ∧
      Named.namedB (ProofFile.k8ParW Z Bs.G₀ Xl l).toPar a.1.st a.1.book tl L = true ∧
      K8Sits (FD Z A B c) cs (lA rad a.1 tl L) (sA rad a.1 tl L) smpT ms N l ∧
      (∀ i, (sA rad a.1 tl L i).1 < base₀) ∧
      (∀ t r c o, early tl (.cell t r c) = true → Named.msgNow L t = some o →
        CellsIn cs (lA rad a.1 tl L) (sA rad a.1 tl L) ms N l a.1 t o) ∧
      ∀ t ∈ [0, 1], ∀ e ∈ N.sent l t,
        noCollJT cs (FD Z A B c) smpT ms e.1 e.2 (z, a.1) (strsOf Fr a.2) := by
  have hm' : a.1.failed = none := not_not.1 hm
  have hx : ((l, if l = 24 then 5 else 4) : ℕ × ℕ) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 (by omega), rfl⟩
  have hr' : RchAt (FD Z A B c) (14 * l + (if l = 24 then 5 else 4) + 2) ((z, a.1), a.2) := by
    rw [← drawAt_place]
    exact hRch _ _ hr
  obtain ⟨tl, L, ht, hL, hN⟩ := P1K8S.namedB_of_reach hS hR O hP hD hx e3 ((z, a.1), a.2) hr'
  have hfr := P1K8S.k8Front_of_test hS hR O hW hx ((z, a.1), a.2) hr'
  obtain ⟨F', hF⟩ := fork_of_onQ N Mg (fun s => (z, s)) l hl a ha hm'
  obtain ⟨hJ, hg, hsome, hfits, hfence, hC⟩ := H.atFold z a tl L ha hr hm' ht hL
  refine ⟨tl, L, F', ht, hL, hF, hfr, hN,
    ⟨hsome, H.bySeat,
      sent_sA (sent_of_joined N Mg (fun s => (z, s)) l hl a ha hm' rad tl L hJ hg), hfits⟩,
    hfence, hC, fun t ht' e he => ?_⟩
  have h01 : t = 0 ∨ t = 1 := by simpa using ht'
  rcases h01 with rfl | rfl
  · exact H.noColl _ _ _ _ (noColl_of_onQ N Mg _ _ (fun s => (z, s)) (drawAt l) l 0 a ha hm'
      (pins_open_full l hl).1 e he)
  · exact H.noColl _ _ _ _ (noColl_of_onQ N Mg _ _ (fun s => (z, s)) (drawAt l) l 1 a ha hm'
      (pins_open_full l hl).2 e he)

end

end P1K8T

#print axioms P1K8T.k08_here
