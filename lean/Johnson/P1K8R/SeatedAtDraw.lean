-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/SeatedAtDraw.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: THE
COMPLEMENT OF `CellsIn`: AT EVERY REACHED STATE IN FRONT OF THE DRAW, EVERY EARLY ARRAY'S MESSAGE IS
SEATED IN THE LINK'S OWN GROUP, AND A MEMBER SITS THERE. NO SOUNDNESS.

WHY. `CellsIn` (Johnson/Desc/First/K8/LawBlockIn.lean), the second half of `K8LeftT`'s field
`alike`, is a conditional: "where the book seats the message o in the link's own group at q, and a
member of the plan's list sits at q, ...". Where one of the two fails it says nothing, and the tie's
reader `cellsAt` reads the table of zeros at every witness (`cellsAt_congr_msgs`, its two arms
"none"). So "`CellsIn` holds" is not yet "every early cell that the tie reads is a committed
message's". Here the two antecedents are shown. The early arrays are the symbols' arrays of the
matrices and the vectors of reads (`early`, OnBytes/Tie/Pv/Tail/LettersAt.lean); they are the arrays
that `Named.arrays` lists (`early_iff_named`).
  `k8SeatedB Ld ms own n os`: A CLOSED TEST WITH CODE: at every number o of os: o < n; the laid list
    has a seat q at o; q is of own; a member of ms sits at q.
  `seated_of_test`: what its yes says.
  `seated_at_draw`: **under the head, the facts along "reached" and a yes of the test at the plan's
    numbers of the link's early arrays (`k8NumsOf`): at every reached state in front of link l's
    draw on which no check has failed, at every early cell's array t with its message o: `seatAt`
    gives a seat q, and `find?` gives a member at q.** So neither arm "none" is taken at an early
    array.
Limits. The test is no theorem in this file: under the head it is
`K8Q35.seated_at_head` (Johnson/K8Q35R/SeatedAtHead.lean), called in EarlyReadFromHead.lean; it
has been evaluated at the release's public files. `Named.msgNow L t = some o` is an antecedent here.
Nothing is said of arrays that are not early (the digits' array is read ahead by another reader). AT
`OnBytes.secondHashFunction` ALONE. Nothing on soundness.

-/
import Johnson.P1K8R.ShareAtDraw
import Johnson.Desc.First.K8.LawEarly

set_option autoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open Iop
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Model.Stages (LinkH)
open OnBytes.Tie.Pv.Tail (early)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S FoldData FoldFacts flatPlacesOf bookAt)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.K9 (seatAt)
open VerifiableInference.Desc.K12.Door (Laid)
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)

/-- The closed test: each number is below n, has a laid seat of the own group, a member there. -/
def k8SeatedB (Ld : Laid) (ms : List Mem) (own : List (ℕ × ℕ)) (n : ℕ) (os : List ℕ) : Bool :=
  os.all fun o =>
    decide (o < n) &&
      match Ld.places[o]? with
      | some q => own.contains q && (ms.find? fun y => decide (seatOf y = q)).isSome
      | none => false

/-- What its yes says. -/
theorem seated_of_test {Ld : Laid} {ms : List Mem} {own : List (ℕ × ℕ)} {n : ℕ} {os : List ℕ}
    (h : k8SeatedB Ld ms own n os = true) {o : ℕ} (ho : o ∈ os) :
    o < n ∧ ∃ q y, Ld.places[o]? = some q ∧ q ∈ own ∧
      (ms.find? fun y => decide (seatOf y = q)) = some y := by
  have a := List.all_eq_true.1 h o ho
  rw [Bool.and_eq_true] at a
  refine ⟨of_decide_eq_true a.1, ?_⟩
  have b := a.2
  split at b
  · rename_i q hq
    rw [Bool.and_eq_true] at b
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 b.2
    exact ⟨q, y, hq, List.contains_iff_mem.1 b.1, hy⟩
  · exact nomatch b

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **EVERY EARLY ARRAY's MESSAGE IS SEATED IN THE LINK's OWN GROUP, AND A MEMBER SITS THERE.** -/
theorem seated_at_draw (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {Ld : Laid} {Fr : Frame}
    {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}
    (FF : FoldFacts Rch (fun a => a.1) (P5J.At.foldD Zp cF Ld) P5J.At.reqW P5J.At.links P5J.At.ps)
    (hRch : ∀ k a, Rch k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24)
    {Xl : LinkH} (e3 : G.built[l]? = some Xl)
    (hT : k8SeatedB Ld (P5J.At.ms Zp Z.lay) ((P5J.At.N Zp cF).group l)
      ((P5J.At.N Zp cF).msgsAt (flatPlacesOf linksFull true)[drawAt l]?)
      (k8NumsOf (P5J.At.foldD Zp cF Ld) (P5J.At.layout Zp) Xl l) = true) :
    ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str) (tl : HTailF2) (L : LinkCtx),
      onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
        (fun s => (z, s)) (drawAt l) a →
      Rch (drawAt l) ((z, a.1), a.2) →
      a.1.failed = none → a.1.tl? = some tl → a.1.link? = some L →
      ∀ t r c o, early tl (.cell t r c) = true → Named.msgNow L t = some o →
        ∃ q y, seatAt ((P5J.At.N Zp cF).group l) a.1.book o = some q ∧
          ((P5J.At.ms Zp Z.lay).find? fun y => decide (seatOf y = q)) = some y := by
  intro z a tl L ha hr hm ht hL t r c o he ho
  have ho' : o ∈ Named.msgs tl L := Named.mem_msgs.2 ⟨t, (early_iff_named tl t r c).1 he, ho⟩
  obtain ⟨hon, q, y, hpl, hqo, hy⟩ :=
    seated_of_test hT (msgs_in_nums h FF hRch hG hl e3 ((z, a.1), a.2) hr hm ht hL o ho')
  have hB := bookAt_of_onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
    (fun s => (z, s)) (drawAt l) a ha hm
  unfold bookAt at hB
  simp only [Bool.and_eq_true, beq_iff_eq] at hB
  obtain ⟨⟨-, hb2⟩, hb3⟩ := hB
  have hoS : o < a.1.st.oracles.size := by rw [hb3]; exact hon
  have hS := FF.seatsCarried (drawAt l) ((z, a.1), a.2) hr hm
  unfold VerifiableInference.Desc.K12.Door.atFirstSeats
    VerifiableInference.Desc.K12.Door.seatsCarriedB at hS
  simp only [Bool.and_eq_true, beq_iff_eq] at hS
  have e0 : a.1.book.place.toList = Ld.places.take a.1.book.place.size := hS.1.1.1
  have h3 : a.1.book.place[o]? = some q := by
    rw [← Array.getElem?_toList, e0, List.getElem?_take_of_lt (by rw [hb2]; exact hoS)]
    exact hpl
  refine ⟨q, y, ?_, hy⟩
  unfold seatAt
  rw [h3]
  show (if ((P5J.At.N Zp cF).group l).contains q = true then some q else none) = some q
  rw [if_pos (List.contains_iff_mem.2 hqo)]

end P1K8T

#print axioms P1K8T.seated_of_test
#print axioms P1K8T.seated_at_draw
