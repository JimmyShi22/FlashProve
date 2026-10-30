-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/FirstBook.lean: **THE PROMISE OF THE LAW OF THE PROXIMITY TEST IN THE PLAIN FORM, FIRST ARM: "THE BOOK IS IN ORDER" IN THE PLACE OF
`FirstOpens`.** Definitions, statements and proofs.

Why. `FirstOpens` (Sheet.lean) stands in the law's promise: at what the record fixes, the trees that the first switch's declared openings name, by
their numbers over the file, are those at the places D.ts of the record's book. Its second clause is the plan's
(firstOpens_of_first, PaidByPlan.lean). Of its FIRST clause: "on the record's book; what the block's guard gives of it is typed by nobody;
the rest must come from an earlier block's promise". Here it is taken apart:
  AT A YES, BY THE BLOCK's OWN GUARD (yes_labels, Labels.lean): the i-th declared opening's label is the NUMBER of the book's tree at the i-th place.
  ON THE PLAN (ownLabelsB, a test with code): every declared opening of the first switch is a tree of the chain's own, "own n", with the label
    firstTree + n.
  OF THE RECORD, AS A PROMISE (BookOrd; bookOrdB: a test with code: Johnson/Desc/Sound/BookInOrder.lean): THE BOOK IS IN ORDER: the tree at the place z of the
    book bears the number firstTree + z. THIS IS WHAT AN EARLIER BLOCK MUST HAND ON: a Bool of the chain's own record.
  first_of_book    the three give the first clause at num := numAt t₁ t₂ c and no := fun z => numAt t₁ t₂ c (.own z).
  book_of_fixes    where the first fold's mask has come ahead, the book of what the record fixes is the record's own.
  firstOpens_of_yes   FirstOpens at every statement from which the piece ever puts out.
  seat_of_book     **AT A SEAT** (a block set inside a chain's state by two doors: seated, Inside.lean): a law whose whole promise is FirstOpens at the record
                   behind the door in holds with "the mask has come · the book is in order" there in its place. The law is a letter.
  uFull_ownLabels | u_ownLabels   the test on the plan says yes at the place of the test on the folded row's group, at the full and the small size
    (the kind's files' closed terms piUFull | piU, Law/PlacesFull.lean | PlacesSmall.lean: A RUN's PRINT MADE INTO TERMS: that they are the places is that run's word). By evaluation.
  taken_fails      a control: a place whose first opening is taken over from another chain fails the test.
Limits. THE FIRST ARM ALONE (the mask ahead: the test on G_u). A CHAIN WHOSE TEST OPENS TREES TAKEN OVER FROM ANOTHER CHAIN (the last chain) HAS NOT ownLabelsB. That
any block hands BookOrd on is not shown here. NO SOUNDNESS IS CLAIMED. Those of Sheet.lean, LawY.lean, Labels.lean.

-/
import Johnson.Desc.K12.Coin.Labels
import Johnson.Desc.K12.Coin.LawY
import Johnson.Desc.K12.Coin.PaidByPlan
import Johnson.Desc.K12.Coin.Inside
import Johnson.Desc.Sound.BookInOrder
import Johnson.Desc.K12.Law.PlacesFull
import Johnson.Desc.K12.Law.PlacesSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.First (gpOf Plain opensOf made_of tree_of_ts entered)

/-- ON THE PLAN: every declared opening of the first switch is a tree of the chain's own, with the label firstTree + n. -/
def ownLabelsB (π : P12) : Bool :=
  match π.nums.stages with
  | a :: _ => (opensOf π a.k).all fun o =>
    match o.2 with
    | .own n => decide (o.1.tree = π.nums.firstTree + n)
    | .taken _ _ => false
  | [] => false

/-- **The first clause of `FirstOpens`.** -/
theorem first_of_book (π : P12) (t₁ t₂ c : ℕ) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : π.nums.stages = a :: rest) (hP : ownLabelsB π = true) (D : Plain)
    (hop : D.opens = opensOf π a.k)
    (hl : D.opens.map (·.1.tree) = D.ts.map (H2K.First.numAt D.book))
    (hts : ∀ z ∈ D.ts, ∃ T, D.book.trees[z]? = some T)
    (hB : BookOrd π.nums.firstTree D.book) :
    D.opens.map (fun o => VerifiableInference.Desc.numAt t₁ t₂ c o.2) =
      D.ts.map fun z => VerifiableInference.Desc.numAt t₁ t₂ c (.own z) := by
  have h1 : ∀ o ∈ D.opens, VerifiableInference.Desc.numAt t₁ t₂ c o.2 =
      VerifiableInference.Desc.numAt t₁ t₂ c (.own (o.1.tree - π.nums.firstTree)) := by
    intro o ho
    rw [hop] at ho
    unfold ownLabelsB at hP
    rw [hs] at hP
    have h2 := List.all_eq_true.1 hP o ho
    obtain ⟨sh, src⟩ := o
    cases src with
    | own n =>
      have e : sh.tree = π.nums.firstTree + n := of_decide_eq_true h2
      show VerifiableInference.Desc.numAt t₁ t₂ c (.own n) =
        VerifiableInference.Desc.numAt t₁ t₂ c (.own (sh.tree - π.nums.firstTree))
      rw [e, Nat.add_sub_cancel_left]
    | taken c' s => cases h2
  have h3 : ∀ z ∈ D.ts, VerifiableInference.Desc.numAt t₁ t₂ c
      (.own (H2K.First.numAt D.book z - π.nums.firstTree)) =
      VerifiableInference.Desc.numAt t₁ t₂ c (.own z) := by
    intro z hz
    obtain ⟨T, hT⟩ := hts z hz
    have e : H2K.First.numAt D.book z = π.nums.firstTree + z := by
      unfold H2K.First.numAt
      rw [hT]
      exact hB z T hT
    rw [e, Nat.add_sub_cancel_left]
  calc D.opens.map (fun o => VerifiableInference.Desc.numAt t₁ t₂ c o.2)
      = D.opens.map (fun o => VerifiableInference.Desc.numAt t₁ t₂ c
          (.own (o.1.tree - π.nums.firstTree))) := List.map_congr_left h1
    _ = (D.opens.map (·.1.tree)).map (fun n => VerifiableInference.Desc.numAt t₁ t₂ c
          (.own (n - π.nums.firstTree))) := by rw [List.map_map]; rfl
    _ = (D.ts.map (H2K.First.numAt D.book)).map (fun n => VerifiableInference.Desc.numAt t₁ t₂ c
          (.own (n - π.nums.firstTree))) := by rw [hl]
    _ = D.ts.map (fun z => VerifiableInference.Desc.numAt t₁ t₂ c
          (.own (H2K.First.numAt D.book z - π.nums.firstTree))) := by rw [List.map_map]; rfl
    _ = D.ts.map (fun z => VerifiableInference.Desc.numAt t₁ t₂ c (.own z)) :=
        List.map_congr_left h3

/-- Where the first fold's mask has come ahead, the book of what the record fixes is the record's own. -/
theorem book_of_fixes (π : P12) (t : T12) (hm : t.mask.isSome = true) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain)
    (hf : Fixes π t a rest G0 Ly D) : D.book = t.book := by
  obtain ⟨id, hid⟩ := Option.isSome_iff_exists.1 hm
  obtain ⟨cu, _, he⟩ := (made_of π _ a Ly D (hf.2.2.2 default)).ent
  unfold entered at he
  dsimp only at he
  rw [hid] at he
  have e := Option.some.inj he
  exact (congrArg (fun q : ℕ × Statement × TreeBook => q.2.2) e).symm

/-- **`FirstOpens` at every statement from which the piece ever puts out.** -/
theorem firstOpens_of_yes {W : Type} (F : Frame) (π : P12) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (ho : π.nums.ownMask = false)
    (hP : ownLabelsB π = true) (t₁ t₂ c base : ℕ) (dB : RDT) (dt : List RDT) (e₀ : ℕ)
    (εt : Err (uLT (ckP .two) dt))
    (n2 : ∀ n, n < π.nums.free → VerifiableInference.Desc.numAt t₁ t₂ c (.own n) < base)
    (n3 : ∀ c' n, (c' + 1, n) ∈ π.before → VerifiableInference.Desc.numAt t₁ t₂ c (.taken c' n) < base)
    (x : T12 × F.E.Str) (hm : x.1.mask.isSome = true) (hB : BookOrd π.nums.firstTree x.1.book)
    (hy : ∃ τ b, (pieceT F W π base dB dt e₀ εt).ior.red.out x τ = some b) :
    FirstOpens π (VerifiableInference.Desc.numAt t₁ t₂ c)
      (fun z => VerifiableInference.Desc.numAt t₁ t₂ c (.own z)) base x.1 := by
  obtain ⟨τ, b, hb⟩ := hy
  refine firstOpens_of_first π _ _ base x.1 hp ho n2 n3 fun a rest G0 Ly D hf => ?_
  have hmd := made_of π _ a Ly D (hf.2.2.2 default)
  refine first_of_book π t₁ t₂ c a rest hf.1 hP D hmd.opens
    (yes_labels F π he hp base dB dt e₀ εt x τ b hb a rest G0 Ly D hf)
    (fun z hz => tree_of_ts π _ a Ly D hmd z hz) ?_
  rw [book_of_fixes π x.1 hm a rest G0 Ly D hf]
  exact hB

/-- **AT A SEAT: "the mask has come · the book is in order" IN THE PLACE OF `FirstOpens`.** law: the kind's law at the block seated by two doors
(`seated`, Inside.lean), with `FirstOpens` at the record behind the door in as its whole promise: A LETTER HERE: whoever holds it lays it. -/
theorem seat_of_book {S W : Type} (F : Frame) (π : P12) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (ho : π.nums.ownMask = false)
    (hP : ownLabelsB π = true) (t₁ t₂ c base : ℕ) (dB : RDT) (dt : List RDT) (e₀ : ℕ)
    (εt : Err (uLT (ckP .two) dt))
    (n2 : ∀ n, n < π.nums.free → VerifiableInference.Desc.numAt t₁ t₂ c (.own n) < base)
    (n3 : ∀ c' n, (c' + 1, n) ∈ π.before → VerifiableInference.Desc.numAt t₁ t₂ c (.taken c' n) < base)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (Q : S × F.E.Str → S × F.E.Str → Prop)
    (law : (seated (pieceT F W π base dB dt e₀ εt) enter leave).ior.red.Leads
      (fun a => ∀ t, enter a.1 = .ok t → FirstOpens π (VerifiableInference.Desc.numAt t₁ t₂ c)
        (fun z => VerifiableInference.Desc.numAt t₁ t₂ c (.own z)) base t) Q
      (seated (pieceT F W π base dB dt e₀ εt) enter leave).err) :
    (seated (pieceT F W π base dB dt e₀ εt) enter leave).ior.red.Leads
      (fun a => ∀ t, enter a.1 = .ok t → t.mask.isSome = true ∧ BookOrd π.nums.firstTree t.book) Q
      (seated (pieceT F W π base dB dt e₀ εt) enter leave).err := by
  intro a ha
  by_cases hy : ∃ τ b, (seated (pieceT F W π base dB dt e₀ εt) enter leave).ior.red.out a τ = some b
  · obtain ⟨τ, b, hb⟩ := hy
    obtain ⟨t₀, t', h1, h2, _⟩ := seated_out (pieceT F W π base dB dt e₀ εt) enter leave a τ b hb
    refine law a fun t ht => ?_
    obtain rfl : t₀ = t := Except.ok.inj (h1.symm.trans ht)
    exact firstOpens_of_yes F π he hp ho hP t₁ t₂ c base dB dt e₀ εt n2 n3 (t₀, a.2) (ha t₀ h1).1
      (ha t₀ h1).2 ⟨τ, _, h2⟩
  · exact Doomed.of_forall _ _ fun τ b hb => absurd ⟨τ, b, hb⟩ hy

/-- The test on the plan at the place of the test on the folded row's group: the full size. -/
theorem uFull_ownLabels : ownLabelsB H2K.Member.piUFull = true := by decide +kernel

/-- The small size. -/
theorem u_ownLabels : ownLabelsB H2K.Member.piU = true := by decide +kernel

/-- A control: the own test of the last chain opens trees that are taken over. -/
theorem taken_fails : ownLabelsB H2K.Member.piWFull = false := by decide +kernel

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.first_of_book
#print axioms VerifiableInference.Desc.K12.Coin.firstOpens_of_yes
#print axioms VerifiableInference.Desc.K12.Coin.seat_of_book
#print axioms VerifiableInference.Desc.K12.Coin.uFull_ownLabels
#print axioms VerifiableInference.Desc.K12.Coin.u_ownLabels
#print axioms VerifiableInference.Desc.K12.Coin.taken_fails
