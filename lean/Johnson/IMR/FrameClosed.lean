-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FrameClosed.lean: THE TWO CLOSED PREMISES OF Johnson/IMR/FrameField.lean's
frameIs_field, PROVED OF THE TERMS WITH CODE THAT FILL THE LETTERS ownAt AND keptAt
(Johnson/Desc/First/SentAtMoment.lean over FillSentLater.lean, SentTerms.lean, FillSent.lean), at
links := IM.linksW, ps := IM.placesW, at every shape, every table of numbers N and every built.
  born_from, keptSize_born: in every group of a request there are as many entries "born" as kept
    targets (both are made of the same list): those terms count the first, this file's the second.
  placeFind, find_numbers: closed equations, by the kernel: the places that those terms' three bases
    look up (of link m; piece 1, 4 or 6, each plus the shift) are the entries number
    entryCut m - 1, entryCut m + 2, entryCut m + 4 of IM.placesW: those of the sub-protocols that
    make the link's first, second and third sending; at all m < 25.
  cntOf N k: N.msgsAt of the entry number k (a number of oracle messages): the letter cnt at which
    the equations hold.
  base0_is, base1_is, base2_is; own_first.
  kept_closed, own_closed: THE TWO EQUATIONS.
  counts_of_bookAt: the first premise on states, CountsBy c Z (cntOf N), follows from the table of
    joints' own Bool bookAt N at every cut (its third clause).
  frameIs_field3: frameIs_field at these terms, at every shape: two premises are left, both on the
    fold's states: CountsBy c Z (cntOf N) and ShapeBy c Z shape.
  frameIs_field1: THE TOP: at shape := Z.first.shape, where ShapeBy is proved (shape_paid): ONE
    PREMISE IS LEFT: CountsBy c Z (cntOf N).
NOT HERE: that one. That the composed meaning's N, shape, built, links, ps are those of one value.
OBJECT: closed terms; and ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. No soundness.
-/
import Johnson.IMR.FrameField
import Johnson.Desc.First.SentAtMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)

/-- In every group of a request: as many entries "born" as kept targets. -/
theorem born_from (s : Params.ReqShape) : ∀ (count l : Nat) (alive : List ReqAlive),
    ∀ G ∈ reqGroupsFrom s count l alive, G.born.size = G.target.kept.size
  | 0, _, _, G, h => by
    simp [reqGroupsFrom] at h
  | count + 1, l, alive, G, h => by
    simp only [reqGroupsFrom, List.mem_cons] at h
    rcases h with rfl | h
    · simp [reqGroupAt]
    · exact born_from s count _ _ G h

theorem keptSize_born (sh : Params.ReqShape) (m : Nat) :
    ((reqGroups sh).getD m {}).born.size = keptSize sh m := by
  unfold keptSize
  rw [Array.getD_eq_getD_getElem?]
  cases h : (reqGroups sh)[m]? with
  | none => rfl
  | some G =>
    have hm : G ∈ reqGroupsFrom sh (sh.link.length + 1) 0 [] := by
      have k := Array.mem_of_getElem? h
      rw [reqGroups_eq] at k
      simpa using k
    exact born_from sh _ _ _ G hm

/-- The place that the closed terms' bases look up: of link m, with the piece j + the shift. -/
def placeFind (m j : Nat) : Option Place :=
  IM.placesW.find? fun p => p.link == some m && p.piece == j + ((IM.linksW[m]?).map shift).getD 0

set_option maxRecDepth 1000000 in
/-- Closed equations, by the kernel: these places are the entries of IM.placesW of the sub-protocols
that make link m's first, second and third sending. -/
theorem find_numbers : ∀ m < 25, placeFind m 1 = IM.placesW[entryCut m - 1]? ∧
    placeFind m 4 = IM.placesW[entryCut m + 2]? ∧ placeFind m 6 = IM.placesW[entryCut m + 4]? := by
  decide +kernel

/-- The number of oracle messages at the cut k, by the table of joints' own numbers. -/
def cntOf (N : Numbers) (k : Nat) : Nat := N.msgsAt IM.placesW[k]?

section
variable (shape : Params.ReqShape) (N : Numbers) (built : Array Stages.LinkH)

theorem base0_is {m : Nat} (h : m < 25) :
    FillSent.baseAt N IM.linksW IM.placesW m = cntOf N (entryCut m - 1) :=
  congrArg N.msgsAt (find_numbers m h).1

theorem base1_is {m : Nat} (h : m < 25) :
    FillSent.base1At N IM.linksW IM.placesW m = cntOf N (entryCut m + 2) :=
  congrArg N.msgsAt (find_numbers m h).2.1

theorem base2_is {m : Nat} (h : m < 25) :
    FillSent.base2At N IM.linksW IM.placesW m = cntOf N (entryCut m + 4) :=
  congrArg N.msgsAt (find_numbers m h).2.2

/-- **THE THIRD NAMED PREMISE, PROVED.** -/
theorem kept_closed : ∀ m < 25,
    FillSent.keptAt shape N IM.linksW IM.placesW built m = keptN (cntOf N) shape m := by
  intro m h
  show (if (m == 0) = true then #[] else (Array.range ((reqGroups shape).getD m {}).born.size).map
    (· + (FillSent.baseAt N IM.linksW IM.placesW m + 1))) = _
  unfold keptN
  rw [keptSize_born, base0_is N h]
  by_cases h0 : m = 0
  · rw [if_pos h0, if_pos (by simpa using h0)]
  · rw [if_neg h0, if_neg (by simpa using h0)]

theorem own_first : ∀ m < 25,
    (FillSent.sentDataAt shape N IM.linksW IM.placesW built).own m =
      ownFirst (cntOf N) shape m := by
  intro m h
  show (Array.range (((shape.link[m]?.map (·.messages)).getD []).filter fun x =>
    x.moment == 0).length).map (· + (FillSent.baseAt N IM.linksW IM.placesW m +
      (if (m == 0) = true then 0 else 1 + ((reqGroups shape).getD m {}).born.size))) = _
  unfold ownFirst nosAt
  rw [keptSize_born, base0_is N h]
  by_cases h0 : m = 0
  · rw [if_pos h0, if_pos (by simpa using h0)]
  · rw [if_neg h0, if_neg (by simpa using h0)]

/-- **THE FOURTH NAMED PREMISE, PROVED.** -/
theorem own_closed : ∀ m < 25, ∀ j, 1 ≤ j → j ≤ 3 →
    FillSent.ownAt shape N IM.linksW IM.placesW built m j = ownN (cntOf N) shape m j := by
  intro m h j h1 h3
  have s2 : FillSent.secondNos shape (FillSent.base1At N IM.linksW IM.placesW) m =
      nosAt shape m 1 (cntOf N (entryCut m + 2)) := by
    unfold FillSent.secondNos nosAt
    rw [base1_is N h]
  have s3 : FillSent.thirdNos shape (FillSent.base2At N IM.linksW IM.placesW) m =
      nosAt shape m 2 (cntOf N (entryCut m + 4)) := by
    unfold FillSent.thirdNos nosAt
    rw [base2_is N h]
  have o2 : (FillSent.sentData1At shape N IM.linksW IM.placesW built).own m =
      ownFirst (cntOf N) shape m ++ nosAt shape m 1 (cntOf N (entryCut m + 2)) := by
    show (FillSent.sentDataAt shape N IM.linksW IM.placesW built).own m ++
      FillSent.secondNos shape (FillSent.base1At N IM.linksW IM.placesW) m = _
    rw [own_first shape N built m h, s2]
  obtain rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 := by omega
  · rw [FillSent.ownAt_one, own_first shape N built m h]
    rfl
  · rw [FillSent.ownAt_two, o2]
    rfl
  · rw [FillSent.ownAt_three, o2, s3]
    rfl

end

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The first premise on states, from the table of joints' own Bool at every cut. -/
theorem counts_of_bookAt {N : Numbers}
    (h : ∀ (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (k : Nat)
      (r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn), k ≤ 358 →
      foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok r →
      bookAt N IM.placesW[k]? r.1 = true) : CountsBy c Z (cntOf N) := by
  intro p R C k r hk f
  have q := h p R C k r hk f
  unfold bookAt at q
  rw [Bool.and_eq_true] at q
  exact beq_iff_eq.1 q.2

/-- **THE FIELD "frameIs" AT THE TERMS WITH CODE THAT FILL ownAt AND keptAt**: two premises are
left, both on the fold's states. -/
theorem frameIs_field3 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (shape : Params.ReqShape) (N : Numbers) (built : Array Stages.LinkH)
    (hN : CountsBy c Z (cntOf N)) (hSh : ShapeBy c Z shape) {X : Type}
    (Rch : Nat → X → Prop) (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → ∃ rs cols r q,
      foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z (at_ a).1) rs cols = .ok ((at_ a).2, r, q)) :
    ∀ k a p m L, Rch k a → (at_ a).2.failed = none → IM.placesW[k]? = some p → p.link = some m →
      (at_ a).2.link? = some L →
      L.check.frame.moment = momentW (shiftW m) p.piece ∧
        L.check.frame.own = FillSent.ownAt shape N IM.linksW IM.placesW built m
          (momentW (shiftW m) p.piece) ∧
        L.check.frame.keptBefore = FillSent.keptAt shape N IM.linksW IM.placesW built m ∧
        (p.piece ≤ 11 + 2 * shiftW m →
          L.check.frame.link = m ∧ L.check.frame.next = .laterOrClose) :=
  frameIs_field hS hR O hN hSh _ _ (kept_closed shape N built) (own_closed shape N built) Rch at_
    hRch

/-- **THE FIELD "frameIs" AT THE PUBLIC SHAPE: ONE PREMISE IS LEFT**: N.msgsAt of the entry number k
is the number of oracle messages at the cut k. -/
theorem frameIs_field1 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (N : Numbers) (built : Array Stages.LinkH) (hN : CountsBy c Z (cntOf N)) {X : Type}
    (Rch : Nat → X → Prop) (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → ∃ rs cols r q,
      foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z (at_ a).1) rs cols = .ok ((at_ a).2, r, q)) :
    ∀ k a p m L, Rch k a → (at_ a).2.failed = none → IM.placesW[k]? = some p → p.link = some m →
      (at_ a).2.link? = some L →
      L.check.frame.moment = momentW (shiftW m) p.piece ∧
        L.check.frame.own = FillSent.ownAt Z.first.shape N IM.linksW IM.placesW built m
          (momentW (shiftW m) p.piece) ∧
        L.check.frame.keptBefore = FillSent.keptAt Z.first.shape N IM.linksW IM.placesW built m ∧
        (p.piece ≤ 11 + 2 * shiftW m →
          L.check.frame.link = m ∧ L.check.frame.next = .laterOrClose) :=
  frameIs_field3 hS hR O Z.first.shape N built hN (shape_paid hS hR O) Rch at_ hRch

end

#print axioms keptSize_born
#print axioms find_numbers
#print axioms kept_closed
#print axioms own_closed
#print axioms counts_of_bookAt
#print axioms frameIs_field3
#print axioms frameIs_field1

end Meaning.K2
