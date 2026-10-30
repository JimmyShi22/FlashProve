-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/AheadAtDigits.lean: **hmeet**: the
binder hmeet of k01_fifty (Johnson/Desc/K1/Law/K01Law.lean) at the wider meaning
`plus13 (d13 Dm) dk (mgAll Dm Mg₀)` and N := Dm.N: `AheadMeets`: an
array that the table's numbers hold "ahead" in front of a later sending, and that is found behind
under a new number, sits at the seat and has the shape that were foretold.
WHERE IT BITES, by evaluation in Lean's kernel at the written list of places (read off the print of
a file that is not in this library, first): no item `forms` is open in front
of a link's reads; in front
of its digits every open `forms` is the segment's own; and "frame.sentIs1" of the segment stands in
the open public set there.
  `formsAt_full`, `sent1In_mw`   [kernel] these facts. `aheadTests_fail`: both tests can fail
  `aheadAtB shape sent P l n01 nT`   A TEST WITH CODE on the list of rounds, which mirrors the term
                   of `K9.aheadOf`: at each new message i of the place, the shape's message number
                   n01 + i has, by the table's numbers, the seat that the sending lays for i, and
                   the shape that the place announces for i. `aheadAt_fails`: it refuses at a
                   table without seats, IF the place sends a message and the shape has one at
                   n01: no place and shape that meet these two are written out here
  `aheadMeets_of`  **`AheadMeets` at two states**, from "frame.sentIs1"'s test in front and behind,
                   the shape of the open link's frame, what the sending does to the book, to the
                   list of the messages' shapes and to the codes, and `aheadAtB`
  `hmeet_plus13`   **the binder**, with ONE POINTWISE PREMISE MORE behind the promise: at the state
                   in front the open link's frame's shape is `Dm.shape`
PREMISES, BY NAME. hM. hAt: `aheadAtB` at the 25 digits' places.
WHY POINTWISE. The promise at this meaning says nothing on the open link's frame's shape: asked of
every state inside it, that premise might have no member. It is paid where "in order" says it.
The recursion limit is raised in this file (maxRecDepth 1000000):
for the elaboration of the kernel's evaluations alone.
What is not claimed. The premises, at any list of rounds. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.HpubPointwise
import Johnson.Desc.K1.Law.DoorThreeAtLater

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.First.FillSent (SentData sentIsB whereIsP link_of_sentIs
  whereIs_of_sentIs)
open VerifiableInference.Desc.K9 (segAt? Ahead aheadOf aheadIn seatAt rowBitsOf placeBitsOf
  rowBits_of placeBits_of)
open VerifiableInference.Desc.Ground (shapesIn)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13)
open VerifiableInference.Desc.K13.Law (openAt plus13)
open VerifiableInference.Desc.K12.Door (K12Data)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix)

/-! ## 1 Where the binder bites: the kernel's facts -/

/-- Every item `forms` that is open in front of sub-protocol k passes c. -/
def formsAtB (links : List ModelPart) (ps : List Place) (k : ℕ) (c : ℕ → Bool) : Bool :=
  (openAt links ps k).all fun i =>
    match i with
    | .forms m _ _ => c m
    | _ => true

theorem formsAt_of {links : List ModelPart} {ps : List Place} {k : ℕ} {c : ℕ → Bool}
    (h : formsAtB links ps k c = true) {m j : ℕ} {r : String}
    (hi : Item.forms m j r ∈ openAt links ps k) : c m = true :=
  List.all_eq_true.1 h _ hi

theorem formsAt_full : ((List.range 25).all fun l =>
    formsAtB linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2)
      (fun _ => false) &&
    formsAtB linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l true + 2)
      (· == l)) = true := by
  decide +kernel

theorem sent1In_mw : ((List.range 25).all fun l =>
    inSetB mwMore linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l true + 2)
      (.more (some l) "frame.sentIs1")) = true := by
  decide +kernel

/-- **The tests can fail**: in front of segment 3's digits some `forms` is open; and in front of its
reads "frame.sentIs1" does not stand yet. -/
theorem aheadTests_fail :
    formsAtB linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 true + 2)
      (fun _ => false) = false ∧
    inSetB mwMore linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 false + 2)
      (.more (some 3) "frame.sentIs1") = false := by
  decide +kernel

/-! ## 2 `AheadMeets` at two states -/

/-- **A TEST on the list of rounds**, after the term of `K9.aheadOf`. -/
def aheadAtB (shape : Params.ReqShape) (sent : ℕ → List (ℕ × ℕ)) (P : Par) (l n01 nT : ℕ) : Bool :=
  (List.range P.sent.size).all fun i =>
    ((((shape.link[l]?.map (·.messages)).getD [])[n01 + i]?).all fun M =>
      (sent M.moment)[((((shape.link[l]?.map (·.messages)).getD []).take (n01 + i)).filter fun x =>
          x.moment == M.moment).length]? ==
        some (nT + (layOf P).tree.getD i 0, (layOf P).part.getD i 0) &&
      (shapesOf P)[i]? == some M.shape)

/-- **The test can fail**: where the table's numbers give no seat at all, it refuses every place
that sends a message for which the shape has one. -/
theorem aheadAt_fails (shape : Params.ReqShape) (P : Par) (l n01 nT : ℕ) (M : Params.ReqMessage)
    (hP : 0 < P.sent.size)
    (hM : ((shape.link[l]?.map (·.messages)).getD [])[n01 + 0]? = some M) :
    aheadAtB shape (fun _ => []) P l n01 nT = false := by
  cases h : aheadAtB shape (fun _ => []) P l n01 nT with
  | false => rfl
  | true =>
    have ht := List.all_eq_true.1 h 0 (List.mem_range.2 hP)
    rw [hM] at ht
    simp at ht

theorem aheadMeets_of {d : SentData} {l : ℕ} {P : Par} {shape : Params.ReqShape}
    {sent : ℕ → List (ℕ × ℕ)} {own : List (ℕ × ℕ)} {s s' : S} (h0 : sentIsB d l s = true)
    (h1 : sentIsB (ownPlus d l (idsOf P s.st.oracles.size)) l s' = true)
    (hSh : ∀ Lk, s.link? = some Lk → Lk.check.frame.shape = shape)
    (hBk : Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size)
    (hfull : s.book.place.size = s.st.oracles.size)
    (hShapes : shapesIn s'.st = shapesIn s.st ++ shapesOf P) (hCodes : s'.st.codes = s.st.codes)
    (hAt : aheadAtB shape sent P l (d.own l).size s.book.trees.size = true) :
    AheadMeets sent own (idsOf P s.st.oracles.size).toList s s' := by
  intro a b c hh o ha hb hah hw _
  obtain ⟨_, hLa, _, _, _⟩ := segAt_some ha
  obtain ⟨_, hLb, _, _, hbk⟩ := segAt_some hb
  have hsta := segAt_st ha
  have hstb := segAt_st hb
  unfold aheadIn at hah
  obtain ⟨hof, hcon⟩ := Option.filter_eq_some_iff.1 hah
  unfold aheadOf at hof
  split at hof
  · rename_i hc
    obtain ⟨A, _, e⟩ := Option.bind_eq_some_iff.1 hof
    split at e
    · exact nomatch e
    · rename_i hnone
      obtain ⟨ms, hms, e⟩ := Option.bind_eq_some_iff.1 e
      obtain ⟨M, hMm, e⟩ := Option.bind_eq_some_iff.1 e
      split at e
      · exact nomatch e
      · obtain ⟨z, hz, e⟩ := Option.map_eq_some_iff.1 e
        subst e
        have hcon' : own.contains z = true := hcon
        have hw' : b.L.check.frame.whereIs c.1 A.message = some o := hw
        have hc' : c.1 = l := (eq_of_beq hc).trans (link_of_sentIs hLa h0)
        -- in front the message is found nowhere: its number is not below the length of "own"
        rw [whereIs_of_sentIs hLa h0 c.1 A.message, hc'] at hnone
        unfold whereIsP at hnone
        rw [if_pos (beq_self_eq_true l)] at hnone
        have i1 : (d.own l).size ≤ A.message := by
          by_contra hn
          rw [Array.getElem?_eq_getElem (by omega)] at hnone
          cases hnone
        -- behind it is found among the new numbers
        rw [whereIs_of_sentIs hLb h1 c.1 A.message, hc'] at hw'
        unfold whereIsP at hw'
        rw [if_pos (beq_self_eq_true l)] at hw'
        have eo : (ownPlus d l (idsOf P s.st.oracles.size)).own l =
            d.own l ++ idsOf P s.st.oracles.size := if_pos rfl
        rw [eo, Array.getElem?_append_right i1] at hw'
        obtain ⟨i, hi0⟩ : ∃ i, i = A.message - (d.own l).size := ⟨_, rfl⟩
        rw [← hi0] at hw'
        have hi : i < P.sent.size := by
          by_contra hn
          rw [Array.getElem?_eq_none (by rw [idsOf_size]; omega)] at hw'
          cases hw'
        unfold idsOf at hw'
        rw [Array.getElem?_map, Array.getElem?_range, if_pos hi] at hw'
        have ho : i + s.st.oracles.size = o := Option.some.inj hw'
        -- the test at i
        have ht := List.all_eq_true.1 hAt i (List.mem_range.2 hi)
        rw [hSh _ hLa, hc'] at hms
        rw [hms] at ht
        simp only [Option.getD_some] at ht
        have hidx : (d.own l).size + i = A.message := by omega
        rw [hidx, hMm] at ht
        simp only [Option.all_some, Bool.and_eq_true, beq_iff_eq] at ht
        obtain ⟨t1, t2⟩ := ht
        rw [hz] at t1
        have hzz := Option.some.inj t1
        -- the new message in the statement behind
        have hs1 : (shapesIn s'.st)[o]? = some M.shape := by
          rw [hShapes, List.getElem?_append_right (by rw [shapesIn_length]; omega),
            shapesIn_length, ← ho, Nat.add_sub_cancel]
          exact t2
        unfold shapesIn at hs1
        rw [List.getElem?_map, Array.getElem?_toList] at hs1
        obtain ⟨Xo, hXo, hXs⟩ := Option.map_eq_some_iff.1 hs1
        refine ⟨?_, ?_, ?_⟩
        · show seatAt own b.d.book o = some z
          unfold seatAt
          rw [hbk, ← ho, Nat.add_comm i, hBk.newer hfull hi, ← hzz]
          show (if own.contains z = true then some z else none) = some z
          rw [if_pos hcon']
        · show b.d.st.rowBits o .main = rowBitsOf M.shape .main
          rw [hstb, rowBits_of s'.st o Xo .main hXo, hXs]
        · show b.d.st.placeBits o .main = placeBitsOf a.d.st.codes M.shape .main
          rw [hstb, hsta, placeBits_of s'.st o Xo .main hXo, hXs, hCodes]
  · exact nomatch hof

/-! ## 3 The binder -/

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

/-- **THE BINDER hmeet OF k01_fifty, AT THE WIDER MEANING**, with the shape asked at x alone. -/
theorem hmeet_plus13 (hM : Mg₀.more = {}) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
    (hAt : ∀ l, l < 25 → aheadAtB Dm.shape (Dm.N.sent l) (parL Z Bs.G₀ l true) l
      (Dm.pubD.dS1.own l).size (Dm.N.treesAt (flatPlacesOf linksFull true)[noL l true]?) = true) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y m j r,
      YesOf (blkL Z Bs.G₀ l d X arrs) x x' →
      InAt Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true)
        (noL l d) x y →
      (∀ Lk, x.2.link? = some Lk → Lk.check.frame.shape = Dm.shape) →
      Item.forms m j r ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) →
      ∀ p ∈ Dm.pubD.runs m j r, Dm.pubD.ah p.1 p.2 = true →
      AheadMeets (Dm.N.sent m) (Dm.N.group m)
        (idsOf (parL Z Bs.G₀ l d) x.2.st.oracles.size).toList x.2 x'.2 := by
  intro l hl d X arrs _ x x' y m j r hy hIn hshape hf _ _ _
  have hk := List.all_eq_true.1 formsAt_full l (List.mem_range.2 hl)
  rw [Bool.and_eq_true] at hk
  cases d with
  | false => exact absurd (formsAt_of hk.1 hf) (by simp)
  | true =>
    have hm : m = l := eq_of_beq (formsAt_of hk.2 hf)
    subst hm
    obtain ⟨-, rs, gs, hfit, hd⟩ := hy
    have hlen : rs.length = 2 :=
      (Keeps.fit_length _ _ hfit).trans (rounds_blkL Z Bs.G₀ m true X arrs)
    obtain ⟨r₁, r₂, rfl⟩ : ∃ r₁ r₂, rs = [r₁, r₂] := by
      match rs, hlen with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    have hin : Pub.more (some m) "frame.sentIs1" ∈
        (First.pubSets (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull
          (flatPlacesOf linksFull true))[noL m true]?.getD [] := by
      rw [plus13_more_closed Dm dk Mg₀ hM]
      exact inSet_of (List.all_eq_true.1 sent1In_mw m (List.mem_range.2 hl))
    have h0 := inAt_pub hIn _ (List.mem_append_left _ hin)
    rw [pub_plus13, First.pubAll_more_sentIs1] at h0
    obtain ⟨hb, hTr⟩ := inAt_book hIn
    have h1 := sentIs_laterAt Bs.G₀.first (gpOf Z) m _ 2 arrs x.2 x'.2 _ _ gs hd Dm.pubD.dS1 m h0
    exact aheadMeets_of h0 h1 hshape
      (laterSend_laterAt Bs.G₀.first (gpOf Z) m _ 2 arrs x.2 x'.2 _ gs rfl hd).2.2 hb
      (laterSeated_blkL Z Bs.G₀ m true X arrs x.2 x'.2 _ gs rfl hd).2.1
      (laterGrows_laterAt Bs.G₀.first (gpOf Z) m _ 2 arrs x.2 x'.2 _ gs hd).1
      (by rw [hTr]; exact hAt m hl)

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.formsAt_full
#print axioms VerifiableInference.Desc.K1.sent1In_mw
#print axioms VerifiableInference.Desc.K1.aheadTests_fail
#print axioms VerifiableInference.Desc.K1.aheadAt_fails
#print axioms VerifiableInference.Desc.K1.aheadMeets_of
#print axioms VerifiableInference.Desc.K1.hmeet_plus13
