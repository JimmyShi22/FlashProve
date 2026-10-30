-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/HpubPointwise.lean: **hpub, in the
pointwise form**: the binder hpub of k01_fifty (K01Law.lean) at the wider meaning
`plus13 (d13 Dm) dk (mgAll Dm Mg₀)`, with nothing asked at a state outside the promise.
WHY. `hpub_of` and `hpub_reads_full` (HpubOf.lean, HpubAtFull.lean), and `hpub_plus13`
(HpubAtPlus13.lean) over them, take `SecondFound` and `ReadersStay` at EVERY pair of states
with an accept between them. No member of such a premise is known. Their proof spends both at the
piece's own two states alone, where the promise is in hand.
  `secondAtB shape l n0 n1`   A TEST WITH CODE on the request's shape: every message of moment 1 of
                   link l stands at an index from n0 up to n0 + n1. `secondAt_of`: what its accept
                   says. `secondAt_fails`: it can fail
  `secondFound_of`   **`SecondFound` at two states**, from the test "frame.sentIs" in front, the
                   same test behind at the list "own" with the new numbers laid behind it, the
                   shape of the open link's frame in front, and `secondAtB`
  `secondFound_reads`   that at an accept of a link's reads, from inside the promise:
                   "frame.sentIs" off the promise (`sentIn_mw`), `sentIs_k1Reads` behind
  `hpub_point`     **the binder.** The tied half is `hpub_of`'s own proof over
                   `pub_formsIn_new_later` (GoAtLaterForms.lean); the made half is
                   `sentIs1_made` (HpubAtPlus13.lean)
PREMISES, BY NAME. hM. Three tests with code on the list of rounds: hOwn1 (`own1B`), hP
(`laterSeatsB` at the reads), hAt (`secondAtB` at each link). And two at the piece's own two states,
behind the promise, "no mark" and the piece's accept: hshape (the open link's frame's shape is
`Dm.shape`) and hRd (`ReadersStay`).
THE LETTERS. F, base, cc, e are free, and nothing is asked of d₁ d₂: the binder, with its two tags
and its equation on the written data, is an instance.
What is not claimed. The premises, at any list of rounds. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.HpubAtPlus13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Iop Run OnBytes.Maker OnBytes.Flat
open Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More PubData pubAll
  flatPlacesOf)
open VerifiableInference.Desc.First.FillSent (SentData sentIsB whereIsP link_of_sentIs
  whereIs_of_sentIs)
open VerifiableInference.Desc.K9 (segAt? atMoment1)
open VerifiableInference.Desc.Sound (Frame linksFull MsgT MgData CellsQ mgAll d13)
open VerifiableInference.Desc.K13.Law (openAt plus13)
open VerifiableInference.Desc.K12.Door (K12Data)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix)

/-! ## 1 The test on the shape -/

/-- Every message of moment 1 of link l stands at an index from n0 up to n0 + n1. -/
def secondAtB (shape : Params.ReqShape) (l n0 n1 : ℕ) : Bool :=
  (List.range ((shape.link[l]?.map (·.messages)).getD []).length).all fun i =>
    ((((shape.link[l]?.map (·.messages)).getD [])[i]?).all fun m =>
      m.moment != 1 || (decide (n0 ≤ i) && decide (i < n0 + n1)))

theorem secondAt_of {shape : Params.ReqShape} {l n0 n1 i : ℕ} {M : Params.ReqMessage}
    (h : secondAtB shape l n0 n1 = true)
    (hM : ((shape.link[l]?).bind fun x => x.messages[i]?) = some M)
    (hm : (M.moment == 1) = true) : n0 ≤ i ∧ i < n0 + n1 := by
  obtain ⟨X, hX, hi⟩ := Option.bind_eq_some_iff.1 hM
  unfold secondAtB at h
  rw [hX] at h
  simp only [Option.map_some, Option.getD_some] at h
  have hlt : i < X.messages.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hi
    cases hi
  have h1 := List.all_eq_true.1 h i (List.mem_range.2 hlt)
  rw [hi] at h1
  have hb : (M.moment != 1) = false := by
    unfold bne
    rw [hm]
    rfl
  simp only [Option.all_some, hb, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h1
  exact h1

/-- **The test can fail**: one link with one message of moment 1, and no room for it. -/
theorem secondAt_fails :
    secondAtB { (default : Params.ReqShape) with
      link := [{ plain := 0, messages := [{ (default : Params.ReqMessage) with moment := 1 }] }] }
      0 0 0 = false := by
  decide

/-! ## 2 `SecondFound` at two states -/

theorem secondFound_of {d : SentData} {l : ℕ} {ids : Array ℕ} {shape : Params.ReqShape}
    {s s' : S} (h0 : sentIsB d l s = true) (h1 : sentIsB (ownPlus d l ids) l s' = true)
    (hSh : ∀ Lk, s.link? = some Lk → Lk.check.frame.shape = shape)
    (hAt : secondAtB shape l (d.own l).size ids.size = true) : SecondFound ids.toList s s' := by
  intro a b c A ha hb _ hm1
  obtain ⟨_, hLa, _, _, _⟩ := segAt_some ha
  obtain ⟨_, hLb, _, _, _⟩ := segAt_some hb
  unfold atMoment1 at hm1
  rw [Bool.and_eq_true] at hm1
  obtain ⟨hc, hmm⟩ := hm1
  have hc' : c.1 = l := (eq_of_beq hc).trans (link_of_sentIs hLa h0)
  rw [hSh _ hLa, hc'] at hmm
  cases hM : ((shape.link[l]?).bind fun x => x.messages[A.message]?) with
  | none =>
    rw [hM] at hmm
    cases hmm
  | some M =>
    rw [hM] at hmm
    obtain ⟨i1, i2⟩ := secondAt_of hAt hM hmm
    rw [whereIs_of_sentIs hLb h1 c.1 A.message, hc']
    unfold whereIsP
    rw [if_pos (beq_self_eq_true l)]
    have e : (ownPlus d l ids).own l = d.own l ++ ids := if_pos rfl
    rw [e, Array.getElem?_append_right i1]
    have hlt : A.message - (d.own l).size < ids.size := by omega
    have ho : ids[A.message - (d.own l).size]? = some ids[A.message - (d.own l).size] :=
      Array.getElem?_eq_getElem hlt
    exact ⟨_, List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact ho), ho⟩

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **`SecondFound` over an accept of a link's reads, from inside the promise.** -/
theorem secondFound_reads (hM : Mg₀.more = {}) (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ)
    (hl : l < 25) (X : LinkH) (arrs : Option (List ℕ)) (x x' : P × S) (y : Strs)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (h2 : rs.length = 2)
    (hd : (blkL Z G l false X arrs).decide x.2 rs gs = .ok x'.2)
    (hIn : InAt Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true)
      (noL l false) x y)
    (hshape : ∀ Lk, x.2.link? = some Lk → Lk.check.frame.shape = Dm.shape)
    (hAt : secondAtB Dm.shape l (Dm.pubD.dS.own l).size (parL Z G l false).sent.size = true) :
    SecondFound (idsOf (parL Z G l false) x.2.st.oracles.size).toList x.2 x'.2 := by
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  have hin : Pub.more (some l) "frame.sentIs" ∈
      (First.pubSets (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull
        (flatPlacesOf linksFull true))[noL l false]?.getD [] := by
    rw [plus13_more_closed Dm dk Mg₀ hM]
    exact inSet_of (List.all_eq_true.1 sentIn_mw l (List.mem_range.2 hl))
  have h0 := inAt_pub hIn _ (List.mem_append_left _ hin)
  rw [pub_plus13, First.pubAll_more_sentIs] at h0
  have h1 := sentIs_k1Reads Z G l X _ arrs x.2 x'.2 r₁ r₂ gs hd Dm.pubD.dS l h0
  exact secondFound_of h0 h1 hshape (by rw [idsOf_size]; exact hAt)

end

/-! ## 3 The binder -/

section
variable {Xi Tok Cl : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public} {F : Frame}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

/-- **THE BINDER hpub OF k01_fifty, AT THE WIDER MEANING, POINTWISE.** -/
theorem hpub_point (hM : Mg₀.more = {}) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
    (hOwn1 : own1B Dm.shape Dm.N Dm.links Z Bs.G₀ = true)
    (hP : ∀ l, l < 25 → laterSeatsB Dm.N (parL Z Bs.G₀ l false) l 1
      (Dm.N.treesAt (flatPlacesOf linksFull true)[14 * l + k1Ix l false + 2]?) = true)
    (hAt : ∀ l, l < 25 → secondAtB Dm.shape l (Dm.pubD.dS.own l).size
      (parL Z Bs.G₀ l false).sent.size = true) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ (base : ℕ) (d₁ d₂ : RDT) (cc e : ℕ),
      ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (c' : Block S Cl),
      c'.UnderR ((blkL Z Bs.G₀ l d X arrs).retype : Block S Cl) →
      ∀ (z : ProofFile.InstPub) (a : S × F.E.Str) τ x,
      Sound.onQ Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true)
        (fun s : S => (z, s)) (noL l d) a → a.1.failed = none →
      (sendPiece (W := Wit (CellsQ rows cols) Tok MsgT) (F := F) c' base d₁ d₂ cc e).ior.red.out
        a τ = some x →
      (∀ Lk, a.1.link? = some Lk → Lk.check.frame.shape = Dm.shape) →
      (∀ j r, Pub.formsInT l j r ∈ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true)
        (14 * l + k1Ix l false + 2)) → ReadersStay Dm.pubD l j r a.1 x.1) →
      ∀ q ∈ tiedL (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more l d,
        (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub q (z, x.1) = true := by
  intro l hl d base d₁ d₂ cc e X arrs _ c' hu z a τ x ha hm hx hshape hRd q hq
  rw [plus13_more_closed Dm dk Mg₀ hM] at hq
  have hmade := List.all_eq_true.1 made_mw l (List.mem_range.2 hl)
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hmade
  cases d with
  | true =>
    have hq' : q ∈ [] ++ madeAt mwMore linksFull (flatPlacesOf linksFull true)
        (14 * l + k1Ix l true + 2) := hq
    rw [hmade.1] at hq'
    simp at hq'
  | false =>
    have hq' : q ∈ tiedAt linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2) ++
        madeAt mwMore linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2) := hq
    rw [hmade.2] at hq'
    obtain ⟨rs, gs, h2, hd⟩ := yes_of_piece (W := Wit (CellsQ rows cols) Tok MsgT) (F := F)
      (blkL Z Bs.G₀ l false X arrs) (rounds_blkL Z Bs.G₀ l false X arrs) c' hu base d₁ d₂ cc e
      a τ x hx
    have hIn : InAt Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true)
        (noL l false) (z, a.1) (Sound.strsOf F a.2) := ⟨ha, hm⟩
    rcases List.mem_append.1 hq' with ht | hmk
    · obtain ⟨j, r, rfl, ho⟩ := tied_reads_full l hl q ht
      have h0 := inAt_pub hIn _ (List.mem_append_right _ ho)
      obtain ⟨hb, hTr⟩ := inAt_book hIn
      rw [pub_plus13] at h0 ⊢
      exact pub_formsIn_new_later (laterSend_k1Reads Z Bs.G₀ l X _ arrs) Dm.pubD _ (z, a.1)
        (z, x.1) rs gs h2 hd hb l j r (hRd j r ho) 1 _ (by decide) hTr (hP l hl)
        (secondFound_reads Dm dk Mg₀ hM Z Bs.G₀ l hl X arrs (z, a.1) (z, x.1) _ rs gs h2 hd hIn
          hshape (hAt l hl)) h0
    · obtain rfl := List.mem_singleton.1 hmk
      exact sentIs1_made Dm dk Mg₀ hM Z Bs.G₀ hOwn1 l hl X arrs (z, a.1) (z, x.1)
        (Sound.strsOf F a.2) rs gs h2 hd hIn

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.secondAt_of
#print axioms VerifiableInference.Desc.K1.secondAt_fails
#print axioms VerifiableInference.Desc.K1.secondFound_of
#print axioms VerifiableInference.Desc.K1.secondFound_reads
#print axioms VerifiableInference.Desc.K1.hpub_point
