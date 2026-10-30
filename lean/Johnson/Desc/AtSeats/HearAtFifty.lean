-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/HearAtFifty.lean: A PIECE OF THE ROW K01_law: THE
FIELD "hear" OF `IM.Shares` (GrownJoin.lean: the ten shares from which (S1) follows at the proof
file's first chain) CUT TO KIND K1, IN THAT STRUCTURE's OWN LETTERS: `IM.Hands` (HandsDef.lean:
what one sub-protocol owes) at kind K1's fifty later sendings: at every link l < 25 its reads' place
and its digits' place. A cast: calls alone; nothing new is proved of a sub-protocol's step.
On words: "the state" is the value of type S that the fold of the IOP as written in Lean carries
from one sub-protocol to the next; "the lot" is the list of sub-protocols that a kind's files hand
to the proof file's description (`ProofFile.onlineFirstChainBlockTables`).
OBJECT. `IM.Hands N linksW placesW (EPub z Mg linksW placesW) ft (14 * l + i + 2) b'`, b' the lot's
own sub-protocol at the address (1, some l, i + 1, K1), 1 ≤ i.
USER. Whoever fills `IM.Shares.hear` by cases on the kind.
LETTERS. N, Mg, z, ft, Z as in `hands_later_pub` (Johnson/Desc/K1/Law/HandsPubAtFifty.lean);
G₀: its G; l, i, b': the field's own.
  linksW_full, placesW_full   (a) the written list of Johnson/IMR/WrittenList.lean IS
                    the table's (`Sound.linksFull`, `flatPlacesOf linksFull true`): by the kernel.
  k1_at_kinds, k1_index       (b) behind a link's first place `kindsBeforeBatching` says K1 at two indices
                    alone: 3 and 5; at the head's link (l = 24) 4 and 6: `IM.k1Ix l d`.
  LotLetters G l d X arrs     the two letters of `blkL` that the lot itself fills: X is the
                    ground's entry number l; arrs the arrays that `K1.linkNumbers` gives for X (the
                    reads' at d = false, the digits' at d = true).
  lot_is_blkL       (c) the lot's own sub-protocol at such an address IS
                    `(blkL Z G l d X arrs).retype` at letters with `LotLetters`: by `IM.lot_K1`, `IM.k1_mem`, `IM.numbers_pieces`
                    (K1Seat.lean). NO SCOPE AND NO OPENING OF THE DESCRIPTION IS ASKED: so
                    `block_by_place` is not needed.
  hear_K1           **THE SHARE.**
PREMISES THAT STAY, BY NAME: `hands_later_pub`'s own eight, each asked at every l < 25 and both d:
hinj, trees, msgs, hP (on the list of rounds' numbers) · hg (the open link's frame has the plan's
group of l) · hOrd, hRide, hNew (the three arms of the field "more"). The three arms speak of
`blkL Z G₀ l d X arrs`: they are asked at the X and arrs with `LotLetters G₀ l d X arrs` alone.
What is not claimed. That any of the eight holds at the numbers and the meaning that are meant.
The other 102 places of the field "hear". Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.HandsPubAtFifty
import Johnson.IMR.WrittenList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning kindsBeforeBatching flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.K13.Law (openAt)
open VerifiableInference.Desc.K1 (blkL parL noL momL tiedL YesOf InB laterSeatsB layOf)
open OnBytes.Model.Stages (LinkH)
open IM (linksW placesW subAt k1Ix)
open ProofFile (Cl)

variable {Pp W : Type}

/-! ## (a) One written list under two names -/

/-- The written row of the links' sorts: the two names have one value. -/
theorem linksW_full : linksW = linksFull := by decide +kernel

/-- So the written list of places. -/
theorem placesW_full : placesW = flatPlacesOf linksFull true := by
  unfold placesW
  rw [linksW_full]

/-! ## (b) Where `kindsBeforeBatching` says K1 -/

/-- Behind the first place: at 3 and 5; in the head's link at 4 and 6. (A head's link that were the
first of its row would have K1 at 1 too: hf shuts that out.) -/
theorem k1_at_kinds (sub : ModelPart) (f : Bool) (i : ℕ) (hf : sub = .head → f = false) (hi : 1 ≤ i)
    (h : (kindsBeforeBatching sub f)[i]? = some KindName.K1) :
    (sub = .head ∧ (i = 4 ∨ i = 6)) ∨ (sub ≠ .head ∧ (i = 3 ∨ i = 5)) := by
  have h9 : i < 9 := by
    have h1 := (List.getElem?_eq_some_iff.1 h).1
    have h2 : (kindsBeforeBatching sub f).length ≤ 9 := by cases sub <;> cases f <;> decide
    omega
  interval_cases i <;> revert h hf <;> cases sub <;> cases f <;> decide

/-- At link number l of the written row. -/
theorem k1_index {l i : ℕ} (hi : 1 ≤ i)
    (h : (kindsBeforeBatching (subAt l) (l == 0))[i]? = some KindName.K1) :
    i = 3 + (if l = 24 then 1 else 0) ∨ i = 5 + (if l = 24 then 1 else 0) := by
  by_cases h24 : l = 24
  · rw [if_pos h24]
    subst h24
    rcases k1_at_kinds _ _ i (fun _ => by decide) hi h with ⟨-, e⟩ | ⟨hs, -⟩
    · omega
    · exact absurd (by decide) hs
  · rw [if_neg h24]
    have hne : subAt l ≠ .head := by
      intro hs
      unfold subAt at hs
      rw [if_neg h24] at hs
      split at hs <;> cases hs
    rcases k1_at_kinds _ _ i (fun hs => absurd hs hne) hi h with ⟨hs, -⟩ | ⟨-, e⟩
    · exact absurd hs hne
    · omega

/-! ## (c) The lot's own sub-protocol at the address -/

/-- The two letters of `blkL` that the lot itself fills at link l. -/
def LotLetters (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH) (arrs : Option (List ℕ)) : Prop :=
  G.built[l]? = some X ∧ ∃ reads digits : Option (List ℕ),
    K1.linkNumbers G X = some (k1Ix l false + 1, k1Ix l true + 1, reads, digits) ∧
      arrs = cond d digits reads

/-- **The lot's own sub-protocol at a later address of kind K1 is `blkL`'s, carried over.** -/
theorem lot_is_blkL {Z : ProofFile.Pub} {G : ProofFile.Ground} {l i : ℕ} {b' : Block S Cl} (hi : 1 ≤ i)
    (hk : (kindsBeforeBatching (subAt l) (l == 0))[i]? = some KindName.K1)
    (hL : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G)
    (hp : b'.place = { chain := 1, link := some l, piece := i + 1, kind := .K1 }) :
    ∃ (d : Bool) (X : LinkH) (arrs : Option (List ℕ)), LotLetters G l d X arrs ∧ i = k1Ix l d ∧
      b' = ((blkL Z G l d X arrs).retype : Block S Cl) := by
  obtain ⟨L, hL, hb⟩ := hL
  obtain ⟨x, hx, rfl⟩ := IM.lot_K1 hL hb (by rw [hp]) (l := l) (by rw [hp])
  have hk' := k1_index hi hk
  have ht : (if l = 24 then 1 else 0) ≤ 1 := by split <;> omega
  rcases IM.k1_mem hx with rfl | ⟨l', X, pr, pd, reads, digits, hX, hn, rfl | rfl⟩
  · exfalso
    have e : (1 : ℕ) = i + 1 := congrArg Place.piece hp
    omega
  · obtain rfl : l' = l := Option.some.inj (congrArg Place.link hp)
    have epc : pr = i + 1 := congrArg Place.piece hp
    have hnp := IM.numbers_pieces hn
    have h1 : i = 3 + (if l' = 24 then 1 else 0) ∧
        pd = 5 + (if l' = 24 then 1 else 0) + 1 := by
      revert hk' ht
      generalize (if l' = 24 then 1 else 0) = t
      intro hk' ht
      omega
    obtain ⟨rfl, rfl⟩ := h1
    subst epc
    exact ⟨false, X, reads, ⟨hX, reads, digits, hn, rfl⟩, rfl, rfl⟩
  · obtain rfl : l' = l := Option.some.inj (congrArg Place.link hp)
    have epc : pd = i + 1 := congrArg Place.piece hp
    have hnp := IM.numbers_pieces hn
    have h1 : i = 5 + (if l' = 24 then 1 else 0) ∧
        pr = 3 + (if l' = 24 then 1 else 0) + 1 := by
      revert hk' ht
      generalize (if l' = 24 then 1 else 0) = t
      intro hk' ht
      omega
    obtain ⟨rfl, rfl⟩ := h1
    subst epc
    exact ⟨true, X, digits, ⟨hX, reads, digits, hn, rfl⟩, rfl, rfl⟩

/-! ## The share -/

/-- **THE FIELD "hear" OF `IM.Shares`, CUT TO KIND K1.** -/
theorem hear_K1 (N : Numbers) (Mg : Meaning Pp W) (z : Pp) (ft : ℕ) (Z : ProofFile.Pub)
    (G₀ : ProofFile.Ground)
    (hinj : ∀ l < 25, ∀ d : Bool,
      ∀ m' ∈ First.rowSegs (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)),
        N.groupAt m' = N.groupAt l → m' = l)
    (trees : ∀ l < 25, ∀ d : Bool, N.treesAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.treesAt (flatPlacesOf linksFull true)[noL l d]? + (layOf (parL Z G₀ l d)).shapes.size)
    (msgs : ∀ l < 25, ∀ d : Bool, N.msgsAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + (parL Z G₀ l d).sent.size)
    (hP : ∀ l < 25, ∀ d : Bool, laterSeatsB N (parL Z G₀ l d) l (momL d)
      (N.treesAt (flatPlacesOf linksFull true)[noL l d]?) = true)
    (hg : ∀ l < 25, ∀ d : Bool, ∀ s : S, s.failed = none →
      IM.XK N linksFull (flatPlacesOf linksFull true)
        (EPub z Mg linksFull (flatPlacesOf linksFull true)) (noL l d) s = true →
      ∀ L, s.link? = some L → L.check.frame.group = N.groupAt l)
    (hOrd : ∀ l < 25, ∀ (d : Bool) (X : LinkH) (arrs : Option (List ℕ)),
      LotLetters G₀ l d X arrs → ∀ x x', YesOf (blkL Z G₀ l d X arrs) x x' →
      InB N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x → Mg.inOrder x' = true)
    (hRide : ∀ l < 25, ∀ (d : Bool) (X : LinkH) (arrs : Option (List ℕ)),
      LotLetters G₀ l d X arrs → ∀ x x' q, YesOf (blkL Z G₀ l d X arrs) x x' →
      InB N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x →
      q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) →
      q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)) →
      Mg.pub q x' = true)
    (hNew : ∀ l < 25, ∀ (d : Bool) (X : LinkH) (arrs : Option (List ℕ)),
      LotLetters G₀ l d X arrs → ∀ x x' q, YesOf (blkL Z G₀ l d X arrs) x x' →
      InB N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x → q ∈ tiedL Mg.more l d →
      Mg.pub q x' = true) :
    ∀ l < 25, ∀ (i : ℕ) (b' : Block S Cl), 1 ≤ i →
      (kindsBeforeBatching (subAt l) (l == 0))[i]? = some KindName.K1 →
      (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) →
      b'.place = { chain := 1, link := some l, piece := i + 1, kind := .K1 } →
      IM.Hands N linksW placesW (EPub z Mg linksW placesW) ft (14 * l + i + 2) b' := by
  intro l hl i b' hi hk hL hp
  obtain ⟨d, X, arrs, hLO, rfl, rfl⟩ := lot_is_blkL hi hk hL hp
  rw [placesW_full, linksW_full]
  exact K1.hands_later_pub N Mg z ft Z G₀ l hl d X arrs _ ⟨rfl, under_refl _⟩ (hinj l hl d)
    (trees l hl d) (msgs l hl d) (hP l hl d) (hg l hl d) (hOrd l hl d X arrs hLO)
    (hRide l hl d X arrs hLO) (hNew l hl d X arrs hLO)

end HashBuild

#print axioms HashBuild.linksW_full
#print axioms HashBuild.placesW_full
#print axioms HashBuild.k1_at_kinds
#print axioms HashBuild.k1_index
#print axioms HashBuild.lot_is_blkL
#print axioms HashBuild.hear_K1
