-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/K1Seat.lean: k1Quiet's two strings follow Johnson/Desc/ProofFile/Lots/PureLots.lean. k1_first_of's LaidFramed follows from the stronger Joined of Johnson/IMR/FirstSeats.lean's k1_first_sits.
Where the rest of this head and the Lean text differ, the Lean text holds.
A LAW ABOUT ProofFile.chainBy AND ProofFile.pureSeat, NO PART OF THEM: K1's blocks (the commitments) at their
places inside the links of onlineDescription's first chain: link 0's first place · every link's
reads' place, with the quiet step behind the reads · every link's digits' place.
OBJECT. THE SEATED CONSTANTS, each carried over by Block.retype: (first) K1.firstSegmentOpening G₀.first (K1.gpOf Z) (Johnson/Desc/K1/First.lean) at F.first.links[0].hear[0] · (reads) IM.k1Reads Z G₀ l Xl pr reads := k.andThen k.name (IM.k1Quiet G₀ l Xl),
k := K1.laterAt G₀.first (K1.gpOf Z) l pr 1 reads (Johnson/Desc/K1/Places.lean), k1Quiet: k1Pure's joining, to the letter (Johnson/Desc/ProofFile/Lots/PureLots.lean: k1Pure; Lots/Makers.lean: orLoud · readsQuietAt) at hear[3] (the head's link: hear[4]) ·
(digits) K1.laterAt G₀.first (K1.gpOf Z) l pd 2 digits at hear[5] (the head's: hear[6]).
USER. k1_first_plan (K1's first place: planOk): no caller. The others: the quiet step behind the
reads (piece 4) · K1's laws.
LETTERS. As in Johnson/IMR/K6Seat.lean; Xl: G₀.built[l]? = some Xl · (pr, pd, reads, digits):
K1.linkNumbers G₀ Xl = some (pr, pd, reads, digits).

Compiled with the whole library.
THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): WHAT NEEDS NO SCOPE STANDS AT EVERY o; WHAT STANDS ON A LAW OF THE LIBRARY OVER «publicOf … = .ok X» STANDS AT OnBytes.secondHashFunction, where publicOfO_older (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean) makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7′ | G7′bits hand every o: for these the in-scope halves are owed, at PublicCut, Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean).

  lot_K1            a block of kind K1 of a lot of the seat that stands in a link is one of k1Pure's own, carried over.
  k1_mem            what k1Pure's own blocks are: the first segment's opening, or, at a link Xl of the list at its number l with its numbers, the reads' joined block or the digits' block.
  numbers_pieces    linkNumbers gives the pieces (4, 6) or (5, 7).
  k1_first_of       in scope: link 0's first block in front of the batching is LaidFramed
                    (Johnson/IMR/FirstPlace.lean) of (K1.firstSegmentOpening G₀.first (K1.gpOf Z)).retype at
                    ⟨1, some 0, 1, K1⟩; G₀.first = Z.first (Open.first).
  k1_first_plan     WEAK: for SOME b ∈ c.blocksInOrder, tied to no place: b.planOk → K1.firstSegmentOpening's planOk.
  k1_later          at an opening's letters, at every link l and index i (2 ≤ i + 1 ≤ 9) at which kindsBeforeBatching has K1: ALONE: the reads' joined block (i + 1 = pr) or the digits' block (i + 1 = pd). No premise on scope.
  k1_reads_layers   in scope, g < 12: at c.links[2 g].hear[3]: ALONE, k1Reads Z G₀ (2 g) Xl 4 reads, with Xl.kind = 0 · Xl.g = g.

WHO PAYS THE PREMISES: as in K6Seat.lean: that onlineDescription returns in scope is a premise.
What is not claimed. At the first place: which arm, and which block of the frames' lot is joined (Johnson/IMR/FirstPlace.lean's head says why). What readsQuietAt returns. K1's place behind the links («M:4»: lot4, Johnson/Desc/ProofFile/Lot/K13At4.lean). No soundness.
-/
import Johnson.IMR.FirstPlace
import Johnson.IMR.SeatOpen
import Johnson.IMR.Subs

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open ProofFile (Cl)

/-- **A block of kind K1 that stands in a link is one of k1Pure's own, carried over.** -/
theorem lot_K1 {Z : ProofFile.Pub} {G : ProofFile.Ground} {L : ProofFile.Lot} (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z)
    {b : Block S Cl} (hb : b ∈ L.blocks G) (hk : b.place.kind = KindName.K1) {l : ℕ}
    (hl : b.place.link = some l) : ∃ x ∈ (ProofFile.k1Pure Z).own G, b = x.retype := by
  unfold ProofFile.onlineFirstChainBlockTables ProofFile.p4Pure at hL
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl)
  · rw [kind_frames Z G b hb] at hk; cases hk
  · rcases blocks_mem hb with ⟨x, hx, rfl⟩ | hb
    · exact ⟨x, hx, rfl⟩
    · exact nomatch hb
  · rw [kind_K2 Z G b hb] at hk; cases hk
  · rw [kind_K3 Z G b hb] at hk; cases hk
  · rw [kind_K4 Z G b hb] at hk; cases hk
  · rw [kind_K5 Z G b hb] at hk; cases hk
  · rw [kind_K8 Z G b hb] at hk; cases hk
  · rcases kind_K9 Z G b hb with e | e <;> rw [e] at hk <;> cases hk
  · rw [kind_K11 Z G b hb] at hk; cases hk
  · rw [kind_K12 Z G b hb] at hk; cases hk
  · rw [kind_K13 Z G b hb] at hk; cases hk
  · rcases blocks_mem hb with ⟨x, hx, rfl⟩ | hb
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
      rw [Option.mem_toList] at hw
      unfold VerifiableInference.Desc.K13.wBlock VerifiableInference.Desc.K1.wAt at hw
      obtain ⟨msg, _, rfl⟩ := Option.map_eq_some_iff.1 hw
      cases hl
    · exact nomatch hb
  · rw [kind_K13_end Z G b hb] at hk; cases hk
  · rw [kind_K6 Z G b hb] at hk; cases hk
  · rw [kind_K7_lot rfl rfl b hb] at hk; cases hk

/-- The quiet block behind the reads' sending, as k1Pure joins it (PureLots.lean). -/
def k1Quiet (G : ProofFile.Ground) (l : ℕ) (X : LinkH) : Block S Unit :=
  let piece : ℕ := if X.kind == 0 || X.kind == 1 then 4 else 5
  ProofFile.orLoud s!"link {l}: the step after the commitment before the smallness test"
    ⟨1, some l, piece, .K1⟩ "the step after the commitment that comes before the smallness test"
    (ProofFile.readsQuietAt G l X piece)

/-- The reads' place's block: K1's own with the quiet block joined. -/
def k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (pr : ℕ) (reads : Option (List ℕ)) :
    Block S Unit :=
  let k : Block S Unit :=
    VerifiableInference.Desc.K1.laterAt G.first (VerifiableInference.Desc.K1.gpOf Z) l pr 1 reads
  k.andThen k.name (k1Quiet G l X)

/-- **What k1Pure's own blocks are.** -/
theorem k1_mem {Z : ProofFile.Pub} {G : ProofFile.Ground} {x : Block S Unit} (h : x ∈ (ProofFile.k1Pure Z).own G) :
    x = VerifiableInference.Desc.K1.firstSegmentOpening G.first (VerifiableInference.Desc.K1.gpOf Z) ∨
      ∃ l X pr pd reads digits, G.built[l]? = some X ∧
        VerifiableInference.Desc.K1.linkNumbers G X = some (pr, pd, reads, digits) ∧
        (x = k1Reads Z G l X pr reads ∨
          x = VerifiableInference.Desc.K1.laterAt G.first (VerifiableInference.Desc.K1.gpOf Z) l pd 2
            digits) := by
  unfold ProofFile.k1Pure VerifiableInference.Desc.K1.lotWith at h
  dsimp only at h
  unfold VerifiableInference.Desc.K1.blocks at h
  dsimp only at h
  rcases List.mem_append.1 h with h | h
  · exact Or.inl (List.mem_singleton.1 h)
  · obtain ⟨y, hy, h⟩ := List.mem_flatMap.1 h
    obtain ⟨X, l⟩ := y
    have hX : G.built[l]? = some X := by
      rw [← Array.getElem?_toList]
      simpa using (List.mk_mem_zipIdx_iff_getElem?.1 hy)
    dsimp only at h
    split at h
    · cases h
    · rename_i pr pd reads digits hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      refine Or.inr ⟨l, X, pr, pd, reads, digits, hX, hn, ?_⟩
      rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl

theorem numbers_pieces {G : ProofFile.Ground} {X : LinkH} {pr pd : ℕ} {reads digits : Option (List ℕ)}
    (h : VerifiableInference.Desc.K1.linkNumbers G X = some (pr, pd, reads, digits)) :
    (pr = 4 ∧ pd = 6) ∨ (pr = 5 ∧ pd = 7) := by
  unfold VerifiableInference.Desc.K1.linkNumbers at h
  split at h
  · obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.1 h
    cases e
    exact Or.inl ⟨rfl, rfl⟩
  · split at h
    · obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.1 h
      cases e
      exact Or.inl ⟨rfl, rfl⟩
    · cases h
      exact Or.inr ⟨rfl, rfl⟩

section
variable {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **K1's later places: the reads' joined block, or the digits' block: ALONE.** -/
theorem k1_later (O : Open o pol lay KL F Z Bs base c A B) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub) (i : ℕ)
    (hk : (kindsBeforeBatching sub (l == 0))[i]? = some KindName.K1) (hi : 2 ≤ i + 1 ∧ i + 1 ≤ 9) :
    ∃ Lk b Xl pr pd reads digits, c.links[l]? = some Lk ∧ Lk.hear[i]? = some b ∧
      Bs.G₀.built[l]? = some Xl ∧
      VerifiableInference.Desc.K1.linkNumbers Bs.G₀ Xl = some (pr, pd, reads, digits) ∧
      ((i + 1 = pr ∧ LaidAlone ProofFile.sameReply b (k1Reads Z Bs.G₀ l Xl pr reads).retype b.name
          { chain := 1, link := some l, piece := i + 1, kind := .K1 }) ∨
        (i + 1 = pd ∧ LaidAlone ProofFile.sameReply b
          (VerifiableInference.Desc.K1.laterAt Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Z) l pd 2
            digits : Block S Unit).retype b.name
          { chain := 1, link := some l, piece := i + 1, kind := .K1 })) := by
  obtain ⟨Lk, b, e1, e2, sp, -, L, hL, b', hb', -, ep, hla⟩ :=
    chain_hear_alone O.made O.places O.chain l sub hl i .K1 hk (by decide) (by decide) hi
  obtain ⟨x, hx, rfl⟩ := lot_K1 hL hb' (by rw [ep]) (l := l) (by rw [ep])
  have hla' := hla
  rw [← alone_name hla] at hla'
  rcases k1_mem hx with rfl | ⟨l', X, pr, pd, reads, digits, hX, hn, rfl | rfl⟩
  · exfalso
    have e : (1 : ℕ) = i + 1 := congrArg Place.piece ep
    omega
  · have el : l' = l := by
      have e : (some l' : Option ℕ) = some l := congrArg Place.link ep
      exact Option.some.inj e
    subst el
    have epc : pr = i + 1 := congrArg Place.piece ep
    exact ⟨Lk, b, X, pr, pd, reads, digits, e1, e2, hX, hn, Or.inl ⟨epc.symm, hla'⟩⟩
  · have el : l' = l := by
      have e : (some l' : Option ℕ) = some l := congrArg Place.link ep
      exact Option.some.inj e
    subst el
    have epc : pd = i + 1 := congrArg Place.piece ep
    exact ⟨Lk, b, X, pr, pd, reads, digits, e1, e2, hX, hn, Or.inr ⟨epc.symm, hla'⟩⟩

end

section
variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- K1's first address. -/
abbrev k1Place0 : Place := { chain := 1, link := some 0, piece := 1, kind := .K1 }

/-- **K1 AT LINK 0's FIRST PLACE.** -/
theorem k1_first_of (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (Lk : Link S Cl) (b : Block S Cl), c.links[0]? = some Lk ∧ Lk.hear[0]? = some b ∧
      LaidFramed Z b
        (VerifiableInference.Desc.K1.firstSegmentOpening Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Z) :
          Block S Unit).retype b.name k1Place0 := by
  have hsub := subs_at hS hR O.pub O.blank (g := 0) (by decide)
  have hk : (kindsBeforeBatching .layers (0 == 0))[0]? = some KindName.K1 := by
    unfold kindsBeforeBatching
    rfl
  obtain ⟨Lk, b, e1, e2, L, hL, b', hb', ep, hla⟩ :=
    chain_hear_first O.made O.places O.chain 0 .layers hsub 0 .K1 hk (by decide)
  obtain ⟨x, hx, rfl⟩ := lot_K1 hL hb' (by rw [ep]) (l := 0) (by rw [ep])
  rcases k1_mem hx with rfl | ⟨l', X, pr, pd, reads, digits, hX, hn, rfl | rfl⟩
  · exact ⟨Lk, b, e1, e2, hla⟩
  · exfalso
    have epc : pr = 1 := congrArg Place.piece ep
    rcases numbers_pieces hn with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  · exfalso
    have epc : pd = 1 := congrArg Place.piece ep
    rcases numbers_pieces hn with ⟨-, h⟩ | ⟨-, h⟩ <;> omega

/-- **Weak as stated**: b stands under a bare ∃, not tied to K1's first place: any b ∈ c.blocksInOrder with
planOk = false meets it. Called by no file. -/
theorem k1_first_plan (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ b ∈ c.blocksInOrder, (b.planOk = true →
               (VerifiableInference.Desc.K1.firstSegmentOpening Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Z) :
                 Block S Unit).planOk = true) := by
  obtain ⟨Lk, b, e1, e2, hla⟩ := k1_first_of hS hR O
  exact ⟨b, hear_mem_flat e1 e2, fun hp => (retype_planOk _ (laid_planOk hla.laid hp)).1⟩

/-- **THE READS' PLACE AT THE LAYERS' LINKS: K1's OWN WITH THE QUIET STEP JOINED BY THE LOT: ALONE.** -/
theorem k1_reads_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ g < 12, ∃ (Lk : Link S Cl) (b : Block S Cl) (Xl : LinkH) (pd : ℕ)
        (reads digits : Option (List ℕ)),
      c.links[2 * g]? = some Lk ∧ Lk.hear[3]? = some b ∧ Bs.G₀.built[2 * g]? = some Xl ∧
      Xl.kind = 0 ∧ Xl.g = g ∧
      VerifiableInference.Desc.K1.linkNumbers Bs.G₀ Xl = some (4, pd, reads, digits) ∧
      LaidAlone ProofFile.sameReply b (k1Reads Z Bs.G₀ (2 * g) Xl 4 reads).retype b.name
        { chain := 1, link := some (2 * g), piece := 4, kind := .K1 } := by
  intro g hg
  obtain ⟨nam, -⟩ := ground_named hS hR O.pub O.blank
  obtain ⟨m, -, fm, km, gm, -⟩ := nam g hg
  have hk : (kindsBeforeBatching .layers (2 * g == 0))[3]? = some KindName.K1 := by
    unfold kindsBeforeBatching
    rfl
  obtain ⟨Lk, b, Xl, pr, pd, reads, digits, e1, e2, hX, hn, harm⟩ :=
    k1_later O (2 * g) .layers (subs_at hS hR O.pub O.blank hg) 3 hk (by decide)
  obtain rfl : m = Xl := Option.some.inj (fm.symm.trans hX)
  rcases harm with ⟨e, h⟩ | ⟨e, h⟩
  · subst e
    exact ⟨Lk, b, m, pd, reads, digits, e1, e2, hX, km, gm, hn, h⟩
  · exfalso
    rcases numbers_pieces hn with ⟨-, h'⟩ | ⟨-, h'⟩ <;> omega

end

end IM

#print axioms IM.lot_K1
#print axioms IM.k1_mem
#print axioms IM.k1_later
#print axioms IM.k1_first_of
#print axioms IM.k1_first_plan
#print axioms IM.k1_reads_layers
