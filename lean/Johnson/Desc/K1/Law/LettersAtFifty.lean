-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/LettersAtFifty.lean: K01_law, J1, AT THE DESCRIPTION: the piece's letters AT THE FIFTY LATER PLACES, FROM TWO THINGS THAT ARE NO LAW OF THE KIND: hC (the row of pieces is the maker's: Three.IsCut's first field: a choice of whoever lays
the rows of pieces) · hWr (the framework's own WrittenAs, shared by every kind: FitsOfOk's premise). NOTHING IS ASKED OF THE RESTS' ERRORS HERE: tiedAt_err (Johnson/Desc/Sound/TiedAtErr.lean) carries a tie to all greater errors. On the pattern of k13_law_top (Johnson/Desc/AtSeats/K13LawTop.lean):
its blocks_of_cut's three lines stand inline: this file does not import that one.
  inFront c k         the rounds that the first k blocks of the chain's flat list declare, counted
  baseL … c l d       the trees that the file's data tell in front of the place: THE PIECE's BASE
  rounds_blk          the lot's own block at (l, d) declares a sending's two rounds
  letters_at_flat     **GENERAL IN THE PLACE: at any flat number k < 357 whose sub-protocol declares a sending's two rounds (so at link 0's first place, 2, and at W's, 356, too)**
  k01_letters         **in scope, at (l, d): there are d₁ d₂ with d₁.entry = seedEntry P, d₁.kind = .seeds, and EVERY PIECE AT THE PLACE HAS A SENDING's STRETCH at the trees in front, d₁, d₂, with the maker's rest's own errors**
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.K01LawTied
import Johnson.Desc.K1.Law.SendLetters
import Johnson.Desc.K1.Law.SendOfWritten
import Johnson.Desc.K1.Law.LaterOne
import Johnson.Desc.AtSeats.K13SitsSealed
import Johnson.Desc.Sound.TilesCutProofs
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.Sound.TiedAtErr

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Iop Run
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law (room_of_later)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open ProofFile (Cl)
open IM (Open k1Ix k1Reads)
open _root_.Desc.K14.Law (roundsIn)

/-- The rounds that the first k blocks of the chain's flat list declare, counted. -/
def inFront (c : Chain S Cl) (k : ℕ) : ℕ := ((c.blocksInOrder.take k).map (·.rounds.length)).sum

theorem roundsIn_flat {c : Chain S Cl} {bs : List (Block (ProofFile.InstPub × S) Cl)}
    (h : bs = (c.blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s))) (k : ℕ) :
    roundsIn (bs.take k) = inFront c k := by
  subst h
  unfold roundsIn inFront
  rw [← List.map_take, ← List.map_take, List.map_map, List.map_map]
  rfl

theorem rounds_blk (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) : (blkL Z G l d X arrs).rounds = rounds (parL Z G l d) := by
  cases d with
  | true => rfl
  | false =>
    show (laterAt G.first (gpOf Z) l (k1Ix l false + 1) 1 arrs : Block S Unit).rounds ++
      (IM.k1Quiet G l X).rounds = _
    rw [rounds_k1Quiet, List.append_nil]
    rfl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- In scope the flat list's entry at (l, d) is under the lot's own block. -/
theorem k01_flat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) (l : ℕ) (hl : l < 25) (d : Bool) :
    ∃ (e : Block S Cl) (X : LinkH) (arrs : Option (List ℕ)), c.blocksInOrder[noL l d]? = some e ∧
      e.UnderR ((blkL Z Bs.G₀ l d X arrs).retype : Block S Cl) := by
  cases d with
  | true =>
    obtain ⟨_, X, _, _, _, _⟩ := k01_flat_reads hS hR O l hl
    obtain ⟨b, digits, h5, h⟩ := k01_flat_digits hS hR O l hl
    exact ⟨b, X, digits, h5, IM.alone_underR h⟩
  | false =>
    obtain ⟨b, X, reads, h5, _, h⟩ := k01_flat_reads hS hR O l hl
    exact ⟨b, X, reads, h5, IM.alone_underR h⟩

variable {a : ℕ} {R₁ R₂ R₃ : Rounds} {e₁ : List (List ByteArray × ByteArray)} {all : List LeftT}
  {X₁ X₂ W : Type}
  {T : ThreeAt (ckP .two) (dataOf a R₁ R₂ R₃) all
    (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) X₁ X₂ W}

/-- **THE PIECE's LETTERS AT ANY SENDING OF THE FIRST CHAIN**: k: the flat number, in front of the seal's (357); e: the description's own sub-protocol there; Q: the sending's numbers: e declares Q's two rounds. Its errors: the maker's rest's own. -/
theorem letters_at_flat' (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) (hT : OfDesc _ T)
    {b₁ : Block (ProofFile.InstPub × S) Cl} {l₁ : List (Block (ProofFile.InstPub × S) Cl)}
    {rest₁ : (i : ℕ) → (ds : List RDT) → Sound.Rest (ckP .two) (Sound.frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁) (ProofFile.InstPub × S) W ds}
    {r : Fmt.RoundView}
    (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf a R₁ R₂ R₃).ds₁ b₁ l₁)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁) (k : ℕ) (hk : k < 357) (e : Block S Cl)
    (hflat : c.blocksInOrder[k]? = some e) (Q : Par) (hrd : e.rounds = rounds Q) :
    ∃ d₁ d₂ : RDT, d₁.entry = seedEntry Q ∧ d₁.kind = .seeds ∧
      ((dataOf a R₁ R₂ R₃).ds₁.drop (inFront c k)).take 2 = [d₁, d₂] ∧
      ∀ q, (T.p₁ :: T.l₁)[k]? = some q →
        HasLettersE (Sound.frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁) (nTrees ((dataOf a R₁ R₂ R₃).ds₁.take (inFront c k))) d₁ d₂
          (rest₁ k [d₁, d₂]).err q := by
  -- (blocks_of_cut, Johnson/Desc/AtSeats/K13LawTop.lean, says this by name; that file is not imported here)
  have hb : b₁ :: l₁ = (c.blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s)) := by
    have h := cutBlocks _ _ _ _ _ rest₁ [r] l₁ b₁ 0 0 (dataOf a R₁ R₂ R₃).ds₁
    rw [← hC] at h
    exact h.symm.trans hT.b₁
  obtain ⟨e7, hflat7, _, hu7⟩ := K13.Law.k13_sits_flat357 hS hR O
  have hx : (b₁ :: l₁)[k]? = some ((below e).lift Prod.snd fun t s => (t.1, s)) := by
    rw [hb]
    simp only [List.getElem?_map, hflat, Option.map_some]
  have hx7 : (b₁ :: l₁)[357]? = some ((below e7).lift Prod.snd fun t s => (t.1, s)) := by
    rw [hb]
    simp only [List.getElem?_map, hflat7, Option.map_some]
  have hlen : k < l₁.length := by
    have h7 : 357 < (b₁ :: l₁).length := (List.getElem?_eq_some_iff.1 hx7).1
    rw [List.length_cons] at h7
    omega
  have hr : ((below e).lift Prod.snd fun (t : ProofFile.InstPub × S) s => (t.1, s)).rounds = rounds Q :=
    hrd
  have hr7 : 0 < ((below e7).lift Prod.snd fun (t : ProofFile.InstPub × S) s => (t.1, s)).rounds.length := by
    show 0 < e7.rounds.length
    rw [hu7.1]
    exact Nat.zero_lt_one
  have hfl : (b₁ :: l₁).flatMap (·.rounds) = c.blocksInOrder.flatMap (·.rounds) := by
    rw [hb, List.map_map, List.flatMap_map]
    rfl
  obtain ⟨d₁, d₂, hds, h1, h2⟩ := send_of_written a R₁ R₂ R₃ (b₁ :: l₁) (e := e₁)
    (by rw [hfl]; exact hWr) k _ hx (room_of_later _ k 357 _ _ hx hx7 hk hr7) Q hr
  have hds' : ((dataOf a R₁ R₂ R₃).ds₁.drop (inFront c k)).take 2 = [d₁, d₂] := by
    rw [← roundsIn_flat hb k]
    have h2r : ((below e).lift Prod.snd fun (t : ProofFile.InstPub × S) s => (t.1, s)).rounds.length = 2 := by
      rw [hr]
      rfl
    rw [← h2r]
    exact hds
  refine ⟨d₁, d₂, h1, h2, hds', fun q hq => ?_⟩
  rw [← roundsIn_flat hb k]
  exact hasLettersE_of_cut rest₁ [r] l₁ b₁ _ k _ hx hlen d₁ d₂ hds q (by rw [← hC]; exact hq)

/-- The first form (without the clause on the data): kept for its callers. WHOEVER QUANTIFIES A PREMISE OVER «all d₁ d₂ with these two tags» ASKS IT OF ROUNDS THAT NO WRITTEN DATA HOLD: bind them by letters_at_flat''s third clause. -/
theorem letters_at_flat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) (hT : OfDesc _ T)
    {b₁ : Block (ProofFile.InstPub × S) Cl} {l₁ : List (Block (ProofFile.InstPub × S) Cl)}
    {rest₁ : (i : ℕ) → (ds : List RDT) → Sound.Rest (ckP .two) (Sound.frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁) (ProofFile.InstPub × S) W ds}
    {r : Fmt.RoundView}
    (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf a R₁ R₂ R₃).ds₁ b₁ l₁)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁) (k : ℕ) (hk : k < 357) (e : Block S Cl)
    (hflat : c.blocksInOrder[k]? = some e) (Q : Par) (hrd : e.rounds = rounds Q) :
    ∃ d₁ d₂ : RDT, d₁.entry = seedEntry Q ∧ d₁.kind = .seeds ∧
      ∀ q, (T.p₁ :: T.l₁)[k]? = some q →
        HasLettersE (Sound.frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁) (nTrees ((dataOf a R₁ R₂ R₃).ds₁.take (inFront c k))) d₁ d₂
          (rest₁ k [d₁, d₂]).err q := by
  obtain ⟨d₁, d₂, h1, h2, _, h3⟩ := letters_at_flat' hS hR O hT hC hWr k hk e hflat Q hrd
  exact ⟨d₁, d₂, h1, h2, h3⟩

/-- **THE PIECE's LETTERS AT A LATER PLACE.** -/
theorem k01_letters (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) (hT : OfDesc _ T)
    {b₁ : Block (ProofFile.InstPub × S) Cl} {l₁ : List (Block (ProofFile.InstPub × S) Cl)}
    {rest₁ : (i : ℕ) → (ds : List RDT) → Sound.Rest (ckP .two) (Sound.frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁) (ProofFile.InstPub × S) W ds}
    {r : Fmt.RoundView}
    (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf a R₁ R₂ R₃).ds₁ b₁ l₁)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁) (l : ℕ) (hl : l < 25) (d : Bool) :
    ∃ d₁ d₂ : RDT, d₁.entry = seedEntry (parL Z Bs.G₀ l d) ∧ d₁.kind = .seeds ∧
      ((dataOf a R₁ R₂ R₃).ds₁.drop (inFront c (noL l d))).take 2 = [d₁, d₂] ∧
      ∀ q, (T.p₁ :: T.l₁)[noL l d]? = some q →
        HasLettersE (Sound.frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁) (nTrees ((dataOf a R₁ R₂ R₃).ds₁.take (inFront c (noL l d)))) d₁ d₂
          (rest₁ (noL l d) [d₁, d₂]).err q := by
  obtain ⟨e, X, arrs, hflat, hu⟩ := k01_flat hS hR O l hl d
  have hk : noL l d < 357 := by
    have : k1Ix l d ≤ 6 := by unfold k1Ix; split <;> split <;> omega
    show 14 * l + k1Ix l d + 2 < 357
    omega
  exact letters_at_flat' hS hR O hT hC hWr (noL l d) hk e hflat (parL Z Bs.G₀ l d)
    (by rw [hu.1]; exact rounds_blk Z Bs.G₀ l d X arrs)

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.k01_flat
#print axioms VerifiableInference.Desc.K1.letters_at_flat'
#print axioms VerifiableInference.Desc.K1.letters_at_flat
#print axioms VerifiableInference.Desc.K1.k01_letters
