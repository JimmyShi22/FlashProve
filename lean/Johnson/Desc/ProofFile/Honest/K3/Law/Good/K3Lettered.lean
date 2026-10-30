-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Good/K3Lettered.lean: THE LOOKUP'S ROW AT A SITE WITH THE
LETTERS OF THE FRAME'S `Good`; ITS SIDE PASSES THE FRAME'S TEST `Side.fits`; ITS LETTER bud HOLDS
EVERYWHERE. One definition; theorems.

  `k3Lettered A s A' B'` the row at the site's place: each part with its simulator
    (Honest/K3/LotRow.lean: `rowPairs`); A', B' free letters; On and bud laid as "true"
  `side_k3` its side at a list of sub-protocols: the member that the search at the place finds
  `half_k3`, `half_k3_seatAt` THE SIDE'S HALF IS THE SEATED ROW AT THE SITE: at the filling that
    folds tables it is the very half that `theLot` lays there
  `fits_k3` `Side.fits` accepts. CONDITIONAL ON four facts on that member and the face
  `fits_k3_of_fits` the same at a description's first chain, from `k3Fits`
  `bud_k3` the letter bud holds at every number, challenges and positions

DEBTS THAT THE TWO LETTERS MAKE, NOT FACTS. On and bud are laid as "true", not earned. What that
makes owed is the frame's to say (Honest/Side.lean, at `Good`); nothing of it is shown here.

Limits. Of `Good`: the field fits alone. `exact`, `fresh`, `plays`, `acc`: not here: no term of
`Good` is made. No instance of these hypotheses is exhibited in this file. Nothing on any property
of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Rule
import Johnson.Desc.ProofFile.Honest.K3.RowAt
import Johnson.Desc.ProofFile.Honest.K3.Law.SeatFitsLaw
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberSite
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberAtSite
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HalfOfLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.K3 (entriesV entriesFit)

local notation "FS" => VerifiableInference.Desc.First.S

section
variable {Bk : ProverCoinCounts} {S Cl V W X Pb : Type}

/-- **The lookup's row at a site, with the letters of `Good`.** A: the filling. A', B': free
letters. -/
def k3Lettered (A : Fill W) (s : Site) (A' B' : Coins Bk → S → Mid W X → Env → Prop) :
    Lettered Bk S Cl V W X Pb :=
  ⟨s.at_.place, rowPairs A s, A', B', fun _ _ _ _ => True, fun _ _ _ => True⟩

/-- **Its side**: the member that the search at the site's place finds, with the row beside it.
CONDITIONAL ON the side being there. -/
theorem side_k3 (A : Fill W) (s : Site) (A' B' : Coins Bk → S → Mid W X → Env → Prop)
    (bs : List (Block S Cl)) (fs : List (Fall S)) (σ : Side S Cl V W X Pb)
    (h : (k3Lettered (Cl := Cl) (V := V) (Pb := Pb) A s A' B').side bs fs = some σ) :
    bs.find? (fun b => b.place == s.at_.place) = some σ.block ∧ σ.row = rowPairs A s ∧
      σ.block.place = s.at_.place := by
  have h' : (bs.find? fun b => b.place == s.at_.place).map
      (fun b => ({ block := b, row := rowPairs A s, fall := fallOf fs s.at_.place } :
        Side S Cl V W X Pb)) = some σ := h
  obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 h'
  exact ⟨hm, rfl, by simpa using List.find?_some hm⟩

/-- The row's parts are the seated row's, in order. No premise. -/
theorem rowPairs_parts (A : Fill W) (s : Site) :
    (rowPairs (V := V) (X := X) (Pb := Pb) A s).map (·.1) =
      (proverSideOfLookupInChainAtOneOwner (V₁ := V) (X₁ := X) theReads (A.jobs s).asked (A.wit s) s.at_).parts := by
  unfold rowPairs lookPairs
  apply map_fst_zip_eq
  rw [lookSims_length, ← List.length_map (f := fun p : Part V W X => p.moves.length),
    proverSideOfLookupInChainAtOneOwner_moves, List.length_map]

/-- **THE SIDE'S HALF IS THE SEATED ROW AT THE SITE**: the very half that a lot of the filling A
lays there. CONDITIONAL ON the side being there. -/
theorem half_k3 (A : Fill W) (s : Site) (A' B' : Coins Bk → S → Mid W X → Env → Prop)
    (bs : List (Block S Cl)) (fs : List (Fall S)) (σ : Side S Cl V W X Pb)
    (h : (k3Lettered (Cl := Cl) (V := V) (Pb := Pb) A s A' B').side bs fs = some σ) :
    σ.half = proverSideOfLookupInChainAtOneOwner theReads (A.jobs s).asked (A.wit s) s.at_ := by
  obtain ⟨_, hrow, hp⟩ := side_k3 A s A' B' bs fs σ h
  unfold Side.half
  rw [hrow, hp, rowPairs_parts]
  rfl

/-- **THE SIDE PASSES THE FRAME'S TEST.** CONDITIONAL ON: the member found declares just the entries
es, bare; it states an empty list of oracle messages for each; es are, but for the work bits, the
entries that the hearing goes by; the face passes its own test. No instance of these hypotheses is
exhibited in this file. -/
theorem fits_k3 (A : Fill W) (s : Site) (A' B' : Coins Bk → S → Mid W X → Env → Prop)
    (bs : List (Block S Cl)) (fs : List (Fall S)) (σ : Side S Cl V W X Pb)
    (h : (k3Lettered (Cl := Cl) (V := V) (Pb := Pb) A s A' B').side bs fs = some σ)
    (es : List Fmt.Entry) (hr : σ.block.rounds = es.map declOf)
    (ho : σ.block.oracles = es.map fun _ => []) (hfit : entriesFit s.at_.face es = true)
    (hok : s.at_.face.ok = true) : σ.fits = true := by
  obtain ⟨_, hrow, hp⟩ := side_k3 A s A' B' bs fs σ h
  have h2 : 2 ≤ s.at_.face.planes := by
    unfold VerifiableInference.Desc.K3.Face.ok at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hok.1.1.1.1.1.1.2
  have hl : es.length = (entriesV s.at_.face).length := by
    unfold entriesFit at hfit
    have e : (es.map fun e => { e with work := 0 }) = entriesV s.at_.face :=
      of_decide_eq_true (by simpa using hfit)
    rw [← e, List.length_map]
  have key := lookPairs_fits (V₁ := V) (X₁ := X) (Pb := Pb) σ.block theReads (A.jobs s).asked
    (A.wit s) s.at_ h2 hp (by rw [hr, List.length_map, hl])
    (by rw [ho, hr, List.length_map, List.length_map])
  obtain ⟨b, r, fl⟩ := σ
  obtain rfl : r = rowPairs A s := hrow
  exact key

/-- **THE LETTER bud HOLDS EVERYWHERE.** No premise. -/
theorem bud_k3 (A : Fill W) (s : Site) (A' B' : Coins Bk → S → Mid W X → Env → Prop) (n : Nat)
    (ds : List Fmt.Drawn) (asks : List (List (List Nat))) :
    (k3Lettered (Cl := Cl) (V := V) (Pb := Pb) A s A' B').bud n ds asks := trivial

end

section
variable {Bk : ProverCoinCounts} {S Cl W₀ Rc Xi Tr X Pb : Type}

/-- **At the filling that folds tables, at the public part's sources, the side's half is the half
that `theLot` lays at the site** (`seatAt`, Honest/K3/Law/Thread/HalfOfLot.lean). CONDITIONAL ON the
side being there. -/
theorem half_k3_seatAt (cells : Tr → Cells) (weights : W₀ → Weights)
    (req : Xi → OnBytes.Model.Head.Covered × Array Nat) (Z : Pub) (s : Site)
    (A' B' : Coins Bk → S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop) (bs : List (Block S Cl))
    (fs : List (Fall S)) (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (h : (k3Lettered (Cl := Cl) (V := Local W₀ Rc Xi Tr) (Pb := Pb)
      (fastFill (Rc := Rc) (sourcesAt cells weights req Z)) s A' B').side bs fs = some σ) :
    σ.half = AtThr.seatAt cells weights req Z s :=
  half_k3 _ s A' B' bs fs σ h

end

section
variable {Bk : ProverCoinCounts} {V W X Pb : Type}

/-- **THE SAME AT A DESCRIPTION'S FIRST CHAIN, FROM "FITS".** CONDITIONAL ON the description's
return, the site, the lot's sub-protocol at the site's place, and `k3Fits` at the chain's flat list.
No instance of these hypotheses is exhibited in this file. -/
theorem fits_k3_of_fits (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A₀ : SharedSeat)
    (B₀ : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A₀ B₀) (s : Site)
    (hs : s ∈ lookSites Z) (b : Block FS ProofFile.Cl) (hb : b ∈ (K3Lot.lot Z).blocks Bs.G₀)
    (hbs : b.place = s.at_.place) (hF : k3Fits Z ch.blocksInOrder s = true) (A : Fill W)
    (A' B' : Coins Bk → FS → Mid W X → Env → Prop) (fs : List (Fall FS))
    (σ : Side FS ProofFile.Cl V W X Pb)
    (h : (k3Lettered (Cl := ProofFile.Cl) (V := V) (Pb := Pb) A s A' B').side ch.blocksInOrder fs = some σ) :
    σ.fits = true := by
  obtain ⟨hf, _, hp⟩ := side_k3 A s A' B' ch.blocksInOrder fs σ h
  obtain ⟨m', hf', hk⟩ := plan_of_fits Z ch.blocksInOrder s hF
  obtain rfl : m' = σ.block := Option.some.inj (hf'.symm.trans hf)
  have hm : σ.block ∈ ch.blocksInOrder := List.mem_of_find?_eq_some hf
  have hmp : σ.block.place = b.place := hp.trans hbs.symm
  obtain ⟨_, e1, _, e3, e4⟩ :=
    site_block o pol lay KL Fd Z Bs base ch A₀ B₀ O s hs b σ.block hb hbs hm hmp hk
  obtain ⟨_, g1, g2, _⟩ := memberAtSite o pol lay KL Fd Z Bs base ch A₀ B₀ O b hb σ.block hm hmp
  exact fits_k3 A s A' B' ch.blocksInOrder fs σ h (s.p.entries.getD []) (g1.trans e3) (g2.trans e4) e1
    (fits_gives Z ch.blocksInOrder s hF).2.2.1

end

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.side_k3
#print axioms ProofFile.Honest.K3.Law.rowPairs_parts
#print axioms ProofFile.Honest.K3.Law.half_k3
#print axioms ProofFile.Honest.K3.Law.half_k3_seatAt
#print axioms ProofFile.Honest.K3.Law.fits_k3
#print axioms ProofFile.Honest.K3.Law.bud_k3
#print axioms ProofFile.Honest.K3.Law.fits_k3_of_fits
