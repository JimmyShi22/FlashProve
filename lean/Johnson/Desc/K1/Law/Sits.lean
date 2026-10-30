-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/Sits.lean: THE ROW K01_sits AT THE KIND K1's OWN FIFTY-ONE PLACES OF A PROOF FILE's FIRST CHAIN: A JOIN OF THEOREMS OF TWO FOLDERS (Johnson/IMR/ AND Johnson/Desc/K1/Law/):
  (b) THE SEAT (Johnson/IMR/K1Seat.lean, K1Scope.lean: k1_first_of, k1_reads_of, k1_digits_of):
      in scope, at an opening O of the pure description: the entry of the description's own chain at the place IS the kind's block, carried over by
      Block.retype, under the seat's wrappers alone (LaidAlone | LaidFramed: another name and place; the mark's guard; the guard on one seat);
  (n) THE NUMBERS (Johnson/Desc/K1/Law/AtFull.lean: k01_sits_first_chain): at the written codes and the written shape that block's parameters stand on their written
      record (PlaceOk).
What joins them: laterAt q gp l piece m arrays is commitAtS (parLater q gp l piece m) l m arrays, and firstSegmentOpening q gp is made of firstPar q gp, by rfl.
  SitsAt c k P: the conjunct at one place
  k01_sits_first · k01_sits_reads · k01_sits_digits
  reads_yes: at the reads' place the lot joins a step without a round behind K1's block: a yes of the joined block gives a yes of K1's own block at
      the same record and rounds, and the joined step's yes behind it.

THE PREMISES, BY NAME: hS hR O: IM's: the public files are in scope, are read, and the pure description is made of them (that it returns in scope is a
premise there) · hc hs: the description's own parameters have the written codes and the written shape: BY RUNS ALONE.
What is not claimed. The thirty places at which another kind hands its sending to K1's text; W's place; the entry file; the small size. Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.IMR.K1Scope
import Johnson.Desc.K1.Law.AtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params Johnson.G Desc.Plain
open VerifiableInference.Desc (Block Chain Link FileDescription Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.ReqLit (shapeFull)
open OnBytes.Model.Stages (LinkH)
open ProofFile (Cl)
open IM (Open LaidAlone LaidFramed k1Reads k1Quiet k1Ix k1PlaceL k1Place0)

theorem laterAt_is (q : Params.First) (gp : GPar) (l piece m : Nat) (arrays : Option (List Nat)) :
    (laterAt q gp l piece m arrays : Block S Unit) = commitAtS (parLater q gp l piece m) l m arrays :=
  rfl

/-- **A yes of the reads' joined block.** -/
theorem reads_yes (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) (X : LinkH) (pr : Nat)
    (reads : Option (List Nat)) (s s'' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (k1Reads Z G l X pr reads).decide s rs gs = .ok s'') :
    ∃ s', (commitAtS (Cl := Unit) (parLater G.first (gpOf Z) l pr 1) l 1 reads).decide s
        (rs.take (rounds (parLater G.first (gpOf Z) l pr 1)).length)
        (gs.take (commitAtS (Cl := Unit) (parLater G.first (gpOf Z) l pr 1) l 1 reads).openings) = .ok s' ∧
      (k1Quiet G l X).decide s'
        (rs.drop (rounds (parLater G.first (gpOf Z) l pr 1)).length)
        (gs.drop (commitAtS (Cl := Unit) (parLater G.first (gpOf Z) l pr 1) l 1 reads).openings) = .ok s'' := by
  have h' : ((commitAtS (Cl := Unit) (parLater G.first (gpOf Z) l pr 1) l 1 reads).decide s
      (rs.take (rounds (parLater G.first (gpOf Z) l pr 1)).length)
      (gs.take (commitAtS (Cl := Unit) (parLater G.first (gpOf Z) l pr 1) l 1 reads).openings)).bind
      (fun s' => (k1Quiet G l X).decide s'
        (rs.drop (rounds (parLater G.first (gpOf Z) l pr 1)).length)
        (gs.drop (commitAtS (Cl := Unit) (parLater G.first (gpOf Z) l pr 1) l 1 reads).openings)) = .ok s'' := h
  cases hk : (commitAtS (Cl := Unit) (parLater G.first (gpOf Z) l pr 1) l 1 reads).decide s
      (rs.take (rounds (parLater G.first (gpOf Z) l pr 1)).length)
      (gs.take (commitAtS (Cl := Unit) (parLater G.first (gpOf Z) l pr 1) l 1 reads).openings) with
  | error e =>
    rw [hk] at h'
    cases h'
  | ok s' =>
    rw [hk] at h'
    exact ⟨s', rfl, h'⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **K01_sits at the first segment's opening.** -/
theorem k01_sits_first (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hc : Bs.G₀.first.codes = codesFull2) (hs : Bs.G₀.first.shape = shapeFull) :
    ∃ (Lk : Link S Cl) (b : Block S Cl), c.links[0]? = some Lk ∧ Lk.hear[0]? = some b ∧
      LaidFramed Z b (firstSegmentOpening Bs.G₀.first (gpOf Z) : Block S Unit).retype b.name k1Place0 ∧
      PlaceOk 2 0 0 (firstPar Bs.G₀.first (gpOf Z)) := by
  obtain ⟨Lk, b, e1, e2, h⟩ := IM.k1_first_of hS hR O
  exact ⟨Lk, b, e1, e2, h, (k01_sits_first_chain _ _ hc hs).1⟩

/-- **K01_sits at every link's reads' place.** -/
theorem k01_sits_reads (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hc : Bs.G₀.first.codes = codesFull2) (hs : Bs.G₀.first.shape = shapeFull) :
    ∀ l < 25, ∃ (Lk : Link S Cl) (b : Block S Cl) (Xl : LinkH) (reads : Option (List Nat)),
      c.links[l]? = some Lk ∧ Lk.hear[k1Ix l false]? = some b ∧ Bs.G₀.built[l]? = some Xl ∧
      LaidAlone ProofFile.sameReply b (k1Reads Z Bs.G₀ l Xl (k1Ix l false + 1) reads).retype b.name
        (k1PlaceL l false) ∧
      PlaceOk 2 0 (3 * l + 1) (parLater Bs.G₀.first (gpOf Z) l (k1Ix l false + 1) 1) := by
  intro l hl
  obtain ⟨Lk, b, Xl, pd, reads, digits, e1, e2, hX, -, h⟩ := IM.k1_reads_of hS hR O l hl
  exact ⟨Lk, b, Xl, reads, e1, e2, hX, h,
    (k01_sits_first_chain _ _ hc hs).2.1 l _ 1 hl (Or.inl rfl)⟩

/-- **K01_sits at every link's digits' place.** -/
theorem k01_sits_digits (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hc : Bs.G₀.first.codes = codesFull2) (hs : Bs.G₀.first.shape = shapeFull) :
    ∀ l < 25, ∃ (Lk : Link S Cl) (b : Block S Cl) (digits : Option (List Nat)),
      c.links[l]? = some Lk ∧ Lk.hear[k1Ix l true]? = some b ∧
      LaidAlone ProofFile.sameReply b
        (commitAtS (parLater Bs.G₀.first (gpOf Z) l (k1Ix l true + 1) 2) l 2 digits :
          Block S Unit).retype b.name (k1PlaceL l true) ∧
      PlaceOk 2 0 (3 * l + 2) (parLater Bs.G₀.first (gpOf Z) l (k1Ix l true + 1) 2) := by
  intro l hl
  obtain ⟨Lk, b, Xl, pr, reads, digits, e1, e2, -, -, h⟩ := IM.k1_digits_of hS hR O l hl
  exact ⟨Lk, b, digits, e1, e2, h, (k01_sits_first_chain _ _ hc hs).2.1 l _ 2 hl (Or.inr rfl)⟩

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.reads_yes
#print axioms VerifiableInference.Desc.K1.k01_sits_first
#print axioms VerifiableInference.Desc.K1.k01_sits_reads
#print axioms VerifiableInference.Desc.K1.k01_sits_digits
