-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/SeatOpen.lean.
Where the rest of this head and the Lean text differ, the Lean text holds.
 A LAW ABOUT ProofFile.onlineDescription, NO PART OF IT: onlineDescription's value OPENED ONCE, so that several seats can be
   called AT
THE SAME LETTERS.
OBJECT. ProofFile.onlineDescription (Johnson/Desc/ProofFile/OnlineDescription.lean) at its own seat ProofFile.pureSeat o Z.
USER. Every seat in its form «‹kind›_of» (k6_of …), and a caller who wants two seats about ONE chain c.
LETTERS. o: the second hash function as a letter · pol lay KL: the three public files · F: onlineDescription's value ·
Z · Bs · base · c · A · B: what onlineDescription made on its way, EACH BY THE CALL THAT MADE IT.

THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): WHAT NEEDS NO SCOPE STANDS AT EVERY o; WHAT STANDS ON A LAW OF THE LIBRARY OVER «publicOf … = .ok X» STANDS AT OnBytes.secondHashFunction, where publicOfO_older makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7′ | G7′bits hand every o: for these the in-scope halves are owed, at PublicCut).

  Open o pol lay KL F Z Bs base c A B   nine clauses; seven are equations of the form ‹a function of earlier letters› = ok | some ‹the letter›: pubPlain o pol lay KL = ok Z · baseOf Z (pureSeat o Z) = ok Bs ·
                    (partsAt (pureSeat o Z) Bs).base = ok base · chainBy Z base … = ok c · onlineSharedChain Z = some A · onlineLastChain Z = some B · F = fileDescBy … c.
                    SO THE LETTERS ARE FUNCTIONS OF THE THREE FILES: Open.unique.
  seat_open         where onlineDescription returns F: there are such letters.
  Open.unique       two openings of the same three files have the same Z, Bs, base, c, A, B (and F).
  Open.blank | Open.publicO | Open.public | Open.W | Open.first   the blank letters are Bs.G₀; at every o: publicOfO o pol KL (some lay) = ok Bs.G₀.W; at secondHashFunction: publicOf pol KL (some lay) = ok Bs.G₀.W; Bs.G₀.W = Z.p.X (ProofFile.Law.blankBy_W); Bs.G₀.first = Z.first.

What is not claimed. Nothing on any block. No soundness.
-/
import Johnson.IMR.PureChain

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-- **onlineDescription's value, opened**: each letter by the call that made it. -/
structure Open (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
    (base : List (Block S Cl)) (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) : Prop where
  pub : ProofFile.pubPlain o pol lay KL = .ok Z
  made : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok Bs
  /-- the seat has no fault · it lacks nothing: onlineDescriptionFromPublicPart's two tests, read off its yes -/
  sound : ProofFile.faultsAt (ProofFile.pureSeat o Z) Bs = []
  whole : ProofFile.lackingAt (ProofFile.pureSeat o Z) (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs) = []
  places : (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).base = .ok base
  chain : ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).frames
    (ProofFile.partsAt (ProofFile.pureSeat o Z) Bs).road = .ok c
  shared : ProofFile.onlineSharedChain Z = some A
  second : ProofFile.onlineLastChain Z = some B
  desc : F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c

/-- **Where onlineDescription returns, it can be opened.** -/
theorem seat_open {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (hF : ProofFile.onlineDescription o pol lay KL = .ok F) : ∃ Z Bs base c A B, Open o pol lay KL F Z Bs base c A B := by
  obtain ⟨Z, hZ, hz⟩ := ProofFile.Law.descPure_made hF
  obtain ⟨Bs, base, c, A, B, hB, hf, hl, hb, hc, hA, hB', eF⟩ := pure_chain hz
  exact ⟨Z, Bs, base, c, A, B, hZ, hB, hf, hl, hb, hc, hA, hB', eF⟩

section
variable {pol lay KL : ByteArray} {F F' : FileDescription ProofFile.Inst} {Z Z' : ProofFile.Pub} {Bs Bs' : ProofFile.PureBase}
  {base base' : List (Block S Cl)} {c c' : Chain S Cl} {A A' : ProofFile.SharedSeat}
  {B B' : ProofFile.SecondSeat}

/-- **The letters are functions of the three files.** -/
theorem Open.unique (O : Open o pol lay KL F Z Bs base c A B)
    (O' : Open o pol lay KL F' Z' Bs' base' c' A' B') :
    Z = Z' ∧ Bs = Bs' ∧ base = base' ∧ c = c' ∧ A = A' ∧ B = B' ∧ F = F' := by
  obtain rfl : Z = Z' := Except.ok.inj (O.pub.symm.trans O'.pub)
  obtain rfl : Bs = Bs' := Except.ok.inj (O.made.symm.trans O'.made)
  obtain rfl : base = base' := Except.ok.inj (O.places.symm.trans O'.places)
  obtain rfl : c = c' := Except.ok.inj (O.chain.symm.trans O'.chain)
  obtain rfl : A = A' := Option.some.inj (O.shared.symm.trans O'.shared)
  obtain rfl : B = B' := Option.some.inj (O.second.symm.trans O'.second)
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, O.desc.trans O'.desc.symm⟩

theorem Open.blank (O : Open o pol lay KL F Z Bs base c A B) :
    ProofFile.blankBy ProofFile.pureRoad.links Z = some Bs.G₀ := (base_made O.made).2.2.1

/-- At every o: the lots' W is publicOfO o's value. -/
theorem Open.publicO (O : Open o pol lay KL F Z Bs base c A B) :
    VerifiableInference.PlanWritten.publicOfO o pol KL (some lay) = .ok Bs.G₀.W :=
  (ground_public O.pub O.blank).1

/-- At the second hash function itself: it is publicOf's. -/
theorem Open.public (O : Open OnBytes.secondHashFunction pol lay KL F Z Bs base c A B) :
    publicOf pol KL (some lay) = .ok Bs.G₀.W := ground_publicK O.pub O.blank

/-- **THE LOTS' W IS FREE OF THE REQUEST**: the blocks are made at the blank letters (a request of zeros); their W is the public part's own record. -/
theorem Open.W (O : Open o pol lay KL F Z Bs base c A B) : Bs.G₀.W = Z.p.X :=
  ProofFile.Law.blankBy_W O.blank

theorem Open.first (O : Open o pol lay KL F Z Bs base c A B) : Bs.G₀.first = Z.first := by
  obtain ⟨_, -, -, -, e⟩ := blank_ground O.blank
  exact e

end

end IM

#print axioms IM.seat_open
#print axioms IM.Open.unique
#print axioms IM.Open.publicO
#print axioms IM.Open.public
#print axioms IM.Open.W
