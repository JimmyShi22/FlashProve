-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtHonest.lean: ONE HEAD FOR THE HONEST SIDE AT THE PROOF FILE's OWN
DESCRIPTION: what the rules on the three chains' threads ask beside the kinds' own debts, gathered
as the library gathers what stands in front of its own laws (`P5J.LaidAt`,
Johnson/P5J/LaidOpens.lean: fields, and a list of named tests with code that all say yes). A
structure, a list of tests, and statements that hold by projection and by Honest/AtPureLaw.lean,
Honest/AtHead.lean and Honest/ProverSelf.lean.

  `frameAsks`       THE FRAME's OWN TESTS WITH CODE AT A MADE PROVER AND ITS ROWS, each with a name:
                   every row stands at a place of its chain · the first chain's last declared round
                   is plain · a half stands at every sub-protocol that sends a root
  `AtHonest`        the head: THE LIBRARY's ONE HEAD (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean) at a
                   public record Z · the honest prover's maker yields A at Z's own three files · the
                   rows' halves are A's prover's · every test of `frameAsks`, AND EVERY TEST OF A
                   LIST `more` THAT THE CALLER LAYS, says yes · `ready` returns at one input
  `AtHonest.laid` · `plan` · `book` · `seats` · `seal` · `rooted` · `ring` · `isTerm` · `asked`
                   what is read off it

THE LIST `more`. A kind's writers name tests with code on the description's data that their laws
take as premises (a number of rounds in front, a shape's counts, that one entry of the book lies
inside another). Each goes into `more` under a name; `AtHonest.asked` hands it back. So the same
term that a law takes as a premise is the term that a test program prints.

WHAT OF IT IS NO EVALUATION. The test on the plan is the library's own field; that the book fails
none of its own tests follows from the maker's yes.

Limits. NO MEMBER OF IT IS MADE, and no program's run has given one: `P5J.AtMgA` is the full
size's, and no program of ours has run the maker or a test of these lists there. At the
small example set the maker and the tests run, and `P5J.AtMgA` does not speak. The format's second
hash function is a letter here; the first chain's letters are typed at `OnBytes.secondHashFunction` alone. `rootedAll`
says no as long as a sender has no half. Nothing on a run, a coin or a measure. This file proves
nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtHead
import Johnson.Desc.ProofFile.Honest.ProverSelf
import Johnson.Desc.ProofFile.Honest.Law.Thread
import Johnson.Desc.ProofFile.Honest.Law.PlanGives
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Chain FileDescription)
open OnBytes.Maker (WholeD)
open P5J (AtMgA LaidAt F0T TS)

variable {W₀ Rc Tr X₀ X : Type}

/-- **The frame's own tests with code**, each with a name. -/
def frameAsks (A : OnlineProverWithDescription W₀ Rc Tr X₀ X) (G : Sides A.F A.B W₀ Rc OnBytes.TableKey Tr X₀ X) :
    List (String × Bool) :=
  [("every row stands at a place of its chain", G.seated),
   ("the first chain's last declared round is plain", sealPlain A.F),
   ("a half stands at every sub-protocol that sends a root", rootedAll A.F (G.prover A.H))]

/-- **The head.** more: the kinds' writers' tests with code, each with a name. -/
structure AtHonest (o : SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (P : OnlineProverParts W₀ Rc Tr X₀ X) (A : OnlineProverWithDescription W₀ Rc Tr X₀ X)
    (G : Sides A.F A.B W₀ Rc OnBytes.TableKey Tr X₀ X) (more : List (String × Bool)) : Prop where
  /-- THE LIBRARY's ONE HEAD, under which the first chain's letters and the kinds' laws at the
  description's own term are typed; that the library's value is laid at Z's three files is its field
  `laid` -/
  head : AtMgA o Z D r Zp Np cF x
  /-- the honest prover's maker yields A at the same files -/
  made : onlineProverFromPublicFiles o Z.pol Z.lay Z.KL P = .ok A
  /-- the rows' halves are A's prover's, chain by chain -/
  first : A.H.first = G.first.map fun L => ⟨L.place, L.row.map (·.1)⟩
  shared : A.H.shared = G.shared.map fun L => ⟨L.place, L.row.map (·.1)⟩
  second : A.H.second = G.second.map fun L => ⟨L.place, L.row.map (·.1)⟩
  /-- every named test says yes -/
  asks : ∀ t ∈ frameAsks A G ++ more, t.2 = true
  /-- `ready` returns at one input -/
  one : ∃ w₀ rc ξ k R, ready A.F A.B A.H w₀ rc ξ k = .ok R

section
variable {o : SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  {G : Sides A.F A.B W₀ Rc OnBytes.TableKey Tr X₀ X} {more : List (String × Bool)}

/-- The library's value is laid at the three files. -/
theorem AtHonest.laid (a : AtHonest o Z D r Zp Np cF x P A G more) :
    LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF := a.head.laid

theorem AtHonest.plan (a : AtHonest o Z D r Zp Np cF x P A G more) : A.F.planOk = true :=
  atPure_planOk a.laid a.made

theorem AtHonest.book (a : AtHonest o Z D r Zp Np cF x P A G more) : A.B.word A.F = none :=
  (atPure_tests a.made).1

theorem AtHonest.ring (a : AtHonest o Z D r Zp Np cF x P A G more) : G.prover A.H = A.H :=
  Sides.prover_self a.first a.shared a.second

theorem AtHonest.seats (a : AtHonest o Z D r Zp Np cF x P A G more) : G.seated = true :=
  a.asks ("every row stands at a place of its chain", G.seated) (by simp [frameAsks])

theorem AtHonest.seal (a : AtHonest o Z D r Zp Np cF x P A G more) : sealPlain A.F = true :=
  a.asks ("the first chain's last declared round is plain", sealPlain A.F) (by simp [frameAsks])

theorem AtHonest.rooted (a : AtHonest o Z D r Zp Np cF x P A G more) :
    rootedAll A.F (G.prover A.H) = true :=
  a.asks ("a half stands at every sub-protocol that sends a root", rootedAll A.F (G.prover A.H))
    (by simp [frameAsks])

theorem AtHonest.isTerm (a : AtHonest o Z D r Zp Np cF x P A G more) :
    A.Z = Zp ∧ A.F = F0T o Zp Np cF := atPure_at_laid a.laid a.made

/-- A test of the caller's list says yes. -/
theorem AtHonest.asked (a : AtHonest o Z D r Zp Np cF x P A G more) {t : String × Bool}
    (h : t ∈ more) : t.2 = true := a.asks t (List.mem_append_right _ h)

end

end ProofFile.Honest

#print axioms ProofFile.Honest.AtHonest.laid
#print axioms ProofFile.Honest.AtHonest.plan
#print axioms ProofFile.Honest.AtHonest.book
#print axioms ProofFile.Honest.AtHonest.ring
#print axioms ProofFile.Honest.AtHonest.seats
#print axioms ProofFile.Honest.AtHonest.seal
#print axioms ProofFile.Honest.AtHonest.rooted
#print axioms ProofFile.Honest.AtHonest.isTerm
#print axioms ProofFile.Honest.AtHonest.asked
