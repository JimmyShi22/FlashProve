-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/PiecesAndPort.lean: THE SHARED "SENDING" (the kind K1) AT THE
FIRST CHAIN's REAL PLANS: (1) IN THE GOALS' SCOPE THE LOT's OWN NUMBERS OF A SEGMENT's TWO PIECES
ARE THE FLAT LIST's; (2) THE KIND's ONE BOOLEAN condPort HOLDS AT THE OPENING's AND AT EVERY LATER
SENDING's PLAN, WHEREVER THE CODES AND THE SHAPE ARE THE WRITTEN ONES. Five theorems; no definition.
It stands over the library alone. Each is a join of what the library has.

  - pieces_inScope: UNDER hS, hR, O (the scope, the files read, the description opened) and hl : l <
    25: there are Xl, reads, digits with Bs.G₀.built[l]? = some Xl and K1.linkNumbers Bs.G₀ Xl =
    some (k1Ix l false + 1, k1Ix l true + 1, reads, digits). The library has the two halves:
    k1_reads_of, k1_digits_of (Johnson/IMR/K1Scope.lean). l = 24, the head's segment, is among them.
  - lotLetters_inScope: the same as the library's own proposition LotLetters
    (Johnson/Desc/AtSeats/HearAtFifty.lean), at both d: there it is concluded from a lot's block at
    the address (lot_is_blkL); here from the scope.
  - parL_later: the plan of the fifty (parL, Johnson/Desc/K1/Law/LaterOne.lean) written out:
    parLater at the piece k1Ix l d + 1, at the moment 1 ("reads", d = false) or 2 ("digits", d =
    true).
  - port_first, port_later: UNDER hc : q.codes = codesFull2 and hs : q.shape = shapeFull
    (port_later: hl : l < 25, hm : m = 1 ∨ m = 2; THE PIECE IS FREE): condPort at firstPar q gp, at
    parLater q gp l piece m, AT THE WRITTEN RECORD's RADII: radRec k P
    (Johnson/Desc/K1/Law/FiftyAtFull.lean).

Two numberings. radRec's k is the number of the written record of the first chain's sendings: 0 for
the opening, 3 l + m for a later sending. It is not the member's number in the flat list (2; K1.noL
l d).

By calls: k1_reads_of, k1_digits_of · k01_sits_first_chain (Johnson/Desc/K1/Law/AtFull.lean) ·
condPort_radRec (Johnson/Desc/K1/Law/FiftyAtFull.lean).

Kin in the library. numbers_pieces (Johnson/IMR/K1Seat.lean): the pieces are 4 and 6, or 5 and 7.
G_hCond_atAll (Johnson/Desc/K1/Law/TiesAtAll2.lean): port_first's end at the description's own
ground, under the library's head. k01_sits_reads, k01_sits_digits (Johnson/Desc/K1/Law/Sits.lean),
k01_law_reads, k01_law_digits (Johnson/Desc/K1/Law/SitsLaw.lean): PlaceOk at the two plans, told by
the link and its place. condPort_mono (Johnson/Desc/K1/Law/PortMono.lean): smaller radii serve.

Limits. (1) stands at the description's own ground Bs.G₀: that a prover's ground is this one is not
said here. (2) hc and hs are premises: at the description's own ground the library pays them under
its head (hc_atAll, hs_atAll, Johnson/Desc/K1/Law/TestsAtAll.lean). Whether the radii by which the
real table's members are made are radRec's is not said here. W's sending is not here. Nothing on
soundness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.IMR.K1Scope
import Johnson.Desc.K1.Law.LaterOne
import Johnson.Desc.K1.Law.FiftyAtFull
import Johnson.Desc.K1.Law.AtFull
import Johnson.Desc.AtSeats.HearAtFifty

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Link FileDescription Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.ReqLit (shapeFull)
open OnBytes.Model.Stages (LinkH)
open OnBytes OnBytes.Params Johnson.G _root_.Desc.Plain

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE PIECES, IN SCOPE**: at every built segment the lot's own numbers of the two pieces are the
flat list's. -/
theorem pieces_inScope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) :
    ∃ (Xl : LinkH) (reads digits : Option (List ℕ)), Bs.G₀.built[l]? = some Xl ∧
      K1.linkNumbers Bs.G₀ Xl =
        some (IM.k1Ix l false + 1, IM.k1Ix l true + 1, reads, digits) := by
  obtain ⟨-, -, Xl, pd, reads, digits, -, -, hX, hn, -⟩ := IM.k1_reads_of hS hR O l hl
  obtain ⟨-, -, Xl', pr, reads', digits', -, -, hX', hn', -⟩ := IM.k1_digits_of hS hR O l hl
  obtain rfl : Xl = Xl' := Option.some.inj (hX.symm.trans hX')
  have e := Option.some.inj (hn.symm.trans hn')
  have e2 : pd = IM.k1Ix l true + 1 := (Prod.mk.inj (Prod.mk.inj e).2).1
  subst e2
  exact ⟨Xl, reads, digits, hX, hn⟩

/-- The same as the library's own proposition, at both d. -/
theorem lotLetters_inScope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    (d : Bool) :
    ∃ (Xl : LinkH) (arrs : Option (List ℕ)), HashBuild.LotLetters Bs.G₀ l d Xl arrs := by
  obtain ⟨Xl, reads, digits, hX, hn⟩ := pieces_inScope hS hR O hl
  exact ⟨Xl, cond d digits reads, hX, reads, digits, hn, rfl⟩

end

/-- The plan of the fifty, written out. -/
theorem parL_later (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) :
    K1.parL Z G l d =
      K1.parLater G.first (K1.gpOf Z) l (IM.k1Ix l d + 1) (if d then 2 else 1) := by
  cases d <;> rfl

/-- **port at the opening's plan**, at the written record's radii. -/
theorem port_first (q : Params.First) (gp : GPar) (hc : q.codes = codesFull2)
    (hs : q.shape = shapeFull) :
    K1.condPort (K1.firstPar q gp) (K1.radRec 0 (K1.firstPar q gp)) = true :=
  K1.condPort_radRec (K1.k01_sits_first_chain q gp hc hs).1

/-- **port at a later sending's plan**, at any piece, at the written record's radii. -/
theorem port_later (q : Params.First) (gp : GPar) (hc : q.codes = codesFull2)
    (hs : q.shape = shapeFull) {l : ℕ} (hl : l < 25) (piece : ℕ) {m : ℕ} (hm : m = 1 ∨ m = 2) :
    K1.condPort (K1.parLater q gp l piece m)
      (K1.radRec (3 * l + m) (K1.parLater q gp l piece m)) = true :=
  K1.condPort_radRec ((K1.k01_sits_first_chain q gp hc hs).2.1 l piece m hl hm)

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.pieces_inScope
#print axioms ProofFile.Honest.K1.lotLetters_inScope
#print axioms ProofFile.Honest.K1.parL_later
#print axioms ProofFile.Honest.K1.port_first
#print axioms ProofFile.Honest.K1.port_later
