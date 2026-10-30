-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SitsShared.lean: THE ROW K01_sits AT THE KIND K1's TWO PLACES OF A PROOF FILE's
SHARED CHAIN (⟨2, none, 2, .K1⟩ "send o_u" · ⟨2, none, 5, .K1⟩ "send o_omega"), in the form of
Johnson/Desc/K1/Law/Sits.lean: the seat, the wrappers' yes, the numbers.

Statements and proofs. qAt Z N: the shared chain's parameters at the maker's public part:
`Desc.K14.p14Of Z.p.chains (Desc.K14.beforePointOf N)`. sendU P u · sendOm P: K14's two sendings at
any parameters P, as Johnson/Desc/K14/Blocks.lean lays them.
Main names:
  blocksOr_sends: at ANY parameters P at which K14 can say what goes out with o_u (hu), and
    whatever list stands behind: entry 1 of `blocksOr P ++ tl` is sendU P u, entry 4 is sendOm P.
    (A key file's shared chain is made of the same `blocksOr`.)
  sendU_place · sendOm_place: each bears its parameters' own place, of the kind K1.
  **sendAt_yes**: THE WRAPPER: a yes of `sendAt P n Q' …` from d to d' gives a yes of the kind's own
    block `K1.sendOwn Q'`, at the same rounds and columns, from the state that holds d's
    statement, book, roots and columns and owes no count; and d' is what K14 notes behind it.
    retype_yes: `Block.retype` leaves the decision as it is. map_retype: an entry of a list that
    is carried over by it.
  **k01_sits_shared_seat**: THE SEAT, IN THE DESCRIPTION's OWN LIST: at the term `descZ o Z N B c`
    (Johnson/Desc/Sound/AtDescPure.lean: what the maker returns): entries 1 and 4 of
    `.shared.back` are the two sendings at qAt Z N, carried over by `Block.retype`.
  **k01_sits_shared**: seat and numbers: under hc (the parameters' codes are the written list) and
    hs (their shape is the typed sizes'): `PlaceOk 2 1 0` and `PlaceOk 2 1 1` at the two
    parameters, by `k01_real` (Johnson/Desc/K1/Law/CondReal.lean).
THE PREMISES, BY NAME: hu (k01_sits_shared derives it from hc and hs) · hc · hs: closed facts on the
planner's sizes of a proof at the public files (Z.p.chains.made.sized.proof): shown here of no
files.
Not claimed here. The seven code switches of this chain's two proximity tests and the four of the
last chain's: rounds inside one block each of another kind's, at that kind's place. The key file;
the entry file. No soundness, no completeness and no hiding is claimed. It holds no coding theory.

-/
import Johnson.Desc.K1.Law.CondReal
import Johnson.Desc.K1.Law.SitsLaw
import Johnson.Desc.K14.Law.SendGood
import Johnson.Desc.Sound.AtDescPure
import Johnson.Desc.K12.SeatLaws
import Johnson.Desc.FoldKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params Johnson.G Desc.Plain
open VerifiableInference.Desc (Block Chain)
open _root_.Desc.K14 (P14 St p14Of beforePointOf parK1 sendAt withU withOmega entries behindU
  behindOmega blocksOr)
open _root_.Desc.K14.Law (descZ)

/-- K14's first sending at the parameters P, where u goes out with o_u. -/
abbrev sendU (P : P14) (u : Array OracleNotice) : Block St Unit :=
  sendAt P "send o_u" (parK1 P 2 "o_u and the first mask" u) (entries P)[0]? [[0], []]
    (behindU P.par)

/-- K14's second sending at the parameters P. -/
abbrev sendOm (P : P14) : Block St Unit :=
  sendAt P "send o_omega" (parK1 P 5 "o_omega and o_sp" (withOmega P.S)) (entries P)[1]?
    [[1], [1, 0]] (behindOmega P.par)

/-- The two sendings among K14's eight blocks, whatever stands behind these. -/
theorem blocksOr_sends (P : P14) {u : Array OracleNotice} (hu : withU P.S = some u)
    (tl : List (Block St Unit)) :
    (blocksOr P ++ tl)[1]? = some (sendU P u) ∧ (blocksOr P ++ tl)[4]? = some (sendOm P) := by
  have hb : ∃ b0 b2 b3 b5 b6 b7, _root_.Desc.K14.blocks P =
      some [b0, sendU P u, b2, b3, sendOm P, b5, b6, b7] := by
    unfold _root_.Desc.K14.blocks
    rw [hu]
    exact ⟨_, _, _, _, _, _, rfl⟩
  obtain ⟨b0, b2, b3, b5, b6, b7, hb⟩ := hb
  unfold blocksOr
  rw [hb]
  exact ⟨rfl, rfl⟩

theorem sendU_place (P : P14) (u : Array OracleNotice) :
    (sendU P u).place = ⟨2, none, 2, .K1⟩ := rfl

theorem sendOm_place (P : P14) : (sendOm P).place = ⟨2, none, 5, .K1⟩ := rfl

/-- **The law's own premise at K14's first sending**: a call of the shared chain's law. -/
theorem sendU_isSend (P : P14) (u : Array OracleNotice) :
    IsSend (parK1 P 2 "o_u and the first mask" u) (fun s : St => s.st) (sendU P u) :=
  _root_.Desc.K14.Law.sendAt_isSend _ _ _ _ _ _ fun d ids d' h =>
    (_root_.Desc.K14.Law.behindU_inv P.par d d' ids h).1

/-- **At its second.** -/
theorem sendOm_isSend (P : P14) :
    IsSend (parK1 P 5 "o_omega and o_sp" (withOmega P.S)) (fun s : St => s.st) (sendOm P) :=
  _root_.Desc.K14.Law.sendAt_isSend _ _ _ _ _ _ fun d ids d' h =>
    (_root_.Desc.K14.Law.behindOmega_inv P.par d d' ids h).1

/-- **THE WRAPPER's YES.** -/
theorem sendAt_yes (P : P14) (n : String) (Q' : Par) (inFront : Option Fmt.Entry)
    (groups : List (List Nat)) (behind : St → Array Nat → Option St) {d d' : St}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (sendAt P n Q' inFront groups behind).decide d rs gs = .ok d') :
    ∃ t : Owing (DState (Array Nat)),
      (sendOwn (Cl := Unit) Q').decide
        { owed := none, held := { st := d.st, book := d.book, roots := d.roots,
                                  opened := d.opened, loc := #[] } } rs gs = .ok t ∧
      behind { d with st := t.held.st, book := t.held.book, roots := t.held.roots,
                      opened := t.held.opened } t.held.loc = some d' := by
  have h' := (VerifiableInference.Desc.K12.Seat.inside_ok _ _ _ d d' rs gs).1
    (show (Block.inside
      (fun d : St => .ok { owed := none, held := { st := d.st, book := d.book, roots := d.roots,
                                                   opened := d.opened, loc := #[] } })
      (sendOwn (Cl := Unit) Q')
      (fun d t => named "the messages just sent are not those that this place records"
        (behind { d with st := t.held.st, book := t.held.book, roots := t.held.roots,
                         opened := t.held.opened } t.held.loc))).decide d rs gs = .ok d' from h)
  obtain ⟨t0, t, e0, e1, e2⟩ := h'
  cases e0
  exact ⟨t, e1, Keeps.named_ok e2⟩

/-- `Block.retype` leaves the decision as it is. -/
theorem retype_yes {T C C' : Type} (b : Block T C) :
    (b.retype (Cl' := C')).decide = b.decide := rfl

/-- An entry of a list that is carried over by `Block.retype`. -/
theorem map_retype {T C C' : Type} (l : List (Block T C)) (i : Nat) (b : Block T C)
    (h : l[i]? = some b) : (l.map (Block.retype (Cl' := C')))[i]? = some b.retype := by
  rw [List.getElem?_map, h]
  rfl

/-- The shared chain's parameters at the maker's public part. -/
abbrev qAt (Z : ProofFile.Pub) (N : H2U.Places4) : P14 := p14Of Z.p.chains (beforePointOf N)

/-- **THE SEAT, IN THE DESCRIPTION's OWN LIST.** -/
theorem k01_sits_shared_seat (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (N : H2U.Places4)
    (B : ProofFile.SecondSeat) (c : Chain VerifiableInference.Desc.First.S ProofFile.Cl)
    {u : Array OracleNotice} (hu : withU (qAt Z N).S = some u) :
    (descZ o Z N B c).shared.back[1]? = some (sendU (qAt Z N) u).retype ∧
      (descZ o Z N B c).shared.back[4]? = some (sendOm (qAt Z N)).retype := by
  obtain ⟨h1, h4⟩ := blocksOr_sends (qAt Z N) hu (VerifiableInference.Desc.K12.Seat.tests N)
  exact ⟨map_retype _ 1 _ h1, map_retype _ 4 _ h4⟩

/-- **SEAT AND NUMBERS AT THE TWO PLACES.** -/
theorem k01_sits_shared : ∃ x : LinSized, realSized = some (x, codesFull2) ∧
    ∀ (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (N : H2U.Places4) (B : ProofFile.SecondSeat)
      (c : Chain VerifiableInference.Desc.First.S ProofFile.Cl),
      (qAt Z N).codes = codesFull2 → (qAt Z N).S = x.shape →
      ∃ u, withU (qAt Z N).S = some u ∧
        (descZ o Z N B c).shared.back[1]? = some (sendU (qAt Z N) u).retype ∧
        PlaceOk 2 1 0 (parK1 (qAt Z N) 2 "o_u and the first mask" u) ∧
        (descZ o Z N B c).shared.back[4]? = some (sendOm (qAt Z N)).retype ∧
        PlaceOk 2 1 1 (parK1 (qAt Z N) 5 "o_omega and o_sp" (withOmega (qAt Z N).S)) := by
  obtain ⟨x, -, -, hx, -, -, -, -, -, -, -, hQ, -, -⟩ := k01_real
  refine ⟨x, hx, fun o Z N B c hc hs => ?_⟩
  obtain ⟨⟨u, hu, p0⟩, p1⟩ := hQ (qAt Z N) hc hs
  obtain ⟨s0, s1⟩ := k01_sits_shared_seat o Z N B c hu
  exact ⟨u, hu, s0, p0, s1, p1⟩

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.blocksOr_sends
#print axioms VerifiableInference.Desc.K1.sendU_place
#print axioms VerifiableInference.Desc.K1.sendOm_place
#print axioms VerifiableInference.Desc.K1.sendU_isSend
#print axioms VerifiableInference.Desc.K1.sendOm_isSend
#print axioms VerifiableInference.Desc.K1.sendAt_yes
#print axioms VerifiableInference.Desc.K1.retype_yes
#print axioms VerifiableInference.Desc.K1.map_retype
#print axioms VerifiableInference.Desc.K1.k01_sits_shared_seat
#print axioms VerifiableInference.Desc.K1.k01_sits_shared
