-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/PaidAll.lean: kind K14: **Plays (Honest/Thread/Pays.lean) AND
FitsAt (Honest/Thread/Shape.lean) AT ALL EIGHT MEMBERS OF THE LINEAR CLAIM's SHARED ROUNDS**: the
kind's own six (Honest/K14/PaidQuiet.lean, FitsPaid.lean) and the two sendings
(Honest/K14/SendingsPaid.lean), under one list of premises on the thread's fields. GENERAL IN ALL
FIELDS OF THE THREAD BUT: bs at eight numbers · hs · table and fixed at the sendings' trees · stored
and valid at the item that "LOC" reads · and, through TreesLaid, front, chain and the counts of
trees and rounds of every member in front of a sending. WHERE THE THREAD's LIST HAS NO MEMBER AT
b0 + i, AtEight's clause, Plays and FitsAt hold there for nothing: each speaks of whatever stands at
the number.

  sendDeclared_like   what a sending's row asks of a sub-protocol hangs on its rounds and oracle
                  messages alone
  witOf           what the two sendings' parts are handed of the input: the committed table's rows,
                  whole
  sendU_found, sendOmega_found   what stands at b0 + 1 | b0 + 4 declares a sending's two rounds, and
                  the sending's half is found at its place
  atSendU_of, atSendOmega_of   so AtSend holds at b0 + 1 and b0 + 4, where TreesLaid does
                  (Honest/K14/SendingsPaid.lean): TreesLaid is a premise and is handed through
  eight_Play      **Plays at b0, …, b0 + 7**
  send_Fits       FitsAt at a member that declares a sending's two rounds, with a sending's half
  eight_Fits      **FitsAt at b0, …, b0 + 7**: it asks neither TreesLaid nor the columns

THE PREMISES, all on the thread's fields: AtEight (Honest/K14/PaidAt.lean) · the two sendings'
halves are among the thread's halves · TreesLaid at both sendings: IT PINS THE FIELD table AT EACH
NEW TREE TO ONE TERM, sendTable: so of "its new trees are the functions' tables" what is proved
here is that the coins at the part's address are those lent, that the table turns no more behind
fixed, and the number of trees; that this table encodes what the thread's witness says is no part of
Plays · for "LOC": the committed table has its columns. None names a coin of the run's, a value that
is sent, a challenge or a state of the verifier's.

What is not claimed. That these premises hold at the shared chain's thread of the IOP as written in
Lean. (Files above this one show some of them at the thread of letters2: AtEight from a premise on
the halves, Honest/K14/AcceptedAll.lean: atEight2; the sendings' halves, and under Plan2 TreesLaid,
at one laid term of the open letters, Honest/K14/Thread2Full.lean: sendsIn_full, treesU_full,
treesO_full. The premise on "LOC"'s columns is not among them.) The other sentences that a thread
asks at a member. Nothing on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.FitsPaid
import Johnson.Desc.ProofFile.Honest.K14.SendingsPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place)
open Desc.K14 (P14 St blocks)

variable {Bk : ProverCoinCounts} {S Cl S' Cl' W₀ Rc Ky X Pb : Type}

/-- What a sending's row asks of a sub-protocol hangs on its rounds and oracle messages alone. -/
theorem sendDeclared_like {b : Block S Cl} {c : Block S' Cl'} {J : SendJob}
    (hr : b.rounds = c.rounds) (ho : b.oracles = c.oracles) (h : SendDeclared c J) :
    SendDeclared b J := by
  obtain ⟨d₀, d₁, os, r, o, rest⟩ := h.rounds
  exact ⟨d₀, d₁, os, hr.trans r, ho.trans o, rest⟩

/-- What the two sendings' parts are handed of the input: the committed table's rows, whole
(rowsOf). -/
def witOf (P : P14) (weights : W₀ → Weights) (rand : Rc → TableRand) (c : Common W₀ Rc Ky) : Ask :=
  ⟨rowsOf P.S (weights c.w₀) (rand c.rc)⟩

variable {T : Thread Bk S Cl Empty (Common W₀ Rc Ky) X Pb} {b0 : Nat} {P : P14} {A : Data}
  {weights : W₀ → Weights} {rand : Rc → TableRand}

/-- What stands at b0 + 1 declares the two rounds of "send o_u", and that sending's half is found at
its place. -/
theorem sendU_found (h : AtEight T b0 P A weights)
    (hh : ∀ g ∈ (proverSidesOfSharedSendings ⟨P, A.atPoint⟩ weights rand :
      List (Placed Empty (Common W₀ Rc Ky) X)), g ∈ T.hs) (blk : Block S Cl)
    (hblk : T.bs[b0 + 1]? = some blk) :
    SendDeclared blk (jobU ⟨P, A.atPoint⟩) ∧ (T.hs.find? fun g => g.place == blk.place) =
      some { place := blk.place
             parts := [liftSend (witOf P weights rand) (sendingPart (jobU ⟨P, A.atPoint⟩))] } := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb, hm⟩ := h.eight
  obtain ⟨dU, pU, -, -⟩ := send_declares P A.atPoint b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨hr, ho, hp⟩ := hm 1 b2 rfl blk hblk
  refine ⟨sendDeclared_like hr ho dU, ?_⟩
  rw [hp, pU]
  exact find_of_mem T.hs { place := sendPlace 2, parts := _ } h.apart
    (hh _ (by rw [sendHalves_eq]; exact List.mem_cons_self ..))

/-- The like of "send o_omega", at b0 + 4. -/
theorem sendOmega_found (h : AtEight T b0 P A weights)
    (hh : ∀ g ∈ (proverSidesOfSharedSendings ⟨P, A.atPoint⟩ weights rand :
      List (Placed Empty (Common W₀ Rc Ky) X)), g ∈ T.hs) (blk : Block S Cl)
    (hblk : T.bs[b0 + 4]? = some blk) :
    SendDeclared blk (jobOmega ⟨P, A.atPoint⟩) ∧ (T.hs.find? fun g => g.place == blk.place) =
      some { place := blk.place
             parts :=
               [liftSend (witOf P weights rand) (sendingPart (jobOmega ⟨P, A.atPoint⟩))] } := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb, hm⟩ := h.eight
  obtain ⟨-, -, dO, pO⟩ := send_declares P A.atPoint b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨hr, ho, hp⟩ := hm 4 b5 rfl blk hblk
  refine ⟨sendDeclared_like hr ho dO, ?_⟩
  rw [hp, pO]
  exact find_of_mem T.hs { place := sendPlace 5, parts := _ } h.apart
    (hh _ (by rw [sendHalves_eq]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)))

/-- AtSend at b0 + 1, for "send o_u": whatever stands there declares that sending's two rounds, and
the sending's half is found at its place. From AtEight and the two sendings' halves among the
thread's. That a member stands there is not said. AtSend's third field, TreesLaid, is a premise (ht)
and is handed through. -/
theorem atSendU_of (h : AtEight T b0 P A weights)
    (hh : ∀ g ∈ (proverSidesOfSharedSendings ⟨P, A.atPoint⟩ weights rand :
      List (Placed Empty (Common W₀ Rc Ky) X)), g ∈ T.hs)
    (ht : TreesLaid T (b0 + 1) (jobU ⟨P, A.atPoint⟩) (witOf P weights rand)) :
    AtSend T (b0 + 1) (jobU ⟨P, A.atPoint⟩) (witOf P weights rand) :=
  ⟨fun blk hblk => (sendU_found h hh blk hblk).1, fun blk hblk => (sendU_found h hh blk hblk).2, ht⟩

/-- AtSend at b0 + 4, for "send o_omega": whatever stands there declares that sending's two rounds,
and the sending's half is found at its place. From AtEight and the two sendings' halves among the
thread's. That a member stands there is not said. AtSend's third field, TreesLaid, is a premise (ht)
and is handed through. -/
theorem atSendOmega_of (h : AtEight T b0 P A weights)
    (hh : ∀ g ∈ (proverSidesOfSharedSendings ⟨P, A.atPoint⟩ weights rand :
      List (Placed Empty (Common W₀ Rc Ky) X)), g ∈ T.hs)
    (ht : TreesLaid T (b0 + 4) (jobOmega ⟨P, A.atPoint⟩) (witOf P weights rand)) :
    AtSend T (b0 + 4) (jobOmega ⟨P, A.atPoint⟩) (witOf P weights rand) :=
  ⟨fun blk hblk => (sendOmega_found h hh blk hblk).1,
    fun blk hblk => (sendOmega_found h hh blk hblk).2, ht⟩

/-- **Plays at all eight members of the linear claim's shared rounds**, from AtEight, the two
sendings' halves among the thread's, TreesLaid at both sendings, and, for "LOC", that at every valid
input the committed table has its columns, each of the declared width. -/
theorem eight_Play (h : AtEight T b0 P A weights)
    (hh : ∀ g ∈ (proverSidesOfSharedSendings ⟨P, A.atPoint⟩ weights rand :
      List (Placed Empty (Common W₀ Rc Ky) X)), g ∈ T.hs)
    (hU : TreesLaid T (b0 + 1) (jobU ⟨P, A.atPoint⟩) (witOf P weights rand))
    (hO : TreesLaid T (b0 + 4) (jobOmega ⟨P, A.atPoint⟩) (witOf P weights rand))
    (hcol : ∀ w, T.valid w → ∀ p < 2 ^ (Desc.K14.readsAtLoc P.S.fold P.item).sh.a,
      ∃ u, T.stored w (Desc.K14.readsAtLoc P.S.fold P.item).item p = some u ∧
        u.length = (Desc.K14.readsAtLoc P.S.fold P.item).sh.W) :
    Plays T b0 ∧ Plays T (b0 + 1) ∧ Plays T (b0 + 2) ∧ Plays T (b0 + 3) ∧ Plays T (b0 + 4) ∧
      Plays T (b0 + 5) ∧ Plays T (b0 + 6) ∧ Plays T (b0 + 7) := by
  obtain ⟨p0, p2, p3, p5, p6, p7⟩ := six_Play h hcol
  exact ⟨p0, send_Plays (atSendU_of h hh hU), p2, p3, send_Plays (atSendOmega_of h hh hO), p5, p6,
    p7⟩

/-- FitsAt at a member that declares a sending's two rounds, with a half of one part of two
moves. -/
theorem send_Fits {b : Nat} {J : SendJob} {wit : Common W₀ Rc Ky → Ask}
    (h : ∀ blk, T.bs[b]? = some blk → SendDeclared blk J ∧
      (T.hs.find? fun g => g.place == blk.place) =
        some { place := blk.place, parts := [liftSend wit (sendingPart J)] }) : FitsAt T b :=
  fitsAt_found fun blk hblk => by
    obtain ⟨hd, hf⟩ := h blk hblk
    obtain ⟨d₀, d₁, os, hr, ho, -⟩ := hd.rounds
    exact ⟨_, hf, by rw [hr]; rfl, by rw [hr, ho]; rfl⟩

/-- **FitsAt at all eight members of the linear claim's shared rounds**, from AtEight and the two
sendings' halves among the thread's. -/
theorem eight_Fits (h : AtEight T b0 P A weights)
    (hh : ∀ g ∈ (proverSidesOfSharedSendings ⟨P, A.atPoint⟩ weights rand :
      List (Placed Empty (Common W₀ Rc Ky) X)), g ∈ T.hs) :
    FitsAt T b0 ∧ FitsAt T (b0 + 1) ∧ FitsAt T (b0 + 2) ∧ FitsAt T (b0 + 3) ∧ FitsAt T (b0 + 4) ∧
      FitsAt T (b0 + 5) ∧ FitsAt T (b0 + 6) ∧ FitsAt T (b0 + 7) := by
  obtain ⟨f0, f2, f3, f5, f6, f7⟩ := six_Fits h
  exact ⟨f0, send_Fits (sendU_found h hh), f2, f3, send_Fits (sendOmega_found h hh), f5, f6, f7⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.sendU_found
#print axioms ProofFile.Honest.K14.sendOmega_found
#print axioms ProofFile.Honest.K14.send_Fits
#print axioms ProofFile.Honest.K14.eight_Fits
#print axioms ProofFile.Honest.K14.sendDeclared_like
#print axioms ProofFile.Honest.K14.atSendU_of
#print axioms ProofFile.Honest.K14.atSendOmega_of
#print axioms ProofFile.Honest.K14.eight_Play
