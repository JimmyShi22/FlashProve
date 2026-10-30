--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyRangesWholeS.lean: THE KEY FILE's TEST ON THE RANGES IS ACCEPTED, FROM THE PAIR, GIVEN TWO
NAMED TIES ON THE THREAD's LETTERS L AND tb. An assembly: `acceptedS_ranges`
(E2E/KeyRangesSeatedS.lean), `owes_of_thr` (E2E/KeyRangesGrows.lean), `old_KR_same`
(Johnson/Desc/ProofFile/Honest/K12/TreesSentBeforeTestFromSameColumns.lean) and the thread's clause on the trees at hand. WHY
THE TIE IS ON THE THREAD's OWN TABLE: the thread ties the table AT HAND to its own table by
`Table.same` alone (Johnson/Desc/ProofFile/Honest/Thread/Thr.lean: the two numbers, and the columns
below the length), and a table's symbols are a function on all numbers: that the table at hand be
EQUAL to the sending's cannot hold at every stand. The letter tb's value is entered by no stand's
tables at hand. A definition, statements and proofs.

  `own1_hand`     in scope the chain's own tree number 1 is among the trees at hand at the border 15
  **`purse_cut`**    in scope, at the key file's book, AT ALL COINS: the sender's purse can be cut
                 at its start to the sender's own count
  `TbIsSent`      THE TIE ON THE LETTER tb, A PREMISE's FORM: the thread's table behind the chain's
                 own tree number 1, where the run stands, is the table that the part of the sending
                 of the multiplicities makes at the sender's own coins: its purse, cut at its start
  **`old_of_tb`**    in scope: the thread at 15 · the row is lent its coins · `TbIsSent` ⟹ `OldAt`
  **`acceptedS_ties`**    the half is laid · at every stand of the pair: `WitIsJob` (the tie on L)
                 and `TbIsSent` ⟹ `AcceptedS (laid₁ …) Said fall 15`, at every letter fall

Limits.
- THE TWO TIES ARE ASKED, AT EVERY STAND OF THE PAIR; they are shown of no letters. Each reads of a
  stand the run's coins, the input and the challenges heard, and the SHAPE of the verifier's state;
  neither reads the tables at hand. Where tb is simply defined as the sending's table, `TbIsSent`
  holds and says nothing of a run; it has content where tb is the table that the frame's play sends.
- THE LOOKUPS' CONTENT IS MOVED, NOT PROVED: it is taken off the thread's own open sentence. Owed by
  whoever pays the thread's rows at the sub-protocols 0 to 14: their exchanges, AT A WITNESS THAT
  MEETS `WitIsJob`, AT THE TRUE MULTIPLICITIES: the letter entry is free here: nothing ties it to
  L's cells.
- `AcceptedS` IS ONE OF THE MEMBER's DEBTS in the frame: that the play returns and its new trees are
  the thread's, what stands behind the member, its exchange of sentences, what rides past it and
  what is said of the run behind it are not touched at this member.
- A premise's form of the frame's: the member's step accepts where the pair stands and the frame's
  play returns; neither is shown here. In scope; at the written sizes.
- Nothing on completeness, on soundness or on what is hidden.


-/
import E2E.KeyRangesSeatedS
import E2E.KeyRangesGrows
import E2E.KeyRangesLends
import Johnson.Desc.ProofFile.Honest.K12.TreesSentBeforeTestFromSameColumns
import Johnson.Desc.ProofFile.Honest.Thread.Sent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Key (Xi FirstState Claim)
open OnBytes.Slice (GF)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyBook (KeyPub fullPub keyBook)
open AtPublicFiles.KeyTest (sMsg)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K12

variable {W₀ Rc Cells M Smp Rec X' : Type} {Z : PublicFiles} {K : KeyPub}
  (Xs : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (Pl : VerifiableInference.Desc.Key.LaterPlaces)
  (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)
  (L : KeyFill (keyBook K) W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
  (tb : Fmt.TreeSource → Coins (keyBook K) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)

/-- In scope the chain's own tree number 1 is at hand at the border 15. -/
theorem own1_hand (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    Fmt.TreeSource.own 1 ∈ (laid₁ Xs N Pl L w₀ rc x hs tb).hand 15 := by
  unfold Thread.hand
  rw [trees15_laid Xs N Pl L w₀ rc x hs tb hsrc scope]
  exact List.mem_append_right _ (List.mem_map.2 ⟨1, by decide, rfl⟩)

/-- **The sender's purse can be cut at its start to the sender's own count, at all coins**: in
scope, at the key file's book at the written sizes. -/
theorem purse_cut (hK : fullPub = some K) (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (k : Coins (keyBook K)) :
    ∃ c₁ : Cs (K1.dueR (sentRanges Xs entry groups first).P
        (sentRanges Xs entry groups first).ride),
      ((k.look 0) sMsg).2.cut ⟨0, 0⟩
        (K1.dueR (sentRanges Xs entry groups first).P (sentRanges Xs entry groups first).ride) =
          some c₁ := by
  have h6 := AtPublicFiles.AtFiles.Full.six_sourced hsrc scope
  have hst := AtPublicFiles.KeyBook.msgJob_stated (V := Unit) (X := Unit) K hK Xs.Y.k.oneTime
    ⟨h6.codes, h6.indexMasks, h6.ranges, h6.lin⟩ VerifiableInference.Desc.Key.pieces groups first
    entry AtPublicFiles.KeyBook.rideMsg AtPublicFiles.KeyBook.rides_full.2.1
  have e1 : K1.dueR (sentRanges Xs entry groups first).P (sentRanges Xs entry groups first).ride =
      dueAt (keyBook K).first sMsg := congrArg (·.1) hst
  have e2 : ((k.look 0) sMsg).1 = dueAt (keyBook K).first sMsg := AtPublicFiles.KeyBook.look_due k 0 sMsg
  refine AtPublicFiles.KeyBook.cut_some _ _ _ ?_
  rw [e1, e2]
  exact ⟨Nat.le_of_eq (Nat.zero_add _), Nat.le_of_eq (Nat.zero_add _)⟩

/-- **The tie on the thread's own table.** k: a run's coins. m: where the prover's run stands. -/
def TbIsSent (k : Coins (keyBook K)) (m : Mid (Local W₀ Rc Xi Unit) X') : Prop :=
  ∀ c₁ : Cs (K1.dueR (sentRanges Xs entry groups first).P (sentRanges Xs entry groups first).ride),
    ((k.look 0) sMsg).2.cut ⟨0, 0⟩
      (K1.dueR (sentRanges Xs entry groups first).P (sentRanges Xs entry groups first).ride) =
        some c₁ →
    (K1.treeTables (sentRanges Xs entry groups first).P
      (K1.rowsR (sentRanges Xs entry groups first).P (sentRanges Xs entry groups first).ride
        ((sentRanges Xs entry groups first).data m.st.input) c₁))[0]? =
      some ((laid₁ Xs N Pl L w₀ rc x hs tb).tableAt (.own 1) k m).2

/-- **`OldAt`, off the thread's clause on the trees at hand and the tie.** -/
theorem old_of_tb (hK : fullPub = some K) (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {k : Coins (keyBook K)} {s : FirstState} {m : Mid (Local W₀ Rc Xi Unit) X'} {E : Env}
    (c : RowCoins [(firstPart (rangesTestJob (X' := X') Xs N Pl entry groups first) :
      Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'),
      restPart (rangesTestJob (X' := X') Xs N Pl entry groups first)])
    (hT : Thr (laid₁ Xs N Pl L w₀ rc x hs tb) 15 k s m E)
    (hc : lendRow (keyBook K) ((keyBook K).rowsOf 0) (k.look 0)
      (rangesTestJob (X' := X') Xs N Pl entry groups first).p.place
      [(firstPart (rangesTestJob (X' := X') Xs N Pl entry groups first) :
        Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'),
        restPart (rangesTestJob (X' := X') Xs N Pl entry groups first)] 0 = .ok c)
    (hTb : TbIsSent Xs N Pl entry groups first L w₀ rc x hs tb k m) :
    OldAt E ((rangesTestJob (X' := X') Xs N Pl entry groups first).trees₀ m.st.input (frontOf m)
      (restCoins (rangesTestJob (X' := X') Xs N Pl entry groups first) c.2.1).mem
      ((rangesTestJob (X' := X') Xs N Pl entry groups first).first m.st.input (frontOf m)
        (restCoins (rangesTestJob (X' := X') Xs N Pl entry groups first) c.2.1)))
      (fun j => [Fmt.TreeSource.own 1].getD j (.own 0)) := by
  obtain ⟨c₁, hown⟩ := purse_cut Xs N Pl entry groups first hK hsrc scope k
  have hTab := hTb c₁ hown
  obtain ⟨pt, hE, -, hsame⟩ := (laid₁ Xs N Pl L w₀ rc x hs tb).handAt_elim
    (hT.1.2 _ (own1_hand Xs N Pl L w₀ rc x hs tb hsrc scope))
  have hsent : E.sent = 2 := by
    obtain ⟨-, -, -, -, ⟨-, -, e, -⟩, -, -⟩ := hT
    rw [e, trees15_laid Xs N Pl L w₀ rc x hs tb hsrc scope]
  obtain rfl := AtPublicFiles.AtFiles.Full.nums_sourced hsrc scope
  exact old_KR_same K hK (sentRanges Xs entry groups first)
    (sent_codes Xs H2K.Member.nKRFull Pl entry groups first hsrc scope)
    (sent_msgs Xs H2K.Member.nKRFull Pl entry groups first hsrc scope) ride_same rfl
    (recRanges Xs H2K.Member.nKRFull Pl) m.st.input (frontOf m) ((keyBook K).rowsOf 0) (k.look 0) c
    hc c₁ hown E pt.1 pt.2 _ (by rw [hsent]; decide) hE hsame hTab

/-- **Accepted, from the pair, given the two ties.** -/
theorem acceptedS_ties (hK : fullPub = some K) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true)
    (Said : Nat → Coins (keyBook K) → Mid (Local W₀ Rc Xi Unit) X' → Prop)
    (hhalf : (hs.find? fun g => g.place == (rangesTestJob (X' := X') Xs N Pl entry groups first).p.place) =
      some (proverSideOfProximityTest (rangesTestJob (X' := X') Xs N Pl entry groups first)))
    (hW : ∀ k s m E (c : RowCoins [(firstPart (rangesTestJob (X' := X') Xs N Pl entry groups first) :
        Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'),
        restPart (rangesTestJob (X' := X') Xs N Pl entry groups first)]),
      ThrS (laid₁ Xs N Pl L w₀ rc x hs tb) Said 15 k s m E →
      lendRow (keyBook K) ((keyBook K).rowsOf 0) (k.look 0)
        (rangesTestJob (X' := X') Xs N Pl entry groups first).p.place
        [(firstPart (rangesTestJob (X' := X') Xs N Pl entry groups first) :
          Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'),
          restPart (rangesTestJob (X' := X') Xs N Pl entry groups first)] 0 = .ok c →
      WitIsJob (X' := X') Xs N Pl entry groups first L k s m
        (restCoins (rangesTestJob (X' := X') Xs N Pl entry groups first) c.2.1))
    (hTb : ∀ k s m E, ThrS (laid₁ Xs N Pl L w₀ rc x hs tb) Said 15 k s m E →
      TbIsSent Xs N Pl entry groups first L w₀ rc x hs tb k m)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    AcceptedS (laid₁ Xs N Pl L w₀ rc x hs tb) Said fall 15 :=
  acceptedS_ranges Xs N Pl entry groups first L w₀ rc x hs tb hK hsrc scope Said hhalf
    (fun k s m E c hT hc =>
      owes_of_thr Xs N Pl entry groups first L w₀ rc x hs tb hsrc scope hT.1 _ (hW k s m E c hT hc)
        (old_of_tb Xs N Pl entry groups first L w₀ rc x hs tb hK hsrc scope c hT.1 hc
          (hTb k s m E hT))) fall

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.own1_hand
#print axioms AtPublicFiles.KeyThread.purse_cut
#print axioms AtPublicFiles.KeyThread.old_of_tb
#print axioms AtPublicFiles.KeyThread.acceptedS_ties
