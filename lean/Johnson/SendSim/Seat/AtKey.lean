-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/AtKey.lean: at the three sub-protocols of the kind K1 in a key file's first
chain (the index-mask message, the lookups' own message, W) the description has a member. The side
of the honest sender and its simulator there satisfies the field fits and ExactAt, and the field
fresh if the book is clear (BookClearAny). It claims no property of the protocol: not hiding, not
zero knowledge.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". There the description is the proof
file's; here it is the key file's Key.descriptionFromSource. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file has. F is Key.descriptionFromSource Xs N Q (Johnson/Desc/Key/Desc.lean), a key file's description, at
any source Xs and any numbers N and Q. F is an explicit Lean term, so no premise says that a maker
returned it. Where the maker descriptionFromPlan returns a description, it is Key.descriptionFromSource at some Xs, N and Q
(descOfMade_is, Johnson/Desc/Key/SlotIs.lean). (P, ride) is any entry of keyPars Xs
(AtKeyPars.lean): the description's own public numbers at one of the three places, and which table
is sent along there. J is any job with J.P = P and J.ride = ride; the number of its first new
message and its data are free.
  fieldsAtKey_all   The main theorem. (1) F's first chain has a member at P's place. (2) Every side
                    that Side.seated returns there for the row of the sender sendPart J and the
                    simulator sendSim J.P J.first J.ride has fits and exact; no book is mentioned.
                    (3) For every book and order at which the book is clear at that sender, that
                    side has fresh.
  Spec.fieldsAtKey  The same under the further premise that no two members of F's first chain are at
                    one place; proved as fieldsAtKey. That premise always holds (key_places_apart,
                    AtKeyStands.lean); fieldsAtKey_all is the same statement without it.
  handAtKey         Parts (2) and (3) in the form that the rule asks of one row: if the book is
                    clear at that sender, every side of the row, with the rule's predicates
                    substituted, has Good for some A₁ and B₁. It says no more.
  key_seat          (AtKeyStands.lean) part (1) in the form of the rule's premise on a row's place.

How it fits. These rows are kept for whoever writes the key file's honest prover in the framework of
Johnson/Desc/ProofFile/Honest/, which is not among the files that this folder imports (Limits): the
sender, which table is sent along, the simulator, and three fields of Good at the description's own
members. The proof joins seatedAt_key (AtKeyStands.lean) to sendExactAt
(Johnson/SendSim/At/ExactAt.lean) and sendFreshAtWide (Johnson/SendSim/Seat/HandedWideProofs.lean),
which speak of every Seated side. Meant as steps toward index privacy
(Johnson/WholeKey/Statement.lean); nothing in this folder derives index privacy from them. Not one
of the release's goal statements.

Limits.
The coins. Both equations take the sender's coins as drawn uniformly for this one run of the key
file's proof, independently of the input. In the frame the input holds the index, the committer's
randomness for the stored table and the key. The sender's coins go to no other part except as the
book says. By the library's definitions (by inspection, not proved), the instance's key and the
commitment ID are made of the stored table's root and answers, the public files' digest and the
shape (OnBytes/Iop/Foldeq.lean, OnBytes/Key/Table.lean, OnBytes/K/Left/Id.lean). None of them is
made of these three messages. The library does not show how the committer's program draws these
coins. The trees' roots, the chains' seals and the file's bytes are made of them; this frame models
no hash. A statement that uses these rows must not put these coins and a fixed parameter into one
premise: under such a premise the law could range over fewer coins than these equations do.
No premise of the statement has a key in it or speaks of the input. Inside exact and fresh the input
appears only in the premise that the part does not abort, which the sender never does. The input is
universally quantified in both equations, so whatever it holds (in the frame: the index, the
committer's randomness, the key) is a fixed parameter there. The simulator reads neither the public
part nor what the parts in front disclose.
Each of the three sampled messages has one pad for each answer: an entry of its last mask row
(padNo, Johnson/SendSim/At/Fresh.lean), except W's at the small size, which has no mask row and lies
in its main row. What is known of the stored table's pads (at a fixed index and key they are no
coins) does not touch these (argued on paper, not proved). Their answers are sent in this run, after
seeds that this run samples, so they are among what is disclosed, on both sides of both equations.
The instance's key holds answers of the stored table's rows alone (TableKey,
OnBytes/Iop/Foldeq.lean).
Not every sending. By a count over the written list (Johnson/G/SendsLit.lean; by inspection, not
proved) a key file has 19 sendings under the entry "SEND seed" at the full size (14 at the small
size), six of them in its first chain. These are three. Each of the 19 sends at least one message
with mask rows. The other three of the first chain are inside the ranges' test (the kind K12). The
rule asks a row at every sub-protocol.
The statement does not tie the fold of a table that is sent along to the test that spends it: N and
Q are free here. The description's own tests on the plan do. Where Key.descriptionFromSource Xs N Q passes them, both
tables are sent along, and k, h and the codes' numbers of each are those of the first stage of the
verifier's proximity test that is made to fold with it (key_folds_some, key_msg_ride_tie,
key_w_ride_tie, key_member_tie, RideTies.lean). The ties reach the verifier's sub-protocols alone:
nothing rules out a book that is clear while it names another part, or none, as the spender.
Among the files that this folder imports there is no honest prover of a key file in the framework of
Johnson/Desc/ProofFile/Honest/ (parts at the description's places). The jobs are tied to the
description's numbers, not to a prover's definition. Data and first number are universally
quantified, so the statement holds at whatever a prover will take; which values those are is said in
no file that this folder imports.
At the three places' numbers the premise on the book is proved in this folder at books without
entries (clearAny_of_no_entry, AtDescLots.lean). At the key file's own book, where `fullPub` returns
it: at the written numbers and the written order of places, key_clear
(AtFullSide/K1/KeyBookClear.lean); at the key file's own numbers, under `OneFull` besides,
index_clear, multiplicities_clear, messageW_clear (E2E/OfflineFirstSends.lean). The files that this
folder imports have no book of a key file.
That a job fits its place (sendFits) is no premise. Where Key.descriptionFromSource Xs N Q passes its tests on the
plan, all three jobs fit (fits_at_key, FitsAtKey.lean). In the goals' scope, wherever the key file's
makers return, the test on queried positions accepts at the three, so the positions that the
description's rounds read of these senders' trees meet the bound (keyReads_in_scope,
bud_of_keyReads, KeyReadsAtLive.lean). Where also the library's gate accepts, the makers return and
the description passes its tests on the plan (keyAt_of_live there; that the gate accepts at named
files: AtFullSide/Top/LiveAtFull.lean, LiveAtPolicies.lean). At the three places a test on the book
accepts at the key file's book at the written letters (`key_fast`, `key_clear`,
AtFullSide/K1/KeyBookClear.lean, with its limits).
One sender at a time: nothing is said of the coins of two senders together (AtDescLots.lean,
Limits). Here this matters: by the verifier's definitions one lookup takes mask entries both of the
lookups' own message and of the index-mask message (OnBytes/Iop/Wf.lean, head).
Where the shape has no message for W, keyPars has two entries. Where Key.descriptionFromSource Xs N Q passes its
tests on the plan it has three (key_w_there, RideTies.lean).
All limits of AtDescLots.lean that speak of exact, fresh, Good, the book and the rule hold here too:
never part (2) without part (3); three fields of five; oracle messages alone; what stands as a
premise inside exact and fresh. At the full size the key file's index-mask sending has one oracle
message, of mask rows alone: it holds no datum, so exact says nothing there, and exact has content
at two of the key file's three rows (by inspection of the written shapes, not proved).
-/
import Johnson.SendSim.Seat.AtKeyStands
import Johnson.SendSim.Seat.AtDescOwn
import Johnson.SendSim.Seat.HandedWideProofs

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At

/-- Statement only; proved as fieldsAtKey below. At a key file's description in whose first chain no
two members are at one place, at each of the three sub-protocols of the kind K1 in that chain, for
every job with the description's public numbers and the table that is sent along there: the chain's
list has a member at the place; every side that Side.seated returns there for the sender's row has
fits and exact; and if a book is clear at that sender, the side has fresh at that book. The bound on
queried positions is a premise inside exact and fresh; KeyReadsAtLive.lean proves it, for the
positions that the description's rounds read, in the goals' scope wherever the key file's makers
return. Among the files that this folder imports there is no book of a key file; where the premise
on the book is proved: the head's Limits. -/
def Spec.fieldsAtKey : Prop :=
  ∀ (V W X Pb : Type) (Xs : Key.Source) (N : H2U.PlaceNums) (Q : Key.LaterPlaces)
    (_ : ((Key.descriptionFromSource Xs N Q).first.blocksInOrder.map (·.place)).Nodup)
    (φ : Face V W Pb) (chain ft : Nat) (fs : List (Fall (Key.descriptionFromSource Xs N Q).S₁)),
    ∀ x ∈ keyPars Xs, ∀ J : SendJob W X, J.P = x.1 → J.ride = x.2 →
      (Key.descriptionFromSource Xs N Q).first.blocksInOrder.any (fun b => b.place == J.P.place) = true ∧
      ∀ σ : Side (Key.descriptionFromSource Xs N Q).S₁ (Key.descriptionFromSource Xs N Q).Cl V W X Pb,
        Side.seated (Key.descriptionFromSource Xs N Q).first.blocksInOrder
            (sendRow (V := V) (Pb := Pb) J.P.place J).place (sendRow J.P.place J).row fs = some σ →
          σ.fits = true ∧
            ExactAt φ σ chain ft (sendRow (V := V) (Pb := Pb) J.P.place J).On
              (sendRow (V := V) (Pb := Pb) J.P.place J).bud ∧
            ∀ (Bk : ProverCoinCounts) (ord : List Place),
              BookClearAny J.P J.ride Bk ord ⟨J.P.place, 0⟩ →
              FreshAt φ σ Bk ord (sendRow (V := V) (Pb := Pb) J.P.place J).bud

variable {V W X Pb : Type}

/-- **At the key file's description Key.descriptionFromSource Xs N Q, for every source and all numbers, at each of
the three sub-protocols of the kind K1 in its first chain, for every job with the description's
public numbers and the table that is sent along there: a member is at the place; every side there
has fits and exact; and, if a book is clear at that sender, fresh at that book.** The premise on the
table that is sent along is not used in the proof, so the theorem holds at every ride; the premise
keeps the statement to the table that keyPars names (how far that is the table really sent:
AtKeyPars.lean, Limits). -/
theorem fieldsAtKey_all (Xs : Key.Source) (N : H2U.PlaceNums) (Q : Key.LaterPlaces)
    (φ : Face V W Pb) (chain ft : Nat) (fs : List (Fall (Key.descriptionFromSource Xs N Q).S₁))
    {x : K1.Par × (Nat → Option Ride)} (hx : x ∈ keyPars Xs) (J : SendJob W X) (hP : J.P = x.1)
    (_hR : J.ride = x.2) :
    (Key.descriptionFromSource Xs N Q).first.blocksInOrder.any (fun b => b.place == J.P.place) = true ∧
      ∀ σ : Side (Key.descriptionFromSource Xs N Q).S₁ (Key.descriptionFromSource Xs N Q).Cl V W X Pb,
        Side.seated (Key.descriptionFromSource Xs N Q).first.blocksInOrder
            (sendRow (V := V) (Pb := Pb) J.P.place J).place (sendRow J.P.place J).row fs = some σ →
          σ.fits = true ∧
            ExactAt φ σ chain ft (sendRow (V := V) (Pb := Pb) J.P.place J).On
              (sendRow (V := V) (Pb := Pb) J.P.place J).bud ∧
            ∀ (Bk : ProverCoinCounts) (ord : List Place),
              BookClearAny J.P J.ride Bk ord ⟨J.P.place, 0⟩ →
              FreshAt φ σ Bk ord (sendRow (V := V) (Pb := Pb) J.P.place J).bud := by
  refine ⟨by rw [hP]; exact key_seat Xs N Q x hx, fun σ hσ => ?_⟩
  obtain ⟨h1, h2, h3⟩ := fields_of_seated At.sendExactAt At.sendFreshAtWide φ
    (seatedAt_key Xs N Q hx hP hσ) chain ft
  exact ⟨h1, h2, fun Bk ord hB => h3 Bk ord (by rw [place_of_seated hσ]; exact hB)⟩

/-- Spec.fieldsAtKey holds. Its premise on the places is not used. -/
theorem fieldsAtKey : Spec.fieldsAtKey :=
  fun _ _ _ _ Xs N Q _ φ chain ft fs _ hx J hP hR => fieldsAtKey_all Xs N Q φ chain ft fs hx J hP hR

/-- The last two parts in the form that the rule asks of one row: if the book is clear at that
sender, every side of the row, with the rule's predicates substituted, has Good for some A₁ and
B₁.
pre is tied to no description; of Good's fields exact alone reads it, and at each pre that field
says no more than ExactAt. -/
theorem handAtKey {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (Xs : Key.Source) (N : H2U.PlaceNums) (Q : Key.LaterPlaces) (φ : Face V W Pb)
    (Bk : ProverCoinCounts) (ord : List Place) (chain ft : Nat)
    (T : W → Thread Bk (Key.descriptionFromSource Xs N Q).S₁ (Key.descriptionFromSource Xs N Q).Cl V W X Pb)
    (Sd : W → Nat → Coins Bk → Mid W X → Prop) (fs : List (Fall (Key.descriptionFromSource Xs N Q).S₁))
    {x : K1.Par × (Nat → Option Ride)} (hx : x ∈ keyPars Xs) (J : SendJob W X) (hP : J.P = x.1)
    (hR : J.ride = x.2) (hB : BookClearAny J.P J.ride Bk ord ⟨J.P.place, 0⟩) :
    ∀ σ, ((sendRow (V := V) (Pb := Pb) J.P.place J).lay T Sd (Key.descriptionFromSource Xs N Q).first.blocksInOrder).side
        (Key.descriptionFromSource Xs N Q).first.blocksInOrder fs = some σ →
      ∃ A₁ B₁, Good pre φ σ Bk ord chain ft A₁ B₁
        ((sendRow J.P.place J).lay T Sd (Key.descriptionFromSource Xs N Q).first.blocksInOrder).On
        ((sendRow J.P.place J).lay T Sd (Key.descriptionFromSource Xs N Q).first.blocksInOrder).bud := by
  intro σ hσ
  obtain ⟨hf, he, hfr⟩ := (fieldsAtKey_all Xs N Q φ chain ft fs hx J hP hR).2 σ hσ
  exact ⟨_, _, good_of_fields hf he (hfr Bk ord hB)⟩

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.fieldsAtKey_all
#print axioms OnBytes.SendSim.Seat.fieldsAtKey
#print axioms OnBytes.SendSim.Seat.handAtKey
#print axioms OnBytes.SendSim.Seat.Spec.fieldsAtKey
