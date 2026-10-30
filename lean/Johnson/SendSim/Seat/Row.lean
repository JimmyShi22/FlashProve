-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/Row.lean: the honest sender with its simulator as a row for the rule. If the
side of that row has K1's rounds and oracle messages it is Seated. If also the book satisfies
BookClear it has the structure Good, at predicates A and B that never hold, so that plays and acc
hold vacuously, given the statement Spec.sendFreshAt as a hypothesis. It claims no property of the
protocol: not hiding, not zero knowledge.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. a is any place, J any job, σ₀ any side that Side.seated returns for sendRow a J.
  sendRow    The sender's row ("our row" in this folder), of the type Unlettered: the place a; one
             part, the sender sendPart J, with its simulator sendSim at the address (a, 0); On :=
             True; the bound on queried positions budAt.
  seated_at  If σ₀'s sub-protocol has K1's two rounds and oracle messages at J.P, σ₀ is Seated at J.
  good_at    If moreover the book satisfies BookClear at (a, 0), σ₀ has Good. A and B are the
             predicates that never hold, so the fields plays (the row can be played) and acc (the
             verifier accepts) hold vacuously. exact comes from the theorem sendExactAt: ExactAt
             gives the field at every pre. fresh comes from the hypothesis Spec.sendFreshAt, which
             is proved as sendFreshAt.
  hand_at    Under the same premises every side of the row, with the rule's predicates substituted
             (Unlettered.lay), has Good for some A₁ and B₁. This is what the rule's premise hand₁
             requires of each row of the first chain. In the proof A₁ and B₁ are again the
             predicates that never hold.

Limits.
No equation between distributions is proved in this file.
BookClear (Johnson/SendSim/At/Fresh.lean, "clear") is a public premise, narrower than the "clear" of
AtDescLots.lean. With a coin spent, it is evaluated at the books of small examples by #guard lines
(Johnson/SendSim/At/FilledBooks.lean), and a #guard leaves no theorem; it is proved in this folder
at no book of the release (see AtDescLots.lean, Limits).
That the sub-protocol at our row's place has K1's rounds and oracle messages is not proved here,
since the maker wraps the sub-protocol at that place (AtDesc.lean, "Why it is needed"). At the
descriptions of the release's files, Seated is proved only for the sides at the places of the kind
K1 that result (3) of Johnson/SendSim/Defs.lean names (seatedAt_job, if the maker of the proof
file's description succeeds; seatedAt_key). The other sendings of that kind are not covered.

How it fits. Unlettered is in Johnson/Desc/ProofFile/Honest/Thread/Rows.lean, sendExactAt in
Johnson/SendSim/At/ExactAt.lean, sendFreshAt in Johnson/SendSim/At/FreshAtMember.lean. hand_at is by
hand_of_house (Johnson/Desc/ProofFile/Honest/Thread/RowsMore.lean). LotOf.lean, Lot.lean and
LotW.lean make lots of rows sendRow and prove that, without the simulators, such a lot is the lot of
the senders. seated_at serves Spec.fieldsAtLots through seated_lifted (LotOf.lean) and seatedAt_own
(AtDesc.lean). HandedWide.lean states the like of good_at and hand_at for BookClearAny (proved in
HandedWideProofs.lean).

The other names.
  row_of_seated   a side that Side.seated returns has the row that Side.seated was given.
  sendRow_half    without the simulator the row is the sender alone at a. No file uses it: it is a
                  check, by rfl, of what is left of the row when the simulator is dropped.
-/
import Johnson.Desc.ProofFile.Honest.Thread.RowsMore
import Johnson.SendSim.At.SeatedAt
import Johnson.SendSim.At.GoodOf
import Johnson.SendSim.At.ExactAt

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc OnBytes.SendSim.At

variable {S Cl V W X Pb : Type}

/-- The sender's row ("our row") at a place a and a job J: the place; one part, the honest sender
sendPart J, with its simulator sendSim at the address (a, 0); On := True; and the bound on queried
positions budAt. -/
def sendRow (a : Place) (J : SendJob W X) : Unlettered V W X Pb :=
  ⟨a, [(sendPart J, sendSim J.P J.first J.ride ⟨a, 0⟩)], fun _ _ _ _ => True,
    fun _ _ asks => budAt J.P asks⟩

/-- Without the simulator, our row is the sender alone at the place. -/
theorem sendRow_half (a : Place) (J : SendJob W X) :
    (sendRow (V := V) (Pb := Pb) a J).half = ⟨a, [sendPart J]⟩ := rfl

/-- A side that Side.seated returns has the row that Side.seated was given. -/
theorem row_of_seated {bs : List (Block S Cl)} {a : Place}
    {row : List (ProofFile.Honest.Part V W X × Sim Pb)} {fs : List (Fall S)} {σ : Side S Cl V W X Pb}
    (h : Side.seated bs a row fs = some σ) : σ.row = row := by
  unfold Side.seated at h
  cases hb : bs.find? fun b => b.place == a with
  | none => rw [hb] at h; cases h
  | some b =>
    rw [hb] at h
    cases h
    rfl

/-- If Side.seated returns a side for our row, and that side's sub-protocol has K1's two rounds and
oracle messages at J.P, then the side is Seated at J. -/
theorem seated_at {bs : List (Block S Cl)} {a : Place} {J : SendJob W X} {fs₀ : List (Fall S)}
    {σ₀ : Side S Cl V W X Pb}
    (hσ : Side.seated bs (sendRow (V := V) (Pb := Pb) a J).place (sendRow a J).row fs₀ = some σ₀)
    (hr : σ₀.block.rounds = K1.rounds J.P) (ho : σ₀.block.oracles = K1.oracles J.P) :
    Seated σ₀ J :=
  seated_of_send σ₀ J (by rw [row_of_seated hσ, place_of_seated hσ]; rfl) hr ho

/-- A side that Side.seated returns for our row, and whose sub-protocol has K1's two rounds and
oracle messages at J.P, has the structure Good at every book that satisfies BookClear at the address
(a, 0), with predicates A and B that never hold, so that plays and acc hold vacuously. The
hypothesis Hr is proved as sendFreshAt in Johnson/SendSim/At/FreshAtMember.lean.
pre is tied to no description; of Good's fields exact alone reads it, and at each pre that field
says no more than ExactAt. -/
theorem good_at {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (Hr : Spec.sendFreshAt) (φ : Face V W Pb) {bs : List (Block S Cl)} {a : Place}
    {J : SendJob W X} {fs₀ : List (Fall S)} {σ₀ : Side S Cl V W X Pb} (Bk : ProverCoinCounts)
    (ord : List Place) (chain ft : Nat)
    (hσ : Side.seated bs (sendRow (V := V) (Pb := Pb) a J).place (sendRow a J).row fs₀ = some σ₀)
    (hr : σ₀.block.rounds = K1.rounds J.P) (ho : σ₀.block.oracles = K1.oracles J.P)
    (hB : BookClear J.P J.ride Bk ord ⟨a, 0⟩) :
    Good pre φ σ₀ Bk ord chain ft (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (sendRow (V := V) (Pb := Pb) a J).On (sendRow (V := V) (Pb := Pb) a J).bud :=
  good_of_specs sendExactAt Hr φ σ₀ J Bk ord chain ft (seated_at hσ hr ho)
    (by rw [place_of_seated hσ]; exact hB)

/-- Under the premises of good_at, every side of our row with the rule's predicates substituted
(Unlettered.lay) has Good for some A₁ and B₁; in the proof these are the two that never hold, so
plays and acc hold vacuously. The hypothesis Hr is proved as sendFreshAt in
Johnson/SendSim/At/FreshAtMember.lean.
pre is tied to no description; of Good's fields exact alone reads it, and at each pre that field
says no more than ExactAt. -/
theorem hand_at {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (Hr : Spec.sendFreshAt) (φ : Face V W Pb) {bs : List (Block S Cl)} {a : Place}
    {J : SendJob W X} {fs fs₀ : List (Fall S)} {σ₀ : Side S Cl V W X Pb} {Bk : ProverCoinCounts}
    (ord : List Place) (chain ft : Nat) (T : W → Thread Bk S Cl V W X Pb)
    (Sd : W → Nat → Coins Bk → Mid W X → Prop)
    (hσ : Side.seated bs (sendRow (V := V) (Pb := Pb) a J).place (sendRow a J).row fs₀ = some σ₀)
    (hr : σ₀.block.rounds = K1.rounds J.P) (ho : σ₀.block.oracles = K1.oracles J.P)
    (hB : BookClear J.P J.ride Bk ord ⟨a, 0⟩) :
    ∀ σ, ((sendRow (V := V) (Pb := Pb) a J).lay T Sd bs).side bs fs = some σ →
      ∃ A₁ B₁, Good pre φ σ Bk ord chain ft A₁ B₁ ((sendRow a J).lay T Sd bs).On
        ((sendRow a J).lay T Sd bs).bud :=
  hand_of_house (sendRow a J) T Sd hσ (good_at Hr φ Bk ord chain ft hσ hr ho hB)

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.seated_at
#print axioms OnBytes.SendSim.Seat.good_at
#print axioms OnBytes.SendSim.Seat.hand_at
#print axioms OnBytes.SendSim.Seat.sendRow
#print axioms OnBytes.SendSim.Seat.sendRow_half
#print axioms OnBytes.SendSim.Seat.row_of_seated
