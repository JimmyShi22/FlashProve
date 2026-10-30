-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/LaysStands.lean: the honest side of the kind "lookup"
(K3): "what the lookup has heard stands for some rounds" (`K3Stands`, Johnson/Top/H/K3RowOut.lean)
as a clause of a thread's rider (Honest/Thread/Riders.lean): the lookup's member lays it behind its
own accepted step on the thread; it stays past a member that keeps what was heard and only adds to
the ledger. The thread is a variable. Theorems; one definition.

Terms. Honest/K3/GLOSSARY.md. In this file: the member number b of a thread T lays the clause c if c
holds behind the member's own accepted step: `LaysAt T b c` (Honest/Thread/Riders.lean). The clause
c stays past the member number b if that follows from the member's clause of keeps alone:
`StaysBy T b c` (there). A later ledger is `Fo.Later` (OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean).
The seat of the sort d is `seatOf K3Lot.ofForm d` (Honest/K3/Law/Stated.lean).

What is shown.
  `StandsHere d lm first t`: (definition) at the state t the seat of the sort d reads a ledger and
    what was heard, and these stand for some rounds.
  `lays_stands`: the lookup's member lays it, at every number lm and at every clause c that follows
    from it (`hc`), as in the theorems of Honest/K3/Law/Thread/LaysNext.lean; from the seven facts
    that the proof uses, one by one.
  `lays_of_stands`: the same from the structure `K3AtSite` (Honest/K3/Law/Thread/AtThreadSite.lean).
  `standsHere_later`: it passes to a state at which the same is heard and the ledger is a later one.
  `stays_of_stands`: hence it stays past such a member.
  `standsHere_all`: its reading "at every ledger and every heard structure that the seat reads".

Why as a rider, and not by one step back from a later border. The step back in the files under
Honest/Thread/ gives a state that is reached and the member's acceptance on some rounds. The
library's law on the hearing asks that the rounds' words are below the prime and that the ledger in
front has its sizes. At an accepted step on the thread both are had (from the played rounds; from
the lookup's promise in front); at a state that is only reached neither is.

Hypotheses that remain.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`, `hb`, `hbs`, `hmem`, `hpl`, `hplan`, `hfront`: the seven facts: the site; the lot's
    sub-protocol, at the site's place; the thread's member number b stands in the first chain's flat
    list, at that place, and passes its test on the plan; from the thread's relation, the lookup's
    promise in front holds (`k3OnIn`, Johnson/Desc/First/Look/K3Borders.lean). In `lays_of_stands`:
    `hS`, the structure `K3AtSite`, which holds the seven and more.
  `hfv`: the library's test `fitsVia` (Johnson/Desc/First/Look/Via/Via.lean) accepts.
  `hc`; `hin`, `hout`: the implications that connect a clause.
  `hk`: (in `stays_of_stands`) what the other member's clause of keeps gives. It is a named
    hypothesis, for the files on that member to show.
  `hh`, `hF`: (in `standsHere_later`) the seat reads the same as heard at the later state; its
    ledger there is later. `h`: (in `standsHere_all`) `StandsHere`.

Imported, through Honest/K3/Law/Thread/LaysNext.lean. Files under Honest/Thread/.

Limits. Conditional on the hypotheses above. Nothing here shows that a thread with such a clause
exists. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LaysNext
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.StandsBehind
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.OkPlayed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork Reading)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3.Law (fitsVia)
open VerifiableInference.OnPublicFiles (K3Stands k3StandsLater)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **At the state t the seat of the sort d reads a ledger and what was heard, and these stand for
some rounds.** -/
def StandsHere (d : Bool) (lm first : Nat) (t : FS) : Prop :=
  ∃ F' g, (seatOf K3Lot.ofForm d).fork t = some F' ∧ (seatOf K3Lot.ofForm d).heard t = some g ∧
    K3Stands g.shape lm first Reading.gl g F'

/-- **It passes to a state at which the same is heard and the ledger is a later one.** -/
theorem standsHere_later {d : Bool} {lm first : Nat} {t t' : FS}
    (hh : (seatOf K3Lot.ofForm d).heard t' = (seatOf K3Lot.ofForm d).heard t)
    (hF : ∀ F, (seatOf K3Lot.ofForm d).fork t = some F →
      ∃ F', (seatOf K3Lot.ofForm d).fork t' = some F' ∧ _root_.Fo.Later F F') :
    StandsHere d lm first t → StandsHere d lm first t' := by
  rintro ⟨F, g, h1, h2, h3⟩
  obtain ⟨F', k1, k2⟩ := hF F h1
  exact ⟨F', g, k1, hh.trans h2,
    k3StandsLater OnBytes.Slice.GE Reading.gl g.shape lm first g F F' k2 h3⟩

/-- **Its reading at every ledger and every heard structure that the seat reads.** -/
theorem standsHere_all {d : Bool} {lm first : Nat} {t : FS} (h : StandsHere d lm first t) :
    ∀ F' g, (seatOf K3Lot.ofForm d).fork t = some F' →
      (seatOf K3Lot.ofForm d).heard t = some g → K3Stands g.shape lm first Reading.gl g F' := by
  obtain ⟨F, g₀, h1, h2, h3⟩ := h
  intro F' g k1 k2
  obtain rfl : F = F' := Option.some.inj (h1.symm.trans k1)
  obtain rfl : g₀ = g := Option.some.inj (h2.symm.trans k2)
  exact h3

section
variable {Bk : ProverCoinCounts} {V W X Pb Wj : Type} (T : Thread Bk FS ProofFile.Cl V W X Pb)

/-- **Hence it stays past such a member.** Conditional on `hk`: what that member's clause of keeps
gives; `hin` and `hout` connect the clause. -/
theorem stays_of_stands {b' : Nat} (d : Bool) (lm first : Nat) (c : RiderCl W FS)
    (hin : ∀ w t, c.prop b' w t → StandsHere d lm first t)
    (hout : ∀ w t, StandsHere d lm first t → c.prop (b' + 1) w t)
    (hk : ∀ t t', T.keeps b' t t' →
      (seatOf K3Lot.ofForm d).heard t' = (seatOf K3Lot.ofForm d).heard t ∧
        ∀ F, (seatOf K3Lot.ofForm d).fork t = some F →
          ∃ F', (seatOf K3Lot.ofForm d).fork t' = some F' ∧ _root_.Fo.Later F F') :
    StaysBy T b' c :=
  fun w t t' hK hc => hout w t' (standsHere_later (hk t t' hK).1 (hk t t' hK).2 (hin w t hc))

variable (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub}
  {Bs : PureBase} (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat)
  (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site}
  {lot : Block FS ProofFile.Cl} {J : LookJobs Wj} {wit : W → Wj}
include O

/-- **The lookup's member lays it, at either sort**, from the seven facts that the proof uses, one
by one: the site; the lot's sub-protocol at its place; that the thread's member number b stands in
the first chain's flat list, at that place, and passes its test on the plan; and, from the thread's
relation, "the lookup's promise in front holds". Conditional on these, on the description's return,
on `fitsVia` and on `hc`. No instance of these hypotheses is exhibited in this file. -/
theorem lays_stands (hs : s ∈ lookSites Z) (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀)
    (hbs : lot.place = s.at_.place) (hmem : ∀ blk, T.bs[b]? = some blk → blk ∈ ch.blocksInOrder)
    (hpl : ∀ blk, T.bs[b]? = some blk → blk.place = lot.place)
    (hplan : ∀ blk, T.bs[b]? = some blk → blk.planOk = true)
    (hfront : ∀ (k : Coins Bk) (st : FS) (m : Mid W X) (E : Env), Thr T b k st m E →
      VerifiableInference.Desc.K3.k3OnIn s.p st = true)
    (hfv : fitsVia s.p = true) (lm : Nat) (c : RiderCl W FS)
    (hc : ∀ w t, StandsHere s.digits lm s.p.first t → c.prop (b + 1) w t) : LaysAt T b c := by
  intro blk hblk k st m E ds y cols s' hA hd hSt
  exact hc _ _ (stands_member o pol lay KL Fd Z Bs base ch A B O s hs lot blk hb hbs
    (hmem blk hblk) (hpl blk hblk) (hplan blk hblk) T.ft st s' _ _ cols hSt.2 hfv
    (okRounds_moved T hSt.1 hd) (hfront k st m E hA) lm)

/-- **The same from the structure `K3AtSite`**, of which the proof uses seven fields: not its field
on the step behind the head's digits. Conditional on the same hypotheses. -/
theorem lays_of_stands (hS : K3AtSite T b Z Bs ch s lot J wit) (hfv : fitsVia s.p = true)
    (lm : Nat) (c : RiderCl W FS)
    (hc : ∀ w t, StandsHere s.digits lm s.p.first t → c.prop (b + 1) w t) : LaysAt T b c :=
  lays_stands T o pol lay KL Fd base A B O hS.site hS.inLot hS.lotPlace hS.mem hS.place hS.plan
    (fun k st m E hA => (hS.front k st m E hA).1) hfv lm c hc

end

#print axioms ProofFile.Honest.K3.Law.AtThr.standsHere_later
#print axioms ProofFile.Honest.K3.Law.AtThr.standsHere_all
#print axioms ProofFile.Honest.K3.Law.AtThr.stays_of_stands
#print axioms ProofFile.Honest.K3.Law.AtThr.lays_stands
#print axioms ProofFile.Honest.K3.Law.AtThr.lays_of_stands

end ProofFile.Honest.K3.Law.AtThr
