-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TotalFront.lean: THE ITEM "totalB" AT THE BATCHING's MEMBER, CUT INTO NAMED
SENTENCES, ONE OWNER EACH, OVER THE SEALED LIBRARY's OWN LETTERS FOR A RUN OF CLAIMS. DEFINITIONS ALONE: NOTHING IS
PROVED IN THIS FILE, and none of them is one of the library's goals. THE THREAD T IS A VARIABLE.

WHAT THE ITEM SAYS. At the library's meaning (Johnson/Desc/Sound/MgAll.lean, `mgAll_totalB`;
Johnson/Desc/Sound/FormsQ.lean, `totalBQ`), of the state s' behind the batching's step and a witness's tables rd, it
has FOUR conjuncts: the link's runs behind the batching return a state t (`Link.runBehind`) · `totalIn own t` ·
`totalQ own t rd`: the ledger's one equation is worth 0 at t · a test rw on s' (the plan's claims and the ties' and
reads' indices are at most the round's rows). On the honest side it is asked only where a letter `test` says nothing
at s'.
THE ROAD. The library has a law on each run of claims in the description's list (`RunOk`,
Johnson/Desc/First/Batch/Law/Gather.lean, at the letters φ, Ok, Fu, tmOf, lenOf of
Johnson/Desc/First/Link/Law/LinkOwes.lean), and AN EQUATION ON STATES that joins them (`value_at`,
Johnson/Desc/First/Batch/Law/Row3Tools.lean): behind the draw of chi, the gatherer, the adding and the runs behind,
the ledger's one equation at t is the polynomial whose coefficients are the runs' terms, read off WHAT IS FIXED IN
FRONT OF THE DRAW (`fixed9 φ s`), at chi. So the one equation is worth 0 at t wherever every term's coefficient is 0:
a sentence whose conclusion names the state s in front of the draw and the witness's data there, and nothing behind
the draw.
  `SealLaw`   NO DEBT OF ITS OWN: what the library's own laws give at a link, gathered: the link's two orders ·
      `OwesRuns` · `OwesFull` · `LinkShare` · what φ shows of the smallness test's state and the tables · that each
      move keeps the three numbers, and each run of the order by itself (`numRun`). It follows from the library's
      structures (Honest/K9/TotalSeal.lean) and, at the library's own constants, from the library's head with letters
      that sit at the segment (Honest/K9/TotalFill.lean): THAT HEAD STAYS A PREMISE
  `BatStand`   WHAT THE SENTENCES MARKED "at a stand" HAVE IN HAND: the thread in front of the member, with the frame's
      own sentence that every word which the rounds seen show is below the prime (`ThrS T SaidOk`,
      Honest/Thread/Said.lean, SaidOk.lean), the member's step, and what K9 reads off its yes (`BatBehind`,
      Honest/K9/YesAtSeat.lean)
THE SENTENCES; all but `KindOver` and `SeatOver` at a stand:
  `OkFront` K9: what is fixed in front of the draw meets the library's promise Ok
  `TermsBack tm Front`   with Ok in hand, from a letter `Front` on s and the witness: every coefficient of the terms tm,
      at what is fixed at s and the witness's data at s, is 0. ITS CONCLUSION names no state behind the draw, no chi and
      no other run; the stand, which is its premise, does
  `ItemBack o Front`   `TermsBack` at the terms of the entry o of the gatherer's order, Front := what the table's items
      of that entry say: THE REVERSE OF THE LIBRARY's "hitems". ONE FOR EACH ENTRY. Meant: the lookups' house at its
      runs; K9's house at the others; BUT AT THE APPROXIMATE RANGE PROOF's EQUATIONS, whose terms are two lists in a
      row, `TermsBack` at the first (four terms): that proof's house with the lookups; at the second: K9's house; the
      two are joined by `termsBack_append` (Honest/K9/TotalJoin.lean)
  `LensAt w`   K9's house: the runs' numbers, off what is fixed, add up to the plan's
  `CountsFront w`   the house of the approximate range proof: the link's counts behind the adding but the first: AT s
  `RwFront`   K9's house: the item's fourth conjunct, at what is fixed in front
  `KindOver r f Pre`, `SeatOver j r`   THE TRUE CONVERSE OF THE LIBRARY's TIE AT AN ENTRY OF THE ORDER BEHIND, IN TWO
      HALVES: the kind's house: the run r of the kind's own block returns wherever the law's text f returns and Pre
      holds in front · K9's house: the run in the description's list at entry j returns wherever r returns and the reply
      is left. In the two joins r is pinned: it is what the kind's own block lists under the run's name (premises that
      the joins' proofs do not spend)
  `LsLaid`, `K8Behind share` the approximate range proof: its last run returns outside its own share of
      the fall, at every state z that goes on from what is fixed (`Fx9`), is good, has the ledger of s' and has the
      tail's slice laid
  `K4Behind share run4`   at a feed-forward segment: its run behind returns outside its own share
  `TotalInBehind` K9: THE LETTERS
φ, Ok, u, π, tmOf, lenOf, nU MUST BE FILLED ALIKE EVERYWHERE: THE ONE NAMED FILLING FOR EACH SORT OF
SEGMENT IS Honest/K9/TotalFill.lean's. own and rdW: at the library's meaning the segment's group of messages and the
witness's tables by seat (`mgAll_totalB`).
THE JOIN's STATEMENT (`GivesTotalB` from `FrontShares` and the runs behind: `JoinPlain`, `JoinLayers`) is typed here as
two definitions; BOTH ARE PROVED in Honest/K9/TotalAfter.lean (`join_plain`, `join_layers`), over
Honest/K9/TotalJoin.lean and TotalBehind.lean. From `GivesTotalB` to the frame's own form of the debt at the item:
`exchange_totalB_seat` (Honest/K9/TotalExchangeSeat.lean).
WHAT IS NOT CLAIMED. Any of the named sentences at any thread, link or entry. That they can be paid. `SealLaw` at any
link. THAT `GivesTotalB` IS THE ITEM: it is so only where the link Lk is what the head's data list as the segment (so
that the item's runs behind are `Lk.runBehind`), own and rdW are as said above, rw is the data's test at the segment,
and test the honest letters' own: none of these ties is typed in this file. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.YesAll
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk
import Johnson.Desc.First.Link.Law.LinkOwes
import Johnson.Desc.First.Link.Law.GoodFull
import Johnson.Desc.First.Link.Law.RidesAtMg
import Johnson.Desc.First.Batch.Law.RowsRide
import Johnson.Desc.First.Batch.Law.RowsNumber
import Johnson.Desc.First.K8.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

section
variable {α : Type} (sub : First.ModelPart) (l : ℕ) (Lk : Link S Claim) (p : Desc.K9.Where) (φ : S → α)
  (Ok : α × Option K9L.Pub9 → Prop) (nU : Array ℕ) (u : HTailF2)
  (π : α → Option HTailF2 × Option (Array HFun))
  (tmOf : ℕ × String → ℕ → α × Option K9L.Pub9 → K9L.Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
  (lenOf : ℕ × String → α × Option K9L.Pub9 → ℕ)

/-- **The sealed library's own laws at a link, gathered.** -/
structure SealLaw : Prop where
  seg : LinkJoin.SegAt l sub Lk
  runs : LinkJoin.OwesRuns sub Lk φ Ok (LinkJoin.FullAt nU) tmOf lenOf
  full : LinkJoin.OwesFull (α := α) Lk (LinkJoin.FullAt nU) tmOf lenOf
  share : LinkJoin.LinkShare Lk p
  reads : ∀ s : S, π (φ s) = (s.tl?.map (TailClaims.Law.blank u), s.funs?)
  num : ∀ m ∈ LinkJoin.moves₁ Lk (LinkJoin.rlOf Lk tmOf lenOf) ++ LinkJoin.moves₂ (α := α) Lk,
    K9L.MoveNum u m.move
  numRun : ∀ o ∈ Lk.order, ∀ run, LinkJoin.At Lk o run → ∀ n e c e₁, run n e = .ok (c, e₁) →
    K9L.numOf u e₁ = K9L.numOf u e

/-- THE KIND's HALF of the converse of the library's tie: the run r of the kind's own block returns wherever the law's
text f returns and Pre holds in front. -/
def KindOver (r f : S → Except String S) (Pre : S → Prop) : Prop :=
  ∀ e x, f e = .ok x → Pre e → r e = .ok x

/-- THE SEAT's HALF: at entry number j of the order behind a run stands, and it returns wherever the kind's own block's
run r returns and the reply is left. -/
def SeatOver (j : ℕ) (r : S → Except String S) : Prop :=
  ∃ o run, Lk.orderAfter[j]? = some o ∧ LinkJoin.AtAfter Lk o run ∧
    ∀ e x, r e = .ok x → ProofFile.sameReply e x = true → run e = .ok x

/-- The smallness test's state at z is that at s' with the tail's slice of the ledger's coefficients laid. -/
def LsLaid (s' z : S) : Prop :=
  ∃ F tl, s'.fork? = some F ∧ s'.tl? = some tl ∧
    z.tl? = some { tl with lsTail := F.LS.extract tl.slotA tl.slotB }

variable {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Claim V W X Pb) (b : ℕ)

/-- **What the sentences at a stand have in hand.** -/
structure BatStand (κ : Coins Bk) (s : S) (m : Mid W X) (En : Env) (ds : List Fmt.Drawn)
    (y : List Played × Mid W X) (cols : List Desc.OpenedColumn) (s' : S) (x : E) (z : S × Desc.K9.Part × List Claim)
    (G : Fork) : Prop where
  thr : ThrS T SaidOk b κ s m En
  fit : drawsFit (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).rounds ds = true
  step : T.Stepped (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) κ s m En ds y cols s'
  bat : BatBehind p (claimsInBy Lk.each Lk.hear Lk.order) s x z G s'

variable (own : List (ℕ × ℕ)) (rdW : T.Wt → ℕ × ℕ → Sound.MsgQ)

/-- What is fixed in front of the draw meets the library's promise. -/
def OkFront : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G → Ok (K9L.fixed9 φ s)

/-- **Every coefficient of the terms tm, at what is fixed in front and the witness's data in front, is 0.** -/
def TermsBack (tm : ℕ → α × Option K9L.Pub9 → K9L.Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)) (Front : S → T.Wt → Prop) :
    Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
    ∀ a v, Desc.K9.atS.get? s = some a → Ok (K9L.fixed9 φ s) → Front s v →
      ∀ n, ∀ c ∈ tm n (K9L.fixed9 φ s) (Sound.dataQ own a (rdW v)), c.2 = 0

/-- **The reverse of the library's "hitems" at the entry o.** -/
def ItemBack (o : ℕ × String) (Front : S → T.Wt → Prop) : Prop :=
  TermsBack Lk p φ Ok T b own rdW (tmOf o) Front

/-- The runs' numbers, off what is fixed, add up to the plan's. -/
def LensAt (w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere) : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
    Ok (K9L.fixed9 φ s) → K9L.lenRuns (K9L.fixed9 φ s) (LinkJoin.rlOf Lk tmOf lenOf) = w.2.1

/-- The sort's counts behind the adding, but the first: at the state in front. -/
def CountsFront (w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere) : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
    ((Desc.K9.countsAt w.1 w.2.1).tail.all fun q => q.2 s) = true

/-- The item's fourth conjunct, at what is fixed in front. -/
def RwFront : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
    K9L.rowsFit p.rows π (K9L.fixed9 φ s)

/-- The approximate range proof's last run behind the batching returns outside its own share of the fall. -/
def K8Behind (share : S → Option String) : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
    Lk.tests s' = .ok () → share s' = none → ∀ z₂, K9L.Fx9 φ Ok (K9L.fixed9 φ s) z₂ → K9L.good9 z₂ →
      z₂.fork? = s'.fork? → LsLaid s' z₂ → ∃ t, K9L.k8Tests nU z₂ = .ok t

/-- At a feed-forward segment: the run between returns outside its own share. -/
def K4Behind (share : S → Option String) (run4 : S → Except String S) : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
    Lk.tests s' = .ok () → share s' = none → ∀ z₁, K9L.k8LsTail s' = .ok z₁ → ∃ z₂, run4 z₁ = .ok z₂

/-- `totalIn` behind. -/
def TotalInBehind : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
    ∀ t, Lk.runBehind s' = .ok t → Desc.K9.totalIn own t = true

/-- What the sentences are to give: the item's four conjuncts, where the letter test says nothing. -/
def GivesTotalB (rw : S → Bool) (test : S → Option String) (Front : ℕ × String → S → T.Wt → Prop) : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
    ∀ v, (∀ o ∈ Lk.order, Front o s v) → test s' = none →
      Sound.totalBQ Lk.runBehind own s' (rdW v) ∧ rw s' = true

/-- The sentences on the state in front, gathered. -/
structure FrontShares (w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere) (Front : ℕ × String → S → T.Wt → Prop) :
    Prop where
  ready : OkFront Lk p φ Ok T b
  back : ∀ o ∈ Lk.order, ItemBack Lk p φ Ok tmOf T b own rdW o (Front o)
  lens : LensAt Lk p φ Ok tmOf lenOf T b w
  counts : CountsFront Lk p T b w
  rw : RwFront Lk p φ π T b
  totalIn : TotalInBehind Lk p T b own

/-- **THE JOIN's STATEMENT, where two runs stand behind the batching.** Proved: `join_plain`. -/
def JoinPlain : Prop :=
  ∀ (c : Chain S Claim) (Z : ProofFile.Pub) (k : ℕ) (w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere) (rw : S → Bool)
    (test share8 : S → Option String) (rLs rTs : S → Except String S) (pW : First.K8.ParW)
    (Front : ℕ × String → S → T.Wt → Prop),
    SeatedFree c Z l k Lk p w → SealLaw sub l Lk p φ Ok nU u π tmOf lenOf →
    (∀ e, rw e = Desc.K9.rowsFit p.rows e) →
    (∀ e, test e = none → freeSlotShare w.2.2.filled e = none ∧ share8 e = none) →
    FrontShares Lk p φ Ok π tmOf lenOf T b own rdW w Front →
    Lk.orderAfter.length = 2 → pW.nU = nU →
    (First.K8.whole pW).after.lookup "K8.lsTail" = some rLs → (First.K8.whole pW).after.lookup "K8.tests" = some rTs →
    SeatOver Lk 0 rLs → KindOver rLs K9L.k8LsTail (fun e => (S.funs? e).isSome = true) →
    SeatOver Lk 1 rTs → KindOver rTs (K9L.k8Tests nU) (fun e => (S.funs? e).isSome = true) →
    K8Behind Lk p φ Ok nU T b share8 →
    GivesTotalB Lk p T b own rdW rw test Front

/-- **THE JOIN's STATEMENT, at a feed-forward segment: three runs behind.** Proved: `join_layers`. -/
def JoinLayers : Prop :=
  ∀ (c : Chain S Claim) (Z : ProofFile.Pub) (k : ℕ) (w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere) (rw : S → Bool)
    (test share8 share4 : S → Option String) (rLs rTs run4 : S → Except String S)
    (p4 : OnBytes.Desc.First.K4.Par) (pW : First.K8.ParW) (Front : ℕ × String → S → T.Wt → Prop),
    SeatedFree c Z l k Lk p w → SealLaw sub l Lk p φ Ok nU u π tmOf lenOf →
    (∀ e, rw e = Desc.K9.rowsFit p.rows e) →
    (∀ e, test e = none → freeSlotShare w.2.2.filled e = none ∧ share8 e = none ∧ share4 e = none) →
    FrontShares Lk p φ Ok π tmOf lenOf T b own rdW w Front →
    Lk.orderAfter.length = 3 → pW.nU = nU →
    (First.K8.whole pW).after.lookup "K8.lsTail" = some rLs → (First.K8.whole pW).after.lookup "K8.tests" = some rTs →
    SeatOver Lk 0 rLs → KindOver rLs K9L.k8LsTail (fun e => (S.funs? e).isSome = true) →
    (OnBytes.Desc.First.K4.blockAtC p4).after.lookup "free-slot" = some run4 → SeatOver Lk 1 run4 →
    SeatOver Lk 2 rTs → KindOver rTs (K9L.k8Tests nU) (fun e => (S.funs? e).isSome = true) →
    K8Behind Lk p φ Ok nU T b share8 → K4Behind Lk p T b share4 run4 →
    GivesTotalB Lk p T b own rdW rw test Front

end

end ProofFile.Honest.K9
