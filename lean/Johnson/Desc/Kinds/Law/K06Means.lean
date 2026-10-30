-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
This file stands over Block.lean and State.lean, and over the seats that go with
them (Stored/HeadSeatAt.lean, Stored/ReplySeatAt.lean). k06_whole: K6On has six
clauses (Law/RowPins.lean).
Johnson/Desc/Kinds/Law/K06Means.lean: THE ROW "K06_means" OF THE LIST OF WHAT IS OWED (a wording of it: "the head's identities, and its rider": at this kind's seat the relation that the kind's law concludes in front gives the integer model's clause for that segment): AS TWO CLOSED STATEMENTS AT THE PUBLIC FILES W AND A RECORD s, IN THE VERY TERMS OF HeadR0 (Johnson/Road/Lane5SplitH.lean): STATED AND PROVED.
  K06MeansIdn     what K6's law closes at a record in front (Law/RowPins.lean: K6In; of it the part "idn") ⇒ THE 17 IDENTITIES OF THE FINAL NORMALISATION AT EVERY POSITION AND THE LEDGER's TWO SUMS (B2), (B3), over the base field, at Hd.npOf W.hS | Req.of (polOf W.hS) x, at the library's record made of the cells (cellsN c).
  RiderAt W s y c the rider's item in this kind's words: Law/K06Statement.lean's CornerGuests (at every position the two guests' corner values, the clip's line and the table's line, are 0), NO SECOND TEXT OF IT: at the seat's letters and the heard token y: the very sentence in which the head's caller ends its guests' half (Desc/First/Look/K3CallerHead.lean: head_guests). (The table's item "constr 4 rider": the lookup's block closes it; the words are this kind's.)
  K06MeansRider   RiderAt ⇒ THE LEDGER's TWO LINES (B4), (Z) AT EVERY POSITION, in the same terms.
  k06_means_idn · k06_means_rider · k06_means
  k06_whole       THE ASSEMBLY AT ONE RECORD: K6On W s · K6In W s (c, mask) (of it "idn") · the heard token y · Law/ReplyPins.lean's LookCallsAt W tab s y c (the item "lookCalls": K7's and the lookup's rows) · RiderAt W s y c · small (the smallness test's) ⇒ Policy.HeadCl (Hd.npOf W.hS) (polOf W.hS) Wz x (cellsN c): the nine families' keys, the 17, the two lines, the two sums: by
                  Law/LibLetters.lean's headCl_at. Its further premises: W.hS.digSh = 8 · THE RECORD IS THE INSTANCE's (the two positions; the tokens; y) · tab is the library's EX on 16 bits · c.Wh is the output matrix in Wz.
They are Law/LibAtSeat.lean's front_to_lib and Law/LibRider.lean's lib_lines at W's letters; the arithmetic beneath is in Law/LibJoin.lean | LibJoinNorm.lean (ported whole).
WHAT IT DOES NOT SAY. **PREMISES**: FullH W.hS (the full size alone) · **THE RECORD's TWO POSITIONS ARE THE INSTANCE's** (s.rowR = x.r, s.rowE = x.e: the frame's tie: typed by nobody) · for the rider: the tests on the plan pass. K6In is what K6's law closes UNDER ITS OWN PREMISES (Law/RowPins.lean, Law/K6Own.lean). RiderAt IS NOT WHAT K6's LAW CLOSES (that is one sum at the lookup's point: FrontRider): it
is the lookup's rider's law's conclusion. THAT cellsN c IS WHAT THE COMMITTED INTEGERS OF SEGMENT 24 SPELL (Hd.cellsH … (own 24) = cellsN c) IS NOT HERE: without it these are clauses on our letter c. The keys (K03's and K07's rows; Law/LibLetters.lean's headCl_at has all four parts together) · SmallH · "y = 0 if e < T": not here. One way alone. No chance in it.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.LibLetters
import Johnson.Desc.Kinds.Law.LibRider
import Johnson.Desc.Kinds.Law.ReplyPins

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open Inst.Model (ppref Instance)
open Inst.Model.Head (Req nT sB2 sB3 dB4 dZ)
open OnBytes.Road.Hd (FullH)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.HeadJoin (cellsN)
open Norm (lt ls d lPd S2 T)

/-- **K06_means, the identities.** -/
def K06MeansIdn : Prop :=
  ∀ (W : OnBytes.Model.Verify.Public) (s : S) (x : Instance ppref) (dd : Pinned),
    FullH W.hS → s.rowR = x.r → s.rowE = x.e → K6In W s dd →
    (∀ i < nT, ∀ k < 17,
      Inst.Model.Head.N.idn (OnBytes.Road.Hd.npOf W.hS) ((cellsN dd.1).cast Cb.Gl.F) i k = 0) ∧
      (sB2 ((cellsN dd.1).cast Cb.Gl.F) (Req.of (OnBytes.Road.Hd.polOf W.hS) x) = 0 ∧
        sB3 ((cellsN dd.1).cast Cb.Gl.F) (Req.of (OnBytes.Road.Hd.polOf W.hS) x) = 0)

/-- The rider's item, in this kind's words: Law/K06Statement.lean's CornerGuests (at every position the two guests' corner values are 0), at the seat's letters and a token y. -/
def RiderAt (W : OnBytes.Model.Verify.Public) (s : S) (y : Nat) (c : NCells) : Prop :=
  let _ : Sizes := sizesOf W.hS
  let _ : Policy := (parOf W.hS (workOf W)).policy
  let _ : Request := requestOf s
  let _ : Token := ⟨y⟩
  CornerGuests c.toCells

/-- **K06_means, the rider.** -/
def K06MeansRider : Prop :=
  ∀ (W : OnBytes.Model.Verify.Public) (s : S) (y : Nat) (x : Instance ppref) (c : NCells),
    FullH W.hS → s.rowR = x.r → s.rowE = x.e → (parOf W.hS (workOf W)).ok = true →
    RiderAt W s y c →
    ∀ i < nT, dB4 ((cellsN c).cast Cb.Gl.F) (Req.of (OnBytes.Road.Hd.polOf W.hS) x) i = 0 ∧
      dZ ((cellsN c).cast Cb.Gl.F) (Req.of (OnBytes.Road.Hd.polOf W.hS) x) i = 0

namespace Came

theorem k06_means_idn : K06MeansIdn := fun W s x dd hF hr he hin =>
  front_to_lib W.hS (readsOf W) (workOf W) s x hF hr he dd.1 hin.1

theorem k06_means_rider : K06MeansRider := fun W s y x c hF hr he hplan hR => by
  letI : Sizes := sizesOf W.hS
  letI : Policy := (parOf W.hS (workOf W)).policy
  letI : Request := requestOf s
  letI : Token := ⟨y⟩
  have P : PlanFacts := planFacts (sT := W.hS.tabS) hplan
  exact lib_lines (same_at W.hS (workOf W) s x hF hr he) (wide_at W.hS hF P.hF) P hR

/-- **K06_means.** -/
theorem k06_means : K06MeansIdn ∧ K06MeansRider := ⟨k06_means_idn, k06_means_rider⟩

/-- **THE ASSEMBLY AT ONE RECORD**: what K6's law asks in front and closes, with the three other items at the same record, token and cells, gives HeadCl. -/
theorem k06_whole (W : OnBytes.Model.Verify.Public) (s : S) (y : Nat) (x : Instance ppref)
    (Wz : Inst.Model.Mat) (tab : Nat → Nat) (dd : Pinned) (hon : K6On W s) (hin : K6In W s dd)
    (hy : Reply.token (seatAt W.hS (readsOf W)).toSeat s = some y)
    (hlook : LookCallsAt W tab s y dd.1) (hrider : RiderAt W s y dd.1)
    (hsmall : ∀ m f t, (dd.1.cell m f t).natAbs < 2 ^ 18)
    (hsmallS : ∀ f t, (dd.1.stream f t).natAbs < 2 ^ 18) (hF : FullH W.hS)
    (h8 : W.hS.digSh = 8) (hr : s.rowR = x.r) (he : s.rowE = x.e)
    (htok : ∀ t, t < 1024 → s.tokv.getD t 0 = x.tok t) (hyx : y = x.y.val)
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u)
    (hW : dd.1.Wh = (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H) :
    _root_.Policy.HeadCl (OnBytes.Road.Hd.npOf W.hS) (OnBytes.Road.Hd.polOf W.hS) Wz x
      (cellsN dd.1) := by
  obtain ⟨_, hplan, _, hreq, hyV, _⟩ := hon
  obtain ⟨g, hg, hrows, hm, hc⟩ := hin.1
  obtain ⟨z, y', _, hy', _, rfl⟩ := given_ok _ _ _ _ hg
  have e : y' = y := Option.some.inj (hy'.symm.trans hy)
  subst e
  exact headCl_at W.hS (workOf W) s y' x Wz (parOf W.hS 0).floor tab dd.1 hF h8 hr he htok hyx
    hplan hreq (hyV y' hy) htab hW
    (@HeadParts.mk (sizesOf W.hS) (parOf W.hS (workOf W)).policy (requestOf s) ⟨y'⟩ _ _ _ ⟨hm, hc⟩
      hrows hlook hrider hsmall hsmallS)

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k06_means
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k06_whole
