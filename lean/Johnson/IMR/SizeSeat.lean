-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/SizeSeat.lean: "EVERY ORACLE MESSAGE OF THE STATEMENT HAS A PLACE IN
THE BOOK, AND NO PLACE MORE" (s.book.place.size = s.st.oracles.size) AT EVERY RECORD IN FRONT OF THE
BLOCKS BEHIND THE LAST LINK, AT THE PROOF FILE's SEAT.

THE RELATION: HR := ByC HasC coreS, HasC a b := (a.book.place.size = a.st.oracles.size →
  b.book.place.size = b.st.oracles.size).
WHO PAYS:
  whoever sends nothing leaves both numbers: Johnson/Goal/Meaning/SizeSeated.lean, over the plain
    ground's coreStill_size (Johnson/Desc/CoreKeepsSize.lean).
  the plain ground's receiving raises both by the number of messages sent: has_recv:
    Book.recvP_seat's clause "count" (Johnson/Desc/Book/BookFitsGround.lean) and
    K1.recvP_received's third clause
    (Johnson/Desc/Sound/FenceSendGround.lean): so coreRecv_has, and K1's two blocks by the library's
    walk over the three (through Johnson/Goal/Meaning/CoreSeated.lean).
  KIND K2's FIVE: structure K2Has, PAID BY ITS FILES' LAWS, CALLED: k2Has: K2.yes_has (behind a yes
    of the switch the two numbers are one, whatever stood in front) and the four "...Q_size"
    (Johnson/Top/H0/Tw/K2C/StillKeeps.lean), with the four "...Q_book" (BookKept.lean beside it).
  the start: no message and no place: start_has.
TOPS: seatKeeps_has, k2Has, descPure_hasFront: NO PREMISE BUT onlineDescription's RETURN.
OBJECT: ProofFile.onlineDescription's value, at every o. USER: whoever shows the row on the book's names.
No soundness.
-/
import Johnson.IMR.FrontCut
import Johnson.Goal.Meaning.SizeSeated
import Johnson.Desc.Sound.FenceSendGround
import Johnson.Top.H0.Tw.K2C.StillKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground (Core coreOf ByC CoreStill CoreRecv coreStill_three)
open VerifiableInference.Desc.K1.RelCore (coreS)
open ProofFile (Pub)

/-- If the book has as many places as the statement has oracle messages in front, so behind. -/
def HasC (a b : Core) : Prop :=
  a.book.place.size = a.st.oracles.size → b.book.place.size = b.st.oracles.size

/-- **The relation.** -/
abbrev HR : S → S → Prop := ByC HasC coreS

theorem has_three (a b : Core) (h1 : b.st.oracles.size = a.st.oracles.size)
    (h2 : b.book = a.book) (_ : b.roots = a.roots) : HasC a b := fun h => by
  rw [h2, h1]
  exact h

theorem has_trans {a b c : Core} (h : HasC a b) (k : HasC b c) : HasC a c := fun x => k (h x)

theorem has_recv {L : Type} (ft : Nat) (d d' : _root_.Desc.Plain.DState L)
    (sent : Array OracleNotice) (ids : Array Nat) (h : Ground.recvP ft d sent = some (ids, d')) :
    HasC (coreOf d) (coreOf d') := fun k => by
  obtain ⟨-, lay, -, S⟩ := Book.recvP_seat ft d d' sent ids h
  obtain ⟨lay', -, -, e, -⟩ := K1.recvP_received ft d d' sent ids h
  show d'.book.place.size = d'.st.oracles.size
  rw [S.count, e]
  exact congrArg (· + sent.size) k

theorem coreRecv_has : CoreRecv 0 HasC where
  refl := fun _ => id
  trans := fun h k => has_trans h k
  newGroup := fun d d' c m n h => let k := coreStill_three.newGroup d d' c m n h
    has_three _ _ k.1 k.2.1 k.2.2
  admit := fun d d' o r h => let k := coreStill_three.admit d d' o r h
    has_three _ _ k.1 k.2.1 k.2.2
  join := fun d d' g o x h => let k := coreStill_three.join d d' g o x h
    has_three _ _ k.1 k.2.1 k.2.2
  addRow := fun d d' g r h => let k := coreStill_three.addRow d d' g r h
    has_three _ _ k.1 k.2.1 k.2.2
  takeMask := fun d d' o n h => let k := coreStill_three.takeMask d d' o n h
    has_three _ _ k.1 k.2.1 k.2.2
  closeLedger := fun d d' o h => let k := coreStill_three.closeLedger d d' o h
    has_three _ _ k.1 k.2.1 k.2.2
  spendAsMask := fun d d' o h => let k := coreStill_three.spendAsMask d d' o h
    has_three _ _ k.1 k.2.1 k.2.2
  elsewhere := fun d d' m o t h => let k := coreStill_three.elsewhere d d' m o t h
    has_three _ _ k.1 k.2.1 k.2.2
  recv := fun d d' sent ids h => has_recv 0 d d' sent ids h

/-- **KIND K2's SHARE, NAMED.** -/
structure K2Has : Prop where
  k2 : ∀ p : K2.P2, p.firstTree = 0 → Whole HR (K2.codeSwitchKind p : Block S Unit)
  front : ∀ tl : HTailF2, Fn HR (K2.headFrontQ tl)
  openQ : ∀ P : K2.HeadPar, Fn HR (K2.headOpenQ P)
  finFront : Fn HR K2.finishFrontQ
  finBehind : Fn HR K2.finishBehindQ

theorem k2Has : K2Has where
  k2 := fun _ _ => ⟨fun _ _ _ _ h _ => K2.yes_has h, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩
  front := fun _ _ _ h =>
    has_three _ _ (K2.headFrontQ_size h) (K2.headFrontQ_book h).1 (K2.headFrontQ_book h).2
  openQ := fun _ _ _ h =>
    has_three _ _ (K2.headOpenQ_size h) (K2.headOpenQ_book h).1 (K2.headOpenQ_book h).2
  finFront := fun _ _ h =>
    has_three _ _ (K2.finishFrontQ_size h) (K2.finishFrontQ_book h).1 (K2.finishFrontQ_book h).2
  finBehind := fun _ _ h =>
    has_three _ _ (K2.finishBehindQ_size h) (K2.finishBehindQ_book h).1
      (K2.finishBehindQ_book h).2

theorem seatKeeps_has (H : K2Has) : SeatKeeps HR where
  refl := fun _ => id
  trans := fun _ _ _ h k => has_trans h k
  frames := fun _ h => framesOf_three has_three h
  k1First := fun q gp h0 => firstAtS_core coreRecv_has q gp h0
  k1Later := fun q gp l p m a h0 => laterAt_core coreRecv_has q gp l p m a h0
  reads := fun h => whole_three has_three (readsQuietAt_quiet h)
  k3 := fun c r X cs sh a _ h => whole_three has_three (theStated_quiet c r X cs sh a h)
  k4 := fun p => whole_three has_three (blockAtC_quiet p)
  k5 := fun W l g bf _ h => whole_three has_three (k5AtN_quiet W l g bf h)
  k6 := fun h => whole_three has_three (seatedClaims_quiet h)
  k7 := fun W l => whole_three has_three (k7Of_quiet W l)
  k8 := fun p => whole_three has_three (k8Whole_quiet p)
  closeOf := closeOf_three has_three
  batch := fun p _ hcl => batch_three has_three has_trans p hcl
  k11 := fun Q => whole_three has_three (headMerge11_quiet Q)
  k2 := H.k2
  front := H.front
  openQ := fun Q _ => H.openQ Q
  finFront := H.finFront
  finBehind := H.finBehind

/-- **The first record: no oracle message, at every request.** -/
theorem start_none {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (p : ProofFile.InstPub) :
    (ProofFile.startS Z p).st.oracles.size = 0 := by
  have e : Z.s₀.st.oracles.size = 0 := by
    have k := pub_start h
    unfold S.startP at k
    split at k
    · rw [← Option.some.inj k]
      rfl
    · cases k
  unfold ProofFile.startS
  dsimp only
  split
  · exact e
  · rfl

/-- **AS MANY PLACES AS ORACLE MESSAGES, AT EVERY RECORD IN FRONT OF THE BLOCKS BEHIND THE LAST
LINK.** -/
theorem descPure_hasFront {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : FileDescription ProofFile.Inst} (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      c.blocksInOrder = frontOf c ++ backOf c ∧
      ∀ (p : ProofFile.InstPub) (l₁ l₂ : List (Block S ProofFile.Cl)), frontOf c = l₁ ++ l₂ →
        ∀ (ft : Nat) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn)
          (r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn),
          foldBlocks ft l₁ (ProofFile.startS Z p) rs cols = .ok r →
          r.1.book.place.size = r.1.st.oracles.size := by
  obtain ⟨Z, A, B, c, hZ, e, hf, k⟩ := descPure_stretch (seatKeeps_has k2Has)
    (fun _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial) h
  refine ⟨Z, A, B, c, hZ, e, hf, fun p l₁ l₂ hl ft rs cols r hr => ?_⟩
  refine k [] l₁ l₂ (by rw [hl]; rfl) ft _ rs cols r hr ?_
  show (ProofFile.startS Z p).book.place.size = (ProofFile.startS Z p).st.oracles.size
  rw [(start_empty hZ p).1, start_none hZ p]
  rfl

#print axioms coreRecv_has
#print axioms seatKeeps_has
#print axioms k2Has
#print axioms start_none
#print axioms descPure_hasFront

end Meaning.K2
