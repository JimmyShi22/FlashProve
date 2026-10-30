-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ClaimOfLock.lean: the kind "the code switch" (K2): TOWARD THE
FIELD claim OF `MadeAsks` (ExchangeAtMade.lean of this folder): FROM THE THREAD's OPEN ITEM "carry"
AND THE LOCK (`LockedAt`, LockAtFront.lean of this folder) TO `ClaimTrue` AT WHAT THE LOT's CLOSING
RETURNS. A JOIN: calls alone. One definition: a premise's form; statements with their proofs. THE
SEAM THAT IS LEFT, FIRST: THE END STANDS AT THE FRONT fx THAT THE CARRY's SENTENCE NAMES: what
`frontAt` takes at `ProofFile.pAtK2 Zp (p.link - 1)` off t, t what `doorZ`
(Johnson/Top/H0/K2Caller/CarryClosed.lean) hands on: at a link's place `rest s`, not s. THE FIELD's
x IS `AtYes`' FRONT: at `IM.k2P Zp p.place nm st n`, off the state behind the place's step in front.
THAT THE TWO FRONTS ARE ONE IS NOT SAID HERE: SO THIS IS NOT YET THE FIELD.

  `LockAsks`        THE LOCK's TWO "IF", AS ONE NAMED PREMISE, to the sign of `LockedAt`'s own text,
                    at the written segment m and every return of the walk in front: the challenges
                    heard at the segment's numbers are the carried rows' · at whatever rows
                    `segmentGroupRows` makes there: each member's main entries, each member's mask
                    entries and the entries of the mask sent ahead are the words'
  `claim_of_locked`   the lock · its two "if" · the claim at `leftAt` of the words ⊢ the claim at
                    what the walk handed on
  `claim_at_closing`  the same at what the lot's closing returns at the written segments
  `head_mg_carry`   at the first chain's letters at the library's head the item "carry" means the
                    letter carryX: by unfolding
  `carry_of_thr`    at the first chain's letters at the library's head, at the exact carry: where
                    the thread's invariant holds in front of a written switch, and the way in and
                    the front are known: the claim at `leftAt` of the Script's witness's words
  `claim_at_head`   THE END: the four joined, at a statement with the front's sizes

By: `lotClosingAt_kept` (HonestAtClosing.lean) · `k2_carry_at` (ExchangeByKind.lean), both of this
folder · `carryExact_iff` (Johnson/Desc/K2/Honest/Carry/Exact.lean).

Limits. AN IMPLICATION. LEFT AS PREMISES: hLk: the lock at the walk's return (`link_lockedAt` and
its two like have it under "reached") · hA: `LockAsks`: whole, all four limbs, it is gathered at the
23 link places (`link_lockAsks`, `first_lockAsks`, LockAsksAtLink.lean) and at the two arms
(`head_lockAsks`, `fin_lockAsks`, LockAsksAtArms.lean), each under premises of its own, which are
proved in these two files of no Script, book or filling; at a step of the thread, from two records:
`lockAsks_of_step` (LockAsksAtStep.lean); in the side library, each under premises of its own: eight
of the second record's thirteen fields at the joined Script (`opener_at_join`,
AtFullSide/K2/OpenerAtJoin.lean), `SharedAsks` at a job of a fit list (`shared_at_job`,
AtFullSide/K2/LaterAsks.lean), `MaskAsks` (`mask_at_job`, AtFullSide/K2/FirstSenders.lean). That all
of these are met together is not shown in these files. Limb by limb: the challenges
(GammaAtFront.lean), the members' entries (MembersAtLink.lean), the entries of the mask sent ahead
(FreshClause.lean, FreshClauseArms.lean, FreshClauseFirst.lean) · hd, hf: the way in and
the front · hl: the place's link is not 0: public · hsz: the sizes read off the statement behind the
joins are those read off the front's · the thread's invariant · the closing's return. One run's
coins: never quoted for a law. NOT IN FRONT OF A LAW OVER COINS. The full size; the
format's second hash function. The line that takes the instance `Inst.Model.Scl.ref` out of reach is
LockAtFront.lean's own, and the library's. Nothing on tails. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.LockAtFront
import Johnson.Desc.ProofFile.Honest.K2.Law.HonestAtClosing
import Johnson.Desc.ProofFile.Honest.K2.Law.ExchangeByKind
import Johnson.Desc.K2.Honest.Carry.Exact

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open OnBytes
open OnBytes.Slice (GE readE)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Chain Strs)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2Caller (doorZ)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K2.Honest (Left ClaimTrue sizesAt leftAt carryExact carryExact_iff)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script lettersHead)

/-- **THE LOCK's TWO "IF", AS ONE NAMED PREMISE.** A definition: the form of a premise. Nothing here
proves that it can be met. One run's coins: never quoted for a law. -/
def LockAsks (table : FreshTable) (own : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (heard : List Fmt.Drawn) (k : Nat → Except String Stretch) (m : Nat)
    (fx : _root_.Tw.K2.Front) (w : Words GE) : Prop :=
  ∀ (Sg : SegmentPub) (y' : Option (Left × List OracleShape) × Nat),
    segsW[m]? = some Sg → closingFrom table own heard k (segsW.take m) 0 0 none = .ok y' →
      challengesOr0 heard Sg.gamma = fx.f.rows.gamma.map readE ∧
      (∀ R, segmentGroupRows table Sg (y'.1.map (·.1)) ((y'.1.map (·.2)).getD []) (own (0 + m)) k y'.2
          true = .ok R →
        (∀ i b j, i < fx.f.rows.layout.members.size →
          b < (fx.st.oracles.getD (fx.f.rows.layout.members.getD i noId) default).shape.mainRows →
          (R.rows.getD i zeroMessage).main
              ((fx.st.oracles.getD (fx.f.rows.layout.members.getD i noId) default).shape.mainDeg
                == 3) b j =
            w (fx.f.rows.layout.members.getD i noId) .main (b + j * 2 ^ ceilLog2
              (fx.st.oracles.getD (fx.f.rows.layout.members.getD i noId)
                default).shape.mainRows)) ∧
        (∀ i b j, i < fx.f.rows.layout.members.size →
          b < (fx.st.oracles.getD (fx.f.rows.layout.members.getD i noId) default).shape.maskRows →
          (R.rows.getD i zeroMessage).mask b j =
            w (fx.f.rows.layout.members.getD i noId) .mask (b + j * 2 ^ ceilLog2
              (fx.st.oracles.getD (fx.f.rows.layout.members.getD i noId)
                default).shape.maskRows)) ∧
        ∀ b j, b < 2 ^ fx.f.rows.layout.h →
          (R.fresh.getD zeroMessage).mask b j = w fx.f.rows.fresh .mask
            (b + j * 2 ^ ceilLog2 (fx.st.oracles.getD fx.f.rows.fresh default).shape.maskRows))

/-- The lock, its two "if", and the claim at the words. -/
theorem claim_of_locked {table : FreshTable} {own : Nat → Nat → Nat → Nat → Cb.Gl.E}
    {heard : List Fmt.Drawn} {k : Nat → Except String Stretch} {m : Nat}
    {y : Option (Left × List OracleShape) × Nat} {fx : _root_.Tw.K2.Front}
    (hLk : LockedAt table own heard k m y fx) {W : Left} {kept : List OracleShape}
    (hy : y.1 = some (W, kept)) (T : SwitchTarget) {w : Words GE}
    (hA : LockAsks table own heard k m fx w)
    (hc : ClaimTrue (sizesAt fx.st fx.f.rows T) fx.f.rows (leftAt fx.st fx.f.rows w)) :
    ClaimTrue (sizesAt fx.st fx.f.rows T) fx.f.rows W := by
  obtain ⟨Sg, y', W', kept', hS, hy', hyW, -, hiff⟩ := hLk
  have e : (W', kept') = (W, kept) := Option.some.inj (hyW.symm.trans hy)
  obtain rfl : W' = W := congrArg Prod.fst e
  obtain ⟨hg, hE⟩ := hA Sg y' hS hy'
  exact (hiff T w hg hE).1 hc

/-- The same at what the lot's closing returns at the written segments. -/
theorem claim_at_closing {lay : OnBytes.Params.ReqLayout} {p : SwitchPlace} {D : RowData}
    {Rd : Readers} {heard : List Fmt.Drawn} {k : Nat → Except String Stretch} {Wl : Left}
    (hW : lotClosingAt lay segsW p D Rd heard k = .ok Wl) {m : Nat} (hl : p.link = m + 1)
    {fx : _root_.Tw.K2.Front}
    (hLk : ∀ y, closingFrom freshTable (lotOwn segsW p D Rd heard) heard k (segsW.take (m + 1)) 0 0
      none = .ok y → LockedAt freshTable (lotOwn segsW p D Rd heard) heard k m y fx)
    (T : SwitchTarget) {w : Words GE}
    (hA : LockAsks freshTable (lotOwn segsW p D Rd heard) heard k m fx w)
    (hc : ClaimTrue (sizesAt fx.st fx.f.rows T) fx.f.rows (leftAt fx.st fx.f.rows w)) :
    ClaimTrue (sizesAt fx.st fx.f.rows T) fx.f.rows Wl := by
  obtain ⟨x, hx, ex⟩ := lotClosingAt_kept hW
  rw [hl] at hx
  exact claim_of_locked (hLk x hx) ex T hA hc

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- At these letters the item "carry" means the letter carryX. -/
theorem head_mg_carry (carryX : Nat → ProofFile.InstPub × TS → Strs → ProofFile.Honest.FirstThread.WtF → Prop)
    (v : Local W₀ Rc ProofFile.Inst Tr) :
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mg v).carry = carryX := rfl

/-- hT, hd AND hf ARE PREMISES. **THE OPEN ITEM "carry" IN FRONT OF A WRITTEN SWITCH**, at every
continuation ds of the challenges heard. One run's coins: never quoted for a law. -/
theorem carry_of_thr {p : SwitchPlace} (hp : p ∈ placesW) {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w).thread (switchNo p) k s m E)
    {t : TS} {fx : _root_.Tw.K2.Front} (hd : doorZ Zp (p.link - 1) s = some t)
    (hf : VerifiableInference.Desc.First.K2.frontAt (ProofFile.pAtK2 Zp (p.link - 1)) t = some fx)
    (ds : List Fmt.Drawn) :
    ClaimTrue (sizesAt fx.st fx.f.rows fx.T) fx.f.rows
      (leftAt fx.st fx.f.rows (VerifiableInference.Desc.Sound.wordsFirst (P5J.At.arr Zp) fx.st
        t.book (Q.wit k m.st.input (m.st.heard ++ ds)))) := by
  have hI : ((lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp w).mg
      m.st.input).carry (p.link - 1)
      ((lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
        w).thread.seat k m s)
      ((lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
        w).thread.strs E) (Q.wit k m.st.input (m.st.heard ++ ds)) :=
    hT.2.2.2.1 ds (VerifiableInference.Desc.First.Item.carry (p.link - 1)) (k2_carry_at hp)
  rw [head_mg_carry] at hI
  exact (carryExact_iff Zp (P5J.At.arr Zp) (p.link - 1) _ _ _ hd hf).1 hI

/-- ALL BUT hp ARE PREMISES. **THE TEXT OF THE FIELD claim, AT THE CARRY's OWN FRONT fx, FROM THE
THREAD's OPEN ITEM AND THE LOCK.** That fx is the front at the kind's yes is not said. One run's
coins: never quoted for a law. NOT IN FRONT OF A LAW OVER COINS. -/
theorem claim_at_head {p : SwitchPlace} (hp : p ∈ placesW) {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w).thread (switchNo p) k s m E)
    {t : TS} {fx : _root_.Tw.K2.Front} (hd : doorZ Zp (p.link - 1) s = some t)
    (hf : VerifiableInference.Desc.First.K2.frontAt (ProofFile.pAtK2 Zp (p.link - 1)) t = some fx)
    (ds : List Fmt.Drawn) {lay : OnBytes.Params.ReqLayout} {D : RowData} {Rr : Readers}
    {heard : List Fmt.Drawn} {kk : Nat → Except String Stretch} {Wl : Left}
    (hW : lotClosingAt lay segsW p D Rr heard kk = .ok Wl) (hl : p.link = (p.link - 1) + 1)
    (hLk : ∀ y, closingFrom freshTable (lotOwn segsW p D Rr heard) heard kk
      (segsW.take ((p.link - 1) + 1)) 0 0 none = .ok y →
      LockedAt freshTable (lotOwn segsW p D Rr heard) heard kk (p.link - 1) y fx)
    (hA : LockAsks freshTable (lotOwn segsW p D Rr heard) heard kk (p.link - 1) fx
      (VerifiableInference.Desc.Sound.wordsFirst (P5J.At.arr Zp) fx.st t.book
        (Q.wit k m.st.input (m.st.heard ++ ds))))
    {S3 : Statement} (hsz : sizesAt S3 fx.f.rows fx.T = sizesAt fx.st fx.f.rows fx.T) :
    ClaimTrue (sizesAt S3 fx.f.rows fx.T) fx.f.rows Wl := by
  rw [hsz]
  exact claim_at_closing hW hl hLk fx.T hA
    (carry_of_thr h H Q test item n₁ n₂ b₀ Vd Rd Kp w hp hT hd hf ds)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.LockAsks
#print axioms ProofFile.Honest.K2.Law.claim_of_locked
#print axioms ProofFile.Honest.K2.Law.claim_at_closing
#print axioms ProofFile.Honest.K2.Law.head_mg_carry
#print axioms ProofFile.Honest.K2.Law.carry_of_thr
#print axioms ProofFile.Honest.K2.Law.claim_at_head
