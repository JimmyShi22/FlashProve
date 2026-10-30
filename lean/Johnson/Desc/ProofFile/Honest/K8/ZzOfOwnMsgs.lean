-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/ZzOfOwnMsgs.lean: the honest side of the smallness test (K8): THE
SENTENCE `ZzBy` (Johnson/Desc/ProofFile/Honest/K8/SmallLaw.lean) AT THE LAW's ONE TABLE OF CELLS
(`cellsAhead`, Johnson/Desc/First/K8/CellsAhead.lean) OVER A SCRIPT's WITNESS, FROM ONE PREMISE ON
THE SCRIPT (hm: `OwnMsgs`, Johnson/Desc/ProofFile/Honest/Thread/ScriptLots.lean) AND NAMED PREMISES.
One statement with its proof; no definition. A JOINING OF FIVE LAWS. NO THREAD, NO STEP.

UNDER hm, PROVED OF NO SCRIPT. IT NAMES THE SCRIPT's WITNESS AND, THROUGH THE LETTER wit, WHAT A
READER YIELDS OF THE INPUT. The run's coins k stand inside `Q.wit`; the part's own cut c is a bound
letter with hc in front; the cells on the right are no coins. No measure; no stop. An equation on
the Script. NOT IN FRONT OF A LAW OVER COINS. At the digits' message's first
sending alone: of a copy that a later member keeps or sends again nothing is said.

  **`zzBy_of_ownMsgs`**
THE FIVE: `zzBy_of_zzOf` (Johnson/Desc/ProofFile/Honest/K8/DrawBridgeProofs.lean) ·
`laidBack_covers` (of other authors; it comes with
Johnson/Desc/ProofFile/Honest/K5/Law/WayBackFill.lean and what that imports): every element inside
the array's sizes is laid · `cellsAhead_is_entry` (Johnson/Desc/ProofFile/Honest/K8/AheadEntry.lean)
· `seatTab_of_mem` (Johnson/Desc/Sound/SeatTabMsgs.lean) · `tab_is_zz`
(Johnson/Desc/ProofFile/Honest/K8/TabIsZz.lean).
THE PREMISES, SORTED. ON THE SCRIPT: hm, with htxt (the text answers, at each place at which the
layout lays an element of the array, what the sending's own text answers there). ON THE PROVER's
TEXT: hJ (which job J is). ON THE RUN's COINS: hc. ON THE INPUT: hw. ON THE CHALLENGES: hN, hdr. ON
THE VERIFIER's STATE s', AND ON A RECORD tl' (a letter: that it is the record of s' is asked nowhere
here), AGAINST THE PLAN: hp, hx, hA, hok, hy, hpar, hmz, and hcf (that record's drawn matrix is tr:
so on the challenges too). ON PUBLIC DATA: all others. THE END STANDS IN THIS SIDE's OWN FORMS: the
list is `K3.matsOwn G.W l`, the cells are `(wit w).R.cells`: WHAT A READER YIELDS OF THE INPUT: NOT
PUBLIC. OF THE SIX PAIRS OF FORMS THAT TabIsZz.lean's LIMITS LIST, NONE IS PROVED ONE HERE. TWO STAY
AS THEY ARE, IN THE END: that list against `matsOf`; these cells against what other laws read off
the input's trace. THREE ARE PUSHED INTO PREMISES THAT BIND tl', EACH PROVED NOWHERE HERE: hpar: the
plan's record tl₀ and tl' give one `Par` (`parOfTail`, Johnson/Desc/ProofFile/Honest/K8/Digits.lean,
reads the matrices' two sizes and tau: not the drawn matrix) · hcf · hmz: the column's bound. THE
SIXTH, `zzOf` AGAINST WHAT THE SECOND STOP ASKS, IS NOT TOUCHED. BESIDES: hsI, hsC (the array is as
large as the plan's record says) · hAa (the array that is ahead is the ground's layout's) · hcs, hsh
(the codes and the shape at the member are the job's).
NO OPTION IS RAISED, NO INSTANCE TAKEN AWAY. NO TACTIC THAT SEARCHES.
Limits. AN IMPLICATION. NO LETTERS ARE GIVEN AT WHICH THE PREMISES HOLD TOGETHER. IT IS COUNTED
NOWHERE. `K8TwoAt.zz` (Johnson/Desc/ProofFile/Honest/K8/ExchangeByKind.lean) STAYS A PREMISE: it
asks this end at every state of a thread behind the draw; here hd, s', tl' are letters. WHERE
tl'.tau = 0 (by hpar: tl₀.tau = 0) OR tl'.mz = 0 THE END RANGES OVER NO (u, col): it holds then of
every table. At a short book all is idle (TabIsZz.lean's Limits); at the chain 0 and the sending's
whole text that is a law of other authors: `ownMsgs_shortBook`
(Johnson/Desc/ProofFile/Honest/K1/SeatedTeeth.lean): of messages alone. A reader of the input's
trace's cells against which `(wit w).R.cells` wants its lemma: cells′, with ReadsAs
(Johnson/FrontRoad/CellsAreTraceSpec.lean, of other authors): that file is not opened here.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.TabIsZz
import Johnson.Desc.ProofFile.Honest.K8.AheadEntry
import Johnson.Desc.ProofFile.Honest.K8.DrawBridgeProofs
import Johnson.Desc.Sound.SeatTabMsgs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Slice VerifiableInference.Desc VerifiableInference.Desc.Sound
open OnBytes.Params (ReqArray)
open OnBytes.Model (HTailF2)
open OnBytes.HonestTrace (pairOf seatsOf seatAt)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.First.K8 (cellsAhead)
open VerifiableInference.Desc.First.K8.Honest (allRows)
open VerifiableInference.Desc.K9 (rowBitsOf placeBitsOf)
open ProofFile.Honest.K2 (drawnAt)
open ProofFile.Honest.K5 (laidBack_covers)
open ProofFile.Honest.FirstThread (Script OwnMsgs)
open Johnson.Prover.Send (shapeAt)

/-- **UNDER hm, PROVED OF NO SCRIPT; AT LETTERS s', tl', hd: `ZzBy` AT THE LAW's TABLE OF CELLS OVER
THE SCRIPT's WITNESS.** At the digits' message's first sending alone: of a copy that a later member
keeps or sends again nothing is said. An equation on the Script.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem zzBy_of_ownMsgs {X Wl Cw Tok Pz : Type} {Bk : ProverCoinCounts} (Q : Script Bk Wl Cw Tok MsgT)
    (Vd : Wl → Prop) (N ch : ℕ) (wit : Wl → K1.PlaceIn ProofFile.Inst) (S₀ : OnBytes.HonestTrace.Sz)
    (Z : Pub) (G : Ground) (gp : _root_.Desc.Plain.GPar) (lk piece first : ℕ)
    {J : K1.SendJob (K1.PlaceIn ProofFile.Inst) X}
    (hJ : J = K1.laterJobAt G.first gp lk piece 2 first (K1.lotData S₀ Z G)) (own₀ : X)
    (front n : ℕ) (txt : Coins Bk → Wl → List Fmt.Drawn → Bool → ℕ → ℕ → Option GE)
    (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (Nn : Numbers) (m : ℕ) {y : Mem}
    (hm : OwnMsgs Q Vd N (numOf arr y) front txt) {l : ℕ} {nm : String} {a : ReqArray}
    (htxt : ∀ u col rp, laidAt a u col = some rp → ∀ k w h v,
      K1.msgTxt ch wit J own₀ n k w h false rp.1 rp.2 = some v →
        txt k w h false rp.1 rp.2 = some v)
    (k : Coins Bk) (c : Cs (K1.dueR J.P J.ride))
    (hc : K1.lentCut k ch ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = some c)
    (w : Wl) (hw : Vd w) (hd : List Fmt.Drawn) (hN : N ≤ hd.length)
    (ok : reqLayoutOk G.first.codes G.first.shape G.first.layout = true)
    (ha : arrayOf G.first.layout l nm = some a) (hname : a.name = "ZZ") {M : Params.ReqMessage}
    (hM : Meaning.messageAt G.first.shape l a.message = some M) (hans : M.shape.answers ≠ 0)
    (hlen : G.first.codes.lengthsOk = true) (hne : (⟨J.P.place, 0⟩ : Addr) ≠ K1.firstAddr)
    (hmom : ∀ t, (seatAt (seatsOf Z G "BZ") ⟨⟨J.P.place, 0⟩, n⟩ = some t ∨
      seatAt (seatsOf Z G "U3") ⟨⟨J.P.place, 0⟩, n⟩ = some t) → K1.momentIs t 2 = true)
    (hB : bearsZz G.first.layout (pairOf (seatsOf Z G "BZ")) ⟨⟨J.P.place, 0⟩, n⟩ =
      some (l, a.message))
    {tl₀ : HTailF2} (htl : (zzPubOf G Z.D.1 (K3.matsOwn G.W)).tl l = some tl₀) {tr : List Int}
    (hdr : drawnAt (zzPubOf G Z.D.1 (K3.matsOwn G.W)).rng
      ((hd.take front).take ((zzDataAt G Z.D.1 (pairOf (seatsOf Z G "BZ")) (K3.matsOwn G.W)).heardAt
        ⟨⟨J.P.place, 0⟩, n⟩)) l = .ok tr)
    (z : Pz) (s' : S) {q : K9.Part} (hp : K9.segAt? s' = some q) {tl' : HTailF2} {x : ℕ × String}
    (hx : q.L.arrayOf[tl'.ix.ZZ]? = some x) {h : K9.Ahead}
    (hA : K9.aheadIn (Nn.sent m) (Nn.group m) q (x.1, x.2) = some h) (hAa : h.A = a)
    (hok : laidMatrixOk h.A (rowBitsOf h.shape .main) (placeBitsOf q.d.st.codes h.shape .main) =
      true)
    (hy : ms.find? (fun y => decide (seatOf y = h.seat)) = some y) (hcs : cs = J.P.codes)
    (hsh : (y.1.l.get y.2).1 = shapeAt J.P n) (hpar : parOfTail tl₀ = parOfTail tl')
    (hcf : tl'.cfF = tr.toArray)
    (hmz : 2 * tl'.mz ≤ 2 * allRows (parOfTail tl₀)) (hsI : tl₀.tau ≤ a.sizeI)
    (hsC : 2 * allRows (parOfTail tl₀) ≤ a.sizeC) :
    ZzBy tl' (cellsAhead cs arr ms Nn m (z, s') (Q.wit k w hd))
      (cellsAtOf (wit w).R.cells (K3.matsOwn G.W l)) := by
  refine zzBy_of_zzOf tl' _ (K3.matsOwn G.W l) (wit w).R.cells tr hcf fun u hu col hcol => ?_
  have htau : tl₀.tau = tl'.tau := congrArg (·.tau) hpar
  have hu₀ : u < tl₀.tau := htau ▸ hu
  have hcol₀ : col < 2 * allRows (parOfTail tl₀) := Nat.lt_of_lt_of_le hcol hmz
  obtain ⟨rp, hrp, -⟩ := laidBack_covers ok ha (i := u) (c := col) (Nat.lt_of_lt_of_le hu₀ hsI)
    (Nat.lt_of_lt_of_le hcol₀ hsC)
  have ez : zzOf tl₀ (K3.matsOwn G.W l) (wit w).R.cells tr u col =
      zzOf tl' (K3.matsOwn G.W l) (wit w).R.cells tr u col := by
    unfold zzOf
    rw [hpar]
  rw [cellsAhead_is_entry cs arr ms Nn m z s' hp hx hA hok _ (hAa.symm ▸ hrp),
    seatTab_of_mem cs arr ms _ _ y hy, ← ez]
  show (Q.wit k w hd).tab cs (y.1.l.get y.2).1 (numOf arr y) (y.1.seat y.2).1 (y.1.seat y.2).2 false
    rp.1 rp.2 = _
  rw [hcs, hsh]
  exact tab_is_zz Q Vd N ch wit S₀ Z G gp lk piece first hJ own₀ front n _ _ _ txt hm
    (htxt u col rp hrp) k c hc w hw hd hN ok ha hname hrp hM hans hlen hne hmom hB htl hu₀ hcol₀ hdr

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.zzBy_of_ownMsgs
