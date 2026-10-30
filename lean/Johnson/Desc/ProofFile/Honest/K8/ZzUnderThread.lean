-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/ZzUnderThread.lean: the honest side of the smallness test (K8): THE
FIELD zz OF `K8TwoAt` (Johnson/Desc/ProofFile/Honest/K8/ExchangeByKind.lean), IN ITS OWN FORM, AT
THE THREAD OF LETTERS L (`Letters.thread`, Johnson/Desc/ProofFile/Honest/Thread/First.lean) AND THE
LAW's TABLE OF CELLS `cellsAhead`: FROM ONE PREMISE ON THE SCRIPT (hm), ONE ON THE THREAD's STATES
BEHIND THE DRAW (hSt), ONE ON TWO READERS OF THE INPUT (hR), AND PUBLIC PREMISES. One statement with
its proof; no definition.

`K8TwoAt.zz` IS EXCHANGED HERE FOR hm · hSt · hR, EACH PROVED NOWHERE: hm: on the Script · hSt: on
the verifier's state alone, asked at every reached state behind the member's step · hR: on two
readers of the hidden input: the one of the three that names it. Behind a yes at which the second
stop is silent. An equation on the Script. NOT IN FRONT OF A LAW OVER COINS. At the
digits' message's first sending alone: of a copy that a later member keeps or sends again nothing is
said.

  **`zz_under_thread`**
HOW. `zzBy_of_ownMsgs` (Johnson/Desc/ProofFile/Honest/K8/ZzOfOwnMsgs.lean) at hd := what was heard,
the draw's challenge d, any tail e. OFF THE THREAD (`Thr`,
Johnson/Desc/ProofFile/Honest/Thread/Thr.lean: the first half of the pair `ThrS`): its clause on the
challenges gives how many were heard (`drawsFit_length`); its last clause that the input is valid.
THE CUT: from the public test hbook (`lentCut_isSome`,
Johnson/Desc/ProofFile/Honest/K1/ScriptAtLaw.lean). THAT THE DRAWN MATRIX IS d's: from hrng, hfront
and that count, by the texts of `drawnAt` and of the filling's `heardAt`.
THE PREMISES, SORTED. ON THE SCRIPT: hm, with htxt. ON THE PROVER's TEXT: hJ. ON THE INPUT: hVd (a
valid input is one that hm speaks of) · hR: AT EVERY VALID INPUT THE READER's CELLS ARE THE CELLS OF
THE INPUT's TRACE: A TIE BETWEEN TWO READERS OF THE HIDDEN INPUT: NOT PUBLIC. ON THE THREAD's
STATES: hSt: AT EVERY STATE BEHIND THE DRAW THERE ARE THE OPEN PART, THE ARRAY's NAME, WHAT THE PLAN
SAYS OF THE ARRAY AHEAD AND THE TABLE's MEMBER AT ITS SEAT, WITH TEN CLAUSES ON THEM. THE TEN SPEAK
OF THE VERIFIER's STATE, THE PLAN AND THE LAYOUT, AND NAME NO COIN, NO INPUT AND NO WITNESS; BUT hSt
ASKS THEM AT EVERY k AND m UNDER THE PAIR `ThrS L.thread Said b k s m E`, A STEP OF THE MEMBER blk
AND THE FORM BEHIND IT, WHICH NAME THE RUN's COINS AND THE INPUT: IT IS A PREMISE ON WHAT THE THREAD
REACHES. THESE FOUR ARE WHAT THE FIELD's ONE CALLER HAS IN HAND (`small_exchange_at`,
Johnson/Desc/ProofFile/Honest/K8/SeatedItemsAt.lean). ON PUBLIC DATA: all others; among them hrng
(the segment's round "RNG" is the round in front of which the thread stands at b), hfront, hNle. THE
LIST IN THE END IS `K3.matsOwn G.W l`, AS THE LOT's DATA HAVE IT.
NO OPTION IS RAISED, NO INSTANCE TAKEN AWAY. NO TACTIC THAT SEARCHES.
Limits. AN IMPLICATION. hm, hSt AND hR ARE PROVED NOWHERE HERE; NO LETTERS ARE GIVEN AT WHICH THE
PREMISES HOLD TOGETHER. IT IS COUNTED NOWHERE; `K8TwoAt.zz` IS NOT PAID BY IT: THREE UNPAID PREMISES
STAND IN ITS STEAD. The idle ways of ZzOfOwnMsgs.lean's Limits are its own too; and where no state
of the thread stands at b, or blk takes no step there, it holds emptily. The field tie is not
touched. IT DOES NOT SAY THAT THE WITNESS IS THE MODEL's: it says what one array of the Script's
witness holds, under hm, in terms of what a reader yields of the input. In the top law's premise the
list stands under "there is", and the payer picks it: whoever pays with this law picks `K3.matsOwn
G.W l`; that this is `matsOf` (Johnson/HonestTrace/DigitsAtTrace.lean) is said nowhere.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.ZzOfOwnMsgs
import Johnson.Desc.ProofFile.Honest.Thread.HeardLaw
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw

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
open ProofFile.Honest.FirstThread (Letters OwnMsgs)
open Johnson.Prover.Send (shapeAt)

/-- **THE FIELD zz OF `K8TwoAt`, IN ITS OWN FORM, EXCHANGED FOR hm · hSt · hR, EACH PROVED
NOWHERE.** hm: on the Script. hSt: on the verifier's state alone, asked at every reached state
behind the member's step. hR: on two readers of the hidden input. Behind a yes at which the second
stop is silent. At the digits' message's first sending alone: of a copy that a later member keeps or
sends again nothing is said. An equation on the Script.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem zz_under_thread {Bk : ProverCoinCounts} {Cl W₀ Rc Tr X Pz Cw Tok : Type}
    (L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr X Pz Cw Tok MsgT)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (b : ℕ) (blk : Block S Cl)
    (cells : Tr → Cells)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (N ch : ℕ) (hch : ch ≤ 1)
    (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst) (S₀ : OnBytes.HonestTrace.Sz) (Z : Pub)
    (G : Ground) (gp : _root_.Desc.Plain.GPar) (lk piece first : ℕ)
    {J : K1.SendJob (K1.PlaceIn ProofFile.Inst) X}
    (hJ : J = K1.laterJobAt G.first gp lk piece 2 first (K1.lotData S₀ Z G)) (own₀ : X)
    (front n num : ℕ)
    (txt : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Bool → ℕ → ℕ → Option GE)
    (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (Nn : Numbers) {l : ℕ}
    (hm : OwnMsgs L.Q Vd N num front txt) {nm : String} {a : ReqArray}
    (htxt : ∀ u col rp, laidAt a u col = some rp → ∀ k w h v,
      K1.msgTxt ch wit J own₀ n k w h false rp.1 rp.2 = some v →
        txt k w h false rp.1 rp.2 = some v)
    (hbook : K1.bookCovers Bk ch ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = true)
    (hVd : ∀ w, L.valid w → Vd w)
    (ok : reqLayoutOk G.first.codes G.first.shape G.first.layout = true)
    (ha : arrayOf G.first.layout l nm = some a) (hname : a.name = "ZZ") {M : Params.ReqMessage}
    (hM : Meaning.messageAt G.first.shape l a.message = some M) (hans : M.shape.answers ≠ 0)
    (hlen : G.first.codes.lengthsOk = true) (hne : (⟨J.P.place, 0⟩ : Addr) ≠ K1.firstAddr)
    (hmom : ∀ t, (seatAt (seatsOf Z G "BZ") ⟨⟨J.P.place, 0⟩, n⟩ = some t ∨
      seatAt (seatsOf Z G "U3") ⟨⟨J.P.place, 0⟩, n⟩ = some t) → K1.momentIs t 2 = true)
    (hB : bearsZz G.first.layout (pairOf (seatsOf Z G "BZ")) ⟨⟨J.P.place, 0⟩, n⟩ =
      some (l, a.message))
    {tl₀ : HTailF2} (htl : (zzPubOf G Z.D.1 (K3.matsOwn G.W)).tl l = some tl₀)
    (hrng : (zzPubOf G Z.D.1 (K3.matsOwn G.W)).rng[l]? = some (roundsTo L.bs b))
    (hfront : roundsTo L.bs b + 1 ≤ front) (hNle : N ≤ roundsTo L.bs b + 1)
    (hcs : cs = J.P.codes) (hsI : tl₀.tau ≤ a.sizeI)
    (hsC : 2 * allRows (parOfTail tl₀) ≤ a.sizeC)
    (hR : ∀ w, L.valid w → (wit w).R.cells = cells w.trace)
    (hSt : ∀ k s m E ds pl cols s' tl', ThrS L.thread Said b k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds pl cols s' →
      L.thread.Form (b + 1) k s' pl.2 → s'.tl? = some tl' →
      ∃ (q : K9.Part) (x : ℕ × String) (h : K9.Ahead) (y : Mem), K9.segAt? s' = some q ∧
        q.L.arrayOf[tl'.ix.ZZ]? = some x ∧
        K9.aheadIn (Nn.sent l) (Nn.group l) q (x.1, x.2) = some h ∧ h.A = a ∧
        laidMatrixOk h.A (rowBitsOf h.shape .main) (placeBitsOf q.d.st.codes h.shape .main) =
          true ∧
        ms.find? (fun y => decide (seatOf y = h.seat)) = some y ∧ numOf arr y = num ∧
        (y.1.l.get y.2).1 = shapeAt J.P n ∧ parOfTail tl₀ = parOfTail tl' ∧
        2 * tl'.mz ≤ 2 * allRows (parOfTail tl₀)) :
    ∀ k s m E ds y cols s' tl' (d : Fmt.Drawn) e (z : Pz), ThrS L.thread Said b k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      L.thread.Form (b + 1) k s' y.2 → s'.tl? = some tl' → tl'.cfF = d.trits.toArray →
      ZzBy tl'
        (cellsAhead cs arr ms Nn l (z, s') (L.thread.wit k m.st.input (m.st.heard ++ d :: e)))
        (cellsAtOf (cells m.st.input.trace) (K3.matsOwn G.W l)) := by
  intro k s m E ds y₀ cols s' tl' d e z hP hds hS hF ht hcf
  obtain ⟨q, x, h, y, hp, hx, hA, hAa, hok, hy, hnum, hsh, hpar, hmz⟩ :=
    hSt k s m E ds y₀ cols s' tl' hP hds hS hF ht
  have hT := hP.1
  have hLen : m.st.heard.length = roundsTo L.bs b := drawsFit_length _ _ hT.2.1
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 ((K1.lentCut_isSome k ch hch _ _).trans hbook)
  have hw : Vd m.st.input := hVd _ hT.2.2.2.2.2.2
  have hN : N ≤ (m.st.heard ++ d :: e).length := by
    rw [List.length_append, List.length_cons, hLen]
    exact Nat.le_trans hNle (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le _)) _)
  have hH : (zzDataAt G Z.D.1 (pairOf (seatsOf Z G "BZ")) (K3.matsOwn G.W)).heardAt
      ⟨⟨J.P.place, 0⟩, n⟩ = roundsTo L.bs b + 1 := by
    show (match (bearsZz G.first.layout (pairOf (seatsOf Z G "BZ")) ⟨⟨J.P.place, 0⟩, n⟩).bind
        fun x => (zzPubOf G Z.D.1 (K3.matsOwn G.W)).rng[x.1]? with
      | some n => n + 1
      | none => 0) = _
    rw [hB]
    show (match (zzPubOf G Z.D.1 (K3.matsOwn G.W)).rng[l]? with
      | some n => n + 1
      | none => 0) = _
    rw [hrng]
  have hAt : (((m.st.heard ++ d :: e).take front).take (roundsTo L.bs b + 1))[roundsTo L.bs b]? =
      some d := by
    rw [List.take_take, Nat.min_eq_left hfront, List.getElem?_take_of_lt (Nat.lt_succ_self _),
      List.getElem?_append_right (Nat.le_of_eq hLen), hLen, Nat.sub_self]
    rfl
  have hdr : drawnAt (zzPubOf G Z.D.1 (K3.matsOwn G.W)).rng
      (((m.st.heard ++ d :: e).take front).take
        ((zzDataAt G Z.D.1 (pairOf (seatsOf Z G "BZ")) (K3.matsOwn G.W)).heardAt
          ⟨⟨J.P.place, 0⟩, n⟩)) l = .ok d.trits := by
    rw [hH]
    unfold drawnAt
    rw [hrng]
    show (match (((m.st.heard ++ d :: e).take front).take
        (roundsTo L.bs b + 1))[roundsTo L.bs b]? with
      | some d => (.ok d.trits : Except String (List Int))
      | none => .error "a segment's matrix has not been drawn") = _
    rw [hAt]
  have hEnd := zzBy_of_ownMsgs L.Q Vd N ch wit S₀ Z G gp lk piece first hJ own₀ front n txt cs arr
    ms Nn l (hnum.symm ▸ hm) htxt k c hc m.st.input hw (m.st.heard ++ d :: e) hN ok ha hname hM hans
    hlen hne hmom hB htl hdr z s' hp hx hA hAa hok hy hcs hsh hpar hcf hmz hsI hsC
  rw [hR _ hT.2.2.2.2.2.2] at hEnd
  exact hEnd

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.zz_under_thread
