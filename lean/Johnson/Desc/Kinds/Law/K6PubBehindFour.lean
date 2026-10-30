-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6PubBehindFour.lean: THE FOUR PUBLIC TESTS THAT THE SUB-PROTOCOL AT THE
OUTPUT HEAD MAKES (lookIn 24 8; formsInT 24 4 "own"; formsInT 24 3 "planes"; formsInT 24 4 "join")
HOLD BEHIND ITS ACCEPT, AT THE COMPOSED MEANING OF THE OPEN CLAIMS AND THE FULL CHAIN: the field
pubBehind of K6DueAt (Law/K6TiedAtObject.lean) at these four items alone. One statement with
its proof: A GATHERING: it calls Law/K6LookInMade.lean, Law/K6FormsMade.lean and
Law/PlanesFormsInT.lean, and pays inside whatever the table's promise in front of the sub-protocol
gives (Law/K6FrontSays.lean, Law/K6FrontShape.lean, Law/K6RestAt.lean, Law/K6LeftSays.lean,
Law/ReadsEntInT.lean, Law/K6PubNumbers.lean, Law/CoveredBehind.lean).

WHAT IT IS NOT. An implication. Nothing on soundness. These four tests are totalities: they say that
a later test of the verifier's will find what it looks for. WHAT IS LEFT AS PREMISES:
(B) ON PUBLIC PARAMETERS ALONE: planB; five tests with code (hC1: k6PubC; hC2: readsRoomC; hB; hRB;
    hC3: seatsK6C); hX (the public parameters are made by publicOf); treesB; sorts; planeCols;
    hTT, hVV (the plan's window and vocabulary are the model's).
(L) ON THE IOP AS WRITTEN IN LEAN, AT ONE LIST OF ROUNDS Lk: KS, KB (the head's four runs, both
    ways, at link 24), runs2, back2 (the run on the planes, both ways), readers.
(F) ON REACHED STATES: hReach (no tables are laid; the merge has laid no end value), hFold (five
    facts along the fold), hwords (the state's words are the public request's), htok (a reply is
    heard, as a token's number), hLv (of what the lookup on the calls left: LeavesReady; the slot of
    the bits' value and the slots of the starting form of the sumcheck over the leaves are filled).
AND hLeft: this kind's first tie. No values are shown at which the premises hold together.
LETTERS. No letter stands under "there is" in the conclusion. In htok: y0: pinned by either
equation.

-/
import Johnson.Desc.Kinds.Law.K6LookInMade
import Johnson.Desc.Kinds.Law.K6FormsMade
import Johnson.Desc.Kinds.Law.ReadsEntInT
import Johnson.Desc.Kinds.Law.K6PubNumbers
import Johnson.Desc.Kinds.Law.K6FrontShape
import Johnson.Desc.Kinds.Law.K6Reached
import Johnson.Desc.Kinds.Law.K6RestAt
import Johnson.Desc.Kinds.Law.PlanesFormsInT
import Johnson.Desc.Kinds.Law.CoveredBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Params (ReqLayout)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Meaning Pub pubFit)
open VerifiableInference.Desc.Sound (Piece Frame MsgT MgData mgAll onQ linksFull)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ)
  (Fr : Frame) (Rch : ℕ → (P × S) × Fr.E.Str → Prop) (Lp : K12.Door.Laid)
  (Mm : List OracleShape)

set_option quotPrecheck false in
/-- The composed meaning. -/
local notation "MGA" => mgAll D Mg

/-- The driver's list of places, at the full chain. -/
local notation "PS" => First.flatPlacesOf linksFull true

/-- **THE FIELD pubBehind.** -/
theorem pubBehind_four {bef : List (ℕ × ℕ)} {B bS : Block S Claim}
    {q : Piece (_root_.Run.ckP .two) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT)}
    (Hs : Seated Wp .two Fr q 24 bef B bS)
    (hp : PS[341]? = some { chain := 1, link := some 24, piece := 4, kind := .K6 })
    (hfit : pubFit (MGA).more linksFull PS = true) (hplan : planB Wp = true)
    {pol KL : ByteArray} {lay : Option ByteArray}
    (hX : OnBytes.Model.Verify.publicOf pol KL lay = .ok Wp)
    (hC1 : k6PubC Wp = true) (hC2 : readsRoomC Wp lay6 (D.sent.arrayOf.getD 24 #[]) = true)
    (hB : tabsPlanB Wp.hS Wp.HLy Wp.H = true) (hRB : readsPlanB Wp.hS Wp.H = true)
    (hC3 : AtFold.seatsK6C D.arr D.N Wp lay6 num (num 24 0) 0 D.cs D.shape D.pubD.dS Lp Mm
      (D.sent.arrayOf.getD 24 #[]) (D.N.msgsAt PS[341]?) = true)
    (treesB : First.FillSent.treesAt D.built 24 = First.FillSent.looksOf Wp.H.Fp)
    (sorts : D.links[24]? = some .head) (hTT : Wp.hS.T = Inst.Model.ppref.T)
    (hVV : Wp.hS.V = Inst.Model.ppref.V)
    (planeCols : ∀ p3 h3, First.Look.placeAt Wp 24 false = some p3 → p3.shape = some h3 →
      h3.NC * 2 ^ (h3.kT + 5 - Wp.hS.lmbH) ≤ (Wp.H.tl.mats.getD (Wp.hS.NHf + 1 + 1) {}).k *
        ((Wp.H.tl.mats.getD (Wp.hS.NHf + 1 + 1) {}).m / 2 ^ Wp.hS.lmbH))
    (piece6 : ℕ) (Lk : Link S Claim) (small : S → Option K9.Read)
    (KS : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) 24 piece6 (K9.statesOfLink Lk) 3)
    (KB : K6Back Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) 24 piece6 (K9.statesOfLink Lk) 3)
    (runs2 : PlanesStates (readsOf Wp) Wp.hS.lmbH (K9.statesOfLink Lk) 2)
    (back2 : PlanesBack (readsOf Wp) Wp.hS.lmbH (K9.statesOfLink Lk) 2)
    (readers : D.Rd 24 = K9.readersOfLink ⟨small, k6Silent (p8K6 Wp 24) (K9.statesOfLink Lk)⟩ Lk)
    (hLeft : ∀ a, onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a → a.1.2.failed = none →
      K6Left Wp a.1.2)
    (hReach : ∀ a, Rch 341 a → a.1.2.failed = none → AtFold.K6Reached a.1.2)
    (hFold : ∀ a, Rch 341 a → a.1.2.failed = none →
      AtFold.FoldAt Lp Mm D.cs D.shape lay6 a.1.2)
    (hwords : ∀ a, onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a → Rch 341 a →
      a.1.2.failed = none → a.1.2.req = OnBytes.Flat.requestWordsOf (D.H.req a.1).val)
    (htok : ∀ a, onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a → Rch 341 a →
      a.1.2.failed = none → ∃ y0, Reply.token (seatAt Wp.hS (readsOf Wp)).toSeat a.1.2 = some y0 ∧
        a.1.2.replyTok? = some y0)
    (hLv : ∀ a, onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a → Rch 341 a →
      a.1.2.failed = none → ∀ Fs gk, a.1.2.fork? = some Fs → a.1.2.lookHeard? = some gk →
      LeavesReady gk Fs ∧ OnBytes.PscRun.Filled Fs gk.sBit ∧
        ∀ x ∈ gk.leaves.start.slots.toList, OnBytes.PscRun.Filled Fs x.1) :
    ∀ a τ b, onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a → Rch 341 a →
      a.1.2.failed = none → q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      ∀ i ∈ [First.Pub.lookIn 24 8, .formsInT 24 4 "own", .formsInT 24 3 "planes",
        .formsInT 24 4 "join"], (MGA).pub i b.1 = true := by
  intro a τ b ha hrc hm hb hA i hi
  obtain ⟨_, c2, c3, c4, c5, p8, sh8, c6, c7, c8⟩ := k6Pub_says Wp hC1
  have hL := hLeft a ha hm
  have left := AtFold.left_front D Mg Fr hfit hp a ha hm
  have R := hReach a hrc hm
  obtain ⟨aK, I, _⟩ := AtFold.stateIsPlan_behind D Mg lay6 Fr Lp Mm Hs hfit hp a b τ ha hm hb
    (hFold a hrc hm)
  obtain ⟨cU, u1, u2⟩ := AtFold.reads_of_C hC3 I
  have hEnt := entInT_reads Wp lay6 _ hC2 (D.N.sent 24 0) b.1.2 aK I.seg I.layout I.arrays cU u1 u2
  have hMask : (K9.maskSeat (D.N.sent 24 0) aK).isSome = true := by
    obtain ⟨o, x, m1, m2, _⟩ := AtFold.maskSeated_of_C hC3 I
    unfold K9.maskSeat
    rw [Sound.maskAt_eq, m1]
    show (K9.seatAt (D.N.sent 24 0) aK.d.book o).isSome = true
    rw [m2]
    rfl
  have tree := AtFold.oneRow_front D Mg Fr hX treesB hfit hp a ha hm
  have hruns := runs_at_head D sorts
  have hc : ∃ cov, b.1.2.covered Wp.hS.T Wp.hS.V = .ok cov := by
    obtain ⟨y0, t1, t2⟩ := htok a ha hrc hm
    exact covered_behind Hs a b τ hb (D.H.req a.1).val (D.H.req a.1).property.1
      (hwords a ha hrc hm) y0 t2 (hL.2.1 y0 t1) hTT hVV
  have forms := made_forms D Hs hplan piece6 Lk small KS KB readers a b τ hb hL hA R.noTab R.wo
    left tree c3 hB hRB hc c4 c5 aK I.seg hMask hEnt
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact made_lookIn D Mg Hs hplan a b τ hb hL left (AtFold.rows_front D Mg Fr hp a ha hm)
      (AtFold.linkArr_front D Mg Fr hfit hp a ha hm) c2 p8 c6 sh8 c7 c8
  · exact made_own D Mg hruns.2.2.2.1 b.1 forms
  · rw [Sound.mgAll_pub, First.pubAll_formsInT]
    have e : D.pubD.runs 24 3 "planes" = [(2, "planes")] := hruns.2.1
    rw [e]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    show K9.formsInT (D.Rd 24) (D.N.sent 24 0) 2 "planes" b.1.2 = true
    obtain ⟨p3, hp3, L3⟩ := left
    obtain ⟨h3, F, g, hs3, hF, hg, Y, hlv⟩ := left_says p3 a.1.2 L3
    obtain ⟨q1, _, q3, q4, q5⟩ := c5 p3 h3 hp3 hs3
    obtain ⟨b6, rs, gs, h6, hd⟩ := below_yes_seated Hs a b τ hb
    obtain ⟨G0, tr, hG0, htr0, hR1, hK⟩ := tree
    obtain rfl : G0 = F := Option.some.inj (hG0.symm.trans hF)
    obtain ⟨_, hd'⟩ := canonical_of_below b6 a.1.2 b.1.2 rs gs hd
    have et := blockOf_trees Wp 24 b6 h6 a.1.2 b.1.2 rs gs hd'
    rw [hF, seg_fork I.seg] at et
    have et' : aK.F.trees = G0.trees := et
    obtain ⟨o', ho', ht'⟩ := (noTablesB_iff b.1.2).1
      (noTables_below Wp 24 b6 h6 a.1.2 b.1.2 rs gs hd R.noTab)
    obtain ⟨v1, v2, v3⟩ := hLv a ha hrc hm G0 g hF hg
    have hFree : K9.mergeOf b.1.2 = none := by
      obtain ⟨o, F1', X, Q, ho, _, _, e⟩ := k6_behind Hs a b τ hb
      have hwo := R.wo
      rw [e]
      unfold K9.mergeOf at hwo ⊢
      rw [ho] at hwo
      exact hwo
    rw [readers]
    exact planes_formsInT_behind Wp 24 b6 h6 a.1.2 b.1.2 rs gs hd
      (k6On_front Hs hplan a b τ hb hL) (p8K6 Wp 24) rfl hB hRB hc aK I.seg tr
      (by rw [et']; exact htr0) (by rw [hK]; exact c3) (by rw [hK]; exact Nat.le_refl _) hR1 2
      (K9.statesOfLink Lk) runs2 back2 _ (D.N.sent 24 0)
      (readers_silent_planes (readsOf Wp) Wp.hS.lmbH 2 Lk runs2 (p8K6 Wp 24) small b.1.2 o' ho' ht')
      G0 hF g hg v1
      (by
        have z0 := Y.zkLen 0 (by rw [q1]; decide)
        show Wp.hS.ls ≤ ((g.zk.getD 0 #[]).extract 0 (Wp.HLy.calls.getD 0 default).lJ).size
        rw [Array.size_extract, z0]
        omega)
      (by
        unfold First.Look.planesOk
        rw [Y.shape, decide_eq_true c4, decide_eq_true q3]
        rfl)
      (by
        show g.shape.NC * 2 ^ (g.shape.kT + 5 - Wp.hS.lmbH) ≤ _
        rw [Y.shape]
        exact planeCols p3 h3 hp3 hs3)
      hlv v3 v2 (by rw [hK]; exact hEnt) hMask hFree
  · exact made_join D Mg hruns.2.2.1 b.1 forms

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.pubBehind_four
