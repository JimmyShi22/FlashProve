-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ReadersHeadDigits.lean: THE OUTPUT HEAD's SEGMENT's SEVEN RUNS AT ITS DIGITS'
PLACE (a commitment alone): what a run's reader answers in front it answers behind. Statements with
their proofs: calls, at the narrower cut (Johnson/Desc/K1/Law/RestDef.lean's restOf, which keeps the
reads' tables). And k01_fifty_atBase's binder hRd with that laid in.

How. As Johnson/Desc/K1/Law/ReadersSeated.lean and ReadersHead.lean do at the wider cut. The members:
"objects", "guests": Johnson/Desc/K1/Law/ReadersStayAt.lean · "planes": RespectsAtt.lean's
respects_planesCalls at the output head's caller's readers (planesAt_rest, here) · "norm", "policy",
"logits": Johnson/Desc/First/Link/Law/RespectsK6.lean (respects_runsBy, seatRest_at) · "join":
respects_joinCalls at the output head's key vectors (callerKeys_rest, over lettersAt_rest).
What the link states: IM.k3_of, IM.k6_of with IM.claims_alone.
Main names:
  alike_tables · withTables_alike1 · silent_alike1 · pairStays_head1   the second reader
  respects_laid1 · respects_states1                                    the seat's form
  planesAt_rest · callerReaders_rest · callerKeys_rest
  k3At_calls_respects1      the lookup's lot's sub-protocol on the calls, AT ANY LINK, "planes" too
  lookup_mem · respects_runsBy_mem · k6_claims_respects               K6's lot's sub-protocol
  states_head2 · states_head3   **blocks 2 and 3 of link 24**
  fwd_head_digits           **Fwd at all seven runs over the digits' place of link 24.**
  hRd_paid2                 **hRd, to the letter**: what stays of the readers is hHeadR: five runs at
                            ONE place: the output head's reads' place.
What is not claimed. hHeadR. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.ReadersPaid
import Johnson.Desc.First.Link.Law.RespectsK6
import Johnson.IMR.K6Seat
import Johnson.Stored.HeadAddsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place)
open VerifiableInference.Desc.First (S Here HeadOwn ModelPart Item Pub Meaning Numbers More PubData
  flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull runsAt MsgT MgData CellsQ mgAll d13 mgBase)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.K13.Law (openAt)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.K9 (Readers RunOf readerOf LinkHoles statesOfLink readersOfLink holesAt
  phAt)
open VerifiableInference.Desc.Kinds.Head (Seat seatAt planesAt callerReaders callerKeys runsBy
  kind kindWithJoin asClaim seatedClaims blockClaims)
open VerifiableInference.Desc.Kinds.Head.Law (withTables withTables_iff k6Silent)
open VerifiableInference.Desc.LinkJoin (lettersAt_rest respects_runsBy seatRest_at)
open VerifiableInference.Reads.Pass (Fwd)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix)
open ProofFile (Cl)

/-! ## 1 The second reader, at the narrower cut -/

theorem alike_tables {s s' : S} (hA : RestAlike s s') (a a' : HeadOwn) (ha : s.here = .head a)
    (ha' : s'.here = .head a') (tt : Head.Tables) :
    RestAlike { s with here := .head { a with t := some tt } }
      { s' with here := .head { a' with t := some tt } } := by
  have hh : (restOf s).here = (restOf s').here := congrArg S.here hA
  have e1 : hereRest (.head a) = hereRest (.head a') := by
    rw [← ha, ← ha']
    exact hh
  have e2 := Here.head.inj e1
  have e3 : hereRest (.head { a with t := some tt }) = hereRest (.head { a' with t := some tt }) :=
    congrArg (fun o : HeadOwn => Here.head { o with t := some tt }) e2
  show ({ restOf s with here := hereRest (.head { a with t := some tt }) } : S) =
    { restOf s' with here := hereRest (.head { a' with t := some tt }) }
  rw [hA, e3]

theorem withTables_alike1 (P : K8.ReadsQuiet.PH) {s s' e : S} (hA : RestAlike s s')
    (he : withTables P s = some e) : ∃ e', withTables P s' = some e' ∧ RestAlike e e' := by
  obtain ⟨a, cov, x, tt, ha, hop, hcov, hx, ht, rfl⟩ := (withTables_iff P s e).1 he
  have hh : (restOf s).here = (restOf s').here := congrArg S.here hA
  have hreq : s'.req = s.req := (congrArg S.req hA).symm
  have hout : s'.out = s.out := hA.out.symm
  cases ha' : s'.here with
  | head a' =>
    have e1 : hereRest (.head a) = hereRest (.head a') := by
      rw [← ha, ← ha']
      exact hh
    have e2 := Here.head.inj e1
    have o1 : a'.opened = a.opened := (congrArg HeadOwn.opened e2).symm
    have o2 : a'.x = a.x := (congrArg HeadOwn.x e2).symm
    refine ⟨{ s' with here := .head { a' with t := some tt } },
      (withTables_iff P s' _).2 ⟨a', cov, x, tt, ha', o1.trans hop, ?_, o2.trans hx, ht, rfl⟩,
      alike_tables hA a a' ha ha' tt⟩
    unfold S.covered S.replyTok? S.coveredAt at hcov ⊢
    rw [hreq, hout]
    exact hcov
  | _ =>
    exfalso
    have e1 : hereRest s.here = hereRest s'.here := hh
    rw [ha, ha'] at e1
    cases e1

theorem silent_alike1 (P : K8.ReadsQuiet.PH) (states : ℕ → List (RunOf S)) (b : ℕ) (name : String)
    (hr : ∀ r, (states b).find? (fun r => r.1 == name) = some r → Respects r.2) {s s' : S}
    (hA : RestAlike s s') : k6Silent P states b name s' = k6Silent P states b name s := by
  show (withTables P s').bind (readerOf states b name) =
    (withTables P s).bind (readerOf states b name)
  cases h : withTables P s with
  | some e =>
    obtain ⟨e', he', k⟩ := withTables_alike1 P hA h
    rw [he']
    exact readerOf_alike states b name hr k
  | none =>
    cases h' : withTables P s' with
    | none => rfl
    | some e' =>
      obtain ⟨e, he, _⟩ := withTables_alike1 P hA.symm h'
      rw [h] at he
      cases he

theorem pairStays_head1 (X : OnBytes.Model.Verify.Public) (mH : ℕ) (lk : Link S Claim)
    (p : ℕ × String) (hn : (p.2 == "K8.equations") = false)
    (hr : ∀ r, (statesOfLink lk p.1).find? (fun r => r.1 == p.2) = some r → Respects r.2) :
    PairStays (holesAt X mH mH lk) lk p := by
  unfold PairStays
  rw [hn]
  refine ⟨hr, fun s s' hA => ?_⟩
  have e : (holesAt X mH mH lk).silent = k6Silent (phAt X mH) (statesOfLink lk) := by
    unfold holesAt
    simp
  rw [e]
  exact silent_alike1 _ _ _ _ hr hA

/-! ## 2 The seat's form -/

theorem respects_laid1 {b b' : Block S Cl} {name : String} {a : Place}
    (la : IM.LaidAlone ProofFile.sameReply b b' name a) (h0 : ∀ r ∈ b'.claims, Respects r.2) :
    ∀ r ∈ b.claims, Respects r.2 := by
  intro r hr
  rw [IM.claims_alone la] at hr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
  exact respects_guarded ProofFile.sameReply (fun s s' t t' h k => sameReply_alike s s' t t' h k) c.2
    (h0 c hc)

theorem respects_states1 (lk : Link S Claim) (b : ℕ) (B : Block S Claim)
    (hB : lk.hear[b]? = some B) (h : ∀ r ∈ B.claims, Respects r.2) (name : String) :
    ∀ r, (statesOfLink lk b).find? (fun r => r.1 == name) = some r → Respects r.2 := by
  intro r hr
  have hm : r ∈ statesOfLink lk b := List.mem_of_find?_eq_some hr
  unfold statesOfLink at hm
  rw [hB] at hm
  exact h r hm

/-! ## 3 The output head's caller's readers and key vectors read the rest alone -/

theorem planesAt_rest (iU3 : ℕ) : ReadsRest (planesAt iU3) := by
  intro s
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head o =>
    by_cases ho : o.opened = true
    · simp only [planesAt, restOf, hereRest, S.fork?, ho, if_true, forkRest, Array.getElem?_map]
      cases o.t with
      | none => rfl
      | some tt => cases o.F.trees[iU3]? <;> rfl
    · simp [planesAt, restOf, hereRest, S.fork?, ho]
  | _ => rfl

theorem callerReaders_rest (iU3 : ℕ) : ReadsRest (callerReaders (planesAt iU3)) := by
  intro s
  unfold callerReaders
  rw [planesAt_rest iU3 s]

theorem callerKeys_rest (p : Kinds.Head.Par) (h : Head.Shape) (iU3 : ℕ) :
    ReadsRest (callerKeys p (seatAt h iU3)) := by
  intro s
  unfold callerKeys
  rw [lettersAt_rest p _ (seatRest_at h iU3) s]

/-! ## 4 The lots' runs -/

/-- **The lookup's lot's sub-protocol on the calls, at any link.** -/
theorem k3At_calls_respects1 (W : Verify.Public) (Z : ProofFile.Pub) (a : Place) (ha : a.piece ≤ 3)
    (b' : Block S Cl) (h : IM.k3At W Z a = some b') : ∀ r ∈ b'.claims, Respects r.2 := by
  have h' : K3.theStated K3Lot.ofForm (K3Lot.readersAt W) W Z.first.codes Z.first.shape a =
      some b' := h
  unfold K3.theStated at h'
  obtain ⟨b₀, h₀, h'⟩ := Option.bind_eq_some_iff.1 h'
  have e0 : ∀ r ∈ b₀.claims, Respects r.2 :=
    theWhole_calls_of (fun c => Respects c.2) K3Lot.ofForm
      (fun piece laid sent p c hc => block_respects false piece laid sent p c hc rfl) W _ _ a ha
      b₀ h₀
  cases hl : a.link with
  | none =>
    simp only [hl] at h'
    obtain rfl : b₀ = b' := Option.some.inj h'
    exact e0
  | some l =>
    simp only [hl] at h'
    by_cases hp : (a.piece != K3.pieceAt W l false) = true
    · rw [if_pos hp] at h'
      obtain rfl : b₀ = b' := Option.some.inj h'
      exact e0
    · rw [if_neg hp] at h'
      cases hr : K3Lot.readersAt W l with
      | none =>
        simp only [hr] at h'
        obtain rfl : b₀ = b' := Option.some.inj h'
        exact e0
      | some rd =>
        simp only [hr] at h'
        obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h'
        have key : ReadsRest rd := by
          simp only [K3Lot.readersAt] at hr
          repeat' split at hr
          all_goals first
            | cases hr
            | (obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.1 hr
               exact callerReaders_rest i)
            | (obtain ⟨A, _, rfl⟩ := Option.map_eq_some_iff.1 hr
               exact readersOfK_rest _ (seatCO_rest _) _)
        intro r hm
        have hm' : r ∈ b₀.claims ++ [("planes", K3.planesRun (K3.seatCalls K3Lot.ofForm) p.lm rd)] :=
          hm
        rcases List.mem_append.1 hm' with h1 | h1
        · exact e0 r h1
        · rw [List.mem_singleton.1 h1]
          exact respects_planesCalls p.lm rd key

theorem lookup_mem {β : Type} (F : String → β) : ∀ (names : List String) (n : String), n ∈ names →
    (names.map fun x => (x, F x)).lookup n = some (F n)
  | [], _, h => nomatch h
  | x :: l, n, h => by
    rw [List.map_cons, List.lookup_cons]
    by_cases e : (n == x) = true
    · rw [e]
      obtain rfl : n = x := by simpa using e
      rfl
    · have e' : (n == x) = false := by simpa using e
      rw [e']
      rcases List.mem_cons.1 h with h1 | h1
      · rw [h1] at e
        simp at e
      · exact lookup_mem F l n h1

theorem respects_runsBy_mem (names : List String)
    (runs : Kinds.Head.Given → Kinds.Head.Behind → Kinds.Head.Places →
      List (String × List Kinds.Form))
    (keys : Kinds.Head.Given → Kinds.Head.Behind → Kinds.Head.Places → List Kinds.Form)
    (toCl : Kinds.Form → Claim) (p : Kinds.Head.Par) (L : Seat S) (h : LinkJoin.SeatRest L) :
    ∀ r ∈ runsBy names runs keys toCl p L, Respects r.2 := by
  intro r hr
  have hr' := hr
  unfold runsBy at hr'
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hr'
  exact respects_runsBy names runs keys toCl p L h n _ (by
    unfold runsBy
    exact lookup_mem _ names n hn)

/-- **K6's lot's sub-protocol: all four runs.** -/
theorem k6_claims_respects {W : Verify.Public} {l : ℕ} {ms : List (ℕ × ℕ)} {b' : Block S Claim}
    (h : seatedClaims W l ms = some b') : ∀ r ∈ b'.claims, Respects r.2 := by
  unfold seatedClaims at h
  obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold blockClaims at h0
  obtain ⟨iU3, _, rfl⟩ := Option.map_eq_some_iff.1 h0
  have hk : ∀ (p : Kinds.Head.Par), ∀ r ∈ (kind asClaim (seatAt W.hS iU3) l 4 p).claims, Respects r.2 := by
    intro p r hr
    unfold kind at hr
    dsimp only at hr
    exact respects_runsBy_mem _ _ _ asClaim p _ (seatRest_at W.hS iU3) r hr
  intro r hr
  have hr' : r ∈ (kind asClaim (seatAt W.hS iU3) l 4
        (Kinds.Head.parOf W.hS ((Params.settingOf W.P.frame).workOf .field .request))).claims.take 1
      ++ [("join", K3.joinRun (K3.seatCalls asClaim) (callerKeys
        (Kinds.Head.parOf W.hS ((Params.settingOf W.P.frame).workOf .field .request))
        (seatAt W.hS iU3)))] ++
      (kind asClaim (seatAt W.hS iU3) l 4
        (Kinds.Head.parOf W.hS ((Params.settingOf W.P.frame).workOf .field .request))).claims.drop 1 :=
    hr
  rcases List.mem_append.1 hr' with h1 | h1
  · rcases List.mem_append.1 h1 with h2 | h2
    · exact hk _ r (List.mem_of_mem_take h2)
    · rw [List.mem_singleton.1 h2]
      exact respects_joinCalls _ (callerKeys_rest _ W.hS iU3)
  · exact hk _ r (List.mem_of_mem_drop h1)

/-! ## 5 Link 24 -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
  (hR : VerifierAndGoals.readFiles P = .ok pp)
  (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
include hS hR O

theorem states_head2 (lk : Link S Cl) (eL : c.links[24]? = some lk) (name : String) :
    ∀ r, (statesOfLink lk 2).find? (fun r => r.1 == name) = some r → Respects r.2 := by
  obtain ⟨Lk, b, b', e1, e2, k3, la⟩ := IM.k3_of hS hR O 24 (by omega) false
  obtain rfl : lk = Lk := Option.some.inj (eL.symm.trans e1)
  have e2' : lk.hear[2]? = some b := e2
  exact respects_states1 lk 2 b e2'
    (respects_laid1 la (k3At_calls_respects1 Bs.G₀.W Z _ (by decide) b' k3)) name

theorem states_head3 (lk : Link S Cl) (eL : c.links[24]? = some lk) (name : String) :
    ∀ r, (statesOfLink lk 3).find? (fun r => r.1 == name) = some r → Respects r.2 := by
  obtain ⟨Lk, b, b', ms, e1, e2, -, k6, la, -⟩ := IM.k6_of hS hR O
  obtain rfl : lk = Lk := Option.some.inj (eL.symm.trans e1)
  exact respects_states1 lk 3 b e2 (respects_laid1 la (k6_claims_respects k6)) name

/-- **Fwd at all seven runs over the digits' place of link 24.** -/
theorem fwd_head_digits {Pp : Type} (XV : OnBytes.Model.Verify.Public) (hX : headLink XV = 24)
    (X : LinkH) (arrs : Option (List ℕ)) (lk : Link S Cl) (eL : c.links[24]? = some lk)
    (x x' : Pp × S) (hy : YesOf (blkL Z Bs.G₀ 24 true X arrs) x x') :
    ∀ p ∈ runsL 24 false,
      Fwd (readersOfLink (holesAt XV (headLink XV) 24 lk) lk) p.1 p.2 x.2 x'.2 := by
  intro p hp
  rw [runsHead] at hp
  have hb : (p.1 = 2 ∨ p.1 = 3) ∧ (p.2 == "K8.equations") = false := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [hX]
  refine fwd_digits Z Bs.G₀ 24 X arrs _ _ lk rfl p (pairStays_head1 XV 24 lk p hb.2 ?_) x x' hy
  rcases hb.1 with e | e
  · rw [e]
    exact states_head2 hS hR O lk eL p.2
  · rw [e]
    exact states_head3 hS hR O lk eL p.2

end

/-! ## 6 hRd -/

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **hRd, to the letter**: of the readers five runs at one place stay. -/
theorem hRd_paid2 (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hX : headLink XV = 24)
    (hHeadR : ∀ X arrs, Bs.G₀.built[24]? = some X → ∀ lk, c.links[24]? = some lk →
      ∀ x x' y, YesOf (blkL Z Bs.G₀ 24 false X arrs) x x' →
      InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull (flatPlacesOf linksFull true)
        (noL 24 false) x y →
      ∀ p ∈ [(3, "norm"), (3, "policy"), (3, "logits"), (2, "planes"), (3, "join")],
        Fwd (readersOfLink (holesAt XV (headLink XV) 24 lk) lk) p.1 p.2 x.2 x'.2) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y m j r, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull (flatPlacesOf linksFull true) (noL l d) x y → (Pub.formsIn m j r ∈ (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) ∨ Pub.formsInT m j r ∈ (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d))) → ReadersStay (dK Dm.pubD Dm.sent) m j r x.2 x'.2 := by
  refine hRd_paid Dm dk hS hR O hDlk hlk hX ?_
  intro d X arrs hXb lk elk x x' y hy hIn p hp
  cases d with
  | false => exact hHeadR X arrs hXb lk elk x x' y hy hIn p hp
  | true =>
    refine fwd_head_digits hS hR O XV hX X arrs lk elk x x' hy p ?_
    rw [runsHead]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp)

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.alike_tables
#print axioms VerifiableInference.Desc.K1.withTables_alike1
#print axioms VerifiableInference.Desc.K1.silent_alike1
#print axioms VerifiableInference.Desc.K1.pairStays_head1
#print axioms VerifiableInference.Desc.K1.respects_laid1
#print axioms VerifiableInference.Desc.K1.respects_states1
#print axioms VerifiableInference.Desc.K1.planesAt_rest
#print axioms VerifiableInference.Desc.K1.callerReaders_rest
#print axioms VerifiableInference.Desc.K1.callerKeys_rest
#print axioms VerifiableInference.Desc.K1.k3At_calls_respects1
#print axioms VerifiableInference.Desc.K1.lookup_mem
#print axioms VerifiableInference.Desc.K1.respects_runsBy_mem
#print axioms VerifiableInference.Desc.K1.k6_claims_respects
#print axioms VerifiableInference.Desc.K1.states_head2
#print axioms VerifiableInference.Desc.K1.states_head3
#print axioms VerifiableInference.Desc.K1.fwd_head_digits
#print axioms VerifiableInference.Desc.K1.hRd_paid2
