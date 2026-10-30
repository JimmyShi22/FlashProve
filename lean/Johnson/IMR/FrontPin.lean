-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FrontPin.lean: OF THE FRONT THAT THE CODE SWITCHING's TEXT MAKES OF
THE VERIFIER's STATE IN FRONT OF IT (K2.frontAt, Johnson/Top/H0/K2Hears/Long.lean): WHAT IS THE
PLAN's, AT THE LINKS 1 TO 23 AND AT THE HEAD's LINK OF THE PROOF FILE's SEAT, IN THE GOALS' SCOPE,
FROM THE FOLD's RETURN ALONE. "The state": the value that the description's fold carries from block
to block.
FOR: the test that kind K2's files ask in front of their law (Johnson/Top/H0/K2Hands/FramePin.lean:
pinB, numsB, headLinkB). HERE, IN THE PLAN's OWN WORDS: pinB's clause 1 (the codes), 4 to 7 (the
target, whole), 8 to 10 (the carried rows' two codes' numbers; two mask rows); headLinkB.
  laid_at: at each of the 25 links the state behind "laid" stands between the links and its frame
    stands at that link.
  front_pin_link (1 ≤ l < 24; the cut 14 l + 2), front_pin_head (the cut 339): the sentences.
  h1_check: the place "H:1" leaves the walk's state of the calls.
NOT HERE: pinB's clauses 2, 3, 11 (the kept old messages' shapes; below the number of messages; the
count of kept rows); numsB, whole; the finish's place. The written front is not named: its target
and its carried rows are to be held against these terms by whoever has it.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USER: kind K2's files.
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.WalkGivesAt
import Johnson.Goal.Meaning.K2Share.FrontNotices
import Johnson.Top.H0.K2Hands.FramePin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Pub Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **Behind "laid", at each of the 25 links.** -/
theorem laid_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    t₀.atBetween = true ∧ t₀.check.frame.link = l := by
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨LkF, f, bL, bB, bC, -, -, -, -, efl, hlay, -, iL, -, dL, -⟩ := hfr l hl
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 14 * l + 1) f₀
  obtain ⟨rsL, gsL, dl⟩ := fold_next iL fm f₀
  rw [dL] at dl
  have hlf := ((hlay tm t₀).1 dl).1
  rw [efl] at hlf
  obtain ⟨et, hBm, -, hk⟩ := Johnson.Desc.First.Walk.Law.layFront_ok hlf
  rw [et]
  exact ⟨hBm, hk⟩

theorem rows_of_pub {sh : Params.ReqShape} {f : ReqFrame} (Fp : FramePub sh f) (h : f.link ≠ 0) :
    f.rows.code = sh.code ∧ f.rows.maskCode = sh.maskCode ∧ f.rows.masks = 2 :=
  Fp.rows.2.resolve_left h

/-- **THE FRONT AT A LINK's SWITCH, 1 ≤ l < 24.** -/
theorem front_pin_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24) {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView}
    {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    {q : K2.P2} (hq : q.stands = .link) {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt q t₀ = some fx) :
    fx.st.codes = Z.first.codes ∧ fx.st.oracles = t₀.st.oracles ∧
      fx.T = K2.targetAt Z.first.shape l ∧ fx.others = K2.othersAt Z.first.shape l ∧
      fx.f.link = l ∧ fx.f.rows = t₀.check.frame.rows ∧
      fx.f.rows.code = Z.first.shape.code ∧ fx.f.rows.maskCode = Z.first.shape.maskCode ∧
      fx.f.rows.masks = 2 ∧ K2Hands.headLinkB t₀ = true := by
  obtain ⟨hB, hk⟩ := laid_at hS hR O (by omega : l < 25) f₀
  have hlen : 14 * l + 2 ≤ (frontOf c).length := by
    have k := draw_in_front hS hR O (l := l) (i := 0) (by omega) (by decide)
    omega
  have Rr : RecAll Z.first.codes Z.first.shape t₀ := open_recAll hS hR O (by omega) hlen f₀
  have hf := K2.front_of_link hq h
  obtain ⟨-, c1, c2, c3⟩ := K2.link_front hf
  obtain ⟨n1, n2, -⟩ := K2.link_notices hf Rr.walk hk
  obtain ⟨r1, r2, r3⟩ := rows_of_pub Rr.walk (by omega)
  refine ⟨c1.trans Rr.codes, c2, n1, n2, (K2.front_carried hf).2.trans hk, c3, by rw [c3, r1],
    by rw [c3, r2], by rw [c3, r3], ?_⟩
  unfold K2Hands.headLinkB
  have hb : t₀.here = .between := by
    unfold S.atBetween at hB
    split at hB
    · assumption
    · cases hB
  rw [hb]

/-- The place "H:1" leaves the walk's state of the calls. -/
theorem h1_check {W : Verify.Public} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (IM.k7Block W 24).decide s rs gs = .ok t) :
    t.check = s.check := by
  obtain ⟨m, a1, a2⟩ := andThen_yes h
  have hq : K2.headFrontQ W.H.tl s = .ok m :=
    ((guarded_yes _ (fun _ => false) _ rfl s _ _ m).1 a1).1
  obtain ⟨a, -, -, -, -, -, -, f6⟩ := K2.headFrontQ_fr hq
  obtain ⟨_, _, _, _, _, _, rfl⟩ := Kinds.Head.Law.Came.reply_record 24 W.hS.V a2
  exact f6

/-- **THE FRONT AT THE HEAD's SWITCH.** -/
theorem front_pin_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    {q : K2.P2} (hq : q.stands = .head) {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt q t₀ = some fx) :
    fx.st.codes = Z.first.codes ∧ fx.st.oracles = t₀.st.oracles ∧
      fx.T = K2.targetAt Z.first.shape 24 ∧ fx.others = K2.othersAt Z.first.shape 24 ∧
      fx.f.link = 24 ∧
      fx.f.rows.code = Z.first.shape.code ∧ fx.f.rows.maskCode = Z.first.shape.maskCode ∧
      fx.f.rows.masks = 2 ∧ K2Hands.headLinkB t₀ = true := by
  have ix : ∀ i, IM.flatIx c 24 i = 338 + i := fun i =>
    (IM.flatIx_scope hS hR O (by decide) i).trans (by omega)
  obtain ⟨Lk, b0, eL, e0, hj, -⟩ := IM.k7_sits hS hR O
  have i0 : c.blocksInOrder[338]? = some b0 := by
    have k := IM.hear_at_flat eL e0
    rwa [ix 0] at k
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 338) f₀
  obtain ⟨rs0, gs0, d0⟩ := fold_next i0 fm f₀
  have d0' := (IM.k7_sits_yes hS hR O hj d0).1
  obtain ⟨a, ha, -, -, o3⟩ := h1_headFr d0'
  have hk : t₀.check.frame.link = 24 := by
    rw [h1_check d0']
    exact (laid_at hS hR O (l := 24) (by decide) fm).2
  have hlen : 339 ≤ (frontOf c).length := by
    have k := draw_in_front hS hR O (l := 24) (i := 1) (by decide) (by decide)
    omega
  have Rr : RecAll Z.first.codes Z.first.shape t₀ := open_recAll hS hR O (by decide) hlen f₀
  have Fa : FramePub Z.first.shape a.fr := Rr.frames _ (by unfold framesIn; rw [ha]; simp)
  obtain ⟨r1, r2, r3⟩ := rows_of_pub Fa (by rw [o3, hk]; decide)
  unfold K2.frontAt at h
  rw [hq, ha] at h
  obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
  refine ⟨Rr.codes, rfl, ?_, ?_, o3.trans hk, r1, r2, r3, ?_⟩
  · show G.target = _
    unfold K2.targetAt
    rw [Rr.walk.groups, hk] at hG
    rw [Array.getD_eq_getD_getElem?, hG]
    rfl
  · show ReqFrame.notices (t₀.check.frame.atMoment 0) ++
      #[foldMaskNotice (t₀.check.frame.foldShape t₀.check.frame.link {})] = _
    unfold K2.othersAt
    rw [K2.atMoment_pub Rr.walk hk, hk, K2.foldShape_pub Rr.walk 24]
  · unfold K2Hands.headLinkB
    rw [ha]
    simp [o3]

#print axioms laid_at
#print axioms front_pin_link
#print axioms front_pin_head

end Meaning.K2
