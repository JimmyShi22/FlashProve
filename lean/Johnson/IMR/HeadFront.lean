-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/HeadFront.lean: THE FRONT OF THE HEAD's CODE SWITCHING (the cut 339,
in front of "H:2"): ITS GROUP, AND THE OLD MESSAGES THAT IT KEEPS: at the proof file's seat, in the
goals' scope, from the fold's return alone.
  h1_front: behind an accept of "H:1" (the quiet step "H.0.front", then kind K7's sub-protocol):
    with x the front that the text makes of the state s in front: the head's own copy of the frame
    is x.f, the statement is x.st, the walk's state of the calls is s's.
  front_nums_head: the front fx that K2.frontAt makes at the cut 339: fx.f.group = 24; the statement
    has 25 groups; the group number 24 has no row, no member, no flag; fx.f.rows are the walk's
    frame's carried rows at the cut 338.
  olds_at_head: (switchKept fx.f.rows).toList = oldsAt 24: under Johnson/IMR/KeptJoin.lean's two
    premises.
NOT HERE: the finish's front.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USER: kind K2's files.
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.KeptJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.PlanWritten (proofSizedFull)
open ProofFile (Cl)

/-- **Behind an accept of "H:1".** -/
theorem h1_front {W : Verify.Public} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (IM.k7Block W 24).decide s rs gs = .ok t) :
    ∃ (x : _root_.Tw.K2.Front) (a : HeadOwn),
      _root_.Tw.K2.firstFront s.st s.check.frame = .ok x ∧ t.here = .head a ∧ a.fr = x.f ∧
      t.st = x.st ∧ t.check = s.check := by
  obtain ⟨m, a1, a2⟩ := andThen_yes h
  have hq : K2.headFrontQ W.H.tl s = .ok m :=
    ((guarded_yes _ (fun _ => false) _ rfl s _ _ m).1 a1).1
  have hc := (K2.headFrontQ_rest hq).2.2.2.2.1
  obtain ⟨x, s₁, a, k⟩ := (K2.headFrontQ_iff W.H.tl s m).1 hq
  obtain ⟨_, _, _, _, _, _, rfl⟩ := Kinds.Head.Law.Came.reply_record 24 W.hS.V a2
  refine ⟨x, { a with fr := x.f }, k.front, ?_, rfl, ?_, hc⟩
  · show m.here = _
    rw [k.out]
  · show m.st = _
    rw [k.out]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE FRONT AT THE HEAD's CODE SWITCHING: ITS GROUP AND ITS CARRIED ROWS.** tm: the state at the
cut 338. -/
theorem front_nums_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R Rm R₀ : List Fmt.RoundView} {C Cm C₀ : List VerifiableInference.Desc.OpenedColumn} {tm t₀ : S}
    (fm : foldBlocks 0 (c.blocksInOrder.take 338) (ProofFile.startS Z p) R C = .ok (tm, Rm, Cm))
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    {q : K2.P2} (hq : q.stands = .head) {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt q t₀ = some fx) :
    fx.f.group = 24 ∧ fx.st.groups.size = 25 ∧ fx.f.rows = tm.check.frame.rows ∧
      ∃ G, fx.st.groups[fx.f.group]? = some G ∧ G.rows = #[] ∧ G.members = #[] ∧ G.kept = #[] := by
  obtain ⟨Lk, b0, eL, e0, hj, -⟩ := IM.k7_sits hS hR O
  have i0 : c.blocksInOrder[338]? = some b0 := by
    have k := IM.hear_at_flat eL e0
    rwa [(IM.flatIx_scope hS hR O (by decide : 24 ≤ 24) 0).trans (by omega : _ = 338)] at k
  obtain ⟨rs0, gs0, d0⟩ := fold_next i0 fm f₀
  have d0' := (IM.k7_sits_yes hS hR O hj d0).1
  obtain ⟨x, a, hx, ha, ea, es, -⟩ := h1_front d0'
  have hc : tm.st.groups.size = 24 := count_at hS hR O 24 (by omega) tm Rm Cm fm
  obtain ⟨e1, e2⟩ := K2.firstFront_st hx
  obtain ⟨L0, G0, S0, g, fa⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 hx
  unfold K2.frontAt at h
  rw [hq, ha] at h
  obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
  have eg : a.fr.group = 24 := by rw [ea, e2, hc]
  refine ⟨eg, ?_, ?_, K2.freshGroup tm.check.frame.shape.code tm.check.frame.shape.maskCode, ?_,
    rfl, rfl, rfl⟩
  · show t₀.st.groups.size = 25
    rw [es, e1]
    simp [K2.withFresh, hc]
  · show a.fr.rows = _
    rw [ea, fa.out]
  · show t₀.st.groups[a.fr.group]? = _
    rw [eg, es, e1, ← hc]
    simp [K2.withFresh]

/-- **WHAT THE HEAD's CODE SWITCHING KEEPS.** -/
theorem olds_at_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hsh : Z.first.shape = proofSizedFull.request) {p : ProofFile.InstPub}
    {R R₃ R₀ : List Fmt.RoundView} {C C₃ C₀ : List VerifiableInference.Desc.OpenedColumn} {t₃ t₀ : S}
    (f₃ : foldBlocks 0 (c.blocksInOrder.take (14 * 23 + 2)) (ProofFile.startS Z p) R C = .ok (t₃, R₃, C₃))
    (hn : t₃.st.oracles.size = K2.n0At 23)
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    {q : K2.P2} (hq : q.stands = .head) {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt q t₀ = some fx) : (switchKept fx.f.rows).toList = K2.oldsAt 24 := by
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 338) f₀
  obtain ⟨-, -, er, -⟩ := front_nums_head hS hR O fm f₀ hq h
  rw [er]
  exact olds_rows hS hR O (l := 23) (by omega) (by omega) hsh f₃ hn fm

end

#print axioms h1_front
#print axioms front_nums_head
#print axioms olds_at_head

end Meaning.K2
