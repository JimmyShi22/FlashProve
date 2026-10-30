-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/JoinPaid.lean: CONDITIONAL, among others on the ties
(`K5Script`), WHICH ARE NOT SHOWN: at the member of a thread that stands at an attention
segment's own rounds: the form that the lookup's run "join" gathers on the segment's four key forms,
at the state behind the lay, is worth 0 in the world of the table's sentence on that form. It is
`join_zero_member` (Johnson/Desc/ProofFile/Honest/K5/Law/JoinMember.lean) with one of its two
premises on values, on what lies under the named scalars' slots, drawn from `scalars_at`
(Johnson/Desc/ProofFile/Honest/K5/Law/ScalarsAtK5.lean). THAT LAW HAS PREMISES ON VALUES OF ITS OWN:
the ties' field on the mask row, and hD. LEFT ON VALUES: these two, and the lookup's half of the
join (`JoinMeets`, Johnson/Desc/K5/Honest/Law/Join.lean). A joining; calls alone.

Main name:
  `join_zero_paid`  **the gathered form is worth 0**

THE PREMISES. Hs (`K5Seated`), Sc (`K5Script`: the ties, which are not shown), hT (the thread in
front), hd (the challenges fit), hM (the prover's side of the step), e (the open segment), hD (the
world's mask row is the one read off the witness), hz (the ledger in front is sized), hh (the
hearing of the segment's own rounds returns on the rounds played). hP: the seat's public data are
the plan's shape and own numbers. Pu, hid, PL: public; from the library's head on the public input.
hk, hj: the key forms and the lookup's text return at the state behind the lay. hm: `JoinMeets`.
Limits. None of the premises is shown to be met.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.JoinMember
import Johnson.Desc.ProofFile.Honest.K5.Law.ScalarsAtK5

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S noDigest)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ worldOwn)
open VerifiableInference.Desc.First.Att.P (Par behind hear)
open H2K5.Honest (PublicAll JoinMeets tOf)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}
  {A : OnBytes.Attention.Plan} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

/-- **The form that the lookup's text returns on the key forms, at the state behind the lay, is
worth 0 in the sentence's world**, from the lookup's half of the join. Conditional; the premises are
listed in the file's head. -/
theorem join_zero_paid (Hs : K5Seated T b cells Z p blk)
    (Sc : K5Script T b cells Z A blk own rdOf) {k : Coins Bk} {s : First.S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn} (hT : Thr T b k s m E)
    (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols)
    {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att)
    (hP : Z.P = ⟨A.S, A.own⟩) (Pu : PublicAll ⟨A.S, A.own⟩ A.fs) {lid : Nat}
    (hid : OnBytes.Attention.shapeHid lid A.S.cf = Except.ok (A.S, A.fs))
    (PL : K5Law.PlanLaw A.S.cf A.S A.fs) {dc : List Fmt.Drawn} {D : Bound GQ}
    (hD : MaskIs T own rdOf k s att m dc D) (hz : OnBytes.Model.Road.Sized att.F) {G : Fork}
    {hd5 : VerifiableInference.Desc.First.Att.P.Heard} {rest : List Fmt.RoundView} {lead : Nat}
    (hh : hear p.own (att.F, (roundsOf y.1).map noDigest, 0) = some (hd5, G, rest, lead))
    {kf : Array Aff}
    (hk : VerifiableInference.Desc.First.Att.P.keysOfK
      (VerifiableInference.Desc.First.Att.P.seatCO (VerifiableInference.Desc.First.Att.P.parCOf A))
      (VerifiableInference.Desc.First.Att.P.parCOf A) (behind s att hd5 G) = some kf)
    (tb : Inst.Model.Tables) {gL : OnBytes.Model.Forest.Heard}
    {v : Aff × Fork × OnBytes.K.Kc.Tape}
    (hj : VerifiableInference.Desc.First.Look.joinF gL kf G [] = some v)
    (hm : ∀ g, att.g = some g →
      JoinMeets Reading.gl (worldOwn (behindPart s att G) [] D) gL fun c =>
        Blocks.ext ((OnBytes.Road.L5.callsOf A.fs).a c)
          (Inst.Model.AttSeg.keyVec (scl := OnBytes.Road.L5.sclOf A.S) (OnBytes.Road.L5.dimOf A.S)
            tb (tOf Reading.gl (inOf Z.P.S Z.link (cells m.st.input.trace))) c)
          ((OnBytes.Road.L5.callsOf A.fs).zC c (OnBytes.Slice.readV (g.zx ++ g.zy)))) :
    v.1.value Reading.gl (worldOwn (behindPart s att G) [] D) = 0 := by
  cases Z with
  | mk link P base keyAt =>
    have hP' : P = ⟨A.S, A.own⟩ := hP
    subst hP'
    refine join_zero_member Hs Sc hT hd e rfl Pu hid PL _ hk tb ?_ hj hm
    intro i n hin a1 a2 pM pD kM kD cM cD b1 b2 e0 e1 s0 s1 q0 q1
    obtain ⟨_, _, _, g, l, _, hg, _, hp, _⟩ := VerifiableInference.Desc.First.Att.P.inOf_behind hin
    exact scalars_at Hs Sc Pu.counted hT hd hM e hD hz hh hg hp Pu.sized b1 b2 s0 s1 e0 e1 q0 q1

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.join_zero_paid
