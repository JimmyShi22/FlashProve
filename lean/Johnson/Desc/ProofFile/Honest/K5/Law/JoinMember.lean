-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/JoinMember.lean: CONDITIONAL: at the member of a thread that
stands at an attention segment's own rounds: the form that the lookup's run "join" gathers on the
segment's four key forms, at the state behind the lay, is worth 0. It is `join_of_scalars`
(Johnson/Desc/K5/Honest/Law/JoinValues.lean) at the member's letters: the challenges at which the
three sums were sent are those in front of their parts of the row; that the verifier's function of
the points returns there, and that the key points there are the state's, come from the half's seat
and the ties. A joining of lemmas; no algebra is in this file.

Main names:
  `frontAt Z heard ds q`   the prover's challenges in front of part q of the row
  `divIn_front`     what the division's summand shares is made in front of every round
  `join_zero_member`   **the gathered form is worth 0**

THE PREMISES OF `join_zero_member`. Hs (`K5Seated`), Sc (`K5Script`), hT (the thread in front), hd
(the challenges fit), e (the open segment): as in the files on the member's slots. hP: the seat's
public data are the plan's shape and own numbers. Pu, hid, PL: public; from the library's head on
the public input (Johnson/Desc/K5/Honest/Law/PublicAtHead.lean). hk, hj: the key forms and the
lookup's text return at the state behind the lay. THE TWO ON VALUES: hs (`ScalarsAt`): under each
named scalar's slot the world holds the prover's scalar, read; hm (`JoinMeets`): the lookup's half
of the join.
Limits. None of the premises is shown to be met. The ties (`K5Script`) are a premise's form that
is not shown.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Starts
import Johnson.Desc.K5.Honest.Law.JoinValues

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork World)
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ)
open VerifiableInference.Desc.First.Att.P (Par behind geoOf)
open H2K5.Honest (Pub5 Chal K5In PublicAll ScalarsAt JoinMeets scalarOf sK sSE iSE tOf divIn ptsOf
  DivIn)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}
  {A : OnBytes.Attention.Plan} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

/-- The prover's challenges in front of part q of the row. -/
def frontAt (Z : Seat5) (heard ds : List Fmt.Drawn) (q : Nat) : Chal :=
  chalOf Z (heard ++ ds.take (H2K5.Honest.firstOf Z.P.x q))

section
variable (Hs : K5Seated T b cells Z p blk) (Sc : K5Script T b cells Z A blk own rdOf)
  {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
  (hT : Thr T b k s m E) (hd : drawsFit blk.rounds ds = true)
  {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att)
include Hs Sc hT hd e

/-- **What the division's summand shares is made in front of every round.** Conditional: the seat,
the ties, the thread in front; the place has the list of the remainders' low bits. -/
theorem divIn_front {wl : VerifiableInference.Desc.First.Att.P.UnitG}
    (hw : Z.P.g.single .wl = some wl) (n : Nat) :
    ∃ Dv, divIn Z.P (chalOf Z (m.st.heard ++ ds.take n)) = some Dv := by
  obtain ⟨q, hq⟩ := pts_front Hs Sc hT hd e n
  unfold divIn
  rw [hq, hw]
  exact ⟨_, rfl⟩

/-- **The form that the lookup's text returns on the key forms, at the state behind the lay, is
worth 0**, in any world W over the field of the challenges. Conditional; the premises are listed in
the file's head. -/
theorem join_zero_member {W : World Cb.Gl.E} (hP : Z.P = ⟨A.S, A.own⟩)
    (Pu : PublicAll ⟨A.S, A.own⟩ A.fs) {lid : Nat}
    (hid : OnBytes.Attention.shapeHid lid A.S.cf = Except.ok (A.S, A.fs))
    (PL : K5Law.PlanLaw A.S.cf A.S A.fs) (w : K5In)
    {hd5 : VerifiableInference.Desc.First.Att.P.Heard} {G : Fork} {kf : Array Aff}
    (hk : VerifiableInference.Desc.First.Att.P.keysOfK
      (VerifiableInference.Desc.First.Att.P.seatCO (VerifiableInference.Desc.First.Att.P.parCOf A))
      (VerifiableInference.Desc.First.Att.P.parCOf A) (behind s att hd5 G) = some kf)
    (tb : Inst.Model.Tables)
    (hs : ∀ i n, VerifiableInference.Desc.First.Att.P.inOf
        (VerifiableInference.Desc.First.Att.P.seatCO
          (VerifiableInference.Desc.First.Att.P.parCOf A))
        (VerifiableInference.Desc.First.Att.P.parCOf A) (behind s att hd5 G) = some (i, n) →
      ∀ a1 a2 pM pD kM kD cM cD, hd5.remainders[0]? = some a1 → hd5.remainders[1]? = some a2 →
        i.p.planes[0]? = some pM → i.p.planes[1]? = some pD → i.p.scores[0]? = some kM →
        i.p.scores[1]? = some kD → i.p.planes[kM.claim]? = some cM →
        i.p.planes[kD.claim]? = some cD →
        ScalarsAt W (OnBytes.Road.L5.dimOf A.S) a1 a2 kM kD i.p.d
          (scalarOf Reading.gl (geoOf A.S) w pM pD cM cD kM kD i.p.d
            (sK ⟨A.S, A.own⟩ w (frontAt Z m.st.heard ds 0) 0).total
            (sK ⟨A.S, A.own⟩ w (frontAt Z m.st.heard ds 1) 1).total
            (sSE ⟨A.S, A.own⟩ w (frontAt Z m.st.heard ds (iSE Z.P.x))).total))
    {gL : OnBytes.Model.Forest.Heard} {y : Aff × Fork × OnBytes.K.Kc.Tape}
    (hj : VerifiableInference.Desc.First.Look.joinF gL kf G [] = some y)
    (hm : ∀ g, att.g = some g → JoinMeets Reading.gl W gL fun c =>
      Blocks.ext ((OnBytes.Road.L5.callsOf A.fs).a c)
        (Inst.Model.AttSeg.keyVec (scl := OnBytes.Road.L5.sclOf A.S) (OnBytes.Road.L5.dimOf A.S) tb
          (tOf Reading.gl w) c)
        ((OnBytes.Road.L5.callsOf A.fs).zC c (OnBytes.Slice.readV (g.zx ++ g.zy)))) :
    y.1.value Reading.gl W = 0 := by
  obtain ⟨g, hg, K3, _⟩ := Sc.keyTie k s m E hT att e
  obtain ⟨g', hg', hz, _⟩ := key_at Sc hT e hd
  obtain rfl : g = g' := Option.some.inj (hg.symm.trans hg')
  obtain ⟨_, _, _, _, wl, _, _, U, _⟩ := Pu.units
  have hw : Z.P.g.single .wl = some wl := by
    rw [hP]
    exact U.sWl
  obtain ⟨p0, h0⟩ := pts_front Hs Sc hT hd e (H2K5.Honest.firstOf Z.P.x 0)
  obtain ⟨p1, h1⟩ := pts_front Hs Sc hT hd e (H2K5.Honest.firstOf Z.P.x 1)
  obtain ⟨Dv, hE⟩ := divIn_front Hs Sc hT hd e hw (H2K5.Honest.firstOf Z.P.x (iSE Z.P.x))
  have h0' : ptsOf ⟨A.S, A.own⟩ (frontAt Z m.st.heard ds 0) = some p0 := by
    rw [← hP]
    exact h0
  have h1' : ptsOf ⟨A.S, A.own⟩ (frontAt Z m.st.heard ds 1) = some p1 := by
    rw [← hP]
    exact h1
  have hE' : divIn ⟨A.S, A.own⟩ (frontAt Z m.st.heard ds (iSE Z.P.x)) = some Dv := by
    rw [← hP]
    exact hE
  exact H2K5.Honest.join_of_scalars A Pu hid PL w hk hg K3 (c0 := frontAt Z m.st.heard ds 0)
    (c1 := frontAt Z m.st.heard ds 1) (cE := frontAt Z m.st.heard ds (iSE Z.P.x)) (hz _) (hz _)
    (hz _) h0' h1' hE' tb hs hj (hm g hg)

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.divIn_front
#print axioms ProofFile.Honest.K5.join_zero_member
