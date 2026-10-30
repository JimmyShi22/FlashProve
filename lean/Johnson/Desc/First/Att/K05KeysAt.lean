-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05KeysAt.lean: kind K5: THE LOOKUP's CLAIM "the join" AGAINST THE KIND's TYPED JOIN: toward the clause "keys" of K5FillIns (Att/K05Closes.lean): K5's half of the second of two identities.

The chain of the clause:  claimJoin h lm first rs ν kf  =  joinVal (joinPubOf h lm first rs) kf (AffK.val (cEndF, cEndC) ν)   [the lookups': Johnson/Top/H/K3JoinVal.lean: claimJoin_joinVal]
                                                          =  joinVal (Q.q x0) kf ((Q.ce x0).val msg)                            [HERE: join_typed]
                          and, at kf := the key vectors at their points, = the kind's TodoJoin's left side                      [another file].
How. Under HeardIs (what the verifier has received from the lookup argument stands for the rounds rs):
  joinPub_is: joinPubOf h lm first rs IS the join's public letters read off what was received (K5Law.qAt): alpha, theta: HeardIs' fields; the calls' weights: Fo.ends_e; the padding's term: heard_empty with Fo.eqTab_top.
  cEnd_is: AffK.val (cEndF, cEndC) ν IS the worth of the received form cEnd at the ledger's own world, where ν reads the mask row at the masks: HeardIs.cEnd; cEndF is cEndInc times −1.
  Both right sides do not name rs. Then hjv_of_heard (Att/K05JoinAtt.lean), at the rounds rs₀ to which the typed statement x0 is tied.
Main names: joinPub_is · cEnd_is · join_typed.
IS IT EMPTY HERE? Equations under HeardIs, which is shown of nothing here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3JoinVal
import Johnson.Desc.First.Att.K05JoinAtt
import Johnson.Desc.First.Att.K05Left

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg Finset
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Ends (eC tauN t0N)
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask att_ok)

section Fields
variable {h : Forest.Shape} (H : FoNums.ok h = true) (lm jLK : ℕ) (rs : TwV.Rounds Cb.Gl.E) {gL : Forest.Heard} {F' : Fork}
  (hI : Fo.HeardIs Reading.gl gL F' (Fo.endsOf h lm jLK rs))

include H hI in
/-- **The lookup's public letters of the join are those read off what was received.** -/
theorem joinPub_is (nc : h.NC = 4) (hsh : gL.shape = h) : Fo.joinPubOf h lm jLK rs = K5Law.qAt Reading.gl gL := by
  have t2 : ∀ t, Fo.ptL ((Fo.endsOf h lm jLK rs).zx ++ (Fo.endsOf h lm jLK rs).zy) t =
      ((Fo.endsOf h lm jLK rs).zx ++ (Fo.endsOf h lm jLK rs).zy).getD t 0 := fun _ => rfl
  have hz := zy_of_ends H lm jLK rs t2
  unfold Fo.joinPubOf K5Law.qAt
  congr 1
  · exact hI.alpha.symm
  · exact hI.theta.symm
  · funext c
    have e := Fo.eK_eq (h := h) (pt := Fo.ptL ((Fo.endsOf h lm jLK rs).zx ++ (Fo.endsOf h lm jLK rs).zy)) c.1
    rw [hz] at e
    rw [heard_eC H lm jLK rs t2 hI c.1 (by rw [nc]; exact c.2)]
    exact e
  · rw [heard_empty H lm jLK rs t2 hI hsh, Finset.sum_Ico_eq_sum_range, hI.alpha]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : h.NT + i < 2 ^ h.rK := by
      have := Finset.mem_range.1 hi
      omega
    have e := Fo.eqTab_top h (Fo.ptL ((Fo.endsOf h lm jLK rs).zx ++ (Fo.endsOf h lm jLK rs).zy)) _ hi'
    rw [hz] at e
    rw [e]
    congr 2
    unfold Fo.padKeyK
    simp only [Nat.cast_zero, zero_mul, add_zero]
    rfl

include hI in
/-- **The typed end of the key side is worth what the received form is worth.** -/
theorem cEnd_is (ν : Fo.Pl → Cb.Gl.E) (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    (hν : ∀ pc ∈ (Fo.endsOf h lm jLK rs).cEndInc, ν pc.1 = Fo.muOf mask pc.1) :
    Fo.AffK.val ((Fo.endsOf h lm jLK rs).cEndF, (Fo.endsOf h lm jLK rs).cEndC) ν =
      gL.cEnd.value Reading.gl (F'.worldOf Reading.gl mask entry) := by
  rw [((hI.cEnd F' (Fo.Later.refl _)).2 mask entry)]
  have eF : (Fo.endsOf h lm jLK rs).cEndF = TwV.scale (-1) (Fo.endsOf h lm jLK rs).cEndInc := rfl
  have b : Fo.evalL ν (Fo.endsOf h lm jLK rs).cEndInc = Fo.evalL (Fo.muOf mask) (Fo.endsOf h lm jLK rs).cEndInc := by
    unfold Fo.evalL
    exact congrArg List.sum (List.map_congr_left fun pc hpc => congrArg (pc.2 * ·) (hν pc hpc))
  show Fo.evalL ν (Fo.endsOf h lm jLK rs).cEndF + (Fo.endsOf h lm jLK rs).cEndC = _
  rw [eF, Fo.evalL_scale, b]
  ring

end Fields

section Typed
variable (x : VerifiableInference.Desc.First.Look.Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E) (ns : ℕ) (N : Nums)

local notation "cA" => attCaller x S tl D rad Ex Wp
local notation "P0A" => attBase x S tl D rad
local notation "ΛA" => attLin x S tl D rad Ex Wp α ns N
local notation "QA" => meantQ P0A (attLin0 x S tl D rad) ns N (attQ0 x S tl D rad Ex Wp α ns N)

/-- **The lookup's join at ITS letters is the kind's typed join at OURS**, at every four values kf. rs: any rounds for which what was received stands; rs₀: the rounds to which the typed statement x0 is tied. -/
theorem join_typed {set : Params.Setting} (H : AttOK set x S tl D rad) (rs rs₀ : TwV.Rounds Cb.Gl.E)
    (ι : Fo.Pl → Option (JAtt x.ns tl)) (hι : ∀ j, ι (.mask j) = some (enMask x.ns tl j)) {gL : Forest.Heard} {F' : Fork}
    (hI : Fo.HeardIs Reading.gl gL F' (Fo.endsOf x.fs x.lm x.F.next rs))
    (hI₀ : Fo.HeardIs Reading.gl gL F' (Fo.endsOf x.fs x.lm x.F.next rs₀)) (hsh : gL.shape = x.fs)
    {x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))} (m : (attSg x D rad).Msg)
    (T : OutTies x0 (Fo.endsOf x.fs x.lm x.F.next rs₀) ι) (ν : Fo.Pl → Cb.Gl.E)
    (hν : ∀ j, j < x.ns → ν (.mask j) = (ΛA).maskOf m j) (kf : Fin 4 → Cb.Gl.E) :
    joinVal (Fo.joinPubOf x.fs x.lm x.F.next rs) kf
        (Fo.AffK.val ((Fo.endsOf x.fs x.lm x.F.next rs).cEndF, (Fo.endsOf x.fs x.lm x.F.next rs).cEndC) ν) =
      joinVal ((QA).q x0) kf (((QA).ce x0).val ((closedOf P0A ΛA ns N).msg m)) := by
  have ok : FoNums.ok x.fs = true := att_ok Ex Wp H cA (List.mem_singleton.2 rfl)
  rw [joinPub_is ok x.lm x.F.next rs hI H.four hsh,
    cEnd_is x.lm x.F.next rs hI ν ((ΛA).maskOf m) (fun _ _ _ => 0) fun pc hpc => by
      obtain ⟨j, hj, _, h2⟩ := Fo.Slots.onMasksIn_keyTop x.fs x.lm x.F.next rs pc hpc
      rw [hj]
      exact hν j (lt_of_lt_of_le h2 H.masksIn)]
  exact hjv_of_heard x S tl D rad Ex Wp α ns N H rs₀ ι hι hI₀ hsh (fun _ _ _ h => h) rfl (fun _ _ _ => 0) m T.theta T.pt T.mf
    T.tg kf

end Typed

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.joinPub_is
#print axioms VerifiableInference.Desc.First.Att.P.cEnd_is
#print axioms VerifiableInference.Desc.First.Att.P.join_typed
