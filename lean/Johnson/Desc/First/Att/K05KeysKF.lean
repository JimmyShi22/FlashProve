-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05KeysKF.lean: kind K5: EACH CALL's KEY VECTOR AT ITS KEY POINT IS THE TYPED
KEY FORM AT THE RULE VALUES: the one premise (hKF) that the clause "keys" of the kind's filling of
the table of joints leaves open (keys_of_todo, Johnson/Desc/First/Att/K05KeysClause.lean):
the lookup argument's item worth "keys" speaks of keysAt: the multilinear extension
of each call's vector of looked-up values at the call's point, a list; the kind's relation in front
(TodoJoin) of KF at the rule values, at the library's point, a function.

IS IT EMPTY HERE? Equations between terms, under three public premises. NO MEMBER IS SHOWN.

Main names:
  `zx_of_ends`, `keyPoint_is`: a call's point among the end values IS the list of the library's key
    point's coordinates: Fo.ends_zk · rho_of_ends, zy_of_ends
    (Johnson/Desc/First/Att/K05JoinHeard.lean) · Fo.zk_eq.
  `keysAt_is_KF`: **keysAt x.fs x.lm x.F.next (the layout's key vectors on the entries read off the
    messages m) rs c = KF … (rv … (attCells … m)) c**, at every call c, where the typed
    out-statement's point is the end values' two lists. BY: keyPoint_is · Fo.ext_top (the list's
    extension is the library's) · zkC_eq_zC (Johnson/Desc/First/Att/K05GuestKeysAt.lean) ·
    K5Law.kf_worth_fit (Johnson/Desc/First/Att/Claims/KeysFit.lean: the library's kfExt at
    L5.CallsFit) · attLay_K (Johnson/Desc/First/Look/K3CallerAtt.lean). NO NEW ALGEBRA.
  `hKF_at`: **hKF, to the letter**, at the letters of the lookup argument's files (K3AttGoodIn.lean)
    Kv w := forK … (zext (attMu … w)), ms := attMs …: the rounds rs carried to the promise's own rs₀
    by what the verifier has received (HeardIs.zx, HeardIs.zy).
PREMISES: FoNums.ok x.fs = true · x.fs.NC = 4 (both in the lookup argument's AttOK or its kin) ·
L5.CallsFit S x.fs (public: the kind's guard gives L5.CallsFit a.S a.fs at the plan's own letters:
guardList_gives, Johnson/Desc/First/Att/GuardNLaw.lean: so x.fs = a.fs is owed
beside it) · OutTies and HeardIs at rs₀ (the lookup argument's promise). The right side's table of
scales is written as TodoJoin writes it; Lean takes it for sclOf S by unfolding. Nothing is claimed
on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.K05AtCaller
import Johnson.Desc.First.Att.K05Meant
import Johnson.Desc.First.Att.K05JoinHeard
import Johnson.Desc.First.Att.K05Left
import Johnson.Desc.First.Look.K3AttGoodIn
import Johnson.Top.H.K3RowOut
import Johnson.Desc.First.Att.K05GuestKeysAt
import Johnson.Desc.First.Att.Claims.KeysFit
import OnBytes.Tie.Pv.Lookup.Port.FoJoin
import OnBytes.Tie.Pv.Lookup.Forest.FoJoinOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Road.L5 (dimOf callsOf sclOf tbOf)
open OnBytes.Ends (zkC iotaN)
open VerifiableInference.Desc.First.Look (Sent attSg JAtt attCells attLay msgAtt rawOf sigListCalls seatCalls attLay_K)
open VerifiableInference.OnPublicFiles (keysAt)

section Pts
variable {h : Forest.Shape} (H : FoNums.ok h = true) (lm jLK : ℕ) (rs : TwV.Rounds Cb.Gl.E) {pt : ℕ → Cb.Gl.E}
  (t2 : ∀ t, pt t = ((Fo.endsOf h lm jLK rs).zx ++ (Fo.endsOf h lm jLK rs).zy).getD t 0)

include H t2 in
theorem zx_of_ends : Fo.zx h.dT (Fo.rhoP (h.dT + h.rK) pt) = (Fo.endsOf h lm jLK rs).zx := by
  unfold Fo.zx
  rw [rho_of_ends H lm jLK rs t2, ← Fo.ends_zx_len h H lm jLK rs, List.take_left']
  rfl

include H t2 in
theorem keyPoint_is (c : ℕ) (hc : c < h.NC) :
    (Fo.endsOf h lm jLK rs).zk.getD c [] = (List.range (FoNums.io h c + h.dT)).map (zkC h pt c) := by
  rw [Fo.ends_zk h H lm jLK rs c hc, ← zx_of_ends H lm jLK rs t2, ← zy_of_ends H lm jLK rs t2]
  exact Fo.zk_eq h pt c ((Fo.ok_prem H).le c hc)

end Pts

section
variable (x : VerifiableInference.Desc.First.Look.Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E) (ns : ℕ) (N : Nums)

/-- **Each call's key vector at its point is the typed key form at the rule values.** -/
theorem keysAt_is_KF (hok : FoNums.ok x.fs = true) (h4 : x.fs.NC = 4)
    (hF : OnBytes.Road.L5.CallsFit S x.fs)
    {x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))} {rs : TwV.Rounds Cb.Gl.E}
    (t2 : ∀ t, x0.2.1.pt t = ((Fo.endsOf x.fs x.lm x.F.next rs).zx ++
      (Fo.endsOf x.fs x.lm x.F.next rs).zy).getD t 0)
    (m : (attSg x D rad).Msg) (c : Fin 4) :
    keysAt x.fs x.lm x.F.next
        (forK Cb.Gl.E (attLay S x.fs x.lm x.F.next x.ns tl) ()
          (zext (msgAtt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) tl x.ns m))) rs c.val =
      KF (scl := (meantQ (attBase x S tl D rad) (attLin0 x S tl D rad) ns N
          (attQ0 x S tl D rad Ex Wp α ns N)).scl)
        (dimOf S) (callsOf x.fs) (pubOfZ Cb.Gl.E x0.2.1.pt)
        (rv (dimOf S) (callsOf x.fs) (pubOfZ Cb.Gl.E x0.2.1.pt) (attCells x S tl D rad m)) c := by
  have hc : c.val < x.fs.NC := by rw [h4]; exact c.isLt
  obtain ⟨i1, _⟩ := OnBytes.Road.L5.callsFit_iota hF c
  have hD : (callsOf x.fs).Dk ≤ (callsOf x.fs).a c :=
    letI : Scl := sclOf S
    (OnBytes.Road.L5.callsFit_ok hF).le c
  have ha : FoNums.io x.fs c.val + x.fs.dT = (callsOf x.fs).a c := by
    have h1 : FoNums.io x.fs c.val = (callsOf x.fs).a c - (callsOf x.fs).Dk := i1
    have h3 : (callsOf x.fs).Dk = x.fs.dT := rfl
    omega
  have R := K5Law.kf_worth_fit hF (tbOf S) (pubOfZ Cb.Gl.E x0.2.1.pt) (attCells x S tl D rad m)
    (v := rv (dimOf S) (callsOf x.fs) (pubOfZ Cb.Gl.E x0.2.1.pt) (attCells x S tl D rad m))
    (fun _ _ => rfl) c
  refine Eq.trans ?_ R.symm
  unfold keysAt
  rw [keyPoint_is hok x.lm x.F.next rs t2 c.val hc, Fo.ext_top, ha, zkC_eq_zC hF c]
  refine Blocks.ext_congr (fun X _ => ?_) _
  exact attLay_K (S := S) (tl := tl) x.fs x.lm x.F.next x.ns _ c X

/-- **hKF, to the letter.** -/
theorem hKF_at {Cells Tok : Type} (hok : FoNums.ok x.fs = true) (h4 : x.fs.NC = 4)
    (hF : OnBytes.Road.L5.CallsFit S x.fs)
    {x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))} {g₀ : Forest.Heard} {F₁ : Fork}
    {rs₀ : TwV.Rounds Cb.Gl.E} {ι : Fo.Pl → Option (JAtt x.ns tl)}
    (T : OutTies x0 (Fo.endsOf x.fs x.lm x.F.next rs₀) ι)
    (hI₀ : Fo.HeardIs Reading.gl g₀ F₁ (Fo.endsOf x.fs x.lm x.F.next rs₀))
    (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (w : VerifiableInference.Desc.Wit Cells Tok VerifiableInference.Desc.Sound.MsgT) :
    ∀ (rs : TwV.Rounds Cb.Gl.E) (F' : Fork),
      Fo.HeardIs Reading.gl g₀ F' (Fo.endsOf x.fs x.lm x.F.next rs) → ∀ c : Fin 4,
        keysAt x.fs x.lm x.F.next
            (forK Cb.Gl.E (attLay S x.fs x.lm x.F.next x.ns tl) ()
              (zext (VerifiableInference.OnPublicFiles.attMu x tl D rad seatT arr w))) rs c.val =
          KF (scl := (meantQ (attBase x S tl D rad) (attLin0 x S tl D rad) ns N
              (attQ0 x S tl D rad Ex Wp α ns N)).scl)
            (dimOf S) (callsOf x.fs) (pubOfZ Cb.Gl.E x0.2.1.pt)
            (rv (dimOf S) (callsOf x.fs) (pubOfZ Cb.Gl.E x0.2.1.pt)
              (attCells x S tl D rad (VerifiableInference.OnPublicFiles.attMs x D rad seatT arr w))) c := by
  intro rs F' hI c
  refine keysAt_is_KF x S tl D rad Ex Wp α ns N hok h4 hF (fun t => ?_) _ c
  rw [T.pt t, ← hI₀.zx, ← hI₀.zy, ← hI.zx, ← hI.zy]

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.keyPoint_is
#print axioms VerifiableInference.Desc.First.Att.P.keysAt_is_KF
#print axioms VerifiableInference.Desc.First.Att.P.hKF_at
