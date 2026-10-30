-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05HostPlanesAt.lean: kind K5: THE ROW K05_host_planes
(Johnson/Desc/First/Att/K05HostPlanes.lean) CALLED WITH ITS TWO DICTIONARY PREMISES PAID: hz :=
hz_at, h4 := cells_are_nu (Johnson/Desc/First/Att/K05PlanesWorth.lean): so that Lean holds that the
letters fit: St := First.S · seat := seatCO (parCOf A) · c := parCOf A · tl := A.seam.tl · S := A.S
· nu := the lookups' attNu at the witness's messages · M := matsOfMsg at the same messages.

IS IT EMPTY HERE? NO MEMBER IS SHOWN. A RULE OVER LETTERS.

Main name:
  `K05_host_planes_at`: K3WorthPlanes … at these letters. ITS PREMISES: K05_host_planes' own but hz
    and h4 · hz_at's.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05HostPlanes
import Johnson.Desc.First.Att.K05PlanesWorth

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.K9 (Readers segAt?)
open VerifiableInference.Desc.Sound (GQ Stated Mem seatTab msgsOf MsgT formsTQ)
open VerifiableInference.Desc.First.Look (Sent JAtt sigListCalls)
open VerifiableInference.OnPublicFiles (attMs attNu K3PlanesPaid K3RanAt K3WorthPlanes)
open K5Law (funsAt matsOf PosG K05_host_planes)

section
variable {Cells Tok : Type} (x : VerifiableInference.Desc.First.Look.Place) (A : Attention.Plan)
  (D : Sent) (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns A.seam.tl)) → Cb.Gl.E)

include Ex Wp α in
theorem K05_host_planes_at {Cl : Type} {gL : Forest.Heard}
    (fork : First.S → Option Fork) (heard : First.S → Option Forest.Heard) (form : Cl → Aff)
    {planes : ℕ → First.S → Except String (List Cl × First.S)} {bit : First.S → ℕ → ℕ → Aff}
    {pin : First.S → ℕ → Aff}
    (hPaid : K3PlanesPaid fork heard form A.S.cf.lmb planes bit pin) (sP : First.S)
    {r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)} {lid : ℕ} {cf : Attention.Cfg}
    {fs : Model.Forest.Shape}
    (hgeo : (parCOf A).geo = geoOf A.S) (hmats : (parCOf A).mats = matsOf A.seam.tl.mats)
    (hp : PosG (parCOf A).geo)
    (hr : readersOfK (seatCO (parCOf A)) (parCOf A) sP = some r)
    (hlook : (seatCO (parCOf A)).look sP = some (lookOf A.S.cf.lmb gL))
    (hr0 : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - A.S.cf.lmb) → (r.1 0 col).isSome)
    (hr1 : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - A.S.cf.lmb) → (r.1 1 col).isSome)
    (hrP : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - A.S.cf.lmb) → (r.2 col).isSome)
    (hs : Attention.shapeHid lid cf = .ok (A.S, fs)) (hm : MatsFit A.S A.seam.tl)
    (hsh : gL.shape = fs) (hrows : (A.seam.tl.mats.getD (A.S.cf.NAs + 2) {}).m = 2 ^ A.S.cf.lmb)
    (hbit : bit sP = fun e col => (r.1 e col).getD (Aff.ofConst zeroE))
    (hpin : pin sP = fun col => (r.2 col).getD (Aff.ofConst zeroE))
    (first : ℕ) {s : First.S} {w : Wit Cells Tok MsgT} {F0 : Fork} (hf : fork s = some F0)
    (hg : heard s = some gL) (clP : List Cl) (GP H : Fork) (hok : FoNums.ok gL.shape = true)
    (hran : K3RanAt fork heard gL F0 planes sP clP GP) (hl : _root_.Fo.Later GP H)
    -- hz_at's
    (ns : ℕ) (N : Nums) (Rd : Readers) (St : Stated) (own : List (ℕ × ℕ)) (arr : ℕ → ℕ → ℕ)
    (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem) (piece : ℕ)
    (run : String) (hi : ℕ) (ps : List (ℕ × (ℕ × ℕ))) (qs : List (ℕ × OracleShape))
    {a₀ : First.AttOwn} {pt : VerifiableInference.Desc.K9.Part} {L : LinkCtx}
    {R : VerifiableInference.Desc.K9.Read} (hsP : sP.here = .att a₀)
    (hU : U3At A (plannedK A) a₀.F)
    (q : formsTQ Rd St own piece run sP (seatTab D.codes arr ms w))
    (hRr : Rd.forms piece run sP = some R) (hsub : ∀ y ∈ clP, form y ∈ R.forms)
    (hlate : LateLaid pt.F R.late H (clP.map form))
    (hR : SymsOK x A.seam.tl D rad) (hmk : masksUpTo D x hi = true) (hhi : hi ≤ x.ns)
    (hone : ∀ (k : ℕ) (hk : k < (sigListCalls D rad x.link).length), maskMsg D x.link = some k →
      ((sigListCalls D rad x.link).get ⟨k, hk⟩).1.maskRows = 1)
    (hmem : ∀ k : Fin (sigListCalls D rad x.link).length,
      ReadMsg (ReadAddr A.seam.tl (clP.map form)) D x.link k.val →
      MemAt ms (sigListCalls D rad x.link) seat k)
    (hcov : ∀ k : Fin (sigListCalls D rad x.link).length,
      ReadMsg (ReadAddr A.seam.tl (clP.map form)) D x.link k.val →
      (k.val, seat k) ∈ ps ∧ (k.val, ((sigListCalls D rad x.link).get k).1) ∈ qs)
    (hcovM : ∀ (k : ℕ) (hk : k < (sigListCalls D rad x.link).length), maskMsg D x.link = some k →
      (k, ((sigListCalls D rad x.link).get ⟨k, hk⟩).1) ∈ qs)
    (hSt : StatedAtt St A (funsAt A) sP)
    (T : TieFacts x A D rad own ps qs hi sP L pt (clP.map form)) :
    K3WorthPlanes fork heard gL.shape A.S.cf.lmb first
      (fun w q => attNu x A.S A.seam.tl D rad seat arr w q) s w :=
  K05_host_planes (tl := A.seam.tl) (S := A.S) (gL := gL) fork heard form hPaid (seatCO (parCOf A))
    (parCOf A) sP hgeo hmats hp hr hlook hr0 hr1 hrP hs hm hsh hrows hbit hpin first
    (fun w q => attNu x A.S A.seam.tl D rad seat arr w q) hf hg clP GP H hok hran hl
    (matsOfMsg x A.seam.tl D rad (attMs x D rad seat arr w))
    (fun r _ c _ => cells_are_nu x A D rad seat arr w r c)
    (hz_at x A D rad Ex Wp α form clP ns N Rd St own arr seat ms w piece run hi ps qs H gL hsP hU q hRr
      hsub hlate hR hmk hhi hone hmem hcov hcovM hSt T)

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_host_planes_at
