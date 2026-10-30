-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/LookClaims.lean

Under PremF (Johnson/HonestTrace/LookDefs.lean), the claims of a sub-proof's lookup (Fo.claimsOf,
OnBytes/Tie/Pv/Lookup/Forest/FoClaims.lean) are 0 at the rounds rsF of LookDefs.lean, if three
statements on plain numbers hold of these rounds. The three are premises of this file.

The setting. LookDefs.lean defines, over TwV's public numbers N alone, the rounds rsT and the value
trT of TwV.Trace; and at the numbers Fo.numsF h lm jLK θ of a sub-proof's lookup the data dataF, the
rounds rsF (rsT behind the round in which θ is drawn, where there are several calls) and the
premises PremF. The list Fo.claimsOf reads rounds through Fo.thetaOf, Fo.afterShift, Fo.forN,
Fo.forTrace and Fo.endsOf. Johnson/Top/H/K3RowOut.lean splits the list into K3Rows, K3Planes and
K3Keys. Below, D stands for dataF h lm jLK kv θ al ν, and
  (a) is: TwV.traceOfFlat D.N (rsT D ν C) = trT D ν C;
  (b) is: every row of Fo.rows16 D.N (trT D ν C) holds at ν;
  (c) is: the field kT of trT D ν C, less the value at ν of the form incTop on the key side's mask
       entries, is ext D.v (facK D.key D.al) at the point Fo.pntK D.N (trT D ν C).

Main theorems:
* "premT_of_premF": PremF h lm jLK kv θ al ν C gives PremT D ν C, the premises of LookDefs.lean on
  plain numbers. "tabF_eq": under FoNums.ok h, Fo.tabF h θ is Ends.jointTab h θ.
* "thetaOf_rsF", "afterShift_rsF", "forN_rsF", "forTrace_rsF": under PremF (the second: always; the
  last: also under (a)), the four functions read θ, rsT D ν C, D.N and trT D ν C off rsF.
* "k3Rows_of", "k3Planes_of": under PremF, (a) and (b): K3Rows and K3Planes at rsF.
* "k3Keys_of": under PremF, (a) and (c): K3Keys at rsF and the key vectors kv.
* "claims_of": under PremF and (a), (b), (c): every member of Fo.claimsOf at rsF, at the caller's
  values Fo.colsK (at zb0 and zb1) and Cb.Fo.Pin.pinColK of ν and keysAt of kv, is 0.
"res_zero": under PremF, (a) and (b), the residue of a row of Fo.rows16 at what is read off rsF is
0. "ext_blocks" carries LookDefs.lean's ext, on a list with coordinate i at bit i, to Blocks.ext.

Limits. (a), (b) and (c) are assumed, not proved, in this file;
Johnson/HonestTrace/LookClaimsHon.lean takes them from "trace_hon", "rows16_hon" and "keyEnd_hon".
The mask entries and all challenges are arguments: nothing is drawn. K is any field.

Not claimed: that a prover's program sends the scalars of rsF; that the Lean verifier's function
which reads these rounds returns a value, or that the forms it then holds have the values of
Fo.claimsOf; that a verifier accepts; anything on what the rounds show of the keys.

-/
import Johnson.HonestTrace.LookDefs
import Johnson.Top.H.K3RowOut
import OnBytes.Tie.Pv.Lookup.Forest.FoGaps
import OnBytes.Tie.Pv.Lookup.Forest.FoDescent
import OnBytes.Tie.Pv.Lookup.Forest.FoJoinOut

set_option autoImplicit false

namespace OnBytes.HonestTrace.Look

open Finset TwV
open OnBytes.Model
open Cb.Lkp
open VerifiableInference.OnPublicFiles (K3Rows K3Planes K3Keys keysAt)

section
variable {K : Type} [Field K]
variable {h : Forest.Shape} {lm jLK : ℕ} {kv : ℕ → ℕ → K} {θ al : K} {ν : _root_.Fo.Pl → K}
  {C : Chal K}

/-! ## From the premises at a sub-proof's lookup to the premises on plain numbers -/

/-- Under FoNums.ok h, the joined table Fo.tabF h θ is Ends.jointTab h θ, at every row. -/
theorem tabF_eq (hok : FoNums.ok h = true) (θ : K) :
    _root_.Fo.tabF h θ = Ends.jointTab h θ := by
  funext u
  rw [jointTab_row hok]
  rfl

/-- PremF h lm jLK kv θ al ν C gives PremT at dataF h lm jLK kv θ al ν, ν and C: 32 planes; the four
orders list each coordinate once; MidP; the bits are what ν reads; the challenges' lists have the
plan's lengths. -/
theorem premT_of_premF (H : PremF h lm jLK kv θ al ν C) :
    PremT (dataF h lm jLK kv θ al ν) ν C where
  planes := rfl
  oK := fun l _ => by
    have e := _root_.Fo.ordK_perm h (Cb.Fo.ok_parts H.ok).1.1 l
    rwa [Nat.zero_add] at e
  oT := fun l _ => List.reverse_perm _
  oE := by
    show (FoNums.ordE h).Perm _
    unfold FoNums.ordE
    rw [_root_.Fo.place_list]
    exact List.reverse_perm _
  oB := by
    show (FoNums.ordB h).Perm _
    unfold FoNums.ordB
    rw [_root_.Fo.place_list]
    exact List.reverse_perm _
  mid := by
    show MidP (FoNums.v' h + 1) h.d FoNums.w (FoNums.n + 2) (Ends.jointKey h kv θ)
      (_root_.Fo.tabF h θ) (FoNums.pads h) _ al
    rw [← Cb.Fo.ok_v H.ok, tabF_eq H.ok]
    exact H.mid
  bits := fun _ _ _ _ => rfl
  chal := by
    show C.Fits (FoNums.v' h + 1) h.d FoNums.w
    rw [← Cb.Fo.ok_v H.ok]
    exact H.chal

/-! ## What the landed functions read off the rounds -/

/-- Under PremF, Fo.thetaOf reads θ off rsF. Where there is one call it reads 0, which PremF says θ
is. -/
theorem thetaOf_rsF (H : PremF h lm jLK kv θ al ν C) :
    _root_.Fo.thetaOf h (rsF h lm jLK kv θ al ν C) = θ := by
  unfold _root_.Fo.thetaOf rsF
  cases hs : FoNums.several h with
  | false => exact (H.one hs).symm
  | true => rfl

/-- Fo.afterShift of rsF is rsT at dataF h lm jLK kv θ al ν. No premise. -/
theorem afterShift_rsF (h : Forest.Shape) (lm jLK : ℕ) (kv : ℕ → ℕ → K) (θ al : K)
    (ν : _root_.Fo.Pl → K) (C : Chal K) :
    _root_.Fo.afterShift h (rsF h lm jLK kv θ al ν C) = rsT (dataF h lm jLK kv θ al ν) ν C := by
  unfold _root_.Fo.afterShift rsF
  cases FoNums.several h <;> rfl

/-- Under PremF, Fo.forN at rsF is the field N of dataF h lm jLK kv θ al ν. -/
theorem forN_rsF (H : PremF h lm jLK kv θ al ν C) :
    _root_.Fo.forN h lm jLK (rsF h lm jLK kv θ al ν C) = (dataF h lm jLK kv θ al ν).N := by
  unfold _root_.Fo.forN
  rw [thetaOf_rsF H]
  rfl

/-- Under PremF, with D = dataF h lm jLK kv θ al ν: if TwV.traceOfFlat D.N (rsT D ν C) = trT D ν C,
then Fo.forTrace at rsF is trT D ν C. -/
theorem forTrace_rsF (H : PremF h lm jLK kv θ al ν C)
    (hTrace : traceOfFlat (dataF h lm jLK kv θ al ν).N (rsT (dataF h lm jLK kv θ al ν) ν C) =
      trT (dataF h lm jLK kv θ al ν) ν C) :
    _root_.Fo.forTrace h lm jLK (rsF h lm jLK kv θ al ν C) =
      trT (dataF h lm jLK kv θ al ν) ν C := by
  unfold _root_.Fo.forTrace
  rw [forN_rsF H, afterShift_rsF, hTrace]

/-! ## The rows and the planes -/

/-- Under PremF, with D = dataF h lm jLK kv θ al ν: if TwV.traceOfFlat D.N (rsT D ν C) = trT D ν C
and every row of Fo.rows16 D.N (trT D ν C) holds at ν, then every row of Fo.rows16 at Fo.forN and
Fo.forTrace of rsF has the residue Fo.rowRes ν r = 0. -/
theorem res_zero (H : PremF h lm jLK kv θ al ν C)
    (hTrace : traceOfFlat (dataF h lm jLK kv θ al ν).N (rsT (dataF h lm jLK kv θ al ν) ν C) =
      trT (dataF h lm jLK kv θ al ν) ν C)
    (hRows : ∀ r ∈ _root_.Fo.rows16 (dataF h lm jLK kv θ al ν).N
      (trT (dataF h lm jLK kv θ al ν) ν C), _root_.Fo.SRowHolds r ν)
    {r : SRow _root_.Fo.Pl K}
    (hm : r ∈ _root_.Fo.rows16 (_root_.Fo.forN h lm jLK (rsF h lm jLK kv θ al ν C))
      (_root_.Fo.forTrace h lm jLK (rsF h lm jLK kv θ al ν C))) :
    _root_.Fo.rowRes ν r = 0 := by
  rw [forN_rsF H, forTrace_rsF H hTrace] at hm
  exact sub_eq_zero.2 (hRows r hm)

/-- Under PremF, with D = dataF h lm jLK kv θ al ν: if TwV.traceOfFlat D.N (rsT D ν C) = trT D ν C
and every row of Fo.rows16 D.N (trT D ν C) holds at ν, then K3Rows h lm jLK ν holds at rsF: the
residue of every row of the sumchecks is 0. -/
theorem k3Rows_of (H : PremF h lm jLK kv θ al ν C)
    (hTrace : traceOfFlat (dataF h lm jLK kv θ al ν).N (rsT (dataF h lm jLK kv θ al ν) ν C) =
      trT (dataF h lm jLK kv θ al ν) ν C)
    (hRows : ∀ r ∈ _root_.Fo.rows16 (dataF h lm jLK kv θ al ν).N
      (trT (dataF h lm jLK kv θ al ν) ν C), _root_.Fo.SRowHolds r ν) :
    K3Rows h lm jLK ν (rsF h lm jLK kv θ al ν C) := by
  intro y hy
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hy
  refine res_zero H hTrace hRows ?_
  have e : _root_.Fo.rows16 (_root_.Fo.forN h lm jLK (rsF h lm jLK kv θ al ν C))
      (_root_.Fo.forTrace h lm jLK (rsF h lm jLK kv θ al ν C)) = _ :=
    _root_.Fo.ends_r16 h lm jLK (rsF h lm jLK kv θ al ν C)
  rw [e]
  rcases List.mem_append.1 hr with hr | hr
  · rcases List.mem_append.1 hr with hr | hr
    · rcases List.mem_append.1 hr with hr | hr
      · exact List.mem_append_left _ (List.mem_reverse.2 hr)
      · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_reverse.2 hr))
    · exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_reverse.2 hr))))
  · rw [List.mem_singleton.1 hr]
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _
      (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))))

/-- Under PremF, with D = dataF h lm jLK kv θ al ν: if TwV.traceOfFlat D.N (rsT D ν C) = trT D ν C
and every row of Fo.rows16 D.N (trT D ν C) holds at ν, then K3Planes h lm jLK ν holds at rsF:
Fo.claimLeaves, Fo.claimBits and Cb.Fo.Pin.countK are 0. -/
theorem k3Planes_of (H : PremF h lm jLK kv θ al ν C)
    (hTrace : traceOfFlat (dataF h lm jLK kv θ al ν).N (rsT (dataF h lm jLK kv θ al ν) ν C) =
      trT (dataF h lm jLK kv θ al ν) ν C)
    (hRows : ∀ r ∈ _root_.Fo.rows16 (dataF h lm jLK kv θ al ν).N
      (trT (dataF h lm jLK kv θ al ν) ν C), _root_.Fo.SRowHolds r ν) :
    K3Planes h lm jLK ν (rsF h lm jLK kv θ al ν C) := by
  have mem : ∀ r, (r = rowEnd (_root_.Fo.forN h lm jLK (rsF h lm jLK kv θ al ν C))
        (_root_.Fo.forTrace h lm jLK (rsF h lm jLK kv θ al ν C)) ∨
      r = rowBitE (_root_.Fo.forN h lm jLK (rsF h lm jLK kv θ al ν C))
        (_root_.Fo.forTrace h lm jLK (rsF h lm jLK kv θ al ν C)) ∨
      r = rowNum (_root_.Fo.forN h lm jLK (rsF h lm jLK kv θ al ν C))) →
      _root_.Fo.rowRes ν r = 0 := by
    intro r hr
    refine res_zero H hTrace hRows ?_
    unfold _root_.Fo.rows16
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  refine ⟨?_, ?_, ?_⟩
  · rw [← _root_.Fo.rowEnd_claim h H.ok lm jLK H.lm5 H.lmT _ ν H.zero]
    exact mem _ (Or.inl rfl)
  · have e := _root_.Fo.rowBitE_claim h H.ok lm jLK H.lm5 H.lmT (rsF h lm jLK kv θ al ν C) ν H.zero
    rw [mem _ (Or.inr (Or.inl rfl))] at e
    exact neg_eq_zero.1 e.symm
  · rw [← _root_.Fo.rowNum_claim h H.ok lm jLK H.lm5 H.lmT (rsF h lm jLK kv θ al ν C) ν H.zero]
    exact mem _ (Or.inr (Or.inr rfl))

/-! ## The join -/

/-- For a list p of m coordinates, coordinate i with bit i: ext m f p is Blocks.ext m f at the point
that reads p from its end. -/
theorem ext_blocks (m : ℕ) (f : ℕ → K) (p : List K) (hp : p.length = m) :
    ext m f p = Blocks.ext m f (_root_.Fo.ptL p.reverse) := by
  unfold ext Blocks.ext
  refine sum_congr rfl fun X _ => ?_
  have e := _root_.Fo.eqN_top (_root_.Fo.ptL p.reverse) 0 m X
  simp only [Nat.zero_add] at e
  have e2 : ((List.range m).map fun i => _root_.Fo.ptL p.reverse i) = p.reverse := by
    have := _root_.Fo.rho_ptL p.reverse
    rw [List.length_reverse, hp] at this
    exact this
  rw [e2, List.reverse_reverse] at e
  rw [e]

/-- Under PremF, with D = dataF h lm jLK kv θ al ν: if TwV.traceOfFlat D.N (rsT D ν C) = trT D ν C,
and the field kT of trT D ν C less the value at ν of the form incTop on the key side's mask entries
is ext D.v (facK D.key D.al) at Fo.pntK D.N (trT D ν C), then K3Keys h lm jLK ν kv holds at rsF:
Fo.claimJoin, at each call's key vector kv c extended at the call's point, is 0. -/
theorem k3Keys_of (H : PremF h lm jLK kv θ al ν C)
    (hTrace : traceOfFlat (dataF h lm jLK kv θ al ν).N (rsT (dataF h lm jLK kv θ al ν) ν C) =
      trT (dataF h lm jLK kv θ al ν) ν C)
    (hKeyEnd : (trT (dataF h lm jLK kv θ al ν) ν C).kT -
        _root_.Fo.valS (incTop (dataF h lm jLK kv θ al ν).N.ledK
          (fK (dataF h lm jLK kv θ al ν).N (trT (dataF h lm jLK kv θ al ν) ν C))
          (trT (dataF h lm jLK kv θ al ν) ν C).keys.reverse) ν =
      ext (dataF h lm jLK kv θ al ν).v
        (facK (dataF h lm jLK kv θ al ν).key (dataF h lm jLK kv θ al ν).al)
        (_root_.Fo.pntK (dataF h lm jLK kv θ al ν).N (trT (dataF h lm jLK kv θ al ν) ν C))) :
    K3Keys h lm jLK ν kv (rsF h lm jLK kv θ al ν C) := by
  have hok := H.ok
  have eN := forN_rsF H
  have eT := forTrace_rsF H hTrace
  have hx := _root_.Fo.ends_zx_len h hok lm jLK (rsF h lm jLK kv θ al ν C)
  have hy := _root_.Fo.ends_zy_len h hok lm jLK (rsF h lm jLK kv θ al ν C)
  have a1 : (_root_.Fo.endsOf h lm jLK (rsF h lm jLK kv θ al ν C)).alpha = al := by
    show (_root_.Fo.forTrace h lm jLK (rsF h lm jLK kv θ al ν C)).lam = al
    rw [eT]
    rfl
  have a2 : (_root_.Fo.endsOf h lm jLK (rsF h lm jLK kv θ al ν C)).theta = θ := thetaOf_rsF H
  have a3 : (_root_.Fo.endsOf h lm jLK (rsF h lm jLK kv θ al ν C)).cEndC =
      (trT (dataF h lm jLK kv θ al ν) ν C).kT := by
    show (_root_.Fo.forTrace h lm jLK (rsF h lm jLK kv θ al ν C)).kT = _
    rw [eT]
  have a4 : (_root_.Fo.endsOf h lm jLK (rsF h lm jLK kv θ al ν C)).cEndF =
      scale (-1) (incTop (dataF h lm jLK kv θ al ν).N.ledK
        (fK (dataF h lm jLK kv θ al ν).N (trT (dataF h lm jLK kv θ al ν) ν C))
        (trT (dataF h lm jLK kv θ al ν) ν C).keys.reverse) := by
    show scale (-1) (incTop (_root_.Fo.forN h lm jLK (rsF h lm jLK kv θ al ν C)).ledK
      (fK (_root_.Fo.forN h lm jLK (rsF h lm jLK kv θ al ν C))
        (_root_.Fo.forTrace h lm jLK (rsF h lm jLK kv θ al ν C)))
      (_root_.Fo.forTrace h lm jLK (rsF h lm jLK kv θ al ν C)).keys.reverse) = _
    rw [eN, eT]
  have a5 : (_root_.Fo.endsOf h lm jLK (rsF h lm jLK kv θ al ν C)).zx ++
      (_root_.Fo.endsOf h lm jLK (rsF h lm jLK kv θ al ν C)).zy =
      (_root_.Fo.pntK (dataF h lm jLK kv θ al ν).N
        (trT (dataF h lm jLK kv θ al ν) ν C)).reverse := by
    show ((_root_.Fo.pntK (_root_.Fo.forN h lm jLK (rsF h lm jLK kv θ al ν C))
        (_root_.Fo.forTrace h lm jLK (rsF h lm jLK kv θ al ν C))).drop h.rK).reverse ++
      ((_root_.Fo.pntK (_root_.Fo.forN h lm jLK (rsF h lm jLK kv θ al ν C))
        (_root_.Fo.forTrace h lm jLK (rsF h lm jLK kv θ al ν C))).take h.rK).reverse = _
    rw [eN, eT, ← List.reverse_append, List.take_append_drop]
  have a6 : (_root_.Fo.pntK (dataF h lm jLK kv θ al ν).N
      (trT (dataF h lm jLK kv θ al ν) ν C)).length = h.v := by
    have e := _root_.Fo.pntK_len h hok lm jLK (rsF h lm jLK kv θ al ν C)
    rw [eN, eT] at e
    exact e
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = (_root_.Fo.endsOf h lm jLK (rsF h lm jLK kv θ al ν C)).zx ++
      (_root_.Fo.endsOf h lm jLK (rsF h lm jLK kv θ al ν C)).zy := ⟨_, rfl⟩
  have hlen : ρ.length = h.dT + h.rK := by rw [hρ, List.length_append, hx, hy]
  have hrho : _root_.Fo.rhoP (h.dT + h.rK) (_root_.Fo.ptL ρ) = ρ := by
    rw [← hlen]
    exact _root_.Fo.rho_ptL _
  have hzx : _root_.Fo.zxOf h (⟨_root_.Fo.ptL ρ, fun _ => 0, 0⟩ : Cb.LdLkp.MCl K (Fin 0)) =
      (_root_.Fo.endsOf h lm jLK (rsF h lm jLK kv θ al ν C)).zx := by
    show (_root_.Fo.rhoP (h.dT + h.rK) (_root_.Fo.ptL ρ)).take h.dT = _
    rw [hrho, hρ]
    exact List.take_left' hx
  have hzy : _root_.Fo.zyOf h (⟨_root_.Fo.ptL ρ, fun _ => 0, 0⟩ : Cb.LdLkp.MCl K (Fin 0)) =
      (_root_.Fo.endsOf h lm jLK (rsF h lm jLK kv θ al ν C)).zy := by
    show (_root_.Fo.rhoP (h.dT + h.rK) (_root_.Fo.ptL ρ)).drop h.dT = _
    rw [hrho, hρ]
    exact List.drop_left' hx
  have hKF : _root_.Fo.KFokAt h (fun _ : Fin 0 → K => kv)
      (_root_.Fo.zkOf h (⟨_root_.Fo.ptL ρ, fun _ => 0, 0⟩ : Cb.LdLkp.MCl K (Fin 0)))
      (fun c => _root_.Fo.AffK.ofConst (keysAt h lm jLK kv (rsF h lm jLK kv θ al ν C) c))
      (fun _ => 0) := by
    intro c hc
    rw [_root_.Fo.AffK.val_ofConst]
    unfold keysAt
    rw [_root_.Fo.ends_zk h hok lm jLK (rsF h lm jLK kv θ al ν C) c hc]
    unfold _root_.Fo.zkOf
    rw [hzx, hzy]
  have hC : _root_.Fo.CEok (⟨_root_.Fo.ptL ρ, fun _ => 0, 0⟩ : Cb.LdLkp.MCl K (Fin 0)) al
      (_root_.Fo.AffK.ofConst al) := by
    intro μ
    rw [_root_.Fo.AffK.val_ofConst]
    simp
  have g := _root_.Fo.join_form_gap (_root_.Fo.ok_prem hok) (fun _ : Fin 0 → K => kv) θ al
    (⟨_root_.Fo.ptL ρ, fun _ => 0, 0⟩ : Cb.LdLkp.MCl K (Fin 0)) _ _ (fun _ => 0) hKF hC
  rw [hzy, _root_.Fo.val_joinK] at g
  have hM : _root_.Fo.MGap (⟨_root_.Fo.ptL ρ, fun _ => 0, 0⟩ : Cb.LdLkp.MCl K (Fin 0)) h.v
      (Ends.jointKey h kv θ) (fun _ => 0) =
      Blocks.ext h.v (Ends.jointKey h kv θ) (_root_.Fo.ptL ρ) := by
    unfold _root_.Fo.MGap
    simp
  rw [hM] at g
  have hE : _root_.Fo.AffK.val
      ((_root_.Fo.endsOf h lm jLK (rsF h lm jLK kv θ al ν C)).cEndF,
        (_root_.Fo.endsOf h lm jLK (rsF h lm jLK kv θ al ν C)).cEndC) ν =
      al - Blocks.ext h.v (Ends.jointKey h kv θ) (_root_.Fo.ptL ρ) := by
    show _root_.Fo.valS (_root_.Fo.endsOf h lm jLK (rsF h lm jLK kv θ al ν C)).cEndF ν +
      (_root_.Fo.endsOf h lm jLK (rsF h lm jLK kv θ al ν C)).cEndC = _
    rw [a3, a4, _root_.Fo.valS_scale]
    have e1 : (dataF h lm jLK kv θ al ν).v = h.v := (Cb.Fo.ok_v hok).symm
    rw [e1, ext_blocks h.v _ _ a6, ← a5, ← hρ] at hKeyEnd
    have e2 : Blocks.ext h.v (facK (dataF h lm jLK kv θ al ν).key (dataF h lm jLK kv θ al ν).al)
        (_root_.Fo.ptL ρ) = al - Blocks.ext h.v (Ends.jointKey h kv θ) (_root_.Fo.ptL ρ) := by
      show Blocks.ext h.v (fun b => al - Ends.jointKey h kv θ b) (_root_.Fo.ptL ρ) = _
      rw [Blocks.ext_sub h.v (fun _ => al) (Ends.jointKey h kv θ), Blocks.ext_const]
    rw [e2] at hKeyEnd
    linear_combination hKeyEnd
  unfold K3Keys _root_.Fo.claimJoin
  rw [_root_.Fo.val_joinK, hE, a1, a2]
  simp only [_root_.Fo.AffK.val_ofConst] at g ⊢
  linear_combination g

/-- **Under PremF and three statements on plain numbers, every claim of the lookup is 0 at rsF.**
Under PremF, with D = dataF h lm jLK kv θ al ν: if TwV.traceOfFlat D.N (rsT D ν C) = trT D ν C,
every row of Fo.rows16 D.N (trT D ν C) holds at ν, and the field kT of trT D ν C less the value at ν
of the form incTop on the key side's mask entries is ext D.v (facK D.key D.al) at Fo.pntK D.N (trT D
ν C), then every member of Fo.claimsOf at rsF, at the columns' sums Fo.colsK and Cb.Fo.Pin.pinColK
of ν and the keys keysAt of kv, is 0. -/
theorem claims_of (H : PremF h lm jLK kv θ al ν C)
    (hTrace : traceOfFlat (dataF h lm jLK kv θ al ν).N (rsT (dataF h lm jLK kv θ al ν) ν C) =
      trT (dataF h lm jLK kv θ al ν) ν C)
    (hRows : ∀ r ∈ _root_.Fo.rows16 (dataF h lm jLK kv θ al ν).N
      (trT (dataF h lm jLK kv θ al ν) ν C), _root_.Fo.SRowHolds r ν)
    (hKeyEnd : (trT (dataF h lm jLK kv θ al ν) ν C).kT -
        _root_.Fo.valS (incTop (dataF h lm jLK kv θ al ν).N.ledK
          (fK (dataF h lm jLK kv θ al ν).N (trT (dataF h lm jLK kv θ al ν) ν C))
          (trT (dataF h lm jLK kv θ al ν) ν C).keys.reverse) ν =
      ext (dataF h lm jLK kv θ al ν).v
        (facK (dataF h lm jLK kv θ al ν).key (dataF h lm jLK kv θ al ν).al)
        (_root_.Fo.pntK (dataF h lm jLK kv θ al ν).N (trT (dataF h lm jLK kv θ al ν) ν C))) :
    ∀ y ∈ _root_.Fo.claimsOf h lm jLK (rsF h lm jLK kv θ al ν C) ν
      (_root_.Fo.colsK h lm (_root_.Fo.endsOf h lm jLK (rsF h lm jLK kv θ al ν C)).zb0 ν)
      (_root_.Fo.colsK h lm (_root_.Fo.endsOf h lm jLK (rsF h lm jLK kv θ al ν C)).zb1 ν)
      (Cb.Fo.Pin.pinColK lm ν) (keysAt h lm jLK kv (rsF h lm jLK kv θ al ν C)), y = 0 :=
  (VerifiableInference.OnPublicFiles.k3_claims_iff h lm jLK ν kv _).2
    ⟨k3Rows_of H hTrace hRows, k3Planes_of H hTrace hRows, k3Keys_of H hTrace hKeyEnd⟩

end

end OnBytes.HonestTrace.Look

#print axioms OnBytes.HonestTrace.Look.tabF_eq
#print axioms OnBytes.HonestTrace.Look.premT_of_premF
#print axioms OnBytes.HonestTrace.Look.thetaOf_rsF
#print axioms OnBytes.HonestTrace.Look.afterShift_rsF
#print axioms OnBytes.HonestTrace.Look.forN_rsF
#print axioms OnBytes.HonestTrace.Look.forTrace_rsF
#print axioms OnBytes.HonestTrace.Look.res_zero
#print axioms OnBytes.HonestTrace.Look.k3Rows_of
#print axioms OnBytes.HonestTrace.Look.k3Planes_of
#print axioms OnBytes.HonestTrace.Look.ext_blocks
#print axioms OnBytes.HonestTrace.Look.k3Keys_of
#print axioms OnBytes.HonestTrace.Look.claims_of
