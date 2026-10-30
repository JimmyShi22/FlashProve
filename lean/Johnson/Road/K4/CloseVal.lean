-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseVal.lean: AT EVERY YES OF THE PIECE THAT HOLDS K4's OWN BLOCK, IN A GROUP THAT
IS NOT THE FIRST: WHAT THE VALUE's TYPED CHAIN PUTS OUT ON THE IMAGE OF THE WRITTEN TRANSCRIPT IS,
BY NAME, THE STATEMENT `TailH.z7` OF THE WORDS ON THE VERY TAPE THAT K4's HEARING HEARD; AND THE
COEFFICIENT OF THE TERMS' SUMCHECK IN IT IS NOT 0. Glue between files that are proved elsewhere: no
new argument, no count.

  `keepsWords_noDigest`: a round without the sealed digest keeps its items and its drawn elements.
  `stgM_ofIs_ok`, `tailM_ofIs_ok`: the ties `TailM.ofIs` (OnBytes/Desc/First/P1/OwnMapsPlan.lean)
    are as OnBytes/Desc/First/P1/OwnView.lean asks (`TailM.Ok`), if every written round's message
    holds elements of the extension field alone.
  `ks_fit`: K4's numbers of variables' rounds (`ksOf`) are those of the declared rounds as data
    (`tailR (numsOf …)`, Johnson/Road/K4/DsTailR.lean).
  `tapeW_cast`: the tape along an equation of lists of written rounds.
  `small_of_all`: from the test "every word is below the prime" to `SmallTape`.
  `ptOf Q t`: the token point, read off a tape's first round.
  `Plan4.tailMK`, `Plan4.tailMK_ok`: the ties inside `Plan4.mapsK4` (PlanMaps.lean), and that they
    are as asked.
  `Plan4.nz_at`: on the tape of a written transcript over K4's declared rounds no further challenge
    reads 0.
  `Plan4.val_at`: at any list ds with e : ds = dsLater par, any written transcript τ over ds and any
    entries es: under `TailH.Claims` at the data read off the tape t0 := tapeW noDigest ds τ es:
    the chain's value on ((mapsK4 A N Ex).castD e).view τ is (k4Tail … t0 …).z7 (x, the token
    point).
  `Plan4.coin_at`: if moreover every drawn word of t0 is below the prime and K4's hearing returns on
    t0: `LayVO.epsOK` at that value.

Limits. `TailH.Claims` IS A PREMISE (seven equations; see Johnson/Road/K4/Claims.lean, Claim4.lean).
`Plan4.Meets` is a premise. A group that is not the first. Nothing on rows, slots or worlds.

-/
import Johnson.Road.K4.OwnCoin
import Johnson.Road.K4.PlanMaps
import OnBytes.Desc.First.P1.NzTape
import OnBytes.Desc.First.P1.CastD
import Cb.Pv.Lay.OwnTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb TWhole Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.Desc.First.K4
open OnBytes.Model (Fork Forest.Heard)
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.Tie.Pv.Lay (StgIs TailIs)
open OnBytes.Tie.Pv.Lay.Eng (TailH)
open OnBytes.Desc.First.P1 (gl Ks NzT Adds7 TailM TailR ScR StgM TailLens TailNums AllE KeepsWords
  IsTape tapeW drawnOf nzT_of_ds tailIs_at)
open VerifiableInference.Desc (noDigest)
open Inst.Model (Scl)
open _root_.Run (ckP)

/-- A round without the sealed digest keeps its items and its drawn elements. -/
theorem keepsWords_noDigest : KeepsWords noDigest := ⟨fun _ => rfl, fun _ => rfl⟩

section Ties
variable {M X : Type}

theorem stgM_ofIs_ok {S : Stg GE M X} {n k dy vals : ℕ} (h : StgIs S n k dy vals) (r : ScR)
    (hk : r.vs.length = k) (num : S.L.T.par.A → ℕ) (hA : ∀ d ∈ r.all, AllE d) :
    (StgM.ofIs h r hk num).Ok where
  e := hA _ (by simp [ScR.all])
  vs := fun d hd => hA d (by simp [ScR.all, hd])
  y := hA _ (by simp [ScR.all])
  v := hA _ (by simp [ScR.all])
  k := hk.trans h.hk.symm
  n := h.hd
  dy := rfl

theorem tailM_ofIs_ok {T : LayTail GE M X} {x : OnBytes.Params.LayerRounds} (h : TailIs T x)
    {R : TailR} (hl : TailLens R x) (N : TailNums T) (hA : ∀ d ∈ R.all, AllE d) :
    (TailM.ofIs h hl N).Ok where
  l := hA _ (by simp [TailR.all])
  p := hA _ (by simp [TailR.all])
  w := hA _ (by simp [TailR.all])
  s1 := stgM_ofIs_ok h.s1 R.r1 hl.l1 N.n1 fun d hd => hA d (by simp [TailR.all, hd])
  s2 := stgM_ofIs_ok h.s2 R.r2 hl.l2 N.n2 fun d hd => hA d (by simp [TailR.all, hd])
  s3 := stgM_ofIs_ok h.s3 R.r3 hl.l3 N.n3 fun d hd => hA d (by simp [TailR.all, hd])
  s4 := stgM_ofIs_ok h.s4 R.r4 hl.l4 N.n4 fun d hd => hA d (by simp [TailR.all, hd])
  s5 := stgM_ofIs_ok h.s5 R.r5 hl.l5 N.n5 fun d hd => hA d (by simp [TailR.all, hd])
  s6 := stgM_ofIs_ok h.s6 R.r6 hl.l6 N.n6 fun d hd => hA d (by simp [TailR.all, hd])
  s7 := stgM_ofIs_ok h.s7 R.r7 hl.l7 N.n7 fun d hd => hA d (by simp [TailR.all, hd])

end Ties

/-- K4's numbers of variables' rounds are the declared rounds'. tk: any tokens. -/
theorem ks_fit (P : Pub) (hp : HPlan2) (g : ℕ) (tk : Array Nat) :
    (ksOf { P with tokv := tk } hp).Fit (tailR (numsOf P hp g)) :=
  ⟨List.length_replicate, List.length_replicate, List.length_replicate, List.length_replicate,
    List.length_replicate, List.length_replicate, List.length_replicate⟩

/-- The tape along an equation of lists of written rounds. -/
theorem tapeW_cast {ds ds' : List RDT} (e : ds' = ds) (f : Fmt.RoundView → Fmt.RoundView)
    (τ : Tr (uLT (ckP .two) ds')) (es : List Fmt.Entry) :
    tapeW f ds' τ es = tapeW f ds (e ▸ τ) es := by
  subst e
  rfl

/-- From the test "every word is below the prime" to `SmallTape`. -/
theorem small_of_all (rs : List Fmt.RoundView) (es : List Fmt.Entry) (g : Fmt.RoundView → Bool)
    (h : (rs.all fun r => g r && r.drawn.elems.all fun x => okE (E.ofTriple x)) = true) :
    SmallTape (paired rs es) :=
  small_paired rs es fun r hr x hx =>
    List.all_eq_true.mp (Bool.and_eq_true _ _ ▸ List.all_eq_true.mp h r hr).2 x hx

section AtTheValue
variable [scl : Scl] {M X : Type} {Q : Plan4 Cb.Gl.E M X} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- The token point, read off a tape's first round. -/
noncomputable abbrev ptOf (Q : Plan4 Cb.Gl.E M X) (t : Tape) : Fin Q.full.own.toOwn.gT → Cb.Gl.E :=
  Johnson.L5.Layers.rd gl Q.full.own.toOwn.gT (drawnOf t)

/-- The ties inside `Plan4.mapsK4`. -/
noncomputable def Plan4.tailMK (A : Q.Meets par hS pcl) (N : TailNums Q.full.own.toOwn.tail) :
    TailM Q.full.own.toOwn.tail (tailR (numsOf par.P par.hp par.g)) :=
  TailM.ofIs
    (tailIs_at Q.full (OnBytes.Model.Verify.layerNumbers par.P par.hp par.g) A.dimIs A.wk A.hg)
    A.written.2.2 N

theorem Plan4.tailMK_ok (A : Q.Meets par hS pcl) (N : TailNums Q.full.own.toOwn.tail) :
    (Plan4.tailMK A N).Ok :=
  tailM_ofIs_ok _ _ N (tailR_pieces (numsOf par.P par.hp par.g)).allE

/-- On the tape of a written transcript over K4's declared rounds no further challenge reads 0. -/
theorem Plan4.nz_at (A : Q.Meets par hS pcl) (tk : Array Nat)
    (τ : Tr (uLT (ckP .two) (dsLater par))) (es : List Fmt.Entry) :
    NzT Q.full.own.toOwn.tail (ksOf { par.P with tokv := tk } par.hp)
      ((tapeW noDigest (dsLater par) τ es).drop 1) :=
  nzT_of_ds keepsWords_noDigest (ks_fit par.P par.hp par.g tk)
    (IsTape.right (as := [rdOf (pointRd .zero par.P.y.h.lt)]) ⟨es, rfl⟩) A.written.2.1

/-- **What the chain puts out at the image of the written transcript, in the words of the tape.** -/
theorem Plan4.val_at (A : Q.Meets par hS pcl) (N : TailNums Q.full.own.toOwn.tail) (Ex : ExtSpec)
    (tk : Array Nat) {ds : List RDT} (e : ds = dsLater par) (τ : Tr (uLT (ckP .two) ds))
    (es : List Fmt.Entry)
    (nz : NzT Q.full.own.toOwn.tail (ksOf { par.P with tokv := tk } par.hp)
      ((tapeW noDigest ds τ es).drop 1))
    (a : Adds7 Q.full.own.toOwn.tail) (x : X) (y : Ex.Str)
    (hc : (k4Tail (Plan4.tailMK A N) { par.P with tokv := tk } par.hp (tapeW noDigest ds τ es) nz
      a).Claims (x, ptOf Q (tapeW noDigest ds τ es))) :
    (Q.full.own.toOwn.ch.val Ex (x, y) (((Plan4.mapsK4 A N Ex).castD e).view τ)).1 =
      (k4Tail (Plan4.tailMK A N) { par.P with tokv := tk } par.hp (tapeW noDigest ds τ es) nz
        a).z7 (x, ptOf Q (tapeW noDigest ds τ es)) := by
  subst e
  exact k4_val Ex Q.full.own.toOwn (rdOf (pointRd .zero par.P.y.h.lt)) (Plan4.tailMK_ok A N)
    (ks_fit par.P par.hp par.g tk) keepsWords_noDigest τ ⟨es, rfl⟩ nz a x y hc

/-- **The coefficient of the terms' sumcheck, as the chain reads it at a hearing's tape, is not
0.** -/
theorem Plan4.coin_at (A : Q.Meets par hS pcl) (N : TailNums Q.full.own.toOwn.tail) (Ex : ExtSpec)
    (tk : Array Nat) {ds : List RDT} (e : ds = dsLater par) (τ : Tr (uLT (ckP .two) ds))
    (es : List Fmt.Entry)
    (nz : NzT Q.full.own.toOwn.tail (ksOf { par.P with tokv := tk } par.hp)
      ((tapeW noDigest ds τ es).drop 1))
    (a : Adds7 Q.full.own.toOwn.tail) (x : X) (y : Ex.Str)
    (hc : (k4Tail (Plan4.tailMK A N) { par.P with tokv := tk } par.hp (tapeW noDigest ds τ es) nz
      a).Claims (x, ptOf Q (tapeW noDigest ds τ es)))
    (hs : SmallTape (tapeW noDigest ds τ es)) {fo : Forest.Heard} {F G : Fork} {u : Tape}
    {o : Own}
    (h : hear engFl { par.P with tokv := tk } par.hp par.g fo F (tapeW noDigest ds τ es) =
      some (o, G, u)) :
    (Q.full.layVO Q.full.wPart).epsOK
      (Q.full.own.toOwn.ch.val Ex (x, y) (((Plan4.mapsK4 A N Ex).castD e).view τ)).1 := by
  rw [Plan4.val_at A N Ex tk e τ es nz a x y hc]
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, v1, v2, v5, u4, _, _, hz, _, _, c3,
    _⟩ := own_calls6 h A.hg
  exact k4_coin (Plan4.tailMK A N) hs c3 hz nz a _ hc

end AtTheValue
end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4.tailMK_ok
#print axioms OnBytes.Road.K4.Plan4.nz_at
#print axioms OnBytes.Road.K4.Plan4.val_at
#print axioms OnBytes.Road.K4.Plan4.coin_at
