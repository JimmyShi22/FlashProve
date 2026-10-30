-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/OwnD12Calls.lean: (D1) AND (D2) OF A SUMCHECK'S OWN ROW, AT THE TEXT's OWN CALLS.
OwnD1.lean and OwnD2.lean say them of a record that is `Ended` and of a form whose public part a
ledger shows. Here they are said where a product layer's call `Fl.levelIn` returns, and where the
merge's call `flatForkEnd` returns and the run "back" has made the merge's own claim (`ownClaim`,
OnBytes/Desc/First/K4/Plain.lean): for every ledger H later than the one in which the row is made.
Statements and proofs.

  `fo_paid_later`: marking an owed claim as added leads to a later ledger (`Fo.Later`).
  `d1_run_at`, `d1_ended_at`: (D1) AT ONE m, one mask row and one table of entries (OwnD1.lean asks
    its tie at every m, with masks and entries as functions of m). All statements below are at one
    m.
  `level_d1`: from the call's return out of a ledger with arrays of the right sizes, the typed
    format (k variables of degree 2 and a further one of degree 2), H later than the call's ledger
    G, and hw (which entry serves as which coefficient): (D1) at the record `levelRec …` in H's
    worlds.
  `level_d2`: from the call's return out of such a ledger, H later than G, and the typed half hinc:
    (D2) there.
  `merge_d1`: the same for the merge's record `wo.p`, where `ownClaim wo.p S0 kept Fb = some (row,
    Fb')`, Fb has arrays of the right sizes and H is later than Fb'.
  `merge_startIs`: the merge's record's start form is `wsForkStart sv (powers (tapeEps t) sv.size)`.
  `merge_d2`: (D2) for the merge's record, from the public part that `merge_recAt` hands out.

NO NEW ARGUMENT: `d1_of_run`'s and `d1_of_ended`'s proofs (OwnD1.lean) at one m, `d2_of_public`
(OwnD2.lean), `level_pscT` (OnBytes/Desc/First/P1/HeardPsc.lean), `levelIn_heard`, `pscRow_spec`,
`merge_recAt` (MergeRec.lean), `hideRun_ok`, `Fo.publicPart_later`,
`filledA_of_publicPart` (OnBytes/Desc/First/P1/LevelKit.lean).

Limits. PREMISES: `Sized`; the typed format; H later; hw; hinc. Nothing on (D3), (D4)
(OwnRowsStage.lean). One world at a time: no draw. Nothing on soundness.
-/
import Johnson.Road.K4.OwnD1
import Johnson.Road.K4.OwnD2
import Johnson.Road.K4.MergeRec
import OnBytes.Desc.First.K4.Plain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open Cb OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.Road.Hd Johnson.L5.Layers
open OnBytes.Tie.Pv (slotP slotNo hCount place_slotNo slotNo_mem slotNo_pIx)
open OnBytes.PscRun (Sized hideRun_ok)
open OnBytes.Psc (Weight)
open OnBytes.Desc.First.K4 (ownClaim)
open OnBytes.Desc.First.P1 (gl pscT levelRec levelWs levelIn_heard level_pscT pscRow_spec tapeEps
  filledA_of_publicPart level_world)
open OnBytes.Slice (GE)
open VerifiableInference.Desc.First.MergeLaw (hear_ended hear_of_flat)

/-- Marking an owed claim as added leaves what lies under the slots. -/
theorem fo_paid_later (F : Fork) (i : ℕ) : Fo.Later F (F.paid i) :=
  ⟨le_refl _, rfl, fun _ h => ⟨h, rfl, rfl⟩⟩

/-- **(D1) at one m**: `d1_of_run` (OwnD1.lean) asks its tie hw at every m, with masks and entries
as functions of m; here one m, one mask row, one table of entries. -/
theorem d1_run_at (Y : PscPar GE) (st : Y.St) {F G H : Fork} {first n : ℕ} (hF : Sized F)
    (hrow : F.hideRun first (Array.replicate n zeroE) (subE zeroE oneE) = some G)
    (hL : Fo.Later G H) (hn : hCount (Y.vars st) ≤ n) (mask : ℕ → GE) (entry : ℕ → ℕ → ℕ → GE)
    (m : Y.J → GE) (hw : ∀ q, m (Y.wAt q) = mask (slotP Y.fmt first q)) :
    Y.W st m = place (H.worldOf gl mask entry).slot (Y.vars st) first := by
  funext i
  rw [place_slotNo]
  obtain ⟨h1, h2⟩ := slotNo_mem (Y.vars st) first i
  obtain ⟨j, hj⟩ : ∃ j, slotNo (Y.vars st) first i = first + j :=
    ⟨slotNo (Y.vars st) first i - first, by omega⟩
  have hi : j < (Array.replicate n zeroE).size := by
    rw [Array.size_replicate]
    omega
  obtain ⟨_, _, hin, _⟩ := hideRun_ok F G first _ _ hF hrow
  obtain ⟨_, _, k3, k4, k5⟩ := hin j hi
  obtain ⟨_, g2, g3⟩ := hL.keep (first + j) k3
  have hz : (Array.replicate n zeroE).getD j zeroE = zeroE := by
    simp [Array.getD]
  have hW : Y.W st m i = mask (slotNo (Y.vars st) first i) := by
    rw [slotNo_pIx]
    exact hw _
  show _ = gl.val (H.vp.getD (slotNo (Y.vars st) first i) zeroE) -
    gl.val (H.mf.getD (slotNo (Y.vars st) first i) zeroE) * mask (slotNo (Y.vars st) first i)
  rw [hW, hj, g2, g3, k4, k5, hz, gl.zero, gl.sub, gl.zero, gl.one]
  ring

/-- (D1) at one m, for a record that is `Ended`. -/
theorem d1_ended_at (Y : PscPar GE) (st : Y.St) {p : Psc} {C : Aff} {τ mu eps : E} {first : ℕ}
    {ws : List Weight} {rs : List (List E × E)} {dY : ℕ} {sentY : List E} {beta : E}
    (a : OnBytes.Model.Road.Ended p C τ mu eps first ws rs dY sentY beta)
    (hd : ∀ w ∈ ws, w.d = 3)
    (hfmt : Y.fmt = List.replicate ws.length (pfCube GE 2) ++ [pDummy GE dY]) {F G H : Fork}
    (hF : Sized F)
    (hrow : F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G)
    (hL : Fo.Later G H) (mask : ℕ → GE) (entry : ℕ → ℕ → ℕ → GE) (m : Y.J → GE)
    (hw : ∀ q, m (Y.wAt q) = mask (slotP Y.fmt p.first q)) :
    Y.W st m = place (H.worldOf gl mask entry).slot (Y.vars st) p.first := by
  refine d1_run_at Y st hF hrow hL ?_ mask entry m hw
  rw [a.walkLen, entries_three ws dY hd]
  show hCount (pVars Y.fmt (Y.dat st)) ≤ _
  rw [hCount_pVars, hfmt, List.map_append, List.sum_append, List.map_replicate,
    List.sum_replicate]
  show 1 + (ws.length • 2 + (dY + 0)) ≤ _
  rw [smul_eq_mul]
  omega

/-- **(D1) where a product layer's call returns.** -/
theorem level_d1 (Y : PscPar GE) (st : Y.St) {k : ℕ} {rho : Array E} {C : Aff} {order : List Nat}
    {F G H : Fork} {t u : Tape} {o : Level} (h : Fl.levelIn k rho C order F t = some (o, G, u))
    (hs : Sized F) (hfmt : Y.fmt = List.replicate k (pfCube GE 2) ++ [pDummy GE 2])
    (hL : Fo.Later G H) (mask : ℕ → GE) (entry : ℕ → ℕ → ℕ → GE) (m : Y.J → GE)
    (hw : ∀ q, m (Y.wAt q) = mask (slotP Y.fmt (levelRec k rho C order F t).first q)) :
    Y.W st m = place (H.worldOf gl mask entry).slot (Y.vars st)
      (levelRec k rho C order F t).first := by
  obtain ⟨ho, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, v, F1, _, hF1, _, hG⟩ :=
    levelIn_heard h
  have hF' : Sized ({ F with next := F.next + 1 + 2 * k + 2 + 2 } : Fork) := hs
  obtain ⟨_, hS1, _, _⟩ := hideRun_ok _ F1 o.sL v _ hF' hF1
  have hlen : (levelWs k rho order).length = k := by
    unfold levelWs
    rw [List.length_map, ho]
  refine d1_ended_at Y st (level_pscT h) (fun w hw' => ?_) (by rw [hlen]; exact hfmt) hS1 hG hL
    mask entry m hw
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 hw'
  rfl

/-- **(D2) where a product layer's call returns.** -/
theorem level_d2 (Y : PscPar GE) (st : Y.St) {k : ℕ} {rho : Array E} {C : Aff} {order : List Nat}
    {F G H : Fork} {t u : Tape} {o : Level} (h : Fl.levelIn k rho C order F t = some (o, G, u))
    (hs : Sized F) (hL : Fo.Later G H) (mask : ℕ → GE) (entry : ℕ → ℕ → ℕ → GE) (m : Y.J → GE)
    (hinc : Y.inc st m = maskSum H C mask - entSum C entry) :
    Y.inc st m = gl.val (levelRec k rho C order F t).target -
      (levelRec k rho C order F t).start.value gl (H.worldOf gl mask entry) := by
  obtain ⟨_, _, hp, _, _, _, _, _, _, _, _, hst, _⟩ := levelIn_heard h
  have hFG : Fo.Later F G := (level_world gl (fun _ => 0) (fun _ _ _ => 0) hs h).1
  refine d2_of_public Y st ?_ (fun _ => mask) (fun _ => entry) m ?_
  · rw [hst, Fo.publicPart_later (hFG.trans hL) C (filledA_of_publicPart hp)]
    exact hp
  · rw [hst]
    exact hinc

/-- **(D1) for the merge's record, where the run "back" has made its own claim.** -/
theorem merge_d1 (Y : PscPar GE) (st : Y.St) {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat}
    {F G Fb Fb' H : Fork} {t u : Tape} {wo : WsForkOut}
    (h : flatForkEnd lay cl sv F t = some (wo, G, u)) {S0 : E} {kept row : Aff}
    (hc : ownClaim wo.p S0 kept Fb = some (row, Fb')) (hs : Sized Fb)
    (hfmt : Y.fmt = List.replicate lay.lk (pfCube GE 2) ++ [pDummy GE 1]) (hL : Fo.Later Fb' H)
    (mask : ℕ → GE) (entry : ℕ → ℕ → ℕ → GE) (m : Y.J → GE)
    (hw : ∀ q, m (Y.wAt q) = mask (slotP Y.fmt wo.p.first q)) :
    row = wo.p.rowForm S0 kept ∧
      Y.W st m = place (H.worldOf gl mask entry).slot (Y.vars st) wo.p.first := by
  unfold ownClaim at hc
  obtain ⟨⟨⟨r', p'⟩, G', u'⟩, hr, he⟩ := Option.map_eq_some_iff.1 hc
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  obtain ⟨e1, _, e3⟩ := pscRow_spec hr
  obtain ⟨C, τ, first, a⟩ := (merge_recAt h).1.psc
  refine ⟨e1, d1_ended_at Y st a (fun w hw' => ?_) (by rw [List.length_replicate]; exact hfmt) hs
    e3 hL mask entry m hw⟩
  rw [List.eq_of_mem_replicate hw']
  rfl

/-- The merge's record's start form. -/
theorem merge_startIs {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F G : Fork} {t u : Tape}
    {wo : WsForkOut} (h : flatForkEnd lay cl sv F t = some (wo, G, u)) :
    wo.p.start = wsForkStart sv (powers (tapeEps t) sv.size) := by
  obtain ⟨x, mu, c, beta, v, T, r1, rY, rV, qs, hn, hq, et, hT, hE, _⟩ :=
    hear_ended (hear_of_flat h)
  have ex : tapeEps t = x := by
    rw [et]
    rfl
  rw [ex]
  exact hE.start

/-- **(D2) for the merge's record.** -/
theorem merge_d2 (Y : PscPar GE) (st : Y.St) {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat}
    {F G H : Fork} {t u : Tape} {wo : WsForkOut}
    (h : flatForkEnd lay cl sv F t = some (wo, G, u)) (hL : Fo.Later F H)
    (mask : ℕ → GE) (entry : ℕ → ℕ → ℕ → GE) (m : Y.J → GE)
    (hinc : Y.inc st m = maskSum H (wsForkStart sv (powers (tapeEps t) sv.size)) mask -
      entSum (wsForkStart sv (powers (tapeEps t) sv.size)) entry) :
    Y.inc st m = gl.val wo.p.target - wo.p.start.value gl (H.worldOf gl mask entry) := by
  have hst := merge_startIs h
  refine d2_of_public Y st ?_ (fun _ => mask) (fun _ => entry) m ?_
  · rw [hst, Fo.publicPart_later hL _ (filledA_of_publicPart (merge_recAt h).2.1)]
    exact (merge_recAt h).2.1
  · rw [hst]
    exact hinc

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.fo_paid_later
#print axioms OnBytes.Road.K4.d1_run_at
#print axioms OnBytes.Road.K4.d1_ended_at
#print axioms OnBytes.Road.K4.level_d1
#print axioms OnBytes.Road.K4.level_d2
#print axioms OnBytes.Road.K4.merge_d1
#print axioms OnBytes.Road.K4.merge_startIs
#print axioms OnBytes.Road.K4.merge_d2
