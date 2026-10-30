-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/FlatWindow.lean: CONDITIONAL.

What is here. THE LEDGER IS READY FOR THE PART's TEXT OF THE MASKED SUMCHECK (`LedgerReady`,
Johnson/Desc/Part/MaskedSumReady.lean) AT A TOKEN SUMCHECK AND AT THE MERGE, WITHOUT A PREMISE ON
ROOM. The flat functions of these two lay nothing under the sumcheck's own slots; a later step of
the verifier lays them, when it makes the row. That this later laying RETURNS, at a ledger later
than the one that the flat function leaves, says that the slots were free all the while. So the two
statements of FlatTops.lean that ask room are had with that return in its stead. Statements and
proofs.

  `free_of_later`   a slot that a later laying found free was free
  `tscWs_sum`, `tsc_ready`   **a token sumcheck**
  `plain_sum`, `merge_ready`   **the merge**
  `rows_win`, `merge_win`   the two statements of FlatTops.lean without room

Limits. Premises: the flat function returns, from a sized ledger; THE LATER LAYING OF THE SUMCHECK's
OWN SLOTS RETURNS, at a sized ledger that is later than the one which the flat function leaves; the
call has at least one end value; the call's variables bear the sumcheck's weights (hk); at a token
sumcheck the laying of the claimed sum returns the ledger G0 (hG0: a naming: `rows_win` has it from
the flat function's return). ONE DIRECTION: FROM RETURNS: the premise on room is not paid here but
moved: behind a step of the verifier that has accepted, the later laying's return is at hand; in a
statement that is to show that the verifier accepts, it is a thing to be shown. For `rows_win` and
`merge_win`: all other premises of `rows_top` and `merge_top` (FlatTops.lean), the start among them.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatTops

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE subE)
open OnBytes.Model (Reading Aff Fork World Tsc WsLay WsClaim WsForkOut wsForkStart powers ledNO)
open OnBytes.PscRun (Sized Filled)
open OnBytes.Slice (GE)
open OnBytes.K.Kc (Fl Tape flatForkEnd)
open OnBytes.Desc.First.P1 (tscWs tscIn_tape tapeCl tapeEps walk_length filledA_of_publicPart)
open OnBytes.Desc.First.K4 (rowsSummand)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc.Part.MaskedSum
open VerifiableInference.Desc.First.MergeLaw (hear_ended hear_of_flat)
open ProofFile.Honest.SumLaw

variable {V : Type}

/-- A slot that a run of layings at a later ledger found free was free. -/
theorem free_of_later {F Fz F1 : Fork} {first : ℕ} {v : Array E} {f : E} (hL : Fo.Later F Fz)
    (hSz : Sized Fz) (hW : Fz.hideRun first v f = some F1) (i : ℕ) (hi : i < v.size) :
    ¬ Filled F (first + i) := fun hf =>
  ((OnBytes.PscRun.hideRun_ok Fz F1 first v f hSz hW).2.2.1 i hi).2.1 (hL.keep _ hf).1

/-- A token sumcheck's weights: two slots each. -/
theorem tscWs_sum : ∀ zs : List E, ((tscWs zs).map fun w => w.d - 1).sum = 2 * zs.length
  | [] => rfl
  | z :: zs => by
    have ih := tscWs_sum zs
    show 2 + ((tscWs zs).map fun w => w.d - 1).sum = _
    rw [ih, List.length_cons]
    omega

/-- **A token sumcheck.** G0: the ledger behind the laying of the claimed sum. Fz: the later ledger
at which the sumcheck's own slots are laid. -/
theorem tsc_ready {P : Array E} {lt n dY : ℕ} {F G G0 Fz F1 : Fork} {t u : Tape} {o : Tsc} {f : E}
    (hF : Fl.tscIn P lt n dY F t = some (o, G, u)) (hS : Sized F)
    (hG0 : ({ F with next := F.next + 1 } : Fork).hideRun F.next #[tapeCl t] oneE = some G0)
    (vs : List Var) (hk : vs.map Var.weight = tscWs (P.toList.take lt)) (hn : 1 ≤ n)
    (hL : Fo.Later G Fz) (hSz : Sized Fz)
    (hW : Fz.hideRun o.p.first (Array.replicate o.p.walk.1.length zeroE) f = some F1) :
    LedgerReady (Aff.slot F.next) ⟨1, vs, some ⟨dY, n⟩⟩ G0 := by
  obtain ⟨_, T, cl, mu0, eps, rs, sentY, beta, w0, wY, wV, ms, y, v1, v, G0', ht, hrs, _, hms, hyy,
    hv1, _, _, hG0', hTp, a1, hy, hheld, _, hvars, hr, _, _, _, _, hfirst, _, hsE, hvn, hrun⟩ :=
    tscIn_tape hF
  have ecl : tapeCl t = cl := by
    rw [ht]
    rfl
  have eG : G0' = G0 := by
    rw [hv1, ← ecl, hG0] at hG0'
    exact (Option.some.inj hG0').symm
  rw [eG] at hTp hfirst hrun hsE
  have hF1 : Sized ({ F with next := F.next + 1 } : Fork) := hS
  have hS0 : Sized G0 := (OnBytes.PscRun.hideRun_ok _ G0 _ _ _ hF1 hG0).2.1
  have hvl : vs.length = (P.toList.take lt).length := by
    have e := congrArg List.length hk
    rw [List.length_map] at e
    rw [e, tscWs, List.length_map]
  have hd : ∀ v ∈ vs, v.d = 3 := weights_d vs _ hk (by
    intro w hw
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hw
    rfl)
  have hown : ownSlots (Call.all ⟨1, vs, some ⟨dY, n⟩⟩) =
      1 + 2 * (P.toList.take lt).length + dY := by
    show ownSlots (vs ++ [Var.point zeroE (dY + 1)]) = _
    rw [own_count vs hd dY, hvl]
  have hm1 : (ms ++ [y]).map (·.1) =
      tscWs (P.toList.take lt) ++ [OnBytes.Psc.Weight.atZero (dY + 1)] := by
    rw [List.map_append, a1, List.map_cons, List.map_nil, hy]
  have hwl : o.p.walk.1.length = 1 + 2 * (P.toList.take lt).length + dY := by
    rw [walk_length (ms := ms ++ [y]) (by simp) (by rw [hvars, hm1]) hr hheld, hm1,
      OnBytes.Psc.hidingEntries, List.map_append, List.sum_append, tscWs_sum]
    show 1 + (2 * (P.toList.take lt).length + (dY + 1 - 1 + 0)) = _
    omega
  have hS0' : Sized ({ G0 with
      next := G0.next + 1 + 2 * (P.toList.take lt).length + dY + n } : Fork) := hS0
  obtain ⟨_, _, hin, hout⟩ := OnBytes.PscRun.hideRun_ok _ G o.sEnd v y.2.2 hS0' hrun
  refine ⟨hS0, filledA_of_publicPart hTp, ?_, ?_⟩
  · have b := (hin (n - 1) (by omega)).1
    have b' : o.sEnd + (n - 1) < G0.ns := b
    rw [hown]
    show G0.next + (1 + 2 * (P.toList.take lt).length + dY) + n ≤ G0.ns
    omega
  · intro j h1 h2
    rw [hown] at h2
    have h2' : j < G0.next + (1 + 2 * (P.toList.take lt).length + dY) + n := h2
    by_cases hj : j < o.sEnd
    · intro hf
      have hfG : Filled G j := (hout j (Or.inl hj)).2.2.mpr hf
      have c := free_of_later hL hSz hW (j - G0.next) (by rw [Array.size_replicate, hwl]; omega)
      rw [hfirst, show G0.next + (j - G0.next) = j by omega] at c
      exact c hfG
    · have c := (hin (j - o.sEnd) (by omega)).2.1
      rw [show o.sEnd + (j - o.sEnd) = j by omega] at c
      exact c

/-- Plain weights of three coefficients: two slots each. -/
theorem plain_sum : ∀ n : ℕ,
    ((List.replicate n (OnBytes.Psc.Weight.plain 3)).map fun w => w.d - 1).sum = 2 * n
  | 0 => rfl
  | n + 1 => by
    have ih := plain_sum n
    rw [List.replicate_succ]
    show 2 + ((List.replicate n (OnBytes.Psc.Weight.plain 3)).map fun w => w.d - 1).sum = _
    rw [ih]
    omega

/-- **The merge.** Fz: the later ledger at which the sumcheck's own slots are laid. -/
theorem merge_ready {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F G Fz F1 : Fork}
    {t u : Tape} {wo : WsForkOut} {f : E} (hF : flatForkEnd lay cl sv F t = some (wo, G, u))
    (hS : Sized F) (vs : List Var)
    (hk : vs.map Var.weight = List.replicate lay.lk (OnBytes.Psc.Weight.plain 3))
    (hL : Fo.Later G Fz) (hSz : Sized Fz)
    (hW : Fz.hideRun wo.p.first (Array.replicate wo.p.walk.1.length zeroE) f = some F1) :
    LedgerReady (wsForkStart sv (powers (tapeEps t) sv.size)) ⟨0, vs, some ⟨1, 1⟩⟩ F := by
  obtain ⟨x, mu, c, beta, v, T, r1, rY, rV, qs, hn, _, et, hTp, hE, _, _, hsF, hhide, _, _⟩ :=
    hear_ended (hear_of_flat hF)
  have ex : tapeEps t = x := by
    rw [et]
    rfl
  have hvl : vs.length = lay.lk := by
    have e := congrArg List.length hk
    rw [List.length_map, List.length_replicate] at e
    exact e
  have hd : ∀ v ∈ vs, v.d = 3 := weights_d vs _ hk (by
    intro w hw
    rw [List.eq_of_mem_replicate hw]
    rfl)
  have hown : ownSlots (Call.all ⟨0, vs, some ⟨1, 1⟩⟩) = 1 + 2 * lay.lk + 1 := by
    show ownSlots (vs ++ [Var.point zeroE (1 + 1)]) = _
    rw [own_count vs hd 1, hvl]
  have hwl : wo.p.walk.1.length = 1 + 2 * lay.lk + 1 := by
    rw [hE.walkLen, OnBytes.Psc.hidingEntries, List.map_append, List.sum_append, plain_sum]
    rfl
  have hF' : Sized ({ F with next := F.next + 1 + 2 * lay.lk + 2 } : Fork) := hS
  obtain ⟨_, _, hin, hout⟩ := OnBytes.PscRun.hideRun_ok _ G wo.sFv #[v] beta hF' hhide
  rw [ex]
  refine ⟨hS, filledA_of_publicPart hTp, ?_, ?_⟩
  · have b := (hin 0 (by simp)).1
    have b' : wo.sFv + 0 < F.ns := b
    rw [hown]
    show F.next + (1 + 2 * lay.lk + 1) + 1 ≤ F.ns
    omega
  · intro j h1 h2
    rw [hown] at h2
    have h2' : j < F.next + (1 + 2 * lay.lk + 1) + 1 := h2
    by_cases hj : j < wo.sFv
    · intro hf
      have hfG : Filled G j := (hout j (Or.inl hj)).2.2.mpr hf
      have c' := free_of_later hL hSz hW (j - F.next) (by rw [Array.size_replicate, hwl]; omega)
      rw [hE.first, show F.next + (j - F.next) = j by omega] at c'
      exact c' hfG
    · have c' := (hin 0 (by simp)).2.1
      rw [show wo.sFv + 0 = j by omega] at c'
      exact c'

/-- **The row products, without room.** F0: the ledger in front of the claimed sum's laying. Fz: the
later ledger at which the verifier reads the shown values and lays the sumcheck's own slots. -/
theorem rows_win (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (rowsSum Q)) (st : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (F0 : Fork) (Wd : World GE)
    (hd : drawsOk ((rowsSum Q).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (rowsSum Q)) c st seen ds = some rounds)
    (hs : ∀ i, i < ownSlots ((rowsSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (F0.next + 1 + i) = hidingCoin c i)
    (j : Job) (hj : jobRows Q st.input (ptsOf Q st.input st.heard) = some j)
    (hxl : Q.P.y.h.xl = 5) (hNI : 1 ≤ Q.P.y.NI) (H : OnBytes.Model.Layer.Heard)
    (hom : H.omV = (ptsOf Q st.input st.heard).omV)
    (hσ : (Aff.slot F0.next).value Reading.gl Wd = Reading.gl.val j.cube.total)
    {tp u : Tape} {G2 : Fork} {o : Tsc}
    (hF : Fl.tscIn (ptsOf Q st.input st.heard).PV Q.P.y.h.lt (ledNO Q.P.y.h.xl * Q.P.y.NI) 2 F0 tp =
      some (o, G2, u))
    (hS : Sized F0) (hT : TapeIs tp rounds) (Fz F1 : Fork) (sh : Array E) (hL : Fo.Later G2 Fz)
    (hSz : Sized Fz)
    (hW : Fz.hideRun o.p.first (Array.replicate o.p.walk.1.length zeroE) (subE zeroE oneE) =
      some F1)
    (hsh : ((Array.range (4 * Q.P.y.NI)).mapM fun i => Fz.shown (o.sEnd + i)) = some sh) :
    (o.p.rowForm (rowsSummand Q.P.y H sh) {}).value Reading.gl Wd = 0 := by
  obtain ⟨_, T, cl, mu0, eps, rs, sentY, beta, w0, wY, wV, ms, y, v1, v, F, ht, _, _, _, _,
    hv1, _, _, hG0', _⟩ := tscIn_tape hF
  have ecl : tapeCl tp = cl := by
    rw [ht]
    rfl
  have hG0 : ({ F0 with next := F0.next + 1 } : Fork).hideRun F0.next #[tapeCl tp] oneE =
      some F := by
    rw [ecl, ← hv1]
    exact hG0'
  have hF1 : Sized ({ F0 with next := F0.next + 1 } : Fork) := hS
  have hnext : F.next = F0.next + 1 := (OnBytes.PscRun.hideRun_ok _ F _ _ _ hF1 hG0).1.next
  have h4 : 1 ≤ ledNO Q.P.y.h.xl * Q.P.y.NI := by
    rw [hxl]
    show 1 ≤ 4 * Q.P.y.NI
    omega
  obtain ⟨h, G, hh, hf⟩ := k4_hears (V := V) name endName (rowsSum Q) c st seen ds rounds
    (Aff.slot F0.next) F (shapeOk_token _ (by norm_num) h4) hd ha
    (tsc_ready hF hS hG0 _
      (rows_weights Q st.input (frontOf st seen) j (ledNO Q.P.y.h.xl * Q.P.y.NI) hj) h4 hL hSz hW)
  exact rows_flat_zero (V := V) name endName Q c st seen ds rounds F0 F G h Wd hd ha hh
    (by rw [hf, hnext]; exact hs) j hj hxl H hom hσ hF hS hG0 hT Fz sh hL hsh

/-- **The merge, without room.** tp: the tape, the batching round first. Fz: the later ledger at
which the verifier lays the sumcheck's own slots. -/
theorem merge_win (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (mergeSum Q)) (st : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (F : Fork) (Wd : World GE)
    {cl : Array WsClaim} {sv : Array Nat} {tp u : Tape} {G2 : Fork} {wo : WsForkOut}
    (hd : drawsOk ((mergeSum Q).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (mergeSum Q)) c st seen ds = some rounds)
    (hs : ∀ i, i < ownSlots ((mergeSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (F.next + i) = hidingCoin c i)
    (cls : List WsClaim) (hc : mergeClaimsAt Q st.input (ptsOf Q st.input st.heard) = some cls)
    (hσ : (wsForkStart sv (powers (tapeEps tp) sv.size)).value Reading.gl Wd = Reading.gl.val
      (mergeJobOf Q.P.wsLay st.input.w cls (ptsOf Q st.input st.heard).rhoW).cube.total)
    (hF : flatForkEnd Q.P.wsLay cl sv F tp = some (wo, G2, u)) (hS : Sized F)
    (hT : TapeIs (tp.drop 1) rounds) (Fz F1 : Fork) (hL : Fo.Later G2 Fz) (hSz : Sized Fz)
    (hW : Fz.hideRun wo.p.first (Array.replicate wo.p.walk.1.length zeroE) (subE zeroE oneE) =
      some F1) :
    (wo.p.rowForm wo.fvp {}).value Reading.gl Wd = 0 := by
  obtain ⟨h, G, hh, hf⟩ := k4_hears (V := V) name endName (mergeSum Q) c st seen ds rounds
    (wsForkStart sv (powers (tapeEps tp) sv.size)) F
    (shapeOk_plain _ (Nat.le_refl 1) (Nat.le_refl 1)) hd ha
    (merge_ready hF hS _ (merge_weights Q st.input (frontOf st seen)) hL hSz hW)
  exact merge_flat_zero (V := V) name endName Q c st seen ds rounds F G h Wd hd ha hh
    (by rw [hf]; exact hs) cls hc hσ hF hS hT

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.free_of_later
#print axioms ProofFile.Honest.K4.tscWs_sum
#print axioms ProofFile.Honest.K4.tsc_ready
#print axioms ProofFile.Honest.K4.plain_sum
#print axioms ProofFile.Honest.K4.merge_ready
#print axioms ProofFile.Honest.K4.rows_win
#print axioms ProofFile.Honest.K4.merge_win
