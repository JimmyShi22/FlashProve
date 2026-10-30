-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/OwnPending.lean: THE PENDING ROW ON THE COMMITTED WEIGHTS, AS THE CHAIN's END ASKS
IT OF ITS LAST STATEMENT (`OkMore`, Cb/Pv/Lay/End/LayHEndAt.lean), SAID IN THE WORDS OF THE MERGE's
OWN RECORD. A definition, statements and proofs.

  `pending_iff`: at every `FullPar`, every data D of the chain and every record p with `OutIs` at
    the seventh stage: `OkMore P Ok' (D.z7 x) m` holds exactly if the pending row holds at the
    seventh stage's state, the challenges heard, the further challenge and the end value, all read;
    and Ok'.
  `WoSays P st wo m`: THE NAMED SENTENCE: the library's `Pending` (Cb/Pv/Lay/End/WeightsPay.lean) at
    the row weights of the state st, at the point ψ i := the reading of `wo.rm[i]`, the factor the
    reading of `wo.beta`, the value the reading of `wo.fvp`, on the messages of m.
  `merge_words`: where `flatForkEnd` returns: `wo.rm` is the list of the challenges that `pscT`
    reads off the tape, `wo.beta` its further challenge.
  `k4_pending`: at K4's data `k4Tail`, where the merge's call returns on its named tape
    (`own_calls7`, OwnRecs.lean), under `OutIs` at the seventh stage and hfv: `OkMore P (fun _ _ =>
    True) ((k4Tail …).z7 x) m ↔ WoSays P a.st7 wo m`.

NO NEW ARGUMENT: `OutIs`'s three fields pt, last, vals; `hear_ended` (Said.lean).

Limits. hfv IS A PREMISE: that the value which the ledger shows under the merge's slot (`wo.fvp`)
reads as the word that the values' round sent. `OutIs` at the seventh stage is a premise here
(`stgT_out` gives it from `own_rec7` and `StgFits`). THE STATE st STAYS A TYPED LETTER: that its
element is the reading of the element drawn in front of the merge, and its points those of the
weight claims, is `TailH.Claims`' seventh equation. THAT THE ROW WEIGHTS ARE WHAT `wo.recs` SPELLS
IS NOT SAID. Nothing on soundness.
-/
import Johnson.Road.K4.MergeRec
import Johnson.Road.K4.OwnJoint
import Cb.Pv.Lay.End.LayHEndAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End
open Cb.Pv.Lay.End.Gated (Pending)
open OnBytes OnBytes.K.Kc OnBytes.Slice
open OnBytes.Model (Fork Psc WsLay WsClaim WsForkOut)
open OnBytes.Model.Layer (Pub HPlan2)
open OnBytes.Tie.Pv.Lay (OutIs)
open OnBytes.Tie.Pv.Lay.Eng (TailH)
open OnBytes.Desc.First.P1 (gl pscT NzT Adds7 TailM TailR array_getD_toList getD_read)
open VerifiableInference.Desc.First.MergeLaw (hear_ended hear_of_flat)
open Inst.Model (Scl)

/-- Where the merge returns: its record's challenges are those that `pscT` reads off the tape. -/
theorem merge_words {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F G : Fork} {t u : Tape}
    {wo : WsForkOut} (h : flatForkEnd lay cl sv F t = some (wo, G, u)) :
    wo.rm.toList = (pscT 0 lay.lk (t.drop 1)).rs.map (·.2) ∧
      wo.beta = (pscT 0 lay.lk (t.drop 1)).beta := by
  obtain ⟨⟨C, τ, first, hE⟩, _, _, _⟩ := (merge_recAt h).1
  obtain ⟨x, mu, c, beta, v, T, r1, rY, rV, qs, hn, hq, et, hT, hE', hrm, hb, _⟩ :=
    hear_ended (hear_of_flat h)
  have r1 := hE.r
  have r2 := hE'.r
  rw [r1] at r2
  have hl : ((pscT 0 lay.lk (t.drop 1)).rs.map (·.2)).length =
      ((qs.map fun q => (q.2.1, q.2.2)).map (·.2)).length := by
    have := congrArg List.length r2
    simpa using this
  obtain ⟨a1, a2⟩ := List.append_inj r2 hl
  refine ⟨?_, ?_⟩
  · rw [hrm, a1, List.map_map]
    rfl
  · rw [hb]
    exact (List.cons.inj a2).1.symm

/-- The pending row at equal letters. -/
theorem pending_congr (P0 : FootW0 GE) {g g' : Fin P0.h → GE} {ψ ψ' : Fin P0.k → GE}
    {β β' v v' : GE} (m : P0.J → GE) (hg : g = g') (h1 : ψ = ψ') (h2 : β = β') (h3 : v = v') :
    Pending P0 g ψ β v m ↔ Pending P0 g' ψ' β' v' m := by
  subst hg
  subst h1
  subst h2
  subst h3
  rfl

variable [scl : Scl] {M X : Type}

/-- **The pending row at the chain's last statement, in what was heard.** -/
theorem pending_iff (P : FullPar GE M X) (D : TailH gl (tailF P)) (x : P.XT) {p : Psc}
    (h7 : OutIs gl D.d7 p) (Ok' : (tailF P).s7.Nx → M → Prop) (m : M) :
    OkMore P Ok' (D.z7 x) m ↔
      Pending P.wp0
          (Gated.rowW (fun c : Fin P.wp0.n => D.d7.st.2 ^ (c : ℕ)) (fun c => P.wp0.ten c D.d7.st.1)
            fun i => gl.val (D.d7.H.rs.getD i.1 ([], zeroE)).2)
          (fun i => gl.val (D.d7.H.rs.getD i.1 ([], zeroE)).2) (gl.val D.d7.H.beta) (D.d7.v ())
          (P.msg m) ∧ Ok' (D.z7 x) m := by
  have e1 : (noKept P.wp0.wt.L.Sm).outPt P.wp0.wt.L.Mk D.d7.out =
      fun i => gl.val (D.d7.H.rs.getD i.1 ([], zeroE)).2 := funext h7.pt
  have e2 : (noKept P.wp0.wt.L.Sm).outB P.wp0.wt.L.Mk D.d7.out = gl.val D.d7.H.beta := h7.last
  have e3 : D.d7.out.vals () = D.d7.v () := congrFun h7.vals ()
  exact and_congr (pending_congr P.wp0 (P.msg m) (congrArg (Gated.rowW _ _) e1) e1 e2 e3) Iff.rfl

/-- **The named sentence**: the pending row on the committed weights, in the merge's record's own
words. -/
def WoSays (P : FullPar GE M X) (st : St7 GE P.wp0.n × GE) (wo : WsForkOut) (m : M) : Prop :=
  Pending P.wp0
    (Gated.rowW (fun c : Fin P.wp0.n => st.2 ^ (c : ℕ)) (fun c => P.wp0.ten c st.1)
      fun i => gl.val (wo.rm.getD i.1 zeroE))
    (fun i => gl.val (wo.rm.getD i.1 zeroE)) (gl.val wo.beta) (gl.val wo.fvp) (P.msg m)

/-- **The pending row at K4's data is the named sentence.** -/
theorem k4_pending (Q : FullPar GE M X) {R : TailR} (W : TailM (tailF Q) R) {P : Pub} {hp : HPlan2}
    {t0 u : Tape} {cl : Array WsClaim} {sv : Array Nat} {F G : Fork} {wo : WsForkOut}
    (h : flatForkEnd P.wsLay cl sv F ((ksOf P hp).tcW (t0.drop 1)) = some (wo, G, u))
    (n7 : (tailF Q).s7.n = 0) (nz : NzT (tailF Q) (ksOf P hp) (t0.drop 1)) (a : Adds7 (tailF Q))
    (x : Q.XT) {p : Psc} (h7 : OutIs gl (k4Tail W P hp t0 nz a).d7 p)
    (hfv : (k4Tail W P hp t0 nz a).d7.v () = gl.val wo.fvp) (m : M) :
    OkMore Q (fun _ _ => True) ((k4Tail W P hp t0 nz a).z7 x) m ↔ WoSays Q a.st7 wo m := by
  obtain ⟨w1, w2⟩ := merge_words h
  have eH : (k4Tail W P hp t0 nz a).d7.H =
      pscT 0 P.wsLay.lk (((ksOf P hp).tcW (t0.drop 1)).drop 1) := by
    show pscT (tailF Q).s7.n P.wsLay.lk (((ksOf P hp).tcW (t0.drop 1)).drop 1) = _
    rw [n7]
  have ept : (fun i : Fin Q.wp0.k =>
      gl.val ((k4Tail W P hp t0 nz a).d7.H.rs.getD i.1 ([], zeroE)).2) =
      fun i => gl.val (wo.rm.getD i.1 zeroE) := by
    funext i
    rw [eH, array_getD_toList, w1]
    exact congrArg gl.val (getD_read (fun q : List E × E => q.2) _ i.1 ([], zeroE) zeroE rfl)
  rw [pending_iff Q _ x h7, and_iff_left trivial]
  have eb : gl.val (k4Tail W P hp t0 nz a).d7.H.beta = gl.val wo.beta := by rw [eH, ← w2]
  exact pending_congr Q.wp0 (Q.msg m) (congrArg (Gated.rowW _ _) ept) ept eb hfv

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.pending_iff
#print axioms OnBytes.Road.K4.merge_words
#print axioms OnBytes.Road.K4.k4_pending
