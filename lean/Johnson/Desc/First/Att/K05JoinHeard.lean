-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05JoinHeard.lean: `K3Join` (Johnson/Desc/First/Att/K05JoinMeets.lean) from
the library's records on the lookup: `HeardIs` (OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean: the heard
record holds the end values) and four ties of the typed out-statement to the record of end values
`endsOf` (OnBytes/Tie/Pv/Lookup/Forest/FoEnds.lean).

Statements and proofs.
Main names:
  `rho_of_ends`, `zy_of_ends`: the out-statement's point, as a list, is the record's zx, then zy.
  `heard_eC`: gL.e[q], read, is `eC` at the point. By `ends_e` and `eK_eq`.
  `heard_empty`: `emptyE` gL (Johnson/Road/HeadJoin.lean), read, is the padding trees' term of
    `joinRhs` at gL.alpha, read, where gL.shape = h. By `eqTab_val`, `eqTab_top`, `padKey_val` and
    `foldl_add_val`.
  `heard_cEnd`: the worth of gL.cEnd in the world of every later ledger is alpha, less the target,
    plus the mask form. By `FormIs`, `dense_val` and `evalL_scale`.
  `k3join_of_heard`: `K3Join` c gL (G.worldOf Reading.gl mask entry) x0 m.
  `later_of_stays`, `k3join_of_stays`: the same with `Stays` F' G and G.ns = F'.ns
    (Johnson/Desc/First/Att/K5Said.lean) for `Later` F' G: a world does not read the next free
    number.
Premises of `k3join_of_heard`: `FoNums.ok c.h`; four calls; `HeardIs` Reading.gl gL F' En at En :=
endsOf c.h lm jLK rs; gL.shape = c.h; `Later` F' G; the four ties: x0.1.2 = En.theta; x0.2.1.pt t =
(En.zx ++ En.zy).getD t 0; x0.2.1.mf j = dense (mapL ι En.cEndF) j; x0.2.1.tg = En.alpha - En.cEndC;
and: at every place of En.cEndInc the caller's entry at ι p is the world's mask entry. The first,
third and fourth tie are premises of `join_ends` (OnBytes/Tie/Pv/Lookup/Forest/FoJoinOut.lean) too;
the second stands there through the point's weights alone.
Used: pure functions, records and lemmas on them alone; no routine in a context:
`ends_zx_len`, `ends_zy_len`, `rho_ptL`, `rdL_getD`, `foldl_add`, `zext`, `muOf`, `evalL`.
Limits: `HeardIs`, gL.shape = c.h, the four ties and the premise on mask entries are shown for no
run in this file or in what it imports. `HeardIs` has no field for the shape. No soundness of the
protocol is claimed. Nothing on an honest prover, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Port.FoHeard
import OnBytes.Tie.Pv.Lookup.Port.FoTwins
import OnBytes.Tie.Pv.Lookup.Forest.FoEndsE
import Johnson.Desc.First.Att.K05JoinMeets
import Johnson.Desc.First.Att.K5Said

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Cb Cb.Fo Cb.LdLkp Finset
open OnBytes OnBytes.Model
open OnBytes.Ends (eC tauN t0N)
open VerifiableInference.OnPublicFiles (LookupCCaller)

section Pts
variable {h : Forest.Shape} (H : FoNums.ok h = true) (lm jLK : ℕ) (rs : TwV.Rounds Cb.Gl.E) {pt : ℕ → Cb.Gl.E}
  (t2 : ∀ t, pt t = ((Fo.endsOf h lm jLK rs).zx ++ (Fo.endsOf h lm jLK rs).zy).getD t 0)

include H t2 in
/-- The point as a list is the record's two lists. -/
theorem rho_of_ends : Fo.rhoP (h.dT + h.rK) pt = (Fo.endsOf h lm jLK rs).zx ++ (Fo.endsOf h lm jLK rs).zy := by
  have e : pt = Fo.ptL ((Fo.endsOf h lm jLK rs).zx ++ (Fo.endsOf h lm jLK rs).zy) := funext t2
  have hlen : ((Fo.endsOf h lm jLK rs).zx ++ (Fo.endsOf h lm jLK rs).zy).length = h.dT + h.rK := by
    rw [List.length_append, Fo.ends_zx_len h H lm jLK rs, Fo.ends_zy_len h H lm jLK rs]
  rw [e, ← hlen]
  exact Fo.rho_ptL _

include H t2 in
theorem zy_of_ends : Fo.zy h.dT (Fo.rhoP (h.dT + h.rK) pt) = (Fo.endsOf h lm jLK rs).zy := by
  unfold Fo.zy
  rw [rho_of_ends H lm jLK rs t2, ← Fo.ends_zx_len h H lm jLK rs, List.drop_left']
  rfl

end Pts

section Fields
variable {h : Forest.Shape} (H : FoNums.ok h = true) (lm jLK : ℕ) (rs : TwV.Rounds Cb.Gl.E) {pt : ℕ → Cb.Gl.E}
  (t2 : ∀ t, pt t = ((Fo.endsOf h lm jLK rs).zx ++ (Fo.endsOf h lm jLK rs).zy).getD t 0)
  {gL : Forest.Heard} {F' : Fork} (hI : Fo.HeardIs Reading.gl gL F' (Fo.endsOf h lm jLK rs))

include H t2 hI in
/-- A call's weight in the heard record, read, is the library's at the point. -/
theorem heard_eC (q : ℕ) (hq : q < h.NC) : Reading.gl.val (gL.e.getD q zeroE) = eC h pt q := by
  rw [Fo.rdL_getD]
  have e1 : Fo.rdL Reading.gl gL.e = (Fo.endsOf h lm jLK rs).e := hI.e
  rw [e1, Fo.ends_e h H lm jLK rs q hq, ← zy_of_ends H lm jLK rs t2, Fo.eK_eq]

include H t2 hI in
/-- The part of the join on the trees that hold padding alone, read. -/
theorem heard_empty (hsh : gL.shape = h) :
    Reading.gl.val (OnBytes.Road.Hd.emptyE gL) = ∑ y ∈ Ico h.NT (2 ^ h.rK),
      Blocks.eqN h.rK h.dT pt y * (Reading.gl.val gL.alpha - (tauN h 0 (t0N h 0) : Cb.Gl.E)) := by
  unfold OnBytes.Road.Hd.emptyE
  rw [hsh]
  have hzy : Fo.rdL Reading.gl gL.zy = Fo.zy h.dT (Fo.rhoP (h.dT + h.rK) pt) := by
    rw [zy_of_ends H lm jLK rs t2]
    exact hI.zy
  have hpad : Reading.gl.val (gL.padKey 0) = (tauN h 0 (t0N h 0) : Cb.Gl.E) := by
    unfold Forest.Heard.padKey
    rw [hsh, Fo.padKey_val Reading.gl h gL.theta 0 (by norm_num)]
    unfold Fo.padKeyK
    simp only [Nat.cast_zero, zero_mul, add_zero]
    rfl
  rw [Fo.foldl_add_val Reading.gl
    (fun i => mulE ((Model.eqTab gL.zy).getD (h.NT + i) zeroE) (subE gL.alpha (gL.padKey 0)))
    (fun i => Blocks.eqN h.rK h.dT pt (h.NT + i) *
      (Reading.gl.val gL.alpha - (tauN h 0 (t0N h 0) : Cb.Gl.E))) _ _ (fun i hi => by
        have hi' : h.NT + i < 2 ^ h.rK := by
          have := List.mem_range.1 hi
          omega
        rw [Reading.gl.mul, Reading.gl.sub, hpad, Fo.rdL_getD, Fo.eqTab_val, hzy, Fo.eqTab_top h pt _ hi']),
    Fo.foldl_add, Reading.gl.zero, zero_add, Finset.sum_Ico_eq_sum_range]
  induction (2 ^ h.rK - h.NT) with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

include hI in
/-- The worth of the heard record's cEnd, at every later ledger. -/
theorem heard_cEnd {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (ι : Fo.Pl → Option J₀) {G : Fork} (hL : Fo.Later F' G)
    (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) {mf : Option J₀ → Cb.Gl.E} {tg : Cb.Gl.E}
    (t3 : ∀ j, mf j = TwV.dense (Fo.mapL ι (Fo.endsOf h lm jLK rs).cEndF) j)
    (t4 : tg = (Fo.endsOf h lm jLK rs).alpha - (Fo.endsOf h lm jLK rs).cEndC) (ν : Option J₀ → Cb.Gl.E)
    (hν : ∀ pc ∈ (Fo.endsOf h lm jLK rs).cEndInc, ν (ι pc.1) = Fo.muOf mask pc.1) :
    gL.cEnd.value Reading.gl (G.worldOf Reading.gl mask entry) =
      Reading.gl.val gL.alpha - tg + ∑ i, mf i * ν i := by
  rw [((hI.cEnd G hL).2 mask entry), hI.alpha, t4]
  simp only [t3]
  rw [Fo.dense_val]
  have eF : (Fo.endsOf h lm jLK rs).cEndF = TwV.scale (-1) (Fo.endsOf h lm jLK rs).cEndInc := rfl
  have e1 : ((Fo.mapL ι (Fo.endsOf h lm jLK rs).cEndF).map fun pc => pc.2 * ν pc.1).sum =
      - Fo.evalL (Fo.muOf mask) (Fo.endsOf h lm jLK rs).cEndInc := by
    rw [eF]
    have a : ((Fo.mapL ι (TwV.scale (-1) (Fo.endsOf h lm jLK rs).cEndInc)).map fun pc => pc.2 * ν pc.1).sum =
        Fo.evalL (fun p => ν (ι p)) (TwV.scale (-1) (Fo.endsOf h lm jLK rs).cEndInc) := by
      unfold Fo.mapL Fo.evalL
      rw [List.map_map]
      rfl
    have b : Fo.evalL (fun p => ν (ι p)) (Fo.endsOf h lm jLK rs).cEndInc =
        Fo.evalL (Fo.muOf mask) (Fo.endsOf h lm jLK rs).cEndInc := by
      unfold Fo.evalL
      exact congrArg List.sum (List.map_congr_left fun pc hpc => congrArg (pc.2 * ·) (hν pc hpc))
    rw [a, Fo.evalL_scale, b]
    ring
  rw [e1]
  ring

end Fields

section Whole
variable (c : LookupCCaller)

/-- **K3Join from the library's own records.** -/
theorem k3join_of_heard (ok : FoNums.ok c.h = true) (nc : c.h.NC = 4) (lm jLK : ℕ) (rs : TwV.Rounds Cb.Gl.E)
    (ι : Fo.Pl → Option c.J₀) {gL : Forest.Heard} {F' G : Fork}
    (hI : Fo.HeardIs Reading.gl gL F' (Fo.endsOf c.h lm jLK rs)) (hsh : gL.shape = c.h) (hL : Fo.Later F' G)
    (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) {x0 : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)}
    {m : c.Sg.Msg} (t1 : x0.1.2 = (Fo.endsOf c.h lm jLK rs).theta)
    (t2 : ∀ t, x0.2.1.pt t = ((Fo.endsOf c.h lm jLK rs).zx ++ (Fo.endsOf c.h lm jLK rs).zy).getD t 0)
    (t3 : ∀ j, x0.2.1.mf j = TwV.dense (Fo.mapL ι (Fo.endsOf c.h lm jLK rs).cEndF) j)
    (t4 : x0.2.1.tg = (Fo.endsOf c.h lm jLK rs).alpha - (Fo.endsOf c.h lm jLK rs).cEndC)
    (hν : ∀ pc ∈ (Fo.endsOf c.h lm jLK rs).cEndInc, zext (c.msg₀ m) (ι pc.1) = Fo.muOf mask pc.1) :
    K3Join c gL (G.worldOf Reading.gl mask entry) x0 m where
  theta := hI.theta.trans t1.symm
  e := fun q => heard_eC ok lm jLK rs t2 hI q.1 (by rw [nc]; exact q.2)
  empty := heard_empty ok lm jLK rs t2 hI hsh
  cEnd := heard_cEnd lm jLK rs hI ι hL mask entry t3 t4 _ hν

/-- What lies under a slot stays, at the same number of slots: a later state in the library's sense,
once the next free number is set high enough. -/
theorem later_of_stays {F G : Fork} (hs : Stays F G) (hn : G.ns = F.ns) :
    Fo.Later F ({ G with next := max F.next G.next } : Fork) :=
  ⟨Nat.le_max_left _ _, hn, fun j hj => by
    obtain ⟨a, b, d⟩ := hs j _ _ ⟨hj, rfl, rfl⟩
    exact ⟨a, b, d⟩⟩

/-- **The same at every ledger in which what lay under the lookup's slots stays**: the next free
number is not read by a world. -/
theorem k3join_of_stays (ok : FoNums.ok c.h = true) (nc : c.h.NC = 4) (lm jLK : ℕ) (rs : TwV.Rounds Cb.Gl.E)
    (ι : Fo.Pl → Option c.J₀) {gL : Forest.Heard} {F' G : Fork}
    (hI : Fo.HeardIs Reading.gl gL F' (Fo.endsOf c.h lm jLK rs)) (hsh : gL.shape = c.h) (hs : Stays F' G)
    (hn : G.ns = F'.ns) (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    {x0 : TX (c.St₀ × Cb.Gl.E) Cb.Gl.E (Option c.J₀)} {m : c.Sg.Msg}
    (t1 : x0.1.2 = (Fo.endsOf c.h lm jLK rs).theta)
    (t2 : ∀ t, x0.2.1.pt t = ((Fo.endsOf c.h lm jLK rs).zx ++ (Fo.endsOf c.h lm jLK rs).zy).getD t 0)
    (t3 : ∀ j, x0.2.1.mf j = TwV.dense (Fo.mapL ι (Fo.endsOf c.h lm jLK rs).cEndF) j)
    (t4 : x0.2.1.tg = (Fo.endsOf c.h lm jLK rs).alpha - (Fo.endsOf c.h lm jLK rs).cEndC)
    (hν : ∀ pc ∈ (Fo.endsOf c.h lm jLK rs).cEndInc, zext (c.msg₀ m) (ι pc.1) = Fo.muOf mask pc.1) :
    K3Join c gL (G.worldOf Reading.gl mask entry) x0 m :=
  k3join_of_heard c ok nc lm jLK rs ι hI hsh (later_of_stays hs hn) mask entry t1 t2 t3 t4 hν

end Whole

end VerifiableInference.Desc.First.Att.P
