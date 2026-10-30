-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/FoldKeeps.lean: the fold's part of the proximity test keeps the joint.

Proves `FoldKeeps` (Johnson/Desc/K12/Law/JointK.lean) for the fold's part `foldJ` of
Johnson/Desc/K12/Join.lean, which runs `foldD` of Johnson/Desc/First/Close/Closing.lean. Statements
and proofs.
Main names:
  `foldedFit_pure`: what is public of the fold's output, as a switch asks it (`FoldedFit`): the
    library's `foldedFit_of` without its contexts, from pure lemmas alone.
  `foldJ_ok`: what a yes of `foldJ`'s decision holds, unfolded.
  `foldKeeps`: `FoldKeeps X p` for every X whose fold's yes holds `foldJ`'s yes: `foldJ` itself, and
    `foldJ` behind a guard.
Limits: No statement and no proof of this file reaches a routine that runs in a context of the
program `verify-on-bytes` (`OnBytes.Ctx`, `OnBytes.Blk`, `OnBytes.Chan`); that program's plain
records and pure functions, some with names that begin with `Blk.`, and lemmas on them, are used. No
soundness is claimed. Nothing here is about hiding.
-/
import Johnson.Desc.K12.Law.JointK
import Johnson.Desc.K12.Law.FoldLaw

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.FoldLaw (bind_ok)

theorem foldedFit_pure (K : Codes) (s s' : Sg) (cur : IoppStage) (hK : StageCodes s cur K)
    (nc nz : Nat) (hzk : (K.mask[cur.maskCode]?).map codeOf = some s.Z)
    (hc' : (K.base[nc]?).map codeOf = some s'.C) (hz' : (K.mask[nz]?).map codeOf = some s'.Z)
    (hsmall : s.C.a ≤ 32) (S0 S1 : Statement) (row : GroupRow) (L : GroupLayout) (o : Nat)
    (eps claim : E) (gamma : List E) (hcK : S0.codes = K) (hc1 : S1.codes = K)
    (h0 : row.kept = #[]) (hkept : ∀ i, i < L.members.size → L.kept.getD i false = false)
    (hlen : gamma.length = s.h + s.g) (hshape : foldShapeOk S0 (ioppFoldShape cur L) = true)
    (hrow : foldRowOk S1 (ioppFoldShape cur L) row = true) :
    FoldedFit s s' K nc nz (foldOutput S1 (ioppFoldShape cur L) row o eps gamma claim) := by
  obtain ⟨hhk, hcol⟩ := of_foldShapeOk S0 (ioppFoldShape cur L) hshape
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ :=
    foldOutput_fit S1 (ioppFoldShape cur L) row o eps gamma claim (hlen.trans hK.k.symm) hrow hhk
      (by rw [hc1, ← hcK]; exact hcol) h0 hkept
  obtain ⟨cd, hcd, hC⟩ := hK.base
  have ez : (S1.codes.mask.getD cur.maskCode default).ell = s.Z.l := by
    rw [hc1]
    exact congrArg (·.l) hK.mask
  have ec : (S1.codes.base.getD cur.code default).ell = s.C.l := by
    rw [hc1, Array.getD_eq_getD_getElem?, hcd]
    exact congrArg (·.l) hC
  have hcode : (K.base[cur.code]?).map codeOf = some s.C := by
    rw [hcd]
    exact congrArg some hC
  exact ⟨⟨hcode, hzk, hc', hz', o2, rfl, o3, hsmall⟩, o1, o4.trans ez, o5.trans ez,
    fun v hv => (o6 v hv).trans (congrArg ceilLog2 ec),
    order_foldOutput S1 (ioppFoldShape cur L) row o eps gamma claim hrow⟩

theorem needK_ok {n : String} {b : Bool} {u : Unit} (h : H2K.need n b = .ok u) : b = true := by
  unfold H2K.need at h
  cases b with
  | true => rfl
  | false => cases h

theorem needD_ok {n : String} {b : Bool} {u : Unit}
    (h : VerifiableInference.Desc.need n b = .ok u) : b = true := by
  unfold VerifiableInference.Desc.need at h
  cases b with
  | true => rfl
  | false => cases h

theorem mapError_ok {ε ε' α : Type} {f : ε → ε'} {x : Except ε α} {a : α}
    (h : x.mapError f = .ok a) : x = .ok a := by
  cases x with
  | error e => cases h
  | ok y => cases h; rfl

/-- What `back` leaves. -/
theorem back_ok {t t' : T12} {s : H2K.PS} {pass : Passing} {mask : Option Nat}
    (h : back t s pass mask = .ok t') :
    t' = { t with st := s.d.st, book := s.d.book, roots := s.d.roots, pass := pass, mask := mask } ∧
      s.rounds = [] ∧ s.entries = [] ∧ s.d.opened = [] := by
  unfold back at h
  obtain ⟨_, h1, h⟩ := bind_ok h
  have h1' := needD_ok h1
  simp only [Bool.and_eq_true, List.isEmpty_iff] at h1'
  cases h
  exact ⟨rfl, h1'.1.1, h1'.1.2, h1'.2⟩

/-- What a yes of the fold's part holds. -/
theorem foldJ_ok (p : P12) (j : Nat) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t1 : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (row : GroupRow) (L : GroupLayout) (cu : IoppStage)
    (hp : t.pass = .claim row L) (hc : stageAt p j cur = some cu)
    (hn : rs.length = 1 + cu.k)
    (h : (foldJ p j cur cut).decide t rs gs = .ok t1) :
    ∃ (n : Nat × Nat) (rows : SingleRows) (d' : _root_.Desc.Plain.DState Unit)
      (es : List Fmt.Entry),
      p.idx[j + 1]? = some n ∧
      First.Close.foldD p.nums.firstTree ⟨t.st, t.book, t.roots, keyed p cut gs, ()⟩
        (ioppFoldShape cu L) row t.mask es rs = .ok (rows, d') ∧
      t1 = { t with st := Ground.withGroup d'.st n.1 n.2, book := d'.book, roots := d'.roots,
                    pass := .single rows d'.st.groups.size, mask := t.mask } := by
  simp only [foldJ, hp, hc] at h
  cases hi : p.idx[j + 1]? with
  | none => rw [hi] at h; cases h
  | some n =>
    rw [hi] at h
    obtain ⟨⟨rows, s1⟩, hx, h⟩ := bind_ok h
    obtain ⟨⟨gp, s2⟩, hy, h⟩ := bind_ok h
    obtain ⟨rfl, _⟩ := back_ok h
    unfold H2K.foldE at hx
    obtain ⟨_, _, hx⟩ := bind_ok hx
    obtain ⟨_, _, hx⟩ := bind_ok hx
    obtain ⟨⟨rows', d'⟩, hf, hx⟩ := bind_ok hx
    cases hx
    have hf' := mapError_ok hf
    have htake : (lay p cut none t rs gs).rounds.take (1 + (ioppFoldShape cu L).layout.k) = rs := by
      show rs.take (1 + cu.k) = rs
      exact List.take_of_length_le (le_of_eq hn)
    rw [htake] at hf'
    unfold H2K.newGroupE at hy
    cases hg : Ground.newGroupP d' n.1 n.2 with
    | none => simp [hg, H2K.opt, Except.map] at hy
    | some v =>
      simp only [hg, H2K.opt, Except.map] at hy
      cases hy
      unfold Ground.newGroupP at hg
      split at hg
      · cases hg
        exact ⟨n, rows', d', _, rfl, hf', rfl⟩
      · cases hg

theorem spend_st {L : Type} (d d' : _root_.Desc.Plain.DState L) (o : Nat)
    (h : Ground.spendAsMaskP d o = some d') : d'.book = d.book ∧ ShapesKeep d.st d'.st := by
  unfold Ground.spendAsMaskP at h
  split at h
  · cases h
    refine ⟨rfl, fun o' x hx => ?_⟩
    show ∃ x', (d.st.oracles.modify o fun x => { x with spentAsMask := true })[o']? = some x' ∧ _
    rw [Array.getElem?_modify, hx]
    by_cases e : o = o'
    · exact ⟨{ x with spentAsMask := true }, by simp [e], rfl⟩
    · exact ⟨x, by simp [e], rfl⟩
  · cases h

/-- The fold's part keeps the joint. -/
theorem foldKeeps (X : Parts T12) (p : P12)
    (hX : ∀ (j : Nat) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12)
      (rs : List Fmt.RoundView) (gs : Gs), (X.fold p j cur cut).decide t rs gs = .ok t' →
      (foldJ p j cur cut).decide t rs gs = .ok t') : FoldKeeps X p := by
  intro s s' hf n0 e dE dT dS dC fW fZ fG εf εc next q y z g b j cur nxt rest l t t1 rs gs hJ h
  obtain ⟨row, L, cu, restI, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hJ
  obtain ⟨nx, later, rfl, hP, hO, hR, hN⟩ := h4
  obtain ⟨nxt', rest', he, hnx, hlater⟩ := stagesAt_cons h3
  cases he
  replace h := hX _ _ _ _ _ _ _ h
  have hlen : ((PQ.rvSL (ckP .two) (foldRds s dE dT) b.1).map noDigest).length = 1 + cu.k := by
    rw [List.length_map, rvSL_length, hP.codes.k]
    simp [foldRds]
    omega
  obtain ⟨n, rows, d', es, hi, hfd, rfl⟩ := foldJ_ok p j cur _ t t1 _ _ row L cu h1 h2 hlen h
  obtain ⟨hst, id, d1, eps, claim, gamma, hcase, hsp, rfl, hpt, hgl, hshape, _, hrow⟩ :=
    H2K.FoldLaw.foldD_sem s (ioppFoldShape cu L) hP.codes.k hP.codes.h _ _ d' row t.mask es dE dT
      b.1 rows (congrArg (·.l) hP.codes.mask) hfd
  have hc1 : d1.st.codes = t.st.codes := by
    rcases hcase with ⟨_, rfl⟩ | ⟨_, ids, hr, _⟩
    · rfl
    · exact H2K.FoldLaw.recv_codes _ _ _ _ _ hr
  have hcd : d'.st.codes = t.st.codes := (H2K.FoldLaw.spend_codes _ _ _ hsp).trans hc1
  obtain ⟨hbk, hsk⟩ := spend_st _ _ _ hsp
  have hnxc : nx.code = n.1 ∧ nx.maskCode = n.2 := by
    unfold stageAt at hnx
    rw [hi] at hnx
    cases hnx
    exact ⟨rfl, rfl⟩
  have hmc : MaskCase p t (ioppFoldShape cu L) id d1.st d1.book := by
    rcases hcase with ⟨hm, rfl⟩ | ⟨hm, ids, hr, h0⟩
    · exact .inl ⟨hm, rfl, rfl⟩
    · exact .inr ⟨hm, _, ids, d1, hr, h0, rfl, rfl⟩
  have hq : stmG s row = q := h5
  refine ⟨_, d'.st.groups.size, cu, nx, later, rfl, h2, hnx, hlater, ?_, ?_, hR, ?_, ?_, ?_, ?_, ?_,
    h10, ?_, (List.cons.inj h12).1, (List.cons.inj h12).2⟩
  · show StepPub d'.st.codes s s' cu nx n0 dS dC
    rw [hcd]; exact hP
  · show next.Own d'.st.codes nx dS
    rw [hcd]; exact hO
  · show next.Pub d'.st.codes nx later
    rw [hcd]; exact hN
  · rw [hst, hq, hP.n0]
  · show FoldedFit s s' d'.st.codes nx.code nx.maskCode _
    rw [hcd]
    exact foldedFit_pure _ s s' cu hP.codes _ _ hP.zk hP.c' hP.z' hP.small t.st d'.st row L id eps
      claim gamma rfl hcd h6 h7 hgl hshape hrow
  · show (d'.st.groups.push { code := n.1, maskCode := n.2 })[d'.st.groups.size]? = _
    rw [Array.getElem?_push_size, hnxc.1, hnxc.2]
  · rw [h9]
    show (foldRds s dE dT ++ ([dS, dC] ++ next.rds)).length = _
    simp [foldRds]
    omega
  · intro i pos B left ys hB hS hft hop hold hlog hread x hx α
    have := h11 id d1.st d1.book hmc i pos B left ys d'.st row eps claim gamma
      (by rw [← hbk]; exact hB) (hsk.trans hS) hft hop hold h6 hgl hlog hread x hx α
    rw [hpt, hold] at this
    exact this

end H2K.JointK
