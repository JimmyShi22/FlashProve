-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/SwitchKeeps.lean: the code switch's part of the proximity test, with the
batching behind it, keeps the joint.

Proves `SwitchKeeps` (Johnson/Desc/K12/Law/JointK.lean) from the two propositions `SwitchUnfolds`
and `SeatReads` (Johnson/Desc/K12/Law/SwDid.lean), over `did_claim`
(Johnson/Desc/K12/Law/SwClaim.lean) and Johnson/Desc/K12/Law/SwTies.lean. Statements and proofs.
Main names:
  `keyed_mem`: a column under the keys of Johnson/Desc/K12/Join.lean lies in one of the groups.
  `lastReads`: columns that are the written last tree's give `LastTie` at the standard readings.
  `did_drawn`: the positions that the library reads off the written round "CS" are drawn in the
    round as shown.
  `switchKeeps`: `SwitchKeeps X p` for every X whose switch's part and batching behind it hold the
    yes of those of Join.lean, at a place with one answer to a sample and early masks, under the two
    propositions.
Limits: The words of the stage behind a switch are the chain's readings of the switch's own written
message "SEND seed" (`Chain.ReadAs`): the stage's message and the mask that comes with it stand in
one tree, sent in that round, in front of that round's own draw and so of every later draw of the
test. No statement and no proof of this file reaches a routine that runs in a context of the
program `verify-on-bytes` (`OnBytes.Ctx`, `OnBytes.Blk`, `OnBytes.Chan`); that program's plain
records and pure functions, some with names that begin with `Blk.`, and lemmas on them, are used. No
soundness is claimed. Nothing here is about hiding.
-/
import Johnson.Desc.K12.Law.SwTies
import Johnson.Desc.K12.Law.BaseGives

set_option autoImplicit false
namespace H2K.Sw
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK

theorem keyed_mem (p : P12) (cut : List Fmt.DeclaredRound) (gs : Gs) (c : Nat × Nat × List UInt64)
    (h : c ∈ keyed p cut gs) : ∃ grp ∈ gs, (c.2.1, c.2.2) ∈ grp := by
  unfold keyed at h
  obtain ⟨x, hx, hc⟩ := List.mem_flatMap.1 h
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hc
  exact ⟨x.2, (List.of_mem_zip hx).2, hy⟩

theorem four_cut (w : List UInt64) (q : Fmt.M1.E × Fmt.M1.E × Fmt.M1.E × Fmt.M1.E)
    (h : Prox.four w = some q) :
    Fmt.M1.cutCol 0 2 2 w = some ([q.1, q.2.1], [q.2.2.1, q.2.2.2]) := by
  unfold Prox.four at h
  split at h
  · cases h
    rfl
  · cases h

theorem lastReads (s : Sg) (d : PQ.RD) (o : (wRound d).Orc) (gs : Gs)
    (h : ∀ grp ∈ gs, ∀ x ∈ grp, x.2 = colW d o x.1) :
    LastTie s (wordIn s (lastColW d o)) (wordMk s (lastMk d o)) gs := by
  refine ⟨lastColW d o, lastMk d o, rfl, rfl, fun grp hg x q hq => ?_⟩
  unfold Prox.colOf at hq
  cases hf : grp.find? (·.1 == x) with
  | none => rw [hf] at hq; cases hq
  | some yy =>
    rw [hf] at hq
    have hm := List.mem_of_find?_eq_some hf
    have hx := List.find?_some hf
    simp only [beq_iff_eq] at hx
    have hw := h grp hg yy hm
    rw [hx] at hw
    have h4 : Prox.four yy.2 = some q := hq
    rw [hw] at h4
    refine lastQ_tie d o x q ?_
    unfold lastQ
    rw [four_cut _ _ h4]

section
variable {ft : Nat} {cols : List Tw.L9.Col} {old : SingleRows} {T : SwitchTarget}
  {gp : ℕ} {others : Array OracleNotice} {S S' : Statement} {Bk Bk' : TreeBook}
  {roots : Nat} {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : Taken}

theorem did_drawn {s s' : Sg} (dS dC : PQ.RD) (hr : CsRounds s s' dS dC)
    (τ : Tr (PQ.uL (ckP .two) [dS, dC]))
    (hp : [D.rS, D.rC] = (PQ.rvSL (ckP .two) [dS, dC] τ).map noDigest) (i : Fin s.t) :
    ((gCs s.C.a s.t _ (valsOf dC τ.2.2.2.1)).1 i).val ∈ D.rC.drawn.poss := by
  injection hp with _ e2
  injection e2 with eC _
  have poC : D.rC.drawn.poss = (rvOf dC τ.2.2.1 τ.2.2.2.1).poss := by rw [eC]; rfl
  obtain ⟨alpha, th, xs, hrv, hxs, _, _, hQ⟩ := cs_read hr.cs τ.2.2.1 τ.2.2.2.1
  rw [hrv] at poC
  rw [poC, hQ i, List.getD_eq_getElem _ _ (by rw [hxs]; exact i.isLt)]
  exact List.getElem_mem _

end

/-- The switch's part with the batching behind it keeps the joint, under `SwitchUnfolds` and
`SeatReads`. -/
theorem switchKeeps (X : Parts T12) (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (hXs : ∀ (j : Nat) (cur nxt : Fmt.M1.Stage) (last : Bool) (cut : List Fmt.DeclaredRound)
      (t t' : T12) (rs : List Fmt.RoundView) (gs : Gs),
      (X.switch p j cur nxt last cut).decide t rs gs = .ok t' →
      (switchJ p j cur nxt last cut).decide t rs gs = .ok t')
    (hXb : ∀ (j : Nat) (nxt : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12)
      (rs : List Fmt.RoundView) (gs : Gs), (X.batBehind p j nxt cut).decide t rs gs = .ok t' →
      (behindJ p j nxt cut).decide t rs gs = .ok t')
    (hU : SwitchUnfolds p) (hR : SeatReads) : SwitchKeeps X p := by
  intro s s' hf n0 dE dT dS dC fW fZ fG next q y z τF τC bN j cur nxt rest l t1 t2 t3 gs hK h2 h3 _
  obtain ⟨rows, gp, cu, nx, later, k1, k2, k3, k4, hP, hO, hRd, hN, hcl, hfit, hgrp, hlen, hshown,
    hread, hst, hstages⟩ := hK
  have hk : cur.k = s.h + s.g := by rw [← hst]; rfl
  have hcuk : cu.k = cur.k := stageAt_k k2
  have hK' := hN.codes
  obtain ⟨out, row', L', theta, D, hrS, hrC, hdid, hpass, hmask⟩ :=
    hU j cur nxt rest.isEmpty (cutS l cur.k) t1 t2 t3 _ _ (grpS l cur.k gs) rows gp nx he ha k1 k3
      (hXs _ _ _ _ _ _ _ _ _ h2) (hXb _ _ _ _ _ _ _ h3)
  rw [hK'.k, hK'.h] at hdid
  have hp : [D.rS, D.rC] = (PQ.rvSL (ckP .two) [dS, dC] τC).map noDigest := by
    rw [hrS, hrC]
    rfl
  have hG : D.G = { code := nx.code, maskCode := nx.maskCode } :=
    Option.some.inj (hdid.group0.symm.trans hgrp)
  have hm : D.G.members = #[] := by rw [hG]
  have hkp : D.G.kept = #[] := by rw [hG]
  have hr : D.G.rows = #[] := by rw [hG]
  have hpos : out.positions = Positions.ofDraws s.C.a (rvOf dC τC.2.2.1 τC.2.2.2.1).poss := by
    have h1 := hdid.logN_eq hfit.prog
    rw [hdid.positions] at h1
    have h1' : D.code.logN = s.C.a := h1
    rw [hdid.positions, h1', hrC]
    rfl
  -- what was read is the folded words
  have hy : ∀ i α, s.cMid.T (foldWords s y z (foldPt s dE dT τF))
      ((gCs s.C.a s.t _ (valsOf dC τC.2.2.2.1)).1 i) α =
      symS s rows out.positions D.y ((gCs s.C.a s.t _ (valsOf dC τC.2.2.2.1)).1 i).val α := by
    obtain ⟨i0, left, i1, i2, i3, i4, i5, i6⟩ := hdid.read
    intro i α
    exact hread i0 out.positions t3.book left D.y (by rw [i2]; exact hdid.bookKeepsB)
      (by rw [i1]; exact hdid.shapesKeepB) i3 (by rw [i4, hcuk]) i5 hpos i6 _
      (hdid.listed _ (did_drawn dS dC hP.rounds τC hp i)) α
  have hclaim := did_claim hf dS dC hP.rounds τC hdid hp hfit.prog hfit.kept hG hfit.d0 hfit.d1
    hfit.vars hP.bits _ hy
  rw [hcl] at hclaim
  have hL := hdid.lay_eq hm hkp
  have hcodes : t3.st.codes = t1.st.codes := hdid.codes
  have hlen' : (l.drop (cur.k + 3)).length = next.rds.length := by
    rw [List.length_drop, hlen, hk]
    omega
  have hkeptL : ∀ i, i < L'.members.size → L'.kept.getD i false = false := by
    intro i hi
    have hl := hdid.layAt hm hkp
    refine hl.kept i ?_
    rw [hl.members] at hi
    exact hi
  rw [← hk] at hshown
  cases next with
  | last s' e dL dB fu fs εb =>
    have hrest : rest = [] := (List.cons.inj hstages).2.symm
    subst hrest
    have hO' : LastOwn t1.st.codes s' nx dS := hO
    have hkL : L'.k = 1 := by
      rw [hL]
      show max (max (s'.h + s'.g) s'.h) 1 = 1
      have := hO'.h0
      have := hO'.g0
      omega
    have hhL : L'.h = 0 := by rw [hL]; exact hO'.h0
    have hRd' : fW τC.1 = wordIn s' (lastColW dS τC.1.1) ∧ fG τC.1 = wordMk s' (lastMk dS τC.1.1) :=
      hRd τC.1
    refine ⟨row', L', nx, later, hpass, k3, k4, by rw [hcodes]; exact hN, ⟨?_, ?_, hO'.h0, hO'.g0⟩,
      hdid.noKept hm hkp hr, hkeptL, rfl, hlen', trivial, ?_, hstages⟩
    · rw [← hkL, ← hhL]
      exact hclaim
    · exact fixLaw_of_order _ (did_order hdid hfit.kept hfit.prog.masks hfit.prog.noKept hm hr
        hfit.order) _ (hdid.vars hm hkp hr)
    · show LastTie s' (fW τC.1) (fG τC.1) _
      rw [hRd'.1, hRd'.2]
      exact lastReads s' dS τC.1.1 _ hshown
  | step s' s'' hf' n0' e dE' dT' dS' dC' fW' fZ' fG' εf εc next' =>
    have hO' : StepOwn t1.st.codes s' nx dS := hO
    have hkL : L'.k = s'.h + s'.g := by
      rw [hL]
      show max (max (s'.h + s'.g) s'.h) 1 = s'.h + s'.g
      have := hO'.k1
      omega
    have hhL : L'.h = s'.h := by rw [hL]
    have hRd' : fW τC.1 = wordIn s' (colSt s' dS τC.1.1) ∧ fZ τC.1 = wordFr s' (colSt s' dS τC.1.1)
        :=
      hRd τC.1
    have hne : rest.isEmpty = false := by
      have h1 := (List.cons.inj hstages).2
      rw [← h1]
      cases next' <;> rfl
    rw [hne] at hdid
    have hmk : t3.mask = some (t1.st.oracles.size + 1) := hmask.trans (did_mask hdid rfl)
    obtain ⟨shT, l1, l2, l3, l4, l5⟩ := hO'.one D.lay hdid.trees
    have hseat := hdid.seat shT l1 l3 l4 l5
    rw [l2] at hseat
    refine ⟨row', L', nx, later, hpass, k3, k4, by rw [hcodes]; exact hN, ?_,
      hdid.noKept hm hkp hr, hkeptL, rfl, hlen', hshown.2, ?_, hstages⟩
    · show stmG s' row' = _
      rw [stmG_eq, ← hkL, ← hhL]
      exact hclaim
    · intro id st book hmc
      rcases hmc with ⟨hm1, rfl, rfl⟩ | ⟨hm1, _⟩
      · have hid : id = t1.st.oracles.size + 1 := Option.some.inj (hm1.symm.trans hmk)
        subst hid
        rw [hRd'.1, hRd'.2]
        refine hR p.nums.firstTree s' nx L' t3.st t3.book t1.st.oracles.size _
          (p.nums.firstTree + t1.roots) dS τC.1.1 _ _ hK'.k
          hK'.h hO'.k1 (hdid.layAt hm hkp) ?_ hO'.w ?_
        · have e : (List.range (sentOf (switchTargetStage nx.code nx.maskCode (s'.h + s'.g) s'.h 1)
              (othersOf false nx)).size).map (· + t1.st.oracles.size)
              = [t1.st.oracles.size, t1.st.oracles.size + 1] := by
            show [0 + t1.st.oracles.size, 1 + t1.st.oracles.size] = _
            rw [Nat.zero_add, Nat.add_comm 1]
          rw [e] at hseat
          exact hseat
        · intro c hc
          obtain ⟨grp, hg, hcg⟩ := keyed_mem _ _ _ _ hc
          rw [hK'.k] at hg
          exact hshown.1 grp hg _ hcg
      · rw [hmk] at hm1
        cases hm1

end H2K.Sw
