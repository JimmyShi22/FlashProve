-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TopF.lean: the law of the proximity test with the reading of the view reduced
to two plain sentences.

The two sentences are: the rounds shown behind "BAT" are the chain's written rounds; and every dealt
column is the written tree's, opening by opening (`Follows`, Johnson/Desc/K12/Law/Written.lean).
Statements and proofs.
Main names:
  `firstDraws_lt`: what the written round "CS" of the first switch drew lies in the stage's range,
    from `Chain.Pub`.
  `cut_rounds`: where the rounds shown behind "BAT" are the chain's written rounds, the first
    switch's two rounds are there, and the second drew `firstDraws`.
  `bat_front`: what the batching returns beside the row hangs on the record in front alone.
  `readsK_written`: `ReadsK` from the two sentences, the two tests on form of `Block.step`, the
    block's test on the plan, `cutOk` and the clauses of `gpOk` at the plain data D. The written
    rounds and oracles of the group's trees go by the book's place (`dT t`, `oT t`), so that two
    tenants of one tree have one oracle.
  `k12_step_accF`: the block's test on the plan, `pubOk` and `cutOk` give the chain c such that a
    yes of `Block.step` gives the batching's return (row, L, S'), and, if `gpOk` says yes at the
    record behind it, the plain data D, the value of `gpOf` at that record, such that for all dT and
    oT as deep as the book's trees, all b and gW: the two sentences give `c.Acc` at the row read in
    the field and at the words read off oT.
Limits: The law of the proximity test is not proved for a view that comes from bytes: the two
sentences are premises. It does not say that the two sentences and the step's yes hold together on
any view. It is stated of `guardedProximityTestParts` (Johnson/Desc/K12/JoinGuarded.lean): the parts of
Johnson/Desc/K12/Join.lean behind guards, with the base case deciding by
Johnson/Desc/Prox/BaseCase.lean. It is not stated of `proximityTestParts`, the parts of Join.lean themselves.
The written oracles oT are not for whoever proves the two sentences to choose: they are the oracles
that the rounds `dT t` wrote; at the unopened positions nothing here ties them to the view. That D,
the layout and the word hang on no round of the test is proved in
Johnson/Desc/K12/Law/GpOfPass.lean. `bat_front` takes the layout from `layout_of_group`
(Johnson/Desc/Own/LayoutAgree.lean); its statement still speaks of `Statement.layout`. No statement
and no proof of this file reaches a routine that runs in a context of the program `verify-on-bytes`
(`OnBytes.Ctx`, `OnBytes.Blk`, `OnBytes.Chan`); plain functions of that program, some with
names that begin with `Blk.`, are reached. No soundness is claimed. Nothing here is about hiding.

-/
import Johnson.Desc.K12.Law.TopE
import Johnson.Desc.K12.Law.Written
import Johnson.Desc.K12.Law.FirstCutLaw
import Johnson.Desc.Own.LayoutAgree

set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.FoldLaw (bind_ok got_ok)
open H2K.Pub (Letters pubOk pub_of_ok sgOf writtenOf WR)
open H2K.First (gpOk gpOf gpL gpG gpP Good Plain good_of_ok gpOk_inv first_at cutOk first_half_paid
  logAt sg_k)
open H2K.Sw (groupsAre_of)

theorem firstDraws_lt {s : Sg} (c : Chain s) (b : c.Bl) (K : Codes) (cu : IoppStage)
    (restI : List IoppStage) (h : c.Pub K cu restI) : ∀ x ∈ firstDraws c b, x < 2 ^ s.C.a := by
  cases c with
  | last s e dL dB fu fs εb => intro x hx; cases hx
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next =>
    obtain ⟨nx, later, _, hP, _⟩ := h
    exact hP.rounds.cs.poss_lt _ _

theorem map_two {α β : Type} (f : α → β) (l : List α) (u v : β) (h : l.map f = [u, v]) :
    ∃ x y, l = [x, y] ∧ f x = u ∧ f y = v := by
  match l, h with
  | [x, y], h =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    exact ⟨x, y, rfl, h.1, h.2⟩

theorem cut_rounds {s : Sg} (c : Chain s) (b : c.Bl) (hc : c.len ≠ 0) (rs : List Fmt.RoundView)
    (h : (rs.map noDigest).drop 1 = (c.rvs b).map noDigest) :
    ∃ rS rC, (rs.drop (1 + (1 + (s.h + s.g)))).take 2 = [rS, rC] ∧
      rC.drawn.poss = firstDraws c b := by
  cases c with
  | last s e dL dB fu fs εb => exact absurd rfl hc
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next =>
    have lA : ((PQ.rvSL (ckP .two) (foldRds s dE dT) b.1).map noDigest).length
        = 1 + (s.h + s.g) := by
      rw [List.length_map, rvSL_length]
      simp [foldRds]
      omega
    have lB : ((PQ.rvSL (ckP .two) [dS, dC] b.2.1).map noDigest).length = 2 := by
      rw [List.length_map, rvSL_length]
      rfl
    have h1 : (rs.map noDigest).drop 1 = (PQ.rvSL (ckP .two) (foldRds s dE dT) b.1).map noDigest ++
        ((PQ.rvSL (ckP .two) [dS, dC] b.2.1).map noDigest ++ (next.rvs b.2.2).map noDigest) := by
      rw [h]
      show List.map noDigest (_ ++ (_ ++ _)) = _
      rw [List.map_append, List.map_append]
    have h2 : (((rs.drop (1 + (1 + (s.h + s.g)))).take 2).map noDigest) =
        (PQ.rvSL (ckP .two) [dS, dC] b.2.1).map noDigest := by
      rw [List.map_take, List.map_drop, ← List.drop_drop, h1, ← lA, List.drop_left, ← lB,
        List.take_left]
    obtain ⟨rS, rC, e1, _, e3⟩ := map_two noDigest _ _ _ h2
    refine ⟨rS, rC, e1, ?_⟩
    exact congrArg (·.drawn.poss) e3

/-- Where the place's numbers give rounds, the chain begins with a step. -/
theorem len_ne (p : P12) {s : Sg} (c : Chain s) (ds : List Fmt.DeclaredRound)
    (hs : stagesOf c = p.nums.stages) (hd : H2U.roundsOfNums p.nums = some ds) : c.len ≠ 0 := by
  cases c with
  | last s e' dL dB fu fs εb =>
    exfalso
    have h1 : p.nums.stages = [s.st] := hs.symm
    unfold H2U.roundsOfNums at hd
    rw [h1] at hd
    cases hd
  | step s s' hf n0 e' dE dT dS dC fW fZ fG εf εc next => exact Nat.succ_ne_zero _

/-- What the batching returns beside the row hangs on the record in front alone. -/
theorem bat_front (S S' : Statement) (g : Nat) (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow)
    (L : GroupLayout) (h : First.Close.bat S g e r = .ok (row, L, S')) :
    ∃ G0, S.groups[g]? = some G0 ∧ S.layout g = some L ∧ S' = begun S g G0 := by
  unfold First.Close.bat at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨input, d⟩, hb, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases h
  have hb' := got_ok hb
  unfold Ground.beginRunP at hb'
  split at hb'
  · cases hG : (First.Close.onSt S).st.groups[g]? with
    | none => simp [hG] at hb'
    | some G =>
      simp [hG] at hb'
      obtain ⟨e1, e2⟩ := hb'
      subst e1
      subst e2
      exact ⟨G, hG, Own.layout_of_group hG, rfl⟩
  · cases hb'

/-- `ReadsK` from the two sentences. -/
theorem readsK_written (p : P12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (c : Chain (sgOf a)) (b : c.Bl) (hc : c.len ≠ 0) (K : Codes) (cu : IoppStage)
    (restI : List IoppStage) (hpub : c.Pub K cu restI)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hs : p.nums.stages = a :: rest)
    (hhk : a.h ≤ a.k) (hcut : cutOk p = true) (t : T12) (row : GroupRow) (L : GroupLayout)
    (D : Plain) (hD : gpOf p t a L = some D) (hok : H2K.First.ok (gpL p a row D) = true)
    (rad : ℕ → ℕ) (dT : ℕ → PQ.RD) (oT : ∀ z, (wRound (dT z)).Orc) (F : ℕ) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (hfit : roundsFit (proximityTestKind guardedProximityTestParts p : Blk').rounds rs = true)
    (hcols : ((cols.take ((groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds
        (rs.map (·.drawn))).flatMap id).length).map (fun c => (c.1, c.2.1, c.2.2.length)) ==
      (groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds (rs.map (·.drawn))).flatMap id) = true)
    (hr : (rs.map noDigest).drop 1 = (c.rvs b).map noDigest)
    (hf : Follows (grpsS p (regroup ((groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds
          (rs.map (·.drawn))).map (·.length))
        (cols.take ((groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds
          (rs.map (·.drawn))).flatMap id).length)))
      (srcFirst c b (laidS p) D.ts fun z x => colW (dT z) (oT z) x)) :
    ReadsK p c b
      (gpP (good_of_ok p a row D hok) rad (fun i => dT (D.mems.get i).t) (dT D.fresh.t))
      (fun j => oT (D.mems.get j).t) (oT D.fresh.t) (fun z x => some (colW (dT z) (oT z) x))
      (rs.map noDigest)
      (regroup ((groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds (rs.map (·.drawn))).map (·.length))
        (cols.take ((groupsOf F (proximityTestKind guardedProximityTestParts p : Blk').rounds
          (rs.map (·.drawn))).flatMap id).length)) := by
  have hk : (sgOf a).h + (sgOf a).g = a.k := sg_k a hhk
  obtain ⟨rS, rC, hcr, hposs⟩ := cut_rounds c b hc rs hr
  rw [hk] at hcr
  have hrange : ∀ x ∈ rC.drawn.poss, x < 2 ^ a.C.a := by
    rw [hposs]
    exact firstDraws_lt c b K cu restI hpub
  have h1 := first_half_paid guardedProximityTestParts p hp F rs cols hfit hcols t a rest row L D hs hD hok hcut rS
      rC
    hcr hrange
  rw [hposs] at h1
  have h2 := second_half c b (laidS p) D.ts (fun z x => colW (dT z) (oT z) x) _ hf hc
    (by rw [hk]; exact h1.length_eq)
  rw [hk] at h2
  refine ⟨hr, shownLater_of_follows c b _ _ _ _ hf, fun _ _ => rfl, fun _ => rfl, ?_⟩
  rw [hk]
  exact groupsAre_of _ _ _ _ _ h1 h2

/-- The law of the proximity test, of `Block.step`: four Booleans, two numbers, and the two
sentences on the view. -/
theorem k12_step_accF (X : Letters) (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 : T12)
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (hpub : pubOk p t0.st.codes = true)
    (hcut : cutOk p = true) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
      H2K.Pub.chainFrom X rest a l = some c ∧ c.rds = l.map WR.rd ∧
      stagesOf c = p.nums.stages ∧
      ∀ (firstTree : Nat) (tE : T12) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (n : Nat),
        (proximityTestKind guardedProximityTestParts p : Blk').step firstTree t0 rs cols = .ok (tE, n) →
        ∃ (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout) (S' : Statement)
          (G0 : Group),
          (rs.map noDigest).take 1 = [r] ∧ First.Close.bat t0.st t0.g e r = .ok (row, L, S') ∧
          t0.st.groups[t0.g]? = some G0 ∧ t0.st.layout t0.g = some L ∧
          S' = begun t0.st t0.g G0 ∧
          (gpOk p { t0 with st := S', pass := .claim row L } = true →
            ∃ (D : Plain) (hok : H2K.First.ok (gpL p a row D) = true),
              gpOf p { t0 with st := S', pass := .claim row L } a L = some D ∧
              ∀ (rad : ℕ → ℕ) (dT : ℕ → PQ.RD) (oT : ∀ z, (wRound (dT z)).Orc),
                (∀ i, PQ.posN (dT (D.mems.get i).t).tree = 2 ^ (D.mems.get i).tsh.logN) →
                PQ.posN (dT D.fresh.t).tree = 2 ^ D.fresh.tsh.logN →
                ∀ (gW : (sgOf a).cIn.Word) (b : c.Bl),
                  (rs.map noDigest).drop 1 = (c.rvs b).map noDigest →
                  Follows (grpsS p (regroup ((groupsOf firstTree (proximityTestKind guardedProximityTestParts p : Blk').rounds
                        (rs.map (·.drawn))).map (·.length))
                      (cols.take ((groupsOf firstTree (proximityTestKind guardedProximityTestParts p : Blk').rounds
                        (rs.map (·.drawn))).flatMap id).length)))
                    (srcFirst c b (laidS p) D.ts fun z x => colW (dT z) (oT z) x) →
                  c.Acc (stmG (sgOf a) row)
                    ((gpG (good_of_ok p a row D hok) rad).word fun j =>
                      ((gpG (good_of_ok p a row D hok) rad).mb j).ofOrc
                        ((gpP (good_of_ok p a row D hok) rad (fun i => dT (D.mems.get i).t)
                          (dT D.fresh.t)).lay j) (dT (D.mems.get j).t) (oT (D.mems.get j).t))
                    (frOf (sgOf a) D.fresh.tsh.logN
                      (gpP (good_of_ok p a row D hok) rad (fun i => dT (D.mems.get i).t)
                        (dT D.fresh.t)).oF (dT D.fresh.t) (oT D.fresh.t))
                    gW b) := by
  obtain ⟨a, rest, w0, l, c, hs, hw, hcf, hrds, hst, hpb⟩ := pub_of_ok X p t0.st.codes hpub
  refine ⟨a, rest, w0, l, c, hs, hw, hcf, hrds, hst, ?_⟩
  intro firstTree tE rs cols n h
  obtain ⟨hfit, hcols, hdec⟩ := Prox.step_ok firstTree _ t0 tE rs cols n h
  obtain ⟨ds, e, r, row, L, S', hd, hr, hb⟩ := k12_bat p he t0 tE _ _ hp hdec
  obtain ⟨G0, g1, g2, g3⟩ := bat_front _ _ _ _ _ _ _ hb
  refine ⟨e, r, row, L, S', G0, hr, hb, g1, g2, g3, ?_⟩
  intro hgp
  have hhk : a.h ≤ a.k := by
    obtain ⟨l', hl'⟩ := stagesOf_ne c
    have h1 : (sgOf a).st = a := (List.cons.inj ((hl'.symm.trans hst).trans hs)).1
    have h2 : a.h + (a.k - a.h) = a.k := congrArg (·.k) h1
    omega
  obtain ⟨D, hD, hok⟩ := gpOk_inv p { t0 with st := S', pass := .claim row L } a rest row L hs rfl
      hgp
  refine ⟨D, hok, hD, ?_⟩
  intro rad dT oT hM hF gW b hrounds hfol
  -- the place's stages in the program's form
  have hidx := idx_len p hp
  rw [hs] at hidx
  obtain ⟨all, hall⟩ := stagesAt_some p (a :: rest) 0 (by rw [hidx]; simp)
  obtain ⟨cu, restI, hcu, hri⟩ : ∃ cu restI, stageAt p 0 a = some cu ∧
      stagesAt p 1 rest = some restI := by
    unfold stagesAt at hall
    cases hcu : stageAt p 0 a with
    | none => rw [hcu] at hall; cases hall
    | some cu =>
      rw [hcu] at hall
      cases hri : stagesAt p (0 + 1) rest with
      | none => simp [hri] at hall
      | some restI => exact ⟨cu, restI, rfl, rfl⟩
  have hPub := hpb a rest cu restI hs hcu hri
  have hlen : c.len ≠ 0 := len_ne p c ds hst hd
  have hreads := readsK_written p a rest c b hlen t0.st.codes cu restI hPub hp hs hhk hcut _ row L
      D hD
    hok rad dT oT firstTree rs cols hfit hcols hrounds hfol
  obtain ⟨p1, ⟨src, p2⟩, _, p4, p5⟩ := first_at p _ a row L D hD hok hhk rad
    (fun i => dT (D.mems.get i).t) (dT D.fresh.t) hM hF
  exact k12_step_accG p he ha c (stmG (sgOf a) row) gW b _ _ _ _ firstTree t0 tE rs cols n hp
    ⟨hst, hpb, p1, p2.keys, hreads, by
      intro e' r' row' L' S'' hr' hb'
      have hrr : r' = r := by
        rw [hr] at hr'
        exact (List.cons.inj hr').1.symm
      subst hrr
      cases bat_unique _ _ _ _ _ _ _ hb hb'
      refine ⟨claimNow_step p c row ds hst hd, p4, ?_⟩
      intro first rest' cu' id st book hs' hcu' hmc
      have hfa : first = a := (List.cons.inj (hs'.symm.trans hs)).1
      subst hfa
      exact p5 cu' id st book hcu' hmc⟩ h

end H2K.JointK
