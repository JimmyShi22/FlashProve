-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/HearOwn.lean: the verifier's routine for all own messages of a layers' sub-proof
(hearOwn, OnBytes/Model/Layer.lean), taken apart into its calls where it succeeds; and what the
merge of the weight claims has heard.

hearOwn makes the embedding's claim and receives its scalar in the first group alone. Here each of
the two is one call (`embClaims`, `embScalar`), and the routine is shown to be the same calls in a
row (`hearOwn_eq`).

Main names:
  `embClaims`, `embScalar`: what only the first group does; else the empty list, the number 0.
  `ownCalls`, `hearOwn_eq`: the routine as calls in a row; it is hearOwn.
  `OwnRan`, `hearOwn_ran`: the successes of the six calls that hear (hearNorms, hearTerms,
    hearStack, hearGated, the embedding's scalar, wsForkEnd), in order, with the states and contexts
    between them, and of what the returned environment O.v is made.
  `MergeSaid`, `merge_heard`: wsForkEnd behind scalars that are still open: two stages, the round
    that batches the claims and the merge's sumcheck; with the sizes of what was heard, the record
    and the state.
  `embScalar_open`: the embedding's scalar is received and nothing is closed.

Limits: those of OnBytes/Tie/Pv/Lay/HearL.lean. What the claims on the weights are is not said here.
-/
import OnBytes.Tie.Pv.Lay.HearL
import OnBytes.Tie.Pv.Lay.MergeTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Model.Layer
open OnBytes.Psc (Weight hearMany hearOne)
open OnBytes.Tie.Pv.Att (PscH claimsIn_said)
open OnBytes.Tie.Pv.Lay.Eng (merge_seam)

/-- The embedding's claim, in the first group alone. -/
def embClaims (b : Bool) (x : Option (List WsClaim)) : SubM (List WsClaim) :=
  if b then form x else pure []

/-- The embedding's scalar, in the first group alone. -/
def embScalar (b : Bool) : SubM Nat := if b then SubM.claimsIn 1 else pure 0

/-- hearOwn as calls in a row. -/
def ownCalls (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) : SubM Own := do
  let y := P.y
  let hasE := g == 0
  let iU3 ← form (hp.tl.ix.U.getD 2 none)
  let H ← hearTerms P (← hearNorms P g fo)
  SubM.must hp.tl.funOpen
  let mats := (P.tails.getD g {}).mats.map fun M => (M.m, M.k)
  let (tab, laid, nU3) ← form (layTables mats (tableAsks y P.rd g) 0)
  mustAs "internal-W-length" (nU3 == hp.nU.getD 2 0)
  let K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0
  let v : Env := { y, sc := P.sc, g, iU3, K3, tab, zk := fo.zk }
  let NCLp := hp.NCL - (if hasE then 1 else 0)
  let K ← hearStack P v H hp.lamS NCLp
  let (hd, hd2) ← hearGated P H K
  let ce : ClaimEnv :=
    { v, wsLay := P.wsLay, rope := P.rope, rs := K.rs, rt := (H.tT.map (·.r)).getD #[] }
  let claimsP ← form (ce.weightClaims (← form (callsTS P)))
  let claimsE ← embClaims hasE ((ce.claimE H.ZE H.tkh P.V P.tokv).map ([·]))
  let claims := (claimsP ++ claimsE).toArray
  mustAs (ofGroup g "internal-claim-count") (claims.size == hp.NCL)
  let sVE ← embScalar hasE
  let sVa := (Array.range NCLp).map (K.sV + ·) ++ (if hasE then #[sVE] else #[])
  let wo ← wsForkEnd P.wsLay claims sVa
  note "the merge's shown value" wo.fvp
  let funs ← form (funsOf y fo (← form (pointsOf y H hd hd2)) laid)
  pure { v, H, K, hd, hd2, sVE, wo, funs }

theorem hearOwn_eq (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) :
    hearOwn P hp g fo = ownCalls P hp g fo := by
  unfold hearOwn ownCalls embClaims embScalar
  by_cases hg : (g == 0) = true <;>
    simp only [hg, if_true, if_false, pure_bind, Bool.false_eq_true]

/-- The slots of the claims' values. -/
def claimSlots (g n sV sVE : Nat) : Array Nat :=
  (Array.range n).map (sV + ·) ++ (if g == 0 then #[sVE] else #[])

/-- The calls of hearOwn that hear, in order. -/
structure OwnRan (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) (O : Own) (F G : Fork)
    (c c' : Ctx) : Prop where
  ran : ∃ (H0 : Heard) (claims : Array WsClaim) (F1 F2 F3 F4 F5 : Fork) (c1 c2 c3 c4 c5 c6 : Ctx),
    hearNorms P g fo F c = .ok ((H0, F1), c1) ∧
    hearTerms P H0 F1 c1 = .ok ((O.H, F2), c2) ∧
    hearStack P O.v O.H hp.lamS (hp.NCL - (if g == 0 then 1 else 0)) F2 c2 = .ok ((O.K, F3), c3) ∧
    hearGated P O.H O.K F3 c3 = .ok (((O.hd, O.hd2), F4), c4) ∧
    claims.size = hp.NCL ∧
    embScalar (g == 0) F4 c4 = .ok ((O.sVE, F5), c5) ∧
    wsForkEnd P.wsLay claims
      (claimSlots g (hp.NCL - (if g == 0 then 1 else 0)) O.K.sV O.sVE) F5 c5 = .ok ((O.wo, G), c6) ∧
    Still c6 c' ∧
    ∃ (iU3 : Nat) (tab : _) (laid : _) (nU3 : Nat), hp.tl.ix.U.getD 2 none = some iU3 ∧
      layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) (tableAsks P.y P.rd g) 0 =
        some (tab, laid, nU3) ∧
      O.v = { y := P.y, sc := P.sc, g := g, iU3 := iU3,
              K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0, tab := tab, zk := fo.zk }

theorem hearOwn_ran (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) (O : Own) (F G : Fork)
    (c c' : Ctx) (h : hearOwn P hp g fo F c = .ok ((O, G), c')) : OwnRan P hp g fo O F G c c' := by
  rw [hearOwn_eq] at h
  simp only [ownCalls] at h
  obtain ⟨iU3, Fa, ca, ha, ka⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨va, ea, ea'⟩ := (getS_ok _ _ _ _ _ _).1 ha
  obtain ⟨H0, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 ka
  obtain ⟨H, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨_, Fb, cb, hb, kb⟩ := (bind_ok _ _ _ _ _).1 k2
  obtain ⟨_, eb, eb'⟩ := (must_ok _ _ _ _ _ _).1 hb
  obtain ⟨⟨tab, laid, nU3⟩, Fd, cd, hd0, kd⟩ := (bind_ok _ _ _ _ _).1 kb
  obtain ⟨vd, ed, ed'⟩ := (getS_ok _ _ _ _ _ _).1 hd0
  obtain ⟨_, Fe, ce0, he, ke⟩ := (bind_ok _ _ _ _ _).1 kd
  obtain ⟨me, ee⟩ := (lift_ok _ _ _ _ _ _).1 he
  obtain ⟨_, ee'⟩ := (mustAs_ok _ _ _ _ _).1 me
  obtain ⟨K, F3, c3, h3, k3⟩ := (bind_ok _ _ _ _ _).1 ke
  obtain ⟨⟨hd, hd2⟩, F4, c4, h4, k4⟩ := (bind_ok _ _ _ _ _).1 k3
  obtain ⟨cts, Ff, cf, hf, kf⟩ := (bind_ok _ _ _ _ _).1 k4
  obtain ⟨_, ef, ef'⟩ := (getS_ok _ _ _ _ _ _).1 hf
  obtain ⟨claimsP, Fg, cg, hg0, kg⟩ := (bind_ok _ _ _ _ _).1 kf
  obtain ⟨_, eg, eg'⟩ := (getS_ok _ _ _ _ _ _).1 hg0
  obtain ⟨claimsE, Fh, ch, hh, kh⟩ := (bind_ok _ _ _ _ _).1 kg
  have eh : Fh = Fg ∧ ch = cg := by
    unfold embClaims at hh
    split at hh
    · obtain ⟨_, x1, x2⟩ := (getS_ok _ _ _ _ _ _).1 hh
      exact ⟨x1, x2⟩
    · obtain ⟨_, x1, x2⟩ := (pure_ok _ _ _ _ _ _).1 hh
      exact ⟨x1, x2⟩
  obtain ⟨_, Fi, ci, hi, ki⟩ := (bind_ok _ _ _ _ _).1 kh
  obtain ⟨mi, ei⟩ := (lift_ok _ _ _ _ _ _).1 hi
  obtain ⟨si, ei'⟩ := (mustAs_ok _ _ _ _ _).1 mi
  obtain ⟨sVE, F5, c5, h5, k5⟩ := (bind_ok _ _ _ _ _).1 ki
  obtain ⟨wo, F6, c6, h6, k6⟩ := (bind_ok _ _ _ _ _).1 k5
  obtain ⟨_, Fj, cj, hj, kj⟩ := (bind_ok _ _ _ _ _).1 k6
  obtain ⟨ej, sj⟩ := note_still _ _ _ _ _ _ _ hj
  obtain ⟨pts, Fk, ck, hk, kk⟩ := (bind_ok _ _ _ _ _).1 kj
  obtain ⟨_, ek, ek'⟩ := (getS_ok _ _ _ _ _ _).1 hk
  obtain ⟨funs, Fl, cl, hl, kl⟩ := (bind_ok _ _ _ _ _).1 kk
  obtain ⟨_, el, el'⟩ := (getS_ok _ _ _ _ _ _).1 hl
  obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 kl
  rw [ea, ea'] at h1
  rw [ee, ed, eb, ee', ed', eb'] at h3
  rw [ei, eh.1, eg, ef, ei', eh.2, eg', ef'] at h5
  have hG : G = F6 := by rw [e2, el, ek, ej]
  have hS : Still c6 c' := by
    rw [e3, el', ek']
    exact sj
  rw [e1, hG]
  exact ⟨H0, _, F1, F2, F3, F4, F5, c1, c2, c3, c4, c5, c6, h1, h2, h3, h4, by simpa using si, h5,
    h6, hS, iU3, tab, laid, nU3, va, vd, rfl⟩

/-- The embedding's scalar is received and nothing is closed. -/
theorem embScalar_open (b : Bool) (F G : Fork) (c c' : Ctx) (j : Nat)
    (h : embScalar b F c = .ok ((j, G), c')) (hz : Sized F) :
    ∃ v : List E, (Blk.recvEs v.length).Yields c v c' ∧ v.length = (if b then 1 else 0) ∧
      Sized G ∧ (b = true → j = F.next ∧ Filled (taken F 1) G F.next v oneE) ∧
      (b = false → G = F) := by
  unfold embScalar at h
  cases b with
  | true =>
    simp only [if_true] at h
    obtain ⟨v, a1, a2, a3, a4, a5⟩ := claimsIn_said 1 F G c c' j h hz
    refine ⟨v, ?_, a2, a5, fun _ => ⟨a3, a4⟩, fun x => by simp at x⟩
    rw [a2]
    exact a1
  | false =>
    simp only [if_false, Bool.false_eq_true] at h
    obtain ⟨_, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 h
    rw [e2, e3]
    exact ⟨[], recvEs_zero c, rfl, hz, fun x => by simp at x, fun _ => rfl⟩

/-- What the merge has said. -/
structure MergeSaid (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) (F G : Fork)
    (wo : WsForkOut) (x : E) (H : PscH) : Prop where
  count : cl.isEmpty = false ∧ cl.size ≤ 4096 ∧ sv.size = cl.size
  rounds : H.rs.map (·.1.length) = List.replicate lay.lk 2
  sentY : H.sentY.length = 1
  vals : H.v = [wo.fvp]
  eps : H.eps = wo.p.eps
  /-- the challenges -/
  rm : wo.rm.toList = H.rs.map (·.2)
  sFv : wo.sFv = F.next + (1 + 2 * lay.lk) + 1
  /-- the sumcheck's record, with the public part of the start form -/
  psc : ∃ τ : E, F.publicPart (wsForkStart sv (powers x sv.size)) = some τ ∧
    Ended wo.p (wsForkStart sv (powers x sv.size)) τ H.mu H.eps F.next
      (List.replicate lay.lk (Weight.plain 3)) H.rs 1 H.sentY H.beta
  /-- the end value stands under its slot, with the factor beta -/
  ends : Filled (taken F (1 + 2 * lay.lk + (1 + 1))) G wo.sFv H.v H.beta
  /-- what is left of each claim -/
  recs : wo.recs = (cl.zip (powers x sv.size)).toList.map fun y =>
    wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 wo.rm))

/-- The merge, behind scalars that are still open. -/
theorem merge_heard (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) (F G : Fork) (c c' : Ctx)
    (wo : WsForkOut) (h : wsForkEnd lay cl sv F c = .ok ((wo, G), c')) (hz : Sized F)
    (pre : List E) (c0 : Ctx) (h0 : (Blk.recvEs pre.length).Yields c0 pre c) :
    ∃ (x : E) (H : PscH),
      HeardL [.bat pre sv.size x, .sum [] (List.replicate lay.lk (Weight.plain 3)) 1 H] c0 c' ∧
      MergeSaid lay cl sv F G wo x H := by
  simp only [wsForkEnd] at h
  obtain ⟨_, Fa, ca, ha, ka⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨ma, ea⟩ := (lift_ok _ _ _ _ _ _).1 ha
  obtain ⟨sa, ea'⟩ := (mustAs_ok _ _ _ _ _).1 ma
  obtain ⟨_, Fb, cb, hb, kb⟩ := (bind_ok _ _ _ _ _).1 ka
  obtain ⟨mb, eb⟩ := (lift_ok _ _ _ _ _ _).1 hb
  obtain ⟨_, eb'⟩ := (mustAs_ok _ _ _ _ _).1 mb
  obtain ⟨_, Fd, cd, hd, kd⟩ := (bind_ok _ _ _ _ _).1 kb
  obtain ⟨md, ed⟩ := (lift_ok _ _ _ _ _ _).1 hd
  obtain ⟨_, ed'⟩ := (mustAs_ok _ _ _ _ _).1 md
  obtain ⟨⟨o, rho⟩, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 kd
  obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 k1
  rw [ed, eb, ea, ed', eb', ea'] at h1
  obtain ⟨cm, τ, mu, rs, sentY, beta, fv, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ :=
    merge_seam lay.lk sv o rho F F1 c c1 h1 hz
  obtain ⟨_, x, p1, r1⟩ := batch_heardL _ _ _ _ _ _ a1 pre c0 h0
  rw [r1] at a2 a4
  refine ⟨x, ⟨mu, o.p.eps, rs, sentY, beta, [fv]⟩, ?_, ?_⟩
  · rw [e3]
    exact HeardL.append [_] [_] c0 cm c1 p1 ⟨cm, c1, a3, rfl⟩
  · rw [e1, e2]
    refine ⟨by simpa [and_assoc] using sa, a6, a7, by rw [← a8], rfl, a5, a9, ⟨τ, a2, a4⟩, a10,
      by rw [r1]⟩

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.hearOwn_eq
#print axioms OnBytes.Tie.Pv.Lay.hearOwn_ran
#print axioms OnBytes.Tie.Pv.Lay.embScalar_open
#print axioms OnBytes.Tie.Pv.Lay.merge_heard
