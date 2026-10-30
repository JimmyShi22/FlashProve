-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/RowAtSeat.lean: the row claim_read_same_index at the output head's link, for the
four forms of the policy, at the blocks that the seated description holds at the fourth and the
fifth place of that link.

Why. Reads/RowBehind.lean speaks of the kind's bare block, and asks the run "policy" at the state
right behind the fifth place. The seated description holds the block with the seat's tests and with
a fourth run; and it runs the claims later: a link lets all its blocks in front of the batching
decide first, and runs their claims inside the batching's block (`Link.blocksInOrder`,
Johnson/Desc/Block.lean).

What is stated and shown.
  `fillOf W iU3 cols`: the filling of Reads/HeadAtRecord.lean from the public values that the
    program makes of the public files. All but the number of columns is a term of W.
  `seated_yes`: a yes of the block that is seated at the fourth place (`Head.seatedClaims`,
    Johnson/Stored/HeadAddsAtS.lean) is a yes of the kind's own decision, at the filling's numbers.
  `seated_policy`: a run of that block under the name "policy" is a run of the kind's bare block.
  `piece5_is`: two blocks laid one behind the other under the first one's name are
    `K8.ReadsQuiet.behind`: the shape in which Johnson/Desc/ProofFile/Lot/K1.lean lays the quiet
    step behind the reads' commitment.
  `KeptAll iU3 s s'`: where s stands in the head's link, so does s', with the same mark "opened",
    the same fields for what was heard, for what the lookup heard and for the tables, the same
    matrices, list of tables and number of matrices in the smallness test's part of the state, and
    as many columns in array iU3 of the ledger; and the two states have the same words and the same
    reply.
  `covered_congr`: a tool: the covered positions read the words and the reply alone.
  `core_kept`: `Core` (Reads/LiesBehind.lean) passes along `KeptAll`. Every field of `KeptAll` is
    spent in its proof, each once: none is spare for this lemma.
  `row_at_seat`: **under `Public (fillOf W iU3 cols)`: behind a yes of the seated block of the
    fourth place, a yes of the seated block of the fifth place, `KeptAll` from the state that this
    leaves to a state s, and a yes at s of the seated block's run "policy": `HeadClaimW` holds of
    the letters filled from W; s is one of the states of which it speaks; and the claims that the
    run returns are the letters' four forms at s.**

Premises of `row_at_seat` that speak of a state, by name, shown by nothing here: `KeptAll`; the
ledger in front of the head's own rounds is well laid; the reads' array has the public number of
columns; the lookup's two points on the planes have all their coordinates.

Who owes `KeptAll`. By the driver's list of kinds and its order of the claims
(Johnson/Desc/First/Driver/Chain.lean: `kindsBeforeBatching`, `orderCuts`), between the fifth place and the
run "policy" stand four decisions and four runs:
  the smallness test's rounds (K8): the nearest law is `hear_leaves_list`
    (Johnson/Desc/First/K8/LawFunsStay.lean): that block leaves the list of tables and its mark;
  the digits' commitment (K1): `kept_commit` (Reads/LiesBehind.lean) has the fields for what was
    heard and for what the lookup heard; the ledger is written whole there, so its array's columns
    want a law of that block;
  the lookup on the digits (K3); the merge (K11): no law was looked for;
  the runs "objects" and "guests" of the lookup on the calls (K3); the kind's own run "norm", which
    lays the key vectors: the seat returns the state as it stands (`claims_lay_nothing`); the run
    "join" (K3).

Limits. That the seated description holds just these two blocks at these places is read in
Johnson/Desc/ProofFile/Lot/K6K7.lean and Lot/K1.lean and is not shown. `Public` holds hJ, which is
shown here of no real layout: a law for it, at the public values that the program makes in the
goals' scope, is stated as `cols_in_scope` in Johnson/Goal/Meaning/HeadColsScope.lean, which this
file does not import. No states are shown at which the premises hold together. Four forms of 35. The
full size alone. Nothing on soundness.


-/
import Johnson.Desc.Reads.RowBehind
import Johnson.Stored.HeadAddsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtSeat

open OnBytes.Model.Head (Covered Tables)
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K8 (ReadsQuiet.head)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Reads.AtHead

/-- The bits of work that the seated block is handed. -/
def workOf (W : OnBytes.Model.Verify.Public) : ℕ :=
  (OnBytes.Params.settingOf W.P.frame).workOf .field .request

/-- The filling, from the public values. -/
def fillOf (W : OnBytes.Model.Verify.Public) (iU3 cols : ℕ) : Fill :=
  { h := W.hS, L := W.HLy, b := OnBytes.Model.Verify.borderOf W.y, hp := W.H, iU3 := iU3
    work := workOf W, cols := cols, tab := planTab W.hS W.H.tl.mats }

/-- **A yes of the seated block is a yes of the kind's own decision.** -/
theorem seated_yes {W : OnBytes.Model.Verify.Public} {l : ℕ} {before : List (ℕ × ℕ)}
    {B : Block S Claim} (hB : seatedClaims W l before = some B) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (h : B.decide s rs gs = .ok s') :
    ∃ iU3, W.H.tl.ix.U.getD 2 none = some iU3 ∧
      (kind asClaim (seatAt W.hS iU3) l 4 (parOf W.hS (workOf W))).decide s rs gs = .ok s' := by
  unfold seatedClaims blockClaims at hB
  cases hi : W.H.tl.ix.U.getD 2 none with
  | none =>
    rw [hi] at hB
    cases hB
  | some iU3 =>
    rw [hi] at hB
    have e := (Option.some.inj hB).symm
    subst e
    refine ⟨iU3, rfl, ?_⟩
    have h' : (if startOk W s then
        (kind asClaim (seatAt W.hS iU3) l 4 (parOf W.hS (workOf W))).decide s rs gs
      else .error "the request: rows and tokens") = .ok s' := h
    split at h'
    · exact h'
    · cases h'

/-- **The seated block's run "policy" is the kind's.** -/
theorem seated_policy {W : OnBytes.Model.Verify.Public} {l : ℕ} {before : List (ℕ × ℕ)}
    {B : Block S Claim} (hB : seatedClaims W l before = some B) {iU3 : ℕ}
    (hi : W.H.tl.ix.U.getD 2 none = some iU3)
    {c : String × (ℕ → S → Except String (List Claim × S))} (hc : c ∈ B.claims)
    (hname : c.1 = "policy") :
    c ∈ (kind asClaim (seatAt W.hS iU3) l 4 (parOf W.hS (workOf W))).claims := by
  unfold seatedClaims blockClaims at hB
  rw [hi] at hB
  have e := (Option.some.inj hB).symm
  subst e
  have hc' : c ∈ (kind asClaim (seatAt W.hS iU3) l 4 (parOf W.hS (workOf W))).claims.take 1 ++
      [("join", _)] ++
      (kind asClaim (seatAt W.hS iU3) l 4 (parOf W.hS (workOf W))).claims.drop 1 := hc
  rcases List.mem_append.1 hc' with h1 | h1
  · rcases List.mem_append.1 h1 with h2 | h2
    · exact List.mem_of_mem_take h2
    · rw [List.mem_singleton.1 h2] at hname
      have hn : ("join" : String) = "policy" := hname
      exact absurd hn (by decide)
  · exact List.mem_of_mem_drop h1

/-- Two blocks laid one behind the other under the first one's name. -/
theorem piece5_is (k z : Block S Unit) :
    k.andThen k.name z = VerifiableInference.Desc.K8.ReadsQuiet.behind k z := rfl

/-- What must stand between the state behind the fifth place and the state of a run of claims. -/
structure KeptAll (iU3 : ℕ) (s s' : S) : Prop where
  req : s'.req = s.req
  reply : s'.out.reply = s.out.reply
  own : ∀ o, s.here = .head o → ∃ o', s'.here = .head o' ∧ o'.opened = o.opened ∧ o'.x = o.x ∧
    o'.lookHeard = o.lookHeard ∧ o'.t = o.t ∧ o'.tl.mats = o.tl.mats ∧ o'.tl.funs = o.tl.funs ∧
    o'.tl.NM = o.tl.NM ∧ (o'.F.trees[iU3]?).map (·.K) = (o.F.trees[iU3]?).map (·.K)

/-- The covered positions read the words and the reply alone. -/
theorem covered_congr {s s' : S} (h1 : s'.req = s.req) (h2 : s'.out.reply = s.out.reply)
    (T V : ℕ) : s'.covered T V = s.covered T V := by
  unfold S.covered S.replyTok? S.coveredAt
  rw [h1, h2]

/-- **Core passes along KeptAll.** Every field of KeptAll is spent here, each once. -/
theorem core_kept (Z : Fill) {s s' : S} (k : KeptAll Z.iU3 s s') {o : HeadOwn} {cov : Covered}
    {x : OnBytes.Model.Head.Heard} {t : Tables} (Q : Core Z s o cov x t) :
    ∃ o', Core Z s' o' cov x t := by
  obtain ⟨o', h', a1, a2, a3, a4, a5, a6, a7, a8⟩ := k.own o Q.here
  obtain ⟨tr, htr, hK⟩ := Q.cols
  have hc : ∃ tr', o'.F.trees[Z.iU3]? = some tr' ∧ tr'.K = Z.cols := by
    rw [htr] at a8
    cases ht : o'.F.trees[Z.iU3]? with
    | none =>
      rw [ht] at a8
      cases a8
    | some tr' =>
      rw [ht] at a8
      exact ⟨tr', rfl, (Option.some.inj a8).trans hK⟩
  exact ⟨o',
    { here := h', opened := a1.trans Q.opened
      covered := (covered_congr k.req k.reply _ _).trans Q.covered, heard := a2.trans Q.heard
      made := Q.made, laid := a4.trans Q.laid, cols := hc, mats := a5.trans Q.mats
      funs := a6.trans Q.funs, nm := a7.trans Q.nm, tab := Q.tab, hX1 := a3.trans Q.hX1
      hX2 := Q.hX2, hqH := Q.hqH, hqN := Q.hqN, hsPV := Q.hsPV, hsSq := Q.hsSq, hsTV := Q.hsTV
      hsTH := Q.hsTH, hzb0 := Q.hzb0, hzb1 := Q.hzb1 }⟩

/-- **The row at the head, at the seated blocks.** -/
theorem row_at_seat (W : OnBytes.Model.Verify.Public) (l iU3 cols : ℕ)
    (hi : W.H.tl.ix.U.getD 2 none = some iU3) (U : Public (fillOf W iU3 cols))
    {before : List (ℕ × ℕ)} {B4 : Block S Claim} (hB4 : seatedClaims W l before = some B4)
    {s0 s2 s4 s : S} {rs4 : List Fmt.RoundView} {gs4 : List (List (ℕ × List UInt64))}
    (h4 : B4.decide s0 rs4 gs4 = .ok s2)
    (P : VerifiableInference.Desc.K1.Par) (link moment : ℕ) (arrays : Option (List ℕ))
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h5 : ((VerifiableInference.Desc.K1.commitAtS P link moment arrays).andThen
      (VerifiableInference.Desc.K1.commitAtS (Cl := Unit) P link moment arrays).name
      (ReadsQuiet.head ⟨⟨1, some l, 5, .K1⟩, W.hS, W.HLy, W.H⟩)).decide s2 rs gs = .ok s4)
    (k : KeptAll iU3 s4 s)
    {c : String × (ℕ → S → Except String (List Claim × S))} (hc : c ∈ B4.claims)
    (hname : c.1 = "policy") {n : ℕ} {y : List Claim × S} (hrun : c.2 n s = .ok y)
    (hWL : WellLaid ((seatAt W.hS iU3).ledger s0))
    (hcols : ∀ o, s4.here = .head o → ∃ tr, o.F.trees[iU3]? = some tr ∧ tr.K = cols)
    (hzb : ∀ o x, s2.here = .head o → o.x = some x →
      x.g1.zb0.size = x.g1.shape.kT + x.g1.shape.cK + 5 ∧
      x.g1.zb1.size = x.g1.shape.kT + x.g1.shape.cK + 5) :
    HeadClaimW (fillOf W iU3 cols).letters ∧ (fillOf W iU3 cols).AtClose s ∧
      y.1 = ((fillOf W iU3 cols).letters.letters.forms () s).map asClaim := by
  obtain ⟨i', hi', h4k⟩ := seated_yes hB4 h4
  have ei : i' = iU3 := by
    rw [hi] at hi'
    exact (Option.some.inj hi').symm
  subst ei
  have hck := seated_policy hB4 hi hc hname
  have h4' : decideBy (fun _ => rounds) (fun _ => Head.hear) (fun _ _ => forTheMerge)
      (parOf W.hS (workOf W)) (seatAt W.hS i') s0 rs4 = .ok s2 := h4k
  obtain ⟨o, cov, x, t, Q⟩ := core_of_kind (fillOf W i' cols) U.tab ⟨1, some l, 5, .K1⟩ h4' hWL
    (U.hJ 0 (by decide)) (U.hlsJ 0 (by decide)) P link moment arrays h5 hcols hzb
  obtain ⟨o', Q'⟩ := core_kept (fillOf W i' cols) k Q
  have hck' : c ∈ runsBy ["norm", "policy", "logits"] (fun _ _ _ => claims)
      (fun g _ _ => g.calls.map fun c => keyVector key c.1 c.2) asClaim (parOf W.hS (workOf W))
      (seatAt W.hS i') := hck
  obtain ⟨g, bh, pl, fs, hl, -, -⟩ := letters_of_run hck' hrun
  have L := Q'.lies (g := g) (bh := bh) (pl := pl) hl
  have hs : (fillOf W i' cols).AtClose s := ⟨o', cov, x, t, g, bh, pl, L⟩
  exact ⟨head_at _ (sane_of_close _ U.first U.num hs) U.mats U.nm U.la U.hJ U.hlsJ U.hc6 U.hls
    U.cols U.T U.S2 U.d U.JV U.count, hs, policy_claims asClaim (fillOf W i' cols) l 4 L hck hname
    hrun⟩

end VerifiableInference.Reads.AtSeat

#print axioms VerifiableInference.Reads.AtSeat.seated_yes
#print axioms VerifiableInference.Reads.AtSeat.seated_policy
#print axioms VerifiableInference.Reads.AtSeat.piece5_is
#print axioms VerifiableInference.Reads.AtSeat.covered_congr
#print axioms VerifiableInference.Reads.AtSeat.core_kept
#print axioms VerifiableInference.Reads.AtSeat.row_at_seat
