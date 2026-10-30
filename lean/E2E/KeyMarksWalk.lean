--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyMarksWalk.lean: ALONG THE FRONT HALF OF THE KEY FILE's FIRST CHAIN NO ROW WITH A WRITTEN-OUT
FACTOR COMES INTO THE STATEMENT OR INTO WHAT THE LOOKUPS WRITE; and behind "rng.0.rows" the mark on
the open rows holds at the ranges' group. From the chain's first round to the laying of the
lookups' rows: the two sendings, a link for each lookup, "rng.0.rows". At all values. Steps of the
verifier's: NOTHING IS SHOWN OF ANY PROVER.

  `PlainAll s`   no row of the statement has a written-out factor (`stPlainB`,
      Johnson/Desc/Ground/Shape/Marks.lean), and no row that the lookups have written has one.
  `k1rows_plain`, `decideSend_plain`, `seat_plain`, `idx_plain`, `msg_plain`   a sending keeps
      `stPlainB`: the kind's laying of the sample rows; its decision; its seat; the two
      sub-protocols "idx.1.send" and "msg.1.send". FOR ANY ACCEPT: nothing is asked of what was
      sent.
  ★ `link_plain`   a link keeps `PlainAll`: of whatever state the fold over the link returns; under
      the premises of `link_fold` (E2E/KeyLookupLink.lean).
  `links_plain`   all links: `links_fold` (E2E/KeyFirstHalf.lean) with `PlainAll` beside `Mid`.
  `layRows_plain`   behind "rng.0.rows": `stPlainB`, and the mark on the open rows (`claimsAtB`) at
      the ranges' group, the second from nothing.
  ★★ `first_half_plain`   THE WHOLE: under the premises of `first_half` and `stPlainB` at the state
      in front of the chain's first round: the fold over the front half accepts, and both hold at
      the state behind.

Why the first mark (`stTidyB`) is not walked here. The ground's law on the admitting of sample rows
keeps it only where these rows lie on their message; the first chain's shape carries that mark by
laws of its own (E2E/KeyShapeFirst.lean), and the guard in front of the ranges' test asks it.

By what. Calls: `sample_noDense`, `rows_noDense` (E2E/KeyRowsNoDense.lean); `recv_plain`,
`admit_plain`, `newGroup_plain`, `join_plain` (Marks.lean), `takeMasks_plain`, `addRows_plain`
(MoreMarks.lean), `addRows_claims`, `claimsAt_iff` (Claims.lean); `layRows_says`
(Johnson/Desc/K12/Honest/Shape/TestMarksAtRanges.lean); `link_fold`, `link_keeps`, `mid_of_front`,
`layRows_accepts`. The unfoldings go as those of E2E/KeyLedgers.lean and E2E/KeyFirstHalf.lean do.

Limits. `link_plain`, `links_plain` and `first_half_plain` STAND UNDER THE HYPOTHESES BY NAME OF
E2E/KeyRowsFit.lean AND E2E/KeyFirstHalf.lean (what was heard; public numbers), shown of no run.
FORM ALONE: that a row holds of anything is not touched. Nothing on completeness, on soundness or
on what a view shows.


-/
import E2E.KeyFirstHalf
import E2E.KeyRowsNoDense
import Johnson.Desc.Ground.Shape.MoreMarks
import Johnson.Desc.K12.Honest.Shape.TestMarksAtRanges

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyLookup
open OnBytes
open OnBytes.Model (Fork)
open _root_.Desc.Plain (DState)
open VerifiableInference.Desc
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Ground.Sh (stPlainB rowPlainB claimsAtB claimsAt_iff recv_plain
  admit_plain newGroup_plain join_plain takeMasks_plain addRows_plain addRows_claims)
open ProofFile.Honest.Sh (layRows_says)

/-- No row of the statement, and no row that the lookups have written, has a written-out factor. -/
def PlainAll (s : FirstState) : Prop :=
  stPlainB s.d.st = true ∧ ∀ r ∈ s.base.rows.flatten, rowPlainB r = true

/-! ## 1. The sendings -/

section Send
variable {L : Type}

/-- The kind's laying of the sample rows. -/
theorem k1rows_plain {codes : Codes} {seeds : List (List E × E)} :
    ∀ (l : List (ℕ × OracleShape)) (ys : List E) (d d' : DState L),
      VerifiableInference.Desc.K1.layRows codes seeds l ys d = .ok d' → stPlainB d.st = true →
      stPlainB d'.st = true
  | [], ys, d, d', e, hp => by
    unfold VerifiableInference.Desc.K1.layRows at e
    split at e
    · cases e
      exact hp
    · cases e
  | (o, s) :: l, ys, d, d', e, hp => by
    unfold VerifiableInference.Desc.K1.layRows at e
    split at e
    · exact k1rows_plain l ys d d' e hp
    · split at e
      · cases e
      · split at e
        · cases e
        · dsimp only at e
          obtain ⟨d₁, ha, e'⟩ := named_bind_ok e
          refine k1rows_plain l _ d₁ d' e' (admit_plain _ _ _ _ ha hp fun r hr => ?_)
          obtain ⟨x, -, rfl⟩ := List.mem_map.1 hr
          exact sample_noDense _ _ _ _ _ _

/-- The sending's decision. -/
theorem decideSend_plain {P : VerifiableInference.Desc.K1.Par} {owed : Option ℕ} {d d' : DState L}
    {rs : List Fmt.RoundView} {ns : Array ℕ}
    (e : VerifiableInference.Desc.K1.decideSend P owed d rs = .ok (ns, d'))
    (hp : stPlainB d.st = true) : stPlainB d'.st = true := by
  unfold VerifiableInference.Desc.K1.decideSend at e
  split at e
  · obtain ⟨_, -, e⟩ := bind_eq_ok e
    obtain ⟨_, -, e⟩ := bind_eq_ok e
    obtain ⟨_, -, e⟩ := bind_eq_ok e
    obtain ⟨_, -, e⟩ := bind_eq_ok e
    obtain ⟨x, hx, e⟩ := bind_eq_ok e
    obtain ⟨_, -, e⟩ := bind_eq_ok e
    obtain ⟨_, -, e⟩ := bind_eq_ok e
    obtain ⟨d₂, hl, e⟩ := bind_eq_ok e
    obtain ⟨ns', d₁⟩ := x
    have hr := named_ok hx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e)
    exact k1rows_plain _ _ d₁ _ hl (recv_plain _ _ _ _ _ hr hp)
  · cases e

end Send

section Key
variable {β Cl : Type}

/-- A sending's seat. -/
theorem seat_plain {name : String} {P : VerifiableInference.Desc.K1.Par} {s s' : ChainState β}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (e : (sendingSeat (Cl := Cl) name P).decide s rs gs = .ok s')
    (hp : stPlainB s.d.st = true) : stPlainB s'.d.st = true ∧ s'.base = s.base := by
  obtain ⟨y, hy, rfl⟩ := map_ok e
  obtain ⟨x, hx, rfl⟩ := map_ok hy
  obtain ⟨ns, d'⟩ := x
  have q : stPlainB d'.st = true := decideSend_plain hx hp
  exact ⟨q, rfl⟩

/-- "idx.1.send". -/
theorem idx_plain {one : Params.OneTime} {N : Pieces} {groups : List (List ℕ)}
    {s s' : ChainState β} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (e : (sendIndexMasks (Cl := Cl) one N groups).decide s rs gs = .ok s')
    (hp : stPlainB s.d.st = true) : stPlainB s'.d.st = true ∧ s'.base = s.base := by
  obtain ⟨s₁, h1, h2⟩ := bind_eq_ok (show (_ >>= _) = _ from e)
  obtain ⟨p1, b1⟩ := seat_plain h1 hp
  obtain ⟨i, -, h2⟩ := bind_eq_ok (show (_ >>= _) = _ from h2)
  obtain rfl := Except.ok.inj h2
  exact ⟨p1, b1⟩

/-- "msg.1.send". -/
theorem msg_plain {one : Params.OneTime} {N : Pieces} {groups : List (List ℕ)}
    {s s' : ChainState β} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (e : (sendOwnMessage (Cl := Cl) one N groups).decide s rs gs = .ok s')
    (hp : stPlainB s.d.st = true) : stPlainB s'.d.st = true ∧ s'.base = s.base := by
  obtain ⟨s₁, h1, h2⟩ := bind_eq_ok (show (_ >>= _) = _ from e)
  obtain ⟨p1, b1⟩ := seat_plain h1 hp
  have h2' : openRangesGroup one s₁ = .ok s' := h2
  unfold openRangesGroup at h2'
  obtain ⟨_, -, h2'⟩ := bind_eq_ok h2'
  obtain ⟨_, -, h2'⟩ := bind_eq_ok h2'
  obtain ⟨_, -, h2'⟩ := bind_eq_ok h2'
  obtain ⟨_, -, h2'⟩ := bind_eq_ok h2'
  obtain ⟨m, -, h2'⟩ := bind_eq_ok h2'
  obtain ⟨_, -, h2'⟩ := bind_eq_ok h2'
  obtain ⟨g, hg, h2'⟩ := bind_eq_ok h2'
  obtain ⟨d₂, hj, h2'⟩ := bind_eq_ok h2'
  obtain rfl := Except.ok.inj h2'
  exact ⟨join_plain _ _ _ _ _ (named_ok hj)
    (newGroup_plain (n := g.1) (d' := g.2) _ _ _ (named_ok hg) p1), b1⟩

end Key

/-! ## 2. The links -/

/-- ★ **A link keeps it**: of whatever state the fold over the link returns. -/
theorem link_plain (one : Params.OneTime) (set : Params.Setting) (i : ℕ) (x : Lookup) (ft : ℕ)
    {s : FirstState} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {es : List Fmt.Entry} {gV : HeardV}
    {G G₂ : Fork} {cl : List PlaneClaim}
    (hf : s.base.fork = none) (hk : s.base.keys.length = i)
    (hne : s.idx ≠ one.ranges.messageId)
    (h1 : Room s.d one.ranges.messageId
      ((faceOfLkp x).slots - 2 * (faceOfLkp x).parts.length))
    (h2 : Room s.d s.idx (2 * (faceOfLkp x).parts.length))
    (hv : ∀ v ∈ (faceOfLkp x).parts, 1 ≤ v)
    (hes : (lookupPlace set i x).entries = some es) (hlen : es.length ≤ rs.length)
    (hfit : roundsFit (es.map fun e => { entry := e }) (rs.take es.length) = true)
    (hh : hearV (faceOfLkp x) (({} : Fork).slots (faceOfLkp x).slots)
      ((rs.take es.length).map noDigest) = some (gV, G))
    (hL : Left (lookupPlace set i x) (toHeardG gV) G cl G₂) (hA : PlainAll s)
    {y : FirstState × List Fmt.RoundView × List OpenedColumn}
    (h : foldBlocks ft (lookupLink one set i x).blocksInOrder s rs cols = .ok y) : PlainAll y.1 := by
  obtain ⟨o, d₁, k, d₂, rows, keys, e1, e2, hrows, hfold⟩ := link_fold one set i x ft
    (cols := cols) hf hk hne h1 h2 hv hes hlen hfit hh hL
  rw [hfold] at h
  obtain rfl := Except.ok.inj h
  refine ⟨takeMasks_plain _ _ _ _ _ e2 (takeMasks_plain _ _ _ _ _ e1 hA.1), fun r hr => ?_⟩
  have hr' : r ∈ (s.base.rows ++ [rows]).flatten := hr
  rw [List.flatten_append, List.mem_append] at hr'
  rcases hr' with c | c
  · exact hA.2 r c
  · exact rows_noDense hrows r (by simpa using c)

/-- **All links.** -/
theorem links_plain (one : Params.OneTime) (set : Params.Setting) (ft : ℕ) {V : ℕ} (hV : V ≤ 63)
    {cols : List OpenedColumn} {B : ℕ} {sm si : OracleShape} {cs : Codes} :
    ∀ {i : ℕ} {xs : List Lookup} {rs rs' : List Fmt.RoundView}, LinksHeard one set V i xs rs rs' →
    ∀ {s : FirstState} {a b k₁ k₂ : ℕ},
      Mid one cs s i (ownTake xs + a) (idxTake xs + b) k₁ k₂ B V sm si → PlainAll s →
      ∃ s', foldBlocks ft (((xs.zipIdx i).map fun x => lookupLink one set x.2 x.1).flatMap
          Link.blocksInOrder) s rs cols = .ok (s', rs', cols) ∧
        Mid one cs s' (i + xs.length) a b (k₁ + ownTake xs) (k₂ + idxTake xs) B V sm si ∧
        PlainAll s' := by
  intro i xs rs rs' h
  induction h with
  | nil i rs =>
    intro s a b k₁ k₂ hM hA
    refine ⟨s, rfl, ?_, hA⟩
    simpa [ownTake, idxTake] using hM
  | @cons i x xs rs rs' es gV G G₂ cl hv hes hlen hfit hh hL hO hO' hT _ ih =>
    intro s a b k₁ k₂ hM hA
    have hM' : Mid one cs s i
        ((faceOfLkp x).slots - 2 * (faceOfLkp x).parts.length + (ownTake xs + a))
        (2 * (faceOfLkp x).parts.length + (idxTake xs + b)) k₁ k₂ B V sm si := by
      simpa [ownTake, idxTake, Nat.add_assoc] using hM
    obtain ⟨s₁, f1, m1⟩ := link_keeps one set i x ft (cols := cols) hM' hv hes hlen hfit hh hL hO
      hO' hT hV
    have p1 : PlainAll s₁ := link_plain one set i x ft hM'.fork hM'.keys hM'.ne
      (hM'.own.room (Nat.le_add_right _ _)) (hM'.idx.room (Nat.le_add_right _ _)) hv hes hlen
      hfit hh hL hA f1
    obtain ⟨s₂, f2, m2, p2⟩ := ih m1 p1
    refine ⟨s₂, ?_, ?_, p2⟩
    · rw [List.zipIdx_cons, List.map_cons, List.flatMap_cons]
      exact (foldBlocks_append_ok _ _ _ _ _ _).2 ⟨s₁, _, _, f1, f2⟩
    · have e1 : i + (x :: xs).length = i + 1 + xs.length := by
        rw [List.length_cons]
        omega
      rw [e1]
      simpa [ownTake, idxTake, Nat.add_assoc] using m2

/-! ## 3. "rng.0.rows", and the whole -/

/-- Behind "rng.0.rows". -/
theorem layRows_plain {one : Params.OneTime} {s s' : FirstState} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (h : (layRows one).decide s rs gs = .ok s')
    (hA : PlainAll s) : stPlainB s'.d.st = true ∧ claimsAtB s'.d.st s'.grp = true := by
  obtain ⟨c2, d, hd, rfl⟩ := layRows_says h
  refine ⟨addRows_plain _ _ _ _ hd hA.1 hA.2,
    addRows_claims _ _ _ _ hd _ (claimsAt_iff.2 fun G hG r hr => ?_)⟩
  rw [hG] at c2
  have c3 : (G.rows.isEmpty && !G.inRun) = true := c2
  rw [Bool.and_eq_true] at c3
  have e : G.rows = #[] := Array.isEmpty_iff.1 c3.1
  rw [e] at hr
  cases hr

/-- ★★ **THE FRONT HALF: no row with a written-out factor in the statement behind it, and the mark
on the open rows at the ranges' group.** -/
theorem first_half_plain (one : Params.OneTime) (set : Params.Setting) (ft : ℕ)
    {g₁ g₂ : List (List ℕ)} {s s₂ : FirstState} {rs rs₂ rs₃ : List Fmt.RoundView}
    {cols cols₂ : List OpenedColumn} {V a b : ℕ}
    (hfront : foldBlocks ft [sendIndexMasks (Cl := Key.Claim) one pieces g₁,
      sendOwnMessage one pieces g₂] s rs cols = .ok (s₂, rs₂, cols₂))
    (i0 : one.indexMasks.shape.answers ≠ 0) (im : 0 < one.indexMasks.shape.maskRows)
    (m0 : one.ranges.message.shape.answers ≠ 0) (mm : 0 < one.ranges.message.shape.maskRows)
    (hf : s.base.fork = none) (hk : s.base.keys = []) (hr : s.base.rows = [])
    (hH : LinksHeard one set V 0 (lookupsOf one) rs₂ rs₃) (hV : V ≤ 63)
    (hown : freeOf s.d.st.codes one.ranges.message.shape = ownTake (lookupsOf one) + a)
    (hidx : freeOf s.d.st.codes one.indexMasks.shape = idxTake (lookupsOf one) + b)
    (hmain : 0 < one.ranges.message.shape.mainRows)
    (hbits : ceilLog2 one.ranges.message.shape.mainRows +
      (s.d.st.codes.base.getD one.ranges.message.shape.code default).logEll = V)
    (hp : stPlainB s.d.st = true) :
    ∃ s₄, foldBlocks ft ([sendIndexMasks one pieces g₁, sendOwnMessage one pieces g₂] ++
        ((lookupsOf one).zipIdx.map fun x => lookupLink one set x.2 x.1).flatMap Link.blocksInOrder ++
        [layRows one]) s rs cols = .ok (s₄, rs₃, cols₂) ∧
      stPlainB s₄.d.st = true ∧ claimsAtB s₄.d.st s₄.grp = true := by
  obtain ⟨-, s₁, c₁, st1, r1⟩ := foldBlocks_cons_ok.1 hfront
  obtain ⟨-, s₂', c₂, st2, r2⟩ := foldBlocks_cons_ok.1 r1
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj r2)
  have e₁ := (Block.step_ok.1 st1).2.2.1
  have e₂ := (Block.step_ok.1 st2).2.2.1
  have hM := mid_of_front V e₁ e₂ i0 im m0 mm hf hk hr
  rw [hown, hidx] at hM
  obtain ⟨p1, b1⟩ := idx_plain e₁ hp
  obtain ⟨p2, b2⟩ := msg_plain e₂ p1
  have hA : PlainAll s₂' := ⟨p2, fun r hr' => by
    rw [b2, b1, hr] at hr'
    cases hr'⟩
  obtain ⟨s₃, f3, m3, p3⟩ := links_plain one set ft hV (cols := cols₂) hH hM hA
  rw [Nat.zero_add] at m3
  obtain ⟨d, hd, -⟩ := layRows_accepts one [] [] m3 hmain hbits
  obtain ⟨q1, q2⟩ := layRows_plain hd p3
  refine ⟨{ s₃ with d := d }, ?_, q1, q2⟩
  rw [List.append_assoc]
  refine (foldBlocks_append_ok _ _ _ _ _ _).2 ⟨_, _, _, hfront, ?_⟩
  refine (foldBlocks_append_ok _ _ _ _ _ _).2 ⟨_, _, _, f3, ?_⟩
  exact fold_quiet rfl ft hd rfl

end AtPublicFiles.KeyLookup

#print axioms AtPublicFiles.KeyLookup.k1rows_plain
#print axioms AtPublicFiles.KeyLookup.decideSend_plain
#print axioms AtPublicFiles.KeyLookup.seat_plain
#print axioms AtPublicFiles.KeyLookup.idx_plain
#print axioms AtPublicFiles.KeyLookup.msg_plain
#print axioms AtPublicFiles.KeyLookup.link_plain
#print axioms AtPublicFiles.KeyLookup.links_plain
#print axioms AtPublicFiles.KeyLookup.layRows_plain
#print axioms AtPublicFiles.KeyLookup.first_half_plain
