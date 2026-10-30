-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/JoinShare.lean: K12's SHARE OF THE FRAME's AUTHORS' JOIN, AS ONE
RECORD, AND ITS TIES AT THEIR `joinQ`. One definition, four theorems.

IT STANDS OVER FOUR FILES OF OTHER AUTHORS:
Honest/Thread/Join.lean and JoinFit.lean,
and beneath them Honest/K1/Law/TreeLotsAtAll.lean and LotsAtAll.lean. The first
two are taken from their authors; by the authors' word the bytes of JoinFit.lean taken here had no
fresh reader.

  `k12Share`   ml, pl, tl, tn out of ScriptLots.lean's and ScriptLotsPads.lean's terms, in the
                 record `Others`
  `share_in_add`   put behind another share with `Others.add`, all of ours is present, provided the
                 other share does not list the number b
  `join_msgs_k12`, `join_pads_k12`, `join_trees_k12`   `OwnMsgs`, `OwnPads` (first and second
                 tenant), `OwnTrees` at our texts and `joinQ`: a single call each of
                 `join_msgs_other`, `join_pads_other`, `join_trees_other`

How the pieces fit. The four conclusions of `share_in_add` are the hypotheses hsub, hsub, hb, htl of
the three ties.

Limits.
- What ScriptLots.lean's head says a law over coins has to mind holds for this file, and what
  LotsLaid.lean's first limit says of itself is true here too: the book's facts are neither imported
  nor named in a statement.
- F : JoinFit … IS A HYPOTHESIS. That a list containing our share is fit is proved nowhere here. At
  the small configuration that the library has written out the authors' test for it, `joinFitB`, was
  seen to accept, by the evaluator, on their lane. On ours, in a trial over the first issue of their
  Join.lean, 6 of the 10 tests of which `joinFitB` consists in their third issue were seen to accept
  (`agreeB`, `ownedB`, `treesB`, `foundB`, `placesB`, `coinsB`; `foundB` with the body it had then,
  which its authors have since changed); `numsB`, `treesFitB`, `seatsB`, `laysB` and `joinFitB`
  itself we have not run. Evaluations, no theorem, and at that size only.
- VACUITY, as in LotsLaid.lean: where the frame lends nothing or ok rejects, our texts return no
  value and the ties assert nothing. Nothing shows that this is ever otherwise.
- `JoinFit` compares how many trees a sub-protocol declares with a plan's number for the shared
  sending's jobs only. Neither it nor this file compares what the sub-protocol at b declares with
  our job's number of switches.
- bs, front and our n₀, t₀ remain independent parameters, as in LotsLaid.lean.
- Only for a job with `J.fresh` = some …: ScriptLots.lean's first limit.
- No control.
- It moves no count. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.LotsLaid
import Johnson.Desc.ProofFile.Honest.Thread.JoinFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (SendJob PlaceIn)

variable {Bk : ProverCoinCounts} {Cl Wl Xi X X₂ Cells Tok : Type}

/-- **K12's share of the join, as one record.** -/
def k12Share (ch : ℕ) (J : TestJob Wl X₂) (own₂ : X₂) (n₀ t₀ : ℕ) (arr : ℕ → ℕ → ℕ)
    (ok : Wl → List Fmt.Drawn → (ℕ → Stretch) → Bool) (codes : OnBytes.Codes)
    (sh sh₁ : ℕ → OnBytes.OracleShape) (b : ℕ) (rest : ℕ → TreeLot Bk Wl) : Others Bk Wl :=
  { ml := testMsgLots ch J own₂ n₀ t₀ arr ok
    pl := testPl ch J codes sh sh₁ t₀
    tl := testTl ch J own₂ n₀ ok b rest
    tn := testTn b }

/-- **Put behind another share with `Others.add`, all of K12's share is present**, provided hb: the
other share does not list b. -/
theorem share_in_add (A : Others Bk Wl) (ch : ℕ) (J : TestJob Wl X₂) (own₂ : X₂) (n₀ t₀ : ℕ)
    (arr : ℕ → ℕ → ℕ) (ok : Wl → List Fmt.Drawn → (ℕ → Stretch) → Bool) (codes : OnBytes.Codes)
    (sh sh₁ : ℕ → OnBytes.OracleShape) (b : ℕ) (rest : ℕ → TreeLot Bk Wl)
    (hb : A.tn.contains b = false) :
    (∀ L ∈ testMsgLots ch J own₂ n₀ t₀ arr ok, L ∈ (A.add (k12Share ch J own₂ n₀ t₀ arr ok codes sh
      sh₁ b rest)).ml) ∧
    (∀ L ∈ testPl ch J codes sh sh₁ t₀, L ∈ (A.add (k12Share ch J own₂ n₀ t₀ arr ok codes sh sh₁ b
      rest)).pl) ∧
    b ∈ (A.add (k12Share ch J own₂ n₀ t₀ arr ok codes sh sh₁ b rest)).tn ∧
    (A.add (k12Share ch J own₂ n₀ t₀ arr ok codes sh sh₁ b rest)).tl b =
      testTreeLot ch J own₂ n₀ ok := by
  refine ⟨fun L hL => List.mem_append_right _ hL, fun L hL => List.mem_append_right _ hL,
    List.mem_append_right _ (List.mem_singleton.2 rfl), ?_⟩
  show (if A.tn.contains b then A.tl b else testTl ch J own₂ n₀ ok b rest b) = _
  rw [hb]
  exact (testTl_at ch J own₂ n₀ ok b rest).1

/-- **`OwnMsgs` at `joinQ` and our messages' texts** (two for each switch of the job), under F and
hsub. -/
theorem join_msgs_k12 {bs : List (Block S Cl)} {front : ℕ} {arr : ℕ → ℕ → ℕ} {seats : List (ℕ × ℕ)}
    {wit : Wl → PlaceIn Xi} {own₀ : X} {jobs : List (ℕ × SendJob (PlaceIn Xi) X)} {O : Others Bk Wl}
    (F : JoinFit bs front arr seats wit own₀ jobs O) (ch : ℕ) (J : TestJob Wl X₂) (own₂ : X₂)
    (n₀ t₀ : ℕ) (ok : Wl → List Fmt.Drawn → (ℕ → Stretch) → Bool)
    (hsub : ∀ L ∈ testMsgLots ch J own₂ n₀ t₀ arr ok, L ∈ O.ml) (cells : Wl → Cells)
    (tok : Wl → Tok) (Vd : Wl → Prop) (N : ℕ) :
    ∀ τ, τ < J.p.nums.stages.length - 1 → ∀ t, t < 2 →
      OwnMsgs (joinQ bs front cells tok arr wit own₀ jobs O) Vd N (arr (t₀ + τ) t)
        (n₀ + seedRound J.p.nums.stages τ) (testMsgTxt ch J own₂ n₀ ok τ t) := by
  intro τ hτ t ht
  exact join_msgs_other F (hsub _ (mem_testMsgLots ch J own₂ n₀ t₀ arr ok hτ ht)) cells tok Vd N

/-- **`OwnPads` at `joinQ` and our pads' texts**, first and second tenant, under F and hsub. -/
theorem join_pads_k12 {bs : List (Block S Cl)} {front : ℕ} {arr : ℕ → ℕ → ℕ} {seats : List (ℕ × ℕ)}
    {wit : Wl → PlaceIn Xi} {own₀ : X} {jobs : List (ℕ × SendJob (PlaceIn Xi) X)} {O : Others Bk Wl}
    (F : JoinFit bs front arr seats wit own₀ jobs O) (ch : ℕ) (J : TestJob Wl X₂)
    (codes : OnBytes.Codes) (sh sh₁ : ℕ → OnBytes.OracleShape) (t₀ : ℕ)
    (hsub : ∀ L ∈ testPl ch J codes sh sh₁ t₀, L ∈ O.pl) (cells : Wl → Cells) (tok : Wl → Tok)
    (Vd : Wl → Prop) :
    ∀ τ, τ < J.p.nums.stages.length - 1 →
      OwnPads (joinQ bs front cells tok arr wit own₀ jobs O) Vd (t₀ + τ) 0 (fun k _ => testPadTxt ch
        J codes sh τ k) ∧
      OwnPads (joinQ bs front cells tok arr wit own₀ jobs O) Vd (t₀ + τ) 1 (fun k _ => testPadTxtB
        ch J codes sh₁ τ k) := by
  intro τ hτ
  have hm := mem_testPl (Bk := Bk) ch J codes sh sh₁ t₀ hτ
  exact ⟨join_pads_other F (hsub _ hm.1) cells tok Vd,
    join_pads_other F (hsub _ hm.2) cells tok Vd⟩

/-- **`OwnTrees` at `joinQ` and our lot of trees**, under F, hb and htl. -/
theorem join_trees_k12 {V X' Pb : Type} {bs : List (Block S Cl)} {front : ℕ} {arr : ℕ → ℕ → ℕ}
    {seats : List (ℕ × ℕ)} {wit : Wl → PlaceIn Xi} {own₀ : X}
    {jobs : List (ℕ × SendJob (PlaceIn Xi) X)} {O : Others Bk Wl}
    (F : JoinFit bs front arr seats wit own₀ jobs O) (cells : Wl → Cells) (tok : Wl → Tok)
    (T : Thread Bk S Cl V Wl X' Pb) (hbs : T.bs = bs) (hfr : T.front = front)
    (htab : T.table = (joinQ bs front cells tok arr wit own₀ jobs O).table)
    (hfix : T.fixed = (joinQ bs front cells tok arr wit own₀ jobs O).fixed) (ch : ℕ)
    (J : TestJob Wl X₂) (own₂ : X₂) (n₀ : ℕ) (ok : Wl → List Fmt.Drawn → (ℕ → Stretch) → Bool)
    {b : ℕ} (hb : b ∈ O.tn) (htl : O.tl b = testTreeLot ch J own₂ n₀ ok) {blk : Block S Cl}
    (hblk : bs[b]? = some blk) :
    OwnTrees T b (blk.oracles.flatMap id).length (testTbl ch J own₂ n₀ ok) (seedRound
      J.p.nums.stages) := by
  have h := join_trees_other F cells tok T hbs hfr htab hfix hb hblk
  rw [htl] at h
  exact h

end ProofFile.Honest.K12

end

#print axioms ProofFile.Honest.K12.k12Share
#print axioms ProofFile.Honest.K12.share_in_add
#print axioms ProofFile.Honest.K12.join_msgs_k12
#print axioms ProofFile.Honest.K12.join_pads_k12
#print axioms ProofFile.Honest.K12.join_trees_k12
