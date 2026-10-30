-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/Law/MakesAtHead.lean: CONDITIONAL: BEHIND A YES OF THE SMALLNESS TEST's DRAW
(kind K8) THE PUBLIC TEST OF THE RUN "K8.equations" HOLDS, AT EVERY MEANING OF THE TABLE OF JOINTS,
under the library's hypothesis on the public input. On the verifier's own text; no prover in it. IT
IMPORTS FILES OF THE LIBRARY ALONE. Statements with their proofs; no definition.

Why. The draw's row opens the run of forms "small", and the table ties a public test to every open
run: the block that opens it must make it. The library has that sentence (`P1K8T.k08_makes`,
Johnson/P1K8R/MakesAt.lean) under a structure of what is left, `MakesOwes`. The library fills that
structure at one place: as the field `makes` of `K8Left`, in `k08_left_const`
(Johnson/P1K8R/ConstAt.lean), at the closed meaning `P5J.mgAtAll h`, out of `K8LeftC` (which
Johnson/P1K8R/TightAt.lean builds), whose field `atFold` has that meaning's promise as a premise.
And it asks that the state in front be reached by the WRAPPED steps (`RchAt`,
Johnson/Top/H0/Walk/ReachAt.lean), which test in front of each member that every word shown is below
the prime. A thread of an honest run has the promise at other letters, and a fold over the bare
members. Here the meaning is a free letter, and the fold over the bare members is enough.

How. Nothing new is shown of the protocol. The law beneath is the library's `formsInA_row`
(Johnson/Desc/First/Batch/SmallNear.lean). Every payer beneath the library's two proofs is general
in the meaning or reads none, and spends of "reached" the fold over the bare members alone.
`fold_at_draw` follows the proof of `P1K8T.k08_fold_at` (Johnson/P1K8R/FoldAtDraw.lean) from that
fold on. `makes_fold` follows the proof of `k08_makes`, with the four lemmas on the fold
(`named_at_place`, `front_at_place`, `own_at_place`, `k8FunsAre` of Johnson/P1K8R/) where that proof
calls their forms at `RchAt`, and with what `MakesOwes` would hand in paid on the spot:
`smallSizes_at_state` at `P5J.ownSizes_at_head`, `near_of_plan_size` at `IM.k08_near_at`,
`seatsOwn_of_onQ`, `reader_small` at `ToldDesc.link_there`, `gtSizes_of_B`.

Main names:
  `makesOwes_any`   `MakesOwes` at every meaning, at a letter for "reached" that gives `RchAt`.
      Nothing here calls it: it is for whoever calls `k08_makes`, or fills `K8Left`, at another
      meaning
  `fold_at_draw`   the nine equations on the open link and the statement of oracles (`K8FoldAt`), at
      the state of a fold over the bare members in front of the draw
  `makes_fold`   **the public test behind the draw's yes, at every meaning, at such a state**
  `makes_reach`   **the same at a state that the bare members' steps reach**
  `makes_any`   the same at a state that the wrapped steps reach

Premises of `makes_fold`. h: the library's hypothesis on the public input (`P5J.AtMgA`,
Johnson/P5J/MgAtAll.lean). O: the opening of the description's maker (the hypothesis has one: its
field `laid.opened`). hl, e3: the segment's number l is at most 24, and Xl is its built link. ha:
the table's promise in front of the draw, at the meaning Mg. f: the fold. hm: no mark in front. hy:
the draw's decision says yes.
ON h. It can be met: at the full-size public files as Ladder/Stored.lean spells them it has a member
with no premise (`headMember_zFull`, AtFullSide/Top/HeadMemberAtFull.lean). This file does not call
it. These files are tied to the package's files by no theorem.

Limits. An implication: no state that meets ha, f, hm and hy together is shown here. The number 4 +
`oOf` l of the run's piece is the library's `pcOf` l - 1 (`P1K8T.pcOf_eq`,
Johnson/P1K8R/BlindJoin.lean); not called here. At the library's full size and at the format's
second hash function alone: h is typed there. K8 is the draw alone: that the committed values are small
against a cheating prover needs K3 (the digits' lookups), K9 (the forms of the run "small") and the
sendings' pins as well (Johnson/P1K8R/KindFromHead.lean's own limit). The file sets `maxHeartbeats`
to 1000000.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.P1K8R.FoldAtDraw
import Johnson.IMR.NearAtDraw
import Johnson.ToldDescR.LinkThere
import Johnson.Desc.Sound.K8Tests.GtSizesOfPublic
import Johnson.Desc.Sound.K8Tests.PlanFitsOfPublic
import Johnson.HB.LLHARD.K8NamesDoorAtHead
import Johnson.P5J.K8OwnSizesAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace H2K8
open Inst.Model
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Claim OpenedColumn foldBlocks)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Meaning flatPlacesOf)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Ready (seven lay7 lay7_of_test cond_of_front planFitsAllB)
open VerifiableInference.Desc.K9 (formsInA formsInA_row segAt_of near_of_plan_size)
open Johnson.Desc.First.Walk.Tied (RchAt Reach rchAt_fold)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA)
open P1K8T (FD MakesOwes K8FoldAt k08_fold_at n0At oOf frameJoined_of_members drawAt_place)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **What the law on "the draw makes its run's public test" leaves, at every meaning.**
CONDITIONAL: the hypothesis h; O; hl; e3; hRch: the letter for "reached" gives `RchAt`. -/
theorem makesOwes_any (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {W' : Type} {Fr : Frame}
    (Mg : Meaning ProofFile.InstPub W') {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) Zp Bs
      base cF (seatZ Zp Np) (secondAt Zp Np))
    {l : ℕ} (hl : l ≤ 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}
    (hRch : ∀ k a, Rch k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a) :
    MakesOwes (P5J.At.N Zp cF) Mg Bs.G₀.W (h.𝔇.Rd l) (4 + oOf l)
      (ProofFile.k8ParW Zp Bs.G₀ Xl l).toPar l Rch := by
  have hx : ((l, if l = 24 then 5 else 4) : ℕ × ℕ) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 (by omega), rfl⟩
  obtain ⟨Lk, hLk, -⟩ := ToldDesc.link_there h.scope h.reads O l hl
  have hGt : Second.K08.gtSizesAllB Bs.G₀.W = true := by
    rw [O.W]
    exact LT28.K8Tests.gtSizesAllB_of_public h.pubOne
  have hOwn := P5J.ownSizes_at_head h _ O.blank
  have hnear := IM.k08_near_at h O.blank hl e3
  refine ⟨fun t => reader_small (𝔇 := h.𝔇) l Lk hLk (4 + oOf l) t,
    fun tlP hv => Second.K08.gtSizes_of_B hGt tlP (P1K8S.planVal_of_at hv),
    fun z a u tl ha hr hm hu ht => ?_⟩
  obtain ⟨L, Gr, pre, hL, hg, hGr, hmem, e1, e2, e5, e6, e4⟩ :=
    k08_fold_at h O.blank hl e3 ((z, a.1), a.2) (hRch _ _ hr)
  have eu : u.L = L := Option.some.inj ((link_of_segAt a.1 u hu).symm.trans hL)
  have hr' : RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF)
      (14 * l + (if l = 24 then 5 else 4) + 2) ((z, a.1), a.2) := by
    rw [← drawAt_place]
    exact hRch _ _ hr
  obtain ⟨tlP, hv, h7, -⟩ := P1K8S.k8LaidOwn h.scope h.reads O hx ((z, a.1), a.2) hr'
  have eP : tlP = Xl.tl := P1K8S.planAt_built h.scope h.reads O e3 hv
  have e7 : seven tl = seven Xl.tl := by
    have e := lay7_of_test h7
    unfold lay7 at e
    rw [ht] at e
    rw [← eP]
    exact Option.some.inj e
  have eZ : tl.ix.ZZ = Xl.tl.ix.ZZ := congrArg (·.2.1.ZZ) e7
  refine ⟨fun tlQ hq => ?_,
    seatsOwn_of_onQ _ _ (fun s => (z, s)) l hl a ha hm (fun L' hL' => ?_) _, ?_⟩
  · rw [eu]
    exact ProofFile.smallSizes_at_state Zp Bs.G₀ hOwn l Xl e3 L tlQ e1 e2
      (by rw [P1K8S.planAt_built h.scope h.reads O e3 hq])
  · obtain rfl : L = L' := Option.some.inj (hL.symm.trans hL')
    exact ⟨frameJoined_of_members hg hGr hmem, hg⟩
  · rw [eZ]
    exact near_of_plan_size (n0At Zp l) _ _ u Xl.arrayOf Bs.G₀.first.layout Zp.first.shape l _
      (by rw [eu]; exact e1) (by rw [eu]; exact e2) (by rw [eu]; exact e6) (by rw [eu]; exact e4)
      (by rw [eu]; exact e5) hnear

/-- **The nine equations at the state of a fold over the members in front of the draw.** After
`P1K8T.k08_fold_at`, which has them at a state reached by the wrapped steps and spends the fold over
the bare members alone. CONDITIONAL: the hypothesis h; hG: G is the ground that the description's
maker makes; hl; e3; f: the fold. -/
theorem fold_at_draw (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24) {Xl : LinkH}
    (e3 : G.built[l]? = some Xl) (z : ProofFile.InstPub) {s : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    (f : foldBlocks 0 (cF.blocksInOrder.take (drawAt l)) (ProofFile.startS Zp z) rs cols = .ok (s, [], [])) :
    K8FoldAt Zp G l Xl (n0At Zp l) s := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  rcases Nat.lt_or_ge l 24 with h24 | h24
  · have ed : drawAt l = 14 * l + 6 := by
      unfold drawAt
      rw [if_neg (by omega)]
    rw [ed] at f
    obtain ⟨L, Gr, pre, hL, -, hg, hGr, -, hmem, -, -⟩ :=
      Meaning.K2.members_at h.scope h.reads O h24 (n := 3) (by omega) f
    obtain ⟨L₂, hL₂, -, e1, e2, -⟩ := Meaning.K2.arrays_open h.scope h.reads O (by omega : l < 25)
      e3 (k := 14 * l + 6) (by rw [if_neg (by omega)]; omega) (by rw [if_neg (by omega)]; omega) f
    obtain ⟨L₃, hL₃, -, e5, e6, e4, -⟩ :=
      Meaning.K2.own_size_draw h.scope h.reads O h24 (n := 0) (by omega) f
    obtain rfl : L = L₂ := Option.some.inj (hL.symm.trans hL₂)
    obtain rfl : L = L₃ := Option.some.inj (hL.symm.trans hL₃)
    exact ⟨L, Gr, pre, hL, hg, hGr, hmem, e1, e2, e5, e6, e4⟩
  · obtain rfl : l = 24 := by omega
    have f'' : foldBlocks 0 (cF.blocksInOrder.take 343) (ProofFile.startS Zp z) rs cols = .ok (s, [], []) := f
    obtain ⟨L, Gr, n₁, hL, -, hg, hGr, hmem, -, -⟩ :=
      Meaning.K2.members_head h.scope h.reads O (n := 3) (by omega) f''
    obtain ⟨L₂, hL₂, -, e1, e2, -⟩ := Meaning.K2.arrays_open h.scope h.reads O (by omega : 24 < 25)
      e3 (k := 343) (by decide) (by decide) f''
    obtain ⟨L₃, hL₃, -, e5, e6, e4, -⟩ :=
      Meaning.K2.own_size_head h.scope h.reads O (n := 0) (by omega) f''
    obtain rfl : L = L₂ := Option.some.inj (hL.symm.trans hL₂)
    obtain rfl : L = L₃ := Option.some.inj (hL.symm.trans hL₃)
    exact ⟨L, Gr, #[n₁], hL, hg, hGr, hmem, e1, e2, e5, e6, e4⟩

/-- **BEHIND A YES OF THE DRAW THE PUBLIC TEST OF THE RUN "K8.equations" HOLDS, AT EVERY MEANING, AT
THE STATE OF A FOLD OVER THE BARE MEMBERS.** After `P1K8T.k08_makes`. CONDITIONAL: the hypothesis h;
O; hl; e3; ha: the promise in front; f: the fold; hm: no mark; hy: the draw's yes. -/
theorem makes_fold (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {W' : Type} {Fr : Frame}
    (Mg : Meaning ProofFile.InstPub W') {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) Zp Bs
      base cF (seatZ Zp Np) (secondAt Zp Np))
    {l : ℕ} (hl : l ≤ 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (z : ProofFile.InstPub) (a b : S × Fr.E.Str)
    (ha : onQ (P5J.At.N Zp cF) Mg linksFull (flatPlacesOf linksFull true) (fun s => (z, s))
      (drawAt l) a)
    {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    (f : foldBlocks 0 (cF.blocksInOrder.take (drawAt l)) (ProofFile.startS Zp z) rs cols = .ok (a.1, [], []))
    (hm : a.1.failed = none)
    (hy : ∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS (ProofFile.k8ParW Zp Bs.G₀ Xl l).toPar).decide a.1 rs gs =
      .ok b.1) :
    formsInA (h.𝔇.Rd l) ((P5J.At.N Zp cF).sent l) ((P5J.At.N Zp cF).group l) (4 + oOf l)
      "K8.equations" b.1 = true := by
  have hx : ((l, if l = 24 then 5 else 4) : ℕ × ℕ) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 (by omega), rfl⟩
  have hW : planFitsAllB Bs.G₀.W = true := by
    rw [O.W]
    exact LT28.K8Tests.planFitsAllB_of_public h.pubOne
  have hGt : Second.K08.gtSizesAllB Bs.G₀.W = true := by
    rw [O.W]
    exact LT28.K8Tests.gtSizesAllB_of_public h.pubOne
  have f' : foldBlocks 0 (cF.blocksInOrder.take (14 * l + (if l = 24 then 5 else 4) + 2)) (ProofFile.startS Zp z)
      rs cols = .ok (a.1, [], []) := by
    rw [← drawAt_place]
    exact f
  obtain ⟨Lk, hLk, -⟩ := ToldDesc.link_there h.scope h.reads O l hl
  have hNa : Named.namedAt (ProofFile.k8ParW Zp Bs.G₀ Xl l).toPar a.1 = true :=
    P1K8S.named_at_place h.scope h.reads O h.laid.planOk (P5J.namesDoorB_at_head h) hx e3 z rs cols
      _ f'
  have hfr : VerifiableInference.Desc.First.K8.Ready.frontB a.1 = true :=
    P1K8S.front_at_place h.scope h.reads O (P1K8S.planFitsAll_of_test hW) hx z rs cols _ f'
  obtain ⟨tlP, hv, h7, -⟩ := P1K8S.own_at_place h.scope h.reads O hx z rs cols _ f'
  obtain ⟨tl, ht, hfu⟩ := P1K8S.k8FunsAre h.scope h.reads O hx z rs cols _ f'
  have ht : a.1.tl? = some tl := ht
  have hfu : a.1.funs? = some tl.funs := hfu
  obtain ⟨L, Gr, pre, hL, hg, hGr, hmem, e1, e2, e5, e6, e4⟩ :=
    fold_at_draw h O.blank hl e3 z f
  obtain ⟨F', hF⟩ := fork_of_onQ _ Mg (fun s => (z, s)) l hl a ha hm
  obtain ⟨q, hq, -, -, -⟩ := segAt_of a.1 L F' tl hL hF ht
  obtain ⟨tl₁, ht₁, -, hX, -, u, hu⟩ := cond_of_front hfr
  obtain rfl : tl = tl₁ := Option.some.inj (ht.symm.trans ht₁)
  have eu : q.L = L := Option.some.inj ((link_of_segAt a.1 q hq).symm.trans hL)
  have eP : tlP = Xl.tl := P1K8S.planAt_built h.scope h.reads O e3 hv
  have e7 : seven tl = seven tlP := by
    have e := lay7_of_test h7
    unfold lay7 at e
    rw [ht] at e
    exact Option.some.inj e
  have eZ : tl.ix.ZZ = Xl.tl.ix.ZZ := by
    rw [← eP]
    exact congrArg (·.2.1.ZZ) e7
  have hgt : tl.gtTree.size = tl.NM := by
    have e := Second.K08.gtSizes_of_B hGt tlP (P1K8S.planVal_of_at hv)
    have e1' : tl.gtTree = tlP.gtTree := congrArg (·.1) e7
    have e2' : tl.NM = tlP.NM := congrArg (·.2.2.2.2.1) e7
    rw [e1', e2']
    exact e
  have hU : tl.ix.U.getD 2 none = some u := by
    rw [Array.getD_eq_getD_getElem?, hu]
    rfl
  have hsz : VerifiableInference.Desc.K9.smallSizesB q.L.arrayOf q.L.check.rows.layout tlP
      (ProofFile.k8ParW Zp Bs.G₀ Xl l).toPar = true := by
    rw [eu]
    exact ProofFile.smallSizes_at_state Zp Bs.G₀ (P5J.ownSizes_at_head h _ O.blank) l Xl e3 L tlP e1 e2
      (by rw [eP])
  have hso := seatsOwn_of_onQ _ Mg (fun s => (z, s)) l hl a ha hm (fun L' hL' => by
    obtain rfl : L = L' := Option.some.inj (hL.symm.trans hL')
    exact ⟨frameJoined_of_members hg hGr hmem, hg⟩) (ProofFile.k8ParW Zp Bs.G₀ Xl l).toPar
  have hnear : VerifiableInference.Desc.K9.nearA ((P5J.At.N Zp cF).sent l)
      ((P5J.At.N Zp cF).group l) q tl.ix.ZZ = true := by
    rw [eZ]
    exact near_of_plan_size (n0At Zp l) _ _ q Xl.arrayOf Bs.G₀.first.layout Zp.first.shape l _
      (by rw [eu]; exact e1) (by rw [eu]; exact e2) (by rw [eu]; exact e6) (by rw [eu]; exact e4)
      (by rw [eu]; exact e5) (IM.k08_near_at h O.blank hl e3)
  obtain ⟨rs', gs, hd⟩ := hy
  exact formsInA_row ((P5J.At.N Zp cF).sent l) ((P5J.At.N Zp cF).group l) (h.𝔇.Rd l) (4 + oOf l) _
    a.1 b.1 rs' gs (reader_small (𝔇 := h.𝔇) l Lk hLk (4 + oOf l) b.1) hd q tl tlP tl.funs u hq ht
    hfu (fun t e _ => by
      obtain rfl : tl = t := Option.some.inj (ht.symm.trans e)
      exact hfu) (hX tl ht).2 e7 hsz hNa hso hgt hU hnear

/-- **The same at a state that the bare members' steps reach.** CONDITIONAL: as `makes_fold`, with
hr for f. -/
theorem makes_reach (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {W' : Type} {Fr : Frame}
    (Mg : Meaning ProofFile.InstPub W') {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) Zp Bs
      base cF (seatZ Zp Np) (secondAt Zp Np))
    {l : ℕ} (hl : l ≤ 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (z : ProofFile.InstPub) (a b : S × Fr.E.Str)
    (ha : onQ (P5J.At.N Zp cF) Mg linksFull (flatPlacesOf linksFull true) (fun s => (z, s))
      (drawAt l) a)
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (drawAt l) (z, a.1)) (hm : a.1.failed = none)
    (hy : ∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS (ProofFile.k8ParW Zp Bs.G₀ Xl l).toPar).decide a.1 rs gs =
      .ok b.1) :
    formsInA (h.𝔇.Rd l) ((P5J.At.N Zp cF).sent l) ((P5J.At.N Zp cF).group l) (4 + oOf l)
      "K8.equations" b.1 = true := by
  obtain ⟨-, rs, cols, f⟩ := hr.fold
  exact makes_fold h Mg O hl e3 z a b ha f hm hy

/-- **The same at a state that the wrapped steps reach.** CONDITIONAL: as `makes_fold`, with hr for
f. -/
theorem makes_any (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {W' : Type} {Fr : Frame}
    (Mg : Meaning ProofFile.InstPub W') {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) Zp Bs
      base cF (seatZ Zp Np) (secondAt Zp Np))
    {l : ℕ} (hl : l ≤ 24) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (z : ProofFile.InstPub) (a b : S × Fr.E.Str)
    (ha : onQ (P5J.At.N Zp cF) Mg linksFull (flatPlacesOf linksFull true) (fun s => (z, s))
      (drawAt l) a)
    (hr : RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) (drawAt l) ((z, a.1), a.2))
    (hm : a.1.failed = none)
    (hy : ∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS (ProofFile.k8ParW Zp Bs.G₀ Xl l).toPar).decide a.1 rs gs =
      .ok b.1) :
    formsInA (h.𝔇.Rd l) ((P5J.At.N Zp cF).sent l) ((P5J.At.N Zp cF).group l) (4 + oOf l)
      "K8.equations" b.1 = true := by
  obtain ⟨-, rs, cols, f⟩ := rchAt_fold hr
  exact makes_fold h Mg O hl e3 z a b ha f hm hy

end H2K8

#print axioms H2K8.makesOwes_any
#print axioms H2K8.fold_at_draw
#print axioms H2K8.makes_fold
#print axioms H2K8.makes_reach
#print axioms H2K8.makes_any
