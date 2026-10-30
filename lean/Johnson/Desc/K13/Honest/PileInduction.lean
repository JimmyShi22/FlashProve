-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/PileInduction.lean: THE INDUCTION: `PileIs` AT THE FILLER `pileBySites` FROM
`ClaimsIs` AT ALL SITES (PileDefs.lean of this folder), UNDER NAMED PREMISES ON THE CHAIN's
SUB-PROTOCOLS. Definitions: premises' forms; and one conditional statement with its proof and
lemmas. General in the chain's list: no kind is named, in the statements or beneath the imports of
this folder, and nothing of the frame for the honest side.

Words. The pile: the verifier's list of pending rows on the weight table (`out.pending`). A site: a
segment whose merge of the claims on the weights leaves a row. The filler: the function
`pileBySites`, which makes the pile's rows of the instance and the challenges. The border k: between
the sub-protocols number k − 1 and k.
The walk, AS THE PREMISES HAVE IT (none of these sentences is shown of any chain here). rd: a
letter: how the pile is read off a state along the walk. At the start rd is empty; a site's merge
leaves something in the state (`ClaimsIs` says what, in terms of the instance and what the rounds
sampled); it stays there until a later sub-protocol makes a row of it by the verifier's own function
and lays that row at rd's end; no other sub-protocol writes rd; at the border rd is the state's own
field `out.pending`. THEN at the border the pile's rows are, in their weights and column points,
what the filler makes of the instance and the challenges, site by site, in the order of the laying.
Why rd is a letter: the library's laws on who writes the pile speak of `S.rows`
(Johnson/Desc/First/State.lean: the pile, but behind K13's batching the one row off the claim), not
of the field.
The rule that carries it: `foldStepsAt` (FoldCut.lean): the fold's own equation is given with each
step, so `ClaimsIs`, which is asked of the fold, is spent at the merging sub-protocol's step; AND
EVERY PREMISE ON A SUB-PROTOCOL IS ASKED AT THE FOLD's OWN STATES ALONE (`FoldReaches`). From the
step to the decision: the library's `stepOk` (Johnson/Desc/Sound/FoldHeardProofs.lean). `ClaimsIs`
asks "failed = none" and, at the head, the reply, right behind the merge. The first is a premise
there (`mark`). `PileIs` gives the reply at the border alone: so the sentence is carried UNDER the
reply, and the premise `reply` takes it back over a step.
Main names:
  `PileSite`: a site with where it stands on the chain: its public numbers; j: the number of the
    sub-protocol that merges; c: the number of the one that lays the row; how what the merge left is
    read off the state; whether it is the head's.
  `FoldReaches bs start k x rs cols s c`: s is the state that the verifier's own fold over the first
    k sub-protocols returns.
  `PileWalk bs start b n lay Sh ss claims asked rd`: **THE PREMISES, twelve, each under a name**:
    `inList`: the border lies within the list · `sites`: `ClaimsIs` at every site · `order`: the
    sites stand in the order of their laying · `inside`: j < c < b · `reach`: the filler may read a
    site's 2 + lk challenges · `stays`: between j and c every decision leaves what the merge left ·
    `clears`: number c lays the verifier's own row of what is left (the library's `rowBy`:
    Johnson/Top/H0/Walk/FrameRow.lean) at rd's end · `quiet`: every other decision in front of the
    border leaves rd · `mark`: A MERGING SUB-PROTOCOL RETURNS ONLY STATES WITH failed = none: asked
    at the sites' numbers j alone · `reply`: behind the head's merge every decision leaves the reply
    · `empty`: rd is empty at the start · `atEnd`: at the border, where failed = none, rd is
    `out.pending`.
  `pileIs_of_claimsIs`: **`PileWalk` gives `PileIs` at `pileBySites lay Sh (ss.map (·.m)) claims`.**
    It speaks at a border in front of which ALL sites' rows are laid.
  `pileWalk_succ`: one step. `SiteOpen`, `WalkCond`, `WalkInv`: the sentence that is carried.
    `pileRowAt_of`: the filler's row at a site has the verifier's row's weights and column point (by
    `rowReadsOf_row`, PileRow.lean). `heardCut_take`, `heardCut_drop_take`, `mapM_snoc`,
    `filter_succ_of_not`, `filter_succ_of_mem`: lists.
WHO CAN MEET WHICH AT THE PROOF FILE's OWN CHAIN, by laws of the library (named by a reader;
none is called here): `mark`: `ProofFile.Law.flat_no_mark`, `descPure_no_mark`
(Johnson/Desc/ProofFile/Law/MarkGuard.lean): every sub-protocol of the chain but the first and each
segment's one behind the batching returns only states with failed = none · `reply`:
`chainBy_leaves`, `sameReply_eq`, `chainBy_count` (Johnson/Desc/Plain/Leaves/PureHears.lean) ·
`empty`: `startS_facts` (Johnson/Desc/AtSeats/StatementSeat.lean) · `clears`, `quiet`, at rd :=
`S.rows`: Johnson/Desc/ProofFile/Honest/K13/PileAtFlat.lean, over `IM.flat_cases`, `IM.frames_arms`,
`clearWith_eq`, `lot_pile` · `stays`: in part: Johnson/Desc/First/Link/Law/OwnStay.lean (`SameOwn`
and its keepers; its `own_from_k4` is said of states that are reached, of no named rounds).
Kin in the library. Of the rule: `LPFK9.fold_ix` (Johnson/LPFK9R/PileByPlace.lean: a sentence that
may read the border's number, carried by decisions, without the fold's equation). Of `mapM_snoc`:
`mapM_append_some` (Johnson/Road/FormsKeysFold.lean, Johnson/Desc/K12/Law/WrittenOfG.lean): the
other direction.

What is not claimed. THAT `PileWalk` HOLDS AT ANY CHAIN WITH A SITE: no member is shown. Any of its
twelve premises at the proof file's own chain; the list of sites there. Anything at a border in
front of which some site's row is not yet laid. It is none of the library's goals. Nothing on
soundness, completeness or hiding.

-/
import Johnson.Desc.K13.Honest.PileRow
import Johnson.Desc.K13.Honest.FoldCut
import Johnson.Top.H0.Walk.FrameRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc (Block OpenedColumn foldBlocks stepOk)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Pend (pendingRowO)
open Johnson.Desc.First.Walk.Law (rowBy rowBy_some)

variable {Xi Cl : Type}

/-! ## Small lemmas on lists -/

/-- `mapM` into `Option` over a list with one more behind it. -/
theorem mapM_snoc {α β : Type} (f : α → Option β) {l : List α} {r : List β} {a : α} {y : β}
    (h : l.mapM f = some r) (ha : f a = some y) : (l ++ [a]).mapM f = some (r ++ [y]) := by
  rw [List.mapM_append, h]
  simp [ha]

/-- The first a of the challenges heard are those of the chain's first a rounds. -/
theorem heardCut_take (rs : List Fmt.RoundView) (tl : List Fmt.Drawn) {n a : Nat} (h1 : a ≤ n)
    (h2 : a ≤ rs.length) :
    ((rs.take n).map (·.drawn) ++ tl).take a = (rs.take a).map (·.drawn) := by
  rw [List.take_append_of_le_length (by simp only [List.length_map, List.length_take]; omega),
    ← List.map_take, List.take_take, Nat.min_eq_left h1]

/-- The m challenges heard from number a on are those of the chain's m rounds from number a on. -/
theorem heardCut_drop_take (rs : List Fmt.RoundView) (tl : List Fmt.Drawn) {n a m : Nat}
    (h1 : a + m ≤ n) (h2 : a + m ≤ rs.length) :
    (((rs.take n).map (·.drawn) ++ tl).drop a).take m = ((rs.drop a).take m).map (·.drawn) := by
  rw [List.drop_append_of_le_length (by simp only [List.length_map, List.length_take]; omega),
    List.take_append_of_le_length
      (by simp only [List.length_drop, List.length_map, List.length_take]; omega),
    ← List.map_drop, ← List.map_take, List.drop_take, List.take_take,
    Nat.min_eq_left (by omega)]

/-! ## A site's row -/

/-- Where the parameter, `mergeDraws` and the verifier's own maker of a row return, the filler's row
at the site has the verifier's row's weights and column point. -/
theorem pileRowAt_of {lay : WsLay} {Sh : LinShape} {claims : SiteClaims Xi} {x : Xi}
    {hd : List Fmt.Drawn} {m : MergeSite} {cl : Array WsClaim} {sg : E} {w : WsForkOut}
    {r : TensorRow} {im : ℕ} {os os' : Array OnBytes.Oracle}
    (h1 : claims m.link x (hd.take m.sigmaAt) = some cl)
    (h2 : mergeDraws lay.lk ((hd.drop m.sigmaAt).take (2 + lay.lk)) = some (sg, w.rm))
    (h3 : w.recs = mergeRecs lay cl sg w.rm)
    (h4 : pendingRowO lay im w m.ncl Sh os = .ok (r, os')) :
    ∃ row, pileRowAt lay Sh claims x hd m = some row ∧ (row.g, row.psi) = (r.g, r.psi) := by
  have q := rowReadsOf_row h4
  rw [h3] at q
  refine ⟨{ g := r.g, psi := r.psi, masks := [], target := zeroE }, ?_, rfl⟩
  unfold pileRowAt
  rw [h1, h2]
  show ((rowReadsOf lay Sh m.ncl (mergeRecs lay cl sg w.rm) w.rm).bind fun q =>
    some ({ g := q.1, psi := q.2, masks := [], target := zeroE } : TensorRow)) = _
  rw [q]
  rfl

/-! ## The sites on the chain -/

/-- **A site, with where it stands on the chain.** -/
structure PileSite where
  /-- its public numbers -/
  m : MergeSite
  /-- the number of the sub-protocol that merges -/
  j : Nat
  /-- the number of the sub-protocol that lays the segment's row on the pile -/
  c : Nat
  /-- how what the merge left is read off the state -/
  left : S → Option WsForkOut
  /-- the site is the head's -/
  head : Bool

/-- Where no site's row is laid by number k: the sites whose rows are laid in front of the border
k + 1 are those in front of k. -/
theorem filter_succ_of_not {ss : List PileSite} {k : Nat} (h : ∀ σ ∈ ss, σ.c ≠ k) :
    (ss.filter fun σ => σ.c < k + 1) = ss.filter fun σ => σ.c < k :=
  List.filter_congr fun σ hσ => by
    have := h σ hσ
    simp only [decide_eq_decide]
    omega

/-- Where the sites stand in the order of their laying: those whose rows are laid in front of the
border behind a site's laying are those in front of it, then that site. -/
theorem filter_succ_of_mem : ∀ {ss : List PileSite}, ss.Pairwise (fun a b => a.c < b.c) →
    ∀ {σ : PileSite}, σ ∈ ss →
    (ss.filter fun τ => τ.c < σ.c + 1) = (ss.filter fun τ => τ.c < σ.c) ++ [σ]
  | [], _, _, hσ => by cases hσ
  | a :: l, ho, σ, hσ => by
    obtain ⟨ha, hl⟩ := List.pairwise_cons.1 ho
    rcases List.mem_cons.1 hσ with e | hσ'
    · subst e
      have e1 : (l.filter fun τ => τ.c < σ.c + 1) = [] :=
        List.filter_eq_nil_iff.2 fun τ hτ => by
          have := ha τ hτ
          simp only [decide_eq_true_eq]
          omega
      have e2 : (l.filter fun τ => τ.c < σ.c) = [] :=
        List.filter_eq_nil_iff.2 fun τ hτ => by
          have := ha τ hτ
          simp only [decide_eq_true_eq]
          omega
      rw [List.filter_cons_of_pos (by simp), List.filter_cons_of_neg (by simp), e1, e2]
      rfl
    · have hlt := ha σ hσ'
      rw [List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; omega),
        List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; omega),
        filter_succ_of_mem hl hσ']
      rfl

/-- s is the state that the verifier's own fold over the first k sub-protocols returns, at the
instance x, the rounds rs and the columns cols; c: the columns that it leaves. -/
def FoldReaches (bs : List (Block S Cl)) (start : Xi → S) (k : Nat) (x : Xi) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (s : S) (c : List OpenedColumn) : Prop :=
  foldBlocks 0 (bs.take k) (start x) rs cols = .ok (s, rs.drop (roundsAhead bs k), c)

/-- **THE PREMISES.** bs, start, b, n, asked: as in `PileIs`. ss: the sites. rd: how the pile is
read off a state along the walk. WHAT IS ASKED OF A SUB-PROTOCOL IS ASKED AT THE FOLD's OWN STATES
ALONE. -/
structure PileWalk (bs : List (Block S Cl)) (start : Xi → S) (b n : Nat) (lay : WsLay)
    (Sh : LinShape) (ss : List PileSite) (claims : SiteClaims Xi) (asked : Xi → E)
    (rd : S → List TensorRow) : Prop where
  /-- the border lies within the list -/
  inList : b ≤ bs.length
  /-- `ClaimsIs` at every site -/
  sites : ∀ σ ∈ ss, ClaimsIs bs start σ.j σ.m lay σ.left claims asked σ.head
  /-- the sites stand in the order in which their rows are laid -/
  order : ss.Pairwise fun a b => a.c < b.c
  /-- a site's row is laid behind its merge, in front of the border -/
  inside : ∀ σ ∈ ss, σ.j < σ.c ∧ σ.c < b
  /-- the filler may read a site's 2 + lk challenges -/
  reach : ∀ σ ∈ ss, σ.m.sigmaAt + (2 + lay.lk) ≤ n
  /-- between the merge and the laying, what the merge left stays -/
  stays : ∀ σ ∈ ss, ∀ k blk, σ.j < k → k < σ.c → bs[k]? = some blk →
    ∀ x rs cols s c, FoldReaches bs start k x rs cols s c →
    ∀ R gs t, blk.decide s R gs = .ok t → σ.left t = σ.left s
  /-- the laying: the verifier's own row of what is left, at the pile's end -/
  clears : ∀ σ ∈ ss, ∀ blk, bs[σ.c]? = some blk →
    ∀ x rs cols s c, FoldReaches bs start σ.c x rs cols s c →
    ∀ R gs t, blk.decide s R gs = .ok t →
    ∃ r, rowBy σ.left lay σ.m.ncl Sh s = some r ∧ rd t = rd s ++ [r]
  /-- every other sub-protocol in front of the border leaves the pile -/
  quiet : ∀ k blk, k < b → (∀ σ ∈ ss, σ.c ≠ k) → bs[k]? = some blk →
    ∀ x rs cols s c, FoldReaches bs start k x rs cols s c →
    ∀ R gs t, blk.decide s R gs = .ok t → rd t = rd s
  /-- a merging sub-protocol returns only states with failed = none -/
  mark : ∀ σ ∈ ss, ∀ blk, bs[σ.j]? = some blk →
    ∀ x rs cols s c, FoldReaches bs start σ.j x rs cols s c →
    ∀ R gs t, blk.decide s R gs = .ok t → t.failed = none
  /-- behind the head's merge the reply stays -/
  reply : ∀ σ ∈ ss, σ.head = true → ∀ k blk, σ.j < k → k < b → bs[k]? = some blk →
    ∀ x rs cols s c, FoldReaches bs start k x rs cols s c →
    ∀ R gs t, blk.decide s R gs = .ok t → t.out.reply = s.out.reply
  /-- the pile is empty at the start -/
  empty : ∀ x, rd (start x) = []
  /-- at the border the reading is the state's own field -/
  atEnd : ∀ x rs cols s r c, foldBlocks 0 (bs.take b) (start x) rs cols = .ok (s, r, c) →
    s.failed = none → rd s = s.out.pending

/-- Of a site whose merge has run and whose row is not yet laid, at a state s between the two: what
`ClaimsIs` says behind the merge, carried. -/
def SiteOpen (lay : WsLay) (claims : SiteClaims Xi) (x : Xi) (rs : List Fmt.RoundView) (σ : PileSite)
    (s : S) : Prop :=
  ∃ w cl sg, σ.left s = some w ∧
    claims σ.m.link x ((rs.take σ.m.sigmaAt).map (·.drawn)) = some cl ∧
    mergeDraws lay.lk (((rs.drop σ.m.sigmaAt).take (2 + lay.lk)).map (·.drawn)) =
      some (sg, w.rm) ∧
    w.recs = mergeRecs lay cl sg w.rm

/-- Under which the sentence is carried. k: the border. s: the fold's state there. Behind the head's
merge s holds the reply asked. -/
def WalkCond (ss : List PileSite) (asked : Xi → E) (x : Xi) (k : Nat) (s : S) : Prop :=
  ∀ σ ∈ ss, σ.head = true → σ.j < k → s.out.reply = some (asked x)

/-- The sentence that is carried from border to border. k: the border. s: the fold's state there.
The filler's rows at the sites whose rows are laid in front of k all return, and agree with rd s in
weights and column points; every site that is merged and not yet laid is `SiteOpen`. -/
def WalkInv (lay : WsLay) (Sh : LinShape) (ss : List PileSite) (claims : SiteClaims Xi)
    (rd : S → List TensorRow) (x : Xi) (rs : List Fmt.RoundView) (hd : List Fmt.Drawn) (k : Nat) (s : S) :
    Prop :=
  (∃ rows, ((ss.filter fun σ => σ.c < k).map (·.m)).mapM (pileRowAt lay Sh claims x hd) =
      some rows ∧
    (rows.map fun q => (q.g, q.psi)) = (rd s).map fun q => (q.g, q.psi)) ∧
  ∀ σ ∈ ss, σ.j < k → k ≤ σ.c → SiteOpen lay claims x rs σ s

/-- **One step**: the sentence goes from the border k to the border k + 1, over the step of number k
on its own slice of the rounds, the fold's own equation in front of it being given. -/
theorem pileWalk_succ {bs : List (Block S Cl)} {start : Xi → S} {b n : Nat} {lay : WsLay}
    {Sh : LinShape} {ss : List PileSite} {claims : SiteClaims Xi} {asked : Xi → E}
    {rd : S → List TensorRow} (H : PileWalk bs start b n lay Sh ss claims asked rd) {x : Xi}
    {rs : List Fmt.RoundView}
    {cols : List OpenedColumn} (tl : List Fmt.Drawn) {k : Nat} {blk : Block S Cl} {s t : S} {c : List OpenedColumn}
    {n' : Nat} (hk : k < b) (hb : bs[k]? = some blk)
    (hfold : foldBlocks 0 (bs.take k) (start x) rs cols =
      .ok (s, rs.drop (roundsAhead bs k), c))
    (hl : ((rs.drop (roundsAhead bs k)).take blk.rounds.length).length = blk.rounds.length)
    (hstep : blk.step 0 s ((rs.drop (roundsAhead bs k)).take blk.rounds.length) c = .ok (t, n'))
    (hI : WalkCond ss asked x k s →
      WalkInv lay Sh ss claims rd x rs ((rs.take n).map (·.drawn) ++ tl) k s) :
    WalkCond ss asked x (k + 1) t →
      WalkInv lay Sh ss claims rd x rs ((rs.take n).map (·.drawn) ++ tl) (k + 1) t := by
  intro hr
  obtain ⟨gs, hdec⟩ := stepOk hstep
  have hC : WalkCond ss asked x k s := fun σ hσ hh hj => by
    have q := hr σ hσ hh (Nat.lt_succ_of_lt hj)
    have e : t.out.reply = s.out.reply :=
      H.reply σ hσ hh k blk hj hk hb x rs cols s c hfold _ _ _ hdec
    rw [← e]
    exact q
  obtain ⟨⟨rows, hm, hrows⟩, hopen⟩ := hI hC
  refine ⟨?_, ?_⟩
  · by_cases hc : ∃ σ ∈ ss, σ.c = k
    · obtain ⟨σ, hσ, rfl⟩ := hc
      obtain ⟨r, hr1, hr2⟩ := H.clears σ hσ blk hb x rs cols s c hfold _ _ _ hdec
      obtain ⟨w', os, hw', hp⟩ := rowBy_some.1 hr1
      obtain ⟨w, cl, sg, hw, h1, h2, h3⟩ := hopen σ hσ (H.inside σ hσ).1 (Nat.le_refl _)
      obtain rfl : w = w' := Option.some.inj (hw.symm.trans hw')
      have hlen : (((rs.drop σ.m.sigmaAt).take (2 + lay.lk)).map (·.drawn)).length =
          2 + lay.lk := by
        have h2' := h2
        unfold mergeDraws at h2'
        split at h2'
        · rename_i h0
          rw [Bool.and_eq_true] at h0
          simpa using h0.1
        · cases h2'
      have hR := H.reach σ hσ
      have hA : σ.m.sigmaAt + (2 + lay.lk) ≤ rs.length := by
        simp only [List.length_map, List.length_take, List.length_drop] at hlen
        omega
      obtain ⟨row, hrow, hq⟩ := pileRowAt_of (Sh := Sh)
        (hd := (rs.take n).map (·.drawn) ++ tl) (m := σ.m)
        (by rw [heardCut_take rs tl (by omega) (by omega)]; exact h1)
        (by rw [heardCut_drop_take rs tl hR hA]; exact h2) h3 hp
      refine ⟨rows ++ [row], ?_, ?_⟩
      · rw [filter_succ_of_mem H.order hσ, List.map_append]
        exact mapM_snoc _ hm hrow
      · rw [hr2, List.map_append, List.map_append, hrows]
        show _ ++ [(row.g, row.psi)] = _ ++ [(r.g, r.psi)]
        rw [hq]
    · have hc' : ∀ σ ∈ ss, σ.c ≠ k := fun σ hσ e => hc ⟨σ, hσ, e⟩
      have e : rd t = rd s := H.quiet k blk hk hc' hb x rs cols s c hfold _ _ _ hdec
      exact ⟨rows, by rw [filter_succ_of_not hc']; exact hm, by rw [e]; exact hrows⟩
  · intro σ hσ hj hkc
    by_cases e : σ.j = k
    · subst e
      have hfold' : foldBlocks 0 (bs.take (σ.j + 1)) (start x) rs cols =
          .ok (t, (rs.drop (roundsAhead bs σ.j)).drop blk.rounds.length, c.drop n') := by
        rw [List.take_add_one, hb]
        exact foldBlocks_snoc 0 blk _ _ _ _ _ _ _ _ _ hfold hl hstep
      have hf : t.failed = none := H.mark σ hσ blk hb x rs cols s c hfold _ _ _ hdec
      obtain ⟨cl, sg, w, h1, h2, h3, h4⟩ := H.sites σ hσ x rs cols t _ _ hfold' hf
        fun hh => hr σ hσ hh (Nat.lt_succ_self _)
      exact ⟨w, cl, sg, h3, h1, h2, h4⟩
    · have hj' : σ.j < k := by omega
      obtain ⟨w, cl, sg, hw, h1, h2, h3⟩ := hopen σ hσ hj' (by omega)
      have e' : σ.left t = σ.left s :=
        H.stays σ hσ k blk hj' (by omega) hb x rs cols s c hfold _ _ _ hdec
      exact ⟨w, cl, sg, by rw [e']; exact hw, h1, h2, h3⟩

/-- **THE INDUCTION: `PileIs` AT THE FILLER, FROM `ClaimsIs` AT ALL SITES.** -/
theorem pileIs_of_claimsIs {bs : List (Block S Cl)} {start : Xi → S} {b n : Nat} {lay : WsLay}
    {Sh : LinShape} {ss : List PileSite} {claims : SiteClaims Xi} {asked : Xi → E}
    {rd : S → List TensorRow} (H : PileWalk bs start b n lay Sh ss claims asked rd) :
    PileIs bs start b n (pileBySites lay Sh (ss.map (·.m)) claims) asked := by
  intro x rs cols s r c hfold hf hreply tl
  have hlen : (bs.take b).length = b := by rw [List.length_take, Nat.min_eq_left H.inList]
  have h0 : (ss.filter fun σ => σ.c < 0) = [] :=
    List.filter_eq_nil_iff.2 fun σ _ => by simp
  have key := foldStepsAt 0 (bs.take b)
    (fun k s => WalkCond ss asked x k s →
      WalkInv lay Sh ss claims rd x rs ((rs.take n).map (·.drawn) ++ tl) k s)
    (start x) rs cols (s, r, c)
    (by
      intro k blk hb' s c t n' hfold' hl hstep hI
      have hk : k < b := by
        have := (List.getElem?_eq_some_iff.1 hb').1
        omega
      have hb : bs[k]? = some blk := by
        rw [List.getElem?_take_of_lt hk] at hb'
        exact hb'
      rw [take_take_le bs (Nat.le_of_lt hk), roundsAhead_take bs (Nat.le_of_lt hk)] at hfold'
      rw [roundsAhead_take bs (Nat.le_of_lt hk)] at hl hstep
      exact pileWalk_succ H tl hk hb hfold' hl hstep hI)
    hfold
    (fun _ => ⟨⟨[], by rw [h0]; rfl, by rw [H.empty x]⟩,
      fun σ _ hj _ => absurd hj (Nat.not_lt_zero _)⟩)
  rw [hlen] at key
  obtain ⟨⟨rows, hm, hrows⟩, _⟩ := key fun _ _ _ _ => hreply
  have hall : (ss.filter fun σ => σ.c < b) = ss :=
    List.filter_eq_self.2 fun σ hσ => by
      simp only [decide_eq_true_eq]
      exact (H.inside σ hσ).2
  rw [hall] at hm
  unfold pileBySites
  rw [hm, ← H.atEnd x rs cols s r c hfold hf]
  exact hrows

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.mapM_snoc
#print axioms VerifiableInference.Desc.K13.Honest.heardCut_take
#print axioms VerifiableInference.Desc.K13.Honest.heardCut_drop_take
#print axioms VerifiableInference.Desc.K13.Honest.pileRowAt_of
#print axioms VerifiableInference.Desc.K13.Honest.filter_succ_of_not
#print axioms VerifiableInference.Desc.K13.Honest.filter_succ_of_mem
#print axioms VerifiableInference.Desc.K13.Honest.pileWalk_succ
#print axioms VerifiableInference.Desc.K13.Honest.pileIs_of_claimsIs
