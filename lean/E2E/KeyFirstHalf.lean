--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyFirstHalf.lean: THE FRONT HALF OF THE KEY FILE'S FIRST CHAIN IS PASSED, in one theorem: from
the chain's first round to the laying of the lookups' rows: the two sendings, a link for each
lookup, "rng.0.rows". Stated at the library's own chain (`firstChain`, Johnson/Desc/Key/Chain1.lean)
and its fold (`foldBlocks`, Johnson/Desc/Block.lean). General in the chain's public values and in
the number of lookups. Statements and proofs; nothing is evaluated.

What is defined.
  `ownTake xs`, `idxTake xs`: the mask entries that a list of lookups takes off the own message's
    and off the index-mask message's ledger.
  **`LinksHeard one set V i xs rs rs'`**: the premises of E2E/KeyRowsFit.lean's `link_keeps`, link
    by link, along the chain's rounds: for each lookup: every part has a level · the planner makes
    its entries · so many rounds are left and fit their entries · `hearV` accepts them from the
    fresh ledger · `Left` · `Off` of the rows and of the three claims' leads · each block's term has
    V variables.
What is shown.
  **`links_fold`**: under `Mid` in front of the first link and `LinksHeard`: the fold over all links
    accepts, and `Mid` holds behind the last, with all entries taken.
  **`first_half`**: PREMISES: the fold over the two sendings accepts · from a state in which no
    lookup has written anything · both messages have an OOD sample and mask rows, the own one main
    rows · `LinksHeard` · FOUR STATEMENTS ON PUBLIC NUMBERS: V ≤ 63; V is the own message's main
    table's number of bits; each ledger's free entries are what the lookups take and a (b) more.
    CONCLUSION: the fold over the two sendings, all links and "rng.0.rows" accepts; behind it no
    lookup's ledger is open, all lookups have written their claims on keys, the codes are as at the
    start, and THE INDEX-MASK MESSAGE'S LEDGER HAS JUST b ENTRIES LEFT (what the batching behind it
    asks: E2E/KeyLedgers.lean's `pile_count`).
  `fold_append_eq`, `fold_planOk`: where the fold over a list accepts, the fold over that list and
    another goes on from there; the fold reads no sub-protocol's test on the plan. General in the
    state's type.
  **`first_half_chain`**: the same at `(firstChain one D told set N).blocksInOrder`: the fold over the whole
    flat list is the fold over what is left behind "rng.0.rows", from that state.

Limits.
- ALL PREMISES OF THE FILES BENEATH STAY PREMISES: that the two sendings accept; `hearV`'s accept,
  `roundsFit`,
  `Left`, `Off` (in `LinksHeard`); the statements on public numbers, which are shown at no plan.
- No member of `LinksHeard` with a lookup is typed.
- The back half (the ranges' test, the batching of the rows on the table, W's sending, the chain's
  end) is not treated.
- FORM ALONE: that what is written and laid holds of anything is not touched.
- Nothing on completeness as such, on soundness, or on what a view shows.


-/
import E2E.KeyRowsFit
import Johnson.Desc.Key.Chain1

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyLookup
open OnBytes
open OnBytes.Model (Fork)
open VerifiableInference.Desc
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.Key
open OnBytes.Means (tableSize)
open AtPublicFiles.RowsFit (padFirst)

/-! ## 1. The links' premises along the rounds -/

/-- The entries that a list of lookups takes off the own message's ledger. -/
def ownTake : List Lookup → ℕ
  | [] => 0
  | x :: xs => ((faceOfLkp x).slots - 2 * (faceOfLkp x).parts.length) + ownTake xs

/-- The entries that it takes off the index-mask message's ledger: two a part. -/
def idxTake : List Lookup → ℕ
  | [] => 0
  | x :: xs => 2 * (faceOfLkp x).parts.length + idxTake xs

/-- **The premises of `link_keeps`, link by link, along the chain's rounds.** i: the first link's
number. rs: the rounds in front of it. rs': those behind the last. -/
inductive LinksHeard (one : Params.OneTime) (set : Params.Setting) (V : ℕ) :
    ℕ → List Lookup → List Fmt.RoundView → List Fmt.RoundView → Prop
  | nil (i : ℕ) (rs : List Fmt.RoundView) : LinksHeard one set V i [] rs rs
  | cons {i : ℕ} {x : Lookup} {xs : List Lookup} {rs rs' : List Fmt.RoundView} {es : List Fmt.Entry}
      {gV : HeardV} {G G₂ : Fork} {cl : List PlaneClaim}
      (hv : ∀ v ∈ (faceOfLkp x).parts, 1 ≤ v)
      (hes : (lookupPlace set i x).entries = some es) (hlen : es.length ≤ rs.length)
      (hfit : roundsFit (es.map fun e => { entry := e }) (rs.take es.length) = true)
      (hh : hearV (faceOfLkp x) (({} : Fork).slots (faceOfLkp x).slots)
        ((rs.take es.length).map noDigest) = some (gV, G))
      (hL : Left (lookupPlace set i x) (toHeardG gV) G cl G₂)
      (hO : ∀ c ∈ (toHeardG gV).rows.toList, Off (faceOfLkp x) 0 c)
      (hO' : ∀ c ∈ cl, Off (faceOfLkp x) 0 c.lead)
      (hT : ∀ bl ∈ blocksOf one.ranges one.codes i, (termOf one.ranges one.codes i
        (canon ((faceOfLkp x).mu + (faceOfLkp x).d)) bl).pairs.length = V)
      (tail : LinksHeard one set V (i + 1) xs (rs.drop es.length) rs') :
      LinksHeard one set V i (x :: xs) rs rs'

/-- **All links are passed.** -/
theorem links_fold (one : Params.OneTime) (set : Params.Setting) (ft : ℕ) {V : ℕ} (hV : V ≤ 63)
    {cols : List OpenedColumn} {B : ℕ} {sm si : OracleShape} {cs : Codes} :
    ∀ {i : ℕ} {xs : List Lookup} {rs rs' : List Fmt.RoundView}, LinksHeard one set V i xs rs rs' →
    ∀ {s : FirstState} {a b k₁ k₂ : ℕ},
      Mid one cs s i (ownTake xs + a) (idxTake xs + b) k₁ k₂ B V sm si →
      ∃ s', foldBlocks ft (((xs.zipIdx i).map fun x => lookupLink one set x.2 x.1).flatMap
          Link.blocksInOrder) s rs cols = .ok (s', rs', cols) ∧
        Mid one cs s' (i + xs.length) a b (k₁ + ownTake xs) (k₂ + idxTake xs) B V sm si := by
  intro i xs rs rs' h
  induction h with
  | nil i rs =>
    intro s a b k₁ k₂ hM
    refine ⟨s, rfl, ?_⟩
    simpa [ownTake, idxTake] using hM
  | @cons i x xs rs rs' es gV G G₂ cl hv hes hlen hfit hh hL hO hO' hT _ ih =>
    intro s a b k₁ k₂ hM
    have hM' : Mid one cs s i
        ((faceOfLkp x).slots - 2 * (faceOfLkp x).parts.length + (ownTake xs + a))
        (2 * (faceOfLkp x).parts.length + (idxTake xs + b)) k₁ k₂ B V sm si := by
      simpa [ownTake, idxTake, Nat.add_assoc] using hM
    obtain ⟨s₁, f1, m1⟩ := link_keeps one set i x ft (cols := cols) hM' hv hes hlen hfit hh hL hO
      hO' hT hV
    obtain ⟨s₂, f2, m2⟩ := ih m1
    refine ⟨s₂, ?_, ?_⟩
    · rw [List.zipIdx_cons, List.map_cons, List.flatMap_cons]
      exact (foldBlocks_append_ok _ _ _ _ _ _).2 ⟨s₁, _, _, f1, f2⟩
    · have e1 : i + (x :: xs).length = i + 1 + xs.length := by
        rw [List.length_cons]
        omega
      rw [e1]
      simpa [ownTake, idxTake, Nat.add_assoc] using m2

/-! ## 2. From the chain's first round to the laying of the rows -/

/-- **The first chain's front half is passed**: where the two sendings accept, under the links'
premises and four equations of public numbers: the fold over the two sendings, all links and
"rng.0.rows" accepts; it takes the links' rounds and none of their columns; behind it all lookups
have written their claims on keys, no lookup's ledger is open, and the index-mask message's ledger
of mask entries has just b entries left. -/
theorem first_half (one : Params.OneTime) (set : Params.Setting) (ft : ℕ) {g₁ g₂ : List (List ℕ)}
    {s s₂ : FirstState} {rs rs₂ rs₃ : List Fmt.RoundView} {cols cols₂ : List OpenedColumn} {V a b : ℕ}
    (hfront : foldBlocks ft [sendIndexMasks (Cl := Claim) one pieces g₁,
      sendOwnMessage one pieces g₂] s rs cols = .ok (s₂, rs₂, cols₂))
    (i0 : one.indexMasks.shape.answers ≠ 0) (im : 0 < one.indexMasks.shape.maskRows)
    (m0 : one.ranges.message.shape.answers ≠ 0) (mm : 0 < one.ranges.message.shape.maskRows)
    (hf : s.base.fork = none) (hk : s.base.keys = []) (hr : s.base.rows = [])
    (hH : LinksHeard one set V 0 (lookupsOf one) rs₂ rs₃) (hV : V ≤ 63)
    (hown : freeOf s.d.st.codes one.ranges.message.shape = ownTake (lookupsOf one) + a)
    (hidx : freeOf s.d.st.codes one.indexMasks.shape = idxTake (lookupsOf one) + b)
    (hmain : 0 < one.ranges.message.shape.mainRows)
    (hbits : ceilLog2 one.ranges.message.shape.mainRows +
      (s.d.st.codes.base.getD one.ranges.message.shape.code default).logEll = V) :
    ∃ s₄, foldBlocks ft ([sendIndexMasks one pieces g₁, sendOwnMessage one pieces g₂] ++
        ((lookupsOf one).zipIdx.map fun x => lookupLink one set x.2 x.1).flatMap Link.blocksInOrder ++
        [layRows one]) s rs cols = .ok (s₄, rs₃, cols₂) ∧
      s₄.base.fork = none ∧ s₄.base.keys.length = (lookupsOf one).length ∧
      s₄.d.st.codes = s.d.st.codes ∧ LeftIs s₄.d s₄.idx b one.indexMasks.shape := by
  obtain ⟨-, s₁, c₁, st1, r1⟩ := foldBlocks_cons_ok.1 hfront
  obtain ⟨-, s₂', c₂, st2, r2⟩ := foldBlocks_cons_ok.1 r1
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj r2)
  have e₁ := (Block.step_ok.1 st1).2.2.1
  have e₂ := (Block.step_ok.1 st2).2.2.1
  have hM := mid_of_front V e₁ e₂ i0 im m0 mm hf hk hr
  rw [hown, hidx] at hM
  obtain ⟨s₃, f3, m3⟩ := links_fold one set ft hV (cols := cols₂) hH hM
  rw [Nat.zero_add] at m3
  obtain ⟨d, hd, hsame⟩ := layRows_accepts one [] [] m3 hmain hbits
  refine ⟨{ s₃ with d := d }, ?_, m3.fork, m3.keys, (hsame 0).1.trans m3.codes,
    m3.idx.same (hsame _)⟩
  rw [List.append_assoc]
  refine (foldBlocks_append_ok _ _ _ _ _ _).2 ⟨_, _, _, hfront, ?_⟩
  refine (foldBlocks_append_ok _ _ _ _ _ _).2 ⟨_, _, _, f3, ?_⟩
  exact fold_quiet rfl ft hd rfl

/-! ## 3. In the library's own chain -/

section
variable {S Cl : Type}

/-- Where the fold over a list accepts, the fold over that list and another goes on from there. -/
theorem fold_append_eq (ft : ℕ) (l₂ : List (Block S Cl)) : ∀ (l₁ : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn),
    foldBlocks ft l₁ s rs cols = .ok r →
    foldBlocks ft (l₁ ++ l₂) s rs cols = foldBlocks ft l₂ r.1 r.2.1 r.2.2
  | [], s, rs, cols, r, h => by
    obtain rfl := Except.ok.inj h
    rfl
  | b :: l₁, s, rs, cols, r, h => by
    obtain ⟨hl, s', k, hs, hr⟩ := foldBlocks_cons_ok.1 h
    rw [List.cons_append]
    simp only [foldBlocks, List.splitAt_eq]
    rw [if_neg (not_not.2 hl), hs]
    exact fold_append_eq ft l₂ l₁ s' _ _ r hr

/-- The fold reads nothing of a sub-protocol's test on the plan. -/
theorem fold_planOk (ft : ℕ) (p : Block S Cl → Bool) : ∀ (l : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn),
    foldBlocks ft (l.map fun b => { b with planOk := p b }) s rs cols = foldBlocks ft l s rs cols
  | [], _, _, _ => rfl
  | b :: l, s, rs, cols => by
    rw [List.map_cons]
    simp only [foldBlocks, List.splitAt_eq]
    have hstep : Block.step ft { b with planOk := p b } s (rs.take b.rounds.length) cols =
        Block.step ft b s (rs.take b.rounds.length) cols := rfl
    rw [hstep]
    split
    · rfl
    · cases Block.step ft b s (rs.take b.rounds.length) cols with
      | error e => rfl
      | ok y => exact fold_planOk ft p l _ _ _

end

/-- **The same in the library's own first chain** (`firstChain`, Johnson/Desc/Key/Chain1.lean): the
fold over the chain's flat list goes on, behind "rng.0.rows", over what is left of the list (the
ranges' test, the batching of the rows on the table, W's sending, the chain's end), from a state s₄
of which the same is said. -/
theorem first_half_chain (one : Params.OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
    (set : Params.Setting) (N : H2U.PlaceNums) (ft : ℕ)
    {s s₂ : FirstState} {rs rs₂ rs₃ : List Fmt.RoundView} {cols cols₂ : List OpenedColumn} {V a b : ℕ}
    (hfront : foldBlocks ft ((firstChain one D told set N).first ::
      (firstChain one D told set N).front) s rs cols = .ok (s₂, rs₂, cols₂))
    (i0 : one.indexMasks.shape.answers ≠ 0) (im : 0 < one.indexMasks.shape.maskRows)
    (m0 : one.ranges.message.shape.answers ≠ 0) (mm : 0 < one.ranges.message.shape.maskRows)
    (hf : s.base.fork = none) (hk : s.base.keys = []) (hr : s.base.rows = [])
    (hH : LinksHeard one set V 0 (lookupsOf one) rs₂ rs₃) (hV : V ≤ 63)
    (hown : freeOf s.d.st.codes one.ranges.message.shape = ownTake (lookupsOf one) + a)
    (hidx : freeOf s.d.st.codes one.indexMasks.shape = idxTake (lookupsOf one) + b)
    (hmain : 0 < one.ranges.message.shape.mainRows)
    (hbits : ceilLog2 one.ranges.message.shape.mainRows +
      (s.d.st.codes.base.getD one.ranges.message.shape.code default).logEll = V) :
    ∃ s₄, foldBlocks ft (firstChain one D told set N).blocksInOrder s rs cols =
        foldBlocks ft
          (((firstChain one D told set N).back.drop 1).map
              (fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }) ++
            [{ (firstChain one D told set N).last with
                planOk := (firstChain one D told set N).last.planOk &&
                  (firstChain one D told set N).last.hasNoClaimsAndNothingAfter }]) s₄ rs₃ cols₂ ∧
      s₄.base.fork = none ∧ s₄.base.keys.length = (lookupsOf one).length ∧
      s₄.d.st.codes = s.d.st.codes ∧ LeftIs s₄.d s₄.idx b one.indexMasks.shape := by
  obtain ⟨s₄, h4, q1, q2, q3, q4⟩ := first_half one set ft hfront i0 im m0 mm hf hk hr hH hV hown
    hidx hmain hbits
  obtain ⟨tail, hb, ht⟩ : ∃ tail, (firstChain one D told set N).back = layRows one :: tail ∧
      (firstChain one D told set N).back.drop 1 = tail := ⟨_, rfl, rfl⟩
  let p : Block FirstState Claim → Bool := fun b => b.planOk && b.hasNoClaimsAndNothingAfter
  let bareF : Block FirstState Claim → Block FirstState Claim := fun b => { b with planOk := p b }
  have hflat : (firstChain one D told set N).blocksInOrder =
      (((firstChain one D told set N).first :: (firstChain one D told set N).front).map bareF ++
        (firstChain one D told set N).links.flatMap Link.blocksInOrder ++ [layRows one].map bareF) ++
        (tail.map bareF ++ [bareF (firstChain one D told set N).last]) := by
    show bareF _ :: ((firstChain one D told set N).front.map bareF ++ _ ++
      (firstChain one D told set N).back.map bareF ++ [bareF _]) = _
    rw [hb]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc]
  -- the fold over the part in front reads no test on the plan
  obtain ⟨sA, rA, cA, fA, fB⟩ := (foldBlocks_append_ok _ _ _ _ _ _).1 h4
  obtain ⟨sB, rB, cB, fA1, fA2⟩ := (foldBlocks_append_ok _ _ _ _ _ _).1 fA
  have g4 : foldBlocks ft
      (((firstChain one D told set N).first :: (firstChain one D told set N).front).map bareF ++
        (firstChain one D told set N).links.flatMap Link.blocksInOrder ++ [layRows one].map bareF)
      s rs cols = .ok (s₄, rs₃, cols₂) := by
    refine (foldBlocks_append_ok _ _ _ _ _ _).2 ⟨sA, rA, cA, ?_, ?_⟩
    · refine (foldBlocks_append_ok _ _ _ _ _ _).2 ⟨sB, rB, cB, ?_, fA2⟩
      rw [fold_planOk ft p]
      exact fA1
    · rw [fold_planOk ft p]
      exact fB
  refine ⟨s₄, ?_, q1, q2, q3, q4⟩
  rw [ht, hflat]
  exact fold_append_eq ft _ _ s rs cols _ g4

end AtPublicFiles.KeyLookup

#print axioms AtPublicFiles.KeyLookup.links_fold
#print axioms AtPublicFiles.KeyLookup.first_half
#print axioms AtPublicFiles.KeyLookup.fold_append_eq
#print axioms AtPublicFiles.KeyLookup.fold_planOk
#print axioms AtPublicFiles.KeyLookup.first_half_chain
