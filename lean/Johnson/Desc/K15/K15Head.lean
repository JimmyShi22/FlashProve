-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K15/K15Head.lean: THE JOIN OF K15's ROW OUT WITH K12's ROW IN, at the claim: the
records' road, stretch (b).
WHAT IS HERE.
  batRan_at        the library's record of facts on a batching (BatRan, OnBytes/Slice/BlkBat.lean)
  holds at carried records laid as data (ctxOf), OF FOUR FACTS: the
                   group is there · no test has begun on it · its layout · Bat.combine's value.
                   Three of the four are what bat_ok (Johnson/Desc/K12/Law/BatOk.lean)
                   proves of a yes of the batching's plain text; this file imports none of
                   K12's files: its theorems TAKE THESE FACTS AS PREMISES, so that no
                   twin of bat_ok grows and whoever calls lays bat_ok in.
  ran_fresh        the fourth: behind the link's five rounds no test has begun on the link's group:
  out of LinkRanR's closed form.
  LinkClaim        **the statement**
  (at (P, plan, ok), as its caller stands; X, D and LinkRanR are HANDED ON, so that
  d5 is
                   tied to the run and the library's HeadKeepsR can be called at the same record):
                   where (descOf P plan ok).run says yes ON A VIEW WHOSE FIRST FIVE ROUNDS ARE
                   WRITTEN ROUNDS of typed messages and challenges and
                   whose stored columns are the two stored strings': there is the record d5 in front
                   of the test (with the test's and the end's yes behind it), and
                   WHATEVER ROW THE BATCHING COMBINES THERE, READ IN THE FIELD, IS THE LIBRARY's
                   sumStmR OF THE TYPED STATEMENT st4R's ROWS under the powers of the drawn
                   element: the very claim at which hsem of link_chain_joh | fr_link_joh |
                   sr_link_joh asks the chain's Acc.
  linkClaim        its proof: HandsOnRun · batRan_at · the library's head_claimR
  (OnBytes/Slice/BlkHeadRec.lean:117), CALLED AS IT LIES.
PREMISES: head_claimR's own public ones (LinkSizes · LinkFit · BatDraws · the two counts of columns
· 3 n ≤ l), the keys hold the records (KeyHasR, under the two tests
that the run has made), the view's form (five written rounds; the stored columns), and hmask (the
row's first coefficients on the mask table read as 0): ALL LETTERS HERE: paid at
no value in this file. No run of `verify-on-bytes` stands in a statement or a proof. Nothing on
soundness by itself.
-/
import Johnson.Desc.K15.K15Run
import OnBytes.Slice.BlkHeadRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain Run Cb Cb.Ood
open VerifiableInference.Desc (foldBlocks OpenedColumn)

theorem batRan_at (es es' : List Fmt.Entry) (d : St) (rs rs' : List Fmt.RoundView) (cols : List OpenedColumn)
    (g : Nat) (G : Group)
    (L : GroupLayout) (x : E) (row : GroupRow) (hG : d.st.groups[g]? = some G)
        (hf : G.inRun = false)
    (hL : d.st.layout g = some L) (hrow : Bat.combine (begun d.st g G) g ⟨L, runRows d.st G⟩ x =
        some row) :
    BatRan g (ctxOf es d rs cols) (ctxOf es' { d with st := begun d.st g G } rs' cols) G L x row :=
  ⟨hG, hf, hL, hrow, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ran_fresh (S : LinkShape) (a b : TableKey) (c c' : Ctx) (X : LinkRun) (D : LinkDataR)
    (h : LinkRanR S a b c c' X D) (G : Group) (hG : c'.st.groups[X.group]? = some G) : G.inRun =
        false := by
  have hg := linkSt_groupR S c.st D.places { D.row0 with target := D.y0 }
      { D.row1 with target := D.y1 } D.rec0 D.rec1
    D.rows0 D.rows1 D.rE
  rw [← h.st, ← h.group, hG] at hg
  rw [Option.some.inj hg]
  rfl

section
variable (S : Sz) (t₀ lg n : ℕ) (d1 d2 d3 d4 d5 dA : PQ.RD)
  (m1 : (wRound d1).Msg) (c1 : (wRound d1).Chal) (m2 : (wRound d2).Msg)
  (c2 : (wRound d2).Chal) (m3 : (wRound d3).Msg) (c3 : (wRound d3).Chal)
  (m4 : (wRound d4).Msg) (c4 : (wRound d4).Chal) (m5 : (wRound d5).Msg) (c5 : (wRound d5).Chal)

/-- **The join at the claim**: the statement. See the head. -/
def LinkClaim : Prop :=
  ∀ (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool) (es : List Fmt.Entry)
      (x : TableKey × TableKey) (v : Fmt.View)
    (tail : List Fmt.RoundView),
    P.set.samples = 1 → (descOf P plan ok).run x v = true →
    LinkSizes S P.S P.codes →
    LinkFit S P.S (P.S.side false 1) (P.S.side true 1) → BatDraws S d1 d2 d3 d4 d5 dA →
    (P.S.side false 1).columns = P.S.columnsFirst →
    (P.S.side true 1).columns = P.S.columnsFurther → 3 * n ≤ S.P.T.l →
    ∀ (r : (S.lkR (recZ S.P.T.l lg n)).X0),
    (x.1.fits P.S.table = true → (x.1.seeds.all fun s => !isZeroE s.beta) = true →
      KeyHasR S.P.v lg n (P.S.side false 1).index x.1 r.1) →
    (x.2.fits P.S.table = true → (x.2.seeds.all fun s => !isZeroE s.beta) = true →
      KeyHasR S.P.v lg n (P.S.side true 1).index x.2 r.2) →
    ∀ (y : (S.lkR (recZ S.P.T.l lg n)).E0.Str),
    v.rounds = rvW d1 m1 c1 :: rvW d2 m2 c2 :: rvW d3 m3 c3 :: rvW d4 m4 c4 :: rvW d5 m5 c5 :: tail
        →
    (∀ o ∈ v.opened,
      (o.1 = Fmt.storedKey 0 → storedOf S.P.T.a y 0 o.2.1 = some o.2.2) ∧
      (o.1 = Fmt.storedKey 1 → storedOf S.P.T.a y 1 o.2.1 = some o.2.2)) →
    ∃ X D d5' cols' d', LinkRanR P.S x.1 x.2 (ctxOf es (first P.codes x) v.rounds v.opened)
        (ctxOf (es.drop 5) d5' tail cols') X D ∧
      X.group = d5'.loc.g ∧ X.mask = d5'.loc.firstMask ∧
      VerifiableInference.Desc.viewWordsBelowPrime v = true ∧ (descOf P plan ok).planOk = true ∧
      foldBlocks 0 (tailOf P) d5' tail cols' = .ok (d', [], []) ∧
      ∀ (G0 : Group) (L : GroupLayout) (θ : E) (row : GroupRow),
        d5'.st.groups[d5'.loc.g]? = some G0 → d5'.st.layout d5'.loc.g = some L →
        Bat.combine (begun d5'.st d5'.loc.g G0) d5'.loc.g ⟨L, runRows d5'.st G0⟩ θ = some row →
        (∀ i, i < S.P.Z.l → readV row.d i = 0) →
        stmG (S.sg t₀) row =
          sumStmR (RowNo.port S (recZ S.P.T.l lg n) n fun σ => Equiv.refl (Fin n) σ) t₀
            (rowsXR S (recZ S.P.T.l lg n) n (Equiv.refl (Fin n)) t₀
              (st4R S (recZ S.P.T.l lg n) r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).1
            (rowsXR S (recZ S.P.T.l lg n) n (Equiv.refl (Fin n)) t₀
              (st4R S (recZ S.P.T.l lg n) r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5).1).2 (readE θ)

theorem linkClaim : LinkClaim S t₀ lg n d1 d2 d3 d4 d5 dA m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 := by
  intro P plan ok es x v tail hs hrun hS hF hd hn0 hn1 hpads r hK0 hK1 y hv hop
  obtain ⟨X, D, d5', rest, cols', d', hR, hg, hmk, hfold, hi0, hi1, hvw, hpl⟩ := handsOnRun P plan
      ok es x v hs hrun
  have hp := hR.pending
  change v.rounds = _ at hp
  rw [hv] at hp
  simp only [List.cons.injEq] at hp
  obtain ⟨a1, a2, a3, a4, a5, arest⟩ := hp
  have hl := hR.left
  change rest = _ at hl
  have htail : tail = rest := arest.trans hl.symm
  subst htail
  refine ⟨X, D, d5', cols', d', hR, hg, hmk, hvw, hpl, hfold, ?_⟩
  intro G0 L θ row hG hL hrow hmask
  rw [← hg] at hG hL hrow
  have hfr := ran_fresh _ _ _ _ _ _ _ hR G0 hG
  have hB := batRan_at (es.drop 5) (es.drop 6) d5' tail (tail.drop 1) cols' X.group G0 L θ row hG
      hfr hL hrow
  exact head_claimR S t₀ lg n P.S x.1 x.2 d1 d2 d3 d4 d5 dA m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 _ _ _ X D
      G0 L θ row hS hF hd
    hn0 hn1 hi0 hi1 hpads r hK0 hK1 y hR hB a1.symm a2.symm a3.symm a4.symm a5.symm hop hmask

end

end Desc.K15

#print axioms Desc.K15.linkClaim
#print axioms Desc.K15.batRan_at
#print axioms Desc.K15.ran_fresh
