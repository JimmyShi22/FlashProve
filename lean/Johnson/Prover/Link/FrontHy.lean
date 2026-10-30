-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FrontHy.lean: WHAT THE LINK's FIRST CODE SWITCH READS OF THE FIRST TREE IS THE
LONG SYMBOL OF THE THREE FOLDED CODE WORDS. The twin, at the first stage, of hy_stage
(Johnson/Prover/Link/HyStage.lean). Statement and proof.

  dFirst S    a round's data with a tree of the first tree's depth and a column's width: a tool of
              the proof
  hy_first    Did (a switch that has run) · the public premises of the library's linkReads
              (Johnson/Desc/Link/LinkReads.lean), to its letter, at mem := S.P.mem, f1 := 2 ^ aR ·
              each dealt column is firstColW at its own position, in range · μ ρ φ ψ hold the
              members' rows and tails on their blocks, 0 elsewhere, and the further row ·
              old is the first fold's output
              ⟹ at each drawn position: the code word of (foldMsg, foldTl) shows what was read

Its end is hy_stage's to the letter: the premise hy of claim_behind
(Johnson/Prover/Link/SwitchHolds.lean).
Which reading law. linkReads is ReadTie at the link's group: two members of one shape and one
further message, three parts of ONE tree, at the words wordIn s (col1 S d orc) and
wordFr s (col1 S d orc). Johnson/Desc/K12/Law/FirstRead.lean's firstReads speaks of several members
in several trees, at other words; it is not called here.

Not shown here. That Did and linkReads' premises hold at a run. That a strategy's oracle has
these columns. Nothing on soundness; nothing on what any row is for, or on what any entry discloses
or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FrontCols
import Johnson.Prover.Link.HyStage
import Johnson.Desc.Link.LinkReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb _root_.Run
open H2K.Sw H2K.JointK

/-- A round's data with a tree of the first tree's depth and a column's width. -/
def dFirst (S : Sz) : PQ.RD :=
  ⟨{ name := "" }, .elems, [],
    some { a := S.P.C.a, W := 3 * (S.P.R + (S.P.R + 1)), tree := 0 }, []⟩

variable {ft : ℕ} {cols : List Tw.L9.Col} {old : SingleRows} {T : SwitchTarget} {gp : ℕ}
  {others : Array OracleNotice} {St St' : Statement} {Bk Bk' : TreeBook} {roots : ℕ}
  {out : Switched} {row : GroupRow} {lay : GroupLayout} {theta : E} {D : Taken}

/-- **The premise hy of claim_behind (Johnson/Prover/Link/SwitchHolds.lean), at the first
stage.** -/
theorem hy_first (S : Sz) (t : ℕ) (mN tN : Bool → ℕ → ℕ → GE) (φN ψN : ℕ → GE)
    (hs : (S.sg t).Sized) (cu : IoppStage) (L : GroupLayout) (o0 o1 id n : ℕ)
    (sh fr : OracleShape)
    (h : Did ft cols old T gp others St Bk roots St' Bk' out row lay theta D)
    (hk : cu.k = (S.sg t).h + (S.sg t).g) (hh : cu.h = (S.sg t).h)
    (hst : (Fmt.M2.starts [S.P.mem, S.P.mem]).1 = [some 0, some (2 ^ S.P.aR)])
    (hk1 : 2 ^ S.P.aR + S.P.R ≤ 2 ^ Fmt.M2.kOf [S.P.mem, S.P.mem])
    (hR : sh.mainRows = S.P.R) (h3 : sh.mainDeg = 3) (hz : sh.maskRows = 0)
    (hfm : fr.mainRows = 0) (hfz : 0 < fr.maskRows)
    (hwid : 3 * (S.P.R + S.P.R) + fr.maskRows * 3 = Fmt.M2.widthOf S.P.mems 1)
    (hL : LayAt [o0, o1] #[some 0, some (2 ^ S.P.aR)] #[none, none] L)
    (seat : SeatP St Bk [o0, o1, id] n (S.sg t).C.a [sh, sh, fr])
    (hcols : ∀ c ∈ cols, c.2.1 < 2 ^ S.P.C.a ∧ c.2.2 = firstColW S mN tN φN ψN c.2.1)
    (μ : (S.sg t).cIn.J → GE) (ρ : (S.sg t).cIn.Q → GE) (φ : (S.sg t).cFr.J → GE)
    (ψ : (S.sg t).cFr.Q → GE)
    (hμ : ∀ a i, i < S.P.R → ∀ j, μ (.inl (memRow S t a i, j)) = mN a i j.val)
    (hμz : FreeZero S t μ) (hμm : ∀ j, μ (.inr j) = 0)
    (hρ : ∀ a i, i < S.P.R → ∀ q, ρ (.inl (memRow S t a i, q)) = tN a i q.val)
    (hρz : ∀ a i q, S.P.R ≤ i → i < 2 ^ S.P.aR → ρ (.inl (memRow S t a i, q)) = 0)
    (hρm : ∀ q, ρ (.inr q) = 0)
    (hφ : ∀ b j, φ (b, j) = φN j.val) (hψ : ∀ b q, ψ (b, q) = ψN q.val)
    (S₀ : Statement) (row₀ : GroupRow) (eps claim : E) (gamma : List E)
    (hold : old = foldOutput S₀ (ioppFoldShape cu L) row₀ id eps gamma claim)
    (hkept : row₀.kept = #[]) (hγ : gamma.length = (S.sg t).h + (S.sg t).g)
    (hlog : D.code.logN = (S.sg t).C.a)
    (Qs : Fin (S.sg t).t → (S.sg t).Ps) (hQ : ∀ i, (Qs i).val = D.rC.drawn.poss.getD i.val 0)
    (ht : D.rC.drawn.poss.length = (S.sg t).t) :
    ∀ i α, (S.sg t).cMid.T ((S.sg t).cMid.enc
        (foldMsg (S.sg t) μ φ (readP ((S.sg t).h + (S.sg t).g) gamma))
        (foldTl (S.sg t) ρ ψ (readP ((S.sg t).h + (S.sg t).g) gamma))) (Qs i) α =
      symS (S.sg t) old out.positions D.y (Qs i).val α := by
  intro i α
  have hc : ∀ x, x < 2 ^ S.P.C.a →
      OnBytes.Slice.colW (dFirst S) (orcOf (dFirst S) (firstColW S mN tN φN ψN)) x =
        firstColW S mN tN φN ψN x := fun x hx =>
    colW_orcOf (dFirst S) _ x hx (length_firstColW S mN tN φN ψN x)
  have hRd := _root_.Desc.K15.linkReads ft S (S.sg t) rfl cu L St Bk o0 o1 id n (dFirst S)
    (orcOf (dFirst S) (firstColW S mN tN φN ψN)) cols D.rC.drawn.poss sh fr S.P.mem rfl rfl rfl
    (2 ^ S.P.aR) hst (le_two_pow_clog S.P.R) hk1 hR h3 hz hfm hfz hwid hk hh hL seat
    (fun c hcc => by rw [hc c.2.1 (hcols c hcc).1]; exact (hcols c hcc).2)
  have hx : (Qs i).val ∈ D.rC.drawn.poss := by
    rw [hQ i, List.getD_eq_getElem _ _ (by rw [ht]; exact i.isLt)]
    exact List.getElem_mem _
  have e := read_of_tie (S.sg t) _ _ (ioppFoldShape cu L) id h hRd S₀ row₀ eps claim gamma hold
    hkept hγ hlog (Qs i) hx α
  rw [wordIn_first t (dFirst S) _ μ ρ hst hk1 hμ hμz hμm hρ hρz hρm hc,
    wordFr_first t (dFirst S) _ φ ψ hst hk1 hφ hψ hc, foldWords_enc (S.sg t) hs] at e
  exact e

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.dFirst
#print axioms Johnson.Prover.Link.hy_first
