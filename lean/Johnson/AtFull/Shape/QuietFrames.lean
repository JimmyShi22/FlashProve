-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/QuietFrames.lean: SEVENTY-SIX MEMBERS WITHOUT A ROUND OF THE PROOF FILE's OWN
FIRST CHAIN, IN THE FRAME's OWN FORM: the two premises that the rule for acceptance asks at a
member: Carries and Returns (another house's Johnson/Desc/ProofFile/Honest/Thread/Shape.lean), by
the pattern of Johnson/AtFull/Shape/FrameForm.lean: the chain's front (1), "link l: laid" (25), K9's
"the segment is shut" (25), "link l: cleared" (25). A joining of laws; nothing is evaluated.

What is new beside the seats' two laws on the chain's shape: what each member does to the other part
of ShA: THE MAKES OF THE STATEMENT's ROWS STAY at all 76. (The arrays' marks lie in the ledger's
shape: the laws on the chain's shape speak of them.)

  (`liftQ g`, Johnson/AtFull/Shape/FrameLift.lean: a step on the chain's shape alone, on the whole:
    the makes stand.)
  **`frame_of_quiet`**: from a member's number, its two laws on the shape and its keeper of the
    makes to Carries and Returns there, for every table of steps G with G ‹number› = liftQ g and
    every table of tests on values.
  `frame_of_value`: the like for a member whose "returns" asks one Bool of the state in front.
  `clearWith_st`: where the link leaves no row, "cleared" leaves the statement.
  **`front_frame`**, **`laid_frame`**, **`shut_frame`**, **`cleared_att_frame`**,
  **`cleared_lay_frame`**, **`cleared_head_frame`**.

Limits. TWO PREMISES OF THE RULE AT 76 OF 358 MEMBERS: the rule asks them at every member, and more
(that the run on shapes returns; the values; the fits). G and vals are letters: no table of steps is
laid. NO FRAME HERE SAYS THAT A MEMBER STANDS AT ITS NUMBER: where none stands Carries and Returns
hold for nothing (the seats' own laws have that fact). front_frame and laid_frame speak at (F0T
…).first.blocksInOrder, the four others at cF.blocksInOrder: one list, by Numbers.lean's first_is. frame_of_value asks
that vals equals V; its proof uses only that a yes of vals gives a yes of V. UNDER THE HEAD: that it
has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files, in
a side library. At the earlier hash. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.FrameLift
import Johnson.AtFull.Shape.FrameAtHead
import Johnson.AtFull.Shape.ShutAtHead
import Johnson.AtFull.Shape.SeatsNamed
import Johnson.AtFull.Shape.ClearedRowAtHead
import Johnson.Desc.First.Walk.Shape.ClearForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link KindName roundsFit noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Shape
open Johnson.Desc.First.Walk.Seat (pubOf)
open VerifiableInference.Desc.K9.Shape (shutG shut_iff)
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA F0T)
open ProofFile.Honest (Carries Returns)

/-! ## 1 The pattern for a member that leaves the makes -/

theorem frame_of_quiet {Cl : Type} {bs : List (Block S Cl)} {i : Nat} {b : Block S Cl}
    {g : ChainSh → Except String ChainSh} (hb : bs[i]? = some b)
    (hc : ∀ s rs gs t u, b.decide s rs gs = .ok t → g (chainSh s) = .ok u → u = chainSh t)
    (hr : ∀ s rs gs u, g (chainSh s) = .ok u → ∃ t, b.decide s rs gs = .ok t)
    (hk : ∀ s rs gs t, b.decide s rs gs = .ok t → formsOf t.st = formsOf s.st)
    (ft : Nat) (G : Nat → ShA → Except String ShA)
    (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hG : G i = liftQ g) :
    Carries bs ft (firstZA G vals) i ∧ Returns bs ft (firstZA G vals) i := by
  constructor
  · refine carries_of_seat hb fun s rs gs t u _ hd hu => ?_
    rw [hG] at hu
    unfold liftQ at hu
    cases hg : g (shA s).1 with
    | error e => rw [hg] at hu; exact nomatch hu
    | ok v =>
      rw [hg] at hu
      obtain rfl := Except.ok.inj hu
      obtain rfl := hc s _ gs t v hd hg
      show (chainSh t, formsOf s.st) = (chainSh t, formsOf t.st)
      rw [hk s _ gs t hd]
  · refine returns_of_seat hb fun s rs gs u _ hu _ => ?_
    rw [hG] at hu
    unfold liftQ at hu
    cases hg : g (shA s).1 with
    | error e => rw [hg] at hu; exact nomatch hu
    | ok v => exact hr s _ gs v hg

/-- The like for a member whose "returns" asks one Bool of the state in front. -/
theorem frame_of_value {Cl : Type} {bs : List (Block S Cl)} {i : Nat} {b : Block S Cl}
    {g : ChainSh → Except String ChainSh} {V : S → Bool} (hb : bs[i]? = some b)
    (hc : ∀ s rs gs t u, b.decide s rs gs = .ok t → g (chainSh s) = .ok u → u = chainSh t)
    (hr : ∀ s rs gs u, g (chainSh s) = .ok u → V s = true → ∃ t, b.decide s rs gs = .ok t)
    (hk : ∀ s rs gs t, b.decide s rs gs = .ok t → formsOf t.st = formsOf s.st)
    (ft : Nat) (G : Nat → ShA → Except String ShA)
    (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hG : G i = liftQ g) (hv : ∀ s rs gs, vals i s rs gs = V s) :
    Carries bs ft (firstZA G vals) i ∧ Returns bs ft (firstZA G vals) i := by
  constructor
  · refine carries_of_seat hb fun s rs gs t u _ hd hu => ?_
    rw [hG] at hu
    unfold liftQ at hu
    cases hg : g (shA s).1 with
    | error e => rw [hg] at hu; exact nomatch hu
    | ok v =>
      rw [hg] at hu
      obtain rfl := Except.ok.inj hu
      obtain rfl := hc s _ gs t v hd hg
      show (chainSh t, formsOf s.st) = (chainSh t, formsOf t.st)
      rw [hk s _ gs t hd]
  · refine returns_of_seat hb fun s rs gs u _ hu hvv => ?_
    rw [hG] at hu
    rw [hv] at hvv
    unfold liftQ at hu
    cases hg : g (shA s).1 with
    | error e => rw [hg] at hu; exact nomatch hu
    | ok v => exact hr s _ gs v hg hvv

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-! ## 3 The front · "laid" -/

theorem front_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (ft : Nat)
    (G : Nat → ShA → Except String ShA)
    (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hG : G 0 = liftQ .ok) :
    Carries (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder ft (firstZA G vals) 0 ∧
      Returns (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder ft (firstZA G vals) 0 := by
  obtain ⟨b, hb, -, hd⟩ := front_at h
  refine frame_of_quiet hb (fun s rs gs t u hy hu => ?_)
    (fun s rs gs u _ => ⟨s, (hd s rs gs s).2 rfl⟩) (fun s rs gs t hy => ?_) ft G vals hG
  · obtain rfl := (hd s rs gs t).1 hy
    exact (Except.ok.inj hu).symm
  · obtain rfl := (hd s rs gs t).1 hy
    rfl

theorem laid_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) (ft : Nat)
    (G : Nat → ShA → Except String ShA)
    (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hG : G (14 * l + 1) = liftQ (laidGS l)) :
    Carries (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder ft (firstZA G vals) (14 * l + 1) ∧
      Returns (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder ft (firstZA G vals) (14 * l + 1) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, fs, -, hall⟩ := IM.frame_of h.scope h.reads O
  obtain ⟨Lk, f, bL, -, -, -, -, -, -, hlay, hL, -, hb, hr, hd, -⟩ := hall l hl
  obtain ⟨b, hb', -, hc, hrt⟩ := laid_at h l hl
  obtain rfl : bL = b := Option.some.inj (hb.symm.trans hb')
  refine frame_of_quiet hb' hc hrt (fun s rs gs t hy => ?_) ft G vals hG
  have hy' : Lk.lay s = .ok t := (hd s rs gs).symm.trans hy
  have hy2 := (hL s t).1 hy'
  rw [hlay] at hy2
  obtain ⟨rfl, -⟩ := Props.layFront_iff.1 hy2.1
  rfl

/-! ## 4 "The segment is shut" -/

theorem shut_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (L : Link S ProofFile.Cl), cF.links[l]? = some L ∧
      ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (14 * l + L.hear.length + 4 + 2) = liftQ shutGS →
        Carries cF.blocksInOrder ft (firstZA G vals) (14 * l + L.hear.length + 4 + 2) ∧
          Returns cF.blocksInOrder ft (firstZA G vals) (14 * l + L.hear.length + 4 + 2) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨L, p, Q, eL, -, -, hall⟩ := IM.close_of h.scope h.reads O l hl
  obtain ⟨b, y, e1, e2, la⟩ := hall 2 .K9 rfl
  obtain rfl : VerifiableInference.Desc.K9.shut p (Q.piece + 1) = y := Option.some.inj e2
  have hy := IM.yes_alone la (by intro k; cases k)
  obtain ⟨L', b', eL', hb', hc, hr⟩ := shut_at h l hl
  obtain rfl : L = L' := Option.some.inj (eL.symm.trans eL')
  have hb := IM.close_numbers h.scope h.reads O hl eL e1
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  refine ⟨L, eL, fun ft G vals hG => frame_of_quiet hb' hc hr (fun s rs gs t hd => ?_) ft G vals hG⟩
  have hd' : (VerifiableInference.Desc.K9.shut (Cl := Unit) p (Q.piece + 1)).decide s rs gs =
    .ok t := ((hy s t rs gs).1 hd).1
  obtain ⟨C, -, rfl⟩ := (shut_iff p (Q.piece + 1) s t rs gs).1 hd'
  rw [putLink_st]

/-! ## 5 "Cleared" -/

/-- Where the link leaves no row, "cleared" leaves the statement. -/
theorem clearWith_st {X : LinkPub} {counts : S → Except String Unit}
    {left : S → Option WsForkOut} {row : RowFn} {s t : S} (hv : X.fv = false)
    (h : clearWith X counts left row s = .ok t) : t.st = s.st := by
  obtain ⟨C, F, -, hF, -, k, q, hbk, hq⟩ := Props.clearWith_iff.1 h
  have hn : q = none := hbk.2.2.2.2.1 hv
  subst hn
  rcases hq with ⟨-, hl⟩ | ⟨w, _, _, e, -⟩
  · obtain ⟨rfl, -⟩ := (leave_iff hF t).1 hl
    rfl
  · exact nomatch e

theorem cleared_att_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (hs : subAt l = .attention) :
    ∃ (Y : Stages.LinkH) (p : Attention.Plan) (L : Link S ProofFile.Cl),
      Zp.p.built.links[l]? = some Y ∧ Zp.p.X.A[Y.g]? = some p ∧ cF.links[l]? = some L ∧
      ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (14 * l + L.hear.length + 7) = liftQ (clearAttG (pubOf Y) p.nLin) →
        Carries cF.blocksInOrder ft (firstZA G vals) (14 * l + L.hear.length + 7) ∧
          Returns cF.blocksInOrder ft (firstZA G vals) (14 * l + L.hear.length + 7) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, fs, hfs, hall⟩ := IM.frame_of h.scope h.reads O
  obtain ⟨Lk, f, -, -, bC, eL, -, hf, -, -, -, hC, -, -, -, -, -, -, hb, -, hd⟩ := hall l hl
  obtain ⟨Y₀, p₀, hY₀, hA₀, hpl, -, hcl⟩ := row_att h hl hs hfs hf
  obtain ⟨Y, p, L, b, hY, hA, eL', hb', -, hc, hr⟩ := cleared_att_named h l hl hs
  obtain rfl : Y₀ = Y := Option.some.inj (hY₀.symm.trans hY)
  obtain rfl : p₀ = p := Option.some.inj (hA₀.symm.trans hA)
  obtain rfl : Lk = L := Option.some.inj (eL.symm.trans eL')
  obtain rfl : bC = b := Option.some.inj (hb.symm.trans hb')
  refine ⟨Y₀, p₀, Lk, hY, hA, eL, fun ft G vals hG =>
    frame_of_quiet hb' hc hr (fun s rs gs t hy => ?_) ft G vals hG⟩
  have hy2 := ((hC s t).1 ((hd s rs gs).symm.trans hy)).1
  rw [hcl] at hy2
  rw [clearWith_st (Props.planAtt_fv hpl) hy2]

theorem cleared_lay_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (hs : subAt l = .layers) :
    ∃ (Y : Stages.LinkH) (hp : Layer.HPlan2) (L : Link S ProofFile.Cl),
      Zp.p.built.links[l]? = some Y ∧ Zp.p.X.G[Y.g]? = some hp ∧ cF.links[l]? = some L ∧
      ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (14 * l + L.hear.length + 7) =
          liftQ (clearLayG (pubOf Y) Zp.p.X.layers.wsLay Zp.first.lin hp.tl.NM) →
        Carries cF.blocksInOrder ft (firstZA G vals) (14 * l + L.hear.length + 7) ∧
          Returns cF.blocksInOrder ft (firstZA G vals) (14 * l + L.hear.length + 7) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, fs, hfs, hall⟩ := IM.frame_of h.scope h.reads O
  obtain ⟨Lk, f, -, -, bC, eL, -, hf, -, -, -, hC, -, -, -, -, -, -, hb, -, hd⟩ := hall l hl
  obtain ⟨Y₀, hp₀, hY₀, hG₀, hcl⟩ := clear_lay h hl hs hfs hf
  obtain ⟨Y, hp, L, b, hY, hGp, eL', hb', -, hc, hr⟩ := cleared_lay_named h l hl hs
  obtain rfl : Y₀ = Y := Option.some.inj (hY₀.symm.trans hY)
  obtain rfl : hp₀ = hp := Option.some.inj (hG₀.symm.trans hGp)
  obtain rfl : Lk = L := Option.some.inj (eL.symm.trans eL')
  obtain rfl : bC = b := Option.some.inj (hb.symm.trans hb')
  refine ⟨Y₀, hp₀, Lk, hY, hGp, eL, fun ft G vals hG =>
    frame_of_quiet hb' hc hr (fun s rs gs t hy => ?_) ft G vals hG⟩
  have hy2 := ((hC s t).1 ((hd s rs gs).symm.trans hy)).1
  rw [hcl] at hy2
  exact clear_forms hy2

theorem cleared_head_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (hs : subAt l = .head) :
    ∃ (Y : Stages.LinkH) (L : Link S ProofFile.Cl),
      Zp.p.built.links[l]? = some Y ∧ cF.links[l]? = some L ∧
      ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (14 * l + L.hear.length + 7) =
          liftQ (clearHeadG (pubOf Y) Zp.p.X.layers.wsLay Zp.first.lin) →
        Carries cF.blocksInOrder ft (firstZA G vals) (14 * l + L.hear.length + 7) ∧
          Returns cF.blocksInOrder ft (firstZA G vals) (14 * l + L.hear.length + 7) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, fs, hfs, hall⟩ := IM.frame_of h.scope h.reads O
  obtain ⟨Lk, f, -, -, bC, eL, -, hf, -, -, -, hC, -, -, -, -, -, -, hb, -, hd⟩ := hall l hl
  obtain ⟨Y₀, hY₀, hcl⟩ := clear_head h hl hs hfs hf
  obtain ⟨Y, L, b, hY, eL', hb', -, hc, hr⟩ := cleared_head_named h l hl hs
  obtain rfl : Y₀ = Y := Option.some.inj (hY₀.symm.trans hY)
  obtain rfl : Lk = L := Option.some.inj (eL.symm.trans eL')
  obtain rfl : bC = b := Option.some.inj (hb.symm.trans hb')
  refine ⟨Y₀, Lk, hY, eL, fun ft G vals hG =>
    frame_of_quiet hb' hc hr (fun s rs gs t hy => ?_) ft G vals hG⟩
  have hy2 := ((hC s t).1 ((hd s rs gs).symm.trans hy)).1
  rw [hcl] at hy2
  exact clearHead_forms hy2

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.shut_frame
#print axioms Johnson.AtFull.Shape.cleared_att_frame
#print axioms Johnson.AtFull.Shape.cleared_lay_frame
#print axioms Johnson.AtFull.Shape.cleared_head_frame
#print axioms Johnson.AtFull.Shape.frame_of_quiet
#print axioms Johnson.AtFull.Shape.frame_of_value
#print axioms Johnson.AtFull.Shape.front_frame
#print axioms Johnson.AtFull.Shape.laid_frame
#print axioms Johnson.AtFull.Shape.clearWith_st
