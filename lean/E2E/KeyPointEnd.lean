-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyPointEnd.lean: what the shared chain's last state notes of Omega's number and of the point:
the equations that the item (Dot) asks of that state (`dot_item`, E2E/KeyDotItem.lean), read off the
fold that `Thr` holds.

Why. (Dot)'s equation at the honest words speaks at the number 2 and at the point of the chain's first
round. The state at the chain's end notes a number and a point of its own. This file says that they
are those.

Main names.
  `point_at9`: behind the first nine members: the point is the first round's, it has the plan's
    length, and Omega's number is two behind the first state's count of messages.
  `point_at12`: the same behind all twelve.
  `point_of_thr`: the same wherever `Thr` holds at border 12, read at the first challenge heard.

What stays open. `Plan2`, `ChainAt` and `TailAt` are premises of `point_of_thr`, as of the library's
`omega_at_twelve`; `TailAt` at the key is not laid here. That a thread stands at border 12 is not said.

NOT IN FRONT OF A LAW OVER COINS: `point_of_thr` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: `hA` stands at a run's coins `k` and ties the
thread's letters and `m`, of the first kind. None of these is the term that the committer makes. None:
the bar is flat. `point_at9` and `point_at12` speak of a fold and name no coin.

Nothing on soundness, completeness, hiding or binding.

-/
import Johnson.Desc.ProofFile.Honest.K14.OmegaTwelve

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyPointEnd
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc.K12 (P12)
open _root_.Desc.K14 (St P14 first drawn)
open _root_.Desc.K14.Honest (Eight FlatAt Public8)

section run
variable {P : P14} {sentU : Array OracleNotice} {layO : TreeLay} {d0 : St} {B : Eight P} {ft : Nat}
  {Cl : Type} {xs : List (Block St Cl)} {c : OnBytes.Model.Verify.Chains} {p₉ p₁₀ : P12}
  {front : List (Block St Unit)}

/-- What the state notes behind the first nine members. -/
theorem point_at9 (F : FlatAt xs c B) (S : Public8 P sentU layO d0) (s : St)
    (rs rs' : List Fmt.RoundView) (cl cl' : List OpenedColumn)
    (h : foldBlocks ft (xs.take 9) d0 rs cl = .ok (s, rs', cl')) :
    ∃ R, rs.head? = some R ∧ s.loc.psiSh = R.drawn.elems.map E.ofTriple ∧
      s.loc.psiSh.length = P.par.S.kCol ∧ s.loc.oOmega = d0.st.oracles.size + 2 := by
  obtain ⟨W, D, hrs, -, rfl, u⟩ := F.stepTo8 S.facts.goes S.facts.two ft d0 s rs rs' cl cl' h
  obtain ⟨x, ids, x', ids', t⟩ := S.to7 u.front
  have A := S.at6 t.front
  have e7 := t.d7_eq
  obtain ⟨cc, n, hh⟩ := u.s8
  obtain ⟨R, -, -, k⟩ := B.back8 S.facts.goes S.facts.two ft D.d7 D.d8 _ cc n hh
  obtain ⟨GU, GO, x₂, l, n₂, row, mu, L⟩ :=
    VerifiableInference.Desc.Key.laid_split P.par D.d7 D.d8 (VerifiableInference.Desc.noDigest R)
      S.facts.two k
  have hl : D.d8.loc = { D.d6.loc with zFd := drawn W.view.r7 } := by
    rw [L.loc, e7]
  have hp : D.d8.loc.psiSh = W.R1.drawn.elems.map E.ofTriple := by
    rw [hl]
    show D.d6.loc.psiSh = _
    rw [A.loc]
    rfl
  have hpt : (drawn W.view.r1).length = P.par.S.kCol :=
    t.front.front.front.front.front.front.point
  refine ⟨W.R1, ?_, hp, ?_, ?_⟩
  · rw [hrs]
    rfl
  · rw [hp]
    exact hpt
  · rw [hl]
    show D.d6.loc.oOmega = _
    rw [A.loc]
    rfl

/-- **The same behind all twelve.** -/
theorem point_at12 (F : FlatAt xs c B) (Tl : TailAt xs p₉ p₁₀ front)
    (S : Public8 P sentU layO d0) (s : St) (rs rs' : List Fmt.RoundView) (cl cl' : List OpenedColumn)
    (h : foldBlocks ft (xs.take 12) d0 rs cl = .ok (s, rs', cl')) :
    ∃ R, rs.head? = some R ∧ s.loc.psiSh = R.drawn.elems.map E.ofTriple ∧
      s.loc.psiSh.length = P.par.S.kCol ∧ s.loc.oOmega = d0.st.oracles.size + 2 := by
  obtain ⟨x11, h11, l11⟩ := Tl.eleven
  obtain ⟨s11, r11, c11, f11, _, _, k11⟩ := fold_rung h11 h
  obtain ⟨x10, h10, l10⟩ := Tl.ten
  obtain ⟨s10, r10, c10, f10, _, _, k10⟩ := fold_rung h10 f11
  obtain ⟨x9, h9, l9⟩ := Tl.nine
  obtain ⟨s9, r9, c9, f9, _, _, k9⟩ := fold_rung h9 f10
  obtain ⟨R, hR, hp, hl, ho⟩ := point_at9 F S s9 rs r9 cl c9 f9
  have hm := mask_of_omegaEnd (omegaEnd_of_facts (omega_of_fold F S s9 _ _ _ _ f9))
  rw [l9.decide] at k9
  rw [l10.decide] at k10
  rw [l11.decide] at k11
  have K9 := omegaKept_onGu p₉ Tl.plan₉ _ _ _ _ k9 hm
  have K10 := omegaKept_onGomega p₁₀ Tl.plan₁₀ _ _ _ _ k10
  obtain ⟨K11, -, -⟩ := kept_closing front _ _ _ _ k11
  refine ⟨R, hR, ?_, ?_, ?_⟩
  · rw [K11.psi, K10.psi, K9.psi]
    exact hp
  · rw [K11.psi, K10.psi, K9.psi]
    exact hl
  · rw [K11.omega, K10.omega, K9.omega]
    exact ho

end run

section thread
variable {Bk : ProverCoinCounts} {Cl V Wt X Pb : Type} {Q : P14} {sentU : Array OracleNotice} {layO : TreeLay}
  {T : Thread Bk St Cl V Wt X Pb} {c : OnBytes.Model.Verify.Chains} {key : Wt → TableKey}
  {p₉ p₁₀ : P12} {front : List (Block St Unit)}

/-- **At border 12, wherever `Thr` holds**: the point is the one that the first challenge heard
draws; it has the plan's length; Omega's number is 2.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem point_of_thr (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key)
    (hL : TailAt T.bs p₉ p₁₀ front) (hf : T.front = 0) {k : Coins Bk} {s : St} {m : Mid Wt X}
    {E' : Env} (hA : Thr T 12 k s m E') :
    ∃ d, m.st.heard.head? = some d ∧ s.loc.psiSh = d.elems.map E.ofTriple ∧
      s.loc.psiSh.length = Q.par.S.kCol ∧ s.loc.oOmega = 2 := by
  obtain ⟨B⟩ := hQ.eight
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨hseen, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes (key m.st.input) := hT.begun _ _ _ _ hbeg
  rw [hf, List.drop_zero] at hfold
  obtain ⟨R, hR, hp, hl, ho⟩ :=
    point_at12 (hT.bs B) hL (hQ.pub (key m.st.input)) s _ _ _ _ hfold
  refine ⟨R.drawn, ?_, hp, hl, ho⟩
  rw [← hseen, List.head?_map, hR]
  rfl

end thread

end AtPublicFiles.KeyPointEnd

#print axioms AtPublicFiles.KeyPointEnd.point_at9
#print axioms AtPublicFiles.KeyPointEnd.point_at12
#print axioms AtPublicFiles.KeyPointEnd.point_of_thr
