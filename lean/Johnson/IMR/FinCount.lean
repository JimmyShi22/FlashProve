-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FinCount.lean: IN FRONT OF THE FINISH (the cut 353, in front of
"F:1") THE STATEMENT HAS JUST 25 GROUPS; AND THE GROUP OF THE FINISH's FRONT: at the proof file's
seat, in the goals' scope, from the fold's return alone.
  headQ: a tool.
  head_one: from the cut 338 to the cut 353: one group more: "H:1" makes it
    (headFrontQ_st); "H:2" fills it (Johnson/IMR/HeadFill.lean's head_gains); the seven hearing
      sub-protocols
    behind, the five from the batching to the shutting and "cleared" leave the number of groups
    (Johnson/IMR/HeadRest.lean's hear_by24, hear_runs24, rest_of_runs at
      Johnson/IMR/GroupCount.lean's Sz).
  count_fin: THE COUNT: 25.
  fin_front: a yes of the quiet step "F.0.front" from a state s: the front fx that K2.frontAt makes
    of the state behind: fx.f.rows = s's walk's frame's carried rows; fx.f.group = the number of s's
    groups; that group is the statement's last and has no row, no member, no flag; the messages are
    s's.
  front_nums_fin: THE TOP: at the cut 353: fx.f.group = 25, 26 groups, the group fresh.
NOT HERE: what the finish keeps.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USER: kind K2's files.
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.HeadFill
import Johnson.IMR.HeadRest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl)

/-- Some numbers of a place that stands at the head: K2.frontAt reads "stands" alone of them. -/
def headQ : K2.P2 :=
  { name := "", place := { chain := 1, link := some 24, piece := 2, kind := .K2 }, stands := .head,
    grp := 0, firstTree := 0, samples := 0, work₁ := 0, roots := 0, seeds := 0, nonZero := 0,
    work₂ := 0, answers := 0, positions := 0, logN := 0, sent := [], read := [] }

/-- **A yes of "F.0.front".** -/
theorem fin_front {s s' : S} (h : K2.finishFrontQ s = .ok s') {q : K2.P2}
    (hq : q.stands = .finish) {fx : _root_.Tw.K2.Front} (hf : K2.frontAt q s' = some fx) :
    fx.f.rows = s.check.frame.rows ∧ fx.f.group = s.st.groups.size ∧
      fx.st.groups.size = s.st.groups.size + 1 ∧ fx.st.oracles = s.st.oracles ∧
      ∃ G, fx.st.groups[fx.f.group]? = some G ∧ G.rows = #[] ∧ G.members = #[] ∧ G.kept = #[] := by
  obtain ⟨G, x, s₁, a, k⟩ := (K2.finishFrontQ_iff s s').1 h
  obtain ⟨G₁, S', g, fa⟩ := (_root_.Tw.K2.finishFront_iff _ _ _).1 k.front
  obtain ⟨e1, e2⟩ := K2.newGroupG_is fa.opened
  have hh : s'.here = .fin { a with G := some G, fr := x.f } := by rw [k.out]
  have hst : s'.st = x.st := by rw [k.out]
  unfold K2.frontAt at hf
  rw [hq, hh] at hf
  obtain rfl : K2.finFrontOf s' { a with G := some G, fr := x.f } G = fx := Option.some.inj hf
  have ex : x.st = K2.withFresh s.st s.check.frame.shape.code s.check.frame.shape.maskCode := by
    rw [fa.out]
    exact e1
  have eg : x.f.group = s.st.groups.size := by
    rw [fa.out]
    exact e2
  refine ⟨?_, eg, ?_, ?_,
    K2.freshGroup s.check.frame.shape.code s.check.frame.shape.maskCode, ?_, rfl, rfl, rfl⟩
  · show x.f.rows = _
    rw [fa.out]
  · show s'.st.groups.size = _
    rw [hst, ex]
    simp [K2.withFresh]
  · show s'.st.oracles = _
    rw [hst, ex]
    rfl
  · show s'.st.groups[x.f.group]? = _
    rw [hst, ex, eg]
    simp [K2.withFresh]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **OVER THE HEAD's LINK: ONE GROUP MORE.** -/
theorem head_one (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R Rm R₂ : List Fmt.RoundView} {C Cm C₂ : List VerifiableInference.Desc.OpenedColumn} {tm t₂ : S}
    (fm : foldBlocks 0 (c.blocksInOrder.take 338) (ProofFile.startS Z p) R C = .ok (tm, Rm, Cm))
    (f₂ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    t₂.st.groups.size = tm.st.groups.size + 1 := by
  obtain ⟨-, fs, hfs, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, f, bL, bB, bC, eL, hlen, hf, -, -, -, hClear, -, -, -, -, -, -, iC, -, dC⟩ :=
    hfr 24 (by omega)
  rw [if_pos rfl] at hlen
  rw [hlen] at iC
  have cut : ∀ n ≤ 15, ∃ t r q,
      foldBlocks 0 (c.blocksInOrder.take (338 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q) := by
    intro n hn
    exact fold_cut (k := 338 + n) (15 - n)
      (by rw [show 338 + n + (15 - n) = 353 by omega]; exact f₂)
  have hearAt : ∀ j < 9, ∃ b, Lk.hear[j]? = some b ∧ c.blocksInOrder[338 + j]? = some b := by
    intro j hj
    obtain ⟨b, e⟩ : ∃ b, Lk.hear[j]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by omega : j < Lk.hear.length)⟩
    refine ⟨b, e, ?_⟩
    have q := IM.hear_at_flat eL e
    rwa [(IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) j).trans
      (by omega : 14 * 24 + j + 2 = 338 + j)] at q
  obtain ⟨t₀, R₀, C₀, f₀⟩ := cut 1 (by omega)
  obtain ⟨t₁, R₁, C₁, f₁⟩ := cut 2 (by omega)
  -- "H:1"
  obtain ⟨Lk0, b0, eL0, e0, hj, -⟩ := IM.k7_sits hS hR O
  obtain rfl : Lk = Lk0 := Option.some.inj (eL.symm.trans eL0)
  obtain ⟨b0', e0', i0⟩ := hearAt 0 (by omega)
  obtain rfl : b0 = b0' := Option.some.inj (e0.symm.trans e0')
  obtain ⟨rs0, gs0, d0⟩ := fold_next i0 fm f₀
  obtain ⟨x, a, hx, ha, -, es, ec⟩ := h1_front (IM.k7_sits_yes hS hR O hj d0).1
  have s0 : t₀.st.groups.size = tm.st.groups.size + 1 := by
    rw [es, (K2.firstFront_st hx).1]
    simp [K2.withFresh]
  -- "H:2"
  obtain ⟨L0, G0, S0, g, fa⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 hx
  have hfx : K2.frontAt headQ t₀ = some (K2.headFrontOf t₀ a G0.target) := by
    unfold K2.frontAt
    rw [show headQ.stands = .head from rfl, ha, ec, fa.group]
    rfl
  have s1 : t₁.st.groups.size = t₀.st.groups.size := (head_gains hS hR O f₀ f₁ rfl hfx).1.1
  -- the rest leaves the number of groups
  obtain ⟨b1, e1, i1⟩ := hearAt 1 (by omega)
  obtain ⟨rs1, gs1, d1⟩ := fold_next i1 f₀ f₁
  have hy : ∀ b₁, Lk.hear[1]? = some b₁ → ∃ s rs gs t, b₁.decide s rs gs = .ok t := by
    intro b₁ e
    obtain rfl : b1 = b₁ := Option.some.inj (e1.symm.trans e)
    exact ⟨_, _, _, _, d1⟩
  have hruns := hear_runs24 sz_refl sz_trans (fun _ _ => sz_of_quiet) hS hR O eL hy
  have step : ∀ n, 2 ≤ n → n ≤ 14 → ∀ t r q t' r' q',
      foldBlocks 0 (c.blocksInOrder.take (338 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q) →
      foldBlocks 0 (c.blocksInOrder.take (338 + (n + 1))) (ProofFile.startS Z p) R C = .ok (t', r', q') →
      Sz t t' := by
    intro n h2 hn t r q t' r' q' g g'
    by_cases h8 : n ≤ 8
    · obtain ⟨b, e, ib⟩ := hearAt n (by omega)
      obtain ⟨rs, gs, d⟩ := fold_next ib g g'
      exact hear_by24 sz_trans (fun _ _ => sz_of_quiet) (fun _ _ _ _ _ _ _ _ => sz_commit)
        hS hR O h2 h8 eL e t rs gs t' d
    · by_cases h13 : n ≤ 13
      · obtain ⟨b, ib⟩ : ∃ b, c.blocksInOrder[338 + n]? = some b :=
          ⟨_, List.getElem?_eq_getElem (by
            have := (List.getElem?_eq_some_iff.1 iC).1
            omega)⟩
        obtain ⟨rs, gs, d⟩ := fold_next ib g g'
        exact rest_of_runs sz_refl sz_trans (fun p _ hcl => batch_sz p hcl) closeOf_sz hS hR O
          (by omega : 24 < 25) eL hruns (n := n - 9) (by omega)
          (by rw [hlen, show 14 * 24 + 9 + 2 + (n - 9) = 338 + n by omega]; exact ib) t rs gs t' d
      · obtain rfl : n = 14 := by omega
        have iC' : c.blocksInOrder[338 + 14]? = some bC := by
          rw [show 338 + 14 = 14 * 24 + 9 + 7 by omega]
          exact iC
        obtain ⟨rs, gs, d⟩ := fold_next iC' g g'
        rw [dC] at d
        exact (framesOf_sz hfs f (List.mem_of_getElem? hf)).2.2 t t' ((hClear t t').1 d).1
  have all : ∀ n ≤ 13, ∀ t r q,
      foldBlocks 0 (c.blocksInOrder.take (338 + (2 + n))) (ProofFile.startS Z p) R C = .ok (t, r, q) →
      Sz t₁ t := by
    intro n
    induction n with
    | zero =>
      intro _ t r q g
      obtain rfl : t₁ = t := congrArg Prod.fst (Except.ok.inj (f₁.symm.trans g))
      exact sz_refl _
    | succ n ih =>
      intro hn t r q g
      obtain ⟨u, ru, qu, gu⟩ := cut (2 + n) (by omega)
      exact sz_trans _ _ _ (ih (by omega) u ru qu gu)
        (step (2 + n) (by omega) (by omega) u ru qu t r q gu g)
  have e2 : t₂.st.groups.size = t₁.st.groups.size := all 13 (by omega) t₂ R₂ C₂ f₂
  rw [e2, s1, s0]

/-- **THE COUNT IN FRONT OF THE FINISH.** -/
theorem count_fin (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₂ : List Fmt.RoundView} {C C₂ : List VerifiableInference.Desc.OpenedColumn} {t₂ : S}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    t₂.st.groups.size = 25 := by
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_cut (k := 338) 15 f₂
  rw [head_one hS hR O fm f₂, count_at hS hR O 24 (by omega) tm Rm Cm fm]

/-- **THE FINISH's FRONT's GROUP.** t': the state behind the quiet step "F.0.front". -/
theorem front_nums_fin (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₂ : List Fmt.RoundView} {C C₂ : List VerifiableInference.Desc.OpenedColumn} {t₂ t' : S}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂))
    (h : K2.finishFrontQ t₂ = .ok t') {q : K2.P2} (hq : q.stands = .finish)
    {fx : _root_.Tw.K2.Front} (hf : K2.frontAt q t' = some fx) :
    fx.f.group = 25 ∧ fx.st.groups.size = 26 ∧ fx.f.rows = t₂.check.frame.rows ∧
      fx.st.oracles = t₂.st.oracles ∧
      ∃ G, fx.st.groups[fx.f.group]? = some G ∧ G.rows = #[] ∧ G.members = #[] ∧ G.kept = #[] := by
  have hc := count_fin hS hR O f₂
  obtain ⟨a1, a2, a3, a4, a5⟩ := fin_front h hq hf
  exact ⟨a2.trans hc, by rw [a3, hc], a1, a4, a5⟩

end

#print axioms fin_front
#print axioms head_one
#print axioms count_fin
#print axioms front_nums_fin

end Meaning.K2
