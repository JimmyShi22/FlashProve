-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/GroupCount.lean: IN FRONT OF THE FIRST SUB-PROTOCOL OF LINK l THE
STATEMENT HAS JUST l GROUPS: at the proof file's seat, in the goals' scope, from the fold's return
alone; and what follows for the front that the code switching's text makes of the verifier's state.
  Sz s t: the statement has as many groups at t as at s. sz_of_quiet; sz_commit (kind K1's later
    sending: its files' Joins.size); batch_sz, closeOf_sz (kind K9's makers leave the statement or
    are calm; kind K10's closeFrame_groups); framesOf_sz (the frames' three).
  first_one: the first sub-protocol of a link l < 24 makes one group more (at l = 0 kind K1's
    firstAtS_group; at l ≥ 1 kind K2's yes_link_groups; "opened" leaves the
    statement).
  link_one: from the cut 14 l + 2 to the cut 14 (l + 1) + 2: one group more.
  count_at: THE COUNT: at the cut 14 l + 2, l ≤ 24: t.st.groups.size = l.
  front_nums_link (1 ≤ l < 24): the front's group is number l, it is the statement's last, and it
    has no row, no member and no flag: the first two conjuncts of kind K2's numsB at
    grp := l, rows := 0.
NOT HERE: the head's and the finish's fronts; the number of messages; the kept old messages.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USER: kind K2's files.
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.GroupRest
import Johnson.Desc.K1.Law.GroupAtLater
import Johnson.Desc.First.Close.Law.GroupsStay
import Johnson.Top.H0.Tw.K2C.GroupsAtYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K9
open ProofFile (Cl)

/-- As many groups. -/
def SzS (T T' : Statement) : Prop := T'.groups.size = T.groups.size

abbrev Sz : S → S → Prop := ByS SzS

theorem sz_refl (s : S) : Sz s s := rfl

theorem sz_trans (a b c : S) (h : Sz a b) (k : Sz b c) : Sz a c := Eq.trans k h

theorem sz_of_st {s t : S} (h : t.st = s.st) : Sz s t := by
  show t.st.groups.size = s.st.groups.size
  rw [h]

theorem sz_of_quiet {s t : S} (q : Quiet s t) : Sz s t := sz_of_st q.1.1

theorem sz_of_calm {s t : S} (q : Calm s t) : Sz s t := q.1

theorem sz_commit {Q : K1.Par} {link moment : Nat} {arrays : Option (List Nat)} {s v : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.commitAtS Q link moment arrays : Block S Unit).decide s rs gs = .ok v) : Sz s v := by
  obtain ⟨r₁, r₂, rfl⟩ := commitAtS_two h
  obtain ⟨L, -, J⟩ := K1.commitAtS_group Q link moment arrays s v r₁ r₂ gs h
  exact J.size

theorem batch_sz (p : Where) {claims : S → Except String (List Claim × S)}
    (hcl : FnCl Sz claims) : Decides Sz (batch atS p claims) := by
  intro s rs gs s' h
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := bindE h
  exact sz_trans _ _ _ (drawAlone_by (R := SzS) (fun _ => rfl) p s rs gs t₁ h1)
    (adds_by p p.piece "the segment's" hcl t₁ [] [] s' h)

theorem closing_sz {C : Type} (Q : Close.Par) : Decides Sz (K9.closing (Cl := C) Q) := by
  intro s rs gs s' h
  obtain ⟨r, hr, rfl⟩ := Keeps.emap_ok h
  obtain ⟨x, hx, rfl⟩ := Keeps.emap_ok hr
  exact (Close.closeFrame_groups hx).1

theorem closeOf_sz (p : Where) (Q : Close.Par) :
    ∀ b ∈ closeOf (Cl := Unit) p Q, Decides Sz b := by
  intro b hb
  unfold closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact fun s rs gs t h => sz_of_calm (oneEquation_calm (Cl := Unit) p s rs gs t h)
  · exact closing_sz Q
  · exact fun s rs gs t h => sz_of_st ((shut_still p _).1 s rs gs t h).1.1

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
/-- The frames' three. -/
theorem framesOf_sz {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (h : framesOf built first W = .ok fs) : ∀ f ∈ fs,
    Fn Sz f.lay ∧ Fn Sz f.opened ∧ Fn Sz f.clear := by
  have lay : ∀ l, Fn Sz (layFront l) := fun l s t k => by
    rw [(Law.layFront_ok k).1]
    exact sz_refl _
  have clr : ∀ (X : LinkPub) (counts : S → Except String Unit) (left : S → Option WsForkOut)
      (row : RowFn), Fn Sz (clearWith X counts left row) := fun X counts left row s t k => by
    show t.st.groups.size = s.st.groups.size
    rw [(Law.clear_carries k).2.2.2.2.2.2.2.2.1]
  have th : ∀ (X : LinkPub) (lay : WsLay) (lin : Params.LinShape),
      Fn Sz (Close.tailHead X lay lin) := fun _ _ _ => clr _ _ _ _
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact ⟨lay l, fun s t k => by cases k; exact sz_refl _, th _ _ _⟩
  · split at e
    · split at e
      · cases e
      · cases e
        exact ⟨lay 0, fun s t k => sz_of_st (openLayZero_enters _ _ _ s t k).1, clr _ _ _ _⟩
    · split at e
      · cases e
      · cases e
        exact ⟨lay l, fun s t k => sz_of_st (openAtt_enters _ s t k).1, clr _ _ _ _⟩
      · cases e
        exact ⟨lay l, fun s t k => sz_of_st (openLay_enters _ s t k).1, clr _ _ _ _⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The first sub-protocol of a link l < 24 makes one group more.** -/
theorem first_one (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₀ R₁ : List Fmt.RoundView} {C C₀ C₁ : List VerifiableInference.Desc.OpenedColumn}
    {t₀ t₁ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁)) :
    t₁.st.groups.size = t₀.st.groups.size + 1 := by
  obtain ⟨hB, -⟩ := laid_at hS hR O (by omega : l < 25) f₀
  have key : ∀ {b : Block S Cl} {b' : Block S Cl} {a : Place}, IM.Joined Z l b b' a →
      c.blocksInOrder[14 * l + 2]? = some b →
      (∀ m rs gs, b'.decide t₀ rs gs = .ok m → m.st.groups.size = t₀.st.groups.size + 1) →
      t₁.st.groups.size = t₀.st.groups.size + 1 := by
    intro b b' a J i0 hm
    obtain ⟨rs, gs, d⟩ := fold_next i0 f₀ f₁
    obtain ⟨fs, f, m, hfs, hf, y1, -, y3, -, -⟩ := J.yes d
    have v : t₁.st.groups.size = m.st.groups.size :=
      (framesOf_sz hfs f (List.mem_of_getElem? hf)).2.1 m t₁ y3
    rw [v]
    exact hm m _ _ y1
  have ix : IM.flatIx c l 0 = 14 * l + 2 :=
    (IM.flatIx_scope hS hR O (by omega : l ≤ 24) 0).trans (by omega)
  by_cases h0 : l = 0
  · subst h0
    obtain ⟨Lk, b, eLk, e0, J⟩ := IM.k1_first_sits hS hR O
    have i0 : c.blocksInOrder[14 * 0 + 2]? = some b := by
      have k := IM.hear_at_flat eLk e0
      rwa [ix] at k
    refine key J i0 fun m rs gs y => ?_
    have y' : (K1.firstSegmentOpening Bs.G₀.first (K1.gpOf Z) : Block S Unit).decide t₀ rs gs = .ok m := y
    have two : ∃ r₁ r₂, rs = [r₁, r₂] := by
      have ha := y'
      unfold K1.firstSegmentOpening at ha
      dsimp only at ha
      obtain ⟨_, -, hb⟩ := bindE ha
      obtain ⟨⟨c', d'⟩, h2, -⟩ := bindE hb
      obtain ⟨g, d₁, ids, d₂, -, hs, -⟩ := K1.firstOwn_ok _ _ _ c' _ d' rs h2
      exact two_of_send hs
    obtain ⟨r₁, r₂, rfl⟩ := two
    exact (K1.firstAtS_group _ _ t₀ m r₁ r₂ gs y').1.size
  · obtain ⟨Lk, b, x, eLk, e0, -, J, hx⟩ := IM.k2_link_sits hS hR O l (by omega) h24
    have i0 : c.blocksInOrder[14 * l + 2]? = some b := by
      have k := IM.hear_at_flat eLk e0
      rwa [ix] at k
    refine key J i0 fun m rs gs y => ?_
    have y' : x.decide t₀ rs gs = .ok m := y
    rcases hx with ⟨-, hm⟩ | ⟨Pp, n, -, -, h3⟩
    · obtain ⟨e, he⟩ := hm t₀ rs gs
      rw [he] at y'
      cases y'
    · rcases h3 with ⟨hl, -⟩ | ⟨l', HP, -, -, e⟩ | ⟨l', -, e⟩
      · cases hl
      · rw [e] at y'
        obtain ⟨v, a1, -⟩ := andThen_yes (n := x.name) y'
        obtain ⟨r₁, r₂, a, G', w, roots, -, H⟩ :=
          K2.head_inv (snd := _root_.Tw.K2.sendByL8) rfl a1
        unfold S.atBetween at hB
        rw [H.hHere] at hB
        cases hB
      · rw [e] at y'
        have h' : K2.decideWith _root_.Tw.K2.sendByL8
            (IM.k2P Z { chain := 1, link := some l, piece := 1, kind := .K2 } x.name .link n) t₀
            rs gs = .ok m := y'
        obtain ⟨fx, -, -, -, sz, -⟩ := K2.yes_link_groups rfl h'
        exact sz

/-- **From in front of a link's first sub-protocol to in front of the next link's: one group
more.** -/
theorem link_one (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₀ R₂ : List Fmt.RoundView} {C C₀ C₂ : List VerifiableInference.Desc.OpenedColumn}
    {t₀ t₂ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    t₂.st.groups.size = t₀.st.groups.size + 1 := by
  obtain ⟨-, fs, hfs, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, f, bL, bB, bC, eL, hlen, hf, -, -, -, hClear, -, -, -, -, -, -, iC, -, dC⟩ :=
    hfr l (by omega)
  rw [if_neg (by omega : ¬ l = 24)] at hlen
  rw [hlen] at iC
  obtain ⟨Lk', f', bL', -, -, -, -, hf', -, -, hLay', -, iL', -, dL', -⟩ := hfr (l + 1) (by omega)
  -- the cuts between
  have cut : ∀ n ≤ 13, ∃ t r q,
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q) := by
    intro n hn
    exact fold_cut (k := 14 * l + 3 + n) (13 - n)
      (by rw [show 14 * l + 3 + n + (13 - n) = 14 * (l + 1) + 2 by omega]; exact f₂)
  obtain ⟨t₁, R₁, C₁, f₁⟩ := cut 0 (by omega)
  have hy : ∀ b₀, Lk.hear[0]? = some b₀ → ∃ s rs gs t, b₀.decide s rs gs = .ok t := by
    intro b₀ e0
    have i0 : c.blocksInOrder[14 * l + 2]? = some b₀ := by
      have q := IM.hear_at_flat eL e0
      rwa [(IM.flatIx_scope hS hR O (by omega : l ≤ 24) 0).trans
        (by omega : 14 * l + 0 + 2 = 14 * l + 2)] at q
    obtain ⟨rs0, gs0, d0⟩ := fold_next i0 f₀ f₁
    exact ⟨_, _, _, _, d0⟩
  -- every sub-protocol from number 14 l + 3 to number 14 l + 15 leaves the number of groups
  have step : ∀ n ≤ 12, ∀ t r q t' r' q',
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q) →
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + (n + 1))) (ProofFile.startS Z p) R C = .ok (t', r', q') →
      Sz t t' := by
    intro n hn t r q t' r' q' g g'
    have hlenF : 14 * l + 3 + n < c.blocksInOrder.length := by
      have := (List.getElem?_eq_some_iff.1 iL').1
      omega
    obtain ⟨b, ib⟩ : ∃ b, c.blocksInOrder[14 * l + 3 + n]? = some b :=
      ⟨_, List.getElem?_eq_getElem hlenF⟩
    obtain ⟨rs, gs, d⟩ := fold_next ib g g'
    by_cases h5 : n ≤ 5
    · obtain ⟨b', e⟩ : ∃ b', Lk.hear[n + 1]? = some b' :=
        ⟨_, List.getElem?_eq_getElem (by omega : n + 1 < Lk.hear.length)⟩
      have ib' : c.blocksInOrder[14 * l + 3 + n]? = some b' := by
        have k := IM.hear_at_flat eL e
        rwa [(IM.flatIx_scope hS hR O (by omega : l ≤ 24) (n + 1)).trans
          (by omega : 14 * l + (n + 1) + 2 = 14 * l + 3 + n)] at k
      obtain rfl := Option.some.inj (ib.symm.trans ib')
      exact hear_by sz_trans (fun _ _ => sz_of_quiet) (fun _ _ _ _ _ _ _ _ => sz_commit)
        hS hR O h24 (by omega) (by omega) eL e t rs gs t' d
    · by_cases h10 : n ≤ 10
      · have ib' : c.blocksInOrder[14 * l + 9 + (n - 6)]? = some b := by
          rw [show 14 * l + 9 + (n - 6) = 14 * l + 3 + n by omega]
          exact ib
        exact rest_by sz_refl sz_trans (fun _ _ => sz_of_quiet) (fun p _ hcl => batch_sz p hcl)
          closeOf_sz hS hR O h24 eL hy (by omega) ib' t rs gs t' d
      · obtain rfl | rfl : n = 11 ∨ n = 12 := by omega
        · obtain rfl := Option.some.inj (ib.symm.trans iC)
          rw [dC] at d
          exact (framesOf_sz hfs f (List.mem_of_getElem? hf)).2.2 t t' ((hClear t t').1 d).1
        · have iL2 : c.blocksInOrder[14 * l + 3 + 12]? = some bL' := by
            rw [show 14 * l + 3 + 12 = 14 * (l + 1) + 1 by omega]
            exact iL'
          obtain rfl := Option.some.inj (ib.symm.trans iL2)
          rw [dL'] at d
          exact (framesOf_sz hfs f' (List.mem_of_getElem? hf')).1 t t' ((hLay' t t').1 d).1
  have all : ∀ n ≤ 13, ∀ t r q,
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q) →
      Sz t₁ t := by
    intro n
    induction n with
    | zero =>
      intro _ t r q g
      obtain rfl : t₁ = t := congrArg Prod.fst (Except.ok.inj (f₁.symm.trans g))
      exact sz_refl _
    | succ n ih =>
      intro hn t r q g
      obtain ⟨u, ru, qu, gu⟩ := cut n (by omega)
      exact sz_trans _ _ _ (ih (by omega) u ru qu gu) (step n (by omega) u ru qu t r q gu g)
  have e2 : Sz t₁ t₂ := all 13 (by omega) t₂ R₂ C₂
    (by rw [show 14 * l + 3 + 13 = 14 * (l + 1) + 2 by omega]; exact f₂)
  have e2' : t₂.st.groups.size = t₁.st.groups.size := e2
  rw [e2', first_one hS hR O h24 f₀ f₁]

/-- **THE COUNT: IN FRONT OF THE FIRST SUB-PROTOCOL OF LINK l THE STATEMENT HAS JUST l GROUPS.** -/
theorem count_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} :
    ∀ l ≤ 24, ∀ (t : S) (R' : List Fmt.RoundView) (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t, R', C') →
      t.st.groups.size = l
  | 0, _, t, R', C', f => by
    rw [laid_is_start hS hR O f, start_groups O.pub p]
    rfl
  | l + 1, hl, t, R', C', f => by
    obtain ⟨u, Ru, Cu, fu⟩ := fold_cut (k := 14 * l + 2) 14
      (by rw [show 14 * l + 2 + 14 = 14 * (l + 1) + 2 by omega]; exact f)
    rw [link_one hS hR O (by omega) fu f, count_at hS hR O l (by omega) u Ru Cu fu]

/-- **THE FRONT's GROUP AT A LINK's CODE SWITCHING, 1 ≤ l < 24.** -/
theorem front_nums_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    {q : K2.P2} (hq : q.stands = .link) {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt q t₀ = some fx) :
    fx.f.group = l ∧ fx.st.groups.size = l + 1 ∧
      ∃ G, fx.st.groups[fx.f.group]? = some G ∧ G.rows = #[] ∧ G.members = #[] ∧ G.kept = #[] := by
  have hc := count_at hS hR O l (by omega) t₀ R₀ C₀ f₀
  obtain ⟨e1, e2⟩ := K2.firstFront_st (K2.front_of_link hq h)
  refine ⟨e2.trans hc, by rw [e1]; simp [K2.withFresh, hc],
    K2.freshGroup t₀.check.frame.shape.code t₀.check.frame.shape.maskCode, ?_, rfl, rfl, rfl⟩
  rw [e1, e2]
  simp [K2.withFresh]

end

#print axioms framesOf_sz
#print axioms first_one
#print axioms link_one
#print axioms count_at
#print axioms front_nums_link

end Meaning.K2
