-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/ViewWide.lean: the second line of Block.step at the written view of the
proximity test (the kind K12): the written columns that the law deals have, opening by opening, the
declared widths.

The columns are srcK's (Johnson/Desc/K12/Law/ViewK.lean) over srcFirst and srcFrom
(Johnson/Desc/K12/Law/Written.lean); the statement is the premise of kpw_colsOf. Statements and
proofs.
Why. The verifier accK of the lemma on the proximity test (Johnson/Desc/K12/Law/K12Lemma.lean) is
Block.step at the written view. Were the step's test "the columns" to fail there for want of width,
accK would be false at every transcript and the lemma would say nothing. With this file and
kpw_colsOf that test holds at the written view, under the premises below.
Main names:
  `colW_length`, `colW_fits`, `listOf_lt`: a written column inside its tree has the tree's width.
  `want_at`, `opensWith_map`, `one_at`, `want_one`: the wants of group number i are the i-th
    declared opening's: its width, at positions inside its depth.
  `take_cut`, `kk_st`: the first k + 3 rounds are the fold's cut and the switch's; the row variables
    of s.st.
  `wideFrom`: from a stage j ≥ 1 on, by induction on the chain, under Dealt
    (Johnson/Desc/K12/Law/DealLaw.lean) and TiedW (Johnson/Desc/K12/Law/TieLaw.lean).
  `wideFirst`: the whole test behind "BAT"; its premise hfirst holds the first switch's i-th opening
    against the i-th tree.
  `opens_W_of_ok`, `first_fits`: hfirst from gpOk's clauses opens.a and opens.W (both are spent
    here), for written trees as deep and as wide as the book's.
  `view_wide`: at the block's own rounds and srcK ("BAT" declares nothing: tieOk's clause bat.none).
  `deep_at`, `view_wide_deep`: at the lemma's own letters W0 and fM under DeepK (its fields mems,
    fresh and wide are spent; same is not).
Limits: No soundness is claimed, and nothing is said on hiding.
Premises: planOk, dealOk and tieOk (tests on the plan); the yes of gpL at D (a test on the record);
the chain's make (stagesOf c is the place's stages; c.rds is the written rounds); DeepK; as many
draws as laid rounds.
It does not say that roundsFit holds at written rounds (Johnson/Desc/K12/Law/FitWritten.lean does),
that the decision says yes, or that any transcript has accK = true.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.TieLaw
import Johnson.Desc.K12.Law.K12Lemma

set_option autoImplicit false
namespace H2K.First
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw
open H2K.Pub (WR writtenOf kk sgOf chainFrom Letters)

/-- A written column inside the tree has the tree's width. -/
theorem colW_length (d : PQ.RD) (o : (wRound d).Orc) (x : ℕ) (hx : x < PQ.posN d.tree) :
    (colW d o x).length = PQ.colW d.tree := by
  unfold colW
  rw [dif_pos hx, List.length_ofFn]

theorem listOf_lt (l : List ℕ) (n x : ℕ) (hn : 0 < n) (h : x ∈ Fmt.listOf (l.map (· % n))) : x < n
    := by
  rw [Fmt.listOf_mem] at h
  obtain ⟨y, _, rfl⟩ := List.mem_map.1 h
  exact Nat.mod_lt _ hn

/-- The wants of group number i are the i-th declared opening's: its width; positions inside its
depth. -/
theorem want_at (F : ℕ) : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    (∀ d ∈ ds, d.stored = []) → ∀ (i : ℕ) (grp : List Want) (w : Want),
    (groupsOf F ds Rs)[i]? = some grp → w ∈ grp →
    ∃ y, (opensWith ds Rs)[i]? = some y ∧ w.2.2 = y.1.1.W ∧ w.2.1 < 2 ^ y.1.1.a
  | [], _, _, i, grp, w, h, _ => by simp [groupsOf] at h
  | _ :: _, [], _, i, grp, w, h, _ => by simp [groupsOf] at h
  | d :: ds, R :: Rs, hst, i, grp, w, h, hw => by
    rw [groupsOf_cons] at h
    have hl : (grp1 F d R).length = d.opens.length := by
      rw [grp1_length, hst d List.mem_cons_self]
      simp
    show ∃ y, (d.opens.map (fun o => (o, R.poss)) ++ opensWith ds Rs)[i]? = some y ∧ _
    by_cases hi : i < d.opens.length
    · rw [List.getElem?_append_left (by rw [hl]; exact hi)] at h
      rw [List.getElem?_append_left (by rw [List.length_map]; exact hi)]
      unfold grp1 at h
      rw [hst d List.mem_cons_self, List.map_nil, List.nil_append, List.getElem?_map] at h
      obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
      refine ⟨(o, R.poss), by rw [List.getElem?_map, ho]; rfl, rfl, ?_⟩
      exact listOf_lt _ _ _ (Nat.pow_pos (by decide)) hx
    · rw [List.getElem?_append_right (by rw [hl]; omega), hl] at h
      rw [List.getElem?_append_right (by rw [List.length_map]; omega), List.length_map]
      exact want_at F ds Rs (fun x hx => hst x (List.mem_cons_of_mem _ hx)) _ grp w h hw

theorem opensWith_map : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn), ds.length = Rs.length →
    (opensWith ds Rs).map (·.1) = ds.flatMap (·.opens)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | d :: ds, R :: Rs, h => by
    show (d.opens.map (fun o => (o, R.poss)) ++ opensWith ds Rs).map (·.1) = _
    rw [List.map_append, List.map_map, opensWith_map ds Rs (by simpa using h), List.flatMap_cons]
    congr 1
    exact List.map_id' _

/-- The first k + 3 rounds are the fold's cut and the switch's. -/
theorem take_cut (l : Laid) (k : ℕ) : (l.map (·.1)).take (k + 3) = cutF l k ++ cutS l k := by
  unfold cutF cutS
  rw [← List.map_append, ← List.map_take]
  congr 1
  rw [show k + 3 = (1 + k) + 2 by omega, List.take_add]

theorem one_at {α β : Type} (L : List (α × β)) (o0 : α) (i : ℕ) (y : α × β)
    (hm : L.map (·.1) = [o0]) (hy : L[i]? = some y) : y.1 = o0 := by
  have h1 : (L.map (·.1))[i]? = some y.1 := by rw [List.getElem?_map, hy]; rfl
  rw [hm] at h1
  cases i with
  | zero => exact (Option.some.inj h1).symm
  | succ i => simp at h1

/-- The wants of rounds that declare one opening o0 alone have its width, at positions inside its
depth. -/
theorem want_one (F : ℕ) (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn)
    (hst : ∀ d ∈ ds, d.stored = []) (hlen : ds.length = Rs.length) (o0 : Fmt.Shape × Fmt.TreeSource)
    (h1 : ds.flatMap (·.opens) = [o0]) (i : ℕ) (grp : List Want) (w : Want)
    (h : (groupsOf F ds Rs)[i]? = some grp) (hw : w ∈ grp) : w.2.2 = o0.1.W ∧ w.2.1 < 2 ^ o0.1.a :=
        by
  obtain ⟨y, hy, a1, a2⟩ := want_at F ds Rs hst i grp w h hw
  have e := one_at _ o0 i y ((opensWith_map ds Rs hlen).trans h1) hy
  rw [e] at a1 a2
  exact ⟨a1, a2⟩

theorem colW_fits (d : PQ.RD) (o : (wRound d).Orc) (sh : Fmt.Shape) (hd : d.tree = some sh) (x : ℕ)
    (hx : x < 2 ^ sh.a) : (colW d o x).length = sh.W := by
  rw [colW_length d o x (by rw [hd]; exact hx), hd]
  rfl

theorem kk_st (s : Sg) : kk s.st = s.h + s.g := by
  show s.h + (s.h + s.g - s.h) = s.h + s.g
  omega

/-- From a stage j ≥ 1 on: at the written view every want is met in width. c: the chain from that
stage on, over the written rounds w; d: the written round that sent the stage's tree: it sends the
shape that the stage's one opening declares. -/
theorem wideFrom (p : P12) (F : ℕ) : ∀ {s : Sg} (c : OnBytes.Slice.Chain s) (j : ℕ) (cur :
    Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (l : Laid) (w : List WR), stagesOf c = cur :: rest →
    c.rds = w.map WR.rd → j ≠ 0 → Dealt p j cur rest l → TiedW j cur rest l w →
    ∀ (d : PQ.RD) (o0 : Fmt.Shape × Fmt.TreeSource), (cutN cur rest l).flatMap (·.opens) = [o0] →
    d.tree = some o0.1 → ∀ (o : (wRound d).Orc) (b : c.Bl) (Rs : List Fmt.Drawn),
    (l.map (·.1)).length = Rs.length → (∀ x ∈ l.map (·.1), x.stored = []) →
    ∀ (i : ℕ) (grp : List Want) (wt : Want), (groupsOf F (l.map (·.1)) Rs)[i]? = some grp →
    wt ∈ grp → (srcFrom c d o b l i wt.2.1).length = wt.2.2 := by
  intro s c
  induction c with
  | last s e dL dB fu fs εb =>
    intro j cur rest l w hs _ _ _ _ d o0 h1 hd o b Rs hlen hst i grp wt hg hw
    obtain ⟨_, rfl⟩ := List.cons.inj (show [s.st] = cur :: rest from hs)
    have h1' : (l.map (·.1)).flatMap (·.opens) = [o0] := h1
    obtain ⟨a1, a2⟩ := want_one F _ Rs hst hlen o0 h1' i grp wt hg hw
    show (colW d o wt.2.1).length = _
    rw [colW_fits d o o0.1 hd _ a2, a1]
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    intro j cur rest l w hs hr hj hD hT d o0 h1 hd o b Rs hlen hst i grp wt hg hw
    obtain ⟨rfl, hrest⟩ := List.cons.inj (show s.st :: stagesOf next = cur :: rest from hs)
    cases hn : stagesOf next with
    | nil =>
      exfalso
      cases next <;> cases hn
    | cons nxt rest' =>
      rw [hn] at hrest
      subst hrest
      obtain ⟨d1, d2, d3⟩ := hD
      obtain ⟨⟨dSw, o1, t1, t2, t3⟩, t4⟩ := hT
      obtain ⟨oc, hoc⟩ := d2 hj
      have hk : s.st.k = s.h + s.g := rfl
      rw [kk_st] at t1 t4
      rw [hk] at d1 d3 t2 t4 hoc
      -- The stage's one opening is o0
      have hcut : cutN s.st (nxt :: rest') l = cutS l (s.h + s.g) := rfl
      rw [hcut] at h1
      have hnS : nOpen (cutS l (s.h + s.g)) = 1 := hoc.nOpen
      -- The written "SEND seed"
      have hdS : dS = dSw.rd := by
        have hfl : (foldRds s dE dT).length = 1 + (s.h + s.g) := by
          simp [foldRds]
          omega
        have h3 : (foldRds s dE dT ++ ([dS, dC] ++ next.rds))[1 + (s.h + s.g)]? = some dS := by
          rw [List.getElem?_append_right (by rw [hfl]), hfl, Nat.sub_self]
          rfl
        have hr' : foldRds s dE dT ++ ([dS, dC] ++ next.rds) = w.map WR.rd := hr
        rw [hr', List.getElem?_map, t1] at h3
        exact (Option.some.inj h3).symm
      have hnext : next.rds = (w.drop (s.h + s.g + 3)).map WR.rd := by
        have hr' : foldRds s dE dT ++ ([dS, dC] ++ next.rds) = w.map WR.rd := hr
        rw [List.map_drop, ← hr']
        have hl : (foldRds s dE dT ++ [dS, dC]).length = s.h + s.g + 3 := by simp [foldRds]
        rw [← List.append_assoc, ← hl, List.drop_left]
      show (if i < nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)) then colW d o wt.2.1
        else srcFrom next dS b.2.1.1.1 b.2.2 (l.drop (s.h + s.g + 3))
          (i - (nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)))) wt.2.1).length = _
      have hsum : nOpen ((l.map (·.1)).take (s.h + s.g + 3)) =
          nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)) := by
        rw [take_cut, nOpen_append]
      by_cases hi : i < nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g))
      · rw [if_pos hi]
        have hg' : (groupsOf F ((l.map (·.1)).take (s.h + s.g + 3)) (Rs.take (s.h + s.g + 3)))[i]?
            = some grp := by
          rw [← groupsOf_take F _ Rs _ hlen, List.getElem?_take, if_pos (by rw [hsum]; exact hi)]
          exact hg
        have hop : ((l.map (·.1)).take (s.h + s.g + 3)).flatMap (·.opens) = [o0] := by
          rw [take_cut, List.flatMap_append, h1]
          have hz : (cutF l (s.h + s.g)).flatMap (·.opens) = [] := by
            have hstF : ∀ x ∈ cutF l (s.h + s.g), x.stored = [] := fun x hx =>
              hst x (by
                have : x ∈ (l.map (·.1)).take (s.h + s.g + 3) := by
                  rw [take_cut]; exact List.mem_append_left _ hx
                exact List.mem_of_mem_take this)
            have := nOpen_of_flat _ hstF
            rw [d1] at this
            exact List.eq_nil_of_length_eq_zero this.symm
          rw [hz]
          rfl
        obtain ⟨a1, a2⟩ := want_one F _ _ (fun x hx => hst x (List.mem_of_mem_take hx))
          (by rw [List.length_take, List.length_take, hlen]) o0 hop i grp wt hg' hw
        rw [colW_fits d o o0.1 hd _ a2, a1]
      · rw [if_neg hi]
        have hg' : (groupsOf F ((l.drop (s.h + s.g + 3)).map (·.1)) (Rs.drop (s.h + s.g + 3)))[
            i - (nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)))]? = some grp := by
          rw [List.map_drop, ← groupsOf_drop F _ Rs _ hlen, List.getElem?_drop, hsum,
            Nat.add_sub_cancel' (by omega)]
          exact hg
        exact ih (j + 1) nxt rest' (l.drop (s.h + s.g + 3)) (w.drop (s.h + s.g + 3)) hn hnext
          (Nat.succ_ne_zero j) d3 t4 dS o1 t2 (by rw [hdS]; exact t3) b.2.1.1.1 b.2.2
          (Rs.drop (s.h + s.g + 3)) (by rw [List.map_drop, List.length_drop, List.length_drop,
              hlen])
          (fun x hx => hst x (by rw [List.map_drop] at hx; exact List.mem_of_mem_drop hx)) _ grp wt
          hg' hw

/-- The whole test behind "BAT": at the written view every want is met in width. hfirst: the first
switch's i-th declared opening against the i-th of the trees ts. -/
theorem wideFirst (p : P12) (F : ℕ) {s : Sg} (c : OnBytes.Slice.Chain s) (cur : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (l : Laid) (w : List WR) (hs : stagesOf c = cur :: rest)
    (hr : c.rds = w.map WR.rd) (hD : Dealt p 0 cur rest l) (hT : TiedW 0 cur rest l w)
    (ts : List ℕ) (gT : ℕ → ℕ → List UInt64)
    (hfirst : ∀ (i : ℕ) (o : Fmt.Shape × Fmt.TreeSource) (x : ℕ),
      ((cutS l cur.k).flatMap (·.opens))[i]? = some o → x < 2 ^ o.1.a →
      (gT (ts.getD i 0) x).length = o.1.W)
    (b : c.Bl) (Rs : List Fmt.Drawn) (hlen : (l.map (·.1)).length = Rs.length)
    (hst : ∀ x ∈ l.map (·.1), x.stored = []) (i : ℕ) (grp : List Want) (wt : Want)
    (hg : (groupsOf F (l.map (·.1)) Rs)[i]? = some grp) (hw : wt ∈ grp) :
    (srcFirst c b l ts gT i wt.2.1).length = wt.2.2 := by
  cases c with
  | last s e dL dB fu fs εb =>
    obtain ⟨_, rfl⟩ := List.cons.inj (show [s.st] = cur :: rest from hs)
    exact absurd rfl hD.1
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next =>
    obtain ⟨rfl, hrest⟩ := List.cons.inj (show s.st :: stagesOf next = cur :: rest from hs)
    cases hn : stagesOf next with
    | nil =>
      exfalso
      cases next <;> cases hn
    | cons nxt rest' =>
      rw [hn] at hrest
      subst hrest
      obtain ⟨d1, _, d3⟩ := hD
      obtain ⟨⟨dSw, o1, t1, t2, t3⟩, t4⟩ := hT
      have hk : s.st.k = s.h + s.g := rfl
      rw [kk_st] at t1 t4
      rw [hk] at d1 d3 t2 t4 hfirst
      have hfl : (foldRds s dE dT).length = 1 + (s.h + s.g) := by
        simp [foldRds]
        omega
      have hdS : dS = dSw.rd := by
        have h3 : (foldRds s dE dT ++ ([dS, dC] ++ next.rds))[1 + (s.h + s.g)]? = some dS := by
          rw [List.getElem?_append_right (by rw [hfl]), hfl, Nat.sub_self]
          rfl
        have hr' : foldRds s dE dT ++ ([dS, dC] ++ next.rds) = w.map WR.rd := hr
        rw [hr', List.getElem?_map, t1] at h3
        exact (Option.some.inj h3).symm
      have hnext : next.rds = (w.drop (s.h + s.g + 3)).map WR.rd := by
        have hr' : foldRds s dE dT ++ ([dS, dC] ++ next.rds) = w.map WR.rd := hr
        rw [List.map_drop, ← hr']
        have hl : (foldRds s dE dT ++ [dS, dC]).length = s.h + s.g + 3 := by simp [foldRds]
        rw [← List.append_assoc, ← hl, List.drop_left]
      show (if i < nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)) then
          gT (ts.getD (i - nOpen (cutF l (s.h + s.g))) 0) wt.2.1
        else srcFrom next dS b.2.1.1.1 b.2.2 (l.drop (s.h + s.g + 3))
          (i - (nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)))) wt.2.1).length = _
      have hsum : nOpen ((l.map (·.1)).take (s.h + s.g + 3)) =
          nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)) := by
        rw [take_cut, nOpen_append]
      by_cases hi : i < nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g))
      · rw [if_pos hi, d1, Nat.sub_zero]
        have hg' : (groupsOf F ((l.map (·.1)).take (s.h + s.g + 3)) (Rs.take (s.h + s.g + 3)))[i]?
            = some grp := by
          rw [← groupsOf_take F _ Rs _ hlen, List.getElem?_take, if_pos (by rw [hsum]; exact hi)]
          exact hg
        have hop : ((l.map (·.1)).take (s.h + s.g + 3)).flatMap (·.opens) =
            (cutS l (s.h + s.g)).flatMap (·.opens) := by
          rw [take_cut, List.flatMap_append]
          have hz : (cutF l (s.h + s.g)).flatMap (·.opens) = [] := by
            have hstF : ∀ x ∈ cutF l (s.h + s.g), x.stored = [] := fun x hx =>
              hst x (by
                have : x ∈ (l.map (·.1)).take (s.h + s.g + 3) := by
                  rw [take_cut]; exact List.mem_append_left _ hx
                exact List.mem_of_mem_take this)
            have := nOpen_of_flat _ hstF
            rw [d1] at this
            exact List.eq_nil_of_length_eq_zero this.symm
          rw [hz]
          rfl
        obtain ⟨y, hy, a1, a2⟩ := want_at F _ _ (fun x hx => hst x (List.mem_of_mem_take hx)) i grp
            wt
          hg' hw
        have hy' : ((cutS l (s.h + s.g)).flatMap (·.opens))[i]? = some y.1 := by
          rw [← hop, ← opensWith_map _ _ (by rw [List.length_take, List.length_take, hlen]),
            List.getElem?_map, hy]
          rfl
        rw [hfirst i y.1 _ hy' a2, a1]
      · rw [if_neg hi]
        have hg' : (groupsOf F ((l.drop (s.h + s.g + 3)).map (·.1)) (Rs.drop (s.h + s.g + 3)))[
            i - (nOpen (cutF l (s.h + s.g)) + nOpen (cutS l (s.h + s.g)))]? = some grp := by
          rw [List.map_drop, ← groupsOf_drop F _ Rs _ hlen, List.getElem?_drop, hsum,
            Nat.add_sub_cancel' (by omega)]
          exact hg
        exact wideFrom p F next 1 nxt rest' (l.drop (s.h + s.g + 3)) (w.drop (s.h + s.g + 3)) hn
            hnext
          (Nat.succ_ne_zero 0) d3 t4 dS o1 t2 (by rw [hdS]; exact t3) b.2.1.1.1 b.2.2
          (Rs.drop (s.h + s.g + 3)) (by rw [List.map_drop, List.length_drop, List.length_drop,
              hlen])
          (fun x hx => hst x (by rw [List.map_drop] at hx; exact List.mem_of_mem_drop hx)) _ grp wt
          hg' hw

/-- gpOk's clause opens.W, as a proposition: here it is spent. -/
theorem opens_W_of_ok (p : P12) (a : Fmt.M1.Stage) (row : GroupRow) (D : Plain)
    (h : ok (gpL p a row D) = true) : D.opens.map (·.1.W) = D.ts.map (widthAt D.book) := by
  unfold ok gpL at h
  dsimp only at h
  rw [List.all_append, Bool.and_eq_true] at h
  have ht := h.2
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at ht
  exact ht.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The first switch's i-th declared opening against the i-th of the book's trees D.ts: a written
tree as deep and as wide as the book's meets the declared width at every position inside the
declared depth. -/
theorem first_fits (p : P12) (t : T12) (a : Fmt.M1.Stage) (row : GroupRow) (L : GroupLayout)
    (D : Plain) (hD : gpOf p t a L = some D) (hok : ok (gpL p a row D) = true) (W : ℕ → WO)
    (hW : ∀ z ∈ D.ts, PQ.posN (W z).1.tree = 2 ^ logAt D.book z ∧
      PQ.colW (W z).1.tree = widthAt D.book z)
    (i : ℕ) (o : Fmt.Shape × Fmt.TreeSource) (x : ℕ)
    (ho : ((cutS (laidS p) a.k).flatMap (·.opens))[i]? = some o) (hx : x < 2 ^ o.1.a) :
    (colW (W (D.ts.getD i 0)).1 (W (D.ts.getD i 0)).2 x).length = o.1.W := by
  have ho' : D.opens[i]? = some o := by
    rw [(made_of p t a L D hD).opens, ← opensOf_cut]
    exact ho
  have ha := congrArg (·[i]?) (opens_a_of_ok p a row D hok)
  have hWd := congrArg (·[i]?) (opens_W_of_ok p a row D hok)
  simp only [List.getElem?_map, ho', Option.map_some] at ha hWd
  cases hz : D.ts[i]? with
  | none =>
    rw [hz] at ha
    cases ha
  | some z =>
    rw [hz] at ha hWd
    have e1 : o.1.a = logAt D.book z := Option.some.inj ha
    have e2 : o.1.W = widthAt D.book z := Option.some.inj hWd
    have hget : D.ts.getD i 0 = z := by rw [List.getD_eq_getElem?_getD, hz]; rfl
    obtain ⟨w1, w2⟩ := hW z (List.mem_of_getElem? hz)
    rw [hget, colW_length _ _ _ (by rw [w1, ← e1]; exact hx), w2, e2]

/-- The step's second line at the written view: kpw_colsOf's premise. Under the block's test on the
plan, dealOk and tieOk (tests on the plan), for the place's chain c over the written rounds, and
hfirst (first_fits): every want of the test's declared groups is met in width by the written columns
that srcK deals. R0 :: Rs: what the test's rounds drew. -/
theorem view_wide {T Cl : Type} (X : Parts T) (p : P12) (hp : (proximityTestKind X p : Block T Cl).planOk = true)
    (F : ℕ) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hs : p.nums.stages = a :: rest)
    (hdeal : dealOk p = true) (htie : tieOk p = true) {s : Sg} (c : OnBytes.Slice.Chain s)
    (hst : stagesOf c = p.nums.stages) (w0 : WR) (w : List WR)
    (hw : writtenOf p.nums = some (w0 :: w)) (hr : c.rds = w.map WR.rd) (ts : List ℕ)
    (gT : ℕ → ℕ → List UInt64)
    (hfirst : ∀ (i : ℕ) (o : Fmt.Shape × Fmt.TreeSource) (x : ℕ),
      ((cutS (laidS p) a.k).flatMap (·.opens))[i]? = some o → x < 2 ^ o.1.a →
      (gT (ts.getD i 0) x).length = o.1.W)
    (b : c.Bl) (R0 : Fmt.Drawn) (Rs : List Fmt.Drawn) (hlen : (laidS p).length = Rs.length)
    (i : ℕ) (grp : List Want) (wt : Want)
    (hg : (groupsOf F (proximityTestKind X p : Block T Cl).rounds (R0 :: Rs))[i]? = some grp) (hwt : wt ∈ grp) :
    (srcK p c b ts gT i wt.2.1).length = wt.2.2 := by
  rw [H2K.Sw.k12_rounds X p hp] at hg
  obtain ⟨w0', w', hw', hbat, _, hT⟩ := tied_of_ok p a rest hs htie
  obtain ⟨rfl, rfl⟩ := List.cons.inj (Option.some.inj (hw.symm.trans hw'))
  have hD := dealt_of_ok p a rest hs hdeal
  have hstored : ∀ x ∈ (laidOf p).map (·.1), x.stored = [] := by
    intro d hd
    unfold laidOf at hd
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
    cases hrn : H2U.roundsOfNums p.nums with
    | none =>
      rw [hrn] at hx
      simp at hx
    | some rds =>
      rw [hrn] at hx
      exact roundsOfNums_stored _ rds hrn _ (List.of_mem_zip hx).1
  unfold srcK
  rw [hbat, if_neg (Nat.not_lt_zero _), Nat.sub_zero]
  cases hlo : laidOf p with
  | nil =>
    rw [hlo] at hg
    simp [groupsOf] at hg
  | cons x0 l' =>
    have hlS : laidS p = l' := by
      unfold laidS
      rw [hlo]
      rfl
    rw [hlo] at hg hbat hstored
    rw [List.map_cons, groupsOf_cons] at hg
    have h0 : grp1 F x0.1 R0 = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [grp1_length]
      have : nOpen [x0.1] = 0 := hbat
      rw [nOpen_cons] at this
      omega
    rw [h0, List.nil_append, ← hlS] at hg
    exact wideFirst p F c a rest (laidS p) w (hst.trans hs) hr hD hT ts gT hfirst b Rs
      (by rw [List.length_map]; exact hlen)
      (fun x hx => hstored x (by rw [hlS] at hx; exact List.mem_cons_of_mem _ hx)) i grp wt hg hwt

/-- DeepK's letters at the transcripts b: at each of the book's trees D.ts the written tree is as
deep and as wide as the book's. -/
theorem deep_at (p : P12) (t : T12) (a : Fmt.M1.Stage) (L : GroupLayout) (D : Plain)
    (hm : Made p t a L D) {s : Sg} (c : OnBytes.Slice.Chain s) (W0 : ℕ → WO) (fM : H2K.Pub.Msg1 c →
        WO)
    (hK : DeepK D W0 fM) (b : c.Bl) (z : ℕ) (hz : z ∈ D.ts) :
    PQ.posN (wAt c W0 D.fresh.t fM b z).1.tree = 2 ^ logAt D.book z ∧
      PQ.colW (wAt c W0 D.fresh.t fM b z).1.tree = widthAt D.book z := by
  unfold wAt
  by_cases e : z = D.fresh.t
  · subst e
    rw [Function.update_self, (keyAt_of (F := 0) hm.fresh).2]
    exact ⟨hK.fresh _, hK.wide.2 _⟩
  · rw [Function.update_of_ne e]
    refine ⟨?_, hK.wide.1 z hz e⟩
    rw [hm.ts, Fmt.listOf_mem, List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | hz
    · obtain ⟨m, hmem, rfl⟩ := List.mem_map.1 hz
      obtain ⟨i, rfl⟩ := List.get_of_mem hmem
      rw [(keyAt_of (F := 0) (hm.mem i).2).2]
      exact hK.mems i
    · exact absurd hz e

/-- The same at the lemma's own letters: W0, fM under DeepK; the plain data D of the record t behind
the batching. -/
theorem view_wide_deep {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) (F : ℕ) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hs : p.nums.stages = a :: rest) (hdeal : dealOk p = true)
    (htie : tieOk p = true) {s : Sg} (c : OnBytes.Slice.Chain s) (hst : stagesOf c = p.nums.stages)
        (w0 : WR)
    (w : List WR) (hw : writtenOf p.nums = some (w0 :: w)) (hr : c.rds = w.map WR.rd) (t : T12)
    (row : GroupRow) (L : GroupLayout) (D : Plain) (hD : gpOf p t a L = some D)
    (hok : ok (gpL p a row D) = true) (W0 : ℕ → WO) (fM : H2K.Pub.Msg1 c → WO)
    (hK : DeepK D W0 fM) (b : c.Bl) (R0 : Fmt.Drawn) (Rs : List Fmt.Drawn)
    (hlen : (laidS p).length = Rs.length) (i : ℕ) (grp : List Want) (wt : Want)
    (hg : (groupsOf F (proximityTestKind X p : Block T Cl).rounds (R0 :: Rs))[i]? = some grp) (hwt : wt ∈ grp) :
    (srcK p c b D.ts (fun z x => colW (wAt c W0 D.fresh.t fM b z).1 (wAt c W0 D.fresh.t fM b z).2 x)
      i wt.2.1).length = wt.2.2 :=
  view_wide X p hp F a rest hs hdeal htie c hst w0 w hw hr D.ts _
    (first_fits p t a row L D hD hok (wAt c W0 D.fresh.t fM b)
      (deep_at p t a L D (made_of p t a L D hD) c W0 fM hK b)) b R0 Rs hlen i grp wt hg hwt

end H2K.First
