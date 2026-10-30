-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/EqTailProofs.lean: THE SMALLNESS TEST: the proof of the statement of
Johnson/Desc/K8/Honest/EqTailReturns.lean: the text of the list "K8.equations" behind its first four
claims returns, under premises on numbers, flags, marks and lengths and one test on values. Lemmas;
none of the library's goals.

By the rules of Johnson/Desc/First/TailClaims/RetRules.lean and the three laws of
Johnson/Desc/K8/Honest/EqReturnsProofs.lean.
  `laidBy_length`, `laidBy_snoc`   claims laid for a list, and one more
  `push_append`, `numbersFrom_succ`, `allDistinct_of_nodup`, `numbersFrom_apart`   lists
  `tabAt_same`, `markLoop_same`, `markRead_same`, `readReady_same`   what reads numbers that the
                     weights' step keeps has one value in front of it and behind
  `tieReady_of_laid`   behind the weights' step every matrix is ready for its tie
  `ReadsAt`            the reads' loops: what holds with the reads l still to come
  `readStep`           one read
  `eqTail_returns`
The limits are those of Johnson/Desc/K8/Honest/EqTailReturns.lean.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.EqTailReturns
import Johnson.Desc.K8.Honest.EqReturnsProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (St Ret eqTail)
open OnBytes.Tie.Pv.Tail.Port (readsList segsOf)

/-! ## Lists -/

theorem laidBy_length {α : Type} (R : Nat → α → Claim → Prop) : ∀ (q : Nat) (l : List α)
    (cs : List Claim), LaidBy R q l cs → cs.length = l.length
  | _, [], [], _ => rfl
  | q, _ :: l, _ :: cs, h => by
    simp only [List.length_cons]
    rw [laidBy_length R (q + 1) l cs h.2]
  | _, [], _ :: _, h => h.elim
  | _, _ :: _, [], h => h.elim

/-- One member and one claim more, at the end. -/
theorem laidBy_snoc {α : Type} (R : Nat → α → Claim → Prop) (x : α) (c : Claim) : ∀ (q : Nat)
    (l : List α) (cs : List Claim), LaidBy R q l cs → R (q + l.length) x c →
    LaidBy R q (l ++ [x]) (cs ++ [c])
  | _, [], [], _, hx => ⟨hx, trivial⟩
  | q, _ :: l, _ :: cs, h, hx =>
    ⟨h.1, laidBy_snoc R x c (q + 1) l cs h.2 (by
      have e : q + 1 + l.length = q + (l.length + 1) := by omega
      rw [e]
      exact hx)⟩
  | _, [], _ :: _, h, _ => h.elim
  | _, _ :: _, [], h, _ => h.elim

theorem push_append (a : Array Claim) (l : List Claim) (c : Claim) :
    (a ++ l.toArray).push c = a ++ (l ++ [c]).toArray := by
  apply Array.toList_inj.1
  simp

theorem numbersFrom_succ (a n : Nat) : numbersFrom a (n + 1) = (numbersFrom a n).push (a + n) := by
  unfold numbersFrom
  apply Array.toList_inj.1
  simp [List.range_succ]

theorem allDistinct_of_nodup : ∀ l : List Nat, l.Nodup → allDistinct l = true
  | [], _ => rfl
  | x :: t, h => by
    have h' := List.nodup_cons.1 h
    unfold HTailF2.allDistinct
    rw [allDistinct_of_nodup t h'.2]
    simp [h'.1]

theorem numbersFrom_apart (a n : Nat) : allDistinct (numbersFrom a n).toList = true := by
  apply allDistinct_of_nodup
  show ((List.range n).map (a + ·)).Nodup
  exact List.Nodup.map (fun x y h => by omega) List.nodup_range

theorem append_append (a : Array Claim) (l m : List Claim) :
    a ++ l.toArray ++ m.toArray = a ++ (l ++ m).toArray := by
  apply Array.toList_inj.1
  simp

/-! ## In front of the weights' step and behind -/

theorem tabAt_same {a b : HTailF2} (h : unlaid a = unlaid b) (Fn : HFun) (c sg : Nat) :
    a.tabAt Fn c sg = b.tabAt Fn c sg := kept_num h fun t => t.tabAt Fn c sg

theorem markLoop_same {a b : HTailF2} (h : unlaid a = unlaid b) (Fn : HFun) (sg t0 : Nat) :
    ∀ (count c : Nat) (m : Array Bool),
      a.markLoop Fn sg t0 count c m = b.markLoop Fn sg t0 count c m
  | 0, _, _ => by
    unfold HTailF2.markLoop
    rfl
  | count + 1, c, m => by
    unfold HTailF2.markLoop
    rw [tabAt_same h]
    cases b.tabAt Fn c sg with
    | none => rfl
    | some pos =>
      dsimp only
      rw [markLoop_same h Fn sg t0 count]

theorem markRead_same {a b : HTailF2} (h : unlaid a = unlaid b) (Fn : HFun) (sg : Nat)
    (rd : Array (Array Bool)) : a.markRead Fn sg rd = b.markRead Fn sg rd := by
  have e1 : a.tabFirst = b.tabFirst := kept_num h (·.tabFirst)
  have e2 : a.mats = b.mats := kept_num h (·.mats)
  unfold HTailF2.markRead
  dsimp only
  rw [e1, e2, markLoop_same h]

theorem readReady_same {a b : HTailF2} (h : unlaid a = unlaid b) {F : Fork} {Fn : HFun}
    {sg tU : Nat} (r : ReadReady b F Fn sg tU) : ReadReady a F Fn sg tU := by
  have e1 : a.ix.U = b.ix.U := kept_num h (·.ix.U)
  have e2 : a.NM = b.NM := kept_num h (·.NM)
  have e3 : a.mats = b.mats := kept_num h (·.mats)
  have e4 : segs a Fn = segs b Fn := by
    unfold segs
    rw [e3]
  exact ⟨by rw [e1]; exact r.unit, r.cols, by rw [e2]; exact r.mat, r.len,
    by rw [e4]; exact r.seg, by rw [e3, e4]; exact r.row⟩

/-- Behind the weights' step every matrix is ready for its tie. -/
theorem tieReady_of_laid {tl tl' : HTailF2} (hL : Laid tl tl') (ho : oneRow tl = true) (mu : Nat)
    (hmu : mu < tl.NM) (hk : (tl.shp.getD mu {}).k = (tl.mats.getD mu {}).k)
    (hm : 0 < (tl.mats.getD mu {}).m) : TieReady tl' mu := by
  have e1 : tl'.shp = tl.shp := kept_num hL.rest (·.shp)
  have e2 : tl'.NM = tl.NM := kept_num hL.rest (·.NM)
  have e3 : tl'.mats = tl.mats := kept_num hL.rest (·.mats)
  have h1 := List.all_eq_true.1 ho mu (List.mem_range.2 hmu)
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  obtain ⟨⟨⟨⟨hJ, _⟩, _⟩, hRr⟩, _⟩ := h1
  have hs : mu < tl.shp.size := by
    by_cases hq : mu < tl.shp.size
    · exact hq
    · exfalso
      have : tl.shp.getD mu {} = {} := by
        simp [Array.getD_eq_getD_getElem?, hq]
      rw [this] at hJ
      exact absurd hJ (by decide)
  exact ⟨by rw [e1, hL.rowX mu hs, hRr], by rw [e1, hL.loX mu hs, hJ],
    by rw [e1, hL.gamX mu hmu, hk], by rw [e2]; exact hmu, by rw [e3]; exact hm⟩

/-! ## The reads' loops -/

/-- What holds in the reads' loops with the reads l still to come. b: how many are laid, and the
marks. c1: the claims in front of the reads. rd: the marks behind all. -/
def ReadsAt (tl' : HTailF2) (funs : Array HFun) (F : Fork) (c1 : Array Claim)
    (rd : Array (Array Bool)) (l : List (HFun × Nat)) (b : MProd Nat (Array (Array Bool)))
    (s : St) : Prop :=
  ∃ (done : List (HFun × Nat)) (reads : List Claim), done ++ l = readsList tl' funs ∧
    s = (F, c1 ++ reads.toArray) ∧
    LaidBy (fun q x c => ∃ tU, ReadClaim tl' F x.1 x.2 q tU c) 0 done reads ∧
    b.fst = done.length ∧ l.foldlM (fun rd x => tl'.markRead x.1 x.2 rd) b.snd = some rd

/-- One read: its marks are set, its claim is laid. -/
theorem readStep {tl' : HTailF2} {funs : Array HFun} {F : Fork} {c1 : Array Claim}
    {rd : Array (Array Bool)} (hr : ∀ x ∈ readsList tl' funs, ∃ tU, ReadReady tl' F x.1 x.2 tU)
    (hv : ∀ x ∈ readsList tl' funs, LiveAt tl' x) (front : Nat) (sums : E) {Fn : HFun} {sg : Nat}
    {l : List (HFun × Nat)} {b : MProd Nat (Array (Array Bool))} {s : St}
    (h : ReadsAt tl' funs F c1 rd ((Fn, sg) :: l) b s) :
    ∃ rd', tl'.markRead Fn sg b.snd = some rd' ∧
      Ret (eqRead tl' Fn sg b.fst sums) front s fun _ s' =>
        ReadsAt tl' funs F c1 rd l ⟨b.fst + 1, rd'⟩ s' := by
  obtain ⟨done, reads, e, rfl, hl, hb, hm⟩ := h
  rw [List.foldlM_cons] at hm
  obtain ⟨rd', h1, h2⟩ := Option.bind_eq_some_iff.1 hm
  have hx : (Fn, sg) ∈ readsList tl' funs := by
    rw [← e]
    simp
  obtain ⟨tU, hR⟩ := hr _ hx
  obtain ⟨c, ec, hc⟩ := eqRead_returns tl' Fn sg b.fst tU sums front F (c1 ++ reads.toArray) hR
    (hv (Fn, sg) hx)
  refine ⟨rd', h1, Ret.intro ec ⟨done ++ [(Fn, sg)], reads ++ [c], by simp [← e], ?_, ?_, ?_, h2⟩⟩
  · rw [push_append]
  · refine laidBy_snoc _ _ _ 0 done reads hl ⟨tU, ?_⟩
    rw [Nat.zero_add, ← hb]
    exact hc
  · simp [hb]

/-! ## The whole -/

theorem eqTail_returns : Spec.eqTail_returns := by
  intro before front tl funs F cs rd s1 s3 h hv
  obtain ⟨tl', eW, hL⟩ := eqWeights_returns tl front F cs h.drawn h.plan h.one h.fresh
  have hNM : tl'.NM = tl.NM := kept_num hL.rest (·.NM)
  have hmats : tl'.mats = tl.mats := kept_num hL.rest (·.mats)
  have hgt : tl'.gtTree = tl.gtTree := kept_num hL.rest (·.gtTree)
  have hlen : tl'.tabLen = tl.tabLen := kept_num hL.rest (·.tabLen)
  have hU : tl'.ix.U = tl.ix.U := kept_num hL.rest (·.ix.U)
  have hrl : readsList tl' funs = readsList tl funs := kept_num hL.rest fun t => readsList t funs
  have ht1 : tl'.tablesTile funs 0 = some s1 :=
    (kept_num hL.rest fun t => t.tablesTile funs 0).trans h.tile1
  have ht3 : tl'.tablesTile funs 2 = some s3 :=
    (kept_num hL.rest fun t => t.tablesTile funs 2).trans h.tile3
  have hready : ∀ x ∈ readsList tl' funs, ∃ tU, ReadReady tl' F x.1 x.2 tU := fun x hx => by
    obtain ⟨tU, r⟩ := h.reads x (by rw [← hrl]; exact hx)
    exact ⟨tU, readReady_same hL.rest r⟩
  have hlive : ∀ x ∈ readsList tl' funs, LiveAt tl' x := fun x hx =>
    hv tl' eW x (by rw [← hrl]; exact hx)
  have hmarks : (readsList tl' funs).foldlM (fun rd x => tl'.markRead x.1 x.2 rd)
      (tl'.tabLen.map fun n => Array.replicate n false) = some rd := by
    have e : (fun (rd : Array (Array Bool)) (x : HFun × Nat) => tl'.markRead x.1 x.2 rd) =
        fun rd x => tl.markRead x.1 x.2 rd := by
      funext rd x
      exact markRead_same hL.rest _ _ _
    rw [e, hrl, hlen]
    exact h.marks
  unfold eqTail
  refine Ret.bind (Ret.claims (Q := fun n s₁ => n = front + cs.size ∧ s₁ = (F, cs)) ⟨rfl, rfl⟩) ?_
  rintro _ _ ⟨rfl, rfl⟩
  refine Ret.bind (Ret.mustAs _ (by rw [h.four]; rfl) (Q := fun _ s₁ => s₁ = (F, cs)) rfl) ?_
  rintro _ _ rfl
  refine Ret.bind (Ret.intro eW (Q := fun a s₁ => tl' = a ∧ s₁ = (F, cs)) ⟨rfl, rfl⟩) ?_
  rintro _ _ ⟨rfl, rfl⟩
  refine Ret.bind (Ret.ask _ rfl (Q := fun n s₁ => n = F.trees.size ∧ s₁ = (F, cs)) ⟨rfl, rfl⟩) ?_
  rintro _ _ ⟨rfl, rfl⟩
  -- one tie for each matrix
  refine Ret.bind (Ret.forInList
    (I := fun rest (b : MProd (Array Nat) (Array Nat)) s₁ =>
      ∃ (done : List Nat) (ties : List Claim), done ++ rest = List.range tl'.NM ∧
        s₁ = (F, cs ++ ties.toArray) ∧ LaidBy (fun _ mu c => TieClaim tl' mu c) 0 done ties ∧
        b.fst = numbersFrom (front + cs.size) done.length ∧
        b.snd = done.foldl (fun a mu => a.modify (tl'.gtTree.getD mu 0) (· + 1))
          (Array.replicate F.trees.size 0)) ?_ _ _ _
    ⟨[], [], rfl, by simp, trivial, rfl, rfl⟩) ?_
  · rintro mu rest b s₁ ⟨done, ties, e, rfl, hl, hb1, hb2⟩
    have hmu : mu < tl.NM := by
      have : mu ∈ List.range tl'.NM := by
        rw [← e]
        simp
      rw [hNM] at this
      exact List.mem_range.1 this
    obtain ⟨hk, hm⟩ := h.fits mu hmu
    obtain ⟨c, ec, hc⟩ := eqTie_returns tl' mu front F (cs ++ ties.toArray)
      (tieReady_of_laid hL h.one mu hmu hk hm)
    dsimp only
    refine Ret.bind (Ret.claims (Q := fun n s₂ =>
      n = front + (cs ++ ties.toArray).size ∧ s₂ = (F, cs ++ ties.toArray)) ⟨rfl, rfl⟩) ?_
    rintro _ _ ⟨rfl, rfl⟩
    refine Ret.bind (Ret.intro ec (Q := fun _ s₂ => s₂ = (F, (cs ++ ties.toArray).push c)) rfl) ?_
    rintro _ _ rfl
    refine Ret.bind (Ret.pure _ (Q := fun _ s₂ => s₂ = (F, (cs ++ ties.toArray).push c)) rfl) ?_
    rintro _ _ rfl
    refine Ret.pure _ ⟨_, rfl, done ++ [mu], ties ++ [c], by simp [← e], by rw [push_append],
      laidBy_snoc _ _ _ 0 done ties hl hc, ?_, ?_⟩
    · show b.fst.push _ = _
      have hlen' := laidBy_length _ 0 done ties hl
      have hsz : (cs ++ ties.toArray).size = cs.size + done.length := by simp [hlen']
      rw [hb1, List.length_append, List.length_singleton, numbersFrom_succ, hsz, Nat.add_assoc]
    · show b.snd.modify _ _ = _
      rw [hb2, List.foldl_append]
      rfl
  rintro bT _ ⟨doneT, ties, eT, rfl, hlT, hT1, hT2⟩
  rw [List.append_nil] at eT
  subst eT
  -- the reads
  refine Ret.bind (Ret.forInList
    (I := fun rest (b : MProd Nat (Array (Array Bool))) s₁ => (∀ mu ∈ rest, mu < tl'.NM) ∧
      ReadsAt tl' funs F (cs ++ ties.toArray) rd
        (rest.flatMap fun mu => [0, 2].flatMap fun un => funs.toList.flatMap (segsOf tl' mu un))
        b s₁) ?_ _ _ _
    ⟨fun mu hmu => List.mem_range.1 hmu, [], [], rfl, by simp, trivial, rfl, hmarks⟩) ?_
  · rintro mu rest b s₁ ⟨hmem, hP⟩
    have hmu : mu < tl'.NM := hmem mu (by simp)
    dsimp only
    refine Ret.bind (Ret.forInList
      (I := fun rest₂ (b₂ : MProd Nat (Array (Array Bool))) s₂ => (∀ un ∈ rest₂, un = 0 ∨ un = 2) ∧
        ReadsAt tl' funs F (cs ++ ties.toArray) rd
          (rest₂.flatMap (fun un => funs.toList.flatMap (segsOf tl' mu un)) ++
            rest.flatMap fun mu => [0, 2].flatMap fun un =>
              funs.toList.flatMap (segsOf tl' mu un)) b₂ s₂) ?_ _ _ _
      ⟨by simp, by rw [List.flatMap_cons] at hP; exact hP⟩) ?_
    · rintro un rest₂ b₂ s₂ ⟨hun, hP₂⟩
      have hun0 : un = 0 ∨ un = 2 := hun un (by simp)
      dsimp only
      refine Ret.bind (Ret.forInArray
        (I := fun rest₃ (b₃ : MProd Nat (Array (Array Bool))) s₃ =>
          (∀ Fn ∈ rest₃, Fn ∈ funs.toList) ∧
          ReadsAt tl' funs F (cs ++ ties.toArray) rd
            (rest₃.flatMap (segsOf tl' mu un) ++
              (rest₂.flatMap (fun un => funs.toList.flatMap (segsOf tl' mu un)) ++
                rest.flatMap fun mu => [0, 2].flatMap fun un =>
                  funs.toList.flatMap (segsOf tl' mu un))) b₃ s₃) ?_ funs _ _
        ⟨fun _ hq => hq, by rw [List.flatMap_cons, List.append_assoc] at hP₂; exact hP₂⟩) ?_
      · rintro Fn rest₃ b₃ s₃ ⟨hFn, hP₃⟩
        rw [List.flatMap_cons, List.append_assoc] at hP₃
        dsimp only
        refine Ret.ite _ (fun hc => ?_) fun hc => ?_
        · have hc' := hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc'
          obtain ⟨hFm, hFt⟩ := hc'
          obtain ⟨t1, t2, t3, t4⟩ := h.table Fn (hFn Fn (by simp)) (by rw [hFm, ← hNM]; exact hmu)
            (by rw [hFt]; exact hun0)
          rw [segsOf, if_pos hc] at hP₃
          refine Ret.bind (Ret.mustAs _ (by rw [hU, ← hFt]; exact t1)
            (Q := fun _ s₄ => s₃ = s₄) rfl) ?_
          rintro _ _ rfl
          refine Ret.bind (Ret.mustAs _ (by
            rw [hmats, ← hFm]
            simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
            exact ⟨⟨t2, t3⟩, t4⟩) (Q := fun _ s₄ => s₃ = s₄) rfl) ?_
          rintro _ _ rfl
          refine Ret.bind (Ret.forInList
            (I := fun rest₄ (b₄ : MProd Nat (Array (Array Bool))) s₄ =>
              ReadsAt tl' funs F (cs ++ ties.toArray) rd
                (rest₄.map (fun sg => (Fn, sg)) ++ (rest₃.flatMap (segsOf tl' mu un) ++
                  (rest₂.flatMap (fun un => funs.toList.flatMap (segsOf tl' mu un)) ++
                    rest.flatMap fun mu => [0, 2].flatMap fun un =>
                      funs.toList.flatMap (segsOf tl' mu un)))) b₄ s₄) ?_ _ _ _ hP₃) ?_
          · rintro sg rest₄ b₄ s₄ hP₄
            rw [List.map_cons, List.cons_append] at hP₄
            obtain ⟨rd', hm, hR⟩ := readStep hready hlive front
              (mulE (sumE Fn.phi) (sumE tl'.vt)) hP₄
            dsimp only
            refine Ret.bind (Ret.get _ hm (Q := fun r s₅ => rd' = r ∧ s₄ = s₅) ⟨rfl, rfl⟩) ?_
            rintro _ _ ⟨rfl, rfl⟩
            refine Ret.bind hR ?_
            intro _ s₅ hP₅
            refine Ret.bind (Ret.pure _ (Q := fun _ s₆ => s₅ = s₆) rfl) ?_
            rintro _ _ rfl
            exact Ret.pure _ ⟨_, rfl, hP₅⟩
          rintro b₄ s₄ hP₄
          simp only [List.map_nil, List.nil_append] at hP₄
          refine Ret.bind (Ret.pure _ (Q := fun _ s₅ => s₄ = s₅) rfl) ?_
          rintro _ _ rfl
          exact Ret.pure _ ⟨_, rfl, fun G hG => hFn G (by simp [hG]), hP₄⟩
        · rw [segsOf, if_neg hc, List.nil_append] at hP₃
          refine Ret.bind (Ret.pure _ (Q := fun _ s₄ => s₃ = s₄) rfl) ?_
          rintro _ _ rfl
          exact Ret.pure _ ⟨_, rfl, fun G hG => hFn G (by simp [hG]), hP₃⟩
      rintro b₃ s₃ ⟨_, hP₃⟩
      rw [List.flatMap_nil, List.nil_append] at hP₃
      refine Ret.bind (Ret.pure _ (Q := fun _ s₄ => s₃ = s₄) rfl) ?_
      rintro _ _ rfl
      exact Ret.pure _ ⟨_, rfl, fun u hu => hun u (by simp [hu]), hP₃⟩
    rintro b₂ s₂ ⟨_, hP₂⟩
    rw [List.flatMap_nil, List.nil_append] at hP₂
    refine Ret.bind (Ret.pure _ (Q := fun _ s₃ => s₂ = s₃) rfl) ?_
    rintro _ _ rfl
    exact Ret.pure _ ⟨_, rfl, fun m hm => hmem m (by simp [hm]), hP₂⟩
  rintro bR _ ⟨_, doneR, reads, eR, rfl, hlR, hR1, hR2⟩
  rw [List.flatMap_nil, List.append_nil] at eR
  subst eR
  obtain rfl : bR.snd = rd := Option.some.inj hR2
  -- the nine tests at the end
  refine Ret.bind (Ret.mustAs _ (by rw [hNM]; exact h.inList) (Q := fun _ s₁ =>
    s₁ = (F, cs ++ ties.toArray ++ reads.toArray)) rfl) ?_
  rintro _ _ rfl
  refine Ret.bind (Ret.mustAs _ h.allSet (Q := fun _ s₁ =>
    s₁ = (F, cs ++ ties.toArray ++ reads.toArray)) rfl) ?_
  rintro _ _ rfl
  refine Ret.bind (Ret.get _ ht1 (Q := fun n s₁ =>
    n = s1 ∧ s₁ = (F, cs ++ ties.toArray ++ reads.toArray)) ⟨rfl, rfl⟩) ?_
  rintro _ _ ⟨rfl, rfl⟩
  refine Ret.bind (Ret.get _ ht3 (Q := fun n s₁ =>
    n = s3 ∧ s₁ = (F, cs ++ ties.toArray ++ reads.toArray)) ⟨rfl, rfl⟩) ?_
  rintro _ _ ⟨rfl, rfl⟩
  refine Ret.bind (Ret.ask _ rfl (Q := fun k s₁ =>
    k = F.trees.map (·.kind) ∧ s₁ = (F, cs ++ ties.toArray ++ reads.toArray)) ⟨rfl, rfl⟩) ?_
  rintro _ _ ⟨rfl, rfl⟩
  have hOn : bT.snd = tiesOnOf tl F.trees.size := by
    rw [hT2, hNM, hgt]
    rfl
  have hObj : bT.fst = numbersFrom (front + cs.size) tl.NM := by
    rw [hT1, List.length_range, hNM]
  have hLaid : bR.fst = (readsList tl funs).length := by rw [hR1, hrl]
  refine Ret.bind (Ret.mustAs _ (by rw [hOn, Array.size_map]; exact h.kinds) (Q := fun _ s₁ =>
    s₁ = (F, cs ++ ties.toArray ++ reads.toArray)) rfl) ?_
  rintro _ _ rfl
  refine Ret.bind (Ret.mustAs _ (by
    rw [hOn, h.sum, hNM, hLaid, h.count]
    simp) (Q := fun _ s₁ => s₁ = (F, cs ++ ties.toArray ++ reads.toArray)) rfl) ?_
  rintro _ _ rfl
  refine Ret.bind (Ret.mustAs _ (by
    rw [hObj, numbersFrom_apart, hgt, h.apart]
    rfl) (Q := fun _ s₁ => s₁ = (F, cs ++ ties.toArray ++ reads.toArray)) rfl) ?_
  rintro _ _ rfl
  refine Ret.pure _ ⟨tl', ties, reads, hL, by rw [hObj, hOn, hLaid], by rw [append_append], ?_, ?_⟩
  · rw [← hNM]
    exact hlT
  · rw [← hrl]
    exact hlR

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.eqTail_returns
#print axioms VerifiableInference.Desc.First.K8.Honest.tieReady_of_laid
#print axioms VerifiableInference.Desc.First.K8.Honest.markRead_same
#print axioms VerifiableInference.Desc.First.K8.Honest.readStep
