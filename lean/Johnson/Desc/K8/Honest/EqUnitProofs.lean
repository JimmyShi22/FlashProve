-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/EqUnitProofs.lean: THE SMALLNESS TEST: the proofs of the three statements of
Johnson/Desc/K8/Honest/EqUnitReturns.lean, and that the run's end with the clause gives the end
without it (statement to statement, all three, is not proved here). Lemmas;
none of the library's goals.

THE THREE PROOFS ARE THOSE OF Johnson/Desc/K8/Honest/EqTailProofs.lean, EqAllProofs.lean AND
EqRunReturns.lean, WRITTEN A SECOND TIME, with the clause on the array carried through the reads'
loops: `ReadsAtU` and `readStepU` are `ReadsAt` and `readStep` with it. The helper lemmas of these
files are called, not written again.
  `laidBy_mono`   claims laid under one relation are laid under a weaker one
  `eqTail_returns_unit`, `eqAll_returns_unit`, `run_returns_unit`
  `behindAll_of_unit`   the end with the clause gives the end without it
The limits are those of Johnson/Desc/K8/Honest/EqUnitReturns.lean.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.EqUnitReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (St Ret OnlySide idxOk keysClaim countsClaims
  eqTail eqAll_split eqRest eqKeys_returns eqCounts_returns tame_counts eqWeights_spec partOf
  sits_equations)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.Look (laidDigits padKeyDigits)
open OnBytes.Tie.Pv.Tail.Port (readsList segsOf gamAt getD_map_range)

/-- Claims laid under one relation are laid under a weaker one. -/
theorem laidBy_mono {α : Type} {R R' : Nat → α → Claim → Prop}
    (h : ∀ q x c, R q x c → R' q x c) : ∀ (q : Nat) (l : List α) (cs : List Claim),
    LaidBy R q l cs → LaidBy R' q l cs
  | _, [], [], _ => trivial
  | q, _ :: l, _ :: cs, hl => ⟨h _ _ _ hl.1, laidBy_mono h (q + 1) l cs hl.2⟩
  | _, [], _ :: _, hl => hl.elim
  | _, _ :: _, [], hl => hl.elim

/-! ## The reads' loops -/

/-- What holds in the reads' loops with the reads l still to come. b: how many are laid, and the
marks. c1: the claims in front of the reads. rd: the marks behind all. -/
def ReadsAtU (tl' : HTailF2) (funs : Array HFun) (F : Fork) (c1 : Array Claim)
    (rd : Array (Array Bool)) (l : List (HFun × Nat)) (b : MProd Nat (Array (Array Bool)))
    (s : St) : Prop :=
  ∃ (done : List (HFun × Nat)) (reads : List Claim), done ++ l = readsList tl' funs ∧
    s = (F, c1 ++ reads.toArray) ∧
    LaidBy (ReadLaid tl' tl' F) 0 done reads ∧
    b.fst = done.length ∧ l.foldlM (fun rd x => tl'.markRead x.1 x.2 rd) b.snd = some rd

/-- One read: its marks are set, its claim is laid. -/
theorem readStepU {tl' : HTailF2} {funs : Array HFun} {F : Fork} {c1 : Array Claim}
    {rd : Array (Array Bool)} (hr : ∀ x ∈ readsList tl' funs, ∃ tU, ReadReady tl' F x.1 x.2 tU)
    (hv : ∀ x ∈ readsList tl' funs, LiveAt tl' x) (front : Nat) (sums : E) {Fn : HFun} {sg : Nat}
    {l : List (HFun × Nat)} {b : MProd Nat (Array (Array Bool))} {s : St}
    (h : ReadsAtU tl' funs F c1 rd ((Fn, sg) :: l) b s) :
    ∃ rd', tl'.markRead Fn sg b.snd = some rd' ∧
      Ret (eqRead tl' Fn sg b.fst sums) front s fun _ s' =>
        ReadsAtU tl' funs F c1 rd l ⟨b.fst + 1, rd'⟩ s' := by
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
  · refine laidBy_snoc _ _ _ 0 done reads hl ⟨tU, hR.unit, ?_⟩
    rw [Nat.zero_add, ← hb]
    exact hc
  · simp [hb]

/-! ## The whole -/

theorem eqTail_returns_unit : Spec.eqTail_returns_unit := by
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
      ReadsAtU tl' funs F (cs ++ ties.toArray) rd
        (rest.flatMap fun mu => [0, 2].flatMap fun un => funs.toList.flatMap (segsOf tl' mu un))
        b s₁) ?_ _ _ _
    ⟨fun mu hmu => List.mem_range.1 hmu, [], [], rfl, by simp, trivial, rfl, hmarks⟩) ?_
  · rintro mu rest b s₁ ⟨hmem, hP⟩
    have hmu : mu < tl'.NM := hmem mu (by simp)
    dsimp only
    refine Ret.bind (Ret.forInList
      (I := fun rest₂ (b₂ : MProd Nat (Array (Array Bool))) s₂ => (∀ un ∈ rest₂, un = 0 ∨ un = 2) ∧
        ReadsAtU tl' funs F (cs ++ ties.toArray) rd
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
          ReadsAtU tl' funs F (cs ++ ties.toArray) rd
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
              ReadsAtU tl' funs F (cs ++ ties.toArray) rd
                (rest₄.map (fun sg => (Fn, sg)) ++ (rest₃.flatMap (segsOf tl' mu un) ++
                  (rest₂.flatMap (fun un => funs.toList.flatMap (segsOf tl' mu un)) ++
                    rest.flatMap fun mu => [0, 2].flatMap fun un =>
                      funs.toList.flatMap (segsOf tl' mu un)))) b₄ s₄) ?_ _ _ _ hP₃) ?_
          · rintro sg rest₄ b₄ s₄ hP₄
            rw [List.map_cons, List.cons_append] at hP₄
            obtain ⟨rd', hm, hR⟩ := readStepU hready hlive front
              (mulE (sumE Fn.phi) (sumE tl'.vt)) hP₄
            dsimp only
            refine Ret.bind (Ret.get _ hm (Q := fun r s₅ => rd' = r ∧ s₄ = s₅) ⟨rfl, rfl⟩) ?_
            rintro _ _ ⟨rfl, rfl⟩
            refine Ret.bind hR ?_
            intro _ s₅ hP₅
            refine Ret.bind (Ret.pure _ (Q := fun _ t => s₅ = t) rfl) ?_
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
    exact laidBy_mono (fun _ _ _ ⟨tU, h1, h2⟩ => ⟨tU, by rw [← hU]; exact h1, h2⟩) _ _ _ hlR

/-! ## The whole list -/

theorem eqAll_returns_unit : Spec.eqAll_returns_unit := by
  intro front tl funs F cs g rd s1 s3 h hheld hzero hlive
  rw [eqAll_split]
  refine Ret.bind (Ret.mustAs _ (by simp [h.closed.1, h.closed.2])
    (Q := fun _ s₁ => s₁ = (F, cs)) rfl) ?_
  rintro _ _ rfl
  refine Ret.bind (Ret.mustAs _ hheld (Q := fun _ s₁ => s₁ = (F, cs)) rfl) ?_
  rintro _ _ rfl
  refine Ret.bind (Ret.ask _ rfl (Q := fun b s₁ =>
    b = (F.LS.extract tl.slotA tl.slotB).all isZeroE ∧ s₁ = (F, cs)) ⟨rfl, rfl⟩) ?_
  rintro _ _ ⟨rfl, rfl⟩
  refine Ret.bind (Ret.testAs _ hzero (Q := fun _ s₁ => s₁ = (F, cs)) rfl) ?_
  rintro _ _ rfl
  refine Ret.bind (Ret.get _ h.heard (Q := fun a s₁ => g = a ∧ s₁ = (F, cs)) ⟨rfl, rfl⟩) ?_
  rintro _ _ ⟨rfl, rfl⟩
  refine Ret.bind (Ret.mustAs _ (by rw [h.rows]; simp) (Q := fun _ s₁ => s₁ = (F, cs)) rfl) ?_
  rintro _ _ rfl
  unfold eqRest
  refine Ret.bind (Ret.claims (Q := fun n s₁ => n = front + cs.size ∧ s₁ = (F, cs)) ⟨rfl, rfl⟩) ?_
  rintro _ _ ⟨rfl, rfl⟩
  refine Ret.bind (eqKeys_returns h.heard h.key h.idx h.laid front F cs) ?_
  rintro _ _ ⟨rfl, c0, rfl, hc0⟩
  refine Ret.bind (Ret.also
    (eqCounts_returns (tl := { tl with joinObj9 := some (front + cs.size) }) (g := g) h.heard
      (open_paid h.leaves g.owedJoin) front (cs.push c0))
    fun a s' e => tame_counts _ front _ s' a e) ?_
  rintro _ ⟨G, c4⟩ ⟨⟨⟨bf, rfl⟩, hled, hsh⟩, hside, new, hnew⟩
  dsimp only at hled hsh hside hnew
  subst hnew
  have hS : OnlySide F G := (side_paid F g.owedJoin).trans hside
  have hnewSh : new.map claimSh = countsClaims tl g := by
    rw [Array.toList_append, List.map_append] at hsh
    exact List.append_cancel_left hsh
  have hlen : (cs.push c0 ++ new.toArray).size = cs.size + 4 := by
    have := congrArg List.length hnewSh
    simp only [List.length_map] at this
    have h3 : (countsClaims tl g).length = 3 := rfl
    simp only [Array.size_append, Array.size_push, List.size_toArray]
    omega
  refine Ret.mono (eqTail_returns_unit (front + cs.size) front _ funs G _ rd s1 s3
    (tailReady_moved (tl := tl) hS (some (front + cs.size)) bf (h.tail _ hlen))
    fun tl' hW x hx => ?_) ?_
  · obtain ⟨_, r⟩ := (h.tail _ hlen).reads x hx
    refine live_of_cols hW x r.mat fun c hc => ?_
    show isZeroE (foldColumn tl.cfF _ tl.tau (powers G.theta tl.tau)) = false
    rw [hS.theta]
    exact hlive x hx c hc
  · rintro _ _ ⟨tl', ties, reads, hL, rfl, rfl, hT, hR⟩
    refine ⟨bf, tl', c0 :: new, ties, reads, hL, ?_, hS, hled, ?_, ?_, hT, hR⟩
    · rw [hlen, hS.trees]
      rfl
    · apply Array.toList_inj.1
      simp
    · rw [List.map_cons, hc0, hnewSh]

/-! ## The run at a state -/

theorem run_returns_unit : Spec.run_returns_unit := by
  intro p run hrun front s q g rd s1 s3 hq hA h1 h2 h3
  obtain ⟨out, ⟨F', c⟩, e, bf, tl', four, ties, reads, a1, a2, a3, a4, a5, a6, a7, a8⟩ :=
    eqAll_returns_unit (q.F.nClaim + front) q.tl q.funs q.F #[] g rd s1 s3 hA h1 h2 h3
  dsimp only at a3 a4 a5 a8
  refine ⟨c.toList, out, F', (sits_equations p run hrun front s _ _).2 ⟨q, out, F', hq, ?_, rfl⟩,
    bf, tl', four, ties, reads, a1, a2, a3, a4, ?_, a6, a7, a8⟩
  · unfold equations
    rw [e]
    rfl
  · rw [a5]
    simp

/-- The end with the clause gives the end without it. -/
theorem behindAll_of_unit {front : Nat} {tl : HTailF2} {funs : Array HFun} {F : Fork}
    {g : Forest.Heard} {out : HTailF2} {F' : Fork} {cls : List Claim}
    (h : BehindAllU front tl funs F g out F' cls) : BehindAll front tl funs F g out F' cls := by
  obtain ⟨bf, tl', four, ties, reads, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  exact ⟨bf, tl', four, ties, reads, a1, a2, a3, a4, a5, a6, a7,
    laidBy_mono (fun _ _ _ ⟨tU, _, h2⟩ => ⟨tU, h2⟩) _ _ _ a8⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.eqTail_returns_unit
#print axioms VerifiableInference.Desc.First.K8.Honest.eqAll_returns_unit
#print axioms VerifiableInference.Desc.First.K8.Honest.run_returns_unit
#print axioms VerifiableInference.Desc.First.K8.Honest.behindAll_of_unit
