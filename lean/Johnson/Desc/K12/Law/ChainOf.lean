-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/ChainOf.lean: wherever `pubOk` says yes, the public premises of the law of the
proximity test (the kind K12) have a member: the place's own chain over its declared rounds.

Definitions, statements and proofs.
Main names:
  `sgOf`, `WR.rd`: the place's stage in the library's form (g := k - h); a plain written round
    (Johnson/Desc/K12/Law/PubOk.lean) as the library's `Run.PQ.RD`, field by field.
  `Letters`: what a chain holds beside stages, rounds and readings: a radius for each stage and the
    blocks' error counts. They are free letters: neither `Chain.Acc` nor `Chain.Pub` reads them, and
    whoever spends the chain in a bound picks them.
  `stepEndX`, `stepMidX`, `chainFrom`: the standard chain over a list of written rounds, which is
    used up to the last round; n0 := Z.l.
  `walk_pub`: the clauses' yes from a stage on gives a chain c of `chainFrom` with c.rds the written
    rounds, `stagesOf c` the stages, `c.Pub`, `c.Own` of the tree that brought the stage, and
    `c.ReadAs` at the standard readings. By recursion on the stages.
  `pub_of_ok`: `pubOk p K = true` gives the place's first stage a, the rest, the written rounds w0
    :: l of the place's declared rounds, and c : Chain (sgOf a) with `chainFrom X rest a l = some
    c`, `c.rds = l.map WR.rd`, `stagesOf c = p.nums.stages` and the clause of `StartK.pub` at K.
  `Letters.std`, `stepMidX_std`, `stepEndX_std`, `chainFrom_last_std`: at the letters of
    OnBytes/Slice/ManyDefs.lean the pieces are `Chain.stepMid`, `Chain.stepEnd` and `Chain.lastStd`,
    by rfl.
Limits: Nothing on the other fields of `StartK` (the rounds; what stands behind). The yes of `pubOk`
is a run's to show: evaluated at the four proximity tests of the two stored example proofs, the
full-size one and the smaller one, with p made of the plan and K the record's codes in front of the
test: true at each, and false at forty controls [the prints are not in this library]. That the
declared rounds are the plan's is the block's comparison of its rounds with the plan's entries. Of
the fold's two rounds `Chain.Pub` asks nothing, and nothing is shown of them here but that the
repeated rounds are one round; `FoldRounds` is shown in Johnson/Desc/K12/Law/ChainSpend.lean. K is a
letter. Nothing on soundness. Nothing on hiding. The proofs call two lemmas of the library on
written rounds: `csRounds_of` and `rBase_sd`, and `Own.treesMade_eq`
(Johnson/Desc/Own/TreesAgree.lean), which turns the test's `Own.treesMade` into the `layTrees` of
which `OneTree` speaks; they reach none of `OnBytes.Ctx`, `OnBytes.Blk`, `OnBytes.Chan`. This is a
statement on the library's chain; that a yes of the block gives the chain's yes is the law of the
kind, under its own premises.

-/
import Johnson.Desc.K12.Law.JointK
import Johnson.Desc.K12.Law.PubOk
import Johnson.Desc.Own.TreesAgree
import OnBytes.Slice.CsMet

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK

/-- The place's stage in the library's form: g := k - h. -/
def sgOf (a : Fmt.M1.Stage) : Sg := ⟨a.C, a.Z, a.h, a.k - a.h, a.t⟩

theorem sgOf_st (a : Fmt.M1.Stage) : (sgOf a).st = stN a := rfl

theorem stN_eq {a : Fmt.M1.Stage} (h : a.h ≤ a.k) : stN a = a := by
  cases a with
  | mk C Z k h' t =>
    show (⟨C, Z, h' + (k - h'), h', t⟩ : Fmt.M1.Stage) = _
    have : h' + (k - h') = k := Nat.add_sub_cancel' h
    rw [this]

/-- A plain written round as the library's. -/
def WR.rd (w : WR) : PQ.RD := ⟨w.entry, w.kind, w.items, w.tree, w.opens⟩

/-- What a chain holds beside its stages, rounds and readings, as letters: a radius for each stage
and the blocks' error counts. Nothing is said of them: neither Chain.Acc nor Chain.Pub reads them.
-/
structure Letters where
  rad : Sg → ℕ
  εb : (s : Sg) → (dL dB : PQ.RD) → Err (PQ.uL (ckP .two) [dL, dB])
  εf : (s : Sg) → (dE dT : PQ.RD) → Err (PQ.uL (ckP .two) (foldRds s dE dT))
  εc : (s s' : Sg) → CsFit s s' → (dS dC : PQ.RD) → Err (PQ.uL (ckP .two) [dS, dC])

theorem ok_cons {x : String × Bool} {l : Clauses} : ok (x :: l) = (x.2 && ok l) := rfl
theorem ok_append (a b : Clauses) : ok (a ++ b) = (ok a && ok b) := by
  unfold ok
  rw [List.all_append]
theorem ok_tag (j : Nat) (l : Clauses) : ok (tag j l) = ok l := by
  unfold ok tag
  rw [List.all_map]
  rfl

theorem csFit_of_B {a b : Fmt.M1.Stage} (h : csFitB a b = true) : CsFit (sgOf a) (sgOf b) := by
  simp only [csFitB, csFitL, ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- A step to the last stage, with ManyDefs.lean's stepEnd's readings. -/
noncomputable def stepEndX (X : Letters) (a b : Fmt.M1.Stage) (hf : CsFit (sgOf a) (sgOf b))
    (dE dT dS dC : WR)
    (next : Chain (sgOf b)) : Chain (sgOf a) :=
  .step (sgOf a) (sgOf b) hf (sgOf a).Z.l (X.rad (sgOf a)) dE.rd dT.rd dS.rd
    dC.rd (fun m => wordIn (sgOf b) (lastColW dS.rd m.1))
    (fun m => wordFr (sgOf b) (lastColW dS.rd m.1))
    (fun m => wordMk (sgOf b) (lastMk dS.rd m.1)) (X.εf (sgOf a) dE.rd dT.rd)
    (X.εc (sgOf a) (sgOf b) hf dS.rd dC.rd) next

/-- A step to a stage that is not the last, with ManyDefs.lean's stepMid's readings. -/
noncomputable def stepMidX (X : Letters) (a b : Fmt.M1.Stage) (hf : CsFit (sgOf a) (sgOf b))
    (dE dT dS dC : WR)
    (next : Chain (sgOf b)) : Chain (sgOf a) :=
  .step (sgOf a) (sgOf b) hf (sgOf a).Z.l (X.rad (sgOf a)) dE.rd dT.rd dS.rd
    dC.rd (fun m => wordIn (sgOf b) (colSt (sgOf b) dS.rd m.1))
    (fun m => wordFr (sgOf b) (colSt (sgOf b) dS.rd m.1))
    (fun m => wordIn (sgOf b) (colSt (sgOf b) dS.rd m.1)) (X.εf (sgOf a) dE.rd dT.rd)
    (X.εc (sgOf a) (sgOf b) hf dS.rd dC.rd) next

/-- **The standard chain over written rounds**: the readings of ManyDefs.lean's lastStd | stepMid |
stepEnd; n0 := Z.l. rest: the stages behind a. l: the written rounds, used up to the last. Nothing
where the rounds cannot be cut so or CsFit fails. -/
noncomputable def chainFrom (X : Letters) : (rest : List Fmt.M1.Stage) → (a : Fmt.M1.Stage) → List
    WR →
    Option (Chain (sgOf a))
  | [], a, l =>
    match l with
    | [dL, dB] =>
      some (.last (sgOf a) (X.rad (sgOf a)) dL.rd dB.rd (fun m => lst (sentW dL.rd m) 0)
        (fun m => shownW (sgOf a) (sentW dB.rd m)) (X.εb (sgOf a) dL.rd dB.rd))
    | _ => none
  | b :: rest, a, l =>
    match l with
    | dE :: dT :: l' =>
      if h : csFitB a b = true ∧ (dT :: l').take (kk a) = List.replicate (kk a) dT then
        match (dT :: l').drop (kk a) with
        | dS :: dC :: l'' =>
          (chainFrom X rest b l'').map fun next =>
            if rest.isEmpty then stepEndX X a b (csFit_of_B h.1) dE dT dS dC next
            else stepMidX X a b (csFit_of_B h.1) dE dT dS dC next
        | _ => none
      else none
    | _ => none

/-! ## From a clause's yes to the library's proposition -/

theorem code_of_B {x : Option OnBytes.Code} {c : Fmt.M1.Code} (h : codeB x c = true) :
    x = some ⟨c.a, c.l, c.r⟩ := of_decide_eq_true h

theorem isRd_of_B {w : WR} {r : Fmt.Round} (h : isRdB w r = true) : IsRd w.rd r := by
  simp only [isRdB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem colW_rd (w : WR) : PQ.colW w.rd.tree = colWB w.tree := by
  cases w with
  | mk e k i t o => cases t <;> rfl

theorem posN_rd (w : WR) : PQ.posN w.rd.tree = posNB w.tree := by
  cases w with
  | mk e k i t o => cases t <;> rfl

theorem stageCodes_of {K : Codes} {a : Fmt.M1.Stage} {i : Nat × Nat} (hk : a.h ≤ a.k)
    (hC : K.base[i.1]? = some ⟨a.C.a, a.C.l, a.C.r⟩)
        (hZ : K.mask[i.2]? = some ⟨a.Z.a, a.Z.l, a.Z.r⟩) :
    StageCodes (sgOf a) (ioOf i a) K where
  base := ⟨_, hC, rfl⟩
  mask := by
    show codeOf (K.mask.getD i.2 default) = a.Z
    rw [Array.getD_eq_getD_getElem?, hZ]
    rfl
  k := (Nat.add_sub_cancel' hk).symm
  h := rfl

theorem oneTree_of_B {K : Codes} {sent : Array OracleNotice} {n : Nat}
    (h : oneTreeB K sent n = true) : OneTree K sent n := by
  intro lay hl
  unfold oneTreeB at h
  rw [VerifiableInference.Desc.Own.treesMade_eq, hl] at h
  dsimp only at h
  split at h
  · rename_i sh hs
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
    refine ⟨sh, ?_, h.1.1.1, fun i hi => h.1.1.2 i hi, h.1.2, h.2⟩
    rw [← Array.toList_inj, hs]
  · cases h

theorem lastLay_of_B {K : Codes} {cu : IoppStage} {a : Fmt.M1.Stage} (h : lastLayB K cu a = true) :
    ∀ lay, layTrees K (sentLast cu a) = some lay →
      ∃ shT : TreeShape, lay.shapes = #[shT] ∧ shT.logN = a.C.a ∧
        (∀ i, i < 2 → lay.tree.getD i 0 = 0 ∧ lay.part.getD i 0 = i) ∧
        shT.mainSymbols = #[3, 3] ∧ shT.maskSymbols = #[3, 3] := by
  intro lay hl
  unfold lastLayB at h
  rw [VerifiableInference.Desc.Own.treesMade_eq, hl] at h
  dsimp only at h
  split at h
  · rename_i sh hs
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
    refine ⟨sh, ?_, h.1.1.1, fun i hi => h.1.1.2 i hi, h.1.2, h.2⟩
    rw [← Array.toList_inj, hs]
  · cases h

theorem stepOwn_of {K : Codes} {a : Fmt.M1.Stage} {cu : IoppStage} {d : WR}
    (h : ok (ownL K a cu false d) = true) : StepOwn K (sgOf a) cu d.rd := by
  simp only [ownL, ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq, Bool.false_eq_true, if_false] at h
  exact ⟨h.1, (colW_rd d).trans h.2.1, oneTree_of_B h.2.2⟩

theorem lastOwn_of {K : Codes} {a : Fmt.M1.Stage} {cu : IoppStage} {d : WR}
    (h : ok (ownL K a cu true d) = true) : LastOwn K (sgOf a) cu d.rd := by
  simp only [ownL, ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq, if_true] at h
  exact ⟨h.1, h.2.1, (colW_rd d).trans h.2.2.1, (posN_rd d).trans h.2.2.2.1,
    lastLay_of_B h.2.2.2.2⟩

theorem stageAt_io {p : P12} {j : Nat} {a : Fmt.M1.Stage} {i : Nat × Nat} (h : p.idx[j]? = some i) :
    stageAt p j a = some (ioOf i a) := by
  unfold stageAt
  rw [h]
  rfl

/-! ## The walk -/

/-- The clauses' yes from the stage number j on gives the standard chain over the written rounds l,
with all that Chain.Pub asks. -/
theorem walk_pub (X : Letters) (p : P12) (K : Codes) : ∀ (rest : List Fmt.M1.Stage) (j : Nat)
    (a : Fmt.M1.Stage)
    (l : List WR) (cu : IoppStage) (restI : List IoppStage),
    ok (walkL p K j a rest l) = true → stageAt p j a = some cu →
    stagesAt p (j + 1) rest = some restI →
    ∃ c : Chain (sgOf a), chainFrom X rest a l = some c ∧ c.rds = l.map WR.rd ∧
      stagesOf c = a :: rest ∧ c.Pub K cu restI ∧
      (∀ d : WR, ok (ownL K a cu rest.isEmpty d) = true → c.Own K cu d.rd) ∧
      (rest = [] → ∀ (d : PQ.RD) (m : (wRound d).Msg) (z : (sgOf a).cFr.Word),
        c.ReadAs d m (wordIn (sgOf a) (lastColW d m.1)) z (wordMk (sgOf a) (lastMk d m.1))) ∧
      (rest ≠ [] → ∀ (d : PQ.RD) (m : (wRound d).Msg) (g : (sgOf a).cIn.Word),
        c.ReadAs d m (wordIn (sgOf a) (colSt (sgOf a) d m.1))
            (wordFr (sgOf a) (colSt (sgOf a) d m.1))
          g)
  | [], j, a, l, cu, restI, h, hcu, hri => by
    unfold walkL at h
    split at h
    · rename_i i dL dB hi
      rw [stageAt_io hi] at hcu
      cases hcu
      cases hri
      rw [ok_tag] at h
      simp only [ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
        decide_eq_true_eq] at h
      obtain ⟨hk, hC, hZ, hza, hsm, hB⟩ := h
      refine ⟨_, rfl, rfl, ?_, ⟨rfl, ?_⟩, fun d hd => lastOwn_of hd, fun _ d m z => ⟨rfl, rfl⟩,
        fun hne => absurd rfl hne⟩
      · show [(sgOf a).st] = [a]
        rw [sgOf_st, stN_eq hk]
      · exact ⟨stageCodes_of hk (code_of_B hC) (code_of_B hZ), hza, hsm,
          ⟨_, rBase_sd (s := (sgOf a).st) (isRd_of_B hB) (le_trans hsm (by decide))⟩,
          fun _ => rfl, fun _ => rfl⟩
    · cases h
  | b :: rest, j, a, l, cu, restI, h, hcu, hri => by
    unfold walkL at h
    split at h
    · rename_i i n dE dT l' hi hn
      split at h
      · rename_i dS dC l'' hd
        rw [stageAt_io hi] at hcu
        cases hcu
        obtain ⟨nxt', rest', later, hr1, hr2, hr3⟩ : ∃ nxt' rest' later, restI = nxt' :: later ∧
            stageAt p (j + 1) b = some nxt' ∧ stagesAt p (j + 1 + 1) rest = some later ∧ rest' =
                rest := by
          unfold stagesAt at hri
          rw [stageAt_io hn] at hri ⊢
          cases hl : stagesAt p (j + 1 + 1) rest with
          | none => simp [hl] at hri
          | some later =>
            simp [hl] at hri
            exact ⟨_, rest, later, hri.symm, rfl, rfl, rfl⟩
        subst hr1
        rw [stageAt_io hn] at hr2
        cases hr2
        rw [ok_append, ok_tag, ok_append, ok_append, ok_append] at h
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨⟨⟨h1, hfit⟩, h2⟩, hown⟩, hw⟩ := h
        simp only [ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
          decide_eq_true_eq] at h1 h2
        obtain ⟨hk, hkb, hcut⟩ := h1
        obtain ⟨hC, hZ, hC', hZ', hsm, hS, hCs, hbits⟩ := h2
        obtain ⟨next, n1, n2, n3, n4, n5, n6, n7⟩ :=
          walk_pub X p K rest (j + 1) b l'' (ioOf n b) later hw (stageAt_io hn) hr3.1
        have hf : CsFit (sgOf a) (sgOf b) := csFit_of_B hfit
        have hl : (dT :: l') = List.replicate (kk a) dT ++ dS :: dC :: l'' := by
          rw [← hcut, ← hd, List.take_append_drop]
        have hpub : StepPub K (sgOf a) (sgOf b) (ioOf i a) (ioOf n b) (sgOf a).Z.l dS.rd dC.rd :=
          { codes := stageCodes_of hk (code_of_B hC) (code_of_B hZ)
            n0 := rfl
            zk := by rw [show (ioOf i a).maskCode = i.2 from rfl, code_of_B hZ]; rfl
            c' := by rw [show (ioOf n b).code = n.1 from rfl, code_of_B hC']; rfl
            z' := by rw [show (ioOf n b).maskCode = n.2 from rfl, code_of_B hZ']; rfl
            small := hsm
            rounds := csRounds_of (s := sgOf a) (s' := sgOf b) (isRd_of_B hS) (isRd_of_B hCs)
              (le_trans hsm (by decide))
            bits := hbits }
        have hrds : ∀ (fW : (wRound dS.rd).Msg → (sgOf b).cIn.Word)
            (fZ : (wRound dS.rd).Msg → (sgOf b).cFr.Word)
                (fG : (wRound dS.rd).Msg → (sgOf b).cIn.Word),
            (Chain.step (sgOf a) (sgOf b) hf (sgOf a).Z.l (X.rad (sgOf a)) dE.rd dT.rd dS.rd dC.rd
                fW fZ
              fG (X.εf (sgOf a) dE.rd dT.rd) (X.εc (sgOf a) (sgOf b) hf dS.rd dC.rd) next).rds
              = (dE :: dT :: l').map WR.rd := by
          intro fW fZ fG
          show dE.rd :: List.replicate (kk a) dT.rd ++ ([dS.rd, dC.rd] ++ next.rds) = _
          rw [n2, hl]
          simp
        have hstg : (sgOf a).st :: stagesOf next = a :: b :: rest := by
          rw [n3, sgOf_st, stN_eq hk]
        have hsome : chainFrom X (b :: rest) a (dE :: dT :: l') =
            some (if rest.isEmpty then stepEndX X a b hf dE dT dS dC next
              else stepMidX X a b hf dE dT dS dC next) := by
          unfold chainFrom
          dsimp only
          rw [dif_pos ⟨hfit, hcut⟩, hd]
          dsimp only
          rw [n1]
          rfl
        by_cases hr : rest = []
        · subst hr
          refine ⟨_, hsome, hrds _ _ _, hstg,
              ⟨_, _, rfl, hpub, n5 dS hown, fun m => n6 rfl dS.rd m _, n4⟩,
            fun d hd' => stepOwn_of hd', fun hne => absurd hne (by simp), fun _ d m g => ⟨rfl, rfl⟩⟩
        · have he : rest.isEmpty = false := by
            cases rest with
            | nil => exact absurd rfl hr
            | cons _ _ => rfl
          rw [he] at hsome
          refine ⟨_, hsome, hrds _ _ _, hstg,
              ⟨_, _, rfl, hpub, n5 dS hown, fun m => n7 hr dS.rd m _, n4⟩,
            fun d hd' => stepOwn_of hd', fun hne => absurd hne (by simp), fun _ d m g => ⟨rfl, rfl⟩⟩
      · cases h
    · cases h

/-- The walk's clauses on idx give the stages' forms. -/
theorem walk_forms (p : P12) (K : Codes) : ∀ (rest : List Fmt.M1.Stage) (j : Nat) (a : Fmt.M1.Stage)
    (l : List WR),
    ok (walkL p K j a rest l) = true →
    ∃ cu restI, stageAt p j a = some cu ∧ stagesAt p (j + 1) rest = some restI
  | [], j, a, l, h => by
    unfold walkL at h
    split at h
    · rename_i i dL dB hi
      exact ⟨_, [], stageAt_io hi, rfl⟩
    · cases h
  | b :: rest, j, a, l, h => by
    unfold walkL at h
    split at h
    · rename_i i n dE dT l' hi hn
      split at h
      · rename_i dS dC l'' hd
        rw [ok_append, Bool.and_eq_true] at h
        obtain ⟨cu', restI', e1, e2⟩ := walk_forms p K rest (j + 1) b l'' h.2
        refine ⟨_, cu' :: restI', stageAt_io hi, ?_⟩
        unfold stagesAt
        rw [e1, e2]
        rfl
      · cases h
    · cases h

/-! ## The top -/

/-- pubOk's yes at a place and at codes K gives the standard chain of the place: over the place's
declared rounds behind "BAT", read as written rounds; with the place's stages; and with StartK.pub's
clause (Top.lean) at K. X: any letters. -/
theorem pub_of_ok (X : Letters) (p : P12) (K : Codes) (h : pubOk p K = true) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      p.nums.stages = a :: rest ∧ writtenOf p.nums = some (w0 :: l) ∧
      chainFrom X rest a l = some c ∧ c.rds = l.map WR.rd ∧ stagesOf c = p.nums.stages ∧
      ∀ (first : Fmt.M1.Stage) (rest' : List Fmt.M1.Stage) (cu : IoppStage)
          (restI : List IoppStage),
        p.nums.stages = first :: rest' → stageAt p 0 first = some cu →
        stagesAt p 1 rest' = some restI → c.Pub K cu restI := by
  unfold pubOk pubL at h
  split at h
  · rename_i a rest w0 l hs hw
    -- the forms of the stages exist, since the walk's clauses on idx hold
    have hex : ∀ (cu : IoppStage) (restI : List IoppStage), stageAt p 0 a = some cu →
        stagesAt p 1 rest = some restI → ∃ c : Chain (sgOf a), chainFrom X rest a l = some c ∧
          c.rds = l.map WR.rd ∧ stagesOf c = a :: rest ∧ c.Pub K cu restI := by
      intro cu restI h1 h2
      obtain ⟨c, c1, c2, c3, c4, _⟩ := walk_pub X p K rest 0 a l cu restI h h1 h2
      exact ⟨c, c1, c2, c3, c4⟩
    obtain ⟨cu0, restI0, e1, e2⟩ := walk_forms p K rest 0 a l h
    obtain ⟨c, c1, c2, c3, _⟩ := hex cu0 restI0 e1 e2
    refine ⟨a, rest, w0, l, c, hs, hw, c1, c2, c3.trans hs.symm, ?_⟩
    intro first rest' cu restI hf h1 h2
    obtain ⟨rfl, rfl⟩ := List.cons.inj (hs.symm.trans hf)
    obtain ⟨c', c1', _, _, c4'⟩ := hex cu restI h1 h2
    obtain rfl := Option.some.inj (c1.symm.trans c1')
    exact c4'
  · cases h

/-! ## The letters of ManyDefs.lean's standard chains: the tie of the readings, by rfl -/

/-- The error counts for lists of one member, at a radius for each stage. -/
noncomputable def Letters.std (rad : Sg → ℕ) : Letters where
  rad := rad
  εb := fun s dL dB => baseErr s (rad s) (rad s + 1) 1 dL dB
  εf := fun s dE dT => foldErr s dE dT (fun _ => 1) (fun _ => rad s + 1) (fun _ => rad s + 1)
    (fun _ => rad s + 1)
  εc := fun s _ hf dS dC => csErr hf (rad s) 1 dS dC

theorem stepMidX_std (rad : Sg → ℕ) (a b : Fmt.M1.Stage) (hf : CsFit (sgOf a) (sgOf b))
    (dE dT dS dC : WR)
    (next : Chain (sgOf b)) : stepMidX (.std rad) a b hf dE dT dS dC next =
      Chain.stepMid (sgOf a) (sgOf b) hf (rad (sgOf a)) dE.rd dT.rd dS.rd dC.rd next := rfl

theorem stepEndX_std (rad : Sg → ℕ) (a b : Fmt.M1.Stage) (hf : CsFit (sgOf a) (sgOf b))
    (dE dT dS dC : WR)
    (next : Chain (sgOf b)) : stepEndX (.std rad) a b hf dE dT dS dC next =
      Chain.stepEnd (sgOf a) (sgOf b) hf (rad (sgOf a)) dE.rd dT.rd dS.rd dC.rd next := rfl

theorem chainFrom_last_std (rad : Sg → ℕ) (a : Fmt.M1.Stage) (dL dB : WR) :
    chainFrom (.std rad) [] a [dL, dB] = some (Chain.lastStd (sgOf a) (rad (sgOf a)) dL.rd dB.rd) :=
        rfl

end H2K.Pub
