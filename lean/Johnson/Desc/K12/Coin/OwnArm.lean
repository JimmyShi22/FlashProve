-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/OwnArm.lean: **THE LAW OF THE PROXIMITY TEST IN THE PLAIN FORM, AT A PLACE
WHOSE FIRST FOLD SENDS ITS OWN MASK.** Definitions, statements and proofs. The second arm of
LawN.lean.

What parts from the first arm. The stretch's own tree number 0 is the mask's, sent by the chain's
first round; the switches' trees are numbers 1, 2, …: `own1` (ownN π = 1) and `TreesOwn` stand for
`own0` and `Chain.Trees`. Of the places D.ts of the book the members' trees were sent in front of
the stretch; the mask's is the stretch's first: `FirstOpensOwn`. The word of fresh mask rows is read
off the chain's own first message (`fMown`), so the library's law is called in the form of
Johnson/Desc/K12/Law/OwnMask.lean (`chain_many_list_own`). The group's word, the promise on the
batching (`BatAtN`) and the conclusion (`QN`) are the first arm's, to the letter.

  `FirstOpensOwn`, `AtPlaceOwn`: the promise's first half and the public premises.
  `fMown`: the mask's tree's columns off the chain's first message, as a written oracle as deep and
    as wide as the book says.
  `first_colsO`, `own_colsO`: the two premises of `follows_of_yes`, paid.
  `yes_accO`: where the piece says yes, the chain says yes in the field at the same transcript.
  `K12LawNO`, `k12_lawNO`: the law.
The text of `k12_lawNO`'s proof was made of `k12_lawN`'s own by a program that turns six places.
Limits: those of Sheet.lean, Law.lean and LawN.lean. NO SOUNDNESS IS CLAIMED. No member of
`AtPlaceOwn` is known.

-/
import Johnson.Desc.K12.Coin.LawN
import Johnson.Desc.K12.Coin.OwnTrees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.JointK H2K.Sw
open H2K.Pub
open H2K.First (gpOf gpL Plain logAt widthAt made_of keyAt_of opensOf_cut opens_a_of_ok
  opens_W_of_ok ownN)

/-- At the statement: the trees that the first switch's openings name are those at the places D.ts
of the book, in turn; the members' were sent in front of the stretch; the mask's is the stretch's
first. -/
def FirstOpensOwn (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (base : ℕ) (t : T12) : Prop :=
  ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
    Fixes π t a rest G0 Ly D →
    D.opens.map (fun o => num o.2) = D.ts.map no ∧ (∀ i, no (D.mems.get i).t < base) ∧
      no D.fresh.t = base

/-- What is public of a place whose first fold sends its own mask, and the facts on codes. -/
structure AtPlaceOwn (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (L mC mS mW : Sg → ℕ → ℕ)
    (rad : Sg → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT) (εt : Err (uLT (ckP .two) dt)) :
    Prop where
  early : π.early = true
  answers : π.answers = 1
  planOk : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true
  spend : spendOk π = true
  deal : H2K.First.dealOk π = true
  codes : CodesAt L mC mS mW rad π.nums.stages
  like : ∃ w0 l, writtenOf π.nums = some (w0 :: l) ∧ List.Forall₂ Like (dB :: dt) (w0 :: l)
  batNone : dB.trees = []
  /-- the test sends one tree beside its switches' -/
  own1 : ownN π = 1
  wants : ∀ Rs,
    wantsOf F.a (⟨F.a, base, F.all, dB :: dt, F.key, F.all⟩ : StageD).depth (dB :: dt) Rs =
      wantsDecl num (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds Rs
  numOwn : ∀ n, num (.own (π.nums.free + n)) = base + n
  trees : ∀ a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), π.nums.stages = a :: rest →
    writtenOf π.nums = some (w0 :: l) → chainFrom (.at L mC mS mW rad) rest a l = some c →
    TreesOwn c
  bears : ∀ a rest w0 l (c : OnBytes.Slice.Chain (sgOf a)), π.nums.stages = a :: rest →
    writtenOf π.nums = some (w0 :: l) → chainFrom (.at L mC mS mW rad) rest a l = some c →
    Bears c.errL εt

/-- The mask's tree off the chain's first message, as deep and as wide as the book says. -/
def fMown {s : Sg} (c : OnBytes.Slice.Chain s) (D : Plain) (m : Msg1 c) : WO :=
  woOf (col1 c m) (logAt D.book D.fresh.t) (widthAt D.book D.fresh.t)

/-- A column of the stretch's own tree number n is the chain's. -/
theorem own_col (F : Frame) (base : ℕ) (dB : RDT) (lo : List (PQ.RD × List ℕ)) (y : F.E.Str)
    (m : (roundT (ckP .two) dB).up.Msg) (c : (roundT (ckP .two) dB).up.Chal)
    (τ : Iop.Tr (uLT (ckP .two) (lo.map mk))) {s : Sg} (ch : OnBytes.Slice.Chain s)
    (hR : ch.rds = lo.map (·.1)) (hbn : dB.trees = []) (n x : ℕ) (col : List UInt64)
    (h : sCol (ckP .two) ⟨F.a, base, F.all, dB :: lo.map mk, F.key, F.all⟩ y (m, c, τ)
      (.tree (base + n) x) = some col) :
    PQ.colAtS (ckP .two) ch.rds
      (ch.trL (blOf ch (castT hR.symm (trW (ckP .two) lo τ)))) n x = some col := by
  have p1' : (if base + n < base then (posL F.all (base + n) x).map y.2
      else colAtST (ckP .two) (dB :: lo.map mk) (m, c, τ) (base + n - base) x) = some col := h
  have hl : dB.trees.length = 0 := by rw [hbn]; rfl
  rw [if_neg (by omega), Nat.add_sub_cancel_left, colAtST_cons,
    if_neg (by rw [hl]; exact Nat.not_lt_zero n), hl, Nat.sub_zero] at p1'
  have p2 : colAtST (ckP .two) (lo.map mk) τ n x = some col := p1'
  rw [trL_blOf, colAtS_cast, ← colAtST_trW]
  exact p2

theorem own_colsO (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (base : ℕ) (dB : RDT)
    (lo : List (PQ.RD × List ℕ)) (y : F.E.Str) (m : (roundT (ckP .two) dB).up.Msg)
    (c : (roundT (ckP .two) dB).up.Chal) (τ : Iop.Tr (uLT (ckP .two) (lo.map mk))) {s : Sg}
    (ch : OnBytes.Slice.Chain s) (hR : ch.rds = lo.map (·.1)) (hT : TreesOwn ch)
    (hown : ownN π = 1) (hnum : ∀ n, num (.own (π.nums.free + n)) = base + n)
    (hbn : dB.trees = []) :
    OwnCols (PCol (ckP .two) ⟨F.a, base, F.all, dB :: lo.map mk, F.key, F.all⟩ y (m, c, τ) num)
      (π.nums.free + (ownN π + 0)) ch (blOf ch (castT hR.symm (trW (ckP .two) lo τ))) := by
  refine ownCols_own _ ch hT _ _ fun k o ho x col hP => ?_
  obtain ⟨p1, _, _⟩ := hP
  have e : π.nums.free + (ownN π + 0) + k = π.nums.free + (k + 1) := by rw [hown]; omega
  rw [ho, e, hnum (k + 1)] at p1
  exact own_col F base dB lo y m c τ ch hR hbn (k + 1) x col p1

theorem first_colsO (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (base : ℕ)
    (dB : RDT) (lo : List (PQ.RD × List ℕ)) (y : F.E.Str) (m : (roundT (ckP .two) dB).up.Msg)
    (c : (roundT (ckP .two) dB).up.Chal) (τ : Iop.Tr (uLT (ckP .two) (lo.map mk))) {s : Sg}
    (ch : OnBytes.Slice.Chain s) (hR : ch.rds = lo.map (·.1)) (hT : TreesOwn ch)
    (hbn : dB.trees = []) (t : T12) (a : Fmt.M1.Stage) (row : GroupRow) (L : GroupLayout)
    (D : Plain) (hD : gpOf π t a L = some D) (hok : H2K.First.ok (gpL π a row D) = true)
    (h1 : D.opens.map (fun o => num o.2) = D.ts.map no) (h2 : ∀ i, no (D.mems.get i).t < base)
    (h3 : no D.fresh.t = base) (i : ℕ) (o : ToldO) (x : ℕ) (col : List UInt64)
    (ho : ((cutS (laidS π) a.k).flatMap (·.opens))[i]? = some o)
    (hP : PCol (ckP .two) ⟨F.a, base, F.all, dB :: lo.map mk, F.key, F.all⟩ y (m, c, τ) num o x
      col) :
    col = colW
      (wAt ch (W0 F no D.book y) D.fresh.t (fMown ch D)
        (blOf ch (castT hR.symm (trW (ckP .two) lo τ))) (D.ts.getD i 0)).1
      (wAt ch (W0 F no D.book y) D.fresh.t (fMown ch D)
        (blOf ch (castT hR.symm (trW (ckP .two) lo τ))) (D.ts.getD i 0)).2 x := by
  have hm := made_of π t a L D hD
  have ho' : D.opens[i]? = some o := by
    rw [hm.opens, ← opensOf_cut]
    exact ho
  have ha := congrArg (·[i]?) (opens_a_of_ok π a row D hok)
  have hWd := congrArg (·[i]?) (opens_W_of_ok π a row D hok)
  have hn := congrArg (·[i]?) h1
  simp only [List.getElem?_map, ho', Option.map_some] at ha hWd hn
  cases hz : D.ts[i]? with
  | none =>
    rw [hz] at ha
    cases ha
  | some z =>
    rw [hz] at ha hWd hn
    have e1 : o.1.a = logAt D.book z := Option.some.inj ha
    have e2 : o.1.W = widthAt D.book z := Option.some.inj hWd
    have e3 : num o.2 = no z := Option.some.inj hn
    have hget : D.ts.getD i 0 = z := by rw [List.getD_eq_getElem?_getD, hz]; rfl
    obtain ⟨p1, p2, p3⟩ := hP
    rw [hget, e3] at *
    unfold wAt
    by_cases hzf : z = D.fresh.t
    · subst hzf
      rw [Function.update_self]
      rw [h3] at p1
      have q := own_col F base dB lo y m c τ ch hR hbn 0 x col p1
      exact (colW_woOf _ _ _ x col (by rw [← e1]; exact p3) (col1_zero ch hT _ x col q).symm
        (by rw [← e2]; exact p2)).symm
    · rw [Function.update_of_ne hzf]
      have hzm : z ∈ D.mems.map (·.t) := by
        have hzt := List.mem_of_getElem? hz
        rw [hm.ts, Fmt.listOf_mem, List.mem_append, List.mem_singleton] at hzt
        exact hzt.resolve_right hzf
      obtain ⟨mm, hmem, rfl⟩ := List.mem_map.1 hzm
      obtain ⟨j, rfl⟩ := List.get_of_mem hmem
      refine (colW_woIn F y (no (D.mems.get j).t) _ _ x col (by rw [← e1]; exact p3) ?_
        (by rw [← e2]; exact p2)).symm
      have p1' : (if no (D.mems.get j).t < base then (posL F.all (no (D.mems.get j).t) x).map y.2
          else colAtST (ckP .two) (dB :: lo.map mk) (m, c, τ) (no (D.mems.get j).t - base) x) =
          some col := p1
      rw [if_pos (h2 j)] at p1'
      unfold colIn
      rw [p1']
      rfl

theorem yes_accO {W : Type} (F : Frame) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (lo : List (PQ.RD × List ℕ)) (e₀ : ℕ) (εt : Err (uLT (ckP .two) (lo.map mk)))
    (hA : AtPlaceOwn F π num L mC mS mW rad base dB (lo.map mk) εt) (w0 : WR) (l : List WR)
    (hw : writtenOf π.nums = some (w0 :: l)) (hB : Like dB w0) (hlo : lo.map (·.1) = l.map WR.rd)
    (x : T12 × F.E.Str) (hfo : FirstOpensOwn π num no base x.1)
    (m : (roundT (ckP .two) dB).up.Msg) (c : (roundT (ckP .two) dB).up.Chal)
    (τ : Iop.Tr (uLT (ckP .two) (lo.map mk))) (b : T12 × F.E.Str)
    (hb : (pieceT F W π base dB (lo.map mk) e₀ εt).ior.red.out x (m, c, τ) = some b) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (ch : OnBytes.Slice.Chain (sgOf a))
      (hR : ch.rds = lo.map (·.1)) (G0 : Group) (Ly : GroupLayout) (D : Plain) (row : GroupRow)
      (hok : H2K.First.ok (gpL π a row D) = true),
      chainFrom (.at L mC mS mW rad) rest a l = some ch ∧ Fixes π x.1 a rest G0 Ly D ∧
      pubOk π x.1.st.codes = true ∧
      First.Close.bat x.1.st x.1.g dB.entry (noDigest (r0Of dB m c)) =
        .ok (row, Ly, begun x.1.st x.1.g G0) ∧
      ch.Acc (stmG (sgOf a) row) (yOf π a row D hok rd (W0 F no D.book x.2))
        (zOf π a row D hok rd (W0 F no D.book x.2)
          (fMown ch D (msg1 ch (blOf ch (castT hR.symm (trW (ckP .two) lo τ))))))
        (fun _ _ => 0) (blOf ch (castT hR.symm (trW (ckP .two) lo τ))) ∧
      PQ.passSL (ckP .two) ch.rds
        (PQ.rhoSL (ckP .two) ch.rds (castT hR.symm (trW (ckP .two) lo τ))) = true := by
  obtain ⟨ht, k, hst, hdrop⟩ :=
    yes_step (pieceT F W π base dB (lo.map mk) e₀ εt) rfl x (m, c, τ) b hb
  have hst' : (proximityTestKind guardedProximityTestParts π : Blk').step F.ft x.1 (rvT (ckP .two) (dB :: lo.map mk) (m, c, τ))
      (sView (ckP .two) ⟨F.a, base, F.all, dB :: lo.map mk, F.key, F.all⟩ x.2 (m, c, τ)).opened =
      .ok (b.1, k) := hst
  have hdrop' : (sView (ckP .two) ⟨F.a, base, F.all, dB :: lo.map mk, F.key, F.all⟩ x.2
      (m, c, τ)).opened.drop k = [] := hdrop
  rw [step_k hst'] at hdrop'
  obtain ⟨hfit, hcols, hdec⟩ := Prox.step_ok F.ft _ x.1 b.1 _ _ k hst'
  obtain ⟨a, rest, w0', l', ch, e1, e2, e3, e4, e5, e, r, row, Ly, S', G0, g1, g2, g3, g4, g5, D,
    hok, g6, g7⟩ := k12_step_accH (.at L mC mS mW rad) π hA.early hA.answers x.1 hA.planOk F.ft b.1
      _ _ k hst'
  obtain ⟨rfl, rfl⟩ := List.cons.inj (Option.some.inj (e2.symm.trans hw))
  have hR : ch.rds = lo.map (·.1) := e4.trans hlo.symm
  subst g5
  have hfix : Fixes π x.1 a rest G0 Ly D := ⟨e1, g3, g4, fun _ => g6⟩
  obtain ⟨f1, f2, f3⟩ := hfo a rest G0 Ly D hfix
  obtain ⟨_, hpub, _⟩ := k12_guards π hA.early x.1 b.1 _ _ hA.planOk hdec
  obtain ⟨r', row', L', S'', q1, q2⟩ := k12_bat_entry π x.1 b.1 _ _ hA.planOk hdec w0' l' hw
  have hr : r' = r := by
    rw [g1] at q1
    exact (List.cons.inj q1).1.symm
  subst hr
  cases bat_unique _ _ _ _ _ _ _ g2 q2
  have hr0 : r' = noDigest (r0Of dB m c) := by
    have h1 : ((rvT (ckP .two) (dB :: lo.map mk) (m, c, τ)).map noDigest).take 1 =
        [noDigest (r0Of dB m c)] := rfl
    rw [g1] at h1
    exact (List.cons.inj h1).1
  rw [hr0, ← hB.1] at q2
  have hm := made_of π _ a Ly D g6
  have hTr := hA.trees a rest w0' l' ch e1 hw e3
  have hWm : ∀ i, wAt ch (W0 F no D.book x.2) D.fresh.t (fMown ch D)
      (blOf ch (castT hR.symm (trW (ckP .two) lo τ))) (D.mems.get i).t =
      W0 F no D.book x.2 (D.mems.get i).t := by
    intro i
    unfold wAt
    refine Function.update_of_ne (fun h => ?_) _ _
    have := f2 i
    rw [h, f3] at this
    exact Nat.lt_irrefl _ this
  have hWf : wAt ch (W0 F no D.book x.2) D.fresh.t (fMown ch D)
      (blOf ch (castT hR.symm (trW (ckP .two) lo τ))) D.fresh.t =
      fMown ch D (msg1 ch (blOf ch (castT hR.symm (trW (ckP .two) lo τ)))) := by
    unfold wAt
    rw [Function.update_self]
  refine ⟨a, rest, ch, hR, G0, Ly, D, row, hok, e3, hfix, hpub, q2, ?_, ?_⟩
  · have hacc := g7 rd
      (fun z => (wAt ch (W0 F no D.book x.2) D.fresh.t (fMown ch D)
        (blOf ch (castT hR.symm (trW (ckP .two) lo τ))) z).1)
      (fun z => (wAt ch (W0 F no D.book x.2) D.fresh.t (fMown ch D)
        (blOf ch (castT hR.symm (trW (ckP .two) lo τ))) z).2)
      (fun i => by
        show PQ.posN (wAt ch (W0 F no D.book x.2) D.fresh.t (fMown ch D)
          (blOf ch (castT hR.symm (trW (ckP .two) lo τ))) (D.mems.get i).t).1.tree = _
        rw [hWm i]
        show 2 ^ logAt D.book (D.mems.get i).t = _
        rw [(keyAt_of (F := 0) (hm.mem i).2).2])
      (by
        show PQ.posN (wAt ch (W0 F no D.book x.2) D.fresh.t (fMown ch D)
          (blOf ch (castT hR.symm (trW (ckP .two) lo τ))) D.fresh.t).1.tree = _
        rw [hWf]
        show 2 ^ logAt D.book D.fresh.t = _
        rw [(keyAt_of (F := 0) hm.fresh).2])
      (fun _ _ => 0) (blOf ch (castT hR.symm (trW (ckP .two) lo τ)))
      (by
        show (rvT (ckP .two) (lo.map mk) τ).map noDigest = _
        rw [← rvSL_trL ch, trL_blOf, rvSL_cast, rvT_trW])
      (follows_of_yes F π num base (dB :: lo.map mk) hA.planOk hA.deal a rest e1 ch e5 x.2 (m, c, τ)
        hA.wants hfit hcols hdrop' D.ts _
        (first_colsO F π num no base dB lo x.2 m c τ ch hR hTr hA.batNone _ a row Ly D g6 hok f1 f2
          f3) _
        (own_colsO F π num base dB lo x.2 m c τ ch hR hTr hA.own1 hA.numOwn hA.batNone))
    unfold yOf zOf
    exact acc_congr ch _ _ _
      (congrArg _ (funext fun j => ofOrc_congr _ _ (hWm j))) (frOf_congr _ _ _ hWf) hacc
  · rw [pass_cast, pass_trW]
    have h1 : (passT (ckP .two) (dB :: lo.map mk) (rhoT (ckP .two) (dB :: lo.map mk) (m, c, τ)) &&
        fullOf (dB :: lo.map mk) (drawnT (ckP .two) (dB :: lo.map mk)
          (rhoT (ckP .two) (dB :: lo.map mk) (m, c, τ))) &&
        sCarries ⟨F.a, base, F.all, dB :: lo.map mk, F.key, F.all⟩ x.2
          (sWants (ckP .two) ⟨F.a, base, F.all, dB :: lo.map mk, F.key, F.all⟩
            (rhoT (ckP .two) (dB :: lo.map mk) (m, c, τ)))) = true := ht
    rw [Bool.and_eq_true, Bool.and_eq_true] at h1
    have h2 : (GChal.pass (b := dB.entry.work) c &&
        passT (ckP .two) (lo.map mk) (rhoT (ckP .two) (lo.map mk) τ)) = true := h1.1.1
    rw [Bool.and_eq_true] at h2
    exact h2.2

def K12LawNO : Prop :=
  ∀ (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (N : ConclK F),
    AtPlaceOwn F π num L mC mS mW rad base dB dt εt →
    (pieceT F W π base dB dt e₀ εt).ior.red.Leads
      (fun x => FirstOpensOwn π num no base x.1 ∧ BatAtN F π no rad rd dB e₀ N x)
      (fun x _ => QN π N x) (pieceT F W π base dB dt e₀ εt).err

/-- **THE LAW OF THE KIND K12 WHERE THE FIRST FOLD SENDS ITS OWN MASK.** -/
theorem k12_lawNO : K12LawNO := by
  intro F W π num no L mC mS mW rad rd base dB dt e₀ εt N hA x hx
  obtain ⟨hfo, hbat⟩ := hx
  obtain ⟨w0, l, hw, hlike⟩ := hA.like
  cases hlike with
  | cons hB hT =>
  obtain ⟨lo, rfl, hlo⟩ := like_lo dt l hT
  show ∀ m : (roundT (ckP .two) dB).up.Msg,
    cnt (fun c : (roundT (ckP .two) dB).up.Chal =>
      ¬ Doomed (uLT (ckP .two) (lo.map mk)) εt fun τ =>
        ∀ b, (pieceT F W π base dB (lo.map mk) e₀ εt).ior.red.out x (m, c, τ) = some b →
          QN π N x) ≤ e₀
  intro m
  by_cases hany : ∃ c τ b,
      (pieceT F W π base dB (lo.map mk) e₀ εt).ior.red.out x (m, c, τ) = some b
  · obtain ⟨c₀, τ₀, b₀, hb₀⟩ := hany
    obtain ⟨a, rest, ch, hR, G0, Ly, D, row₀, hok₀, e3, hfix, hpub, _, _, _⟩ :=
      yes_accO F π num no L mC mS mW rad rd base dB lo e₀ εt hA w0 l hw hB hlo x hfo m c₀ τ₀ b₀ hb₀
    refine le_trans (cnt_mono ?_) (hbat a rest G0 Ly D row₀ hok₀ hfix m)
    intro c hc
    by_contra hnot
    apply hc
    by_cases hyc : ∃ τ b,
        (pieceT F W π base dB (lo.map mk) e₀ εt).ior.red.out x (m, c, τ) = some b
    · obtain ⟨τ₁, b₁, hb₁⟩ := hyc
      obtain ⟨a', rest', ch', hR', G0', Ly', D', row, hok, e3', hfix', _, hbt, _, _⟩ :=
        yes_accO F π num no L mC mS mW rad rd base dB lo e₀ εt hA w0 l hw hB hlo x hfo m c τ₁ b₁ hb₁
      obtain ⟨rfl, rfl⟩ := List.cons.inj (hfix'.1.symm.trans hfix.1)
      obtain rfl := Option.some.inj (e3'.symm.trans e3)
      obtain rfl := Option.some.inj (hfix'.2.1.symm.trans hfix.2.1)
      obtain rfl := Option.some.inj (hfix'.2.2.1.symm.trans hfix.2.2.1)
      obtain rfl := Option.some.inj ((hfix'.2.2.2 row).symm.trans (hfix.2.2.2 row))
      by_cases hN : N x a' rest' G0' Ly' D'
      · exact Doomed.of_forall _ _ fun τ b _ => ⟨a', rest', G0', Ly', D', hfix, hN⟩
      · have hno : ∀ w, ¬ (sgOf a').RIn (rad (sgOf a'))
            (stmG (sgOf a') row, yOf π a' row D' hok rd (W0 F no D'.book x.2)) w :=
          fun w hw' => hnot ⟨yes_pass0 F π base dB (lo.map mk) e₀ εt x m c τ₁ b₁ hb₁, row, w, hbt,
            hw', hN⟩
        obtain ⟨hH, hrad⟩ := holds_at π L mC mS mW rad x.1.st.codes hpub hA.spend hA.codes a' rest'
          w0 l ch' hfix.1 hw e3
        classical
        have hd := chain_many_list_own ch' hH (stmG (sgOf a') row)
          (yOf π a' row D' hok rd (W0 F no D'.book x.2))
          (fun m₁ => zOf π a' row D' hok rd (W0 F no D'.book x.2) (fMown ch' D' m₁))
          (fun _ _ => 0) (by rw [hrad]; exact hno)
          (fun τ' => decide (ch'.Acc (stmG (sgOf a') row)
              (yOf π a' row D' hok rd (W0 F no D'.book x.2))
              (zOf π a' row D' hok rd (W0 F no D'.book x.2) (fMown ch' D' (msg1 ch' (blOf ch' τ'))))
              (fun _ _ => 0) (blOf ch' τ') ∧
            PQ.passSL (ckP .two) ch'.rds (PQ.rhoSL (ckP .two) ch'.rds τ') = true))
          (fun b hb => by
            have h := of_decide_eq_true hb
            rw [blOf_trL] at h
            exact h)
        have hd2 := doomed_back (ckP .two) lo _ _ (doomed_castL hR _ _ hd)
        refine Doomed.mono _ _ ?_ (Doomed.mono_err _ (bears_le _ _ εt ?_) hd2)
        · intro τ hτ b hb
          exfalso
          obtain ⟨a₂, rest₂, ch₂, hR₂, G₂, Ly₂, D₂, row₂, hok₂, e3₂, hfix₂, _, hbt₂, hacc₂,
            hpass₂⟩ :=
            yes_accO F π num no L mC mS mW rad rd base dB lo e₀ εt hA w0 l hw hB hlo x hfo m c τ b
              hb
          obtain ⟨rfl, rfl⟩ := List.cons.inj (hfix₂.1.symm.trans hfix.1)
          obtain rfl := Option.some.inj (e3₂.symm.trans e3)
          obtain rfl := Option.some.inj (hfix₂.2.1.symm.trans hfix.2.1)
          obtain rfl := Option.some.inj (hfix₂.2.2.1.symm.trans hfix.2.2.1)
          obtain rfl := Option.some.inj ((hfix₂.2.2.2 row).symm.trans (hfix.2.2.2 row))
          obtain rfl : row₂ = row := congrArg Prod.fst (Except.ok.inj (hbt₂.symm.trans hbt))
          have ht : decide (ch₂.Acc (stmG (sgOf a₂) row₂)
              (yOf π a₂ row₂ D₂ hok rd (W0 F no D₂.book x.2))
              (zOf π a₂ row₂ D₂ hok rd (W0 F no D₂.book x.2)
                (fMown ch₂ D₂ (msg1 ch₂ (blOf ch₂ (castT hR.symm (trW (ckP .two) lo τ))))))
              (fun _ _ => 0) (blOf ch₂ (castT hR.symm (trW (ckP .two) lo τ))) ∧
            PQ.passSL (ckP .two) ch₂.rds
              (PQ.rhoSL (ckP .two) ch₂.rds (castT hR.symm (trW (ckP .two) lo τ))) = true) = true :=
            decide_eq_true ⟨hacc₂, hpass₂⟩
          exact Bool.noConfusion (ht.symm.trans hτ)
        · unfold Bears
          rw [errList_errW, errList_cast]
          exact hA.bears a' rest' w0 l ch' hfix.1 hw e3
    · exact Doomed.of_forall _ _ fun τ b hb => absurd ⟨τ, b, hb⟩ hyc
  · exact le_trans (le_of_eq (cnt_false fun c hc =>
      hc (Doomed.of_forall _ _ fun τ b hb => absurd ⟨c, τ, b, hb⟩ hany))) (Nat.zero_le _)

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.yes_accO
#print axioms VerifiableInference.Desc.K12.Coin.k12_lawNO
