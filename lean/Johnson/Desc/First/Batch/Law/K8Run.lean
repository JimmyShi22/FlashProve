-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/K8Run.lean
(kind K9's soundness lemma): THEOREM: THE FIRST PAYER OF RunOk (Law/Gather.lean) AT A
REAL RUN: the smallness test's run of claims "K8.equations", at the real record S, at K9's lens atS
and the letters O9 φ Ok Fu, Fx9 φ Ok (Law/FitsAtS.lean).
IT IS A BRIDGE: all that is said of the run's list is other files' (the smallness test's claims:
Johnson/Desc/First/TailClaims/EquationsAny, EquationsBlank, EquationsFrame, EquationsLater:
k08_run, eq_blank, eq_side, eq_later, eq_split).
  k8Run         the run's text at S. (To the letter the text "k8Equations" of the seat for the
                adding: the ledger's count is added to the number that the gathering hands.)
  batchOf_terms those files' sum of single equations under the powers of chi is termsAt of the list
                (exponent, what the equation lacks at the cells).
  k8_rest       at ledgers: where the list is made and, behind any list, can be added to a ledger
                with the returned ledger's core and frame: the sum of all claims behind the first
                four, under their weights, is that polynomial.
  get_put       what K9's lens reads behind the run's writing.
  k8_runOk      **RunOk of k8Run**, at the terms tm4 (A LETTER: the first four claims': the digits'
                lookup's: other files') followed by the ties' and reads' single equations.
THE HYPOTHESES ON THE LETTERS, each to be met by whoever chooses them for all kinds together:
  hπ      φ holds the smallness test's record with the fourteen written fields blanked, and funs;
  hkeep   φ does not see the run's writing (the record where the blanked records agree; the ledger);
  hOk     the promise on the fixed part gives "the shapes fit the matrices";
  hFu     at a full state THAT GOES ON FROM q (so that its payer may lean on the promise on the
          fixed part: the reads run over the list of tables, which no later yes reads): the test on
          the weights says yes at that state's own record and ledger, and the two public facts of
          k08_run hold there;
  h4      the first four claims' sum is termsAt (tm4 ..).
Not claimed: that such letters exist together with the other kinds'; h4.

-/
import Johnson.Desc.First.TailClaims.EquationsBlank
import Johnson.Desc.First.TailClaims.EquationsLater
import Johnson.Desc.First.Batch.Law.Gather
import Johnson.Desc.First.Batch.Law.FitsAtS
import Johnson.Desc.First.Batch.Law.Raw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Tie.Pv.Tail.Port OnBytes.Road.Rows
open OnBytes.Tie.Pv.Tail (ReadsRaw UnitRow)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc.K9 (atS RunOf there)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims (equations rkSelfTestP)
open VerifiableInference.Desc.First.TailClaims.Law (blank eq_blank eq_side eq_later eq_split
  k08_run)

/-- The run's text at S. -/
def k8Run : RunOf S :=
  ("K8.equations", fun front s => do
    let F ← there "K9.in-a-segment" s.fork?
    let tl ← there "K9.in-a-segment" s.tl?
    let funs ← there "K9.in-a-segment" s.funs?
    let x ← equations (F.nClaim + front) tl funs F
    pure (x.2.2, (s.putTl x.1).putFork x.2.1))

theorem k8Run_ok (front : Nat) (e e₁ : S) (c : List Claim) (h : k8Run.2 front e = .ok (c, e₁)) :
    ∃ F tl funs tl' F1, e.fork? = some F ∧ e.tl? = some tl ∧ e.funs? = some funs ∧
      equations (F.nClaim + front) tl funs F = .ok (tl', F1, c) ∧
      e₁ = (e.putTl tl').putFork F1 := by
  simp only [k8Run] at h
  obtain ⟨F, hF, h⟩ := ok_bind h
  obtain ⟨tl, ht, h⟩ := ok_bind h
  obtain ⟨funs, hf, h⟩ := ok_bind h
  obtain ⟨x, hx, h⟩ := ok_bind h
  obtain ⟨e1, e2⟩ := Prod.mk.inj (Except.ok.inj h)
  refine ⟨F, tl, funs, x.1, x.2.1, there_ok hF, there_ok ht, there_ok hf, ?_, e2.symm⟩
  rw [hx, ← e1]

section
variable {K : Type} [Field K] (ρ : Reading K)

theorem batchOf_terms (θ : K) (A : Nat → Nat → Nat → K) (L : List (Nat × Gap K)) :
    batchOf θ A L = termsAt K (L.map fun r => (r.1, r.2 A)) θ := by
  unfold batchOf termsAt
  rw [List.map_map]
  rfl

/-- At ledgers: the claims behind the first four. -/
theorem k8_rest (W : World K) (A : Nat → Nat → Nat → K) (front : Nat) (tl tl' u ts : HTailF2)
    (funs : Array HFun) (F F1 A0 G Fc : Fork) (pre cls : List Claim) (hs : F.LS.size = F.ns)
    (he : equations front tl funs F = .ok (tl', F1, cls)) (hc : core A0 = core F1)
    (hw : treesFrame A0.trees = treesFrame F1.trees) (hadd : addAll A0 (pre ++ cls) = some G)
    (hfit : OnBytes.Tie.Pv.Tail.Port.Fits tl) (hb : blank u ts = blank u tl)
    (hth : Fc.theta = F.theta)
    (hrk : rkSelfTestP ts Fc = .ok ()) (hW : ReadsRaw ρ ts funs Fc W A)
    (hrows : (Fc.trees.getD ts.ix.ZZ {}).rows.size = 2 * ts.zzBlocks + 2)
    (hU : ∀ x ∈ readsList ts funs, UnitRow Fc (uOf ts x.1) ∧
      ∀ d, d < (ts.mats.getD x.1.mat {}).k → posOf ts x.1 x.2 d < colsU F1 (uOf ts x.1)) :
    claimsSum ρ W (ρ.val F.theta) F.planClaimsF (F.nClaim + pre.length + 4) (cls.drop 4) =
      termsAt K ((rowsTail ρ tl funs F.planClaimsF).map fun r => (r.1, r.2 A))
        (ρ.val F.theta) := by
  have os := eq_side he
  obtain ⟨_, c2, c3, c4, c5, c6⟩ := core_parts hc
  have hsA : A0.LS.size = A0.ns := by
    rw [c5, c6, os.LS, os.ns]
    exact hs
  obtain ⟨_, _, four, rest, X, X4, e, l4, _, a1, a2, a3, ht⟩ :=
    k08_run K ρ W A front tl tl' u ts funs F F1 A0 G Fc pre cls hs he hsA hw c2 c4 hadd hfit hb hth
      hrk hW hrows hU
  obtain ⟨_, x1, x2, _⟩ := addAll_total ρ W pre A0 X hsA a1
  obtain ⟨_, y1, y2, _⟩ := addAll_total ρ W four X X4 x2 a2
  obtain ⟨z0, _⟩ := addAll_total ρ W rest X4 G y2 a3
  have hd : cls.drop 4 = rest := by
    rw [e, ← l4, List.drop_left]
  have tX : X.theta = A0.theta := by rw [x1]
  have tX4 : X4.theta = X.theta := by rw [y1]
  have pX : X.planClaimsF = A0.planClaimsF := by rw [x1]
  have pX4 : X4.planClaimsF = X.planClaimsF := by rw [y1]
  have nX : X.nClaim = A0.nClaim + pre.length := by rw [x1]
  have nX4 : X4.nClaim = X.nClaim + four.length := by rw [y1]
  rw [tX4, tX, c2, os.theta, pX4, pX, c4, os.plan, nX4, nX, c3, os.nClaim, l4] at z0
  rw [hd, ← batchOf_terms]
  exact add_left_cancel (z0.symm.trans ht)

end

/-- What K9's lens reads behind the run's writing. -/
theorem get_put (e : S) (a : K9.Part) (ha : atS.get? e = some a) (tl' : HTailF2) (F1 : Fork) :
    ∃ a₁, atS.get? ((e.putTl tl').putFork F1) = some a₁ ∧ a₁.F = F1 ∧ a₁.L = a.L ∧
      a₁.d.st = a.d.st ∧ ((e.putTl tl').putFork F1).tl? = some tl' ∧
      ((e.putTl tl').putFork F1).funs? = e.funs? ∧ e.fork? = some a.F := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := e
  cases here with
  | lay x =>
    obtain rfl := Option.some.inj ha
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | att x =>
    obtain rfl := Option.some.inj ha
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | head x =>
    by_cases ho : x.opened = true
    · cases hs : x.slot with
      | none => simp [atS, S.link?, S.fork?, S.tl?, K9.usedOf, ho, hs] at ha
      | some n =>
        simp only [atS, S.link?, S.fork?, S.tl?, K9.usedOf, ho, hs, if_true, Option.bind_eq_bind,
          Option.bind_some, Option.pure_def, Option.some.injEq] at ha
        subst ha
        simp [atS, S.putTl, S.putFork, S.link?, S.fork?, S.tl?, S.funs?, K9.usedOf, ho, hs]
    · simp [atS, S.link?, ho] at ha
  | between => simp [atS, S.link?] at ha
  | fin x => simp [atS, S.link?] at ha
  | mem x => simp [atS, S.link?] at ha

/-- The number of columns of an array is read off the arrays' numbers of columns. -/
theorem colsU_widths (F G : Fork) (h : G.trees.map (·.K) = F.trees.map (·.K)) (t : Nat) :
    colsU G t = colsU F t := by
  have := congrArg (fun a => (a[t]?).getD 0) h
  simpa [colsU, Array.getElem?_map] using this

section
variable {α : Type}

abbrev GE8 : Type := Cb.Gl.E

/-- The number of the run's claims, off the fixed part. -/
def len8 (π : α → Option HTailF2 × Option (Array HFun)) (q : α × Option Pub9) : ℕ :=
  match π q.1 with
  | (some tlb, some funs) => 4 + (tlb.NM + (readsList tlb funs).length)
  | _ => 0

/-- The arrays' entries by the array's number, off a list of names. -/
def cellsA (arr : Array (Nat × String)) (D : Bound GE8) : Nat → Nat → Nat → GE8 := fun t R i =>
  D.cell (arr.getD t (0, "")).1 (arr.getD t (0, "")).2 R i

/-- The ties' and the reads' single equations, each with its exponent, off the fixed part. -/
def tmRest (π : α → Option HTailF2 × Option (Array HFun)) (q : α × Option Pub9)
    (y : Bound GE8) : List (ℕ × GE8) :=
  match π q.1, q.2 with
  | (some tlb, some funs), some v =>
    (rowsTail Reading.gl tlb funs v.F.planClaimsF).map fun r => (r.1, r.2 (cellsA v.arrayOf y))
  | _, _ => []

/-- **RunOk of the smallness test's run of claims, at the real record.** -/
theorem k8_runOk (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (u : HTailF2)
    (π : α → Option HTailF2 × Option (Array HFun))
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (hkeep : ∀ s tl tl' F1, s.tl? = some tl → blank u tl' = blank u tl →
      φ ((s.putTl tl').putFork F1) = φ s)
    (hOk : ∀ q tlb, Ok q → (π q.1).1 = some tlb → OnBytes.Tie.Pv.Tail.Port.Fits tlb)
    (hFu : ∀ q t b ts funs, Fx9 φ Ok q t → Fu t → atS.get? t = some b → t.tl? = some ts →
      t.funs? = some funs →
      rkSelfTestP ts b.F = .ok () ∧
        (b.F.trees.getD ts.ix.ZZ {}).rows.size = 2 * ts.zzBlocks + 2 ∧
        ∀ x ∈ readsList ts funs, UnitRow b.F (uOf ts x.1) ∧
          ∀ d, d < (ts.mats.getD x.1.mat {}).k → posOf ts x.1 x.2 d < colsU b.F (uOf ts x.1))
    (tm4 : ℕ → α × Option Pub9 → Bound GE8 → List (ℕ × GE8))
    (h4 : ∀ q front e a c e₁, Fx9 φ Ok q e → good9 e → atS.get? e = some a →
      k8Run.2 front e = .ok (c, e₁) → ∀ t y, laterK atS (O9 (K := GE8) φ Ok Fu) e₁ t → Fu t →
        wsumK atS Reading.gl t y (Reading.gl.val a.F.theta) (a.F.nClaim + front) (c.take 4) =
          termsAt GE8 (tm4 (a.F.nClaim + front) q y) (Reading.gl.val a.F.theta)) :
    RunOk Reading.gl atS (O9 φ Ok Fu) (Fx9 φ Ok) k8Run.2
      (fun n q y => tm4 n q y ++ tmRest π q y) (len8 π) := by
  intro q front e a c e₁ hf hg ha hs hr
  obtain ⟨F, tl, funs, tl', F1, hF, htl, hfu, he, rfl⟩ := k8Run_ok front e e₁ c hr
  obtain ⟨a₁, ha₁, f1, f2, f3, t1, t2, hF'⟩ := get_put e a ha tl' F1
  have eF : F = a.F := Option.some.inj (hF.symm.trans hF')
  subst eF
  have os := eq_side he
  have hbl := eq_blank u he
  have hφ1 : φ ((e.putTl tl').putFork F1) = φ e := hkeep e tl tl' F1 htl hbl
  have hcore : core a₁.F = core a.F := by
    rw [f1]
    simp only [core, sums, os.trees, os.LS, os.c0, os.ns, os.theta, os.nClaim, os.plan]
  have hgo : GoesOn (pubOf a) a₁ :=
    ⟨by rw [f1]; exact eq_later he, by rw [f1]; exact os.plan, by rw [f1, os.trees]; rfl,
      by rw [f2]; rfl, by rw [f2]; rfl, f3⟩
  have hmore : more9 φ e ((e.putTl tl').putFork F1) := ⟨hφ1, fun a' ha' => by
    have ea : a' = a := Option.some.inj (ha'.symm.trans ha)
    rw [ea]
    exact ⟨a₁, ha₁, hgo⟩⟩
  obtain ⟨a0, ha0, g1, _⟩ := hg
  have ea0 : a0 = a := Option.some.inj (ha0.symm.trans ha)
  subst ea0
  have hq1 : π q.1 = (some (blank u tl), some funs) := by
    rw [← hf.2.1, hπ, htl, hfu]
    rfl
  obtain ⟨four, rest, ec, l4, lr⟩ :=
    eq_split Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ he
  have hlen : c.length = len8 π q := by
    simp only [len8, hq1]
    rw [ec, List.length_append, l4, lr]
    rfl
  refine ⟨a₁, ha₁, hcore, by rw [f1, os.trees], ⟨a₁, ha₁, by rw [f2]; exact g1,
    by rw [f1, os.LS, os.ns]; exact hs⟩, hmore, fx_of_more φ Ok q e _ hf hmore, hlen,
    fun pre A₀ G hn hc hw hA t y ht hfull => ?_⟩
  obtain ⟨b, hb, gb⟩ := ht.2.1.2 a₁ ha₁
  have hφt : φ t = φ e := ht.2.1.1.trans hφ1
  have hπt := hπ t
  rw [hφt, hf.2.1, hq1] at hπt
  obtain ⟨p1, p2⟩ := Prod.mk.inj hπt
  obtain ⟨ts, hts, hbs⟩ := Option.map_eq_some_iff.1 p1.symm
  obtain ⟨k1, k2, k3⟩ := hFu q t b ts funs
    (fx_of_more φ Ok q _ t (fx_of_more φ Ok q e _ hf hmore) ht.2.1) hfull hb hts p2.symm
  have hthb : b.F.theta = a0.F.theta := by
    have h0 := ht.2.2
    simp only [thetaOf, ha₁, hb, Option.map_some, Option.some.injEq] at h0
    rw [← h0, f1, os.theta]
  have hcol : ∀ x, colsU b.F x = colsU F1 x := fun x => by
    rw [← f1]
    exact colsU_widths _ _ (goesOn_widths gb) x
  have hrest := k8_rest Reading.gl (worldAt Reading.gl b.L b.F y) (cellsOf b.L y)
    (a0.F.nClaim + front) tl tl' u ts funs a0.F F1 A₀ G b.F pre c hs he (by rw [← f1]; exact hc)
    (by rw [← f1]; exact hw) hA
    (hOk q (blank u tl) hf.1 (by rw [hq1])) hbs hthb k1
    (worldAt_readsRaw Reading.gl ts funs b.L b.F y) k2
    (fun x hx => ⟨(k3 x hx).1, fun d hd => by rw [← hcol]; exact (k3 x hx).2 d hd⟩)
  have h4' := h4 q front e a0 c _ hf ⟨a0, ha, g1, hs⟩ ha hr t y ht hfull
  have hplan : b.F.planClaimsF = a0.F.planClaimsF := by
    rw [gb.2.1]
    show a₁.F.planClaimsF = _
    rw [f1, os.plan]
  obtain ⟨_, _, v, b0, hv, hb0, gv⟩ := hf
  have eb0 : b0 = a0 := Option.some.inj (hb0.symm.trans ha)
  subst eb0
  have harr : b.L.arrayOf = v.arrayOf := by
    rw [gb.2.2.2.1]
    show a₁.L.arrayOf = _
    rw [f2, gv.2.2.2.1]
  have htm : tmRest π q y =
      (rowsTail Reading.gl tl funs b0.F.planClaimsF).map fun r => (r.1, r.2 (cellsOf b.L y)) := by
    have hce : cellsOf b.L y = cellsA v.arrayOf y := by
      rw [← harr]
      rfl
    simp only [tmRest, hq1, hv]
    rw [gv.2.1, hce]
    rfl
  have hc4 : (c.take 4).length = 4 := by
    rw [List.length_take, ec, List.length_append, l4]
    omega
  have hsplit : c = c.take 4 ++ c.drop 4 := (List.take_append_drop 4 c).symm
  rw [hsplit, wsumK_append, h4', hc4, termsAt_append, htm,
    wsumK_eq atS Reading.gl t b hb y _ (c.drop 4), hplan, ← hn]
  rw [← hrest]

end

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.k8_runOk
#print axioms VerifiableInference.Desc.K9L.k8_rest
#print axioms VerifiableInference.Desc.K9L.get_put
