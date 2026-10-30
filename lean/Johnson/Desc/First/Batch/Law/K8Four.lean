-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/K8Four.lean
(kind K9's soundness lemma): THEOREMS: THE FIRST FOUR CLAIMS OF THE SMALLNESS TEST's RUN
"K8.equations" (one on the digits' lookup's keys, three on the planes of its counts): the hypothesis
h4 of Law/K8Run.lean IS BROUGHT DOWN TO TWO HYPOTHESES ON THE SHARED LETTERS (hOk4, hFu4 below):
WHICH CLAIMS THEY ARE AND THE SLOTS' HALF OF THEIR VALUES ARE PROVED; THE ENTRIES' HALF IS TAKEN AS
GIVEN.
The four are PLAIN claims (each under its own number's power) WITH RUNS OF ENTRIES on virtual rows.
  four8 tl g    the four, written out: a function of the test's record and of what its lookup heard.
  take_four     where the run says yes, the first four of its list are four8 tl g; and the returned
                ledger is the one handed in with one mark paid, the leaves' window of slots laid
                (shown 0, factor -1), one mark more paid. (The cut behind the fourth claim is, line
                for line, first_four (Johnson/Desc/First/K8/Four/Exchange.lean); the two steps'
                yes, cut step by step, eqKeys_cut and eqCounts_cut (Johnson/Top/H/EqPort/).)
  claim_ref     a claim's value at a later ledger is its value in the world that the ledger in front
                of the draw names (the link's law's refWorld), runs of entries too.
  vals4         the four values, off the fixed part and the data.
  k8_goes       the run's state behind goes on from the state in front.
  k8_four       **h4**, at tm4 := the four values, numbered: under hOk4 and hFu4.
  k8_runOk_all  **RunOk of the whole run**, at the terms: the four values numbered, then the ties'
                and the reads' single equations: no claim's terms are a letter any more.
THE HYPOTHESES ON THE LETTERS, beside those of Law/K8Run.lean (h-pi, hkeep, hOk, hFu):
  hOk4    the promise on the fixed part: the snapshot's ledger has one place a slot; every slot that
          a form of the four names lies in the leaves' window or is filled in the snapshot;
  hFu4    AT A FULL STATE THAT GOES ON FROM q THE ENTRIES THAT THE FOUR NAME ARE ent q y's: THIS IS
          THE ENTRIES' HALF OF THE CONCLUSION, TAKEN AS GIVEN: it says that the virtual rows which
          the four read have, at a full state, weights that were fixed before the draw.
Not claimed: that such letters exist together with the other kinds'.

-/
import Johnson.Top.H.EqPort.EqJoin
import Johnson.Top.H.EqPort.EqBits
import Johnson.Desc.First.TailClaims.EquationsCover
import Johnson.Desc.First.Link.Law.K4Values
import Johnson.Desc.First.Batch.Law.K8Run
import Johnson.Desc.First.Batch.Law.PlainRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.PscRun (Later Sized Filled paid_later)
open OnBytes.Tie.Pv.Tail (UnitRow)
open OnBytes.Tie.Pv.Tail.Port (readsList uOf posOf colsU)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims (equations eqKeys eqCounts rkSelfTestP EqM)
open VerifiableInference.Desc.First.TailClaims.Law (blank eq_blank eq_side eq_later eq_parts
  eqTail_total)
open VerifiableInference.Desc.K4Values (refWorld winOf LaidAt laid_of_run value_ref)
open _root_.Fo (joinRuns joinConst bzRun pinW)
open _root_.Fo.Eq (at_ok eqKeys_cut eqCounts_cut)

/-- The four claims, written out. -/
def four8 (tl : HTailF2) (g : Forest.Heard) : List Claim :=
  [{ form := Aff.ofConst (joinConst tl g) - g.cEnd, runs := (joinRuns tl g).toArray },
   { form := g.leaves.rowForm oneE {},
     runs := #[bzRun tl 0 (mulE g.leaves.eps g.leavesA)
       (eqTab (g.zb0.extract 5 (5 + tl.f9.kT + tl.f9.cK)))] },
   { form := Aff.slot g.sBit,
     runs := #[bzRun tl 1 (subE zeroE oneE) (eqTab (g.zb1.extract 5 (5 + tl.f9.kT + tl.f9.cK)))] },
   { form := Aff.ofConst (subE zeroE (ofNat (2 ^ tl.f9.v - tl.f9.padding))),
     runs := #[bzRun tl 2 oneE (pinW tl)] }]

/-- The four read none of the fourteen written fields. -/
theorem four8_blank (u tl : HTailF2) (g : Forest.Heard) : four8 (blank u tl) g = four8 tl g := rfl

/-- **Where the run says yes: its first four claims, and its ledger.** -/
theorem take_four {front : ℕ} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) :
    ∃ (g : Forest.Heard) (Fa : Fork), tl.heard = some g ∧ cls.take 4 = four8 tl g ∧
      (F.paid g.owedJoin).hideRun g.leaves.first
        (Array.replicate g.leaves.walk.1.length zeroE) (subE zeroE oneE) = some Fa ∧
      F1 = Fa.paid g.owedPlanes := by
  obtain ⟨before, tla, tlb, s1, s2, arr, h8, h9, k9, hcl⟩ := eq_parts h
  obtain ⟨_, _, _, _, _, _, new, e, _, _⟩ :=
    eqTail_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ F before tlb tl' funs front s2
      (F1, arr) k9
  have eF : F1 = s2.1 := congrArg Prod.fst e
  have eA : arr = s2.2 ++ new.toArray := congrArg Prod.snd e
  have hJ : EqM.at (eqKeys tl) front F #[] = .ok ((tla, s1.1), s1.2) := (at_ok _ _ _ _).2 h8
  have hB : EqM.at (eqCounts tla) front s1.1 s1.2 = .ok ((tlb, s2.1), s2.2) :=
    (at_ok _ _ _ _).2 h9
  obtain ⟨g, runs, j1, _, j3, j4, j5, j6⟩ := eqKeys_cut tl tla F s1.1 #[] s1.2 hJ
  obtain ⟨g', Fa, k1, _, k2, k3, k4, _⟩ := eqCounts_cut tla tlb s1.1 s2.1 s1.2 s2.2 hB
  have eg : g' = g := by
    rw [j6] at k1
    exact Option.some.inj (k1.symm.trans j1)
  subst eg
  have er : runs = (joinRuns tl g').toArray := by
    rw [← j3]
  have hsz : s2.2.size = 4 := by
    rw [k3, j4]
    simp
  refine ⟨g', Fa, j1, ?_, by rw [← j5]; exact k2, by rw [eF, k4]⟩
  rw [← hcl, eA, Array.toList_append, List.take_left' (by simpa using hsz), k3, j4, er, j6]
  rfl

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- A run's sum reads its function at the run's own places alone. -/
theorem runSum_congr (h h' : ℕ → K) : ∀ (count i : ℕ),
    (∀ j, i ≤ j → j < i + count → h j = h' j) → runSum h count i = runSum h' count i
  | 0, _, _ => rfl
  | c + 1, i, H => by
    simp only [runSum]
    rw [H i (Nat.le_refl i) (by omega),
      runSum_congr h h' c (i + 1) fun j h1 h2 => H j (by omega) (by omega)]

/-- **A claim's value at a later ledger is its value in the world that U names.** -/
theorem claim_ref (cl : Claim) (L : LinkCtx) (U B : Fork) (wins : List (ℕ × ℕ))
    (ent : ℕ → ℕ → ℕ → K) (y : Bound K) (hU : Later U B) (hw : ∀ w ∈ wins, LaidAt B w)
    (hs : ∀ x ∈ cl.form.slots.toList, (∃ w ∈ wins, K4Values.InWin w x.1) ∨ Filled U x.1)
    (he : ∀ x ∈ cl.form.ents.toList, (worldAt ρ L B y).entry x.tree x.row x.idx =
      ent x.tree x.row x.idx)
    (hr : ∀ r ∈ cl.runs.toList, ∀ i < r.n, (worldAt ρ L B y).entry r.tree r.row (r.first + i) =
      ent r.tree r.row (r.first + i)) :
    claimValue ρ (worldAt ρ L B y) cl = claimValue ρ (refWorld ρ U wins ent y) cl := by
  unfold claimValue
  rw [value_ref ρ cl.form L U B wins ent y hU hw hs he]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun r hr' => ?_)
  unfold Run2.value
  rw [runSum_congr _ (fun i => ρ.val (r.w.getD (r.w0 + i) zeroE) *
    (refWorld ρ U wins ent y).entry r.tree r.row (r.first + i)) r.n 0 fun j _ hj => by
      rw [hr r hr' j (by omega)]
      rfl]

end

section
variable {α : Type}

/-- The four values, off the fixed part and the data. -/
def vals4 (π : α → Option HTailF2 × Option (Array HFun))
    (ent : α × Option Pub9 → Bound GE8 → ℕ → ℕ → ℕ → GE8) (q : α × Option Pub9)
    (y : Bound GE8) : List GE8 :=
  match (π q.1).1, q.2 with
  | some tlb, some v =>
    match tlb.heard with
    | some g =>
      (four8 tlb g).map (claimValue Reading.gl
        (refWorld Reading.gl v.F [winOf g.leaves] (ent q y) y))
    | none => []
  | _, _ => []

/-- The run's state behind goes on from the state in front. -/
theorem k8_goes (φ : S → α) (u : HTailF2)
    (hkeep : ∀ s tl tl' F1, s.tl? = some tl → blank u tl' = blank u tl →
      φ ((s.putTl tl').putFork F1) = φ s)
    (front : ℕ) (e : S) (a : K9.Part) (tl tl' : HTailF2) (funs : Array HFun) (F1 : Fork)
    (c : List Claim) (ha : atS.get? e = some a) (htl : e.tl? = some tl)
    (he : equations front tl funs a.F = .ok (tl', F1, c)) :
    more9 φ e ((e.putTl tl').putFork F1) := by
  obtain ⟨a₁, ha₁, f1, f2, f3, _⟩ := get_put e a ha tl' F1
  have os := eq_side he
  refine ⟨hkeep e tl tl' F1 htl (eq_blank u he), fun a' ha' => ?_⟩
  have ea : a' = a := Option.some.inj (ha'.symm.trans ha)
  rw [ea]
  exact ⟨a₁, ha₁, by rw [f1]; exact eq_later he, by rw [f1]; exact os.plan,
    by rw [f1, os.trees]; rfl, by rw [f2]; rfl, by rw [f2]; rfl, f3⟩

/-- **h4: the first four claims' sum.** -/
theorem k8_four (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (u : HTailF2)
    (π : α → Option HTailF2 × Option (Array HFun))
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (hkeep : ∀ s tl tl' F1, s.tl? = some tl → blank u tl' = blank u tl →
      φ ((s.putTl tl').putFork F1) = φ s)
    (ent : α × Option Pub9 → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (hOk4 : ∀ q v tlb g, Ok q → q.2 = some v → (π q.1).1 = some tlb → tlb.heard = some g →
      Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1)
    (hFu4 : ∀ q t b y tlb g, Fx9 φ Ok q t → Fu t → atS.get? t = some b →
      (π q.1).1 = some tlb → tlb.heard = some g → ∀ cl ∈ four8 tlb g,
      (∀ x ∈ cl.form.ents.toList, (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx =
        ent q y x.tree x.row x.idx) ∧
      ∀ r ∈ cl.runs.toList, ∀ i < r.n,
        (worldAt Reading.gl b.L b.F y).entry r.tree r.row (r.first + i) =
          ent q y r.tree r.row (r.first + i)) :
    ∀ q front e a c e₁, Fx9 φ Ok q e → good9 e → atS.get? e = some a →
      k8Run.2 front e = .ok (c, e₁) → ∀ t y, laterK atS (O9 (K := GE8) φ Ok Fu) e₁ t → Fu t →
        wsumK atS Reading.gl t y (Reading.gl.val a.F.theta) (a.F.nClaim + front) (c.take 4) =
          termsAt GE8 (numbered (a.F.nClaim + front) (vals4 π ent q y))
            (Reading.gl.val a.F.theta) := by
  intro q front e a c e₁ hf _ ha hr t y ht hfull
  obtain ⟨F, tl, funs, tl', F1, hF, htl, hfu, he, rfl⟩ := k8Run_ok front e e₁ c hr
  obtain ⟨a₁, ha₁, f1, _, _, _, _, hF'⟩ := get_put e a ha tl' F1
  have eF : F = a.F := Option.some.inj (hF.symm.trans hF')
  subst eF
  obtain ⟨g, Fa, hg, h4, hrun, hF1⟩ := take_four he
  have hmore := k8_goes φ u hkeep _ e a tl tl' funs F1 c ha htl he
  have hft : Fx9 φ Ok q t :=
    fx_of_more φ Ok q _ t (fx_of_more φ Ok q e _ hf hmore) ht.2.1
  have hft' := hft
  obtain ⟨b, hb, gb⟩ := ht.2.1.2 a₁ ha₁
  have hq1 : (π q.1).1 = some (blank u tl) := by
    rw [← hf.2.1, hπ, htl]
    rfl
  obtain ⟨hok, _, v, a0, hv, ha0, gv⟩ := hf
  have ea0 : a0 = a := Option.some.inj (ha0.symm.trans ha)
  subst ea0
  obtain ⟨_, _, v', b', hv', hb', gv'⟩ := hft
  have ev : v' = v := Option.some.inj (hv'.symm.trans hv)
  have eb : b' = b := Option.some.inj (hb'.symm.trans hb)
  subst ev eb
  obtain ⟨hsz, hslots⟩ := hOk4 q v' (blank u tl) g hok hv hq1 hg
  rw [four8_blank] at hslots
  have hsa : Sized a0.F := gv.1.sized hsz
  have hlb : Later F1 b'.F := by
    have := gb.1
    rwa [show (pubOf a₁).F = F1 from f1] at this
  have hlaid : LaidAt b'.F (winOf g.leaves) :=
    laid_of_run ((paid_later a0.F g.owedJoin).sized hsa) hrun
      ((by rw [hF1]; exact paid_later Fa g.owedPlanes : Later Fa F1).trans hlb)
  have hplain : ∀ cl ∈ c.take 4, cl.eqFirst = none := by
    rw [h4]
    intro cl hcl
    simp only [four8, List.mem_cons, List.mem_nil_iff, or_false] at hcl
    rcases hcl with rfl | rfl | rfl | rfl <;> rfl
  rw [wsumK_plain Reading.gl atS t b' hb y _ (c.take 4) _ hplain, h4]
  have hvals : vals4 π ent q y = (four8 tl g).map (claimValue Reading.gl
      (refWorld Reading.gl v'.F [winOf g.leaves] (ent q y) y)) := by
    have hg' : (blank u tl).heard = some g := hg
    simp only [vals4, hq1, hv, hg']
    rw [four8_blank]
  have h5 := hFu4 q t b' y (blank u tl) g hft' hfull hb hq1 hg
  rw [four8_blank] at h5
  have hm : (four8 tl g).map (claimValue Reading.gl (worldAt Reading.gl b'.L b'.F y)) =
      (four8 tl g).map (claimValue Reading.gl
        (refWorld Reading.gl v'.F [winOf g.leaves] (ent q y) y)) :=
    List.map_congr_left fun cl hcl =>
      claim_ref Reading.gl cl b'.L v'.F b'.F [winOf g.leaves] (ent q y) y gv'.1
        (fun w hw => by
          rw [List.mem_singleton] at hw
          rw [hw]
          exact hlaid)
        (fun x hx => (hslots cl hcl x hx).imp (fun h => ⟨_, List.mem_singleton.2 rfl, h⟩) id)
        (h5 cl hcl).1 (h5 cl hcl).2
  rw [hvals, hm]

/-- **RunOk of the whole run.** -/
theorem k8_runOk_all (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (u : HTailF2)
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
    (ent : α × Option Pub9 → Bound GE8 → ℕ → ℕ → ℕ → GE8)
    (hOk4 : ∀ q v tlb g, Ok q → q.2 = some v → (π q.1).1 = some tlb → tlb.heard = some g →
      Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1)
    (hFu4 : ∀ q t b y tlb g, Fx9 φ Ok q t → Fu t → atS.get? t = some b →
      (π q.1).1 = some tlb → tlb.heard = some g → ∀ cl ∈ four8 tlb g,
      (∀ x ∈ cl.form.ents.toList, (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx =
        ent q y x.tree x.row x.idx) ∧
      ∀ r ∈ cl.runs.toList, ∀ i < r.n,
        (worldAt Reading.gl b.L b.F y).entry r.tree r.row (r.first + i) =
          ent q y r.tree r.row (r.first + i)) :
    RunOk Reading.gl atS (O9 φ Ok Fu) (Fx9 φ Ok) k8Run.2
      (fun n q y => numbered n (vals4 π ent q y) ++ tmRest π q y) (len8 π) :=
  k8_runOk φ Ok Fu u π hπ hkeep hOk hFu (fun n q y => numbered n (vals4 π ent q y))
    (k8_four φ Ok Fu u π hπ hkeep ent hOk4 hFu4)

end

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.k8_runOk_all
#print axioms VerifiableInference.Desc.K9L.take_four
#print axioms VerifiableInference.Desc.K9L.claim_ref
#print axioms VerifiableInference.Desc.K9L.k8_four
