-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Names/ArrNamesWalk.lean: «THE OPEN LEDGER's ARRAYS HAVE THE PLAN's NAMES»:
THE SENTENCE ON THE FIRST CHAIN's STATE, THE TOOLS BY WHICH IT PASSES FROM A STATE TO THE NEXT, AND
TWO KINDS' SHARES (K8's DRAW · K1's LATER SENDING). MADE BY PROGRAM FROM THE LIBRARY's
Johnson/Desc/First/Link/Law/LooksWalk.lean, WITH AN ARRAY's NAME (`treeName`,
Johnson/Desc/K8/Honest/Names/TreeName.lean) IN THE PLACE OF ITS LOOK: every declaration of that file
that the instance `seatKeeps_arrNames` (Names/ArrNamesSeat.lean) wants and that names the looks, or
leans on one that does, under a new name; the others are called where they lie: that file is
imported. NO NEW ARGUMENT: the library's proofs, token for token, but for the turns that are named
here. None of the library's goals.
Why. The smallness test's second computation asks that the digits' array bears the name "ZZ"
(`piecesTile`, OnBytes/Model/Tail.lean). The library carries each array's look (kind, rows, columns,
number of virtual rows) from the planned ledger to every reached state; a look holds no name. Spent
in Johnson/Desc/K8/Honest/NamesAtBatch.lean.
KEPT AND RENAMED (17): LooksInv → ArrNamesInv · KeepsLooks → KeepsArrNames · keeps_refl →
keeps_reflN · keeps_trans → keeps_transN · keeps_of_cases → keeps_of_casesN · keeps_same →
keeps_sameN · keeps_none → keeps_noneN · keeps_puts → keeps_putsN · looksInv_none → arrNamesInv_none
· k8_steps → k8_stepsN · rootTaken_looks → rootTaken_arrNames · commitOne_looks → commitOne_arrNames
· commitAll_looks → commitAll_arrNames · commitBehind_looks → commitBehind_arrNames ·
commitStep_looks → commitStep_arrNames · commitOwn_looks → commitOwn_arrNames · k1_steps →
k1_stepsN.
CALLED WHERE THEY LIE (2): reads_puts · steps_under.
NOT WANTED BY THE INSTANCE, AND SO NOT MADE (5): looks_reach · looks_reach_from · hasFork_reach ·
hasFork_reach_from · quiet_steps.
THE GENERAL TURNS: look → treeName · Look → String · …looks… → …arrNames… · …Looks… → …ArrNames… ·
shOfBuilt → anOfBuilt · shOf_at → anOf_at · Stays → StaysN · the tactic stays → staysN · every other
kept name gets an N behind; the letter shOf stays, at the type ℕ → List String; in comments "look" →
"name". Lines over 100 signs are broken.
TURNED BY HAND: nothing.
Limits. ITS SOURCE's LIMITS ARE ITS OWN: one direction, from a yes or from a return; nothing says
that any state is reached. It is no second text of its source: it speaks of another field of an
array, and no law ties the two. The comments on the declarations are the source's, turned by the
same program: they were not written for this file. It stands in the source's own namespace, so that
every name resolves as there. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.First.Link.Law.LooksWalk
import Johnson.Desc.K8.Honest.Names.ArrNamesAre
import Johnson.Desc.K8.Honest.Names.TreeName

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (step_ok_iff)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)

section
variable (shOf : ℕ → List String)

/-- **Where a ledger and a link are open, the ledger has that link's names.** -/
def ArrNamesInv (s : S) : Prop :=
  ∀ G L, s.fork? = some G → s.link? = some L → ArrNamesAre (shOf L.link) G

/-- It passes from s to s'. -/
def KeepsArrNames (s s' : S) : Prop := ArrNamesInv shOf s → ArrNamesInv shOf s'

theorem keeps_reflN (s : S) : KeepsArrNames shOf s s := id

theorem keeps_transN (a b c : S) (h : KeepsArrNames shOf a b) (k : KeepsArrNames shOf b c) :
    KeepsArrNames shOf a c := fun x => k (h x)

/-- **The tool**: a maker, or a keeper. -/
theorem keeps_of_casesN {s s' : S}
    (h : ∀ G' L', s'.fork? = some G' → s'.link? = some L' → ArrNamesAre (shOf L'.link) G' ∨
      ∃ G L, s.fork? = some G ∧ s.link? = some L ∧ L.link = L'.link ∧
        G'.trees.map treeName = G.trees.map treeName) : KeepsArrNames shOf s s' := by
  intro hs G' L' hG hL
  rcases h G' L' hG hL with h1 | ⟨G, L, e1, e2, e3, e4⟩
  · exact h1
  · rw [← e3]
    exact arrNames_map e4 (hs G L e1 e2)

/-- The two readings are left. -/
theorem keeps_sameN {s s' : S} (hf : s'.fork? = s.fork?)
    (hl : s'.link?.map (·.link) = s.link?.map (·.link)) : KeepsArrNames shOf s s' := by
  refine keeps_of_casesN shOf fun G' L' hG hL => Or.inr ?_
  rw [hL] at hl
  cases e : s.link? with
  | none =>
    rw [e] at hl
    exact nomatch hl
  | some L =>
    rw [e] at hl
    exact ⟨G', L, hf ▸ hG, rfl, (Option.some.inj hl).symm, rfl⟩

/-- No ledger is open behind. -/
theorem keeps_noneN {s s' : S} (hf : s'.fork? = none) : KeepsArrNames shOf s s' := by
  intro _ G' L' hG _
  rw [hf] at hG
  exact nomatch hG

end

/-- A writing of a context of the same number and of a ledger with the same names. u: any state
with s's two readings (what a kind lays back beside them). -/
theorem keeps_putsN (shOf : ℕ → List String) {s u : S} {L0 L : LinkCtx} {F0 F : Fork}
    (hL : s.link? = some L0) (hF : s.fork? = some F0) (uL : u.link? = some L0)
    (uF : u.fork? = some F0) (el : L.link = L0.link)
    (ef : F.trees.map treeName = F0.trees.map treeName) :
    KeepsArrNames shOf s ((u.putLink L).putFork F) := by
  obtain ⟨r1, r2⟩ := reads_puts u L0 F0 uL uF L F
  refine keeps_of_casesN shOf fun G' L' hG hL' => Or.inr ⟨F0, L0, hF, hL, ?_, ?_⟩
  · rw [← Option.some.inj (r1.symm.trans hL'), el]
  · rw [← Option.some.inj (r2.symm.trans hG), ef]

/-- Where no ledger is open the property holds idly. -/
theorem arrNamesInv_none (shOf : ℕ → List String) {s : S} (h : s.fork? = none) :
    ArrNamesInv shOf s := by
  intro G _ hG _
  rw [h] at hG
  exact nomatch hG

/-- **K8: the approximate range proof's draw.** -/
theorem k8_stepsN {Cl : Type} (shOf : ℕ → List String) (p : First.K8.Par) :
    (First.K8.approximateRangeProofDrawKind (Cl := Cl) First.K8.atS p).Steps (KeepsArrNames shOf) := by
  intro s rs gs s' h
  obtain ⟨r, rfl⟩ := First.K8.decide_one First.K8.atS p s s' rs gs h
  obtain ⟨tl, _, hm⟩ := (First.K8.decide_atS_iff p s s' r gs).1 h
  rw [hm.2.2.2.2.2.2.2.2]
  exact keeps_sameN shOf (First.K8.putTl_fork _ _) (by rw [First.K8.putTl_link])

theorem rootTaken_arrNames (F : Fork) (t w : ℕ) :
    (F.rootTaken t w).trees.map treeName = F.trees.map treeName :=
  map_modify_same treeName (fun X => { X with root := some w }) (fun _ => rfl) F.trees t

theorem commitOne_arrNames {L : LinkCtx} {F F' : Fork} {t : ℕ} (h : L3.commitOne L F t = .ok F') :
    F'.trees.map treeName = F.trees.map treeName := by
  simp only [L3.commitOne] at h
  split at h <;> split at h <;> first
    | (injection h with h; subst h; exact rootTaken_arrNames _ _ _)
    | cases h

theorem commitAll_arrNames {L : LinkCtx} : ∀ (ts : List ℕ) (F F' : Fork),
    ts.foldlM (L3.commitOne L) F = .ok F' → F'.trees.map treeName = F.trees.map treeName
  | [], F, F', h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact rfl
  | t :: ts, F, F', h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    cases h1 : L3.commitOne L F t with
    | error e => simp [h1] at h
    | ok F₁ =>
      simp only [h1] at h
      exact (commitAll_arrNames ts F₁ F' h).trans (commitOne_arrNames h1)

theorem commitBehind_arrNames {L L' : LinkCtx} {check : ChainCheck} {F F' : Fork} {ts : List ℕ}
    (h : L3.commitBehind L check F ts = .ok (L', F')) :
    L'.link = L.link ∧ F'.trees.map treeName = F.trees.map treeName := by
  simp only [L3.commitBehind, bind, Except.bind] at h
  cases h1 : ts.foldlM (L3.commitOne L) F with
  | error e => simp [h1] at h
  | ok F₁ =>
    simp only [h1] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2]
      exact ⟨rfl, commitAll_arrNames ts F F₁ h1⟩
    · cases h

theorem commitStep_arrNames {W : Type} {send : L3.Send W} {ts : List ℕ} {s s' : L3.St W}
    {rs : List Fmt.RoundView} (h : L3.commitStep send ts s rs = .ok s') :
    s'.L.link = s.L.link ∧ s'.F.trees.map treeName = s.F.trees.map treeName := by
  simp only [L3.commitStep, bind, Except.bind] at h
  cases h0 : L3.commitFront s.L with
  | error e => simp [h0] at h
  | ok u =>
    simp only [h0] at h
    cases h1 : send s.L.check s.w rs with
    | error e => simp [h1] at h
    | ok x =>
      simp only [h1] at h
      cases h2 : L3.commitBehind s.L x.1 s.F ts with
      | error e => simp [h2] at h
      | ok y =>
        simp only [h2, pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact commitBehind_arrNames (L' := y.1) (F' := y.2) h2

theorem commitOwn_arrNames {Cl : Type} {P : K1.Par} {link moment : ℕ} {arrays : Option (List ℕ)}
    {x y : K1.Owing (L3.St (_root_.Desc.Plain.DState Unit))} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (K1.commitOwn (Cl := Cl) P link moment arrays).decide x rs gs = .ok y) :
    y.held.L.link = x.held.L.link ∧ y.held.F.trees.map treeName = x.held.F.trees.map treeName := by
  simp only [K1.commitOwn] at h
  split at h
  · split at h
    · cases h
    · rename_i ts
      cases h1 : L3.commitStep (K1.laterOwn P x.owed) ts x.held rs with
      | error e => simp [h1, Except.map] at h
      | ok z =>
        simp only [h1, Except.map, Except.ok.injEq] at h
        subst h
        exact commitStep_arrNames h1
  · cases h

/-- **K1: a segment's later sending.** -/
theorem k1_stepsN {Cl : Type} (shOf : ℕ → List String) (P : K1.Par) (link moment : ℕ)
    (arrays : Option (List ℕ)) :
    (K1.commitAtS (Cl := Cl) P link moment arrays).Steps (KeepsArrNames shOf) := by
  intro s rs gs s' h
  simp only [K1.commitAtS] at h
  split at h
  · rename_i L F tl hL hF ht
    cases h1 : (K1.commitOwn (Cl := Cl) P link moment arrays).decide
        { owed := K1.owedOf s, held := { L := L, F := F, tl := tl, w := K1.stateOf s () } } rs
        gs with
    | error e => simp [h1, Except.map] at h
    | ok y =>
      simp only [h1, Except.map, Except.ok.injEq] at h
      obtain ⟨e1, e2⟩ := commitOwn_arrNames h1
      rw [← h]
      exact keeps_putsN shOf hL hF (u := K1.laid s y.held.w) hL hF e1 e2
  · cases h

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.keeps_reflN
#print axioms VerifiableInference.Desc.LinkJoin.keeps_transN
#print axioms VerifiableInference.Desc.LinkJoin.keeps_of_casesN
#print axioms VerifiableInference.Desc.LinkJoin.keeps_sameN
#print axioms VerifiableInference.Desc.LinkJoin.keeps_noneN
#print axioms VerifiableInference.Desc.LinkJoin.keeps_putsN
#print axioms VerifiableInference.Desc.LinkJoin.arrNamesInv_none
#print axioms VerifiableInference.Desc.LinkJoin.k8_stepsN
#print axioms VerifiableInference.Desc.LinkJoin.rootTaken_arrNames
#print axioms VerifiableInference.Desc.LinkJoin.commitOne_arrNames
#print axioms VerifiableInference.Desc.LinkJoin.commitAll_arrNames
#print axioms VerifiableInference.Desc.LinkJoin.commitBehind_arrNames
#print axioms VerifiableInference.Desc.LinkJoin.commitStep_arrNames
#print axioms VerifiableInference.Desc.LinkJoin.commitOwn_arrNames
#print axioms VerifiableInference.Desc.LinkJoin.k1_stepsN
