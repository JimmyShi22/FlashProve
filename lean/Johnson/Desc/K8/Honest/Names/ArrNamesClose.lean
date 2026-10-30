-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Names/ArrNamesClose.lean: «THE OPEN LEDGER's ARRAYS HAVE THE PLAN's NAMES»:
THE BATCHING, THE SUB-PROTOCOL BEHIND IT AND THE CLOSING (K9 | K10). MADE BY PROGRAM FROM THE
LIBRARY's Johnson/Desc/First/Link/Law/LooksClose.lean, WITH AN ARRAY's NAME (`treeName`,
Johnson/Desc/K8/Honest/Names/TreeName.lean) IN THE PLACE OF ITS LOOK: every declaration of that file
that the instance `seatKeeps_arrNames` (Names/ArrNamesSeat.lean) wants and that names the looks, or
leans on one that does, under a new name; the others are called where they lie: that file is
imported. NO NEW ARGUMENT: the library's proofs, token for token, but for the turns that are named
here. None of the library's goals.
Why. The smallness test's second computation asks that the digits' array bears the name "ZZ"
(`piecesTile`, OnBytes/Model/Tail.lean). The library carries each array's look (kind, rows, columns,
number of virtual rows) from the planned ledger to every reached state; a look holds no name. Spent
in Johnson/Desc/K8/Honest/NamesAtBatch.lean.
KEPT AND RENAMED (15): addEntry_looks → addEntry_arrNames · addRun_looks → addRun_arrNames ·
addForm_looks → addForm_arrNames · addRuns_looks → addRuns_arrNames · addOne_looks → addOne_arrNames
· addList_looks → addList_arrNames · keeps_set → keeps_setN · draw_decides → draw_decidesN ·
adds_decides → adds_decidesN · batch_whole → batch_wholeN · oneEq_decides → oneEq_decidesN ·
keeps_putLive → keeps_putLiveN · closing_decides → closing_decidesN · shut_decides → shut_decidesN ·
closeOf_whole → closeOf_wholeN.
CALLED WHERE THEY LIE (2): foldE_inv · there_ok.
NOT WANTED BY THE INSTANCE, AND SO NOT MADE (2): looks_of_part · looks_of_pub.
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
import Johnson.Desc.First.Link.Law.LooksClose
import Johnson.Desc.K8.Honest.Names.TreeName
import Johnson.Desc.K8.Honest.Names.ArrNamesWalk
import Johnson.Desc.K8.Honest.Names.ArrNamesRuns
import Johnson.Desc.K8.Honest.Names.ArrNamesAre

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K9
open VerifiableInference.Desc.K9L

theorem addEntry_arrNames {w : E} {tr tr' : Array HTree} {x : Ent}
    (h : addEntry w tr x = .ok tr') : tr'.map treeName = tr.map treeName := by
  unfold addEntry at h
  obtain ⟨_, _, h⟩ := ok_bind h
  rw [← Except.ok.inj h]
  exact map_modify_same treeName _ (fun X => arrName_rows_modify X _ _) tr x.tree

theorem addRun_arrNames {w : E} {tr tr' : Array HTree} {r : Run2}
    (h : addRun w tr r = .ok tr') : tr'.map treeName = tr.map treeName := by
  unfold addRun at h
  obtain ⟨_, _, h⟩ := ok_bind h
  rw [← Except.ok.inj h]
  exact map_modify_same treeName _ (fun X => arrName_rows_modify X _ _) tr r.tree

theorem addForm_arrNames {F G : Fork} {w : E} {a : Aff} (h : addForm F w a = .ok G) :
    G.trees.map treeName = F.trees.map treeName := by
  unfold addForm at h
  dsimp only at h
  obtain ⟨tr, h1, h⟩ := ok_bind h
  obtain ⟨LS, _, h⟩ := ok_bind h
  rw [← Except.ok.inj h]
  rw [← Array.foldlM_toList] at h1
  exact foldE_inv (addEntry w) (fun t => t.map treeName = F.trees.map treeName)
    (fun _ _ _ e hb => (addEntry_arrNames e).trans hb) _ _ _ h1 rfl

theorem addRuns_arrNames {F G : Fork} {w : E} {runs : Array Run2} (h : addRuns F w runs = .ok G) :
    G.trees.map treeName = F.trees.map treeName := by
  unfold addRuns at h
  dsimp only at h
  obtain ⟨tr, h1, h⟩ := ok_bind h
  rw [← Except.ok.inj h]
  rw [← Array.foldlM_toList] at h1
  exact foldE_inv (addRun w) (fun t => t.map treeName = F.trees.map treeName)
    (fun _ _ _ e hb => (addRun_arrNames e).trans hb) _ _ _ h1 rfl

theorem addOne_arrNames {F G : Fork} {cl : Claim} (h : addOne F cl = .ok G) :
    G.trees.map treeName = F.trees.map treeName := by
  unfold addOne at h
  dsimp only at h
  obtain ⟨x, hx, h⟩ := ok_bind h
  obtain ⟨G₁, h1, h⟩ := ok_bind h
  have e0 : x.2.trees = F.trees := by
    unfold weightNext at hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    rw [← Except.ok.inj hx]
  rw [addRuns_arrNames h, addForm_arrNames h1, e0]

/-- **The adding of a list of claims leaves the names: no premise on the sizes.** -/
theorem addList_arrNames {F G : Fork} {cls : List Claim} (h : addList F cls = .ok G) :
    G.trees.map treeName = F.trees.map treeName :=
  foldE_inv addOne (fun H => H.trees.map treeName = F.trees.map treeName)
    (fun _ _ _ e hb => (addOne_arrNames e).trans hb) cls F G h rfl

section
variable (shOf : ℕ → List String)

/-- The lens's writing of a part. -/
theorem keeps_setN {s : S} {q p : K9.Part} (hq : atS.get? s = some q) (el : p.L.link = q.L.link)
    (ef : p.F.trees.map treeName = q.F.trees.map treeName) : KeepsArrNames shOf s
        (atS.set s p) := by
  have hL := (part_reads s q hq).1
  have hF := fork_part s q hq
  exact fun hs G L hG hL' => keeps_putsN shOf hL hF (u := s) hL hF el ef hs G L hG hL'

/-- The batching draw. -/
theorem draw_decidesN {Cl : Type} (p : Where) :
    Decides (KeepsArrNames shOf) (drawAlone (Cl := Cl) atS p) := by
  intro s rs gs s' h
  simp only [drawAlone] at h
  split at h
  · obtain ⟨q, hq, h⟩ := ok_bind h
    obtain ⟨chi, _, h⟩ := ok_bind h
    obtain ⟨o, ho, h⟩ := ok_bind h
    obtain rfl := Except.ok.inj h
    exact keeps_setN shOf (there_ok hq) (drawn_link _ _ _ _ _ _ _ ho)
      (sameArrNames_of fun sh => arrNames_draw _ _ _ _ _ _ _ ho)
  · exact nomatch h

/-- Claims made and added. -/
theorem adds_decidesN {Cl : Type} (p : Where) (piece : ℕ) (what : String)
    {claims : S → Except String (List Claim × S)} (hcl : FnCl (KeepsArrNames shOf) claims) :
    Decides (KeepsArrNames shOf) (adds (Cl := Cl) atS p piece what claims) := by
  intro s rs gs s' h
  simp only [adds] at h
  obtain ⟨s₀, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨x, hx, h⟩ := ok_bind h
  obtain ⟨q, hq, h⟩ := ok_bind h
  obtain ⟨F, hF, h⟩ := ok_bind h
  obtain rfl := Except.ok.inj h
  exact keeps_transN shOf _ _ _ (hcl s x hx)
    (keeps_setN shOf (there_ok hq) rfl (addList_arrNames hF))

/-- **The batching.** -/
theorem batch_wholeN (p : Where) {claims : S → Except String (List Claim × S)}
    (hcl : FnCl (KeepsArrNames shOf) claims) : Whole (KeepsArrNames shOf) (batch atS p claims) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := ok_bind h
  exact keeps_transN shOf _ _ _ (draw_decidesN shOf p s rs gs t₁ h1)
    (adds_decidesN shOf p p.piece "the segment's" hcl t₁ [] [] s' h)

/-- The one equation: the ledger is marked as shut. -/
theorem oneEq_decidesN {Cl : Type} (p : Where) :
    Decides (KeepsArrNames shOf) (oneEquation (Cl := Cl) atS p) := by
  intro s rs gs s' h
  simp only [oneEquation] at h
  obtain ⟨q, hq, h⟩ := ok_bind h
  obtain ⟨o, ho, h⟩ := ok_bind h
  obtain rfl := Except.ok.inj h
  have e : o.L = q.L ∧ o.F.trees = q.F.trees := by
    unfold door at ho
    obtain ⟨_, _, ho⟩ := ok_bind ho
    obtain ⟨x, hx, ho⟩ := ok_bind ho
    obtain ⟨_, _, ho⟩ := ok_bind ho
    obtain ⟨_, _, ho⟩ := ok_bind ho
    obtain ⟨_, _, ho⟩ := ok_bind ho
    obtain ⟨y, _, ho⟩ := ok_bind ho
    obtain ⟨d', _, ho⟩ := ok_bind ho
    rw [← Except.ok.inj ho]
    refine ⟨rfl, ?_⟩
    unfold equation at hx
    dsimp only at hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    obtain ⟨_, _, hx⟩ := ok_bind hx
    rw [← Except.ok.inj hx]
  exact keeps_setN shOf (there_ok hq) (by show o.L.link = q.L.link; rw [e.1])
    (by show o.F.trees.map treeName = q.F.trees.map treeName; rw [e.2])

/-- A writing of the live state of the calls. -/
theorem keeps_putLiveN (s : S) (c : ChainCheck) : KeepsArrNames shOf s (s.putLive c) := by
  unfold S.putLive
  split
  case h_2 => exact keeps_sameN shOf rfl rfl
  case h_1 L e =>
    refine keeps_sameN shOf (First.fork_putLink s _) ?_
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here with
    | head x =>
      by_cases ho : x.opened = true
      · have e' : x.L = L := by simpa [S.link?, ho] using e
        simp [S.putLink, S.link?, ho, e']
      · simp [S.link?, ho] at e
    | lay x =>
      have e' : x.L = L := Option.some.inj e
      show some L.link = some x.L.link
      rw [e']
    | att x =>
      have e' : x.L = L := Option.some.inj e
      show some L.link = some x.L.link
      rw [e']
    | _ => exact nomatch e

/-- The closing (K10). -/
theorem closing_decidesN {Cl : Type} (P : First.Close.Par) :
    Decides (KeepsArrNames shOf) (closing (Cl := Cl) P) := by
  intro s rs gs s' h
  obtain ⟨r, _, rfl⟩ := Keeps.emap_ok h
  exact fun hs G L hG hL => keeps_putLiveN shOf s { s.live with frame := r.frame } hs G L hG hL

/-- The shutting. -/
theorem shut_decidesN {Cl : Type} (p : Where) (piece : ℕ) :
    Decides (KeepsArrNames shOf) (shut (Cl := Cl) p piece) := by
  intro s rs gs s' h
  obtain ⟨L, hL, h⟩ := ok_bind h
  obtain rfl := Except.ok.inj h
  have hl := there_ok hL
  refine keeps_sameN shOf (First.fork_putLink s _) ?_
  have k := (rb_putLink s L (closed L L.check.frame) hl rfl).num
  exact k

/-- **What closes a segment, sub-protocol by sub-protocol.** -/
theorem closeOf_wholeN {Cl : Type} (p : Where) (P : First.Close.Par) :
    ∀ b ∈ closeOf (Cl := Cl) p P, Whole (KeepsArrNames shOf) b := by
  intro b hb
  unfold closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact ⟨oneEq_decidesN (Cl := Cl) shOf p, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  · exact ⟨closing_decidesN shOf P, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  · exact ⟨shut_decidesN shOf p _, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.addEntry_arrNames
#print axioms VerifiableInference.Desc.LinkJoin.addRun_arrNames
#print axioms VerifiableInference.Desc.LinkJoin.addForm_arrNames
#print axioms VerifiableInference.Desc.LinkJoin.addRuns_arrNames
#print axioms VerifiableInference.Desc.LinkJoin.addOne_arrNames
#print axioms VerifiableInference.Desc.LinkJoin.addList_arrNames
#print axioms VerifiableInference.Desc.LinkJoin.keeps_setN
#print axioms VerifiableInference.Desc.LinkJoin.draw_decidesN
#print axioms VerifiableInference.Desc.LinkJoin.adds_decidesN
#print axioms VerifiableInference.Desc.LinkJoin.batch_wholeN
#print axioms VerifiableInference.Desc.LinkJoin.oneEq_decidesN
#print axioms VerifiableInference.Desc.LinkJoin.keeps_putLiveN
#print axioms VerifiableInference.Desc.LinkJoin.closing_decidesN
#print axioms VerifiableInference.Desc.LinkJoin.shut_decidesN
#print axioms VerifiableInference.Desc.LinkJoin.closeOf_wholeN
