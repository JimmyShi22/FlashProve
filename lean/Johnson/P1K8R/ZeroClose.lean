-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/ZeroClose.lean: THE BATCHING, THE ONE EQUATION, THE CLOSING AND THE SHUTTING STAND IN
`KeepsZero`. NEW AGAINST THE LIBRARY's FILE: THE ADDING OF AN ENTRY AND OF A RUN WRITES A ROW's
WEIGHTS L ALONE (`addEntry_l0s`, `addRun_l0s`: a side condition that the looks do not have). MADE BY
PROGRAM FROM THE LIBRARY's Johnson/Desc/First/Link/Law/LooksClose.lean, WITH THE ROWS' FIRST COLUMNS
(`l0s`, Johnson/P1K8R/ZeroFrame.lean) IN THE PLACE OF THE ARRAYS' LOOKS AND `KeepsZero` IN THE PLACE
OF KeepsLooks: every declaration of that file that names the looks, or leans on one that does, under
a new name; the others are called where they lie. None of the library's goals. No prover stands in
it; nothing on completeness, soundness or hiding.

  `addEntry_l0s`, `addRun_l0s`, `addForm_l0s`, `addRuns_l0s`, `addOne_l0s`, **`addList_l0s`**   the
      adding of claims leaves the first columns
  `kz_set`, `zero_of_part`, `zero_of_pub`, `drawn_l0s`   the lens's writing; the draw
  `draw_decidesZ`, `adds_decidesZ`, **`batch_wholeZ`**   the batching
  `oneEq_decidesZ`, `kz_putLive`, `closing_decidesZ`, `shut_decidesZ`, **`closeOf_wholeZ`**   what
      closes a segment
Limits. At the batching's lens atS. That the claims' function stands in `KeepsZero` is a premise of
`adds_decidesZ` and `batch_wholeZ`. Nothing on any reached state.

-/
import Johnson.P1K8R.ZeroRuns
import Johnson.Desc.First.Link.Law.LooksClose

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K9
open VerifiableInference.Desc.K9L
open P1K8 (l0At AllZero l0s ZeroInv KeepsZero allZero_map allZero_trees allZero_frame l0s_of_frame
  l0s_of_sums l0s_rows_map l0s_rows_modify allZero_laid allZero_start fill_l0s allZero_fill
  allZero_rests kz_refl kz_trans kz_of_cases kz_same kz_none zeroInv_none kz_trees)

theorem addEntry_l0s {w : E} {tr tr' : Array HTree} {x : Ent}
    (h : addEntry w tr x = .ok tr') : tr'.map l0s = tr.map l0s := by
  unfold addEntry at h
  obtain ⟨_, _, h⟩ := ok_bind h
  rw [← Except.ok.inj h]
  refine map_modify_same l0s _ ?_ tr x.tree
  intro X
  exact l0s_rows_modify X _ _ fun _ => rfl

theorem addRun_l0s {w : E} {tr tr' : Array HTree} {r : Run2}
    (h : addRun w tr r = .ok tr') : tr'.map l0s = tr.map l0s := by
  unfold addRun at h
  obtain ⟨_, _, h⟩ := ok_bind h
  rw [← Except.ok.inj h]
  refine map_modify_same l0s _ ?_ tr r.tree
  intro X
  exact l0s_rows_modify X _ _ fun _ => rfl

theorem addForm_l0s {F G : Fork} {w : E} {a : Aff} (h : addForm F w a = .ok G) :
    G.trees.map l0s = F.trees.map l0s := by
  unfold addForm at h
  dsimp only at h
  obtain ⟨tr, h1, h⟩ := ok_bind h
  obtain ⟨LS, _, h⟩ := ok_bind h
  rw [← Except.ok.inj h]
  rw [← Array.foldlM_toList] at h1
  exact foldE_inv (addEntry w) (fun t => t.map l0s = F.trees.map l0s)
    (fun _ _ _ e hb => (addEntry_l0s e).trans hb) _ _ _ h1 rfl

theorem addRuns_l0s {F G : Fork} {w : E} {runs : Array Run2} (h : addRuns F w runs = .ok G) :
    G.trees.map l0s = F.trees.map l0s := by
  unfold addRuns at h
  dsimp only at h
  obtain ⟨tr, h1, h⟩ := ok_bind h
  rw [← Except.ok.inj h]
  rw [← Array.foldlM_toList] at h1
  exact foldE_inv (addRun w) (fun t => t.map l0s = F.trees.map l0s)
    (fun _ _ _ e hb => (addRun_l0s e).trans hb) _ _ _ h1 rfl

theorem addOne_l0s {F G : Fork} {cl : Claim} (h : addOne F cl = .ok G) :
    G.trees.map l0s = F.trees.map l0s := by
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
  rw [addRuns_l0s h, addForm_l0s h1, e0]

/-- **The adding of a list of claims leaves the first columns: no premise on the sizes.** -/
theorem addList_l0s {F G : Fork} {cls : List Claim} (h : addList F cls = .ok G) :
    G.trees.map l0s = F.trees.map l0s :=
  foldE_inv addOne (fun H => H.trees.map l0s = F.trees.map l0s)
    (fun _ _ _ e hb => (addOne_l0s e).trans hb) cls F G h rfl

section

/-- The lens's writing of a part. -/
theorem kz_set {s : S} {q p : K9.Part} (hq : atS.get? s = some q) (el : p.L.link = q.L.link)
    (ef : p.F.trees.map l0s = q.F.trees.map l0s) : KeepsZero s (atS.set s p) := by
  have hL := (part_reads s q hq).1
  have hF := fork_part s q hq
  exact fun hs G hG => kzL_puts hL hF (u := s) hL hF el ef hs G hG

/-- **What the invariant gives at the batching's lens**: the part's ledger has it; so has the
snapshot's (`pubOf`). -/
theorem zero_of_part {s : S} {p : K9.Part} (h : ZeroInv s) (hp : atS.get? s = some p) :
    AllZero p.F := h p.F (fork_part s p hp)

theorem zero_of_pub {s : S} {p : K9.Part} (h : ZeroInv s) (hp : atS.get? s = some p) :
    AllZero (pubOf p).F := allZero_trees (F := p.F) rfl (zero_of_part h hp)

/-- The batching's draw leaves the first columns: it fills the weights that are not yet there. -/
theorem drawn_l0s (rows : ℕ) (chi : E) (owed : Option ℕ) (used : ℕ) (L : LinkCtx) (F : Fork)
    (o : K9.Drawn) (h : drawnClean rows chi owed used L F = .ok o) :
    o.F.trees.map l0s = F.trees.map l0s := by
  unfold drawnClean at h
  obtain ⟨o', ho, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain rfl : o' = o := Except.ok.inj h
  unfold drawn at ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  obtain ⟨_, _, ho⟩ := ok_bind ho
  rw [← Except.ok.inj ho]
  exact fill_l0s F L.list

/-- The batching draw. -/
theorem draw_decidesZ {Cl : Type} (p : Where) :
    Decides KeepsZero (drawAlone (Cl := Cl) atS p) := by
  intro s rs gs s' h
  simp only [drawAlone] at h
  split at h
  · obtain ⟨q, hq, h⟩ := ok_bind h
    obtain ⟨chi, _, h⟩ := ok_bind h
    obtain ⟨o, ho, h⟩ := ok_bind h
    obtain rfl := Except.ok.inj h
    exact kz_set (there_ok hq) (drawn_link _ _ _ _ _ _ _ ho)
      (drawn_l0s _ _ _ _ _ _ _ ho)
  · exact nomatch h

/-- Claims made and added. -/
theorem adds_decidesZ {Cl : Type} (p : Where) (piece : ℕ) (what : String)
    {claims : S → Except String (List Claim × S)} (hcl : FnCl KeepsZero claims) :
    Decides KeepsZero (adds (Cl := Cl) atS p piece what claims) := by
  intro s rs gs s' h
  simp only [adds] at h
  obtain ⟨s₀, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨x, hx, h⟩ := ok_bind h
  obtain ⟨q, hq, h⟩ := ok_bind h
  obtain ⟨F, hF, h⟩ := ok_bind h
  obtain rfl := Except.ok.inj h
  exact kz_trans _ _ _ (hcl s x hx)
    (kz_set (there_ok hq) rfl (addList_l0s hF))

/-- **The batching.** -/
theorem batch_wholeZ (p : Where) {claims : S → Except String (List Claim × S)}
    (hcl : FnCl KeepsZero claims) : Whole KeepsZero (batch atS p claims) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := ok_bind h
  exact kz_trans _ _ _ (draw_decidesZ p s rs gs t₁ h1)
    (adds_decidesZ p p.piece "the segment's" hcl t₁ [] [] s' h)

/-- The one equation: the ledger is marked as shut. -/
theorem oneEq_decidesZ {Cl : Type} (p : Where) :
    Decides KeepsZero (oneEquation (Cl := Cl) atS p) := by
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
  exact kz_set (there_ok hq) (by show o.L.link = q.L.link; rw [e.1])
    (by show o.F.trees.map l0s = q.F.trees.map l0s; rw [e.2])

/-- A writing of the live state of the calls. -/
theorem kz_putLive (s : S) (c : ChainCheck) : KeepsZero s (s.putLive c) := by
  unfold S.putLive
  split
  case h_2 => exact kzL_same rfl rfl
  case h_1 L e =>
    refine kzL_same (First.fork_putLink s _) ?_
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
theorem closing_decidesZ {Cl : Type} (P : First.Close.Par) :
    Decides KeepsZero (closing (Cl := Cl) P) := by
  intro s rs gs s' h
  obtain ⟨r, _, rfl⟩ := Keeps.emap_ok h
  exact fun hs G hG => kz_putLive s { s.live with frame := r.frame } hs G hG

/-- The shutting. -/
theorem shut_decidesZ {Cl : Type} (p : Where) (piece : ℕ) :
    Decides KeepsZero (shut (Cl := Cl) p piece) := by
  intro s rs gs s' h
  obtain ⟨L, hL, h⟩ := ok_bind h
  obtain rfl := Except.ok.inj h
  have hl := there_ok hL
  refine kzL_same (First.fork_putLink s _) ?_
  have k := (rb_putLink s L (closed L L.check.frame) hl rfl).num
  exact k

/-- **What closes a segment, sub-protocol by sub-protocol.** -/
theorem closeOf_wholeZ {Cl : Type} (p : Where) (P : First.Close.Par) :
    ∀ b ∈ closeOf (Cl := Cl) p P, Whole KeepsZero b := by
  intro b hb
  unfold closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact ⟨oneEq_decidesZ (Cl := Cl) p, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  · exact ⟨closing_decidesZ P, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  · exact ⟨shut_decidesZ p _, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.addEntry_l0s
#print axioms VerifiableInference.Desc.LinkJoin.addRun_l0s
#print axioms VerifiableInference.Desc.LinkJoin.addForm_l0s
#print axioms VerifiableInference.Desc.LinkJoin.addRuns_l0s
#print axioms VerifiableInference.Desc.LinkJoin.addOne_l0s
#print axioms VerifiableInference.Desc.LinkJoin.addList_l0s
#print axioms VerifiableInference.Desc.LinkJoin.kz_set
#print axioms VerifiableInference.Desc.LinkJoin.zero_of_part
#print axioms VerifiableInference.Desc.LinkJoin.zero_of_pub
#print axioms VerifiableInference.Desc.LinkJoin.draw_decidesZ
#print axioms VerifiableInference.Desc.LinkJoin.adds_decidesZ
#print axioms VerifiableInference.Desc.LinkJoin.batch_wholeZ
#print axioms VerifiableInference.Desc.LinkJoin.oneEq_decidesZ
#print axioms VerifiableInference.Desc.LinkJoin.kz_putLive
#print axioms VerifiableInference.Desc.LinkJoin.closing_decidesZ
#print axioms VerifiableInference.Desc.LinkJoin.shut_decidesZ
#print axioms VerifiableInference.Desc.LinkJoin.closeOf_wholeZ
#print axioms VerifiableInference.Desc.LinkJoin.drawn_l0s
