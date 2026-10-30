-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LooksClose.lean: THE BATCHING KIND's OWN SUB-PROTOCOLS (K9: the draw,
the adding, the batching, the one equation, the shutting) AND THE CLOSING (K10) STAND IN
`KeepsLooks`
(Johnson/Desc/First/Link/Law/LooksWalk.lean), AT THEIR OWN TEXTS, WITH NO PREMISE ON THE STATE.
Theorems. No text already in the library turns.

Why. `looks_batch`, `looks_behind`, `looks_shut` (LooksAre.lean) speak of an accepting step under
«the ledger is well laid» and through the moves' law. `Meaning.K2.SeatKeeps` asks the makers bare.
  `foldE_inv`: a fold that may refuse hands on what each step hands on.
  `addEntry_looks`, `addRun_looks`, `addForm_looks`, `addRuns_looks`, `addOne_looks`,
    `addList_looks`: **the adding of a list of claims turns the weights' values alone: NO PREMISE ON
    THE SIZES** (Johnson/Desc/First/Batch/Add.lean).
  `keeps_set`: the lens's writing of a part whose context has the number, and whose ledger the
    looks, of what it has read.
  `looks_of_part`, `looks_of_pub`: what the invariant gives at the batching's lens and snapshot.
  `draw_decides` · `adds_decides` (from the same of the function of claims) · `batch_whole` ·
    `oneEq_whole` · `closing_whole` · `shut_whole` · `closeOf_whole`.
Limits. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.LooksRuns
import Johnson.Desc.First.Batch.Place
import Johnson.Desc.First.LedgerLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K9
open VerifiableInference.Desc.K9L

/-- A fold that may refuse hands on what each step hands on. -/
theorem foldE_inv {α β : Type} (f : β → α → Ans β) (P : β → Prop)
    (hf : ∀ b a b', f b a = .ok b' → P b → P b') :
    ∀ (l : List α) (b b' : β), l.foldlM f b = .ok b' → P b → P b'
  | [], b, b', h, hb => by
    obtain rfl : b = b' := Except.ok.inj h
    exact hb
  | a :: l, b, b', h, hb => by
    rw [List.foldlM_cons] at h
    obtain ⟨b₁, h1, h2⟩ := ok_bind h
    exact foldE_inv f P hf l b₁ b' h2 (hf b a b₁ h1 hb)

theorem addEntry_looks {w : E} {tr tr' : Array HTree} {x : Ent}
    (h : addEntry w tr x = .ok tr') : tr'.map look = tr.map look := by
  unfold addEntry at h
  obtain ⟨_, _, h⟩ := ok_bind h
  rw [← Except.ok.inj h]
  exact map_modify_same look _ (fun X => look_rows_modify X _ _) tr x.tree

theorem addRun_looks {w : E} {tr tr' : Array HTree} {r : Run2}
    (h : addRun w tr r = .ok tr') : tr'.map look = tr.map look := by
  unfold addRun at h
  obtain ⟨_, _, h⟩ := ok_bind h
  rw [← Except.ok.inj h]
  exact map_modify_same look _ (fun X => look_rows_modify X _ _) tr r.tree

theorem addForm_looks {F G : Fork} {w : E} {a : Aff} (h : addForm F w a = .ok G) :
    G.trees.map look = F.trees.map look := by
  unfold addForm at h
  dsimp only at h
  obtain ⟨tr, h1, h⟩ := ok_bind h
  obtain ⟨LS, _, h⟩ := ok_bind h
  rw [← Except.ok.inj h]
  rw [← Array.foldlM_toList] at h1
  exact foldE_inv (addEntry w) (fun t => t.map look = F.trees.map look)
    (fun _ _ _ e hb => (addEntry_looks e).trans hb) _ _ _ h1 rfl

theorem addRuns_looks {F G : Fork} {w : E} {runs : Array Run2} (h : addRuns F w runs = .ok G) :
    G.trees.map look = F.trees.map look := by
  unfold addRuns at h
  dsimp only at h
  obtain ⟨tr, h1, h⟩ := ok_bind h
  rw [← Except.ok.inj h]
  rw [← Array.foldlM_toList] at h1
  exact foldE_inv (addRun w) (fun t => t.map look = F.trees.map look)
    (fun _ _ _ e hb => (addRun_looks e).trans hb) _ _ _ h1 rfl

theorem addOne_looks {F G : Fork} {cl : Claim} (h : addOne F cl = .ok G) :
    G.trees.map look = F.trees.map look := by
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
  rw [addRuns_looks h, addForm_looks h1, e0]

/-- **The adding of a list of claims leaves the looks: no premise on the sizes.** -/
theorem addList_looks {F G : Fork} {cls : List Claim} (h : addList F cls = .ok G) :
    G.trees.map look = F.trees.map look :=
  foldE_inv addOne (fun H => H.trees.map look = F.trees.map look)
    (fun _ _ _ e hb => (addOne_looks e).trans hb) cls F G h rfl

theorem there_ok {α : Type} {n : String} {o : Option α} {x : α} (h : there n o = .ok x) :
    o = some x := by
  cases o with
  | none => exact nomatch h
  | some y => exact congrArg some (Except.ok.inj h)

section
variable (shOf : ℕ → List Look)

/-- The lens's writing of a part. -/
theorem keeps_set {s : S} {q p : K9.Part} (hq : atS.get? s = some q) (el : p.L.link = q.L.link)
    (ef : p.F.trees.map look = q.F.trees.map look) : KeepsLooks shOf s (atS.set s p) := by
  have hL := (part_reads s q hq).1
  have hF := fork_part s q hq
  exact fun hs G L hG hL' => keeps_puts shOf hL hF (u := s) hL hF el ef hs G L hG hL'

/-- **What the invariant gives at the batching's lens**: the part's ledger has the looks of the
part's link's number; so has the snapshot's (`pubOf`): what a clause of Ok on the snapshot's looks
is paid from, at a reached state. -/
theorem looks_of_part {s : S} {p : K9.Part} (h : LooksInv shOf s) (hp : atS.get? s = some p) :
    LooksAre (shOf p.L.link) p.F := h p.F p.L (fork_part s p hp) (part_reads s p hp).1

theorem looks_of_pub {s : S} {p : K9.Part} (h : LooksInv shOf s) (hp : atS.get? s = some p) :
    (pubOf p).F.trees.toList.map look = shOf p.L.link := looks_of_part shOf h hp

/-- The batching draw. -/
theorem draw_decides {Cl : Type} (p : Where) :
    Decides (KeepsLooks shOf) (drawAlone (Cl := Cl) atS p) := by
  intro s rs gs s' h
  simp only [drawAlone] at h
  split at h
  · obtain ⟨q, hq, h⟩ := ok_bind h
    obtain ⟨chi, _, h⟩ := ok_bind h
    obtain ⟨o, ho, h⟩ := ok_bind h
    obtain rfl := Except.ok.inj h
    exact keeps_set shOf (there_ok hq) (drawn_link _ _ _ _ _ _ _ ho)
      (sameLooks_of fun sh => looks_draw _ _ _ _ _ _ _ ho)
  · exact nomatch h

/-- Claims made and added. -/
theorem adds_decides {Cl : Type} (p : Where) (piece : ℕ) (what : String)
    {claims : S → Except String (List Claim × S)} (hcl : FnCl (KeepsLooks shOf) claims) :
    Decides (KeepsLooks shOf) (adds (Cl := Cl) atS p piece what claims) := by
  intro s rs gs s' h
  simp only [adds] at h
  obtain ⟨s₀, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨x, hx, h⟩ := ok_bind h
  obtain ⟨q, hq, h⟩ := ok_bind h
  obtain ⟨F, hF, h⟩ := ok_bind h
  obtain rfl := Except.ok.inj h
  exact keeps_trans shOf _ _ _ (hcl s x hx)
    (keeps_set shOf (there_ok hq) rfl (addList_looks hF))

/-- **The batching.** -/
theorem batch_whole (p : Where) {claims : S → Except String (List Claim × S)}
    (hcl : FnCl (KeepsLooks shOf) claims) : Whole (KeepsLooks shOf) (batch atS p claims) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := ok_bind h
  exact keeps_trans shOf _ _ _ (draw_decides shOf p s rs gs t₁ h1)
    (adds_decides shOf p p.piece "the segment's" hcl t₁ [] [] s' h)

/-- The one equation: the ledger is marked as shut. -/
theorem oneEq_decides {Cl : Type} (p : Where) :
    Decides (KeepsLooks shOf) (oneEquation (Cl := Cl) atS p) := by
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
  exact keeps_set shOf (there_ok hq) (by show o.L.link = q.L.link; rw [e.1])
    (by show o.F.trees.map look = q.F.trees.map look; rw [e.2])

/-- A writing of the live state of the calls. -/
theorem keeps_putLive (s : S) (c : ChainCheck) : KeepsLooks shOf s (s.putLive c) := by
  unfold S.putLive
  split
  case h_2 => exact keeps_same shOf rfl rfl
  case h_1 L e =>
    refine keeps_same shOf (First.fork_putLink s _) ?_
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
theorem closing_decides {Cl : Type} (P : First.Close.Par) :
    Decides (KeepsLooks shOf) (closing (Cl := Cl) P) := by
  intro s rs gs s' h
  obtain ⟨r, _, rfl⟩ := Keeps.emap_ok h
  exact fun hs G L hG hL => keeps_putLive shOf s { s.live with frame := r.frame } hs G L hG hL

/-- The shutting. -/
theorem shut_decides {Cl : Type} (p : Where) (piece : ℕ) :
    Decides (KeepsLooks shOf) (shut (Cl := Cl) p piece) := by
  intro s rs gs s' h
  obtain ⟨L, hL, h⟩ := ok_bind h
  obtain rfl := Except.ok.inj h
  have hl := there_ok hL
  refine keeps_same shOf (First.fork_putLink s _) ?_
  have k := (rb_putLink s L (closed L L.check.frame) hl rfl).num
  exact k

/-- **What closes a segment, sub-protocol by sub-protocol.** -/
theorem closeOf_whole {Cl : Type} (p : Where) (P : First.Close.Par) :
    ∀ b ∈ closeOf (Cl := Cl) p P, Whole (KeepsLooks shOf) b := by
  intro b hb
  unfold closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact ⟨oneEq_decides (Cl := Cl) shOf p, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  · exact ⟨closing_decides shOf P, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  · exact ⟨shut_decides shOf p _, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.addList_looks
#print axioms VerifiableInference.Desc.LinkJoin.keeps_set
#print axioms VerifiableInference.Desc.LinkJoin.looks_of_part
#print axioms VerifiableInference.Desc.LinkJoin.looks_of_pub
#print axioms VerifiableInference.Desc.LinkJoin.draw_decides
#print axioms VerifiableInference.Desc.LinkJoin.adds_decides
#print axioms VerifiableInference.Desc.LinkJoin.batch_whole
#print axioms VerifiableInference.Desc.LinkJoin.oneEq_decides
#print axioms VerifiableInference.Desc.LinkJoin.closing_decides
#print axioms VerifiableInference.Desc.LinkJoin.shut_decides
#print axioms VerifiableInference.Desc.LinkJoin.closeOf_whole
