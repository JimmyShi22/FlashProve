-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksRespHand.lean: `Resp.K` (OnBytes/Flat/LinksRespBase.lean) of the routines that
read or change the state of a sub-proof's check, by hand.

The walk of OnBytes/Flat/LinksRespTool.lean stops at a routine that is written as a function of the
state. Here are the theorems on these, under the names that the walk looks for: fourteen routines of
OnBytes/Model/Hide.lean (`SubM.slots`, `slot`, `takeSlots`, `hide`, `shown`, `batchBy`, `kap`,
`push`, `lin`, `setPlanClaims`, `claims`, `allTaken`, `owe`, `paid`), and `uEnt`, `t2Lin`, `pscRow`,
`HTailF2.weightsF`, `HTailF2.linTie`.

Main theorems beside these: `ask_same` (a question to the state whose answer does not hang on the
coefficients), `get_rel`, `hide_alike`, `hideRun_alike`, `resp_hideRun`, `resp_leadF`.

Not claimed: `Resp.K` of `SubM.settle`, of `LinkM.fork` or of any routine that returns a coefficient
or the state: these do not have it. For proofs only; no module of the program imports this file.


-/
import OnBytes.Flat.LinksRespTool

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model

/-- Opens `ForkAlike F F'` in a goal on all such F, F': F' becomes F with two other fields. Then
the step's text is split into its cases, and each is closed by what is at hand. -/
local macro "frame" : tactic => `(tactic| (
  intro F F' h
  obtain ⟨e, hT⟩ := h
  generalize F'.trees = T' at e hT
  generalize F'.c0 = c' at e
  subst e
  dsimp only
  repeat' split
  all_goals first
    | trivial
    | exact rfl
    | exact ⟨rfl, hT⟩
    | exact ⟨rfl, rfl, hT⟩))

theorem RespOf.OnBytes.Model.SubM.slots (n : Nat) : Resp.K (SubM.slots n) :=
  ⟨by keeps, change_rel (by unfold Fork.slots; frame)⟩

theorem RespOf.OnBytes.Model.SubM.slot : Resp.K SubM.slot := ⟨by keeps, ask_rel (by frame)⟩

theorem RespOf.OnBytes.Model.SubM.takeSlots (n : Nat) : Resp.K (SubM.takeSlots n) :=
  ⟨by keeps, take_rel (by frame)⟩

theorem RespOf.OnBytes.Model.SubM.hide (j : Nat) (s f : E) : Resp.K (SubM.hide j s f) :=
  ⟨by keeps, change_rel (by unfold Fork.hide; frame)⟩

theorem RespOf.OnBytes.Model.SubM.shown (j : Nat) : Resp.K (SubM.shown j) :=
  ⟨by keeps, ask_rel (by unfold Fork.shown; frame)⟩

theorem RespOf.OnBytes.Model.SubM.batchBy (d : E) : Resp.K (SubM.batchBy d) :=
  ⟨by keeps, change_rel (by unfold Fork.batchBy; frame)⟩

theorem RespOf.OnBytes.Model.SubM.kap : Resp.K SubM.kap :=
  ⟨by keeps, take_rel fun _ _ h => kap_alike h⟩

theorem RespOf.OnBytes.Model.SubM.push (w : E) (a : Aff) : Resp.K (SubM.push w a) :=
  ⟨by keeps, change_rel fun _ _ h => push_alike h w (AffAlike.refl a)⟩

theorem RespOf.OnBytes.Model.SubM.lin (f : Aff) : Resp.K (SubM.lin f) :=
  ⟨by keeps, change_rel fun _ _ h => lin_alike h (AffAlike.refl f)⟩

theorem RespOf.OnBytes.Model.SubM.setPlanClaims (n : Nat) : Resp.K (SubM.setPlanClaims n) :=
  ⟨by keeps, change_rel (by frame)⟩

theorem RespOf.OnBytes.Model.SubM.claims : Resp.K SubM.claims := ⟨by keeps, ask_rel (by frame)⟩

theorem RespOf.OnBytes.Model.SubM.allTaken : Resp.K SubM.allTaken :=
  ⟨by keeps, ask_rel (by unfold Fork.kapAllTakenF; frame)⟩

theorem RespOf.OnBytes.Model.SubM.owe (what : String) : Resp.K (SubM.owe what) :=
  ⟨by keeps, take_rel (by unfold Fork.owe; frame)⟩

theorem RespOf.OnBytes.Model.SubM.paid (i : Nat) : Resp.K (SubM.paid i) :=
  ⟨by keeps, change_rel (by unfold Fork.paid; frame)⟩

/-! ## Steps that read what two states that are alike share -/

/-- A question to the state whose answer does not hang on the coefficients of the one equation. -/
theorem ask_same {α : Type} (f : Fork → Option α)
    (h : ∀ (F : Fork) (T' : Array HTree) (c' : E), F.trees.map eraseTree = T'.map eraseTree →
      f { F with trees := T', c0 := c' } = f F) : Resp.K (SubM.ask f) := by
  refine ⟨by keeps, ask_rel ?_⟩
  intro F F' hF
  obtain ⟨e, h1⟩ := hF
  generalize F'.trees = T' at e h1
  generalize F'.c0 = c' at e
  subst e
  rw [h F T' c' h1]
  exact OptRel.refl (fun _ => rfl) _

/-- The state itself, read at two states that are alike. -/
theorem get_rel : cmpA.Rel ForkAlike (get : SubM Fork) get := fun _ _ hs _ _ => ⟨⟨hs, hs⟩, rfl⟩

theorem RespOf.OnBytes.Model.uEnt (t x : Nat) : Resp.K (uEnt t x) := by
  refine ⟨by keeps, ?_⟩
  unfold _root_.OnBytes.Model.uEnt
  refine cmpA.bind' (by keeps) get_rel fun F F' hF => ?_
  rw [trees_read hF.2 (fun o => (o.map (·.K)).getD 0) (fun o => by cases o <;> rfl) t]
  exact (resp_sub (by resp)).2

theorem RespOf.OnBytes.Model.t2Lin (a : Aff) (runs : Array Run2) : Resp.K (t2Lin a runs) := by
  have h : ∀ k, Resp.K (SubM.change (·.pushRuns k runs)) := fun k =>
    ⟨by keeps, change_rel fun _ _ h => pushRuns_alike h k k (All2.refl Run2Alike.refl _)⟩
  unfold _root_.OnBytes.Model.t2Lin
  resp

theorem hide_alike {F F' : Fork} (h : ForkAlike F F') (j : Nat) (s f : E) :
    OptRel ForkAlike (F.hide j s f) (F'.hide j s f) := by
  revert F F'
  unfold Fork.hide
  frame

theorem hideRun_alike {F F' : Fork} (h : ForkAlike F F') (first : Nat) (v : Array E) (f : E) :
    OptRel ForkAlike (F.hideRun first v f) (F'.hideRun first v f) := by
  have key : ∀ (l : List E) (j : Nat) (G G' : Fork), ForkAlike G G' →
      OptRel (fun x x' => x.1 = x'.1 ∧ ForkAlike x.2 x'.2)
        (l.foldlM (Fork.hideStep f) (j, G)) (l.foldlM (Fork.hideStep f) (j, G')) := by
    intro l
    induction l with
    | nil => exact fun _ _ _ hG => ⟨rfl, hG⟩
    | cons y l ih =>
      intro j G G' hG
      rw [List.foldlM_cons, List.foldlM_cons]
      refine optRel_bind (S := fun x x' => x.1 = x'.1 ∧ ForkAlike x.2 x'.2) ?_ ?_
      · exact optRel_map' (hide_alike hG j y f) fun _ _ k => ⟨rfl, k⟩
      · intro x x' k
        obtain ⟨j1, G1⟩ := x
        obtain ⟨j2, G2⟩ := x'
        obtain ⟨k1, k2⟩ := k
        have k1' : j1 = j2 := k1
        subst k1'
        exact ih _ _ _ k2
  have h0 := key v.toList first F F' h
  unfold Fork.hideRun
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]
  revert h0
  cases List.foldlM (Fork.hideStep f) (first, F) v.toList <;>
    cases List.foldlM (Fork.hideStep f) (first, F') v.toList <;> intro h0
  · trivial
  · exact h0.elim
  · exact h0.elim
  · exact h0.2

theorem resp_hideRun (first : Nat) (v : Array E) (f : E) :
    Resp.K (SubM.change (·.hideRun first v f)) :=
  ⟨by keeps, change_rel fun _ _ h => hideRun_alike h first v f⟩

theorem RespOf.OnBytes.Model.pscRow (p : Psc) (S0 : E) (kept : Aff) :
    Resp.K (pscRow p S0 kept) := by
  have h := resp_hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE)
  unfold _root_.OnBytes.Model.pscRow
  resp

theorem RespOf.OnBytes.Model.HTailF2.weightsF (tl : HTailF2) : Resp.K tl.weightsF := by
  have h : Resp.K (SubM.ask fun F => tl.powersF F) :=
    ask_same _ fun _ _ _ _ => rfl
  unfold _root_.OnBytes.Model.HTailF2.weightsF
  resp

theorem resp_leadF (first : Nat) : Resp.K (SubM.ask fun F => HTailF2.leadF F first) :=
  ask_same _ fun _ _ _ _ => rfl

theorem RespOf.OnBytes.Model.HTailF2.linTie (tl : HTailF2) (mu : Nat) : Resp.K (tl.linTie mu) := by
  have h := resp_leadF (tl.eqFirst.getD mu 0)
  unfold _root_.OnBytes.Model.HTailF2.linTie
  resp

end OnBytes.Flat
