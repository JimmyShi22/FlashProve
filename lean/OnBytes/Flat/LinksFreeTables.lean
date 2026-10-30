-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksFreeTables.lean: the head's tables of reads at two requests: `TablesFree`
(OnBytes/Flat/LinksFreeHead.lean), one of the seven pieces of the check of the head at two requests.
Statements and proofs.

Where the request enters `Head.tablesOf` (OnBytes/Model/HeadTables.lean), by the program's text: at
one place, `costWeights cov ..`: so in the weights (the field `phi`) of three of the fifteen tables:
"hf@phiZ", "hr@phiC", "hr@rhoC". These vectors have the same lengths whatever the covered positions
are. The checked tokens (`Heard.win`), the one field in which what was heard differs, are not read.
`addFun` does not read the weights: neither where it refuses, nor in another field of what it
returns. No call of `tablesOf` touches the state of the check.

Main names:
  `AskAlike`: two askings for a table: all is equal but the weights, of which there are as many.
  `addFun_alike`: `addFun` at two lists of tables that are alike and two such askings: both refuse,
    or both return lists that are alike.
  `foldlM_addFun`: the same along two lists of askings.
  `tablesFree`: `TablesFree`.
Not claimed: anything on a run on a view. For proofs only; no module of the program imports this
file.


-/
import OnBytes.Flat.LinksFreeHead

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model OnBytes.Model.Head

/-- Closes `Blk.Keeps b` by the walk. -/
local macro "keeps_blk" : tactic => `(tactic| (show Over.K (m := Blk) _; keeps))

/-- An asking for a table, as `tablesOf` lists them: the first matrix, the number of parts, the
length of a stretch, the weights, the name. -/
abbrev Ask : Type := Nat × Nat × Nat × Array E × String

/-- Two askings: all is equal but the weights, of which there are as many. -/
def AskAlike (a a' : Ask) : Prop :=
  a.1 = a'.1 ∧ a.2.1 = a'.2.1 ∧ a.2.2.1 = a'.2.2.1 ∧ a.2.2.2.1.size = a'.2.2.2.1.size ∧
    a.2.2.2.2 = a'.2.2.2.2

theorem AskAlike.refl (a : Ask) : AskAlike a a := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem TablesAlike.refl (t : Tables) : TablesAlike t t :=
  ⟨rfl, All2.refl (fun _ => ⟨rfl, rfl⟩) _⟩

/-- The inner fold of `addFun`. -/
theorem addFun_fold (mats : Array TMat) (M0 Lf : Nat) {phi phi' : Array E}
    (hp : phi.size = phi'.size) :
    ∀ (l : List Nat) (s s' : Array HFun × Nat), FunsAlike s.1 s'.1 → s.2 = s'.2 →
      FunsAlike
          (l.foldl (fun (s : Array HFun × Nat) q =>
            (s.1.push { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 },
              s.2 + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf))) s).1
          (l.foldl (fun (s : Array HFun × Nat) q =>
            (s.1.push { mat := M0 + q, len := Lf, phi := phi', tree := 2, start := s.2 },
              s.2 + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf))) s').1 ∧
        (l.foldl (fun (s : Array HFun × Nat) q =>
            (s.1.push { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 },
              s.2 + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf))) s).2 =
          (l.foldl (fun (s : Array HFun × Nat) q =>
            (s.1.push { mat := M0 + q, len := Lf, phi := phi', tree := 2, start := s.2 },
              s.2 + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf))) s').2
  | [], _, _, h1, h2 => ⟨h1, h2⟩
  | q :: l, s, s', h1, h2 => by
    rw [List.foldl_cons, List.foldl_cons]
    refine addFun_fold mats M0 Lf hp l _ _ ?_ ?_
    · show All2 FunAlike (Array.push _ _).toList (Array.push _ _).toList
      rw [Array.toList_push, Array.toList_push]
      exact h1.append (.cons ⟨by rw [h2], hp⟩ .nil)
    · show s.2 + _ = s'.2 + _
      rw [h2]

/-- **One table more, at two lists that are alike.** -/
theorem addFun_alike (mats : Array TMat) {t t' : Tables} (ht : TablesAlike t t')
    (M0 parts Lf : Nat) {phi phi' : Array E} (hp : phi.size = phi'.size) (nm : String) :
    OptRel TablesAlike (addFun mats t M0 parts Lf phi nm) (addFun mats t' M0 parts Lf phi' nm) := by
  obtain ⟨et, hf⟩ := ht
  have ep : t'.p = t.p := by rw [et]
  have eb : t'.tab = t.tab := by rw [et]
  obtain ⟨h1, h2⟩ := addFun_fold mats M0 Lf hp (List.range parts) (t.funs, t.p) (t'.funs, t.p) hf
    rfl
  unfold addFun
  dsimp only
  rw [ep, eb, ← h2]
  split
  · trivial
  · exact ⟨rfl, h1⟩

/-- The same along two lists of askings. -/
theorem foldlM_addFun (mats : Array TMat) {l l' : List Ask} (h : All2 AskAlike l l') :
    ∀ {t t' : Tables}, TablesAlike t t' →
      OptRel TablesAlike
        (l.foldlM (fun t a => addFun mats t a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) t)
        (l'.foldlM (fun t a => addFun mats t a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) t') := by
  induction h with
  | nil => exact fun ht => ht
  | @cons a a' l l' ha _ ih =>
    intro t t' ht
    rw [List.foldlM_cons, List.foldlM_cons]
    obtain ⟨e1, e2, e3, e4, e5⟩ := ha
    rw [← e1, ← e2, ← e3, ← e5]
    exact optRel_bind (addFun_alike mats ht _ _ _ e4 _) fun _ _ k => ih k

/-- **The head's tables of reads at two requests.** -/
theorem tablesFree : TablesFree := by
  intro h L hp cov cov' x x' _ hx
  obtain ⟨ex, hw⟩ := hx
  generalize x'.win = w' at ex hw
  subst ex
  unfold tablesOf costWeights
  dsimp only
  refine cmpS.bind_same same_cmpS (by keeps) fun _ => ?_
  refine cmpS.bind_same same_cmpS (by keeps) fun ZV => ?_
  refine cmpS.bind_same same_cmpS (by keeps) fun lowN => ?_
  refine cmpS.bind_same same_cmpS (by keeps) fun _ => ?_
  refine cmpS.bind_same same_cmpS (by keeps) fun qFC => ?_
  refine cmpS.bind_same same_cmpS (by keeps) fun qROW => ?_
  refine cmpS.bind_same same_cmpS (by keeps) fun b0 => ?_
  refine cmpS.bind_same same_cmpS (by keeps) fun b1 => ?_
  refine cmpS.bind' (S := TablesAlike) (by keeps)
    (Cmp.blk.lift Eq (by keeps_blk) (getAs_rel _ (foldlM_addFun _ ?_ (TablesAlike.refl _))))
    fun t t' ht => ?_
  · refine .cons (AskAlike.refl _) (.cons ⟨rfl, rfl, rfl, ?_, rfl⟩ (.cons (AskAlike.refl _)
      (.cons (AskAlike.refl _) (.cons (AskAlike.refl _) (.cons (AskAlike.refl _)
      (.cons (AskAlike.refl _) (.cons (AskAlike.refl _) (.cons (AskAlike.refl _)
      (.cons (AskAlike.refl _) (.cons ⟨rfl, rfl, rfl, ?_, rfl⟩ (.cons ⟨rfl, rfl, rfl, ?_, rfl⟩
      (.cons (AskAlike.refl _) (.cons (AskAlike.refl _) (.cons (AskAlike.refl _)
      .nil))))))))))))))
    · simp only [Array.size_map, Array.size_range]
    · simp only [Array.size_mapIdx]
    · simp only [Array.size_mapIdx]
  · have ep : t'.p = t.p := by rw [ht.1]
    rw [ep]
    refine cmpS.bind_same same_cmpS (by keeps) fun _ => ?_
    exact cmpS.pure' ht

end OnBytes.Flat

#print axioms OnBytes.Flat.tablesFree
