-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-


Johnson/Desc/First/Link/Law/BehindOfClose.lean: WHAT `hCar_heavy` (HCarHeavy.lean) ASKS BEHIND K10's
CLOSING (its premise hBehind: the four sizes; four facts on the code switch's front), FROM THE
CLOSING's OWN YES AND WHAT IS KNOWN IN FRONT. By calls. Theorems.

  `closeFrame_group`: a yes of the frame's closing: the statement in front has a group at the
    frame's group.
  `shape_behind`: a yes of the frame's closing keeps each message's shape.
  `behind_of_close`: **closeFrame (rdK s).1 (rdK s).2.1 (rdK s).2.2 es rs = .ok (rdBK s') ·
    ShapesAre
    in front at the frame's group · the frame's group of the link has gs's two numbers · gs.h ≤ gs.k
    · hH (under «the way in answers») · «the book behind the switch's sending is there» ⊢ the four
    sizes at s'.live.frame.rows ∧ hFr's four facts.** CALLED: `sizes_at_stage`
    (CarriedSizes.lean) · `closing_carried` (CarriedRows.lean),
    `closing_sameRows` (RidesMore.lean), `layout_of_shapes`' kin through `layout_behind`
    (CloseReads.lean) · `front_shapes_door`, `keptCount_door` (FrontStEnds.lean).
Limits. The premises stand. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.CloseReads
import Johnson.Desc.First.Link.Law.FrontStEnds
import Johnson.Desc.First.Link.Law.CarriedSizes
import Johnson.Desc.First.Close.Law.RidesMore
import Johnson.Desc.First.Close.Law.AtBlock
import Johnson.Desc.First.Close.Law.CubeOfShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice OnBytes.Params Johnson.G Johnson.Top.H
open VerifiableInference.Desc.Own (keptNos)
open VerifiableInference.Desc.First.Close
open VerifiableInference.Desc.First.K2Caller (doorZ)
open _root_.Tw.K2 (switchNotices)

theorem closeFrame_group {owed : Option ℕ} {f : ReqFrame} {S : Statement} {es : List Fmt.Entry}
    {rs : List Fmt.RoundView} {x : ReqFrame × Statement} (h : closeFrame owed f S es rs = .ok x) :
    ∃ G, S.groups[f.group]? = some G := by
  obtain ⟨f', S'⟩ := x
  obtain ⟨-, Lk, -, Gf, -, -, rows, hc, -⟩ := (closeFrame_iff owed f S es rs f' S').1 h
  obtain ⟨G, hG, -⟩ := closing_carried ((closing_iff _ _ _ _ _ _ _).2 hc)
  exact ⟨G, hG⟩

theorem shape_behind {owed : Option ℕ} {f : ReqFrame} {S : Statement} {es : List Fmt.Entry}
    {rs : List Fmt.RoundView} {x : ReqFrame × Statement} (h : closeFrame owed f S es rs = .ok x) (j : ℕ) :
    (x.2.oracles[j]?).map (fun o : OnBytes.Oracle => o.shape) =
      (S.oracles[j]?).map fun o : OnBytes.Oracle => o.shape := by
  obtain ⟨f', S'⟩ := x
  obtain ⟨-, Lk, -, Gf, -, -, rows, hc, -⟩ := (closeFrame_iff owed f S es rs f' S').1 h
  have h1 := congrArg (Option.map Prod.fst)
    ((closing_sameRows ((closing_iff _ _ _ _ _ _ _).2 hc)).2 j)
  simpa [Option.map_map, Function.comp_def] using h1

/-- **BEHIND THE CLOSING, FROM ITS OWN YES.** -/
theorem behind_of_close {s s' : First.S} {es : List Fmt.Entry} {rs : List Fmt.RoundView}
    (hcf : closeFrame (rdK s).1 (rdK s).2.1 (rdK s).2.2 es rs = .ok (rdBK s'))
    {lo : List (OracleShape × ℕ)} {kb : Fin lo.length → Bool} {no : Fin lo.length → ℕ}
    (H : ∀ Gr, (rdK s).2.2.groups[(rdK s).2.1.group]? = some Gr →
      ShapesAre (rdK s).2.2 Gr lo kb no) (hLA : LayoutAgrees lo kb)
    (gs : GroupSize) (hle : gs.h ≤ gs.k)
    (hGf : ∀ Gf, (rdK s).2.1.groups[(rdK s).2.1.link]? = some Gf → Gf.k = gs.k ∧ Gf.h = gs.h)
    (Z : ProofFile.Pub) (m : ℕ)
    (hH : ∀ t, doorZ Z m s' = some t → (ProofFile.pAtK2 Z m).stands = .head → ∀ b, s'.here ≠ .head b)
    (hBook : ∀ t fx', doorZ Z m s' = some t → First.K2.frontAt (ProofFile.pAtK2 Z m) t = some fx' →
      ∃ Bk, First.K2.bookAt (First.K2.par9 (ProofFile.pAtK2 Z m)).firstTree fx'.st t.book t.roots
        (switchNotices fx'.T fx'.others) = some Bk) :
    (s'.live.frame.rows.masks = 2 ∧
      s'.live.frame.rows.gamma.length = (stageOf gs 219).h + (stageOf gs 219).g ∧
      s'.live.frame.rows.layout.k = (stageOf gs 219).h + (stageOf gs 219).g ∧
      s'.live.frame.rows.layout.h = (stageOf gs 219).h) ∧
    ∀ t fx', doorZ Z m s' = some t → First.K2.frontAt (ProofFile.pAtK2 Z m) t = some fx' →
      (∃ Bk, First.K2.bookAt (First.K2.par9 (ProofFile.pAtK2 Z m)).firstTree fx'.st t.book t.roots
        (switchNotices fx'.T fx'.others) = some Bk) ∧
      (∀ b : {i // memMain lo i}, ∃ xo, (First.K2.skelOf fx').oracles[no b.1]? = some xo ∧
        xo.shape = (lo.get b.1).1) ∧
      (∃ xoF, (First.K2.skelOf fx').oracles[s'.live.frame.rows.fresh]? = some xoF ∧
        xoF.shape.maskRows = 2 ^ (stageOf gs 219).h) ∧
      keptCount s'.live.frame.rows.layout
        (fun w => ((First.K2.skelOf fx').oracles.getD
          (s'.live.frame.rows.layout.members.getD w 0) default).shape.mainRows)
        (List.range s'.live.frame.rows.layout.members.size) = s'.live.frame.rows.keptRows := by
  obtain ⟨Gr, hG⟩ := closeFrame_group hcf
  have HS := H Gr hG
  obtain ⟨z1, z2, z3, z4, o, ho, ho'⟩ := sizes_at_stage hcf gs 219 hle hGf
  obtain ⟨hLm, -, -⟩ := layout_behind hcf hG HS hLA
  have hsh : ∀ i ∈ membersOf lo, ∃ xo, s'.st.oracles[no i]? = some xo ∧
      xo.shape = (lo.get i).1 := fun i hi => by
    have e := (shape_behind hcf (no i)).trans (HS.shape i hi)
    obtain ⟨xo, x1, x2⟩ := Option.map_eq_some_iff.1 e
    exact ⟨xo, x1, x2⟩
  have hkr : s'.live.frame.rows.keptRows = ((switchKept s'.live.frame.rows).toList.map fun o =>
      ((s'.st.oracles[o]?).map (·.shape.mainRows)).getD 0).sum := by
    obtain ⟨-, Lk, -, Gf, -, -, rows, hc, e⟩ :=
      (closeFrame_iff _ _ _ _ _ (rdBK s').1 (rdBK s').2).1 hcf
    obtain ⟨G, -, C⟩ := closing_carried ((closing_iff _ _ _ _ _ _ _).2 hc)
    have er : s'.live.frame.rows = rows := by
      show (rdBK s').1.rows = rows
      rw [e]
    rw [er]
    exact C.keptRows
  have hlt : ∀ w ∈ keptNos s'.live.frame.rows.layout,
      s'.live.frame.rows.layout.members.getD w 0 < s'.st.oracles.size := fun w hw => by
    have hw1 : w < s'.live.frame.rows.layout.members.size :=
      List.mem_range.1 (List.mem_filter.1 hw).1
    have hLm' : s'.live.frame.rows.layout.members = Gr.members := hLm
    have e1 : s'.live.frame.rows.layout.members.toList = (membersOf lo).map no := by
      rw [hLm']
      exact HS.members
    have hw2 : w < ((membersOf lo).map no).length := by
      rw [← e1]
      simpa using hw1
    have e2 : s'.live.frame.rows.layout.members.getD w 0 = ((membersOf lo).map no)[w] := by
      rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, e1, List.getElem?_eq_getElem hw2]
      rfl
    rw [e2, List.getElem_map]
    obtain ⟨xo, x1, -⟩ := hsh _ (List.getElem_mem (by simpa using hw2))
    exact (Array.getElem?_eq_some_iff.1 x1).1
  refine ⟨⟨z1, z2, z3, z4⟩, fun t fx' hd hf => ?_⟩
  obtain ⟨f1, f2⟩ := front_shapes_door (hH t hd) hd hf lo no (stageOf gs 219).h
    s'.live.frame.rows.fresh (fun b => hsh b.1 (mem_members.2 b.2)) ⟨o, ho, ho'⟩
  exact ⟨hBook t fx' hd hf, f1, f2, keptCount_door (hH t hd) hd hf hkr hlt⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.closeFrame_group
#print axioms VerifiableInference.Desc.LinkJoin.shape_behind
#print axioms VerifiableInference.Desc.LinkJoin.behind_of_close
