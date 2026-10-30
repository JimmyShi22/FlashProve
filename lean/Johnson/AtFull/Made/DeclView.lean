-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/DeclView.lean: WHAT headLast, linksCount AND declareLinks
(OnBytes/Model/StagesLinks.lean) READ OF A LINK, AS A SMALL STRUCTURE (LV), AND:
**EQUAL VIEWS, EQUAL RETURNS.** Definitions, and statements with their proofs.

Why. For the planner's second half (Johnson/AtFull/Made/Ledger.lean: shapesOf_of_parts'
premises a₁ to a₄). A link holds its sub-proof's whole plan, and its check as a closure; the three
routines read fifteen small fields of it. So their returns at the real links can be had from their
returns at small written links, which Lean's kernel evaluates.

  LV · viewL          the view: name · kind · gid · pkMat · pxMat · of each foreign matrix's place
                      the owner and the number among the owner's symbol arrays · of ix: PK TX FT,
                      the first four of U, ZZ BZ · gtTree · of each array of the list: ec · of each
                      array of the planned state: rows and columns. fv · ns · NCL ride: no one of
                      the three routines reads them.
  ofView              a small link with a given view; its check is never applied.
  own_view · declareOwn_view · foreign_view · headLast_view · linksCount_view
                      these return values that hold no link: equal views give THE SAME VALUE.
  declareLinks_view   **its state holds the links themselves: equal views give equal returns under
                      the projection to the arrays' names, link by link, and the declarations.**
  Tools: forIn_alike · forIn_proj · outer · bind_alike · zipIdx_view · zip_view · tree_view ·
  nt_view · at_view.

No twin of any routine is typed: each proof unfolds the routine's own text.
Limits. Nothing is said on whether any of the routines returns. No soundness is claimed.

-/
import OnBytes.Model.VerifyLinks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made.Decl
open OnBytes OnBytes.Model OnBytes.Model.Stages

/-- **What headLast, linksCount and declareLinks read of a link**; fv, ns and NCL ride: no one of
the three reads them. -/
structure LV where
  name : String
  kind : Nat
  gid : Nat
  fv : Bool
  ns : Nat
  NCL : Nat
  pkMat : Array Nat
  pxMat : Array Nat
  /-- of each foreign matrix's place: the owner, the number among the owner's symbol arrays -/
  plFor : Array (Option Nat × Option Nat)
  PK : Array Nat
  TX : Array Nat
  FT : Array Nat
  /-- the first four of U -/
  U4 : List (Option Nat)
  ZZ : Nat
  BZ : Nat
  gtTree : Array Nat
  /-- of each array of the list: ec -/
  nt : Array Nat
  /-- of each array of the planned state: rows, columns -/
  trees : Array (Nat × Nat)
  deriving DecidableEq, Repr

def viewL (X : LinkH) : LV :=
  { name := X.name, kind := X.kind, gid := X.gid, fv := X.fv, ns := X.ns, NCL := X.NCL,
    pkMat := X.tl.pkMat, pxMat := X.tl.pxMat,
    plFor := X.tl.plFor.map fun p => (p.owner, p.rootIndex), PK := X.tl.ix.PK, TX := X.tl.ix.TX,
    FT := X.tl.ix.FT, U4 := X.tl.ix.U.toList.take 4, ZZ := X.tl.ix.ZZ, BZ := X.tl.ix.BZ,
    gtTree := X.tl.gtTree, nt := X.Tp.nt.map (·.ec), trees := X.Fp.trees.map fun t => (t.R, t.K) }

/-- A small link with a given view: the fields that are read, and nothing else. Its check is never
applied. -/
def ofView (v : LV) : LinkH :=
  { name := v.name, kind := v.kind, gid := v.gid, fv := v.fv, ns := v.ns, NCL := v.NCL,
    tl := { pkMat := v.pkMat, pxMat := v.pxMat,
            plFor := v.plFor.map fun p => { owner := p.1, rootIndex := p.2 },
            ix := { U := v.U4.toArray, ZZ := v.ZZ, BZ := v.BZ, TX := v.TX, FT := v.FT, PK := v.PK },
            gtTree := v.gtTree },
    Tp := { nt := v.nt.map fun e => { ec := e } },
    Fp := { trees := v.trees.map fun t => { R := t.1, K := t.2 } },
    run := pure none }

/-! ## Equal views, equal returns -/

theorem tree_view {X X' : LinkH} (h : viewL X = viewL X') (t : Nat) :
    (X.Fp.trees[t]?).map (fun t => (t.R, t.K)) = (X'.Fp.trees[t]?).map fun t => (t.R, t.K) := by
  have e := congrArg LV.trees h
  have e2 := congrArg (·[t]?) e
  simpa [viewL, Array.getElem?_map] using e2

theorem nt_view {X X' : LinkH} (h : viewL X = viewL X') (t : Nat) :
    (X.Tp.nt[t]?).map (·.ec) = (X'.Tp.nt[t]?).map (·.ec) := by
  have e := congrArg LV.nt h
  have e2 := congrArg (·[t]?) e
  simpa [viewL, Array.getElem?_map] using e2

theorem own_view {X X' : LinkH} (h : viewL X = viewL X') : own X = own X' := by
  funext l d tree name
  unfold own
  have h1 := tree_view h tree
  have h2 := nt_view h tree
  cases e1 : X.Fp.trees[tree]? <;> cases e1' : X'.Fp.trees[tree]? <;>
    cases e2 : X.Tp.nt[tree]? <;> cases e2' : X'.Tp.nt[tree]? <;>
    simp_all


/-- A loop over two lists whose members are alike, with bodies that agree at members alike. -/
theorem forIn_alike {α α' γ β ε : Type} (π : α → γ) (π' : α' → γ)
    (f : α → β → Except ε (ForInStep β)) (f' : α' → β → Except ε (ForInStep β))
    (hf : ∀ a a', π a = π' a' → f a = f' a') :
    ∀ (l : List α) (l' : List α'), l.map π = l'.map π' → ∀ b, forIn l b f = forIn l' b f'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | a :: l, a' :: l', h, b => by
    have h1 : π a = π' a' := (List.cons.inj h).1
    have h2 : l.map π = l'.map π' := (List.cons.inj h).2
    rw [List.forIn_cons, List.forIn_cons, hf a a' h1]
    cases f' a' b with
    | error e => rfl
    | ok s =>
      cases s with
      | done b' => rfl
      | yield b' => exact forIn_alike π π' f f' hf l l' h2 b'

theorem declareOwn_view {X X' : LinkH} (h : viewL X = viewL X') : declareOwn X = declareOwn X' := by
  funext l
  have e1 : X.tl.pkMat = X'.tl.pkMat := congrArg LV.pkMat h
  have e2 : X.tl.pxMat = X'.tl.pxMat := congrArg LV.pxMat h
  have e3 : X.tl.ix.PK = X'.tl.ix.PK := congrArg LV.PK h
  have e6 : X.tl.ix.TX = X'.tl.ix.TX := congrArg LV.TX h
  have e7 : X.tl.ix.FT = X'.tl.ix.FT := congrArg LV.FT h
  have e8 : X.tl.ix.U.toList.take 4 = X'.tl.ix.U.toList.take 4 := congrArg LV.U4 h
  have e9 : X.tl.ix.ZZ = X'.tl.ix.ZZ := congrArg LV.ZZ h
  have e10 : X.tl.ix.BZ = X'.tl.ix.BZ := congrArg LV.BZ h
  have e4 : X.tl.plFor.size = X'.tl.plFor.size := by
    have e := congrArg (fun v => v.plFor.size) h
    simpa [viewL] using e
  have e5 : X.Tp.nt.size = X'.Tp.nt.size := by
    have e := congrArg (fun v => v.nt.size) h
    simpa [viewL] using e
  unfold declareOwn
  simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, own_view h]

theorem linksCount_view {L L' : Array LinkH} (h : L.map viewL = L'.map viewL) :
    linksCount L = linksCount L' := by
  have e : L.size = L'.size := by
    have e := congrArg Array.size h
    simpa using e
  unfold linksCount
  rw [e]

theorem at_view {L L' : Array LinkH} (h : L.map viewL = L'.map viewL) (i : Nat) :
    (L[i]?).map viewL = (L'[i]?).map viewL := by
  have e2 := congrArg (·[i]?) h
  simpa [Array.getElem?_map] using e2


theorem foreign_view {L L' : Array LinkH} (hL : L.map viewL = L'.map viewL) {X X' : LinkH}
    (hX : viewL X = viewL X') (N : Nat) (p4 : Bool) (l : Nat)
    (s : Array (Nat × String) × Array FrameLink) (tree : Nat) {pl pl' : PlaceF}
    (ho : pl.owner = pl'.owner) (hr : pl.rootIndex = pl'.rootIndex) :
    foreign L N p4 l X s tree pl = foreign L' N p4 l X' s tree pl' := by
  have hT := tree_view hX tree
  unfold foreign
  rw [ho, hr]
  cases pl'.owner with
  | none => rfl
  | some owner =>
    have hY := at_view hL (layersLink p4 owner)
    dsimp only
    by_cases hc : (decide (owner ≥ N) || decide (layersLink p4 owner ≥ l)) = true
    · simp only [hc, if_true]
      rfl
    · simp only [hc, Bool.false_eq_true, if_false, pure_bind]
      cases eY : L[layersLink p4 owner]? <;> cases eY' : L'[layersLink p4 owner]? <;>
        rewrite [eY, eY'] at hY
      · rfl
      · cases hY
      · cases hY
      · rename_i Y Y'
        have hv : viewL Y = viewL Y' := Option.some.inj hY
        have p1 : Y.tl.pkMat = Y'.tl.pkMat := congrArg LV.pkMat hv
        have p2 : Y.tl.pxMat = Y'.tl.pxMat := congrArg LV.pxMat hv
        have p3 : Y.tl.gtTree = Y'.tl.gtTree := congrArg LV.gtTree hv
        dsimp only
        rw [p1, p2, p3]
        cases pl'.rootIndex with
        | none => rfl
        | some ri =>
          dsimp only
          by_cases hc2 : (decide (ri < Y'.tl.pkMat.size) ||
              decide (ri ≥ Y'.tl.pkMat.size + Y'.tl.pxMat.size)) = true
          · simp only [hc2, if_true]
            rfl
          · simp only [hc2, Bool.false_eq_true, if_false]
            cases Y'.tl.pxMat[ri - Y'.tl.pkMat.size]? with
            | none => rfl
            | some mu =>
              have hTh : ((Y'.tl.gtTree[mu]?).bind fun t => Y.Fp.trees[t]?).map
                  (fun t => (t.R, t.K)) =
                  ((Y'.tl.gtTree[mu]?).bind fun t => Y'.Fp.trees[t]?).map fun t => (t.R, t.K) := by
                cases Y'.tl.gtTree[mu]? with
                | none => rfl
                | some t => exact tree_view hv t
              dsimp only
              cases e1 : X.Fp.trees[tree]? <;> cases e1' : X'.Fp.trees[tree]? <;>
                rewrite [e1, e1'] at hT
              · rfl
              · cases hT
              · cases hT
              · rename_i m m'
                have q := Option.some.inj hT
                have q1 : m.R = m'.R := congrArg Prod.fst q
                have q2 : m.K = m'.K := congrArg Prod.snd q
                dsimp only
                cases e2 : ((Y'.tl.gtTree[mu]?).bind fun t => Y.Fp.trees[t]?) <;>
                  cases e2' : ((Y'.tl.gtTree[mu]?).bind fun t => Y'.Fp.trees[t]?) <;>
                  rewrite [e2, e2'] at hTh
                · rfl
                · cases hTh
                · cases hTh
                · rename_i th th'
                  have r := Option.some.inj hTh
                  have r1 : th.R = th'.R := congrArg Prod.fst r
                  have r2 : th.K = th'.K := congrArg Prod.snd r
                  dsimp only
                  rw [q1, q2, r1, r2]


def stepMap {β δ : Type} (ρ : β → δ) : ForInStep β → ForInStep δ
  | .done b => .done (ρ b)
  | .yield b => .yield (ρ b)

/-- Two loops whose states are alike under a projection stay so. -/
theorem forIn_proj {α α' γ β δ ε : Type} (π : α → γ) (π' : α' → γ) (ρ : β → δ)
    (f : α → β → Except ε (ForInStep β)) (f' : α' → β → Except ε (ForInStep β))
    (hf : ∀ a a' b b', π a = π' a' → ρ b = ρ b' →
      (f a b).map (stepMap ρ) = (f' a' b').map (stepMap ρ)) :
    ∀ (l : List α) (l' : List α'), l.map π = l'.map π' → ∀ b b', ρ b = ρ b' →
      (forIn l b f).map ρ = (forIn l' b' f').map ρ
  | [], [], _, b, b', hb => by
    show Except.map ρ (.ok b) = Except.map ρ (.ok b')
    show Except.ok (ρ b) = Except.ok (ρ b')
    rw [hb]
  | [], _ :: _, h, _, _, _ => by cases h
  | _ :: _, [], h, _, _, _ => by cases h
  | a :: l, a' :: l', h, b, b', hb => by
    have h1 : π a = π' a' := (List.cons.inj h).1
    have h2 : l.map π = l'.map π' := (List.cons.inj h).2
    have k := hf a a' b b' h1 hb
    rw [List.forIn_cons, List.forIn_cons]
    cases e : f a b with
    | error x =>
      cases e' : f' a' b' with
      | error x' =>
        rw [e, e'] at k
        obtain rfl : x = x' := Except.error.inj k
        rfl
      | ok s' =>
        rw [e, e'] at k
        cases k
    | ok s =>
      cases e' : f' a' b' with
      | error x' =>
        rw [e, e'] at k
        cases k
      | ok s' =>
        rw [e, e'] at k
        have k2 : stepMap ρ s = stepMap ρ s' := Except.ok.inj k
        cases s with
        | done c =>
          cases s' with
          | done c' =>
            have k3 : ρ c = ρ c' := ForInStep.done.inj k2
            show Except.ok (ρ c) = Except.ok (ρ c')
            rw [k3]
          | yield c' => cases k2
        | yield c =>
          cases s' with
          | done c' => cases k2
          | yield c' =>
            exact forIn_proj π π' ρ f f' hf l l' h2 c c' (ForInStep.yield.inj k2)

theorem outer {β σ δ ε : Type} {A A' : Except ε β} (k : β → Except ε σ) (P : σ → δ) (ρ : β → δ)
    (hk : ∀ b, (k b).map P = .ok (ρ b)) (h : A.map ρ = A'.map ρ) :
    (A >>= k).map P = (A' >>= k).map P := by
  cases A with
  | error x =>
    cases A' with
    | error x' => exact h
    | ok b' => cases h
  | ok b =>
    cases A' with
    | error x' => cases h
    | ok b' =>
      show (k b).map P = (k b').map P
      rw [hk, hk]
      exact h

theorem bind_alike {β σ δ ε : Type} {A A' : Except ε β} {k k' : β → Except ε σ} {P : σ → δ}
    (hA : A = A') (hk : ∀ b, (k b).map P = (k' b).map P) : (A >>= k).map P = (A' >>= k').map P := by
  subst hA
  cases A with
  | error x => rfl
  | ok b => exact hk b

theorem zipIdx_view {L L' : Array LinkH} (h : L.map viewL = L'.map viewL) :
    L.toList.zipIdx.map (Prod.map viewL id) = L'.toList.zipIdx.map (Prod.map viewL id) := by
  have e : L.toList.map viewL = L'.toList.map viewL := by
    have e := congrArg Array.toList h
    simpa using e
  rw [← List.zipIdx_map, ← List.zipIdx_map, e]

theorem zip_view {X X' : LinkH} (h : viewL X = viewL X') :
    (zipT X.tl.ix.FT.toList X.tl.plFor.toList).map
        (Prod.map id fun p : PlaceF => (p.owner, p.rootIndex)) =
      (zipT X'.tl.ix.FT.toList X'.tl.plFor.toList).map
        (Prod.map id fun p : PlaceF => (p.owner, p.rootIndex)) := by
  have e7 : X.tl.ix.FT = X'.tl.ix.FT := congrArg LV.FT h
  have e : X.tl.plFor.toList.map (fun p : PlaceF => (p.owner, p.rootIndex)) =
      X'.tl.plFor.toList.map fun p : PlaceF => (p.owner, p.rootIndex) := by
    have e := congrArg (fun v => v.plFor.toList) h
    simpa [viewL] using e
  rw [zipT_eq, zipT_eq, ← List.zip_map_right, ← List.zip_map_right, e7, e]

theorem headLast_view {L L' : Array LinkH} (h : L.map viewL = L'.map viewL) :
    headLast L = headLast L' := by
  have es : L.size = L'.size := by
    have e := congrArg Array.size h
    simpa using e
  unfold headLast
  dsimp only
  rw [es]
  congr 1
  refine forIn_alike (Prod.map viewL id) (Prod.map viewL id) _ _ ?_ _ _ (zipIdx_view h) _
  rintro ⟨X, i⟩ ⟨X', i'⟩ hp
  have hv : viewL X = viewL X' := congrArg Prod.fst hp
  obtain rfl : i = i' := congrArg Prod.snd hp
  have k1 : X.kind = X'.kind := congrArg LV.kind hv
  have k2 : X.gid = X'.gid := congrArg LV.gid hv
  funext r
  simp only [k1, k2]

/-- **Equal views, equal returns of declareLinks**, under the projection to the arrays' names and
the declarations. -/
theorem declareLinks_view {L L' : Array LinkH} (h : L.map viewL = L'.map viewL) (N : Nat)
    (p4 : Bool) :
    (declareLinks L N p4).map (fun r => (r.1.map (·.arrayOf), r.2)) =
      (declareLinks L' N p4).map fun r => (r.1.map (·.arrayOf), r.2) := by
  unfold declareLinks
  dsimp only
  refine outer _ _ (fun r : MProd (Array FrameLink) (Array LinkH) => (r.snd.map (·.arrayOf), r.fst))
    (fun b => rfl)
    (forIn_proj (Prod.map viewL id) (Prod.map viewL id) _ _ _ ?_ _ _ (zipIdx_view h) _ _ rfl)
  rintro ⟨X, l⟩ ⟨X', l'⟩ ⟨dc, nm⟩ ⟨dc', nm'⟩ hp hr
  have hv : viewL X = viewL X' := congrArg Prod.fst hp
  obtain rfl : l = l' := congrArg Prod.snd hp
  have hn : nm.map (·.arrayOf) = nm'.map (·.arrayOf) := congrArg Prod.fst hr
  obtain rfl : dc = dc' := congrArg Prod.snd hr
  have hname : X.name = X'.name := congrArg LV.name hv
  dsimp only
  rw [declareOwn_view hv]
  refine bind_alike rfl fun d => ?_
  dsimp only
  refine bind_alike (forIn_alike (Prod.map id fun p : PlaceF => (p.owner, p.rootIndex))
    (Prod.map id fun p : PlaceF => (p.owner, p.rootIndex)) _ _ ?_ _ _ (zip_view hv) _) fun s => ?_
  · rintro ⟨t, pl⟩ ⟨t', pl'⟩ hq
    obtain rfl : t = t' := congrArg Prod.fst hq
    have ho : pl.owner = pl'.owner := congrArg (fun z => z.2.1) hq
    have hri : pl.rootIndex = pl'.rootIndex := congrArg (fun z => z.2.2) hq
    funext r
    dsimp only
    rw [foreign_view h hv N p4 l r t ho hri]
  · by_cases hc : (s.fst.any fun a => a.snd.isEmpty) = true
    · simp only [hc, if_true]
      rfl
    · simp only [bind, Except.bind, hc, Bool.false_eq_true, if_false, pure, Except.pure,
        Except.map, stepMap, Array.map_push, hn, hname]

end Johnson.AtFull.Made.Decl

#print axioms Johnson.AtFull.Made.Decl.tree_view
#print axioms Johnson.AtFull.Made.Decl.nt_view
#print axioms Johnson.AtFull.Made.Decl.own_view
#print axioms Johnson.AtFull.Made.Decl.forIn_alike
#print axioms Johnson.AtFull.Made.Decl.declareOwn_view
#print axioms Johnson.AtFull.Made.Decl.linksCount_view
#print axioms Johnson.AtFull.Made.Decl.at_view
#print axioms Johnson.AtFull.Made.Decl.foreign_view
#print axioms Johnson.AtFull.Made.Decl.forIn_proj
#print axioms Johnson.AtFull.Made.Decl.outer
#print axioms Johnson.AtFull.Made.Decl.bind_alike
#print axioms Johnson.AtFull.Made.Decl.zipIdx_view
#print axioms Johnson.AtFull.Made.Decl.zip_view
#print axioms Johnson.AtFull.Made.Decl.headLast_view
#print axioms Johnson.AtFull.Made.Decl.declareLinks_view
