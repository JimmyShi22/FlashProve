-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/BatchMember.lean: THE BATCHING OF A LINK (K9.batch,
Johnson/Desc/First/Batch/Kind.lean) against the shape of the first chain's state (chainSh,
Johnson/Desc/First/Shape/Chain.lean): one step on the shape, made of the draw (BatchDraw.lean), the
gathering (BatchFold.lean) and the adding (AddShape.lean); and one law at the bare sub-protocol's
decision. General laws; nothing is evaluated.

  `thereB`: a link's context, a ledger and the smallness test's structure are there, and the slots
    in use are told.
  `laidG`, `laid_ok`: the claims' shapes added to the ledger's shape behind the gathering.
  **`addsG k g order`**: the second half on shapes: the segment's part is there · the draw has run ·
    the gathering on shapes returns · the part is there behind it · the adding on shapes returns:
    then the ledger's shape behind the adding is laid.
  **`batchG rows k g order`**: THE STEP: drawG, then addsG.
  `adds_follows`: addsG returns u at chainSh s and the runs' premises hold along the gathering: then
    the second half's decision accepts, to a state of shape u.
  **`batch_follows`**: batchG returns u at chainSh s · the round has drawn just one element · the
    ledger is empty (K9.ledger-empty: THE BATCHING's OWN ONE TEST ON VALUES) · the runs' premises
    hold along the gathering from the state behind the draw: then the batching's decision accepts,
    to a state of shape u.

Limits. IT IS WORTH WHAT THE RunLaws ARE WORTH (ClaimShape.lean's limits): the step's g is theirs,
and so are the premises PreAll. ONE WAY: from the shapes to the decision: "carries" from a bare
accept is not stated (the runs' own "carries" stand under their premises). adds_follows is stated at
the empty lists of rounds and of columns alone. Where the part is missing addsG refuses under
another name than the block. The bare sub-protocol. That batchG returns at a shape that the chain
reaches is not shown. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Batch.Shape.BatchDraw
import Johnson.Desc.First.Batch.Shape.BatchFold
import Johnson.Desc.First.Batch.Shape.AddShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape

/-- The segment's part can be read, on the shape. -/
def thereB (a : ChainSh) : Bool :=
  a.link.isSome && a.led.isSome && a.tl.isSome && (usedSh a).isSome

theorem there_sh (s : S) : thereB (chainSh s) = true ↔ ∃ P, atS.get? s = some P := by
  unfold thereB
  rw [← usedOf_sh]
  have e1 : (chainSh s).link = s.link?.map linkSh := rfl
  have e2 : (chainSh s).led = s.fork?.map ledSh := rfl
  have e3 : (chainSh s).tl = s.tl?.map tailSh := rfl
  rw [e1, e2, e3]
  have hg : atS.get? s = (do
    let L ← s.link?
    let F ← s.fork?
    let tl ← s.tl?
    let used ← usedOf s
    pure ({ owed := owedOf s, used := used, laid := laidOf tl, L := L, F := F,
            d := { st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } } :
      Part) : Option Part) := rfl
  rw [hg]
  cases s.link? with
  | none => exact ⟨(fun h => by simp at h), (fun ⟨_, h⟩ => nomatch h)⟩
  | some L =>
    cases s.fork? with
    | none => exact ⟨(fun h => by simp at h), (fun ⟨_, h⟩ => nomatch h)⟩
    | some F =>
      cases s.tl? with
      | none => exact ⟨(fun h => by simp at h), (fun ⟨_, h⟩ => nomatch h)⟩
      | some tl =>
        cases usedOf s with
        | none => exact ⟨(fun h => by simp at h), (fun ⟨_, h⟩ => nomatch h)⟩
        | some u => exact ⟨fun _ => ⟨_, rfl⟩, fun _ => rfl⟩

/-- The claims' shapes added to the ledger's shape behind the gathering. -/
def laidG (y : List ClaimSh × ChainSh) : Except String ChainSh :=
  if thereB y.2 then
    match y.2.led.bind fun F => addListS F y.1 with
    | some F' => .ok ((y.2.setLed F').setRowsOwed (owedSh y.2))
    | none => .error "the adding: the shape"
  else .error "K9.in-a-segment"

theorem laid_ok {y : List ClaimSh × ChainSh} {u : ChainSh} (h : laidG y = .ok u) :
    thereB y.2 = true ∧ ∃ F F', y.2.led = some F ∧ addListS F y.1 = some F' ∧
      u = (y.2.setLed F').setRowsOwed (owedSh y.2) := by
  unfold laidG at h
  split at h
  · rename_i hb
    cases hl : y.2.led with
    | none => rw [hl] at h; exact nomatch h
    | some F =>
      rw [hl] at h
      cases ha : addListS F y.1 with
      | none =>
        have e : ((some F : Option LedSh).bind fun F => addListS F y.1) = none := ha
        rw [e] at h
        exact nomatch h
      | some F' =>
        have e : ((some F : Option LedSh).bind fun F => addListS F y.1) = some F' := ha
        rw [e] at h
        exact ⟨hb, F, F', rfl, ha, (Except.ok.inj h).symm⟩
  · exact nomatch h

/-- **The second half on shapes.** -/
def addsG (k : SegSort)
    (g : Nat × String → Nat → ChainSh → Except String (List ClaimSh × ChainSh))
    (order : List (Nat × String)) (a : ChainSh) : Except String ChainSh :=
  if thereB a && (a.link.map (·.handed)).getD false then (gatherG k g order a).bind laidG
  else .error "K9.draw-has-run"

/-- **THE STEP ON THE SHAPE.** -/
def batchG (rows : Nat) (k : SegSort)
    (g : Nat × String → Nat → ChainSh → Except String (List ClaimSh × ChainSh))
    (order : List (Nat × String)) (a : ChainSh) : Except String ChainSh :=
  (drawG rows a).bind (addsG k g order)

/-- Laying the part back with a new ledger alone. -/
theorem set_led {s : S} {P : Part} (h : atS.get? s = some P) (F : Fork) :
    chainSh (atS.set s { P with F := F }) =
      ((chainSh s).setLed (ledSh F)).setRowsOwed (owedSh (chainSh s)) := by
  obtain ⟨l1, -, -, -, l5, l6⟩ := part_sh h
  rw [set_sh]
  dsimp only
  rw [setLink_same l1, l5, l6, ← chainSh_core]
  rfl

theorem adds_follows {bs : List (Block S Claim)} {order : List (Nat × String)} (k : SegSort)
    (R : RunsLaw bs order) (p : Where) (piece : Nat) (what : String) (s : S) (u : ChainSh)
    (hg : addsG k (fun o => (R.law o).runG) order (chainSh s) = .ok u)
    (hp : PreAll R order 0 s) :
    ∃ t, (adds (Cl := Claim) atS p piece what (claimsInBy (eachAtS k) bs order)).decide s [] [] =
      .ok t ∧ u = chainSh t := by
  unfold addsG at hg
  split at hg
  · rename_i hb
    rw [Bool.and_eq_true] at hb
    obtain ⟨P₀, hP₀⟩ := (there_sh s).1 hb.1
    have hh : P₀.L.handed = true := by
      have := hb.2
      rw [(part_sh hP₀).1] at this
      exact this
    cases hG : gatherG k (fun o => (R.law o).runG) order (chainSh s) with
    | error e => rw [hG] at hg; exact nomatch hg
    | ok y =>
      rw [hG] at hg
      obtain ⟨cs, s₁, hc, rfl⟩ := gather_follows k R s y hG hp
      have hg' : laidG (cs.map claimSh, chainSh s₁) = .ok u := hg
      obtain ⟨hb₁, F, F', hl, ha, rfl⟩ := laid_ok hg'
      obtain ⟨P₁, hP₁⟩ := (there_sh s₁).1 hb₁
      obtain rfl : ledSh P₁.F = F := Option.some.inj ((part_sh hP₁).2.1.symm.trans hl)
      obtain ⟨G, hGa⟩ := addList_returns cs P₁.F F' ha
      obtain rfl : ledSh G = F' :=
        Option.some.inj ((addList_carries cs P₁.F G hGa).symm.trans ha)
      refine ⟨atS.set s₁ { P₁ with F := G }, ?_, (set_led hP₁ G).symm⟩
      show (atS.part s >>= fun s₀ => need "K9.draw-has-run" s₀.L.handed >>= fun _ =>
        claimsInBy (eachAtS k) bs order s >>= fun x => atS.part x.2 >>= fun q =>
          addList q.F x.1 >>= fun F =>
            (pure (atS.set x.2 { q with F := F }) : Ans S)) = _
      simp only [ans_bind, need_ok, exists_const]
      exact ⟨P₀, (there_ok _ _ _).2 hP₀, hh, (cs, s₁), hc, P₁, (there_ok _ _ _).2 hP₁, G, hGa,
        rfl⟩
  · exact nomatch hg

/-- **WHERE THE STEP ON THE SHAPE RETURNS AND THE NAMED PREMISES HOLD, THE BATCHING ACCEPTS, TO A
STATE OF THAT SHAPE.** -/
theorem batch_follows {bs : List (Block S Claim)} {order : List (Nat × String)} (k : SegSort)
    (R : RunsLaw bs order) (p : Where) (s : S) (r : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (u : ChainSh)
    (hg : batchG p.rows k (fun o => (R.law o).runG) order (chainSh s) = .ok u)
    (x : UInt64 × UInt64 × UInt64) (hr : r.drawn.elems = [x])
    (hv : ∀ F, s.fork? = some F → ledgerEmpty F = true)
    (hp : ∀ s₁, (drawAlone (Cl := Claim) atS p).decide s [r] gs = .ok s₁ → PreAll R order 0 s₁) :
    ∃ t, (batch atS p (claimsInBy (eachAtS k) bs order)).decide s [r] gs = .ok t ∧
      u = chainSh t := by
  have hg' : (drawG p.rows (chainSh s)).bind
    (addsG k (fun o => (R.law o).runG) order) = .ok u := hg
  cases hd : drawG p.rows (chainSh s) with
  | error e => rw [hd] at hg'; exact nomatch hg'
  | ok a₁ =>
    rw [hd] at hg'
    obtain ⟨s₁, hs₁⟩ := draw_returns (Cl := Claim) p s r gs a₁ hd x hr hv
    obtain rfl : chainSh s₁ = a₁ :=
      Except.ok.inj ((draw_carries p s s₁ r gs hs₁).symm.trans hd)
    obtain ⟨t, ht, eu⟩ := adds_follows k R p p.piece "the segment's" s₁ u hg' (hp s₁ hs₁)
    refine ⟨t, ?_, eu⟩
    show ((drawAlone (Cl := Claim) atS p).decide s [r] gs >>= fun t₁ =>
      (adds (Cl := Claim) atS p p.piece "the segment's"
        (claimsInBy (eachAtS k) bs order)).decide t₁ [] []) = _
    rw [hs₁]
    exact ht

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.there_sh
#print axioms VerifiableInference.Desc.K9.Shape.adds_follows
#print axioms VerifiableInference.Desc.K9.Shape.batch_follows
#print axioms VerifiableInference.Desc.K9.Shape.thereB
#print axioms VerifiableInference.Desc.K9.Shape.laidG
#print axioms VerifiableInference.Desc.K9.Shape.laid_ok
#print axioms VerifiableInference.Desc.K9.Shape.addsG
#print axioms VerifiableInference.Desc.K9.Shape.batchG
#print axioms VerifiableInference.Desc.K9.Shape.set_led
