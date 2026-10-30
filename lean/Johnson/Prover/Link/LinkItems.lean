-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkItems.lean: WHICH SORTS OF ITEMS EACH ROUND OF linkAll SHOWS
(Johnson/Prover/Link/LinkAll.lean): a public list, the same at all draws, letters and inputs.
Statements and proofs. It is what the first clause of roundsFit (Johnson/Desc/Block.lean) and the
laying of a message into its declared items (layP, LinkFrame.lean) compare with a plan's declared
rounds.

  bodyItems        a stage: [e] · s.h + s.g times [e, e] · [] · [answer]; the last: [e] · as many e
                   as the two codes' message and tail lengths together
  showRV_items, foldRV_items, bodyAll_items, linkAll_items

Not shown here. That a plan declares these items. Nothing on a decision, on soundness or on what
any value that is sent discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)
open _root_.Desc.K15 (P15 p12Of)
open H2K.JointK (laidOf)

/-- The sorts of the items that a round shows. -/
def sortsOf (r : Fmt.RoundView) : List Fmt.Item := r.vals.map itemOf

def bodyItems : Fmt.M1.Stage → List Fmt.M1.Stage → List (List Fmt.Item)
  | cur, [] => [[.e], List.replicate
      ((sgOf cur).C.l + ((sgOf cur).Z.l + ((sgOf cur).C.r + (sgOf cur).Z.r))) .e]
  | cur, next :: rest =>
    ([.e] :: List.replicate ((sgOf cur).h + (sgOf cur).g) [.e, .e]) ++ [[], [.answer]] ++
      bodyItems next rest

theorem showRV_items : ∀ (k : ℕ) (q : RIdx (sVars GE 2 k) → GE) (D : ℕ → Fmt.Drawn),
    (showRV k q D).map sortsOf = List.replicate k [.e, .e]
  | 0, _, _ => rfl
  | k + 1, q, D => by
    show [Fmt.Item.e, .e] :: (showRV k _ _).map sortsOf = [.e, .e] :: List.replicate k [.e, .e]
    rw [showRV_items k]

theorem foldRV_items (s : Sg) (v μ : s.cIn.J → GE) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (D : ℕ → Fmt.Drawn) :
    (foldRV s v μ W D).map sortsOf = [.e] :: List.replicate (s.h + s.g) [.e, .e] := by
  show [Fmt.Item.e] :: (showRV _ _ _).map sortsOf = _
  rw [showRV_items]

theorem items_e : ∀ l : List Fmt.M1.E,
    (l.map Fmt.ItemValue.e).map itemOf = List.replicate l.length .e
  | [] => rfl
  | _ :: l => congrArg (Fmt.Item.e :: ·) (items_e l)

theorem length_shownAll (C Z : Fmt.M1.Code) (lam : Fmt.M1.E)
    (m0 r0 m1 r1 h0 s0 h1 s1 : ℕ → GE) :
    (shownAll C Z lam m0 r0 m1 r1 h0 s0 h1 s1).length = C.l + (Z.l + (C.r + Z.r)) := by
  unfold shownAll
  rw [List.length_append, List.length_append, List.length_append, length_wr, length_wr, length_wr,
    length_wr]

theorem bodyAll_items (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) :
    ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS)
      (col : ℕ → List UInt64),
      (bodyAll p K rest j cur l o t P col D).rs.map sortsOf = bodyItems cur rest
  | [], j, cur, l, o, t, P, col => by
    show [[Fmt.Item.e], ((shownAll _ _ _ _ _ _ _ _ _ _ _).map Fmt.ItemValue.e).map itemOf] = _
    rw [items_e, length_shownAll]
    rfl
  | next :: rest, j, cur, l, o, t, P, col => by
    show (sRF K j cur o P (rowOf t) D ++ sRS p K j cur next l o t P (rowOf t) D ++
      (bodyAll p K rest _ _ _ _ _ _ _ D).rs).map sortsOf = _
    rw [List.map_append, List.map_append, bodyAll_items p K D rest]
    show (foldRV _ _ _ _ _).map sortsOf ++ [[], [Fmt.Item.answer]] ++ _ = _
    rw [foldRV_items]
    rfl

theorem linkAll_items (P : P15) (S : Sz) (t : ℕ) (X : LIn S) (C : LCoins) (D : ℕ → Fmt.Drawn)
    (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : (p12Of P).nums.stages = first :: rest) :
    (linkAll P S t X C D).rs.map sortsOf =
      [[], [], [.answer, .answer], [], [], []] ++ bodyItems first rest := by
  rw [linkAll_rs P S t X C D first rest hs, List.map_append, List.map_append, bodyAll_items]
  rfl

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.showRV_items
#print axioms Johnson.Prover.Link.foldRV_items
#print axioms Johnson.Prover.Link.items_e
#print axioms Johnson.Prover.Link.length_shownAll
#print axioms Johnson.Prover.Link.bodyAll_items
#print axioms Johnson.Prover.Link.linkAll_items
