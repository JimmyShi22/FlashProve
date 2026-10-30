-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodySorts.lean: bodyAll's ROUNDS PASS roundsFit AT THE CUTS OF THE PROXIMITY
TEST's FRAME (Johnson/Desc/K12/Frame.lean). Two facts ride beside the invariant of the induction
over the stages: FitFrom D l o (BodyFit.lean: the draws fit) and SortsFrom l cur rest (here; public:
the declared rounds still to be dealt ask items of just the sorts that bodyAll shows: bodyItems,
LinkItems.lean). From the two: the premise roundsFit of the laws on a fold, a switch and the base
case, at sRF | sRS | lastOut. Definition, statements, proofs.

  SortsFrom, SortsFrom.drop     the clause, and its ride over a stage
  FitFrom.take                  the draws fit the first m declared rounds too
  roundsFit_sorts               rounds that drew D (o + n) and show the declared sorts fit
  fitF_at, fitS_at, fitB_at     at the fold's cut · at the switch's cut · at the last stage

Not shown here. That a plan's rounds are such (at the full size: a closed fact). Nothing on a
decision, on soundness or on what any value that is sent discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkItems
import Johnson.Prover.Link.BodyFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)

/-- A declared round's items, the roots apart. -/
def asked (d : Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle) : List Fmt.Item :=
  d.1.items.filter (· != .root)

/-- **The declared rounds still to be dealt ask just the sorts that bodyAll shows.** -/
def SortsFrom (l : Laid) (cur : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) : Prop :=
  l.map asked = bodyItems cur rest

theorem kk_eq {cur : Fmt.M1.Stage} (h : cur.h ≤ cur.k) : (sgOf cur).h + (sgOf cur).g = cur.k :=
  Nat.add_sub_cancel' h

theorem SortsFrom.drop {l : Laid} {cur next : Fmt.M1.Stage} {rest : List Fmt.M1.Stage}
    (h : SortsFrom l cur (next :: rest)) (hk : cur.h ≤ cur.k) :
    SortsFrom (l.drop (cur.k + 3)) next rest := by
  unfold SortsFrom at h ⊢
  rw [List.map_drop, h]
  show (([Fmt.Item.e] :: List.replicate ((sgOf cur).h + (sgOf cur).g) [.e, .e]) ++
    [[], [Fmt.Item.answer]] ++ bodyItems next rest).drop (cur.k + 3) = _
  refine List.drop_left' ?_
  rw [List.length_append, List.length_cons, List.length_replicate, kk_eq hk]
  rfl

theorem FitFrom.take {D : ℕ → Fmt.Drawn} {l : Laid} {o : ℕ} (h : FitFrom D l o) (m : ℕ) :
    FitFrom D (l.take m) o := fun n d hd => by
  rw [List.getElem?_take] at hd
  split at hd
  · exact h n d hd
  · cases hd

theorem roundsFit_sorts {D : ℕ → Fmt.Drawn} (l : Laid) (o : ℕ) (rs : List Fmt.RoundView)
    (hF : FitFrom D l o) (hs : l.map asked = rs.map sortsOf)
    (hd : ∀ (n : ℕ) (r : Fmt.RoundView), rs[n]? = some r → r.drawn = D (o + n)) :
    roundsFit (l.map (·.1)) rs = true := by
  refine roundsFit_of l o rs hF ?_ hd fun n r d h1 h2 => ?_
  · have e := congrArg List.length hs
    rw [List.length_map, List.length_map] at e
    exact e.symm
  · have e := congrArg (·[n]?) hs
    simp only [List.getElem?_map, h1, h2, Option.map_some] at e
    exact (Option.some.inj e).symm

section
variable (p : P12) (K : BCoins) (j : ℕ) (cur next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
  (l : Laid) (o : ℕ) (t : T12) (P : PS) (col : ℕ → List UInt64) (row : GroupRow)
  (D : ℕ → Fmt.Drawn)

theorem fitF_at (hF : FitFrom D l o) (hS : SortsFrom l cur (next :: rest)) (hk : cur.h ≤ cur.k) :
    roundsFit ((l.take (1 + cur.k)).map (·.1)) (sRF K j cur o P row D) = true := by
  refine roundsFit_sorts (l.take (1 + cur.k)) o _ (hF.take _) ?_
    (foldRV_drawn _ _ _ _ fun n => D (o + n))
  unfold SortsFrom at hS
  rw [List.map_take, hS]
  show ((([Fmt.Item.e] :: List.replicate ((sgOf cur).h + (sgOf cur).g) [.e, .e]) ++
    [[], [Fmt.Item.answer]]) ++ bodyItems next rest).take (1 + cur.k) =
      (foldRV _ _ _ _ _).map sortsOf
  rw [foldRV_items, List.append_assoc]
  refine List.take_left' ?_
  rw [List.length_cons, List.length_replicate, kk_eq hk, Nat.add_comm]

theorem fitS_at (hF : FitFrom D l o) (hS : SortsFrom l cur (next :: rest)) (hk : cur.h ≤ cur.k) :
    roundsFit (((l.drop (1 + cur.k)).take 2).map (·.1)) (sRS p K j cur next l o t P row D) =
      true := by
  refine roundsFit_sorts ((l.drop (1 + cur.k)).take 2) (o + (1 + cur.k)) _
    ((hF.drop _).take _) ?_ ?_
  · unfold SortsFrom at hS
    rw [List.map_take, List.map_drop, hS]
    show (((([Fmt.Item.e] :: List.replicate ((sgOf cur).h + (sgOf cur).g) [.e, .e]) ++
      [[], [Fmt.Item.answer]]) ++ bodyItems next rest).drop (1 + cur.k)).take 2 =
        [[], [Fmt.Item.answer]]
    rw [List.append_assoc, List.drop_left' (by
      rw [List.length_cons, List.length_replicate, kk_eq hk, Nat.add_comm])]
    rfl
  · intro n r h
    match n, h with
    | 0, h =>
      cases h
      show D (o + 1 + _) = D (o + (1 + cur.k) + 0)
      rw [kk_eq hk]
      congr 1
      omega
    | 1, h =>
      cases h
      show D (o + 2 + _) = D (o + (1 + cur.k) + 1)
      rw [kk_eq hk]
      congr 1
      omega
    | _ + 2, h => cases h

theorem fitB_at (hF : FitFrom D l o) (hS : SortsFrom l cur []) :
    roundsFit (l.map (·.1)) (lastOut p j cur o t P col row D).rs = true := by
  refine roundsFit_sorts l o _ hF ?_ ?_
  · unfold SortsFrom at hS
    rw [hS]
    show _ = [[Fmt.Item.e], ((shownAll _ _ _ _ _ _ _ _ _ _ _).map Fmt.ItemValue.e).map itemOf]
    rw [items_e, length_shownAll]
    rfl
  · intro n r h
    match n, h with
    | 0, h => cases h; rfl
    | 1, h => cases h; rfl
    | _ + 2, h => cases h

end

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.SortsFrom.drop
#print axioms Johnson.Prover.Link.FitFrom.take
#print axioms Johnson.Prover.Link.roundsFit_sorts
#print axioms Johnson.Prover.Link.fitF_at
#print axioms Johnson.Prover.Link.fitS_at
#print axioms Johnson.Prover.Link.fitB_at
