-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkFrame.lean: from a next-message function to a strategy of the link protocol,
one equation for the view of its run, and the verifier's whole accept from the decision's accept.
General in the protocol's parameters.
What the link is, where these files stand, and the common limits 1 to 4:
Johnson/Prover/Link/LinkYesStm.lean.

The setting. The protocol is (linkSkeletonOfRoundData C ds a xs dec).up (OnBytes/Flat/LinkSib.lean). Its parameters are
the kit C (each round's type of challenges; in this file C is the kit, not the prover's free
parameters), the rounds' data ds, the length 2 ^ a of the two input oracles, the external openings
xs (which of a round's sampled positions are read in which of these two oracles) and the decision
dec. wqW (Johnson/RunOne/StrictLinkW.lean) is the data for its compilation, round by round. The
caller gives next i hist : MsgV. That is round i's message as a view has it: the items, no root
among them, and the columns of the round's trees. hist is the list of the earlier rounds'
challenges, as a view has them. A view (Fmt.View, Fmt/View.lean) is a decision's input: each round's
items and challenge, and the opened columns; no root, no nonce. It is not the library's disclosed
view (DView, Iop/InteractiveOracleProof.lean).

What this file has. stratSL C ds 0 [] next is the strategy of the rounds ds, and stratOf C ds next
is the same strategy behind the protocol's empty first round.
view_run: for all verifier challenges ρ, the view (viewX) of the run of stratSL C ds 0 [] next at ρ
equals viewOf ds a xs next y (drawnSL C ds ρ). It has no premise. viewOf is a function of ds, a, xs,
next, the two input oracles y and the challenges: no kit and no transcript occur in it. drawnSL
gives the challenges as a view has them, without their proof-of-work bits.
AccLaw Q wq x y σ B (Johnson/Prover/Law/Defs.lean) says that the interactive verifier accepts every
transcript τ with three properties. All proof-of-work checks pass at τ's challenges. τ is σ's own
run at these challenges, up to nonces (Puts). τ's challenges lie outside the set B.
accLaw_link has three premises. At all challenges everyOpeningHasItsDraws (Run/PlanQX.lean) holds: every external
opening has as many sampled positions as it counts. At all challenges symbolsCarryTheirPositions
(OnBytes/TypedOracleCompiler/Run/PlanQX.lean) holds: every stored symbol that is read carries its position. At every
ρ that passes all proof-of-work checks, dec accepts viewOf. Then AccLaw holds of stratOf C ds next
with B empty.
linkRec is the value of the library's structure Honest (Iop/InteractiveOracleProof.lean) whose strategy is stratOf at
next w x c. The type of its coins and next are parameters, and its abort set (withheld) is empty.
linkRec_acc: under accLaw_link's three premises, AccLaw holds of linkRec at every private input w,
instance x and coin c.

How it fits. At the full-size parameter set and at linkNext (Johnson/Prover/Link/LinkAll.lean), the
premise on dec is proved by link_yes (Johnson/Prover/Link/LinkJoinF.lean) where Meant holds. The
premise on everyOpeningHasItsDraws is proved by full_full (Johnson/Goal/Conditions/LinkFitsPaid.lean). The premise on
symbolsCarryTheirPositions follows by carriesX_of where every symbol of the two oracles carries its position.
link_accLaw (Johnson/Prover/Link/LinkAccept.lean) puts these together. On the way to linkFits_at
(Johnson/Goal/Conditions/LinkFitsAt.lean), linkFits_home (Johnson/Goal/Conditions/LinkFitsHome.lean)
uses linkRec_acc_with, linkRec_wh and linkRec_pr for HonFit's fields accL, whL and prL.

Other names (namespace Johnson.Prover.Link): each has a docstring below. To note:
  layP, orcT   are total: where an item or a column does not fit, typed zeros are sent.
  msgS   sends the nonce 0 and searches for none.
  colOf_at   colOf finds a column at every position of the prover's own trees that can be queried.
      viewX's list is a filterMap, which would drop a missing one in silence.

Lemmas used: ok_grOf, old_put (Johnson/LPFFrame/Proofs.lean); GPlain.old_mk (Iop/GrindProofs.lean);
listOf_mem (Fmt/Rules6Laws.lean); pr_empty (Prob/Count.lean).

Limits. 1. That the decision accepts any view is not proved here. It is accLaw_link's premise, and
this file proves it at no parameters (at the full-size parameter set, at linkNext, where Meant
holds: link_yes, LinkJoinF.lean; Meant at homeR b Z: meant_home,
Johnson/Goal/Conditions/LinkMeant.lean). So accLaw_link and the theorems on linkRec's acceptance are
implications. At the full-size parameter set and at linkNext the files named under "How it fits"
prove their premises, each under its own conditions.
2. AccLaw speaks only of the challenges that pass all proof-of-work checks (common limit 2), and the
library's own completeness Honest.Acc (Iop/InteractiveOracleProof.lean) is not claimed of linkRec. The reason, and
what is proved instead, are in linkRec's docstring.
3. everyOpeningHasItsDraws stays a premise here: it is a fact on how many positions the kit's challenges yield (at the
full-size parameter set: full_full).
4. The statements are about a protocol with general parameters. That the link of the protocol
structure HolographicProtocol is this protocol at some parameters, and so the clauses of HonFit
(Johnson/Prover/All/OfHonest.lean) on the link, are not said here (at homeR b Z: linkFits_at, under
its own conditions).
Nothing on what a coin holds or on how next reads it. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LPFFrame.Proofs
import Johnson.RunOne.StrictLinkW
import Johnson.Prover.Law.Defs
import Johnson.Desc.Block
import OnBytes.Flat.LinkSib
import Fmt.Rules6Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes TypedOracleCompiler.Iop
open OnBytes.Flat (linkSkeletonOfRoundData linkProtocolOfRoundData)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (CK PlainOf View RV XO SgX storedKey xPos everyOpeningHasItsDraws Dn)
open TypedOracleCompiler.Run.PQ (RD roundS SL SOf uL drawnSL passSL rhoSL rvSL colAtS PosT SymT colT posAtT
  wireS wire0S wiresSL wantedX wantedXL xWanted viewX symbolsCarryTheirPositions treeSh)
open OnBytes.Prover (AccLaw Puts)
open VerifiableInference.Desc (itemOf)
open Johnson.RunOne.StrictW (wqW)

/-! ## 1 A message at the level of a view -/

/-- **A round's message as a view has it**: the items that a view reads (no root among them), and
the columns of the round's trees, by the tree's number in the round and the position. -/
structure MsgV where
  vals : List Fmt.ItemValue
  col : ℕ → ℕ → List UInt64

/-- The plain part with these items. It is total: a root takes nothing; where the list's head is not
of the item's sort the item is 0. -/
def layP : (l : List Fmt.Item) → List Fmt.ItemValue → PlainOf l
  | [], _ => ()
  | .root :: l, g => layP l g
  | .f :: l, g =>
    (((match g.head? with | some (.f x) => x | _ => 0), layP l g.tail) : UInt64 × PlainOf l)
  | .word :: l, g =>
    (((match g.head? with | some (.word x) => x | _ => 0), layP l g.tail) : UInt64 × PlainOf l)
  | .e :: l, g =>
    (((match g.head? with | some (.e x) => x | _ => (0, 0, 0)), layP l g.tail) :
      Fmt.Ext × PlainOf l)
  | .answer :: l, g =>
    (((match g.head? with | some (.answer x) => x | _ => (0, 0, 0)), layP l g.tail) :
      Fmt.Ext × PlainOf l)

/-- Items that fit are read back. -/
theorem gots_layP (l : List Fmt.Item) : ∀ g : List Fmt.ItemValue,
    g.map itemOf = l.filter (· != .root) → PlainOf.gots l (layP l g) = g := by
  induction l with
  | nil =>
    intro g h
    cases g with
    | nil => rfl
    | cons a g => cases h
  | cons it l ih =>
    intro g h
    cases it
    case root => exact ih g h
    all_goals
      cases g with
      | nil => cases h
      | cons a g =>
        have h1 := (List.cons.inj h).1
        have h2 := (List.cons.inj h).2
        cases a <;> first | exact congrArg (List.cons _) (ih g h2) | cases h1

/-- The oracle with these columns. It is total: a column is cut, or filled with 0, to its tree's
width. -/
def orcT : (ts : List Fmt.Shape) → (ℕ → ℕ → List UInt64) → (p : PosT ts) → SymT ts p
  | _ :: _, f, .inl x => fun k => (f 0 x.val).getD k.val 0
  | _ :: ts, f, .inr p => orcT ts (fun n => f (n + 1)) p

/-- A column of its tree's width is read back. -/
theorem colT_orcT : ∀ (ts : List Fmt.Shape) (f : ℕ → ℕ → List UInt64) (n x : ℕ) (p : PosT ts)
    (s : Fmt.Shape), posAtT ts n x = some p → ts[n]? = some s → (f n x).length = s.W →
    colT ts p (orcT ts f p) = f n x
  | [], _, _, _, _, _, hp, _, _ => by cases hp
  | s :: ts, f, 0, x, p, s', hp, hs, hl => by
      unfold posAtT at hp
      split at hp
      · cases hp
        cases hs
        show List.ofFn (fun k : Fin s.W => (f 0 x).getD k.val 0) = f 0 x
        refine List.ext_getElem (by rw [List.length_ofFn, hl]) fun k h1 h2 => ?_
        rw [List.getElem_ofFn]
        exact List.getD_eq_getElem _ _ h2
      · cases hp
  | s :: ts, f, n + 1, x, p, s', hp, hs, hl => by
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hp
      exact colT_orcT ts (fun n => f (n + 1)) n x q s' hq hs hl

/-- A position below the tree's length is there. -/
theorem posAtT_some : ∀ (ts : List Fmt.Shape) (k x : ℕ) (s : Fmt.Shape), ts[k]? = some s →
    x < 2 ^ s.a → ∃ p, posAtT ts k x = some p
  | [], _, _, _, h, _ => by simp at h
  | s0 :: ts, 0, x, s, h, hx => by
      have e : s0 = s := by simpa using h
      subst e
      exact ⟨.inl ⟨x, hx⟩, by unfold posAtT; rw [dif_pos hx]⟩
  | s0 :: ts, k + 1, x, s, h, hx => by
      obtain ⟨p, hp⟩ := posAtT_some ts k x s (by simpa using h) hx
      refine ⟨.inr p, ?_⟩
      show (posAtT ts k x).map Sum.inr = _
      rw [hp]
      rfl

/-! ## 2 The function to a strategy -/

section
variable (C : CK)

/-- One round's message; the nonce 0. -/
def msgS (d : RD) (v : MsgV) : (roundS C d).up.Msg :=
  (orcT d.trees v.col, GPlain.mk d.entry.work (layP d.items v.vals) 0)

/-- **The strategy of the rounds ds.** next i hist: the message of round i, where hist is the list
of the earlier rounds' challenges, as a view has them. -/
def stratSL : (ds : List RD) → ℕ → List Fmt.Drawn → (ℕ → List Fmt.Drawn → MsgV) →
    Strat (uL C ds) Unit
  | [], _, _, _ => ()
  | d :: ds, i, hist, next =>
    (msgS C d (next i hist), fun c =>
      stratSL ds (i + 1) (hist ++ [C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)]) next)

/-- **The same strategy behind the protocol's empty first round.** -/
def stratOf (ds : List RD) (next : ℕ → List Fmt.Drawn → MsgV) :
    Strat (_root_.Run.Twin.up (SOf C ds)) Unit :=
  (((), ()), fun _ => stratSL C ds 0 [] next)

end

/-- The rounds of the view of the strategy's run: a function of the challenges. -/
def rvOf : (ds : List RD) → ℕ → List Fmt.Drawn → (ℕ → List Fmt.Drawn → MsgV) → List Fmt.Drawn →
    List RV
  | d :: ds, i, hist, next, D :: Ds =>
    ⟨PlainOf.gots d.items (layP d.items (next i hist).vals), D⟩ ::
      rvOf ds (i + 1) (hist ++ [D]) next Ds
  | _, _, _, _, _ => []

/-- The columns of the prover's own trees in the run: a function of the challenges. -/
def colOf : (ds : List RD) → ℕ → List Fmt.Drawn → (ℕ → List Fmt.Drawn → MsgV) → List Fmt.Drawn →
    ℕ → ℕ → Option (List UInt64)
  | d :: ds, i, hist, next, D :: Ds, n, x =>
    if n < d.trees.length then
      (posAtT d.trees n x).map fun p => colT d.trees p (orcT d.trees (next i hist).col p)
    else colOf ds (i + 1) (hist ++ [D]) next Ds (n - d.trees.length) x
  | _, _, _, _, _, _, _ => none

/-- **The view of the strategy's run: a function of ds, a, xs, the messages next, the two input
oracles and the challenges**; no kit and no transcript occur in it. -/
def viewOf (ds : List RD) (a : ℕ) (xs : List XO) (next : ℕ → List Fmt.Drawn → MsgV)
    (y : (twoExternalStrings (2 ^ a) SgX).Str) (Ds : List Fmt.Drawn) : View where
  rounds := rvOf ds 0 [] next Ds
  opened := (wantedX a ds xs Ds).filterMap fun kx =>
    if kx.1 = storedKey false then
      (xPos (2 ^ a) (false, kx.2)).map fun p => (kx.1, kx.2, ((twoExternalStrings (2 ^ a) SgX).rd y p).2)
    else if kx.1 = storedKey true then
      (xPos (2 ^ a) (true, kx.2)).map fun p => (kx.1, kx.2, ((twoExternalStrings (2 ^ a) SgX).rd y p).2)
    else (colOf ds 0 [] next Ds kx.1 kx.2).map fun c => (kx.1, kx.2, c)

/-- The round that sends own tree number n, and the tree's number in that round: the numbering of
treeSh and of colAtS (OnBytes/TypedOracleCompiler/Run/). -/
def seatOf : List RD → ℕ → Option (ℕ × ℕ)
  | [], _ => none
  | d :: ds, n =>
    if n < d.trees.length then some (0, n)
    else (seatOf ds (n - d.trees.length)).map fun p => (p.1 + 1, p.2)

/-- The shape of own tree number n is the shape at its seat. -/
theorem treeSh_seat : ∀ (ds : List RD) (n : ℕ),
    treeSh ds n = (seatOf ds n).bind fun p => (ds[p.1]?).bind fun d => d.trees[p.2]?
  | [], _ => rfl
  | d :: ds, n => by
      unfold treeSh seatOf
      split
      · rfl
      · rw [treeSh_seat ds]
        cases seatOf ds (n - d.trees.length) <;> rfl

section
variable (next : ℕ → List Fmt.Drawn → MsgV)

/-- An index shift for next: one more earlier challenge, one round further. -/
theorem next_shift (i j : ℕ) (hist Ds : List Fmt.Drawn) (D0 : Fmt.Drawn) :
    next (i + 1 + j) (hist ++ [D0] ++ Ds.take j) =
      next (i + (j + 1)) (hist ++ (D0 :: Ds).take (j + 1)) := by
  have e1 : i + 1 + j = i + (j + 1) := by omega
  rw [e1, List.take_succ_cons, List.append_assoc]
  rfl

/-- **Round j of the view's rounds**: what next sends at the earlier challenges, with round j's
challenge. -/
theorem rvOf_at : ∀ (ds : List RD) (i : ℕ) (hist Ds : List Fmt.Drawn) (j : ℕ) (d : RD)
    (D : Fmt.Drawn), ds[j]? = some d → Ds[j]? = some D →
    (rvOf ds i hist next Ds)[j]? =
      some ⟨PlainOf.gots d.items (layP d.items (next (i + j) (hist ++ Ds.take j)).vals), D⟩
  | [], _, _, _, _, _, _, h, _ => by simp at h
  | _ :: _, _, _, [], _, _, _, _, h => by simp at h
  | d0 :: ds, i, hist, D0 :: Ds, 0, d, D, h1, h2 => by
      have e1 : d0 = d := by simpa using h1
      have e2 : D0 = D := by simpa using h2
      subst e1 e2
      rw [List.take_zero, List.append_nil]
      rfl
  | d0 :: ds, i, hist, D0 :: Ds, j + 1, d, D, h1, h2 => by
      have h := rvOf_at ds (i + 1) (hist ++ [D0]) Ds j d D (by simpa using h1) (by simpa using h2)
      rw [next_shift next i j hist Ds D0] at h
      exact h

/-- The same where the items fit: the round has them as they are. -/
theorem rvOf_fits (ds : List RD) (i : ℕ) (hist Ds : List Fmt.Drawn) (j : ℕ) (d : RD)
    (D : Fmt.Drawn) (h1 : ds[j]? = some d) (h2 : Ds[j]? = some D)
    (hf : (next (i + j) (hist ++ Ds.take j)).vals.map itemOf = d.items.filter (· != .root)) :
    (rvOf ds i hist next Ds)[j]? = some ⟨(next (i + j) (hist ++ Ds.take j)).vals, D⟩ := by
  rw [rvOf_at next ds i hist Ds j d D h1 h2, gots_layP d.items _ hf]

/-- **colOf returns the prover's column at every position that can be queried**: at a tree's place
(seatOf), a position below the tree's length, a column of the tree's width. -/
theorem colOf_at : ∀ (ds : List RD) (i : ℕ) (hist Ds : List Fmt.Drawn) (n x j k : ℕ) (d : RD)
    (s : Fmt.Shape), seatOf ds n = some (j, k) → ds[j]? = some d → d.trees[k]? = some s →
    x < 2 ^ s.a → j < Ds.length →
    ((next (i + j) (hist ++ Ds.take j)).col k x).length = s.W →
    colOf ds i hist next Ds n x = some ((next (i + j) (hist ++ Ds.take j)).col k x)
  | [], _, _, _, _, _, _, _, _, _, hs, _, _, _, _, _ => by cases hs
  | _ :: _, _, _, [], _, _, _, _, _, _, _, _, _, _, hj, _ => by simp at hj
  | d0 :: ds, i, hist, D0 :: Ds, n, x, j, k, d, s, hs, hd, ht, hx, hj, hw => by
      unfold seatOf at hs
      unfold colOf
      split at hs
      · rename_i hn
        cases hs
        have e : d0 = d := by simpa using hd
        subst e
        rw [if_pos hn]
        obtain ⟨p, hp⟩ := posAtT_some d0.trees n x s ht hx
        rw [hp]
        rw [List.take_zero, List.append_nil] at hw ⊢
        exact congrArg some (colT_orcT d0.trees _ n x p s hp ht hw)
      · rename_i hn
        obtain ⟨⟨j', k'⟩, hq, he⟩ := Option.map_eq_some_iff.1 hs
        cases he
        rw [if_neg hn]
        rw [← next_shift next i j' hist Ds D0] at hw ⊢
        exact colOf_at ds (i + 1) (hist ++ [D0]) Ds (n - d0.trees.length) x j' k' d s hq
          (by simpa using hd) ht hx (by simpa using hj) hw

end

section
variable (C : CK) (next : ℕ → List Fmt.Drawn → MsgV)

/-- One round read off the run. -/
theorem run_cons (d : RD) (ds : List RD) (i : ℕ) (hist : List Fmt.Drawn)
    (c : (roundS C d).up.Chal) (ρ : Rho (uL C ds)) :
    ((stratSL C (d :: ds) i hist next).run ((c, ρ) : Rho (uL C (d :: ds)))).1 =
      ((msgS C d (next i hist), c, ((stratSL C ds (i + 1)
        (hist ++ [C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)]) next).run ρ).1) :
        Tr (uL C (d :: ds))) := rfl

/-- The run's challenges are the given ones. -/
theorem rho_run : ∀ (ds : List RD) (i : ℕ) (hist : List Fmt.Drawn) (ρ : Rho (uL C ds)),
    rhoSL C ds ((stratSL C ds i hist next).run ρ).1 = ρ
  | [], _, _, () => rfl
  | d :: ds, i, hist, (c, ρ) => by
      show (c, rhoSL C ds ((stratSL C ds (i + 1)
        (hist ++ [C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)]) next).run ρ).1) = (c, ρ)
      rw [rho_run ds _ _ ρ]

/-- The rounds of the run's view are rvOf at the challenges drawnSL C ds ρ. -/
theorem rv_run : ∀ (ds : List RD) (i : ℕ) (hist : List Fmt.Drawn) (ρ : Rho (uL C ds)),
    rvSL C ds ((stratSL C ds i hist next).run ρ).1 = rvOf ds i hist next (drawnSL C ds ρ)
  | [], _, _, () => rfl
  | d :: ds, i, hist, (c, ρ) => by
      show (⟨PlainOf.gots d.items (GPlain.old (b := d.entry.work)
          (GPlain.mk d.entry.work (layP d.items (next i hist).vals) 0)),
          C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩ ::
        rvSL C ds ((stratSL C ds (i + 1)
          (hist ++ [C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)]) next).run ρ).1 :
          List RV) = _
      rw [GPlain.old_mk, rv_run ds _ _ ρ]
      rfl

/-- The columns of the prover's own trees in the run are colOf at the challenges drawnSL C ds ρ. -/
theorem col_run : ∀ (ds : List RD) (i : ℕ) (hist : List Fmt.Drawn) (ρ : Rho (uL C ds)),
    colAtS C ds ((stratSL C ds i hist next).run ρ).1 = colOf ds i hist next (drawnSL C ds ρ)
  | [], _, _, () => rfl
  | d :: ds, i, hist, (c, ρ) => by
      funext n x
      show (if n < d.trees.length then
          (posAtT d.trees n x).map fun p => colT d.trees p (orcT d.trees (next i hist).col p)
        else colAtS C ds ((stratSL C ds (i + 1)
          (hist ++ [C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)]) next).run ρ).1
            (n - d.trees.length) x) = _
      rw [col_run ds _ _ ρ]
      rfl

/-- **The view of the strategy's run at ρ is viewOf at the challenges drawnSL C ds ρ**, for all ρ.
-/
theorem view_run (ds : List RD) (a : ℕ) (xs : List XO) (y : (twoExternalStrings (2 ^ a) SgX).Str)
    (ρ : Rho (uL C ds)) :
    viewX C ds a xs y ((stratSL C ds 0 [] next).run ρ).1 =
      viewOf ds a xs next y (drawnSL C ds ρ) := by
  unfold viewX viewOf
  rw [rho_run, rv_run, col_run]

/-- Two lists of challenges with the same drawnSL give the same rounds and columns of the run
(drawnSL: the challenges as a view has them, without their proof-of-work bits). -/
theorem run_same (ds : List RD) (i : ℕ) (hist : List Fmt.Drawn) (ρ ρ' : Rho (uL C ds))
    (h : drawnSL C ds ρ = drawnSL C ds ρ') :
    rvSL C ds ((stratSL C ds i hist next).run ρ).1 =
        rvSL C ds ((stratSL C ds i hist next).run ρ').1 ∧
      colAtS C ds ((stratSL C ds i hist next).run ρ).1 =
        colAtS C ds ((stratSL C ds i hist next).run ρ').1 := by
  rw [rv_run, rv_run, col_run, col_run, h]
  exact ⟨rfl, rfl⟩

end

/-! ## 3 The compilation data: proof of work and nonces -/

section
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- At a local round the compilation data's check is the proof-of-work check on the challenge, if
the round has one; else true. -/
theorem pass_lo {lam K' : ℕ} {r : Round} {a : RAnn r} (w : WireRB lam K' r a) (hk : a.kind = .lo)
    (c : r.Chal) : w.pass c = w.grJ.elim true fun g => g.ok c := by
  unfold TypedOracleCompiler.Iop.WireRB.pass
  split
  · cases w.grJ <;> rfl
  · rename_i h
    rw [hk] at h
    cases h

/-- One round's compilation data checks the round's proof of work on the challenge (GChal.pass). -/
theorem pass_wireS (d : RD) (c : (roundS C d).up.Chal) :
    (wireS C K chal d).pass c = GChal.pass (b := d.entry.work) c :=
  (pass_lo (wireS C K chal d) rfl c).trans
    (LPFFrame.ok_grOf d.entry.work (C.Ch d.entry d.kind) (PlainOf d.items) c)

/-- **The compilation data's checks are the rounds' own proof-of-work checks (passSL).** -/
theorem pass_wiresSL : ∀ (ds : List RD) (ρ : Rho (uL C ds)),
    RoundsQueryLayout.pass _ _ (wiresSL C K chal ds) ρ = passSL C ds ρ
  | [], _ => rfl
  | d :: ds, (c, ρ) => by
      show ((wireS C K chal d).pass c && RoundsQueryLayout.pass _ _ (wiresSL C K chal ds) ρ) =
        (GChal.pass (b := d.entry.work) c && passSL C ds ρ)
      rw [pass_wiresSL ds ρ, pass_wireS]

/-- **Two transcripts that differ in nonces only (Puts) have the same rounds, challenges and
columns.** So the decision's view (viewX) holds no nonce. The disclosed view (DView, Iop/InteractiveOracleProof.lean)
holds it. -/
theorem shown_SL : ∀ (ds : List RD) (τ τ' : Tr (uL C ds)),
    Puts _ _ (wiresSL C K chal ds) τ τ' →
      rvSL C ds τ' = rvSL C ds τ ∧ rhoSL C ds τ' = rhoSL C ds τ ∧ colAtS C ds τ' = colAtS C ds τ
  | [], _, _, _ => ⟨rfl, rfl, rfl⟩
  | d :: ds, (m, c, τ), (m', c', τ'), ⟨h1, h2, h3, h4⟩ => by
      obtain ⟨i1, i2, i3⟩ := shown_SL ds τ τ' h4
      have ho : GPlain.old (b := d.entry.work) m'.2 = GPlain.old (b := d.entry.work) m.2 := by
        rcases h3 with h | ⟨g, n, -, hg, h⟩ | ⟨g, n, hk, -, -⟩
        · rw [h]
        · rw [h]
          exact LPFFrame.old_put d.entry.work _ _ g hg n m.2
        · cases hk
      refine ⟨?_, ?_, ?_⟩
      · show (⟨PlainOf.gots d.items (GPlain.old (b := d.entry.work) m'.2),
            C.dr d.entry d.kind (GChal.old (b := d.entry.work) c')⟩ :: rvSL C ds τ' : List RV) =
          ⟨PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
            C.dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩ :: rvSL C ds τ
        rw [ho, h2, i1]
      · show (c', rhoSL C ds τ') = (c, rhoSL C ds τ)
        rw [h2, i2]
      · funext n x
        show (if n < d.trees.length then
            (posAtT d.trees n x).map fun p => colT d.trees p (m'.1 p)
          else colAtS C ds τ' (n - d.trees.length) x) =
          (if n < d.trees.length then
            (posAtT d.trees n x).map fun p => colT d.trees p (m.1 p)
          else colAtS C ds τ (n - d.trees.length) x)
        rw [h1, i3]

end

/-! ## 4 The two input oracles -/

/-- Under an input oracle's key only positions below the oracles' length can be queried. -/
theorem wantedXL_stored (a : ℕ) (all : List RD) (xs : List XO) : ∀ (i : ℕ) (ds : List RD)
    (Ds : List Fmt.Drawn), (∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) →
    ∀ kx ∈ wantedXL a all xs i ds Ds, 2 ^ 16 ≤ kx.1 → kx.2 < 2 ^ a
  | _, [], _, _, _, h, _ => by simp [wantedXL] at h
  | _, _ :: _, [], _, _, h, _ => by simp [wantedXL] at h
  | i, d :: ds, D :: Ds, hop, kx, h, hk => by
      unfold wantedXL at h
      rcases List.mem_append.1 h with h | h
      · rcases List.mem_append.1 h with h | h
        · obtain ⟨o, -, h⟩ := List.mem_flatMap.1 h
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
          obtain ⟨z, -, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ _).1 hx)
          exact Nat.mod_lt _ (Nat.two_pow_pos a)
        · obtain ⟨n, hn, h⟩ := List.mem_flatMap.1 h
          have hlt := hop d List.mem_cons_self n hn
          split at h
          · cases h
          · obtain ⟨x, -, rfl⟩ := List.mem_map.1 h
            exact absurd hk (Nat.not_le.2 hlt)
      · exact wantedXL_stored a all xs (i + 1) ds Ds
          (fun d' hd => hop d' (List.mem_cons_of_mem _ hd)) kx h hk

/-- **Every symbol that is read carries its position**, where every symbol of the two input oracles
does and the prover's own trees that are opened have numbers below 2 ^ 16. -/
theorem carriesX_of (ds : List RD) (a : ℕ) (xs : List XO) (Ds : List Fmt.Drawn)
    (y : (twoExternalStrings (2 ^ a) SgX).Str) (hop : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (hy : ∀ (w : Bool) (x : ℕ) (h : x < 2 ^ a),
      ((twoExternalStrings (2 ^ a) SgX).rd y (if w then .inr ⟨x, h⟩ else .inl ⟨x, h⟩)).1 = x) :
    symbolsCarryTheirPositions a ds xs Ds y = true := by
  unfold symbolsCarryTheirPositions
  rw [List.all_eq_true]
  intro wx hwx
  unfold xWanted at hwx
  obtain ⟨kx, hk, he⟩ := List.mem_filterMap.1 hwx
  have hlt : wx.2 < 2 ^ a := by
    split at he
    · rename_i e
      cases he
      exact wantedXL_stored a ds xs 0 ds Ds hop kx hk (by rw [e]; exact Nat.le_add_right _ _)
    · split at he
      · rename_i e
        cases he
        exact wantedXL_stored a ds xs 0 ds Ds hop kx hk (by rw [e]; exact Nat.le_add_right _ _)
      · cases he
  unfold xPos
  rw [dif_pos hlt]
  exact beq_iff_eq.2 (hy wx.1 wx.2 hlt)

/-! ## 5 From the decision's accept to AccLaw -/

/-- AccLaw (Johnson/Prover/Law/Defs.lean) for a set B gives AccLaw for every larger set. -/
theorem accLaw_mono {lam K : ℕ} {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}
    {wq : ProtocolQueryLayout lam K Q} {x : Y} {y : E.Str} {σ : Strat Q.loc.shape Unit}
    {B B' : Set (Rho Q.loc.shape)} (hB : B ⊆ B') (h : AccLaw Q wq x y σ B) :
    AccLaw Q wq x y σ B' :=
  fun τ hp hP hn => h τ hp hP fun hb => hn (hB hb)

section
variable (C : CK) (ds : List RD) (a : ℕ) (xs : List XO) {X : Type} (dec : X → View → Bool)
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- **From the decision's accept at viewOf to AccLaw, with the set B empty.** The three premises:
everyOpeningHasItsDraws and symbolsCarryTheirPositions at all ρ; the decision's accept at every ρ that passes all proof-of-work checks.
-/
theorem accLaw_link (next : ℕ → List Fmt.Drawn → MsgV) (x : X) (y : (twoExternalStrings (2 ^ a) SgX).Str)
    (hfull : ∀ ρ, everyOpeningHasItsDraws xs (drawnSL C ds ρ) = true)
    (hcar : ∀ ρ, symbolsCarryTheirPositions a ds xs (drawnSL C ds ρ) y = true)
    (hdec : ∀ ρ, passSL C ds ρ = true → dec x (viewOf ds a xs next y (drawnSL C ds ρ)) = true) :
    AccLaw (linkSkeletonOfRoundData C ds a xs dec).up (wqW C ds a xs dec K chal) x y (stratOf C ds next) ∅ := by
  rintro ⟨m0, c0, τ⟩ hp hP -
  have hp2 : RoundsQueryLayout.pass _ _ (wiresSL C K chal ds) (Tr.rho τ) = true :=
    (Bool.and_eq_true_iff.1 hp).2
  have hP2 : Puts _ _ (wiresSL C K chal ds) ((stratSL C ds 0 [] next).run (Tr.rho τ)).1 τ :=
    hP.2.2.2
  obtain ⟨e1, e2, e3⟩ := shown_SL C K chal ds _ τ hP2
  have hρ : rhoSL C ds τ = Tr.rho τ := e2.trans (rho_run C next ds 0 [] _)
  have hv : viewX C ds a xs y τ = viewOf ds a xs next y (drawnSL C ds (Tr.rho τ)) := by
    rw [← view_run C next ds a xs y (Tr.rho τ)]
    unfold viewX
    rw [e1, e2, e3]
  have hq : passSL C ds (Tr.rho τ) = true := (pass_wiresSL C K chal ds _).symm.trans hp2
  show (passSL C ds (rhoSL C ds τ) && everyOpeningHasItsDraws xs (drawnSL C ds (rhoSL C ds τ)) &&
    symbolsCarryTheirPositions a ds xs (drawnSL C ds (rhoSL C ds τ)) y && dec x (viewX C ds a xs y τ)) = true
  rw [hv, hρ, hq, hfull, hcar, hdec _ hq]
  rfl

/-- **The value of the structure Honest at next.** The type of its coins and the messages are
parameters; the abort set (withheld) is empty. The library's own completeness Honest.Acc
(Iop/InteractiveOracleProof.lean) is not claimed of this structure: its abort set is empty, and the accept's first
condition (passSL) reads the challenges alone: at a ρ whose proof-of-work bits do not all pass it
rejects, whatever is sent (by inspection, not proved). The strategy sends the nonce 0 (msgS) and
searches for none: the search is the compiled prover's. What is proved is the conditional form:
accLaw_link, linkRec_acc: at the challenges that pass all proof-of-work checks. -/
def linkRec {Wt Kc : Type} [Fintype Kc] [Nonempty Kc] (ext : Wt → (twoExternalStrings (2 ^ a) SgX).Str)
    (next : Wt → X → Kc → ℕ → List Fmt.Drawn → MsgV) : Honest (linkProtocolOfRoundData C ds a xs dec) Wt where
  Coin := Kc
  ext := ext
  strat := fun w x c => stratOf C ds (next w x c)
  Bad := ∅
  Hid := fun _ _ => ∅

variable {Wt Kc : Type} [Fintype Kc] [Nonempty Kc] (ext : Wt → (twoExternalStrings (2 ^ a) SgX).Str)
  (next : Wt → X → Kc → ℕ → List Fmt.Drawn → MsgV)

/-- linkRec's abort set (withheld) is empty. -/
theorem linkRec_withheld (w : Wt) (x : X) :
    (linkRec C ds a xs dec ext next).withheld w x = ∅ := Set.union_empty _

/-- **AccLaw for linkRec, at every private input, instance and coin**, under accLaw_link's three
premises (hfull, hcar, hdec). AccLaw speaks of the challenges that pass all proof-of-work checks. -/
theorem linkRec_acc (w : Wt) (x : X) (c : Kc)
    (hfull : ∀ ρ, everyOpeningHasItsDraws xs (drawnSL C ds ρ) = true)
    (hcar : ∀ ρ, symbolsCarryTheirPositions a ds xs (drawnSL C ds ρ) (ext w) = true)
    (hdec : ∀ ρ, passSL C ds ρ = true →
      dec x (viewOf ds a xs (next w x c) (ext w) (drawnSL C ds ρ)) = true) :
    AccLaw (linkSkeletonOfRoundData C ds a xs dec).up (wqW C ds a xs dec K chal) x
      ((linkRec C ds a xs dec ext next).ext w) ((linkRec C ds a xs dec ext next).strat w x c)
      ((linkRec C ds a xs dec ext next).withheld w x) := by
  rw [linkRec_withheld]
  exact accLaw_link C ds a xs dec K chal (next w x c) x (ext w) hfull hcar hdec

/-- The same with any further set beside the abort set. -/
theorem linkRec_acc_with (w : Wt) (x : X) (c : Kc)
    (Fl : Set (Rho (linkProtocolOfRoundData C ds a xs dec).shape))
    (hfull : ∀ ρ, everyOpeningHasItsDraws xs (drawnSL C ds ρ) = true)
    (hcar : ∀ ρ, symbolsCarryTheirPositions a ds xs (drawnSL C ds ρ) (ext w) = true)
    (hdec : ∀ ρ, passSL C ds ρ = true →
      dec x (viewOf ds a xs (next w x c) (ext w) (drawnSL C ds ρ)) = true) :
    AccLaw (linkSkeletonOfRoundData C ds a xs dec).up (wqW C ds a xs dec K chal) x
      ((linkRec C ds a xs dec ext next).ext w) ((linkRec C ds a xs dec ext next).strat w x c)
      ((linkRec C ds a xs dec ext next).withheld w x ∪ Fl) :=
  accLaw_mono (Set.empty_subset _)
    (accLaw_link C ds a xs dec K chal (next w x c) x (ext w) hfull hcar hdec)

/-- The abort set with the empty set beside it is empty. -/
theorem linkRec_union (w : Wt) (x : X) :
    (linkRec C ds a xs dec ext next).withheld w x ∪
      (∅ : Set (Rho (linkProtocolOfRoundData C ds a xs dec).shape)) = ∅ := by
  rw [linkRec_withheld, Set.union_empty]

/-- Membership in that union does not depend on ρ: it is empty. Stated in the shape of HonFit's
field whL. -/
theorem linkRec_wh (w : Wt) (x : X) (ρ ρ' : Rho (linkProtocolOfRoundData C ds a xs dec).shape)
    (h : ρ' ∈ (linkRec C ds a xs dec ext next).withheld w x ∪
      (∅ : Set (Rho (linkProtocolOfRoundData C ds a xs dec).shape))) :
    ρ ∈ (linkRec C ds a xs dec ext next).withheld w x ∪
      (∅ : Set (Rho (linkProtocolOfRoundData C ds a xs dec).shape)) := by
  rw [linkRec_union] at h
  exact h.elim

/-- Its measure is 0. Stated in the shape of HonFit's field prL. -/
theorem linkRec_pr (w : Wt) (x : X) :
    prRho ((linkRec C ds a xs dec ext next).withheld w x ∪
      (∅ : Set (Rho (linkProtocolOfRoundData C ds a xs dec).shape))) = 0 := by
  rw [linkRec_union]
  exact Prob.pr_empty _

end

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.gots_layP
#print axioms Johnson.Prover.Link.colT_orcT
#print axioms Johnson.Prover.Link.posAtT_some
#print axioms Johnson.Prover.Link.treeSh_seat
#print axioms Johnson.Prover.Link.next_shift
#print axioms Johnson.Prover.Link.rvOf_at
#print axioms Johnson.Prover.Link.rvOf_fits
#print axioms Johnson.Prover.Link.colOf_at
#print axioms Johnson.Prover.Link.run_cons
#print axioms Johnson.Prover.Link.rho_run
#print axioms Johnson.Prover.Link.rv_run
#print axioms Johnson.Prover.Link.col_run
#print axioms Johnson.Prover.Link.view_run
#print axioms Johnson.Prover.Link.run_same
#print axioms Johnson.Prover.Link.pass_lo
#print axioms Johnson.Prover.Link.pass_wireS
#print axioms Johnson.Prover.Link.pass_wiresSL
#print axioms Johnson.Prover.Link.shown_SL
#print axioms Johnson.Prover.Link.wantedXL_stored
#print axioms Johnson.Prover.Link.carriesX_of
#print axioms Johnson.Prover.Link.accLaw_mono
#print axioms Johnson.Prover.Link.accLaw_link
#print axioms Johnson.Prover.Link.linkRec_withheld
#print axioms Johnson.Prover.Link.linkRec_acc
#print axioms Johnson.Prover.Link.linkRec_acc_with
#print axioms Johnson.Prover.Link.linkRec_union
#print axioms Johnson.Prover.Link.linkRec_wh
#print axioms Johnson.Prover.Link.linkRec_pr
