-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/K9.lean: THE ROUNDS THAT KIND K9's LOT DECLARES (ProofFile.k9Ninth,
Johnson/Desc/ProofFile/Lot/K9.lean: the closing as three blocks; the batching at the gatherer), AS A
FUNCTION OF WHAT THE LOT READS OF THE PUBLIC PART: the first state's groups and the stretches of the
declared rounds' ENTRIES. General laws: no written value, nothing evaluated. Definitions with code,
statements and proofs.

Why. That the proof file's description declares the written rounds is to be shown out of the blocks'
own rounds, lot by lot. The lot's first row (Johnson/AtFull/Desc/Lots/K9Row.lean, K9RowAt.lean) says
the like of the blocks' skeletons, which hold how many rounds a block has. Here stands a second
column beside it: a block's place and its rounds. That row's twins on entries are called, not typed
anew.

  PR, prOf   a place with a list of declared rounds; a block's.
  closeRd p P, pr_closeOf   the three blocks that close a segment: the one equation and "shut"
      declare no round; the closing declares K10's entries at P.
  k9RdAtE, k9CloseAt_pr   one segment's three, on entries. Where a number cannot be read the lot
      lays a block that refuses: it declares no round.
  **k9_blocks_pr**   the lot's blocks' places and rounds, in order: no premise. The ground G is an
      idle letter: the lot's blocks do not read it.
  k9_blocks_at   the same under hs · he · hg, each on one thing that the lot reads of Z.
  k9BatchRdE, **k9_batch_pr**   the batching's rounds at a place a, AT EVERY GATHERER g: one round,
      K9's entry at the segment's numbers.
  k9_batch_name   the batching's name does not hang on the gatherer.
  k9BatchAllE, mem_of_lookup, k9_batch_mem   where the lot supplies a batching at a place ON CHAIN
      1, the place and the rounds are a member of one list with a member a segment.

THE LOT's batch READS OF A PLACE ITS KIND, LINK AND PIECE, NOT ITS CHAIN: at a place on another
chain it supplies the same maker. So k9_batch_mem has the premise a.chain = 1.

Limits. Equations of terms: nothing is shown to return or to be a written value. This file imports
the lot's first row, which imports laws on skeletons.
Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K9RowAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Rounds
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.K9 (Where atS)
open ProofFile
open Johnson.AtFull.Desc.Lots

/-- A place with a list of declared rounds. -/
abbrev PR : Type := Place × List Fmt.DeclaredRound

/-- A block's place and rounds. -/
def prOf {T Cl : Type} (b : Block T Cl) : PR := (b.place, b.rounds)

/-! ### the closing's three blocks -/

/-- The places and rounds of the three blocks that close a segment. -/
def closeRd (p : Where) (P : Par) : List PR :=
  [(⟨p.chain, some p.link, p.pieceEq, .K9⟩, []),
   (⟨1, some P.link, P.piece, .K10⟩, (First.Close.entries P).map fun e => { entry := e }),
   (⟨p.chain, some p.link, P.piece + 1, .K9⟩, [])]

theorem pr_closeOf (p : Where) (P : Par) :
    ((K9.closeOf (Cl := Unit) p P).map fun b => prOf (b.retype : Block S ProofFile.Cl)) =
      closeRd p P := rfl

/-- One segment's three, as a function of the groups and the stretches of entries. -/
def k9RdAtE (groups : Array OnBytes.ReqGroup) (xs : XsE) (w : Nat × Option Where) : List PR :=
  match w.2.bind fun p => (k10ParE groups xs p).map fun P => (p, P) with
  | some (p, P) => closeRd p P
  | none => [(⟨1, some w.1, 0, .K10⟩, [])]

theorem k9CloseAt_pr (groups : Array OnBytes.ReqGroup) (xs : XsD) (w : Nat × Option Where) :
    ((k9CloseAt groups xs w).map fun b => prOf (b.retype : Block S ProofFile.Cl)) =
      k9RdAtE groups (xs.map toE) w := by
  unfold k9CloseAt k9RdAtE
  have e : (fun p => (k10ParG groups xs p).map fun P => (p, P)) =
      fun p => (k10ParE groups (xs.map toE) p).map fun P => (p, P) :=
    funext fun p => by rw [k10ParG_eq]
  rw [e]
  cases w.2.bind fun p => (k10ParE groups (xs.map toE) p).map fun P => (p, P) with
  | none => rfl
  | some y =>
    obtain ⟨p, P⟩ := y
    exact pr_closeOf p P

/-- **The lot's blocks' places and rounds, in order.** -/
theorem k9_blocks_pr (Z : Pub) (G : Ground) :
    ((k9Ninth Z).blocks G).map prOf =
      (k9WsE ((k9Stretches Z).map toE)).flatMap
        (k9RdAtE Z.s₀.check.frame.groups ((k9Stretches Z).map toE)) := by
  have e : (k9Ninth Z).blocks G = ((k9Ninth Z).own G).map fun b => b.retype := by
    show ((k9Ninth Z).own G).map (fun b => b.retype) ++ [] = _
    rw [List.append_nil]
  rw [e, k9_own, List.map_map, List.map_flatMap, k9Ws_eq]
  exact congrArg (fun f => (k9WsE ((k9Stretches Z).map toE)).flatMap f)
    (funext fun w => k9CloseAt_pr _ _ w)

/-- The stretches of entries, under two hypotheses by field. -/
theorem k9_stretches_at (Z : Pub) {ps : List Spot} {es : List Fmt.Entry}
    (hs : spotsOf Z.cuts = some ps) (he : Z.D.1.map (·.entry) = es) :
    (k9Stretches Z).map toE = stretchedE ps es 0 := by
  unfold k9Stretches
  rw [hs, ← he]
  exact stretched_entries ps Z.D.1 0

/-- The same under three hypotheses by field. -/
theorem k9_blocks_at (Z : Pub) (G : Ground) {ps : List Spot} {es : List Fmt.Entry}
    {groups : Array OnBytes.ReqGroup} (hs : spotsOf Z.cuts = some ps)
    (he : Z.D.1.map (·.entry) = es) (hg : Z.s₀.check.frame.groups = groups) :
    ((k9Ninth Z).blocks G).map prOf =
      (k9WsE (stretchedE ps es 0)).flatMap (k9RdAtE groups (stretchedE ps es 0)) := by
  rw [k9_blocks_pr, k9_stretches_at Z hs he, hg]

/-! ### the batching -/

/-- The batching's rounds at a place, on entries. -/
def k9BatchRdE (xs : XsE) (a : Place) : Option (List Fmt.DeclaredRound) :=
  match a.kind, a.link with
  | .K9, some l =>
    (((k9WsE xs).lookup l).bind id).bind fun p =>
      if p.piece == a.piece then some [{ entry := K9.entry p }] else none
  | _, _ => none

/-- **The batching's rounds, at every gatherer.** -/
theorem k9_batch_pr (Z : Pub) (G : Ground) (a : Place) (g : Gatherer) :
    ((k9Ninth Z).batch G a).map (fun mk => (mk g).rounds) =
      k9BatchRdE ((k9Stretches Z).map toE) a := by
  rw [k9_batch_is, k9Ws_eq]
  unfold k9BatchRdE
  obtain ⟨c, lk, pc, kd⟩ := a
  cases kd <;> cases lk <;> try rfl
  rename_i l
  show ((((k9WsE ((k9Stretches Z).map toE)).lookup l).bind id).bind fun p =>
      if p.piece == pc then some fun g => K9.batch atS p g else none).map _ =
    (((k9WsE ((k9Stretches Z).map toE)).lookup l).bind id).bind fun p =>
      if p.piece == pc then some ([{ entry := K9.entry p }] : List Fmt.DeclaredRound) else none
  cases ((k9WsE ((k9Stretches Z).map toE)).lookup l).bind id with
  | none => rfl
  | some p =>
    show (if p.piece == pc then some fun g => K9.batch atS p g else none).map _ =
      if p.piece == pc then some ([{ entry := K9.entry p }] : List Fmt.DeclaredRound) else none
    split <;> rfl

/-- The batching's name, at every gatherer. -/
theorem k9_batch_name (Z : Pub) (G : Ground) (a : Place) (mk : Gatherer → Block S ProofFile.Cl)
    (h : (k9Ninth Z).batch G a = some mk) : ∀ g, (mk g).name = "K9: the batching draw" := by
  obtain ⟨p, rfl⟩ := k9_batch_form Z G a mk h
  exact fun _ => rfl

/-- A member a segment: the batching's place on chain 1, and its rounds. -/
def k9BatchAllE (xs : XsE) : List PR :=
  (k9WsE xs).filterMap fun w =>
    w.2.map fun p => (⟨1, some w.1, p.piece, .K9⟩, [{ entry := K9.entry p }])

theorem mem_of_lookup {β : Type} : ∀ (l : List (Nat × β)) (a : Nat) (b : β),
    l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (k, c) :: l, a, b, h => by
    cases e : a == k with
    | true =>
      simp only [List.lookup, e, Option.some.injEq] at h
      have hk : a = k := beq_iff_eq.1 e
      rw [hk, h]
      exact List.mem_cons_self ..
    | false =>
      simp only [List.lookup, e] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup l a b h)

/-- Where a batching is supplied at a place on chain 1: the place and the rounds are in the list. -/
theorem k9_batch_mem (xs : XsE) (a : Place) (r : List Fmt.DeclaredRound)
    (h : k9BatchRdE xs a = some r) (hc : a.chain = 1) : (a, r) ∈ k9BatchAllE xs := by
  obtain ⟨c, lk, pc, kd⟩ := a
  have hc' : c = 1 := hc
  subst hc'
  unfold k9BatchRdE at h
  cases kd <;> cases lk <;> try cases h
  rename_i l
  have h' : ((((k9WsE xs).lookup l).bind id).bind fun p =>
      if p.piece == pc then some [({ entry := K9.entry p } : Fmt.DeclaredRound)] else none) =
        some r := h
  obtain ⟨p, hp, hq⟩ := Option.bind_eq_some_iff.1 h'
  obtain ⟨o, ho, hi⟩ := Option.bind_eq_some_iff.1 hp
  have hi' : o = some p := hi
  subst hi'
  cases e : p.piece == pc with
  | false =>
    rw [e] at hq
    cases hq
  | true =>
    rw [e] at hq
    have hr : [({ entry := K9.entry p } : Fmt.DeclaredRound)] = r := Option.some.inj hq
    have hpc : p.piece = pc := beq_iff_eq.1 e
    subst hr
    subst hpc
    exact List.mem_filterMap.2 ⟨(l, some p), mem_of_lookup _ _ _ ho, rfl⟩

end Johnson.AtFull.Rounds

#print axioms Johnson.AtFull.Rounds.pr_closeOf
#print axioms Johnson.AtFull.Rounds.k9CloseAt_pr
#print axioms Johnson.AtFull.Rounds.k9_blocks_pr
#print axioms Johnson.AtFull.Rounds.k9_stretches_at
#print axioms Johnson.AtFull.Rounds.k9_blocks_at
#print axioms Johnson.AtFull.Rounds.k9_batch_pr
#print axioms Johnson.AtFull.Rounds.k9_batch_name
#print axioms Johnson.AtFull.Rounds.mem_of_lookup
#print axioms Johnson.AtFull.Rounds.k9_batch_mem
