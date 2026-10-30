-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/AtSide.lean: ON LISTS AND TESTS ALONE: the test on a
sub-protocol's rounds of Law/ExactFresh/Whole.lean (`k4StatedAllB`) accepts, AT EVERY PLAN, all
rounds whose entries are those of the verifier's table of K4's rounds (`entries`,
Johnson/Desc/First/K4/Block.lean) and that have no oracle message; and what the side that `k4Side`
makes (Honest/K4/Part.lean) is. Statements and proofs.

  `k4Side_is`   what the side that is made is; its entries.
  `canon`, `keyOf`         rounds made of a table's rows; what the tests read of a round.
  `statedByB_congr`, `betaMarked_congr`, `statedB_congr`, `statedWalk_congr`   the tests read a
      round's entry and its list of oracle messages alone.
  `statedByB_canon`, `quiet_ok`, `lone_ok`, `masked_Y`, `ms_ok`   one part's rows pass its sort's
      test.
  `canon_append`, `walk_flatten`   part by part.
  `k4Rows`, `k4Rows_flatten`, `k4Rows_ok`   the table cut part by part.
  `sent_level`, `sent_token`, `sent_plain`, `level_ok`, `token_ok`, `plain_ok`   the rows of a
      masked sumcheck of each of the row's three shapes: what they send; they pass the sort's test.
  `k4_stated_table`         **the test accepts the table's own rounds, at every plan.**
  `k4_stated_entries`       **it accepts all rounds with these entries and no oracle message.**
  `k4Side_stated`           so at the side that `k4Side` makes.
  `entries_roots`, `oracles_of_shaped`, `k4Side_stated_shaped`   from the description's own test
      on a sub-protocol's shape.

Limits. No statement here is on a law of coins. THE TEST IS THE LONGER OF THIS FOLDER's TWO:
`k4StatedAllB` goes over all the row's parts. Of the shorter, `k4StatedB betaMarked`
(Law/ExactFresh/Join.lean: the parts but the last two), which `k4_closed_row`
(Law/ExactFresh/Closed.lean) takes as its premise, no statement here speaks, and no statement of
this folder leads from the longer to it. `k4StatedAllB` asks two things of each round: what its
entry says, and that it has no oracle message. THE FIRST IS PAID BY `k4Side`'s OWN TEST ON THE
ENTRIES. THE SECOND IS THE REST OF `k4StatedAllB`, NOT A PREMISE BESIDE IT: `k4Side` does not ask
it; it stands here by name (hno), with «as many lists of oracle messages as rounds» (ho); and both
follow from the description's own test on a sub-protocol's shape (`Block.shaped`,
Johnson/Desc/Block.lean), since the table's entries state no root (`entries_roots`; the step:
`oracles_of_shaped`). That the member of any description has these entries is what `k4Side`'s own
test asks: where a description's member as it is wrapped bears another entry, `k4Side` yields none,
and nothing is said. fo, tokv (`k4Side_is`, `k4Side_stated`, `k4Side_stated_shaped`): any pair at
which `k4Fits` accepts; tied to no run. Of the three tests of `k4Side` the proofs spend the one on
the entries alone: neither `k4Fits` nor the count of rounds in front. `k4Rows` types the verifier's
table once more, cut part by part; `k4Rows_flatten` holds it against the table.

Kin. Short names that stand elsewhere, each read at its line beside ours. NEAR: `entries_roots`
(Johnson/Desc/K14/Law/LedgerBases.lean): the same sentence of another kind's entries; `sent_level`
(Honest/K6/Law/Rounds.lean): how many scalars the rounds of the output head's level send, as a list
written out. ON OTHER MATTERS: `canon_append` (Honest/K6/Law/OutAtRow.lean: a predicate on rounds
shown) and the definition `canon` (`SumLaw.canon`, Honest/SumLaw/Reads.lean: an element's words
reduced); `quiet_ok` (OnBytes/Tie/Pv/Lookup/Forest/FoPlaneClaims.lean,
Johnson/Desc/K13/Law/M4Tries.lean, Johnson/Desc/Sound/SharedJointCountFront.lean,
Johnson/Top/H/FlPort/FoPlaneClaims.lean); `level_ok` (Run/WalkPaths.lean,
OnBytes/Tie/Pv/Lookup/Port/FoLevelRun.lean, Johnson/Road/HeadEndForm.lean,
Johnson/Top/H/FlPort/FoLevelRun.lean); `plain_ok` (Cb/Ld/LdHideProofs.lean,
OnBytes/Slice/KeyPscF.lean, Johnson/Road/K4/Slots/Panels.lean); `sent_plain`
(OnBytes/Maker/Page/SmallOf.lean, Johnson/Desc/Ground/Shape/Marks.lean). BY MATTER, NOT BY NAME.
Beneath this file: `statedBy_nums`, `statedBy_like` and `statedBy_entries` (Honest/SumLaw/Fits.lean)
have `StatedBy`, the proposition of which `statedByB` is the test, from three numbers of each
round's entry and no oracle message: at any list of numbers; at rounds that agree in these numbers
with a call's own entries; at rounds made of these entries. `betaMarked_of_like` and
`betaMarked_entries` (Honest/SumLaw/BetaMarked.lean) have `betaMarked` at rounds that agree with a
call's own entries in the name and the numbers sampled. Of other writers. Here the rounds are those
of K4's table, which this file holds against no call's own entries: of the five none is called
(`firstMarked_of`, of the second file, is). THE LIKE AT THE OUTPUT HEAD's TABLE:
Honest/K6/Law/Segs.lean: `headSegs`, `head_rounds_segs` (that table cut part by part, and held
against the verifier's), `at_Y`, `beta_laySeg`, `headSeg_small`, `headSeg_sums`, `headSeg_beta`
(what each part's rounds state; the mark at "PSC Y"), with `declare_stated` and `head_stated`
(Honest/K6/Law/Rounds.lean): of other writers: propositions part by part, where here it is one test
with code; neither file lies beneath this one. `oracles_of_shaped` goes beside `roots_of_shaped`
(Honest/Small/Field.lean, of other writers), which goes the other way at one round: from no oracle
message to no root; that file lies beneath this one; the statement is not called.
`oracles_of_shaped`'s first clause is, from the same premise, the end of `shaped_len`
(Honest/K12/TreeInFront.lean), and the first clause of `shaped_parts` (Honest/Law/Data.lean); that
law's second clause, which is `shape_of` (Honest/Law/Rule/FileOkOf.lean), has at each round as many
oracle messages as the entry counts roots (as two lists: `lists_of_shaped`,
Honest/Small/FixedSent.lean): the second clause here follows from it where no entry counts a root.
Of other writers; none of these four files lies beneath this one, and none of these statements is
called. `k4Side_is` unfolds `k4Side` and `Side.seated` itself; it calls neither `seated_is`
(Law/ExactFresh/Whole.lean) nor that law's kin, which that file's head tells. Sought: by statement,
to the letter and up to the bound letters, and by short name, among the theorems of the library as
it lay with the writer, and by short name among the definitions under Honest/: by statement no hit;
by short name what is told here. The search by statement does not see a statement that has a binder
in front of the colon where ours has it behind, or the other way round. The kin by matter were found
by a reader, by the names `StatedBy`, `betaMarked` and `Block.shaped`.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.ExactFresh
open OnBytes.Model (ledNS ledNP ledNO)
open OnBytes.Model.Layer (nEndT)
open OnBytes.Desc.First.K4 (Rd masked pointRd batchRd layerRds entryOf)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Oracle Place)
open VerifiableInference.Desc.Part.MaskedSum (Call)
open ProofFile.Honest.SumLaw (betaMarked firstMarked firstMarked_of)

/-! ## The side that is made -/

section
variable {S Cl W₀ Rc Xi Tr X : Type}

/-- **What `k4Side` makes**: the side that `Side.seated` makes of K4's place and row; and its
rounds' entries are the verifier's table's. -/
theorem k4Side_is {bs : List (Block S Cl)} {Q : K4Pub} {cells : Tr → Cells}
    {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : List Fmt.Drawn → OnBytes.Model.Forest.Heard} {fo : OnBytes.Model.Forest.Heard}
    {tokv : Array Nat} {σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (h : k4Side bs Q cells weights tokens look fo tokv = some σ) :
    Side.seated bs (k4Place Q) (k4Sided Q cells weights tokens look) [k4Fall Q] = some σ ∧
      σ.block.rounds.map (·.entry) = OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g := by
  unfold k4Side at h
  split at h
  · rename_i hc
    refine ⟨h, ?_⟩
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc
    have h2 := hc.1.2
    unfold Side.seated at h
    cases hf : bs.find? (fun b => b.place == k4Place Q) with
    | none =>
      rw [hf] at h
      cases h
    | some b =>
      rw [hf] at h h2
      obtain rfl := Option.some.inj h
      exact eq_of_beq h2
  · cases h

end

/-! ## What the tests read of a round -/

/-- Rounds made of a table's rows, without an oracle message. -/
def canon (L : List Rd) : List (Fmt.DeclaredRound × List Oracle) :=
  L.map fun d => ({ entry := entryOf d }, [])

/-- What the tests read of a round: its entry and its list of oracle messages. -/
def keyOf (r : Fmt.DeclaredRound × List Oracle) : Fmt.Entry × List Oracle := (r.1.entry, r.2)

theorem statedByB_congr : ∀ (ns : List Nat) (rs rs' : List (Fmt.DeclaredRound × List Oracle)),
    rs.map keyOf = rs'.map keyOf → statedByB ns rs = statedByB ns rs'
  | [], [], [], _ => rfl
  | [], [], _ :: _, h => by cases h
  | [], _ :: _, [], h => by cases h
  | [], _ :: _, _ :: _, _ => rfl
  | _ :: _, [], [], _ => rfl
  | _ :: _, [], _ :: _, h => by cases h
  | _ :: _, _ :: _, [], h => by cases h
  | n :: ns, r :: rs, r' :: rs', h => by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at h
    have h1 : r.1.entry = r'.1.entry := (congrArg Prod.fst h.1 : (keyOf r).1 = (keyOf r').1)
    have h2 : r.2 = r'.2 := (congrArg Prod.snd h.1 : (keyOf r).2 = (keyOf r').2)
    show (r.1.entry.cut.filter (· != .root) == List.replicate n .e && r.2.isEmpty &&
      statedByB ns rs) = (r'.1.entry.cut.filter (· != .root) == List.replicate n .e &&
      r'.2.isEmpty && statedByB ns rs')
    rw [h1, h2, statedByB_congr ns rs rs' h.2]

theorem betaMarked_congr (k : Call) (rs rs' : List (Fmt.DeclaredRound × List Oracle))
    (h : rs.map keyOf = rs'.map keyOf) : betaMarked k rs = betaMarked k rs' := by
  unfold betaMarked
  cases k.ends with
  | none => rfl
  | some e =>
    have h1 := congrArg (·[k.vs.length + 1]?) h
    simp only [List.getElem?_map] at h1
    show (rs[k.vs.length + 1]?).any (fun r => firstMarked r.1) =
      (rs'[k.vs.length + 1]?).any fun r => firstMarked r.1
    cases hr : rs[k.vs.length + 1]? with
    | none =>
      rw [hr] at h1
      cases hr' : rs'[k.vs.length + 1]? with
      | none => rfl
      | some r' =>
        rw [hr'] at h1
        cases h1
    | some r =>
      rw [hr] at h1
      cases hr' : rs'[k.vs.length + 1]? with
      | none =>
        rw [hr'] at h1
        cases h1
      | some r' =>
        rw [hr'] at h1
        have e1 : r.1.entry = r'.1.entry :=
          (congrArg Prod.fst (Option.some.inj h1) : (keyOf r).1 = (keyOf r').1)
        show firstMarked r.1 = firstMarked r'.1
        unfold firstMarked
        rw [e1]

theorem statedB_congr (x : K4Kind) (rs rs' : List (Fmt.DeclaredRound × List Oracle))
    (h : rs.map keyOf = rs'.map keyOf) : x.statedB betaMarked rs = x.statedB betaMarked rs' := by
  unfold K4Kind.statedB
  rw [statedByB_congr x.sent rs rs' h]
  cases x with
  | quiet => rfl
  | lone n => rfl
  | ms k =>
    show (_ && betaMarked k rs) = (_ && betaMarked k rs')
    rw [betaMarked_congr k rs rs' h]

theorem statedWalk_congr : ∀ (ks : List K4Kind) (rs rs' : List (Fmt.DeclaredRound × List Oracle)),
    rs.map keyOf = rs'.map keyOf → statedWalk betaMarked ks rs = statedWalk betaMarked ks rs'
  | [], _, _, _ => rfl
  | x :: ks, rs, rs', h => by
    show (x.statedB betaMarked (rs.take x.sent.length) &&
      statedWalk betaMarked ks (rs.drop x.sent.length)) =
      (x.statedB betaMarked (rs'.take x.sent.length) &&
        statedWalk betaMarked ks (rs'.drop x.sent.length))
    rw [statedB_congr x (rs.take x.sent.length) (rs'.take x.sent.length)
        (by rw [List.map_take, List.map_take, h]),
      statedWalk_congr ks (rs.drop x.sent.length) (rs'.drop x.sent.length)
        (by rw [List.map_drop, List.map_drop, h])]

/-! ## One part's rows -/

/-- Rounds made of a table's rows state the table's column "sent". -/
theorem statedByB_canon : ∀ L : List Rd, statedByB (L.map (·.sent)) (canon L) = true
  | [] => rfl
  | d :: L => by
    have e : (entryOf d).cut.filter (· != .root) = List.replicate d.sent .e := by
      unfold Fmt.Entry.cut entryOf
      simp
    show ((entryOf d).cut.filter (· != .root) == List.replicate d.sent .e &&
      ([] : List Oracle).isEmpty && statedByB (L.map (·.sent)) (canon L)) = true
    rw [e, statedByB_canon L, beq_self_eq_true]
    rfl

theorem quiet_ok (d : Rd) (h : d.sent = 0) :
    K4Kind.quiet.statedB betaMarked (canon [d]) = true ∧ [d].length = K4Kind.quiet.sent.length := by
  refine ⟨?_, rfl⟩
  have e := statedByB_canon [d]
  rw [List.map_cons, h] at e
  show (statedByB [0] (canon [d]) && true) = true
  rw [Bool.and_true]
  exact e

theorem lone_ok (d : Rd) :
    (K4Kind.lone d.sent).statedB betaMarked (canon [d]) = true ∧
      [d].length = (K4Kind.lone d.sent).sent.length := by
  refine ⟨?_, rfl⟩
  show (statedByB [d.sent] (canon [d]) && true) = true
  rw [Bool.and_true]
  exact statedByB_canon [d]

/-- The row behind a masked sumcheck's variables. -/
theorem masked_Y (nv f y e : Nat) :
    (masked nv f y e)[nv + 1]? = some { name := .pscY, sent := y, notZero := 1 } := by
  unfold masked
  rw [List.append_assoc, List.singleton_append, List.getElem?_cons_succ,
    List.getElem?_append_right (by rw [List.length_replicate]),
    List.length_replicate, Nat.sub_self]
  rfl

theorem ms_ok (k : Call) (nv f y e : Nat) (hs : scalarsOf k = (masked nv f y e).map (·.sent))
    (hv : k.vs.length = nv) (he : k.ends.isSome = true) :
    (K4Kind.ms k).statedB betaMarked (canon (masked nv f y e)) = true ∧
      (masked nv f y e).length = (K4Kind.ms k).sent.length := by
  refine ⟨?_, ?_⟩
  · show (statedByB (scalarsOf k) (canon (masked nv f y e)) &&
      betaMarked k (canon (masked nv f y e))) = true
    rw [hs, statedByB_canon, Bool.true_and]
    unfold betaMarked
    cases hk : k.ends with
    | none => exact absurd he (by rw [hk]; decide)
    | some e0 =>
      show ((canon (masked nv f y e))[k.vs.length + 1]?).any (fun r => firstMarked r.1) = true
      unfold canon
      rw [hv, List.getElem?_map, masked_Y]
      exact firstMarked_of _ rfl rfl rfl
  · show _ = (scalarsOf k).length
    rw [hs, List.length_map]

/-! ## Part by part -/

theorem canon_append (A B : List Rd) : canon (A ++ B) = canon A ++ canon B := List.map_append

theorem walk_flatten : ∀ (ks : List K4Kind) (Ls : List (List Rd)),
    List.Forall₂ (fun x L => x.statedB betaMarked (canon L) = true ∧ L.length = x.sent.length)
      ks Ls → statedWalk betaMarked ks (canon Ls.flatten) = true
  | [], _, _ => rfl
  | x :: ks, L :: Ls, h => by
    cases h with
    | cons h1 h2 =>
      have hl : (canon L).length = x.sent.length := by
        unfold canon
        rw [List.length_map]
        exact h1.2
      show (x.statedB betaMarked ((canon (L :: Ls).flatten).take x.sent.length) &&
        statedWalk betaMarked ks ((canon (L :: Ls).flatten).drop x.sent.length)) = true
      rw [List.flatten_cons, canon_append, List.take_left' hl, List.drop_left' hl, h1.1,
        walk_flatten ks Ls h2]
      rfl
  | _ :: _, [], h => by cases h

/-- **The verifier's table of K4's rounds, cut part by part.** -/
def k4Rows (Q : K4Pub) : List (List Rd) :=
  [[pointRd .zero Q.P.y.h.lt]] ++
  (if Q.g == 0 then [[pointRd .zero (Q.P.y.ls + Q.P.y.h.lt)],
    [pointRd .zero (Q.P.y.lPd - Q.P.y.ls)]] else []) ++
  [[batchRd (ledNS Q.P.y.h.xl * Q.P.y.NI) (ledNS Q.P.y.h.xl)], [pointRd .join Q.P.rd.lNI],
   masked Q.P.rd.muV 1 2 2, [{ name := .line }],
   [batchRd (ledNP Q.P.y.h.xl * Q.P.y.NI) (ledNP Q.P.y.h.xl * Q.P.y.NI)],
   masked Q.P.y.h.lt 2 2 (ledNO Q.P.y.h.xl * Q.P.y.NI), masked Q.P.y.h.lt 2 1 (nEndT Q.P.y),
   [batchRd 0 2],
   masked Q.hp.lamS 1 2 (2 + (1 + Q.P.y.LamM) + (Q.hp.NCL - if Q.g == 0 then 1 else 0)),
   masked Q.P.rd.muH 1 2 2, [{ name := .line }], [pointRd .join (Q.P.y.h.ll - 1)],
   masked Q.P.rd.muH2 1 2 2, [{ name := .line }],
   [batchRd (if Q.g == 0 then 1 else 0) Q.hp.NCL], masked Q.P.wsLay.lk 1 1 1]

theorem k4Rows_flatten (Q : K4Pub) :
    (k4Rows Q).flatten = OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g := by
  unfold k4Rows OnBytes.Desc.First.K4.rounds layerRds
  cases (Q.g == 0) <;> simp

theorem sent_level (mu : Nat) : scalarsOf (k4LevelShape mu) = (masked mu 1 2 2).map (·.sent) := by
  simp [scalarsOf, k4LevelShape, masked, VerifiableInference.Desc.Part.MaskedSum.Var.d]

theorem sent_token (lt dY n : Nat) :
    scalarsOf (k4TokenShape lt dY n) = (masked lt 2 dY n).map (·.sent) := by
  simp [scalarsOf, k4TokenShape, masked, VerifiableInference.Desc.Part.MaskedSum.Var.d]

theorem sent_plain (lam dY n : Nat) :
    scalarsOf (k4PlainShape lam dY n) = (masked lam 1 dY n).map (·.sent) := by
  simp [scalarsOf, k4PlainShape, masked, VerifiableInference.Desc.Part.MaskedSum.Var.d]

theorem level_ok (mu : Nat) :
    (K4Kind.ms (k4LevelShape mu)).statedB betaMarked (canon (masked mu 1 2 2)) = true ∧
      (masked mu 1 2 2).length = (K4Kind.ms (k4LevelShape mu)).sent.length :=
  ms_ok _ _ _ _ _ (sent_level mu) List.length_replicate rfl

theorem token_ok (lt dY n : Nat) :
    (K4Kind.ms (k4TokenShape lt dY n)).statedB betaMarked (canon (masked lt 2 dY n)) = true ∧
      (masked lt 2 dY n).length = (K4Kind.ms (k4TokenShape lt dY n)).sent.length :=
  ms_ok _ _ _ _ _ (sent_token lt dY n) List.length_replicate rfl

theorem plain_ok (lam dY n : Nat) :
    (K4Kind.ms (k4PlainShape lam dY n)).statedB betaMarked (canon (masked lam 1 dY n)) = true ∧
      (masked lam 1 dY n).length = (K4Kind.ms (k4PlainShape lam dY n)).sent.length :=
  ms_ok _ _ _ _ _ (sent_plain lam dY n) List.length_replicate rfl

/-- Each part's rows pass its sort's test. -/
theorem k4Rows_ok (Q : K4Pub) :
    List.Forall₂ (fun x L => x.statedB betaMarked (canon L) = true ∧ L.length = x.sent.length)
      (k4KindsAll Q) (k4Rows Q) := by
  unfold k4KindsAll k4Kinds k4Rows
  by_cases h : (Q.g == 0) = true
  · simp only [h, ↓reduceIte]
    exact .cons (quiet_ok _ rfl) (.cons (quiet_ok _ rfl) (.cons (quiet_ok _ rfl)
      (.cons (lone_ok _) (.cons (quiet_ok _ rfl) (.cons (level_ok _) (.cons (quiet_ok _ rfl)
      (.cons (lone_ok _) (.cons (token_ok _ _ _) (.cons (token_ok _ _ _) (.cons (quiet_ok _ rfl)
      (.cons (plain_ok _ _ _) (.cons (level_ok _) (.cons (quiet_ok _ rfl) (.cons (quiet_ok _ rfl)
      (.cons (level_ok _) (.cons (quiet_ok _ rfl) (.cons (lone_ok _) (.cons (plain_ok _ _ _)
      .nil))))))))))))))))))
  · rw [Bool.not_eq_true] at h
    simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact .cons (quiet_ok _ rfl)
      (.cons (lone_ok _) (.cons (quiet_ok _ rfl) (.cons (level_ok _) (.cons (quiet_ok _ rfl)
      (.cons (lone_ok _) (.cons (token_ok _ _ _) (.cons (token_ok _ _ _) (.cons (quiet_ok _ rfl)
      (.cons (plain_ok _ _ _) (.cons (level_ok _) (.cons (quiet_ok _ rfl) (.cons (quiet_ok _ rfl)
      (.cons (level_ok _) (.cons (quiet_ok _ rfl) (.cons (quiet_ok _ rfl) (.cons (plain_ok _ _ _)
      .nil))))))))))))))))

/-- **The test accepts the table's own rounds, at every plan.** -/
theorem k4_stated_table (Q : K4Pub) :
    k4StatedAllB Q (canon (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g)) = true := by
  rw [← k4Rows_flatten]
  exact walk_flatten _ _ (k4Rows_ok Q)

/-- **It accepts all rounds with the table's entries and no oracle message.** CONDITIONAL on
these two. -/
theorem k4_stated_entries (Q : K4Pub) (rs : List (Fmt.DeclaredRound × List Oracle))
    (he : rs.map (·.1.entry) = OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g)
    (ho : ∀ r ∈ rs, r.2 = []) : k4StatedAllB Q rs = true := by
  have e : rs.map keyOf = (canon (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g)).map keyOf := by
    have e1 : rs.map keyOf = (rs.map (·.1.entry)).map fun x => (x, ([] : List Oracle)) := by
      rw [List.map_map]
      refine List.map_congr_left fun r hr => ?_
      show (r.1.entry, r.2) = (r.1.entry, [])
      rw [ho r hr]
    rw [e1, he]
    unfold OnBytes.Desc.First.K4.entries canon
    rw [List.map_map, List.map_map]
    rfl
  unfold k4StatedAllB
  rw [statedWalk_congr _ _ _ e]
  exact k4_stated_table Q

section
variable {S Cl W₀ Rc Xi Tr X : Type}

/-- **So at the side that `k4Side` makes**, where there are as many lists of oracle messages as
rounds (ho) and each is empty (hno): the rest of the one test. CONDITIONAL on these two. -/
theorem k4Side_stated {bs : List (Block S Cl)} {Q : K4Pub} {cells : Tr → Cells}
    {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : List Fmt.Drawn → OnBytes.Model.Forest.Heard} {fo : OnBytes.Model.Forest.Heard}
    {tokv : Array Nat} {σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (h : k4Side bs Q cells weights tokens look fo tokv = some σ)
    (ho : σ.block.oracles.length = σ.block.rounds.length) (hno : ∀ o ∈ σ.block.oracles, o = []) :
    k4StatedAllB Q (σ.block.rounds.zip σ.block.oracles) = true := by
  refine k4_stated_entries Q _ ?_ fun r hr => hno r.2 (List.of_mem_zip hr).2
  have e : (σ.block.rounds.zip σ.block.oracles).map (·.1) = σ.block.rounds :=
    map_fst_zip_same _ _ ho.symm
  have e2 : (σ.block.rounds.zip σ.block.oracles).map (·.1.entry) =
      ((σ.block.rounds.zip σ.block.oracles).map (·.1)).map (·.entry) := by
    rw [List.map_map]
    rfl
  rw [e2, e]
  exact (k4Side_is h).2

/-- The table's entries state no root. -/
theorem entries_roots (Q : K4Pub) :
    ∀ e ∈ OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g, e.roots = 0 := by
  intro e he
  unfold OnBytes.Desc.First.K4.entries at he
  obtain ⟨d, -, rfl⟩ := List.mem_map.1 he
  rfl

/-- **A sub-protocol that passes the description's test on its shape, and whose entries state no
root, has as many lists of oracle messages as rounds, and each is empty.** -/
theorem oracles_of_shaped (b : Block S Cl) (hs : b.shaped = true)
    (hr : ∀ r ∈ b.rounds, r.entry.roots = 0) :
    b.oracles.length = b.rounds.length ∧ ∀ o ∈ b.oracles, o = [] := by
  unfold Block.shaped at hs
  rw [Bool.and_eq_true, List.all_eq_true] at hs
  have hl : b.oracles.length = b.rounds.length := eq_of_beq hs.1
  refine ⟨hl, fun o ho => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
  have hi' : i < b.rounds.length := hl ▸ hi
  have hm : (b.rounds[i], b.oracles[i]) ∈ b.rounds.zip b.oracles := by
    have e : (b.rounds.zip b.oracles)[i]'(by rw [List.length_zip]; omega) =
        (b.rounds[i], b.oracles[i]) := List.getElem_zip
    rw [← e]
    exact List.getElem_mem _
  have h2 := hs.2 _ hm
  rw [Bool.and_eq_true] at h2
  have h3 : b.oracles[i].length = b.rounds[i].entry.roots := eq_of_beq h2.1
  rw [hr _ (List.getElem_mem hi')] at h3
  exact List.eq_nil_of_length_eq_zero h3

/-- **At the side that `k4Side` makes, under the description's own test on the sub-protocol's
shape.** CONDITIONAL on that test. -/
theorem k4Side_stated_shaped {bs : List (Block S Cl)} {Q : K4Pub} {cells : Tr → Cells}
    {weights : W₀ → Weights} {tokens : Xi → Array Nat}
    {look : List Fmt.Drawn → OnBytes.Model.Forest.Heard} {fo : OnBytes.Model.Forest.Heard}
    {tokv : Array Nat} {σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
    (h : k4Side bs Q cells weights tokens look fo tokv = some σ)
    (hs : σ.block.shaped = true) :
    k4StatedAllB Q (σ.block.rounds.zip σ.block.oracles) = true := by
  have hr : ∀ r ∈ σ.block.rounds, r.entry.roots = 0 := fun r hr =>
    entries_roots Q _ ((k4Side_is h).2 ▸ List.mem_map_of_mem hr)
  obtain ⟨ho, hno⟩ := oracles_of_shaped σ.block hs hr
  exact k4Side_stated h ho hno

end

end ProofFile.Honest.K4.ExactFresh

#print axioms ProofFile.Honest.K4.ExactFresh.k4Side_is
#print axioms ProofFile.Honest.K4.ExactFresh.canon
#print axioms ProofFile.Honest.K4.ExactFresh.keyOf
#print axioms ProofFile.Honest.K4.ExactFresh.statedByB_congr
#print axioms ProofFile.Honest.K4.ExactFresh.betaMarked_congr
#print axioms ProofFile.Honest.K4.ExactFresh.statedB_congr
#print axioms ProofFile.Honest.K4.ExactFresh.statedWalk_congr
#print axioms ProofFile.Honest.K4.ExactFresh.statedByB_canon
#print axioms ProofFile.Honest.K4.ExactFresh.quiet_ok
#print axioms ProofFile.Honest.K4.ExactFresh.lone_ok
#print axioms ProofFile.Honest.K4.ExactFresh.masked_Y
#print axioms ProofFile.Honest.K4.ExactFresh.ms_ok
#print axioms ProofFile.Honest.K4.ExactFresh.canon_append
#print axioms ProofFile.Honest.K4.ExactFresh.walk_flatten
#print axioms ProofFile.Honest.K4.ExactFresh.k4Rows
#print axioms ProofFile.Honest.K4.ExactFresh.k4Rows_flatten
#print axioms ProofFile.Honest.K4.ExactFresh.sent_level
#print axioms ProofFile.Honest.K4.ExactFresh.sent_token
#print axioms ProofFile.Honest.K4.ExactFresh.sent_plain
#print axioms ProofFile.Honest.K4.ExactFresh.level_ok
#print axioms ProofFile.Honest.K4.ExactFresh.token_ok
#print axioms ProofFile.Honest.K4.ExactFresh.plain_ok
#print axioms ProofFile.Honest.K4.ExactFresh.k4Rows_ok
#print axioms ProofFile.Honest.K4.ExactFresh.k4_stated_table
#print axioms ProofFile.Honest.K4.ExactFresh.k4_stated_entries
#print axioms ProofFile.Honest.K4.ExactFresh.k4Side_stated
#print axioms ProofFile.Honest.K4.ExactFresh.entries_roots
#print axioms ProofFile.Honest.K4.ExactFresh.oracles_of_shaped
#print axioms ProofFile.Honest.K4.ExactFresh.k4Side_stated_shaped
