-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/Joint.lean: a second form of Compile/Batch/Joint.lean.

The files under OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`) are a second form of the verifier's side of
the library's compiler and of its road to soundness. They stand beside the library's own files, with
five changes:
  (1) a query holds a list of roots, and a component of a round has a list of trees; the verifier
  takes, and the analysis counts, at most `maxRt` = 2 of them;
  (2) the body of a leaf of a tree over oracles is a type that the interface names (`BatchProtocolWithLeafBody.Bd`); the
  wire has functions that write a symbol into a body and read it back;
  (3) the input of a leaf of the request tree is the slot value and, behind it, a string that comes
  with the proof string (`OneProtocolProof.rsalt`);
  (4) a Fiat-Shamir query of the format (F5) holds no external roots;
  (5) Test and Link have annotations of their own (`BatchProtocolWithLeafBody.annT`, `BatchProtocolWithLeafBody.annL`: which of their rounds are
  shared), and the depth of a request tree goes by the protocol (`QueryLayout.depthReqT`, `depthReqL`,
  `depthReq`; `QueryLayout.dReq`).
The folder has the verifier's side alone: no prover and no completeness. Nothing here is on hiding.
The names are the library's: under `TypedOracleCompiler`, names such as `Iop.QueryLayout` or
`Compile.Batch.verifyB` mean this folder's declarations, not the library's. No theorem of this
folder carries a statement from one form to the other. In the comments, "here:" marks what is other
than in the library's file.

What differs in this file from Compile/Batch/Joint.lean, comments apart: definitions: `shPart`;
proofs alone: `joint_le`. Every other declaration has that file's text.

The rest of this head is the head of Compile/Batch/Joint.lean, to be read with these changes; the
files that it names under Iop/ and Compile/Batch/ are, where this folder has a file of that name,
this folder's.

Compile/Batch/Joint.lean: two bounds behind the event E'_S (`Lane.step`, Compile/Batch/Rooted.lean:
a new, rooted query whose answer turns the state of its slot's transcript, or of the transcript of
one of its live slots, from 0 to 1). Both are under three hypotheses: `RoundsQueryLayout.OKG`; of (Snd-B)
(round-by-round soundness of a protocol with slots: `BatchInteractiveOracleProof.SndB`, Iop/Batch.lean) the law on
verifier messages, `JointLaw`; and `Err.Below ε εs` (every round's error, divided by the number of
challenges, is at most εs). Under these: a uniform Fiat-Shamir answer turns a slot's state from 0 to
1 with probability at most εs (`pr_flip_le`); in a shared round (`Compat`), for all slots jointly
(`joint_le`).

Part 1: `pr_flip_le`, the first line of (Snd-B) (the clause of `JointLaw` for a local round). Part
2: `joint_le`, the second (for a shared round); the partial transcript of the whole batch is not
built as an object.

Notation:
  `pre`: a `Trace` (Rom/OSpec.lean): a query-answer trace, first query first;
  `prjS`, `prjP`: how leaves and fields are read back (`Lane`, Compile/Batch/Rooted.lean);
  `St j`: the state function of slot j on what is left of the protocol (none: the slot is empty)
    (`JointLaw`, Iop/Batch.lean);
  `Item`, `Rec` (Compile/Batch/Rooted.lean): what the prover message of one round of a slot's
    transcript is read from; an item with the answer that gives the verifier message of its round;
  `D j`: the records of slot j and its current item; `n`: a natural number; in `Compat D n`, the
    number of records of each live slot (D j = some d);
  `trOf pre t s A ws prjS prjP l cur` (Compile/Batch/Rooted.lean): the slot's transcript with the
    records l and the current item cur: it ends with the prover message that cur gives.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Rooted

noncomputable section

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol
open scoped ENNReal

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## Part 1. One local transcript -/

/-- For `RoundsQueryLayout.OKG`: a uniform answer gives a uniform challenge. -/
theorem pr_chalAt {s : Shape} {A : RoundSplits s} {ws : RoundsQueryLayout lam K s A} (hws : RoundsQueryLayout.OKG s A ws)
    (τ : AtV s) (P : τ.round.Chal → Prop) :
    pr (unif (FsAns lam K)) {a | P (chalAt ws τ a.1)} = pr (unif τ.round.Chal) {c | P c} := by
  have h1 : pr (unif (FsAns lam K)) {a | P (chalAt ws τ a.1)}
      = pr (((unif (FsAns lam K)).map Prod.fst).map (chalAt ws τ)) {c | P c} := by
    rw [pr_map, pr_map]; rfl
  rw [h1, map_fst_unif, chalAt_unif hws τ]

/-- Under `RoundsQueryLayout.OKG`, `Err.Below ε εs` and `JointLaw`: in state 0 the state of a non-empty slot
(hS) becomes 1 with probability at most εs. -/
theorem pr_flip_le {N : ℕ} {s : Shape} {A : RoundSplits s} {ws : RoundsQueryLayout lam K s A}
    (hws : RoundsQueryLayout.OKG s A ws) {ε : Err s} {εs : ℝ≥0∞} (hε : Err.Below ε εs)
    {St : Fin N → Option (PTr s → Bool)} (hJ : JointLaw N s A ε St) (j : Fin N) (S : PTr s → Bool)
    (hS : St j = some S) (τ : AtV s) (h0 : S (.atV τ) = false) :
    pr (unif (FsAns lam K)) {a | S (τ.snoc (chalAt ws τ a.1)) = true} ≤ εs := by
  rw [pr_chalAt hws τ fun c => S (τ.snoc c) = true]
  exact (pr_unif_le_of_cnt_le (hJ.at_slot j S hS τ h0)).trans (hε.errPr_le τ)

/-! ## Part 2. A family of local transcripts with the same shared parts -/

/-- what of a record is common to all slots: the fields of the shared component, and in a shared
round the answer -/
def shPart {t : Tag} (rc : Rec lam K L t) :
    Option (List (Dig lam) × PlainPart (shapeOf L t) (annOf L t)) × Option (FsAns lam K) :=
  (rc.1.shd, if rc.1.kind = .sh then some rc.2 else none)

/-- The slots fit together: all live slots have n records; the shared parts of their records and of
their current items are the same; the current round is shared. -/
structure Compat {t : Tag} {N : ℕ}
    (D : Fin N → Option (List (Rec lam K L t) × Item lam L t)) (n : ℕ) : Prop where
  len : ∀ j d, D j = some d → d.1.length = n
  sh : ∀ j j' d d',
    D j = some d → D j' = some d' → d.1.map shPart = d'.1.map shPart ∧ d.2.shd = d'.2.shd
  cur : ∀ j d, D j = some d → d.2.kind = .sh

theorem msgOf_eq_some {t : Tag} {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s}
    {tr : Trace (typedOracleFamily lam K L)} {w : WireRB lam K r a}
    {prj : (p : r.Pos) → Body L → Option (r.Sym p)}
    {prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart (r :: s) (a, A))} {it : Item lam L t}
    {M : r.Msg} (h : msgOf tr w prj prjP it = some M) :
    it.kind = a.kind ∧
    ∃ z0 zJ,
      rd0 prjP it.shd = some z0 ∧
      rdJ prjP it.own = some zJ ∧
      M = a.join (m0Of tr w prj z0) (mJOf tr w prj zJ) := by
  unfold msgOf at h
  split at h
  · rename_i hk
    obtain ⟨z0, h0, h1⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨zJ, hJ, h2⟩ := Option.map_eq_some_iff.1 h1
    exact ⟨hk, z0, zJ, h0, hJ, h2.symm⟩
  · cases h

/-- The joint bound (shared round), under `RoundsQueryLayout.OKG`, `Err.Below ε εs`, `JointLaw`, `Compat`: some
slot's state goes from 0 to 1 with probability at most εs. -/
theorem joint_le {t : Tag} {N : ℕ} (pre : Trace (typedOracleFamily lam K L)) {εs : ℝ≥0∞} :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A ws →
      ∀ (ε : Err s), Err.Below ε εs →
        ∀ (prjS : (p : OPos s) → Body L → Option (OSym s p))
            (prjP : PlainPart (shapeOf L t) (annOf L t) → Option (PlainPart s A))
            (St : Fin N → Option (PTr s → Bool)),
          JointLaw N s A ε St →
          ∀ (n : ℕ) (D : Fin N → Option (List (Rec lam K L t) × Item lam L t)), Compat D n →
            pr (unif (FsAns lam K))
                {a | ∃ j S d τ, St j = some S ∧ D j = some d ∧
                  trOf pre t s A ws prjS prjP d.1 d.2 = some τ ∧
                  S (.atV τ) = false ∧ S (τ.snoc (chalAt ws τ a.1)) = true} ≤ εs
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => by
      refine le_trans (le_of_eq (pr_eq_zero_of_forall_not_mem _ ?_)) (zero_le _)
      rintro a - ⟨j, S, d, τ, -, -, h, -⟩
      cases h
  | r :: s, (a, A), (w, ws), hws, (e, ε), hε, prjS, prjP, St, hJ, n, D, hD => by
      by_cases hlive : ∃ j d, D j = some d
      swap
      · refine le_trans (le_of_eq (pr_eq_zero_of_forall_not_mem _ ?_)) (zero_le _)
        rintro a - ⟨j, S, d, τ, -, h, -⟩
        exact hlive ⟨j, d, h⟩
      obtain ⟨j₀, d₀, h₀⟩ := hlive
      cases n with
      | zero =>
        -- the current round: the joint error
        cases hz : rd0 prjP d₀.2.shd with
        | none =>
          refine le_trans (le_of_eq (pr_eq_zero_of_forall_not_mem _ ?_)) (zero_le _)
          rintro x - ⟨j, S, d, τ, -, hd, hτ, -⟩
          obtain ⟨l, cur⟩ := d
          have hl : l = [] := List.length_eq_zero_iff.1 (hD.len j _ hd)
          subst hl
          obtain ⟨M, hM, -⟩ := Option.map_eq_some_iff.1
            (show (msgOf pre w (fun p => prjS (.inl p)) prjP cur).map Sum.inl = some τ from hτ)
          obtain ⟨-, z0, zJ, h0, -⟩ := msgOf_eq_some hM
          rw [show cur.shd = d₀.2.shd from (hD.sh j j₀ _ _ hd h₀).2, hz] at h0
          cases h0
        | some z0 =>
          by_cases hk : a.kind = .sh
          swap
          · refine le_trans (le_of_eq (pr_eq_zero_of_forall_not_mem _ ?_)) (zero_le _)
            rintro x - ⟨j, S, d, τ, -, hd, hτ, -⟩
            obtain ⟨l, cur⟩ := d
            have hl : l = [] := List.length_eq_zero_iff.1 (hD.len j _ hd)
            subst hl
            obtain ⟨M, hM, -⟩ := Option.map_eq_some_iff.1
              (show (msgOf pre w (fun p => prjS (.inl p)) prjP cur).map Sum.inl = some τ from hτ)
            exact hk ((msgOf_eq_some hM).1.symm.trans (hD.cur j _ hd))
          let m0 : a.M0 := m0Of pre w (fun p => prjS (.inl p)) z0
          let m : Fin N → a.Mj := fun j =>
            mJOf pre w (fun p => prjS (.inl p))
              (((D j).bind fun d => rdJ prjP d.2.own).getD ([], none))
          have h1 := (hJ m0 m).1
          simp only [hk] at h1
          have hsub : {x : FsAns lam K | ∃ j S d τ,
                St j = some S ∧ D j = some d ∧
                trOf pre t (r :: s) (a, A) (w, ws) prjS prjP d.1 d.2 = some τ ∧
                S (.atV τ) = false ∧
                S (τ.snoc (chalAt (s := r :: s) (A := (a, A)) (w, ws) τ x.1)) = true} ⊆
              {x | (fun c : r.Chal =>
                  ∃ j S,
                    St j = some S ∧
                    S (.atV (Sum.inl (a.join m0 (m j)))) = false ∧
                    S (PTr.cons (a.join m0 (m j)) c (PTr.empty s)) = true)
                (w.chal x.1)} := by
            rintro x ⟨j, S, d, τ, hS, hd, hτ, hf, ht⟩
            obtain ⟨l, cur⟩ := d
            have hl : l = [] := List.length_eq_zero_iff.1 (hD.len j _ hd)
            subst hl
            obtain ⟨M, hM, rfl⟩ := Option.map_eq_some_iff.1
              (show (msgOf pre w (fun p => prjS (.inl p)) prjP cur).map Sum.inl = some τ from hτ)
            obtain ⟨-, z0', zJ, h0, hJ', rfl⟩ := msgOf_eq_some hM
            rw [show cur.shd = d₀.2.shd from (hD.sh j j₀ _ _ hd h₀).2, hz] at h0
            cases h0
            have hm : m j = mJOf pre w (fun p => prjS (.inl p)) zJ := by
              show mJOf pre w _ (((D j).bind fun d => rdJ prjP d.2.own).getD ([], none)) = _
              rw [hd]
              show mJOf pre w _ ((rdJ prjP cur.own).getD ([], none)) = _
              rw [hJ']
              rfl
            exact ⟨j, S, hS, by rw [hm]; exact hf, by rw [hm]; exact ht⟩
          refine le_trans (pr_mono _ hsub) ?_
          have h2 := pr_chalAt (s := r :: s) (A := (a, A)) (ws := (w, ws))
            hws (Sum.inl (a.join m0 (m j₀))) (fun c : r.Chal =>
              ∃ j S,
                St j = some S ∧
                S (.atV (Sum.inl (a.join m0 (m j)))) = false ∧
                S (PTr.cons (a.join m0 (m j)) c (PTr.empty s)) = true)
          refine le_trans (le_of_eq h2) ?_
          exact (pr_unif_le_of_cnt_le h1).trans
            (Err.Below.errPr_le (s := r :: s) (ε := (e, ε)) hε (Sum.inl (a.join m0 (m j₀))))
      | succ n =>
        -- an earlier round: choose its messages and go on
        obtain ⟨l₀, cur₀⟩ := d₀
        obtain ⟨rc₀, rest₀, rfl⟩ : ∃ rc rest, l₀ = rc :: rest := by
          cases l₀ with
          | nil => exact absurd (hD.len j₀ _ h₀) (by simp)
          | cons rc rest => exact ⟨rc, rest, rfl⟩
        have hhead : ∀ j l cur,
            D j = some (l, cur) → ∃ rc rest, l = rc :: rest ∧ shPart rc = shPart rc₀ := by
          intro j l cur hd
          cases l with
          | nil => exact absurd (hD.len j _ hd) (by simp)
          | cons rc rest =>
            have := (hD.sh j j₀ _ _ hd h₀).1
            simp only [List.map_cons, List.cons.injEq] at this
            exact ⟨rc, rest, rfl, this.1⟩
        cases hz : rd0 prjP rc₀.1.shd with
        | none =>
          refine le_trans (le_of_eq (pr_eq_zero_of_forall_not_mem _ ?_)) (zero_le _)
          rintro x - ⟨j, S, d, τ, -, hd, hτ, -⟩
          obtain ⟨l, cur⟩ := d
          obtain ⟨rc, rest, rfl, hsp⟩ := hhead j l cur hd
          obtain ⟨M, hM, -⟩ := Option.bind_eq_some_iff.1
            (show (msgOf pre w (fun p => prjS (.inl p)) prjP rc.1).bind _ = some τ from hτ)
          obtain ⟨-, z0, zJ, h0, -⟩ := msgOf_eq_some hM
          rw [show rc.1.shd = rc₀.1.shd from congrArg Prod.fst hsp, hz] at h0
          cases h0
        | some z0 =>
          let m0 : a.M0 := m0Of pre w (fun p => prjS (.inl p)) z0
          let m : Fin N → a.Mj := fun j => mJOf pre w (fun p => prjS (.inl p))
            (((D j).bind fun d => d.1.head?.bind fun rc => rdJ prjP rc.1.own).getD ([], none))
          obtain ⟨v, hv⟩ : ∃ v : a.kind.All N r.Chal, ∀ j rc rest cur, D j =
                some (rc :: rest, cur) →
              rc.1.kind = a.kind → a.kind.slot v j = w.chal rc.2.1 := by
            generalize a.kind = k
            cases k with
            | sh =>
              refine ⟨w.chal rc₀.2.1, fun j rc rest cur hd hk => ?_⟩
              obtain ⟨rc', rest', he, hsp⟩ := hhead j _ cur hd
              cases he
              have h2 : (if rc.1.kind = Kind.sh then some rc.2 else none) =
                  (if rc₀.1.kind = Kind.sh then some rc₀.2 else none) :=
                congrArg Prod.snd hsp
              rw [if_pos hk] at h2
              by_cases hk0 : rc₀.1.kind = Kind.sh
              · rw [if_pos hk0] at h2
                rw [Option.some.inj h2]
                rfl
              · rw [if_neg hk0] at h2
                cases h2
            | lo =>
              refine ⟨fun j =>
                  w.chal (((D j).bind fun d => d.1.head?.map fun rc => rc.2.1).getD default),
                fun j rc rest cur hd _ => ?_⟩
              show w.chal (((D j).bind fun d => d.1.head?.map fun rc => rc.2.1).getD default) = _
              rw [hd]
              rfl
          have hD' : Compat (fun j => (D j).map fun d => (d.1.tail, d.2)) n := by
            refine ⟨fun j d hd => ?_, fun j j' d d' hd hd' => ?_, fun j d hd => ?_⟩
            · obtain ⟨d1, h1, rfl⟩ := Option.map_eq_some_iff.1 hd
              have := hD.len j _ h1
              simp only [List.length_tail]
              omega
            · obtain ⟨d1, h1, rfl⟩ := Option.map_eq_some_iff.1 hd
              obtain ⟨d2, h2, rfl⟩ := Option.map_eq_some_iff.1 hd'
              have := hD.sh j j' _ _ h1 h2
              refine ⟨?_, this.2⟩
              show List.map shPart d1.1.tail = List.map shPart d2.1.tail
              rw [List.map_tail, List.map_tail, this.1]
            · obtain ⟨d1, h1, rfl⟩ := Option.map_eq_some_iff.1 hd
              exact hD.cur j d1 h1
          refine le_trans (pr_mono _ ?_)
            (joint_le pre s A ws hws.2 ε hε.2 (fun p => prjS (.inr p))
              (fun z => (prjP z).bind PlainPart.tail?)
            _ ((hJ m0 m).2 v) n _ hD')
          rintro x ⟨j, S, d, τ, hS, hd, hτ, hf, ht⟩
          obtain ⟨l, cur⟩ := d
          obtain ⟨rc, rest, rfl, hsp⟩ := hhead j l cur hd
          obtain ⟨M, hM, h3⟩ := Option.bind_eq_some_iff.1
            (show (msgOf pre w (fun p => prjS (.inl p)) prjP rc.1).bind _ = some τ from hτ)
          obtain ⟨τ', hτ', rfl⟩ := Option.map_eq_some_iff.1 h3
          obtain ⟨hk, z0', zJ, h0, hJ', rfl⟩ := msgOf_eq_some hM
          rw [show rc.1.shd = rc₀.1.shd from congrArg Prod.fst hsp, hz] at h0
          cases h0
          have hm : m j = mJOf pre w (fun p => prjS (.inl p)) zJ := by
            show mJOf pre w _
                (((D j).bind fun d => d.1.head?.bind fun rc => rdJ prjP rc.1.own).getD
                  ([], none)) = _
            rw [hd]
            show mJOf pre w _ ((rdJ prjP rc.1.own).getD ([], none)) = _
            rw [hJ']
            rfl
          have hc := hv j rc rest cur hd hk
          refine ⟨j, _, (rest, cur), τ', by rw [hS]; rfl, by rw [hd]; rfl, hτ', ?_, ?_⟩
          · show S (PTr.cons (a.join m0 (m j)) (a.kind.slot v j) (.atV τ')) = false
            rw [hm, hc]
            exact hf
          · show S (PTr.cons (a.join m0 (m j)) (a.kind.slot v j) (τ'.snoc (chalAt ws τ' x.1))) =
              true
            rw [hm, hc]
            exact ht

end TypedOracleCompiler.Compile.Batch
