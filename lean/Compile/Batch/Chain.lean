-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Chain.lean: one round of the proof that the Fiat-Shamir chain of an accepted proof of
a slot is rooted (`rooted`, `link`, records and items: Compile/Batch/Rooted.lean; formats (F1) to
(F5): `Head`, Compile/Batch/Oracles.lean).

A query of round i, with the head h, is rooted if its data can be read from h and the earlier
entries pre of the trace (`rooted t pre i h`). The data are: for a locally rooted query: the
external roots, the instance and the records of the earlier rounds; for a shared rooted query: the
external roots, the request root, the data of the slot values and the earlier shared queries. Among
the hypotheses of `step_rooted`: neither hash event `EM`, `EF` (Compile/Batch/Events.lean) occurs.

Notation: `Data` (Compile/Batch/Rooted.lean): the data of a rooted query: of a local round before
the shared rounds (`locV`), of a shared round (`shd`), of a local round after them (`locA`); an
item: an `Item` (Compile/Batch/Rooted.lean): what the prover message of one round of a slot's
transcript is read from; a record: a `Rec` (Compile/Batch/Rooted.lean): an item with the answer that
gives the verifier message of its round; `Phase lam` (`first`, `loc`, `shr`, `aft`;
Compile/Batch/Verifier.lean): how far the chain of a slot has come; `VStep`
(Compile/Batch/Runs.lean): one round of the verifier's chain: from the phase ph, with the item cur
and the answer ans of its Fiat-Shamir query, to the next phase; rt holds the roots of the round;
`C`: a `Ctx W`: the fixed data of an accepted proof of a slot: trace, protocol, external roots
(cms), instance (none: Test, Link), salt, request root, slot number (j); the slot value: the answer
of the oracle g (`OracleName.g t`, Compile/Batch/Oracles.lean) in the joining round; the request tree: the
Merkle tree over the slot values (the head of Compile/Batch/Prover.lean).
-/
import Compile.Batch.Runs

noncomputable section

namespace Compile.Batch
open Iop Rom Prob

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-! ## Part 1. Occurrence, and extraction before a Fiat-Shamir query -/

section Occ
variable {K : ℕ} {t : Tag}

theorem evM_occurs_rt (q : FbIn lam L t) (a : FsAns lam K) {d : Dig lam} (h : q.rt = some d) :
    (evM lam K L).Occurs (fbE t q a) d := by
  show d ∈ rootFields q
  unfold rootFields
  rw [h]
  exact List.mem_cons_self

theorem evM_occurs_g (gq : JoiningRoundQuery lam L t) (c : Dig lam) {d : Dig lam} (h : gq.rt = some d) :
    (evM lam K L).Occurs (gE t gq c) d := by
  show d ∈ gq.rt.toList
  rw [h]
  exact List.mem_cons_self

theorem evM_occurs_cms {q : FbIn lam L t} (a : FsAns lam K) {cms : List (Dig lam)} {x : Option X}
    {sl : Bits} (h : q.head = .f1 cms x sl) {c : Dig lam} (hc : c ∈ cms.take 2) :
    (evM lam K L).Occurs (fbE t q a) c := by
  show c ∈ rootFields q
  simp only [rootFields, h]
  exact List.mem_append_right _ hc

theorem evM_occurs_rtreq {q : FbIn lam L t} (a : FsAns lam K) {cms : List (Dig lam)}
    {rtreq : Dig lam} (h : q.head = .f4 cms (List.ofFn rtreq)) :
    (evM lam K L).Occurs (fbE t q a) rtreq := by
  show rtreq ∈ rootFields q
  simp only [rootFields, h, digOf_ofFn]
  exact List.mem_append_right _ (List.mem_append_left _ (List.mem_singleton.2 rfl))

theorem evF_occurs_chain {q : FbIn lam L t} (a : FsAns lam K) {v : Bits} (h : v ∈ chainFields q) :
    (evF lam K L).Occurs (fbE t q a) v :=
  List.mem_cons_of_mem _ h

theorem evF_occurs_gρ (gq : JoiningRoundQuery lam L t) (c : Dig lam) : (evF lam K L).Occurs (gE t gq c) gq.ρ :=
  List.mem_cons_of_mem _ List.mem_cons_self

theorem evF_occurs_rleaf (v : Bits) (u : Dig lam) :
    (evF lam K L).Occurs (⟨OracleName.rleaf, v, u⟩ : QA (spec lam K L)) v :=
  List.mem_cons_self

/-- Outside `EM`: under a digest that occurs before a Fiat-Shamir query, or at it, the trace before
that query and the whole trace determine the same leaf. -/
theorem extLeaf_before {tr pre post : Trace (spec lam K L)} {q : FbIn lam L t} {a : FsAns lam K}
    (htr : tr = pre ++ fbE t q a :: post) (hM : ¬ EM tr) {c : Dig lam}
    (hc : (evM lam K L).OccursIn (pre ++ [fbE t q a]) c) (d j : ℕ) :
    extLeaf pre d c j = extLeaf tr d c j := by
  have hp : pre ++ [fbE t q a] <+: tr := ⟨post, by simp [htr]⟩
  rw [← extLeaf_stable hM hp hc]
  exact (preimage_concat (pairM lam K L) pre (fbE t q a) rfl rfl (posOf d j) c).symm

theorem extReq_before {tr pre post : Trace (spec lam K L)} {q : FbIn lam L t} {a : FsAns lam K}
    (htr : tr = pre ++ fbE t q a :: post) (hM : ¬ EM tr) {c : Dig lam}
    (hc : (evM lam K L).OccursIn (pre ++ [fbE t q a]) c) (d j : ℕ) :
    extReq pre d c j = extReq tr d c j := by
  have hp : pre ++ [fbE t q a] <+: tr := ⟨post, by simp [htr]⟩
  rw [← extReq_stable hM hp hc]
  exact (preimage_concat (pairR lam K L) pre (fbE t q a) rfl rfl (posOf d j) c).symm

/-- The roots of a record whose queries are entries of a trace occur in it. -/
theorem roots_occur {pre : Trace (spec lam K L)} {rc : Rec lam K L t} (h : RecIn pre rc) :
    (∀ z d, rc.1.shd = some z → z.1 = some d → (evM lam K L).OccursIn pre d) ∧
      (∀ z d, rc.1.own = some z → z.1 = some d → (evM lam K L).OccursIn pre d) := by
  obtain ⟨it, a⟩ := rc
  cases it with
  | lo q =>
    refine ⟨fun z d hz => (by cases hz), fun z d hz hd => ?_⟩
    cases Option.some.inj hz
    exact ⟨_, h, evM_occurs_rt q a hd⟩
  | jn gq q =>
    obtain ⟨⟨c, hg⟩, hq⟩ := h
    refine ⟨fun z d hz hd => ?_, fun z d hz hd => ?_⟩
    · cases Option.some.inj hz
      exact ⟨_, hq, evM_occurs_rt q a hd⟩
    · cases Option.some.inj hz
      exact ⟨_, hg, evM_occurs_g gq c hd⟩
  | sh q =>
    refine ⟨fun z d hz hd => ?_, fun z d hz => (by cases hz)⟩
    cases Option.some.inj hz
    exact ⟨_, h, evM_occurs_rt q a hd⟩

/-- Outside `EF`, an entry whose link value occurs at another entry comes before that entry. -/
theorem mem_of_link_occurs {tr pre post : Trace (spec lam K L)} (hF : ¬ EF tr)
    {e e' : QA (spec lam K L)} (htr : tr = pre ++ e :: post) (he' : e' ∈ tr) {v : Bits}
    (ha : (evF lam K L).answer e' = some v) (ho : (evF lam K L).Occurs e v) (hne : e' ≠ e) :
    e' ∈ pre := by
  have h1 := Merkle.Events.mem_prefix_of_answer
    hF (tr' := pre ++ [e]) ⟨post, by simp [htr]⟩ ⟨e, by simp, ho⟩ he' ha
  rcases List.mem_append.1 h1 with h2 | h2
  · exact h2
  · exact absurd (List.mem_singleton.1 h2) hne

/-- If the first occurrence of e' is in pre, then pre begins with the entries before that
occurrence. -/
theorem prefix_of_mem {E : Type} {tr pre₀ post₀ pre post : List E} {e' e : E}
    (h₀ : tr = pre₀ ++ e' :: post₀) (hn : e' ∉ pre₀) (h : tr = pre ++ e :: post) (hm : e' ∈ pre) :
    ∃ more, pre = pre₀ ++ more := by
  rcases List.prefix_or_prefix_of_prefix
    (l₁ := pre₀) (l₂ := pre) (l₃ := tr) ⟨_, h₀.symm⟩ ⟨_, h.symm⟩ with h1 | h1
  · obtain ⟨more, hm'⟩ := h1
    exact ⟨more, hm'.symm⟩
  · exact absurd (h1.subset hm) hn

end Occ

/-! ## Part 2. The data of an accepted proof -/

/-- the fixed data of an accepted proof of a slot: trace, protocol, external roots (cms), instance
(none: Test, Link), salt, request root, slot number (j) -/
structure Ctx (W : QueryLayout lam L) where
  tr : Tc W
  t : Tag
  cms : List (Dig lam)
  x : Option X
  salt : Bits
  rtreq : Dig lam
  j : ℕ

variable {W : QueryLayout lam L}

/-- the instance as it is in (F1) (`Head.f1`) -/
def Ctx.xo (C : Ctx W) : Option X := C.x.map L.early

/-- The data of the query q, after pre, are those of our slot: q is locally rooted with our external
roots, our instance and the records l, and cur is q; or it is shared rooted with our external roots
and request root, a slot value is extracted at our slot number, and this slot value has our
instance, the records l and the current item cur. -/
def Ours (C : Ctx W) (pre : Tc W) (q : FbIn lam L C.t)
    (l : List (Rec lam W.K L C.t)) (cur : Item lam L C.t) : Prop :=
  ((rooted C.t pre q.round q.head = some (.locV C.cms C.xo l) ∨
      rooted C.t pre q.round q.head = some (.locA C.cms C.xo l)) ∧
    cur = .lo q) ∨
  ∃ slot sh c sd,
    rooted C.t pre q.round q.head = some (.shd C.cms (List.ofFn C.rtreq) slot sh) ∧
    extReq pre W.depthReq C.rtreq C.j = some c ∧
    slot c = some sd ∧ sd.x = C.xo ∧
    slotTr sd sh q = (l, cur)

/-- What is known before round i, in the phase ph, with the records front of the earlier rounds: in
the phase `first`, i = 0 and no records; else the last query of the chain, at its first place in the
trace, had the data of our slot. -/
def PrevOK (C : Ctx W) (i : ℕ) : Phase lam → List (Rec lam W.K L C.t) → Prop
  | .first, front => i = 0 ∧ front = []
  | .loc ρ, front =>
    ∃ q' a' pre₀ post₀ l,
      C.tr = pre₀ ++ fbE C.t q' a' :: post₀ ∧
      fbE C.t q' a' ∉ pre₀ ∧
      q'.round + 1 = i ∧ link a' = ρ ∧
      rooted C.t pre₀ q'.round q'.head = some (.locV C.cms C.xo l) ∧
      front = l ++ [(.lo q', a')]
  | .aft ρ _, front =>
    ∃ q' a' pre₀ post₀ l,
      C.tr = pre₀ ++ fbE C.t q' a' :: post₀ ∧
      fbE C.t q' a' ∉ pre₀ ∧
      q'.round + 1 = i ∧ link a' = ρ ∧
      rooted C.t pre₀ q'.round q'.head = some (.locA C.cms C.xo l) ∧
      front = l ++ [(.lo q', a')]
  | .shr ρ0 c, front =>
    ∃ q' a' pre₀ post₀ slot sh sd,
      C.tr = pre₀ ++ fbE C.t q' a' :: post₀ ∧
      fbE C.t q' a' ∉ pre₀ ∧
      q'.round + 1 = i ∧ link a' = ρ0 ∧
      rooted C.t pre₀ q'.round q'.head = some (.shd C.cms (List.ofFn C.rtreq) slot sh) ∧
      extReq pre₀ W.depthReq C.rtreq C.j = some (List.ofFn c) ∧
      slot (List.ofFn c) = some sd ∧
      sd.x = C.xo ∧
      front = (slotTr sd sh q').1 ++ [((slotTr sd sh q').2, a')]

/-- Outside `EF`: every proper prefix of the trace that contains the last query of the chain extends
the trace before its first occurrence, and `predF` finds the query in it from its link value. -/
theorem resolve_prev (C : Ctx W) (hF : ¬ EF C.tr) {q' : FbIn lam L C.t} {a' : FsAns lam W.K}
    {pre₀ post₀ : Tc W} (h₀ : C.tr = pre₀ ++ fbE C.t q' a' :: post₀)
    (hn₀ : fbE C.t q' a' ∉ pre₀) {e : QA (spec lam W.K L)} {pre post : Tc W}
    (htr : C.tr = pre ++ e :: post) (hm : fbE C.t q' a' ∈ pre) :
    (∃ more, pre = pre₀ ++ more) ∧ predF C.t pre q'.round (link a') = some (q', a') :=
  ⟨prefix_of_mem h₀ hn₀ htr hm, predF_eq hF (by rw [htr]; exact List.subset_append_left _ _) hm⟩

/-! ## Part 3. One round -/

theorem fbE_ne_of_round {K : ℕ} {t : Tag} {q q' : FbIn lam L t}
    {a a' : FsAns lam K} (h : q'.round ≠ q.round) : fbE t q' a' ≠ fbE t q a :=
  fun he => h (congrArg FbIn.round (fbE_inj he).1)

/-- One round, outside `EM`, `EF`, under the hypotheses below: if the chain so far had the data of
our slot, then so has the query of this round, at its first place in the trace (`Ours`); `PrevOK`
holds for the next round, and the round's record is in the trace (`RecIn`). -/
theorem step_rooted (C : Ctx W) (hM : ¬ EM C.tr) (hF : ¬ EF C.tr) {r : Round} {s : Shape}
    {a : RAnn r} {A : RoundSplits s} {embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L C.t) (annOf L C.t)} {i : ℕ}
    {pl : r.Plain} {ph ph₁ : Phase lam} {cur : Item lam L C.t} {ans : FsAns lam W.K}
    {rt : RtC lam × RtC lam} {front : List (Rec lam W.K L C.t)}
    (hv : VStep C.tr C.cms C.x C.salt C.rtreq embP i pl ph cur ans ph₁ rt)
    (hprev : PrevOK C i ph front) {pre post : Tc W} (htr : C.tr = pre ++ fbE C.t cur.q ans :: post)
    (hnew : fbE C.t cur.q ans ∉ pre)
    (hfin : ∀ c, ph₁.slotVal = some c → extReq C.tr W.depthReq C.rtreq C.j = some (List.ofFn c)) :
    Ours C pre cur.q front cur ∧
    PrevOK C (i + 1) ph₁ (front ++ [(cur, ans)]) ∧
    RecIn (pre ++ [fbE C.t cur.q ans]) (cur, ans) := by
  have hself : fbE C.t cur.q ans ∈ pre ++ [fbE C.t cur.q ans] := by simp
  cases hv with
  | f1 root ans hk =>
    obtain ⟨rfl, rfl⟩ := hprev
    exact ⟨Or.inl ⟨Or.inl rfl, rfl⟩, ⟨_, ans, pre, post, [], htr, hnew, rfl, rfl, rfl, rfl⟩, hself⟩
  | f2 ρ root ans hk =>
    obtain ⟨q', a', pre₀, post₀, l, h₀, hn₀, rfl, rfl, hr, rfl⟩ := hprev
    have hm : fbE C.t q' a' ∈ pre :=
      mem_of_link_occurs hF htr (by rw [h₀]; simp) (evF_answer_fbE _ q' a')
        (evF_occurs_chain ans (List.mem_singleton.2 rfl))
        (fbE_ne_of_round (Nat.ne_of_lt (Nat.lt_succ_self _)))
    obtain ⟨⟨more, rfl⟩, hp⟩ := resolve_prev C hF h₀ hn₀ htr hm
    obtain ⟨D', h1, h2⟩ := rooted_mono more _ _ _ hr
    cases (show D' = .locV C.cms C.xo l from h2)
    have h3 := viaTail_locV (rec := rooted C.t (pre₀ ++ more) q'.round) hp h1
    exact ⟨Or.inl ⟨Or.inl h3, rfl⟩, ⟨_, ans, _, post, _, htr, hnew, rfl, rfl, h3, rfl⟩, hself⟩
  | f2' ρ c root ans hk =>
    obtain ⟨q', a', pre₀, post₀, l, h₀, hn₀, rfl, rfl, hr, rfl⟩ := hprev
    have hm : fbE C.t q' a' ∈ pre :=
      mem_of_link_occurs hF htr (by rw [h₀]; simp) (evF_answer_fbE _ q' a')
        (evF_occurs_chain ans (List.mem_singleton.2 rfl))
        (fbE_ne_of_round (Nat.ne_of_lt (Nat.lt_succ_self _)))
    obtain ⟨⟨more, rfl⟩, hp⟩ := resolve_prev C hF h₀ hn₀ htr hm
    obtain ⟨D', h1, h2⟩ := rooted_mono more _ _ _ hr
    cases (show D' = .locA C.cms C.xo l from h2)
    have h3 := viaTail_locA (rec := rooted C.t (pre₀ ++ more) q'.round) hp h1
    exact ⟨Or.inl ⟨Or.inr h3, rfl⟩, ⟨_, ans, _, post, _, htr, hnew, rfl, rfl, h3, rfl⟩, hself⟩
  | f3 ρ0 c root ans hk =>
    obtain ⟨q', a', pre₀, post₀, slot, sh, sd, h₀, hn₀, rfl, rfl, hr, -, hs, hx, rfl⟩ := hprev
    have hm : fbE C.t q' a' ∈ pre :=
      mem_of_link_occurs hF htr (by rw [h₀]; simp) (evF_answer_fbE _ q' a')
        (evF_occurs_chain ans List.mem_cons_self)
        (fbE_ne_of_round (Nat.ne_of_lt (Nat.lt_succ_self _)))
    obtain ⟨⟨more, rfl⟩, hp⟩ := resolve_prev C hF h₀ hn₀ htr hm
    obtain ⟨D', h1, slot', rfl, h2⟩ := rooted_mono more _ _ _ hr
    have h3 := rooted_f3_of hp h1 (h2 _ _ hs) (joinRecs_concat sd sh (q', a'))
    rw [hx] at h3
    exact ⟨Or.inl ⟨Or.inr h3, rfl⟩, ⟨_, ans, _, post, _, htr, hnew, rfl, rfl, h3, rfl⟩, hself⟩
  | f5 ρ0 c root ans hk =>
    obtain ⟨q', a', pre₀, post₀, slot, sh, sd, h₀, hn₀, rfl, rfl, hr, he, hs, hx, rfl⟩ := hprev
    have hm : fbE C.t q' a' ∈ pre :=
      mem_of_link_occurs hF htr (by rw [h₀]; simp) (evF_answer_fbE _ q' a')
        (evF_occurs_chain ans (List.mem_singleton.2 rfl))
        (fbE_ne_of_round (Nat.ne_of_lt (Nat.lt_succ_self _)))
    obtain ⟨⟨more, rfl⟩, hp⟩ := resolve_prev C hF h₀ hn₀ htr hm
    obtain ⟨D', h1, slot', rfl, h2⟩ := rooted_mono more _ _ _ hr
    have h3 := rooted_f5_of hp h1
    have he' : extReq (pre₀ ++ more) W.depthReq C.rtreq C.j = some (List.ofFn c) :=
      (pairR lam W.K L).preimage_mono (List.prefix_append _ _) he
    have h4 : ∀ q : FbIn lam L C.t, slotTr sd (sh ++ [(q', a')]) q =
        ((slotTr sd sh q').1 ++ [((slotTr sd sh q').2, a')], .sh q) := fun q => by
      unfold slotTr
      rw [joinRecs_concat sd sh (q', a')]
      rfl
    exact ⟨Or.inr ⟨slot', _, _, sd, h3, he', h2 _ _ hs, hx, h4 _⟩,
      ⟨_, ans, _, post, slot', _, sd, htr, hnew, rfl, rfl, h3, he', h2 _ _ hs, hx, by rw [h4]; rfl⟩,
      hself⟩
  | join ρ rtj rt0 c ans hk hg =>
    obtain ⟨q', a', pre₀, post₀, l, h₀, hn₀, rfl, rfl, hr, rfl⟩ := hprev
    -- the slot value is extracted under the request root before the query (F4)
    have he : extReq pre W.depthReq C.rtreq C.j = some (List.ofFn c) := by
      rw [extReq_before htr hM ⟨_, hself, evM_occurs_rtreq ans rfl⟩]
      exact hfin c rfl
    -- so its query to g is in pre, and so is the last local query
    obtain ⟨u, hu⟩ := rleaf_mem_of_extReq he
    have hpre : pre <+: C.tr := ⟨_, htr.symm⟩
    have hg' := Merkle.Events.mem_prefix_of_answer
      hF hpre ⟨_, hu, evF_occurs_rleaf _ u⟩ hg (evF_answer_gE _ _ c)
    have hm : fbE C.t q' a' ∈ pre :=
      Merkle.Events.mem_prefix_of_answer
        hF hpre ⟨_, hg', evF_occurs_gρ _ c⟩ (by rw [h₀]; simp) (evF_answer_fbE _ q' a')
    obtain ⟨⟨more, rfl⟩, hp⟩ := resolve_prev C hF h₀ hn₀ htr hm
    obtain ⟨D', h1, h2⟩ := rooted_mono more _ _ _ hr
    cases (show D' = .locV C.cms C.xo l from h2)
    have h3 := viaTail_locV (rec := rooted C.t (pre₀ ++ more) q'.round) hp h1
    have h4 := slotFn_of (rec := rooted C.t (pre₀ ++ more) q'.round) (cms := C.cms)
      (predG_eq hF hpre.subset hg') h3
    exact ⟨Or.inr ⟨_, [], _, _, rfl, he, h4, rfl, rfl⟩,
      ⟨_, ans, _, post, _, [], _, htr, hnew, rfl, rfl, rfl, he, h4, rfl, rfl⟩,
      ⟨⟨c, List.mem_append_left _ hg'⟩, hself⟩⟩

end Compile.Batch
