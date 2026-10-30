-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Heard.lean: at the member of a chain's thread at which the
honest side of an attention segment's own rounds (kind K5) is seated: what the verifier's hearing
holds of challenges, and the named points and weights that the verifier makes of it, are the
prover's. Statements with their proofs. EVERY STATEMENT IS CONDITIONAL.

  base_is         the seat's number of rounds in front is the number of challenges heard in front
  chalOf_own      so the challenges that a part may read are the member's own, from its first on
  reads_played    the prover's challenges hold the elements that the rounds as played drew, also
                  when more challenges follow
  heard_at        **where the kind's hearing returns at the rounds as played, it holds the
                  prover's challenges, in all parts** (SameTo,
                  Johnson/Desc/K5/Honest/Law/HeardIs.lean)
  key_at          under the ties (K5Script, Honest/K5/Law/Script.lean): the prover's key points in
                  front of each part, and behind the last, are the state's
  points_at       **the prover's named points and weights are the verifier's**, field by field
                  (PtsTo, Johnson/Desc/K5/Honest/Law/PointsIs.lean)
  front_agree     the challenges in front of part number q and all the member's challenges are one
                  in the rounds in front of that part

Who is meant to show the premises. K5Seated: whoever lays the thread's list of halves and makes the
seat. The thread's clause on the challenges heard, and the prover's side of the member's step: they
are in hand wherever a law on the member is asked. The hearing's return: it follows from the
member's yes. K5Script is not shown.

Limits. Nothing is said of a value that is sent. The equations are word for word. No property is
claimed. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Script
import Johnson.Desc.ProofFile.Honest.Thread.HeardLaw
import Johnson.Desc.K5.Honest.Law.Stable

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S noDigest)
open VerifiableInference.Desc.Sound (MsgQ)
open VerifiableInference.Desc.First.Att.P (Par Heard Left Pts hear pointsOf St)
open H2K5.Honest (Chal Reads Agree SameTo PtsTo heardAt ptsOf heard_is_ours points_same)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}

/-- The seat's number of rounds in front of the place is the number of challenges heard there.
CONDITIONAL: the half's seat; the thread's clause on the challenges heard. -/
theorem base_is (Hs : K5Seated T b cells Z p blk) {m : Mid (Local W₀ Rc Xi Tr) X}
    (hF : T.Fit b m) : m.st.heard.length = Z.base := by
  have h := Hs.fits m.st.heard hF
  unfold Seat5.fits at h
  exact beq_iff_eq.1 (Bool.and_eq_true_iff.1 h).1

/-- The challenges that a part may read are the member's own. CONDITIONAL: as `base_is`. -/
theorem chalOf_own (Hs : K5Seated T b cells Z p blk) {m : Mid (Local W₀ Rc Xi Tr) X}
    (hF : T.Fit b m) (ds : List Fmt.Drawn) : (chalOf Z (m.st.heard ++ ds)).own = ds :=
  List.drop_left' (base_is Hs hF)

/-- **The prover's challenges hold the elements that the rounds as played drew.** more: challenges
that follow behind the member's. CONDITIONAL: the half's seat; the thread's clause on the challenges
heard; the prover's side of the member's step. -/
theorem reads_played (Hs : K5Seated T b cells Z p blk) {k : Coins Bk}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn} (hF : T.Fit b m)
    (hM : T.Moved blk k m E ds y cols) (more : List Fmt.Drawn) :
    Reads (chalOf Z (m.st.heard ++ (ds ++ more))) ((roundsOf y.1).map noDigest) := by
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  have hdr : (roundsOf y.1).map (·.drawn) = ds := yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)
  intro i r hr
  rw [chalOf_own Hs hF]
  rw [List.getElem?_map] at hr
  obtain ⟨r0, h0, rfl⟩ := Option.map_eq_some_iff.1 hr
  have h1 : ds[i]? = some r0.drawn := by rw [← hdr, List.getElem?_map, h0]; rfl
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h1).1, h1]
  rfl

/-- **Where the kind's hearing returns at the rounds as played, it holds the prover's challenges, in
all parts.** CONDITIONAL: as `reads_played`, and the hearing's return, from any ledger. -/
theorem heard_at (Hs : K5Seated T b cells Z p blk) {k : Coins Bk}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn} (hF : T.Fit b m)
    (hM : T.Moved blk k m E ds y cols) {F : Fork} {hd : Heard} {st : St}
    (hh : hear p.own (F, (roundsOf y.1).map noDigest, 0) = some (hd, st))
    (more : List Fmt.Drawn) (q : Nat) :
    SameTo Z.P.x q hd (heardAt Z.P (chalOf Z (m.st.heard ++ (ds ++ more))) fun _ => none) := by
  rw [Hs.own] at hh
  exact heard_is_ours Z.P _ hh (reads_played Hs hF hM more) q

/-- The challenges in front of part number q, and all the member's challenges, are one in the rounds
in front of that part. CONDITIONAL: as `base_is`. -/
theorem front_agree (Hs : K5Seated T b cells Z p blk) {m : Mid (Local W₀ Rc Xi Tr) X}
    (hF : T.Fit b m) (ds : List Fmt.Drawn) (q : Nat) :
    Agree (H2K5.Honest.firstOf Z.P.x q)
      (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x q)))
      (chalOf Z (m.st.heard ++ ds)) := fun i hi => by
  rw [chalOf_own Hs hF, chalOf_own Hs hF, List.getElem?_take_of_lt hi]

section
variable {A : OnBytes.Attention.Plan} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

/-- **The prover's key points are the state's**, in front of each part and behind the last.
CONDITIONAL: on the ties, which are not shown; on the thread in front of the member. -/
theorem key_at (Sc : K5Script T b cells Z A blk own rdOf) {k : Coins Bk} {s : First.S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : Thr T b k s m E)
    {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att) {ds : List Fmt.Drawn}
    (hd : drawsFit blk.rounds ds = true) :
    ∃ g, att.g = some g ∧ (∀ n, (chalOf Z (m.st.heard ++ ds.take n)).zk = g.zk) ∧
      (chalOf Z (m.st.heard ++ ds)).zk = g.zk := by
  obtain ⟨g, hg, -, hk⟩ := Sc.keyTie k s m E hT att e
  refine ⟨g, hg, fun n => hk ds n hd, ?_⟩
  have h := hk ds ds.length hd
  rw [List.take_length] at h
  exact h

/-- **The prover's named points and weights are the verifier's**, field by field. L: the rows that
the verifier lays; g: what the lookup on the calls heard. CONDITIONAL: on the ties, which are not
shown; the half's seat; the thread in front; the prover's side of the step; the hearing's return;
and the return of both calls of the verifier's function for the points. -/
theorem points_at (Hs : K5Seated T b cells Z p blk) (Sc : K5Script T b cells Z A blk own rdOf)
    {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn} (hT : Thr T b k s m E)
    (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols)
    {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att)
    {g : OnBytes.Model.Forest.Heard} (hg : att.g = some g) {F : Fork} {hd5 : Heard} {st : St}
    (hh : hear p.own (F, (roundsOf y.1).map noDigest, 0) = some (hd5, st)) {L : Left} {p₀ pv : Pts}
    (hp₀ : ptsOf Z.P (chalOf Z (m.st.heard ++ ds)) = some p₀)
    (hp : pointsOf Z.P.g g.zk hd5 L = some pv) (q : Nat) : PtsTo Z.P.x q p₀ pv := by
  obtain ⟨g', hg', -, hk⟩ := key_at Sc hT e hd
  obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hg)
  have S := heard_at Hs hT.2.1 hM hh [] q
  rw [List.append_nil] at S
  rw [← hk] at hp
  exact points_same Z.P S hp₀ hp

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.base_is
#print axioms ProofFile.Honest.K5.chalOf_own
#print axioms ProofFile.Honest.K5.reads_played
#print axioms ProofFile.Honest.K5.heard_at
#print axioms ProofFile.Honest.K5.front_agree
#print axioms ProofFile.Honest.K5.key_at
#print axioms ProofFile.Honest.K5.points_at
