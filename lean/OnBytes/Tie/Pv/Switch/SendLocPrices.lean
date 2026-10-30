-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Switch/SendLocPrices.lean: the planner's price of a sending of any number of sampled
messages covers the shares of their clashing seeds. Under named conditions on its letters, and if
the planner has admitted the two rounds, the two errors of the typed block of a sending with a
rider, followed by the round of positions, are covered by the errors of the plan's rounds SEND seed
and LOC. Definitions, statements and proofs.

Background. A round of a plan has an error: the upper end of a bound that the planner computes in
its own arithmetic on intervals (Bound, OnBytes/Params/Real.lean). OnBytes/Params/BoundLaws.lean and
SqrtLaws.lean say which number a bound encloses, unless it is marked bad. That a price covers a
count means: the count, divided by the number of values of the verifier's message, is at most the
round's error (OnBytes/Params/MorePrices.lean). A typed block has errors that are such counts.
OnBytes/Tie/Pv/Switch/SendLocShape.lean lays the block `Cb.Pv.SendLocRide.R z` beside the plan's two
rounds sendSeed s o roots and locRound s c g b r a, and ties their numbers of bytes and draws. This
file ties their errors.

The first half is of general use: it speaks of the planner alone. OnBytes/Params/MorePrices.lean
has the price of a sending of one message and of a link's two (send_one_covers, send_two_covers),
and names a sending of more messages as not claimed.

Main names, on the planner alone:
  `clashShare s L x`: for a list of at most L code words and the sampled message x: L choose 2
    pairs, times the share of the seeds at which a pair can clash, for s.samples answers
    (clashSeeds, allSeeds, OnBytes/Params/RecordPrice.lean).
  `send_many_le`, `send_many_covers`: for every list o of sampled messages and numbers that are at
    most the planner's list sizes, the sum of the shares is at most the number that the planner's
    sum of sample errors encloses; so it is at most that bound's error, if it is not marked bad.
  `said_covers`: a number that is not negative and at most what a routine's bound encloses is at
    most the error of the round that close adds, also where close counts the bound once for each
    instance. Asked: what close has tested of the round (RoundSpec.Good).
Main names, on the typed block:
  `SendLocPrices z s o g idx`: the conditions on the letters z, along an enumeration idx of the
    family's members by the places of o. Each is told at its field.
  `sendLoc_seed_covers`: under them the block's first error, ldSendFamErr, over the number of seeds
    is at most the error of the round of sendSeed s o roots.
  `sendLoc_loc_covers`: under them, if the long positions are the numbers below 2 ^ logN and
    baseCount s c g positions are drawn, the block's second error, (|P| - e - 1) ^ t, over the
    number of lists of t positions is at most the error of the round of locRound. It asks a radius
    from the upper radius on and no upper limit: a larger e makes the count smaller.
  `sendLoc_covers`: both, said of the block's own lists of errors and of numbers of values
    (SendLocRide.errs, SendLocRide.vals).

Limits.
 - One list bound and one radius must serve two sides. That the two counts bound a prover's chance
   is not said here: it is SendLocRide.hAt, under the block's own condition SendLocRide.OK. That
   condition asks that L a is at least the size of a member's list (LdSendD.HypK) and has laws on
   the open word at the radius e (LdLocD.HypK). Here L a must be at most the planner's list size,
   and e at least the upper radius. No statement here says that numbers exist which meet both.
 - No statement here says that a value of the letters meets SendLocPrices. idx is any enumeration:
   nothing says that a member is the message at its place in o. Nothing ties the number of elements
   of E to s.cardE: the conditions speak of s.cardE alone.
 - The conditions rule, source and counted follow from JohnsonGroup s g e
   (OnBytes/Params/GroupPrices.lean). That record asks more, which is not needed here: conditions
   on the mask code, and a radius of at most the distance times the length. The closeness rounds of
   a group ask a radius up to the lower radius, a draw of positions one from the upper radius on;
   that one number serves both is no law (OnBytes/Params/MorePrices.lean says the same).
 - That the bounds are not marked bad is asked through RoundSpec.Good. Runs gives it of every round
   with a verifier's message that a routine has added (OnBytes/Params/PlanningLaws.lean).
 - Upper ends alone: nothing on how near a price is to the count.
 - Nothing on proof of work, which the plan counts beside a round's error.
-/
import OnBytes.Params.MorePrices
import OnBytes.Tie.Pv.Switch.SendLocShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Switch
open Iop Cb OnBytes OnBytes.Params OnBytes.Plan OnBytes.Params.Bound

/-! ### The planner alone -/

/-- L choose 2 pairs, times the share of the seeds at which a pair can clash in all answers. -/
noncomputable def clashShare (s : Setting) (L : ℕ) (x : SampleSize) : ℝ :=
  ((L.choose 2 * clashSeeds s.cardE x.cubeBits ^ s.samples : ℕ) : ℝ) /
    ((allSeeds s.cardE x.cubeBits ^ s.samples : ℕ) : ℝ)

theorem clashShare_nonneg (s : Setting) (L : ℕ) (x : SampleSize) : 0 ≤ clashShare s L x := by
  unfold clashShare
  positivity

/-- The planner's largest list size is at least 1. -/
theorem one_le_largestList (s : Setting) : ∀ gs : List GroupSize, 1 ≤ largestList s gs
  | [] => le_rfl
  | _ :: gs => le_trans (one_le_largestList s gs) (le_max_right _ _)

/-- One message's share is at most the number that its sample error encloses. -/
theorem clashShare_le (s : Setting) (hq : 2 ≤ s.cardE) {L : ℕ} (x : SampleSize)
    (h : L ≤ largestList s x.groups) :
    clashShare s L x ≤
      ((sampleShare s (largestList s x.groups) x.cubeBits s.samples : ℚ) : ℝ) := by
  have h0 := record_share_le s (L := L) (list := largestList s x.groups) (lg := x.cubeBits)
    (a := s.samples) (b := 0) (x := 0) hq h le_rfl (by simp) (one_le_largestList s x.groups)
  simpa [clashShare] using h0

/-- The sum of the shares, from v on, against the planner's sum, from y on. -/
theorem shares_le (s : Setting) (hq : 2 ≤ s.cardE) :
    ∀ (o : List SampleSize) (Lf : Fin o.length → ℕ),
      (∀ i, Lf i ≤ largestList s (o.get i).groups) → ∀ (y : ℚ) (v : ℝ), v ≤ (y : ℝ) →
        v + ∑ i, clashShare s (Lf i) (o.get i) ≤ ((sampleShares s o y : ℚ) : ℝ)
  | [], _, _, y, v, hv => by simpa [sampleShares] using hv
  | x :: xs, Lf, h, y, v, hv => by
    have h0 : clashShare s (Lf ⟨0, Nat.succ_pos _⟩) x ≤ _ :=
      clashShare_le s hq x (h ⟨0, Nat.succ_pos _⟩)
    have ih := shares_le s hq xs (fun i => Lf i.succ) (fun i => h i.succ)
      (y + sampleShare s (largestList s x.groups) x.cubeBits s.samples)
      (v + clashShare s (Lf ⟨0, Nat.succ_pos _⟩) x) (by push_cast; exact add_le_add hv h0)
    have e : ∑ i : Fin (x :: xs).length, clashShare s (Lf i) ((x :: xs).get i) =
        clashShare s (Lf ⟨0, Nat.succ_pos _⟩) x +
          ∑ i : Fin xs.length, clashShare s (Lf i.succ) (xs.get i) :=
      Fin.sum_univ_succ (n := xs.length) fun i => clashShare s (Lf i) ((x :: xs).get i)
    rw [e, ← add_assoc]
    exact ih

/-- The sum of the shares is at most the number that the planner's sum of sample errors encloses. -/
theorem send_many_le (s : Setting) (hq : 2 ≤ s.cardE) (o : List SampleSize)
    (Lf : Fin o.length → ℕ) (h : ∀ i, Lf i ≤ largestList s (o.get i).groups) :
    ∑ i, clashShare s (Lf i) (o.get i) ≤ ((sampleShares s o ((0 : ℕ) : ℚ) : ℚ) : ℝ) := by
  simpa using shares_le s hq o Lf h ((0 : ℕ) : ℚ) 0 (by simp)

/-- **The price of a sending of any number of sampled messages covers the sum of their shares.** -/
theorem send_many_covers (s : Setting) (hq : 2 ≤ s.cardE) (o : List SampleSize)
    (Lf : Fin o.length → ℕ) (h : ∀ i, Lf i ≤ largestList s (o.get i).groups)
    (g : (sampleSum s o (Bound.ofWord 0)).bad = false) :
    ∑ i, clashShare s (Lf i) (o.get i) ≤
      (((sampleSum s o (Bound.ofWord 0)).error.val : ℚ) : ℝ) :=
  (send_many_le s hq o Lf h).trans
    (le_errorR (enclR_of_encl (encl_sampleSum s o (encl_ofWord 0))) g)

/-- A number that is not negative and at most what a routine's bound encloses is at most the error
of the round that close adds. -/
theorem said_covers {s : Setting} {c : Scope} {name : String} {why : ErrorKind} {e : Bound}
    {d : Draws} {b r a : ℕ} {v w : ℝ} (he : EnclR e w) (hv : 0 ≤ v) (hvw : v ≤ w)
    (hg : (RoundSpec.said name why e d b r a).Good s c) :
    v ≤ ((((RoundSpec.said name why e d b r a).round s c).error.val : ℚ) : ℝ) := by
  obtain ⟨g, -, -⟩ := hg
  show v ≤ ((((RoundSpec.said name why e d b r a).bound s c).error.val : ℚ) : ℝ)
  have hb : (RoundSpec.said name why e d b r a).bound s c =
      if (c == .request && decide (1 < s.instances)) = true then e * Bound.ofNat s.instances
      else e := rfl
  rw [hb] at g ⊢
  by_cases hc : (c == .request && decide (1 < s.instances)) = true
  · rw [if_pos hc] at g ⊢
    have h1 : (1 : ℝ) ≤ (s.instances : ℝ) := by
      have h2 := hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
      exact_mod_cast le_of_lt h2.2
    refine le_trans ?_ (le_errorR (enclR_mul he (enclR_ofNat s.instances)) g)
    nlinarith
  · rw [if_neg hc] at g ⊢
    exact hvw.trans (le_errorR he g)

/-! ### The typed block -/

/-- One member of a family: its count among the joint seeds against its share. m: from how many
joint seeds a seed of the member may come; zd: the member's seeds; D: the joint seeds; er: the
member's clashing seeds; C: the pairs; cl of al: the share. -/
theorem member_le {m zd D er C cl al : ℕ} (hD : m * zd = D) (hD0 : 0 < D) (hal : 0 < al)
    (h : er * al ≤ cl * zd) :
    ((m * (C * er) : ℕ) : ℝ) / (D : ℝ) ≤ ((C * cl : ℕ) : ℝ) / ((al : ℕ) : ℝ) := by
  rw [div_le_div_iff₀ (by exact_mod_cast hD0) (by exact_mod_cast hal)]
  have k : m * (C * er) * al ≤ C * cl * D := by
    rw [← hD]
    calc m * (C * er) * al = m * C * (er * al) := by ring
      _ ≤ m * C * (cl * zd) := Nat.mul_le_mul_left _ h
      _ = C * cl * (m * zd) := by ring
  exact_mod_cast k

theorem allSeeds_pos {q : ℕ} (hq : 2 ≤ q) (lg : ℕ) : 0 < allSeeds q lg := by
  unfold allSeeds
  exact Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)

variable {E : Type} [Field E] [Fintype E] (z : Cb.Pv.SendLocRide.Size E)

/-- The conditions on the letters z of the block under which the plan's two errors cover the
block's. idx: an enumeration of the family's members by the places of the list o of sampled
messages. -/
structure SendLocPrices (s : Setting) (o : List SampleSize) (g : GroupSize)
    (idx : z.sw.d.N.O ≃ Fin o.length) : Prop where
  /-- the extension field has two elements or more -/
  field : 2 ≤ s.cardE
  /-- exact marginals: mult a times the number of the member's seeds is the number of joint seeds -/
  marginals : ∀ a,
    z.sw.d.Sd.mult a * Fintype.card (z.sw.d.N.om a).Z.D = Fintype.card z.sw.d.Sd.D
  /-- a member's clashing seeds, among its seeds, are at most the share that the planner prices at
  the cube of the member's place in o -/
  clash : ∀ a,
    (z.sw.d.N.om a).Z.err * allSeeds s.cardE (o.get (idx a)).cubeBits ^ s.samples ≤
      clashSeeds s.cardE (o.get (idx a)).cubeBits ^ s.samples *
        Fintype.card (z.sw.d.N.om a).Z.D
  /-- a member's list bound is at most the planner's list size at the member's place in o -/
  lists : ∀ a, z.sw.d.L a ≤ largestList s (o.get (idx a)).groups
  /-- the group before is priced under the rule johnson -/
  rule : g.rule = .johnson
  /-- its main code's count has the source johnson -/
  source : (analysisOfM s g).mainAt.source = .johnson
  /-- and is not marked bad -/
  counted : (analysisOfM s g).mainAt.count.bad = false
  /-- the block's radius is at least the upper radius of the group before -/
  radius : upperRadiusTest s g z.sw.e = true

variable {z}

/-- **The error of the plan's round SEND seed covers the block's first error.** -/
theorem sendLoc_seed_covers {s : Setting} {o : List SampleSize} {g : GroupSize}
    {idx : z.sw.d.N.O ≃ Fin o.length} (h : SendLocPrices z s o g idx) (c : Scope) (roots : ℕ)
    (hg : (sendSeed s o roots).Good s c) :
    ((ldSendFamErr z.sw.d.N z.sw.d.Sd z.sw.d.L : ℕ) : ℝ) / ((Fintype.card z.sw.d.Sd.D : ℕ) : ℝ) ≤
      ((((sendSeed s o roots).round s c).error.val : ℚ) : ℝ) := by
  have hD0 : 0 < Fintype.card z.sw.d.Sd.D := Fintype.card_pos
  have h1 : ((ldSendFamErr z.sw.d.N z.sw.d.Sd z.sw.d.L : ℕ) : ℝ) /
      ((Fintype.card z.sw.d.Sd.D : ℕ) : ℝ) ≤
        ∑ a, clashShare s (z.sw.d.L a) (o.get (idx a)) := by
    unfold ldSendFamErr
    rw [Nat.cast_sum, Finset.sum_div]
    exact Finset.sum_le_sum fun a _ =>
      member_le (h.marginals a) hD0 (Nat.pow_pos (allSeeds_pos h.field _)) (h.clash a)
  have h2 : ∑ a, clashShare s (z.sw.d.L a) (o.get (idx a)) =
      ∑ i, clashShare s (z.sw.d.L (idx.symm i)) (o.get i) := by
    rw [← Equiv.sum_comp idx]
    simp
  have h3 := send_many_le s h.field o (fun i => z.sw.d.L (idx.symm i))
    (fun i => by simpa using h.lists (idx.symm i))
  exact said_covers (enclR_of_encl (encl_sampleSum s o (encl_ofWord 0))) (by positivity)
    (h1.trans (h2.le.trans h3)) hg

/-- **The error of the plan's round LOC covers the block's second error.** -/
theorem sendLoc_loc_covers {s : Setting} {o : List SampleSize} {g : GroupSize}
    {idx : z.sw.d.N.O ≃ Fin o.length} (h : SendLocPrices z s o g idx) (c : Scope) (b r a : ℕ)
    (hP : Nonempty (z.sw.P ≃ Fin (2 ^ g.main.logN))) (ht : z.sw.t = baseCount s c g)
    (hg : (locRound s c g b r a).Good s c) :
    (((Fintype.card z.sw.P - z.sw.e - 1) ^ z.sw.t : ℕ) : ℝ) /
        ((Fintype.card (Fin z.sw.t → z.sw.P) : ℕ) : ℝ) ≤
      ((((locRound s c g b r a).round s c).error.val : ℚ) : ℝ) := by
  obtain ⟨eP⟩ := hP
  have hn : Fintype.card z.sw.P = (wordOf g.main).n := by
    rw [Fintype.card_congr eP, Fintype.card_fin]
    rfl
  obtain ⟨a1, d1, -⟩ := analysisOfM_main h.source h.counted
  obtain ⟨gp, hu⟩ := upperRadius_of_test h.radius
  have hpos : (0 : ℝ) < ((wordOf g.main).n : ℝ) := by
    have : 0 < (wordOf g.main).n := by unfold Word.n; positivity
    exact_mod_cast this
  have hle := agree_of_upperRadius d1 gp hu (agreeAt_nonneg _ _ _)
  have key : (((Fintype.card z.sw.P - z.sw.e - 1) ^ z.sw.t : ℕ) : ℝ) /
      ((Fintype.card (Fin z.sw.t → z.sw.P) : ℕ) : ℝ) =
        ((((wordOf g.main).n - z.sw.e - 1 : ℕ) : ℝ) / ((wordOf g.main).n : ℝ)) ^ z.sw.t := by
    rw [Fintype.card_fun, Fintype.card_fin, hn, div_pow]
    push_cast
    rfl
  have hb : ((((wordOf g.main).n - z.sw.e - 1 : ℕ) : ℝ) / ((wordOf g.main).n : ℝ)) ^ z.sw.t ≤
      groupAgree s g ^ z.sw.t :=
    pow_le_pow_left₀ (by positivity) ((div_le_iff₀ hpos).mpr hle) _
  unfold locRound at hg ⊢
  rw [← ht, analysis_johnson h.rule] at hg ⊢
  rw [key]
  exact said_covers (enclR_pow a1 z.sw.t) (by positivity) hb hg

/-- **Both**, of the block's own lists of errors and of numbers of values of the verifier's
messages, round by round. -/
theorem sendLoc_covers {s : Setting} {o : List SampleSize} {g : GroupSize}
    {idx : z.sw.d.N.O ≃ Fin o.length} (h : SendLocPrices z s o g idx) (c : Scope) (roots : ℕ)
    (hf : SendLocFits z s.samples (largestCube o) (s.samples * o.length) (baseCount s c g)
      g.main.logN)
    (b r a : ℕ) (hg1 : (sendSeed s o roots).Good s c) (hg2 : (locRound s c g b r a).Good s c) :
    List.Forall₂
      (fun (x : ℕ × ℕ) (ρ : PlanRound) => (x.1 : ℝ) / (x.2 : ℝ) ≤ ((ρ.error.val : ℚ) : ℝ))
      ((Err.toList (Cb.Pv.SendLocRide.eps z)).zip (Shape.chalList (Cb.Pv.SendLocRide.R z).shape))
      [(sendSeed s o roots).round s c, (locRound s c g b r a).round s c] := by
  rw [Cb.Pv.SendLocRide.errs, Cb.Pv.SendLocRide.vals]
  exact List.Forall₂.cons (sendLoc_seed_covers h c roots hg1)
    (List.Forall₂.cons (sendLoc_loc_covers h c b r a hf.positions.2 hf.positions.1 hg2)
      List.Forall₂.nil)

end OnBytes.Tie.Pv.Switch
