-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Port6.lean: the kind's law in the library's own terms, with no letter left but
the radii and the words sent: under one Boolean on the plan, the seeds of a place at which some
sampled message's word has a collision in its list are few, by the library's own count; and behind
a yes of the sending's decision at any other seed, at most one message of each word's list meets the
rows laid.

Main names: clash_port; unique_port'; shapeAt, seedAt, condPort, BadPort, errPort; cond_tie;
badPort_count; behind_row; unique_behind_port.
The lists' bound and the evading samples are the library's (Johnson/Pack/Buys.lean: allMeet_buys;
Cb/Ld/LdSigProofs.lean: sig_cnt_clash).

What is not claimed. One answer a message. The radii are arguments: which radius a later test of
proximity has is not said. That a message is in the list of the word sent is a premise of the last
theorem. From a hash's blocks to seeds: not here. Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.PortTries
import Johnson.Desc.K1.Law.RowsOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack Cb Cb.Ood Prob

variable {L : Type}

/-- **The seeds with a collision in a word's list are few**: the library's count, at the library's
bound on the list, under the library's test on numbers. -/
theorem clash_port (cs : Codes) (s : OracleShape) (e : Nat) (h : meetsB cs s e = true)
    (f : (portOmZ cs s e).Str) :
    cnt ((portOmZ cs s e).Clash f) ≤ (lOf cs s e).choose 2 * (portZ cs s).err := by
  have B := allMeet_buys cs [(s, e)] (by simp [allMeet, h])
  exact (Cb.sig_cnt_clash GE _ _ (B.list ⟨0, Nat.one_pos⟩) (B.evades ⟨0, Nat.one_pos⟩) f).1

/-- unique_port, at codes and a shape that are named. -/
theorem unique_port' (S : Statement) (o : Nat) (x : OnBytes.Oracle) (hx : S.oracles[o]? = some x)
    (cs : Codes) (s : OracleShape) (hc : S.codes = cs) (hs : x.shape = s) (h : Tie cs s) (e : Nat)
    (f : (portOmZ cs s e).Str) (z : List E) (β y : E) (ρ : (Fin (bitsZ cs s) → GE) × GEˣ)
    (r : ReadsOne cs s z β ρ) (hno : ¬ (portOmZ cs s e).Clash f ρ) (w w' : Means.Words GE)
    (msg msg' : (portCode cs s).J → GE) (hw : w o = tabOf cs s msg) (hw' : w' o = tabOf cs s msg')
    (hl : (portOmZ cs s e).InList f msg) (hl' : (portOmZ cs s e).InList f msg')
    (hs1 : Means.Says rdE S (sampleRow (Msg.of cs s) o z β 0 y) w)
    (hs2 : Means.Says rdE S (sampleRow (Msg.of cs s) o z β 0 y) w') : msg = msg' := by
  subst hc hs
  exact unique_port S o x hx h e f z β y ρ r hno w w' msg msg' hw hw' hl hl' hs1 hs2

/-! ## A place -/

/-- The shape of the place's message number k. -/
def shapeAt (P : Par) (k : Fin (shapesOf P).length) : OracleShape := (shapesOf P)[k.val]

/-- The seed that a message with one answer and b coordinates reads of the joint seeds. -/
def seedAt (P : Par) (b : Nat) (ρ : Seeds P) : (Fin b → GE) × GEˣ := ownSeeds 1 b ρ 0

/-- **The condition, as one Boolean on the plan and the radii.** rad n: the radius of the place's
message number n among all that it sends, sampled or not. lengthsOk: every code's message length ell
is a power of two. -/
def condPort (P : Par) (rad : Nat → Nat) : Bool :=
  planOkOwn P && P.codes.lengthsOk &&
    decide (∀ k, sampledAt P k → meetsB P.codes (shapeAt P k) (rad k.val) = true)

/-- The bad seeds: some sampled message's word has a collision in its list. -/
def BadPort (P : Par) (rad : Nat → Nat)
    (f : ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str) (ρ : Seeds P) : Prop :=
  ∃ k, sampledAt P k ∧ (portOmZ P.codes (shapeAt P k) (rad k.val)).Clash (f k)
    (seedAt P (bitsZ P.codes (shapeAt P k)) ρ)

/-- Their number is at most this. -/
noncomputable def errPort (P : Par) (rad : Nat → Nat) : Nat :=
  ∑ k : Fin (shapesOf P).length, if sampledAt P k then
    (lOf P.codes (shapeAt P k) (rad k.val)).choose 2 * (portZ P.codes (shapeAt P k)).err *
      Fintype.card (Rest GE GEˣ P.seeds 1 P.coordinates (bitsZ P.codes (shapeAt P k)))
  else 0

theorem cond_parts (P : Par) (rad : Nat → Nat) (h : condPort P rad = true) :
    planOkOwn P = true ∧ P.codes.lengthsOk = true ∧
      ∀ k, sampledAt P k → meetsB P.codes (shapeAt P k) (rad k.val) = true := by
  simp only [condPort, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem plan_shape (P : Par) (hB : planOkOwn P = true) (k : Fin (shapesOf P).length) :
    Blk.shapeOk P.codes (shapeAt P k) = true := by
  simp only [planOkOwn, planOk, Bool.and_eq_true] at hB
  have hmem : (shapesOf P)[k.val] ∈ shapesOf P := List.getElem_mem k.isLt
  obtain ⟨nn, hn, hnn⟩ := List.mem_map.1 hmem
  have := Array.all_eq_true_iff_forall_mem.1 hB.1.1.1 nn (Array.mem_toList_iff.1 hn)
  rw [hnn] at this
  exact this

/-- Under the condition every sampled message has the premises of the tie. -/
theorem cond_tie (P : Par) (rad : Nat → Nat) (h : condPort P rad = true)
    (k : Fin (shapesOf P).length) (hk : sampledAt P k) : Tie P.codes (shapeAt P k) := by
  obtain ⟨h1, h2, h3⟩ := cond_parts P rad h
  have hm := h3 k hk
  simp only [meetsB, Bool.and_eq_true, decide_eq_true_eq] at hm
  exact ⟨hm.1.1.1.1.2, h2, plan_shape P h1 k, (plan_msg P h1 k hk).2⟩

theorem bits_le_coordinates (P : Par) (k : Fin (shapesOf P).length) (hk : sampledAt P k) :
    bitsZ P.codes (shapeAt P k) ≤ P.coordinates := by
  rw [← v_bitsZ]
  exact msgAt_v_le P k hk

theorem one_le_seeds (P : Par) (k : Fin (shapesOf P).length) (hk : sampledAt P k) :
    1 ≤ P.seeds :=
  Nat.le_trans (Nat.pos_of_ne_zero hk) (msgAt_answers_le P k)

/-- **The bad seeds are few.** -/
theorem badPort_count (P : Par) (rad : Nat → Nat) (h : condPort P rad = true)
    (f : ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str) :
    cnt (BadPort P rad f) ≤ errPort P rad := by
  unfold BadPort errPort
  refine Nat.le_trans (cnt_exists_le _) (Finset.sum_le_sum fun k _ => ?_)
  by_cases hk : sampledAt P k
  · rw [if_pos hk]
    have e : (fun ρ : Seeds P => sampledAt P k ∧
        (portOmZ P.codes (shapeAt P k) (rad k.val)).Clash (f k)
          (seedAt P (bitsZ P.codes (shapeAt P k)) ρ)) =
        fun ρ : Seeds P => (fun g : Fin 1 → (Fin (bitsZ P.codes (shapeAt P k)) → GE) × GEˣ =>
          (portOmZ P.codes (shapeAt P k) (rad k.val)).Clash (f k) (g 0))
          (partSeeds P.seeds 1 P.coordinates (bitsZ P.codes (shapeAt P k)) (one_le_seeds P k hk)
            (bits_le_coordinates P k hk) ρ).1 := by
      funext ρ
      unfold seedAt
      rw [ownSeeds_eq _ _ (one_le_seeds P k hk) (bits_le_coordinates P k hk)]
      exact propext ⟨fun c => c.2, fun c => ⟨hk, c⟩⟩
    rw [e]
    refine Nat.le_trans (Nat.le_of_eq (cnt_part P.seeds 1 P.coordinates
      (bitsZ P.codes (shapeAt P k)) (one_le_seeds P k hk) (bits_le_coordinates P k hk)
      fun g : Fin 1 → (Fin (bitsZ P.codes (shapeAt P k)) → GE) × GEˣ =>
        (portOmZ P.codes (shapeAt P k) (rad k.val)).Clash (f k) (g 0))) ?_
    refine Nat.mul_le_mul_right _ ?_
    have e2 := cnt_equiv (Equiv.funUnique (Fin 1)
      ((Fin (bitsZ P.codes (shapeAt P k)) → GE) × GEˣ))
      ((portOmZ P.codes (shapeAt P k) (rad k.val)).Clash (f k))
    exact Nat.le_trans (Nat.le_of_eq e2) (clash_port _ _ _ ((cond_parts P rad h).2.2 k hk) (f k))
  · rw [if_neg hk]
    exact Nat.le_of_eq (cnt_false fun ρ c => hk c.1)

/-! ## Behind a yes -/

/-- Behind a yes, of a sampled message: it stands in the statement, marked, under the plan's codes
and its own shape; and for each of its answers the row at that answer's seed is among its sample
rows. -/
theorem behind_row (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array Nat) (hfit : roundsFit (rounds P) [r₁, r₂] = true)
    (hyes : decideSend P owed d [r₁, r₂] = .ok (ids, d')) (k : Fin (shapesOf P).length)
    (hk : sampledAt P k) :
    d'.st.codes = P.codes ∧ ∃ x, d'.st.oracles[d.st.oracles.size + k.val]? = some x ∧
      x.sampled = true ∧ x.shape = shapeAt P k ∧
      ∀ (i : Nat) (sd : List E × E), i < (shapeAt P k).answers → (seedsOf P r₁)[i]? = some sd →
        sd.1.length = P.coordinates ∧ ∃ y, sampleRow (Msg.of P.codes (shapeAt P k))
          (d.st.oracles.size + k.val) sd.1 sd.2 i y ∈ x.sampleRows.toList := by
  obtain ⟨⟨_, hc, _, _, hf⟩, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 hyes
  obtain ⟨ys', hy, hget⟩ := outs_spec P.codes (seedsOf P r₁) P.seeds (shapesOf P)
    d.st.oracles.size (answersIn r₂) hf k.val k.isLt
  have hk' : (shapesOf P)[k.val].answers ≠ 0 := hk
  have hx : (behind P d (seedsOf P r₁) (answersIn r₂)).st.oracles[d.st.oracles.size + k.val]? =
      some (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k.val) (shapesOf P)[k.val] ys') := by
    show (d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
      (answersIn r₂)).toArray[d.st.oracles.size + k.val]? = _
    rw [List.getElem?_toArray, List.getElem?_append_right (by simp)]
    simpa using hget
  refine ⟨hc, _, hx, by simp [wr, hk'], ?_, fun i sd hi hsd => ?_⟩
  · unfold wr
    split <;> rfl
  · refine ⟨cutSeeds_get _ _ _ _ sd (draw_len P r₁ r₂ hfit) hsd, ?_⟩
    obtain ⟨y, hyi⟩ : ∃ y, ys'[i]? = some y :=
      ⟨ys'[i]'(Nat.lt_of_lt_of_le hi hy), List.getElem?_eq_getElem _⟩
    refine ⟨y, ?_⟩
    have hrows : (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k.val) (shapesOf P)[k.val]
        ys').sampleRows = rowsOf P.codes (seedsOf P r₁) (d.st.oracles.size + k.val)
          (shapesOf P)[k.val] ys' := by simp [wr, hk']
    rw [hrows]
    exact rowsOf_mem P.codes (seedsOf P r₁) _ (shapesOf P)[k.val] ys' i hi sd y hsd hyi

/-- **Behind a yes at a seed that is not bad: of each sampled message's word's list at most one
message meets the rows laid on the message.** -/
theorem unique_behind_port (P : Par) (rad : Nat → Nat)
    (f : ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str) (owed : Option Nat)
    (d d' : DState L) (r₁ r₂ : Fmt.RoundView) (ids : Array Nat) (hC : condPort P rad = true)
    (hfit : roundsFit (rounds P) [r₁, r₂] = true)
    (hyes : decideSend P owed d [r₁, r₂] = .ok (ids, d')) (ρ : Seeds P) (hρ : ReadsAs P r₁ ρ)
    (hgood : ¬ BadPort P rad f ρ) (k : Fin (shapesOf P).length) (hk : sampledAt P k)
    (w w' : Means.Words GE) (msg msg' : (portCode P.codes (shapeAt P k)).J → GE)
    (hw : w (d.st.oracles.size + k.val) = tabOf P.codes (shapeAt P k) msg)
    (hw' : w' (d.st.oracles.size + k.val) = tabOf P.codes (shapeAt P k) msg')
    (hl : (portOmZ P.codes (shapeAt P k) (rad k.val)).InList (f k) msg)
    (hl' : (portOmZ P.codes (shapeAt P k) (rad k.val)).InList (f k) msg') :
    ∃ x, d'.st.oracles[d.st.oracles.size + k.val]? = some x ∧ x.sampled = true ∧
      (Means.AllSay rdE d'.st x.sampleRows.toList w →
        Means.AllSay rdE d'.st x.sampleRows.toList w' → msg = msg') := by
  obtain ⟨hc, x, hx, hs, hsh, hrow⟩ := behind_row P owed d d' r₁ r₂ ids hfit hyes k hk
  refine ⟨x, hx, hs, fun a b => ?_⟩
  have hT := cond_tie P rad hC k hk
  have h1 : 0 < P.seeds := one_le_seeds P k hk
  obtain ⟨sd, hsd, hz, hβ⟩ := hρ ⟨0, h1⟩
  obtain ⟨hlen, y, hmem⟩ := hrow 0 sd (by rw [hT.one]; exact Nat.one_pos) hsd
  have hb := bits_le_coordinates P k hk
  have e3 : seedAt P (bitsZ P.codes (shapeAt P k)) ρ =
      (fun t => pointOf (ρ ⟨0, h1⟩).1 t.val, (ρ ⟨0, h1⟩).2) := by
    unfold seedAt ownSeeds
    exact dif_pos h1
  have r : ReadsOne P.codes (shapeAt P k) sd.1 sd.2
      (seedAt P (bitsZ P.codes (shapeAt P k)) ρ) := by
    rw [e3]
    refine ⟨by rw [hlen]; exact hb, fun t => ?_, hβ⟩
    have ht : t.val < P.coordinates := Nat.lt_of_lt_of_le t.isLt hb
    show readL sd.1 t.val = pointOf (ρ ⟨0, h1⟩).1 t.val
    unfold pointOf
    rw [dif_pos ht]
    exact hz ⟨t.val, ht⟩
  exact unique_port' d'.st _ x hx P.codes (shapeAt P k) hc hsh hT (rad k.val) (f k) sd.1 sd.2 y _ r
    (fun c => hgood ⟨k, hk, c⟩) w w' msg msg' hw hw' hl hl' (a _ hmem) (b _ hmem)

end VerifiableInference.Desc.K1
