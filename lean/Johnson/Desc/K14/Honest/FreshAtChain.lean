--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/FreshAtChain.lean: fresh_sent (Johnson/Desc/K14/Honest/FreshAt.lean) at the
shared chain's own "send o_omega", for every shape that splits and meets SpShape; joins of its
triple: to any coins that agree with the row below the lengths, to what the shared sending writes,
and to the left side of the verifier's own constraint at "SPLIT"; and send_enc, called at the second
message, at free rows and a free position.

  SpShape         the six premises of fresh_sent on the codes and the shape alone, as one
                  proposition
  FreshLaw        the conclusion of fresh_sent, as a proposition of a function from o_sp's coins to
                  a triple
  fresh_sent_shape   fresh_sent, CALLED from SpShape
  parO_two, parO_omega, parO_split, sent_split   at a shape that splits, the chain's own parameters
                  of "send o_omega" (parO, Johnson/Desc/K14/Law/LedgerRow.lean) have two messages,
                  of o_omega's and of o_sp's shape; the statement that has received them has an
                  entry of o_sp's shape at the second new number
  fresh_chain     **fresh_sent there**: Q is parO P, T the statement T₀ with these messages
                  received, first the number of T₀'s messages. Of fresh_sent's premises stay:
                  SpShape, the set's size, and the two on the seed. New premises: the shape splits,
                  and T₀ has the codes. The verifier's own test on that message
                  (splitMessageFits, Johnson/Desc/Own/Lin.lean) is wider than SpShape
  held_mask, mu_at   the held mask table and the scalar at ANY coins of o_sp
  spTripleAt, spTripleAt_agree, fresh_agree   the triple, and the statement, at any family of coins
                  that agrees with the row below n + 1 and with the tail below r: what stands beyond
                  these lengths is not read
  maskRowZ, spCoinsZ, fresh_zero   so at the row that holds 0 beyond its n + 1 entries, as the
                  shared sending asks of its caller
  fresh_chain_zero   both at once: that row, at the chain's own parameters
  spTriple_written, spTriple_answer   the triple's first two components are what the shared sending
                  writes (sp_written, sp_answer), if its parameters have the codes
  sp_read         send_enc (Johnson/Prover/Send/Enc.lean), called at the second message, at free
                  rows and a free position: the cut of a leaf by the IOP as written in Lean, at the
                  written column, reads as the symbol. It is not stated at the triple
  muVal_sent, spTriple_muVal   muVal_formula (Johnson/Desc/K14/Honest/SplitValue.lean) and mu_chain
                  (Johnson/Desc/K14/Honest/SendHeld.lean), called: at the tables of the two sendings
                  the left side of the verifier's constraint at "SPLIT" is the scalar muSent, so the
                  triple's component at kappa

HOW FAR IT REACHES. As FreshAt.lean's head says: one row, one pad, one answer; z_fd, the seed and
the set of positions are fixed parameters bound outside the distribution. T₀, the words in front,
psi_lo and the folded row are free parameters: that they are a run's own is not said here.

What is not claimed. That an honest prover samples the coins uniformly. That kappa is the entry that
the verifier takes at "SPLIT". That any honest prover written in Lean lays these rows. How many
positions a run reads. Nothing on roots and paths, on any other value that is shown, or on a
verifier's view. No property of a protocol is claimed.

-/
import Johnson.Desc.K14.Honest.FreshAt
import Johnson.Desc.K14.Honest.SendHeld
import Johnson.Desc.K14.Honest.SplitValue
import Johnson.Desc.K14.Law.LedgerRow
import Johnson.Desc.K14.Law.PlanShapes
import Johnson.Prover.Send.Enc
import OnBytes.Slice.BlkStLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)
open VerifiableInference.Desc (K1.Msg K1.Msg.of K1.sampleRow)
open Johnson.Prover.Link (symG symG_congr words3)
open Johnson.Prover.Send (Rows shapeAt held)
open Desc.K14.Law (parO)

/-! ## fresh_sent, called from its public premises -/

/-- **The six premises of fresh_sent on the codes and the shape alone.** -/
structure SpShape (codes : Codes) (Sh : LinShape) (n : ℕ) : Prop where
  length : (spSymCode codes Sh).l = n + 1
  power : 2 ^ (codes.mask.getD Sh.sharedSplit.maskCode default).logEll = (spSymCode codes Sh).l
  positions : (spSymCode codes Sh).a ≤ 32
  noMain : Sh.sharedSplit.mainRows = 0
  oneRow : Sh.sharedSplit.maskRows = 1
  oneAnswer : Sh.sharedSplit.answers = 1

/-- **The conclusion of fresh_sent, as a proposition**, of a function tr from o_sp's coins to a
triple: over uniform coins, whatever is made of tr has the distribution of the same made of a
uniform triple. -/
def FreshLaw (r n : ℕ) {a : ℕ} (S : Finset (Fin (2 ^ a)))
    (tr : (Fin r → GE) × GE × (Fin n → GE) → (S → GE) × GE × (Fin n → GE)) : Prop :=
  ∀ (γ : Type) (f : (S → GE) × GE × (Fin n → GE) → γ),
    (Prob.unif ((Fin r → GE) × GE × (Fin n → GE))).map (fun x => f (tr x)) =
      (Prob.unif ((S → GE) × GE × (Fin n → GE))).map f

/-- **fresh_sent, CALLED from SpShape**: so this file stops compiling if the premises of fresh_sent
change. -/
theorem fresh_sent_shape (codes : Codes) (Sh : LinShape) (n : ℕ) (H : SpShape codes Sh n)
    (Q : VerifiableInference.Desc.K1.Par) (first : ℕ) (w₀ : Words GE) (psiLo zfd : List GE)
    (u : ℕ → GE) (cOmega : MsgCoins) (S : Finset (Fin (2 ^ (spSymCode codes Sh).a)))
    (hS : S.card ≤ (spSymCode codes Sh).r) (T : Statement) (X : OnBytes.Oracle)
    (hX : T.oracles[first + 1]? = some X) (hXs : X.shape = Sh.sharedSplit) (hT : T.codes = codes)
    (h2 : 1 < Q.sent.size) (hQ : shapeAt Q 1 = Sh.sharedSplit) (z : List E) (β y : E)
    (hz : (K1.Msg.of codes Sh.sharedSplit).v ≤ z.length) (hβ : readE β ≠ 0) (kappa : Fin n) :
    FreshLaw (spSymCode codes Sh).r n S
      (spTriple codes Sh Q first w₀ psiLo zfd u cOmega n S T z β y kappa) :=
  fun _ f => fresh_sent codes Sh Q first w₀ psiLo zfd u cOmega n H.length H.power H.positions
    H.noMain H.oneRow H.oneAnswer S hS T X hX hXs hT h2 hQ z β y hz hβ kappa f

/-! ## The chain's own "send o_omega" at a shape that splits -/

theorem parO_two (P : P14) (hs : P.S.sharedSplitNeeded = true) : 1 < (parO P).sent.size := by
  rw [Law.parK1_sent, Law.withOmega_split hs]
  exact Nat.one_lt_two

theorem parO_omega (P : P14) (hs : P.S.sharedSplitNeeded = true) :
    shapeAt (parO P) 0 = P.S.omega := by
  unfold shapeAt
  rw [Law.parK1_sent, Law.withOmega_split hs]
  rfl

theorem parO_split (P : P14) (hs : P.S.sharedSplitNeeded = true) :
    shapeAt (parO P) 1 = P.S.sharedSplit := by
  unfold shapeAt
  rw [Law.parK1_sent, Law.withOmega_split hs]
  rfl

/-- The statement that has received the two messages has o_sp's shape at the second new number. -/
theorem sent_split (P : P14) (hs : P.S.sharedSplitNeeded = true) (T₀ : Statement) :
    (stSent T₀ (parO P).sent).oracles[T₀.oracles.size + 1]? =
      some { shape := P.S.sharedSplit } := by
  rw [stSent_new, Law.parK1_sent, Law.withOmega_split hs]
  rfl

/-- **fresh_sent at the chain's own "send o_omega", for every shape that splits and meets SpShape.**
-/
theorem fresh_chain (P : P14) (n : ℕ) (H : SpShape P.codes P.S n)
    (hs : P.S.sharedSplitNeeded = true) (T₀ : Statement) (hT₀ : T₀.codes = P.codes)
    (w₀ : Words GE) (psiLo zfd : List GE) (u : ℕ → GE) (cOmega : MsgCoins)
    (S : Finset (Fin (2 ^ (spSymCode P.codes P.S).a))) (hS : S.card ≤ (spSymCode P.codes P.S).r)
    (z : List E) (β y : E) (hz : (K1.Msg.of P.codes P.S.sharedSplit).v ≤ z.length)
    (hβ : readE β ≠ 0) (kappa : Fin n) :
    FreshLaw (spSymCode P.codes P.S).r n S
      (spTriple P.codes P.S (parO P) T₀.oracles.size w₀ psiLo zfd u cOmega n S
        (stSent T₀ (parO P).sent) z β y kappa) :=
  fresh_sent_shape P.codes P.S n H (parO P) T₀.oracles.size w₀ psiLo zfd u cOmega S hS
    (stSent T₀ (parO P).sent) { shape := P.S.sharedSplit } (sent_split P hs T₀) rfl hT₀
    (parO_two P hs) (parO_split P hs) z β y hz hβ kappa

/-! ## Any coins that agree below the lengths -/

/-- The held mask table of the second message of "send o_omega", at any coins of o_sp. -/
theorem held_mask (codes : Codes) (Sh : LinShape) (Q : VerifiableInference.Desc.K1.Par) (first : ℕ)
    (w₀ : Words GE) (psiLo : List GE) (u : ℕ → GE) (cOmega cSp : MsgCoins) (h2 : 1 < Q.sent.size)
    (hm : (shapeAt Q 1).maskRows = 1) (j : ℕ) :
    held w₀ first Q (sendsOmega codes Sh psiLo u cOmega cSp) (first + 1) .mask j =
      cSp.mask 0 j := by
  rw [Johnson.Prover.Send.held_new w₀ first Q _ 1 h2]
  have h := Johnson.Prover.Send.word_mask (sendsOmega codes Sh psiLo u cOmega cSp 1) (shapeAt Q 1) 0
    j (by rw [hm]; exact Nat.one_pos)
  have e : 0 + j * 2 ^ VerifiableInference.Desc.K1.clog (shapeAt Q 1).maskRows = j := by
    rw [hm]
    have : VerifiableInference.Desc.K1.clog 1 = 0 := rfl
    rw [this, Nat.pow_zero, Nat.mul_one, Nat.zero_add]
  rw [e] at h
  rw [h]
  rfl

/-- The scalar at any coins of o_sp: omega_col at z_fd, plus the row's entry kappa. -/
theorem mu_at (Sh : LinShape) (psiLo z : List GE) (u : ℕ → GE) (cSp : MsgCoins)
    (hm : Sh.sharedSplit.maskRows = 1) (kappa : ℕ) :
    muSent Sh psiLo z u cSp kappa =
      (∑ j ∈ Finset.range Sh.matrixRows, Law.eqK z j * omegaHon Sh psiLo u j) +
        cSp.mask 0 kappa := by
  unfold muSent muHon kappaOf
  rw [hm]
  have e1 : kappa / 2 ^ ceilLog2 1 = kappa := by
    have : ceilLog2 1 = 0 := rfl
    rw [this, Nat.pow_zero, Nat.div_one]
  have e2 : kappa % 2 ^ ceilLog2 1 = 0 := by
    have : ceilLog2 1 = 0 := rfl
    rw [this, Nat.pow_zero, Nat.mod_one]
  rw [e1, e2]

/-- The triple of FreshAt.lean's spTriple, at any coins cSp of o_sp. -/
def spTripleAt (codes : Codes) (Sh : LinShape) (Q : VerifiableInference.Desc.K1.Par) (first : ℕ)
    (w₀ : Words GE) (psiLo zfd : List GE) (u : ℕ → GE) (cOmega : MsgCoins) (n : ℕ)
    (S : Finset (Fin (2 ^ (spSymCode codes Sh).a))) (T : Statement) (z : List E) (β y : E)
    (kappa : Fin n) (cSp : MsgCoins) : (S → GE) × GE × (Fin n → GE) :=
  (fun j => symG (spSymCode codes Sh) j.1.val
      ((sendsOmega codes Sh psiLo u cOmega cSp 1).mask 0)
      ((sendsOmega codes Sh psiLo u cOmega cSp 1).maskTl 0),
    Means.value rdE T (K1.sampleRow (K1.Msg.of codes Sh.sharedSplit) (first + 1) z β 0 y)
      (held w₀ first Q (sendsOmega codes Sh psiLo u cOmega cSp)),
    fun i => if i = kappa then muSent Sh psiLo zfd u cSp kappa.val else cSp.mask 0 i.val)

/-- **What stands beyond the lengths is not read**: coins that agree with the row below n + 1 and
with the tail below r give the triple of spTriple. -/
theorem spTripleAt_agree (codes : Codes) (Sh : LinShape) (Q : VerifiableInference.Desc.K1.Par)
    (first : ℕ) (w₀ : Words GE) (psiLo zfd : List GE) (u : ℕ → GE) (cOmega : MsgCoins) (n : ℕ)
    (H : SpShape codes Sh n) (S : Finset (Fin (2 ^ (spSymCode codes Sh).a))) (T : Statement)
    (X : OnBytes.Oracle) (hX : T.oracles[first + 1]? = some X) (hXs : X.shape = Sh.sharedSplit)
    (hT : T.codes = codes) (h2 : 1 < Q.sent.size) (hQ : shapeAt Q 1 = Sh.sharedSplit) (z : List E)
    (β y : E) (hz : (K1.Msg.of codes Sh.sharedSplit).v ≤ z.length) (kappa : Fin n)
    (x : (Fin (spSymCode codes Sh).r → GE) × GE × (Fin n → GE)) (cSp : MsgCoins)
    (hrow : ∀ j, j < n + 1 → cSp.mask 0 j = maskRowOf n x.2.1 x.2.2 j)
    (htail : ∀ q, q < (spSymCode codes Sh).r →
      cSp.maskTail 0 q = maskTailOf (spSymCode codes Sh).r x.1 q) :
    spTripleAt codes Sh Q first w₀ psiLo zfd u cOmega n S T z β y kappa cSp =
      spTriple codes Sh Q first w₀ psiLo zfd u cOmega n S T z β y kappa x := by
  have hmQ : (shapeAt Q 1).maskRows = 1 := by rw [hQ]; exact H.oneRow
  have e : K1.Msg.of T.codes X.shape = K1.Msg.of codes Sh.sharedSplit := by rw [hT, hXs]
  have hne : ((K1.Msg.of T.codes X.shape).K != 0 || (K1.Msg.of T.codes X.shape).Kzk != 0) =
      true := by
    rw [e]
    have : (K1.Msg.of codes Sh.sharedSplit).Kzk = 1 := H.oneRow
    simp [this]
  have val : ∀ c : MsgCoins, (∀ j, j < n + 1 → c.mask 0 j = maskRowOf n x.2.1 x.2.2 j) →
      Means.value rdE T (K1.sampleRow (K1.Msg.of codes Sh.sharedSplit) (first + 1) z β 0 y)
        (held w₀ first Q (sendsOmega codes Sh psiLo u cOmega c)) =
      readE β * x.2.1 + ∑ i : Fin n,
        (K1.Msg.of codes Sh.sharedSplit).weight (readL z) (readE β) 0 .mask i.val * x.2.2 i := by
    intro c hc
    have h1 := sampleValue_form T (first + 1) X hX z β 0 y
      (held w₀ first Q (sendsOmega codes Sh psiLo u cOmega c)) hne (by rw [e]; exact hz)
    rw [e] at h1
    rw [h1]
    exact answer_form _ n (readL z) (readE β) H.noMain H.oneRow H.oneAnswer
      (H.power.trans H.length) x.2.1 x.2.2 _ fun j hj => by
        rw [held_mask codes Sh Q first w₀ psiLo u cOmega c h2 hmQ j]
        exact hc j hj
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext j
    exact symG_congr _ _ _ _ _ _ (fun i hi => hrow i (by rw [← H.length]; exact hi)) htail
  · show Means.value rdE T _ _ = Means.value rdE T _ _
    rw [val cSp hrow, val (spCoins (spSymCode codes Sh).r n x) fun _ _ => rfl]
  · funext i
    show (if i = kappa then _ else _) = (if i = kappa then _ else _)
    have hi : cSp.mask 0 i.val = x.2.2 i := by
      rw [hrow i.val (Nat.lt_succ_of_lt i.isLt)]
      unfold maskRowOf
      rw [dif_pos i.isLt]
    by_cases hk : i = kappa
    · rw [if_pos hk, if_pos hk, mu_at Sh psiLo zfd u cSp H.oneRow,
        mu_form Sh psiLo zfd u _ n x H.oneRow kappa, ← hk, hi]
    · rw [if_neg hk, if_neg hk, hi]

/-- **The statement at any family of coins that agrees below the lengths.** -/
theorem fresh_agree (codes : Codes) (Sh : LinShape) (n : ℕ) (H : SpShape codes Sh n)
    (Q : VerifiableInference.Desc.K1.Par) (first : ℕ) (w₀ : Words GE) (psiLo zfd : List GE)
    (u : ℕ → GE) (cOmega : MsgCoins) (S : Finset (Fin (2 ^ (spSymCode codes Sh).a)))
    (hS : S.card ≤ (spSymCode codes Sh).r) (T : Statement) (X : OnBytes.Oracle)
    (hX : T.oracles[first + 1]? = some X) (hXs : X.shape = Sh.sharedSplit) (hT : T.codes = codes)
    (h2 : 1 < Q.sent.size) (hQ : shapeAt Q 1 = Sh.sharedSplit) (z : List E) (β y : E)
    (hz : (K1.Msg.of codes Sh.sharedSplit).v ≤ z.length) (hβ : readE β ≠ 0) (kappa : Fin n)
    (c : (Fin (spSymCode codes Sh).r → GE) × GE × (Fin n → GE) → MsgCoins)
    (hrow : ∀ x j, j < n + 1 → (c x).mask 0 j = maskRowOf n x.2.1 x.2.2 j)
    (htail : ∀ x q, q < (spSymCode codes Sh).r →
      (c x).maskTail 0 q = maskTailOf (spSymCode codes Sh).r x.1 q) :
    FreshLaw (spSymCode codes Sh).r n S fun x =>
      spTripleAt codes Sh Q first w₀ psiLo zfd u cOmega n S T z β y kappa (c x) := by
  have e : (fun x => spTripleAt codes Sh Q first w₀ psiLo zfd u cOmega n S T z β y kappa (c x)) =
      spTriple codes Sh Q first w₀ psiLo zfd u cOmega n S T z β y kappa := by
    funext x
    exact spTripleAt_agree codes Sh Q first w₀ psiLo zfd u cOmega n H S T X hX hXs hT h2 hQ z β y hz
      kappa x (c x) (hrow x) (htail x)
  rw [e]
  exact fresh_sent_shape codes Sh n H Q first w₀ psiLo zfd u cOmega S hS T X hX hXs hT h2 hQ z β y
    hz hβ kappa

/-- The row that holds 0 beyond its n + 1 entries. -/
def maskRowZ (n : ℕ) (p : GE) (k : Fin n → GE) (j : ℕ) : GE :=
  if h : j < n then k ⟨j, h⟩ else if j = n then p else 0

/-- The coins of the mask message, of (t, p, k), with 0 beyond the row's entries. -/
def spCoinsZ (r n : ℕ) (x : (Fin r → GE) × GE × (Fin n → GE)) : MsgCoins :=
  ⟨fun _ _ => 0, fun _ => 0, fun _ j => maskRowZ n x.2.1 x.2.2 j, fun _ q => maskTailOf r x.1 q⟩

/-- **The statement at the row that holds 0 from its code's message length on.** -/
theorem fresh_zero (codes : Codes) (Sh : LinShape) (n : ℕ) (H : SpShape codes Sh n)
    (Q : VerifiableInference.Desc.K1.Par) (first : ℕ) (w₀ : Words GE) (psiLo zfd : List GE)
    (u : ℕ → GE) (cOmega : MsgCoins) (S : Finset (Fin (2 ^ (spSymCode codes Sh).a)))
    (hS : S.card ≤ (spSymCode codes Sh).r) (T : Statement) (X : OnBytes.Oracle)
    (hX : T.oracles[first + 1]? = some X) (hXs : X.shape = Sh.sharedSplit) (hT : T.codes = codes)
    (h2 : 1 < Q.sent.size) (hQ : shapeAt Q 1 = Sh.sharedSplit) (z : List E) (β y : E)
    (hz : (K1.Msg.of codes Sh.sharedSplit).v ≤ z.length) (hβ : readE β ≠ 0) (kappa : Fin n) :
    FreshLaw (spSymCode codes Sh).r n S fun x =>
      spTripleAt codes Sh Q first w₀ psiLo zfd u cOmega n S T z β y kappa
        (spCoinsZ (spSymCode codes Sh).r n x) :=
  fresh_agree codes Sh n H Q first w₀ psiLo zfd u cOmega S hS T X hX hXs hT h2 hQ z β y hz hβ kappa
    (spCoinsZ (spSymCode codes Sh).r n)
    (fun x j hj => by
      show maskRowZ n x.2.1 x.2.2 j = maskRowOf n x.2.1 x.2.2 j
      unfold maskRowZ maskRowOf
      by_cases h : j < n
      · rw [dif_pos h, dif_pos h]
      · rw [dif_neg h, dif_neg h, if_pos (by omega)])
    (fun _ _ _ => rfl)

/-- **Both at once**: at the chain's own "send o_omega", for every shape that splits and meets
SpShape, at the row that holds 0 from its code's message length on. -/
theorem fresh_chain_zero (P : P14) (n : ℕ) (H : SpShape P.codes P.S n)
    (hs : P.S.sharedSplitNeeded = true) (T₀ : Statement) (hT₀ : T₀.codes = P.codes)
    (w₀ : Words GE) (psiLo zfd : List GE) (u : ℕ → GE) (cOmega : MsgCoins)
    (S : Finset (Fin (2 ^ (spSymCode P.codes P.S).a))) (hS : S.card ≤ (spSymCode P.codes P.S).r)
    (z : List E) (β y : E) (hz : (K1.Msg.of P.codes P.S.sharedSplit).v ≤ z.length)
    (hβ : readE β ≠ 0) (kappa : Fin n) :
    FreshLaw (spSymCode P.codes P.S).r n S fun x =>
      spTripleAt P.codes P.S (parO P) T₀.oracles.size w₀ psiLo zfd u cOmega n S
        (stSent T₀ (parO P).sent) z β y kappa (spCoinsZ (spSymCode P.codes P.S).r n x) :=
  fresh_zero P.codes P.S n H (parO P) T₀.oracles.size w₀ psiLo zfd u cOmega S hS
    (stSent T₀ (parO P).sent) { shape := P.S.sharedSplit } (sent_split P hs T₀) rfl hT₀
    (parO_two P hs) (parO_split P hs) z β y hz hβ kappa

/-! ## What the shared sending writes, and what is read of it -/

/-- The triple's symbols, written, are the mask symbols that the shared sending writes. -/
theorem spTriple_written (codes : Codes) (Sh : LinShape) (Q : VerifiableInference.Desc.K1.Par)
    (first : ℕ) (w₀ : Words GE) (psiLo zfd : List GE) (u : ℕ → GE) (cOmega : MsgCoins) (n : ℕ)
    (S : Finset (Fin (2 ^ (spSymCode codes Sh).a))) (T : Statement) (z : List E) (β y : E)
    (kappa : Fin n) (x : (Fin (spSymCode codes Sh).r → GE) × GE × (Fin n → GE))
    (hQc : Q.codes = codes) (hQ : shapeAt Q 1 = Sh.sharedSplit)
    (hm : Sh.sharedSplit.maskRows = 1) (j : S) :
    Johnson.Prover.Send.maskSyms Q
        (sendsOmega codes Sh psiLo u cOmega (spCoins (spSymCode codes Sh).r n x)) 1 j.1.val =
      words3 (ofE
        ((spTriple codes Sh Q first w₀ psiLo zfd u cOmega n S T z β y kappa x).1 j)) := by
  rw [sp_written codes Sh Q _ j.1.val hQc hQ hm, Nat.mod_eq_of_lt j.1.isLt]
  rfl

/-- The triple's answer, at the target 0, written, stands in the shared sending's list of answers.
-/
theorem spTriple_answer (codes : Codes) (Sh : LinShape) (Q : VerifiableInference.Desc.K1.Par)
    (first : ℕ) (w₀ : Words GE) (psiLo zfd : List GE) (u : ℕ → GE) (cOmega : MsgCoins) (n : ℕ)
    (S : Finset (Fin (2 ^ (spSymCode codes Sh).a))) (T : Statement) (z : List E) (β : E)
    (kappa : Fin n) (x : (Fin (spSymCode codes Sh).r → GE) × GE × (Fin n → GE))
    (seeds : List (List E × E)) (hQc : Q.codes = codes) (h2 : 1 < Q.sent.size)
    (hQ : shapeAt Q 1 = Sh.sharedSplit) (hA : Sh.sharedSplit.answers = 1)
    (h0 : seeds.getD 0 default = (z, β)) :
    (Johnson.Prover.Send.answers Q T first
        (held w₀ first Q (sendsOmega codes Sh psiLo u cOmega (spCoins (spSymCode codes Sh).r n x)))
        seeds)[VerifiableInference.Desc.K1.offset Q 1 + 0]? =
      some (ofE
        (spTriple codes Sh Q first w₀ psiLo zfd u cOmega n S T z β zeroE kappa x).2.1) :=
  sp_answer codes Sh Q T first _ seeds z β hQc h2 hQ hA h0

/-- **send_enc, called at the second message, at free rows V and a free position x**: the cut of a
leaf by the IOP as written in Lean, at the column that the shared sending writes, reads in its one
mask row as the symbol at the position modulo the mask code's length. -/
theorem sp_read (codes : Codes) (Sh : LinShape) (Q : VerifiableInference.Desc.K1.Par)
    (V : ℕ → Rows) (X : OnBytes.Oracle) (x : ℕ)
    (hP : VerifiableInference.Desc.K1.planOkOwn Q = true) (hQc : Q.codes = codes)
    (h2 : 1 < Q.sent.size) (hQ : shapeAt Q 1 = Sh.sharedSplit)
    (hm : Sh.sharedSplit.maskRows = 1) (hX : X.shape = Sh.sharedSplit) :
    readE ((Blk.columnOf X
        (Johnson.Prover.Send.skipMain
          (((VerifiableInference.Desc.Own.treesMade Q.codes Q.sent).getD {}).shapes.getD
            (((VerifiableInference.Desc.Own.treesMade Q.codes Q.sent).getD {}).tree.getD 1 0) {})
          (((VerifiableInference.Desc.Own.treesMade Q.codes Q.sent).getD {}).part.getD 1 0))
        (Johnson.Prover.Send.skipMask
          (((VerifiableInference.Desc.Own.treesMade Q.codes Q.sent).getD {}).shapes.getD
            (((VerifiableInference.Desc.Own.treesMade Q.codes Q.sent).getD {}).tree.getD 1 0) {})
          (((VerifiableInference.Desc.Own.treesMade Q.codes Q.sent).getD {}).part.getD 1 0))
        (Johnson.Prover.Send.col Q V
          (((VerifiableInference.Desc.Own.treesMade Q.codes Q.sent).getD {}).tree.getD 1 0)
          x).toArray).mask.getD 0 zeroE) =
      symG (spSymCode codes Sh) (x % 2 ^ (spSymCode codes Sh).a) ((V 1).mask 0)
        ((V 1).maskTl 0) := by
  have eZ : OnBytes.Slice.codeOf (Q.codes.mask.getD (shapeAt Q 1).maskCode default) =
      spSymCode codes Sh := by
    rw [hQ, hQc]
    rfl
  rw [← eZ]
  exact (Johnson.Prover.Send.send_enc Q V hP 1 X x h2 (hX.trans hQ.symm)).2.2.2 0
    (by rw [hQ, hm]; exact Nat.one_pos)

/-! ## The verifier's own constraint at "SPLIT" -/

/-- **At the tables of the two sendings, the left side of the verifier's constraint at "SPLIT" is
the scalar muSent.** By muVal_formula and mu_chain. -/
theorem muVal_sent (T : Statement) (codes : Codes) (Sh : LinShape) (l : Lin) (row : Row)
    (members : Array Nat) (kappa : ℕ) (w₀ : Words GE) (first next : ℕ)
    (PU PO : VerifiableInference.Desc.K1.Par) (VU : ℕ → Rows) (psiLo : List GE) (u : ℕ → GE)
    (cOmega cSp : MsgCoins) (hf : Desc.K14.fold Sh l (linLayOmega codes Sh) = some row)
    (hP : Law.Placed T Sh l (linLayOmega codes Sh)) (hO : members.contains l.oOmega = true)
    (hU : members.contains l.oU.oracle = false) (ho : l.oSp < T.oracles.size)
    (hk : kappa < Means.tableSize T l.oSp .mask)
    (hfit : VerifiableInference.Desc.Own.linFits codes Sh = true) (hsz : 1 < PO.sent.size)
    (hsh0 : shapeAt PO 0 = Sh.omega) (hsh1 : shapeAt PO 1 = Sh.sharedSplit)
    (hlO : l.oOmega = next) (hlS : l.oSp = next + 1)
    (hk' : kappa % 2 ^ ceilLog2 Sh.sharedSplit.maskRows < Sh.sharedSplit.maskRows) :
    muVal rdE T row members l.oSp kappa
        (chainWords w₀ first next PU PO VU (sendsOmega codes Sh psiLo u cOmega cSp)) =
      muSent Sh psiLo (l.zFd.map rdE.val) u cSp kappa := by
  rw [muVal_formula rdE T Sh l (linLayOmega codes Sh) row members kappa _ hf hP hO hU ho hk]
  exact mu_chain w₀ first next PU PO VU codes Sh psiLo (l.zFd.map rdE.val) u cOmega cSp l hfit hsz
    hsh0 hsh1 hlO hlS kappa hk'

/-- **The triple's component at kappa is the left side of the verifier's constraint at "SPLIT"**, at
the tables of the two sendings: the words in front of "send o_omega" are those that hold "send
o_u"'s tables. -/
theorem spTriple_muVal (T T' : Statement) (codes : Codes) (Sh : LinShape) (l : Lin) (row : Row)
    (members : Array Nat) (n : ℕ) (kappa : Fin n) (w₀ : Words GE) (first next : ℕ)
    (PU PO : VerifiableInference.Desc.K1.Par) (VU : ℕ → Rows) (psiLo : List GE) (u : ℕ → GE)
    (cOmega : MsgCoins) (S : Finset (Fin (2 ^ (spSymCode codes Sh).a))) (z : List E) (β y : E)
    (x : (Fin (spSymCode codes Sh).r → GE) × GE × (Fin n → GE))
    (hf : Desc.K14.fold Sh l (linLayOmega codes Sh) = some row)
    (hP : Law.Placed T Sh l (linLayOmega codes Sh)) (hO : members.contains l.oOmega = true)
    (hU : members.contains l.oU.oracle = false) (ho : l.oSp < T.oracles.size)
    (hk : kappa.val < Means.tableSize T l.oSp .mask)
    (hfit : VerifiableInference.Desc.Own.linFits codes Sh = true) (hsz : 1 < PO.sent.size)
    (hsh0 : shapeAt PO 0 = Sh.omega) (hsh1 : shapeAt PO 1 = Sh.sharedSplit)
    (hlO : l.oOmega = next) (hlS : l.oSp = next + 1) (hm : Sh.sharedSplit.maskRows = 1) :
    (spTriple codes Sh PO next (held w₀ first PU VU) psiLo (l.zFd.map rdE.val) u cOmega n S T' z β y
        kappa x).2.2 kappa =
      muVal rdE T row members l.oSp kappa.val (chainWords w₀ first next PU PO VU
        (sendsOmega codes Sh psiLo u cOmega (spCoins (spSymCode codes Sh).r n x))) := by
  rw [muVal_sent T codes Sh l row members kappa.val w₀ first next PU PO VU psiLo u cOmega _ hf hP hO
    hU ho hk hfit hsz hsh0 hsh1 hlO hlS (by
      rw [hm]
      have : ceilLog2 1 = 0 := rfl
      rw [this, Nat.pow_zero, Nat.mod_one]
      exact Nat.one_pos)]
  show (if kappa = kappa then _ else _) = _
  rw [if_pos rfl]

end Desc.K14.Honest

#print axioms Desc.K14.Honest.fresh_sent_shape
#print axioms Desc.K14.Honest.parO_two
#print axioms Desc.K14.Honest.parO_omega
#print axioms Desc.K14.Honest.parO_split
#print axioms Desc.K14.Honest.sent_split
#print axioms Desc.K14.Honest.fresh_chain
#print axioms Desc.K14.Honest.held_mask
#print axioms Desc.K14.Honest.mu_at
#print axioms Desc.K14.Honest.spTripleAt_agree
#print axioms Desc.K14.Honest.fresh_agree
#print axioms Desc.K14.Honest.fresh_zero
#print axioms Desc.K14.Honest.fresh_chain_zero
#print axioms Desc.K14.Honest.spTriple_written
#print axioms Desc.K14.Honest.spTriple_answer
#print axioms Desc.K14.Honest.sp_read
#print axioms Desc.K14.Honest.muVal_sent
#print axioms Desc.K14.Honest.spTriple_muVal
